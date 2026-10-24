import http.server, datetime, os, secrets, urllib.parse, urllib.request, json
import base64, hashlib, struct, threading, time, signal
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

# ---------- guid registration (design: guid-hash-cert-design) ----------
# All knobs are env-overridable so the test harness can run the same
# code with short clocks and scratch paths.
STATE_PATH = os.environ.get('KW_STATE_PATH', '/var/lib/knockwire/state.json')
LOG_PATH = os.environ.get('KW_LOG_PATH', '/var/log/kw-test.log')
CERTMINT_BASE = os.environ.get('KW_CERTMINT_BASE', 'https://www.certmint.net')
PORT_POOL_START = int(os.environ.get('KW_PORT_START', '20000'))
PORT_POOL_END = int(os.environ.get('KW_PORT_END', '20999'))
LEASE_TTL_SECS = int(os.environ.get('KW_LEASE_TTL_SECS', str(24 * 3600)))
PORT_COLLECT_SECS = int(os.environ.get('KW_PORT_COLLECT_SECS', str(24 * 3600)))
CHALLENGE_TTL_SECS = int(os.environ.get('KW_CHALLENGE_TTL_SECS', '300'))
CULL_INTERVAL_SECS = int(os.environ.get('KW_CULL_INTERVAL_SECS', '60'))
MAILBOX_FLUSH_SECS = int(os.environ.get('KW_MAILBOX_FLUSH_SECS', '15'))
MAILBOX_TTL_SECS = int(os.environ.get('KW_MAILBOX_TTL_SECS', str(24 * 3600)))
MAILBOX_MAX = int(os.environ.get('KW_MAILBOX_MAX', '500'))
# Certwire app-layer delivery (2026-10-23): registrations that carry a
# certwire address get knocks for these services delivered as app-layer
# posts via the kw-bridge companion (the ack is the delivery signal).
# A failed certwire attempt does NOT fall back to the tunnel port
# (stripped 2026-10-24, Chris's direction: certwire is the transport
# for certwire-bearing registrations; failures spool to the mailbox
# and the flusher retries there). The tunnel port remains only as the
# primary delivery for registrations without a certwire address.
# The mailbox flush uses the same deliver() path.
BRIDGE_URL = os.environ.get('KW_BRIDGE_URL', 'http://127.0.0.1:18770')
CW_SERVICES = {s.strip() for s in os.environ.get(
    'KW_CERTWIRE_SERVICES', 'gmail,gmailwork,test').split(',') if s.strip()}
DELIVER_LOG = os.environ.get('KW_DELIVER_LOG', '/var/log/kw-deliver.log')
TRUST_TTL_SECS = int(os.environ.get('KW_TRUST_TTL_SECS', '300'))
LISTEN_PORT = int(os.environ.get('KW_PORT', '18080'))

def now_utc():
    return datetime.datetime.now(datetime.timezone.utc)

def ts(dt):
    return dt.strftime('%Y-%m-%dT%H:%M:%SZ')

def parse_ts(s):
    return datetime.datetime.strptime(s, '%Y-%m-%dT%H:%M:%SZ').replace(tzinfo=datetime.timezone.utc)

LOCK = threading.Lock()
def load_state():
    try:
        with open(STATE_PATH) as f:
            return json.load(f)
    except Exception:
        return {'registrations': {}, 'challenges': {}, 'ports': {},
                'mailboxes': {}, 'mailbox_stats': {}}

def save_state(st):
    tmp = STATE_PATH + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(st, f)
    os.replace(tmp, STATE_PATH)

# ---------- certmint trust anchors (fetched, cached) ----------
TRUST = {'fetched': 0, 'mint_raw': None, 'revoked': set()}

def trust():
    """(mint public key raw bytes, revoked serial set) from certmint,
    cached for TRUST_TTL_SECS. Raises if never fetched successfully."""
    if time.time() - TRUST['fetched'] < TRUST_TTL_SECS and TRUST['mint_raw']:
        return TRUST['mint_raw'], TRUST['revoked']
    # A named UA: Cloudflare 403s urllib's default Python-urllib one.
    ua = {'User-Agent': 'knockwire/1.0'}
    with urllib.request.urlopen(urllib.request.Request(
            CERTMINT_BASE + '/pubkey', headers=ua), timeout=10) as r:
        pub = json.load(r)
    blob = base64.b64decode(pub['key'].split()[1])
    raw = blob[-32:]
    with urllib.request.urlopen(urllib.request.Request(
            CERTMINT_BASE + '/revoked', headers=ua), timeout=10) as r:
        revoked = {int(x) for x in r.read().decode().split()}
    TRUST.update(fetched=time.time(), mint_raw=raw, revoked=revoked)
    return raw, revoked

# ---------- cert / key helpers (same constructions as certmint) ----------
def parse_cert(text):
    lines = text.strip().split('\n')
    sig_line = lines[-1]
    if not sig_line.startswith('signature: '):
        raise ValueError('no signature line')
    body = ('\n'.join(lines[:-1]) + '\n').encode()
    fields = {}
    identities = []
    for ln in lines[:-1]:
        if ': ' in ln:
            k, v = ln.split(': ', 1)
            if k == 'identity':
                identities.append(v)
            else:
                fields[k] = v
    return fields, identities, body, sig_line.split(': ', 1)[1]

def parse_openssh_key(line):
    parts = line.strip().split()
    if len(parts) < 2 or parts[0] != 'ssh-ed25519':
        raise ValueError('not an ssh-ed25519 key')
    blob = base64.b64decode(parts[1])
    ln, = struct.unpack('>I', blob[:4])
    if blob[4:4 + ln] != b'ssh-ed25519':
        raise ValueError('bad blob')
    off = 4 + ln
    ln2, = struct.unpack('>I', blob[off:off + 4])
    raw = blob[off + 4:off + 4 + ln2]
    if len(raw) != 32:
        raise ValueError('bad key length')
    return blob, raw

def guid_hash_of(guid_bytes):
    return 'SHA256:' + base64.b64encode(hashlib.sha256(guid_bytes).digest()).decode().rstrip('=')

# ---------- ports: what is actually bound, not just registered ----------
def bound_ports():
    """Listening TCP ports in the pool range, read from the kernel
    tables — the ground truth for 'in use'."""
    out = set()
    for path in ('/proc/net/tcp', '/proc/net/tcp6'):
        try:
            lines = open(path).read().splitlines()[1:]
        except Exception:
            continue
        for ln in lines:
            f = ln.split()
            if f[3] == '0A':  # LISTEN
                port = int(f[1].rsplit(':', 1)[1], 16)
                if PORT_POOL_START <= port <= PORT_POOL_END:
                    out.add(port)
    return out

def kill_port(port):
    """SIGTERM whatever process holds the listener on `port` — the
    sshd session serving that forward. Cull teardown, step one."""
    inodes = set()
    for path in ('/proc/net/tcp', '/proc/net/tcp6'):
        try:
            lines = open(path).read().splitlines()[1:]
        except Exception:
            continue
        for ln in lines:
            f = ln.split()
            if f[3] == '0A' and int(f[1].rsplit(':', 1)[1], 16) == port:
                inodes.add(f[9])
    if not inodes:
        return
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            for fd in os.listdir(f'/proc/{pid}/fd'):
                try:
                    target = os.readlink(f'/proc/{pid}/fd/{fd}')
                except OSError:
                    continue
                if target.startswith('socket:[') and target[8:-1] in inodes:
                    os.kill(int(pid), signal.SIGTERM)
                    break
        except OSError:
            continue

# ---------- mailbox: store-and-forward for registered knocks ----------
# A knock for a registered guid whose delivery attempt fails (tunnel
# down, client demux not answering) is spooled per-guid and retried by
# the flusher until it lands, the entry ages past MAILBOX_TTL_SECS, or
# the registration is culled. Unregistered/lapsed guids still drop —
# the mailbox never queues for strangers. Knocks are pointers: a late
# or duplicate delivery is harmless downstream (pulls are range-based),
# so delivery here is at-least-once.

def try_deliver(port, method, rest):
    """One path-only delivery attempt to the bound port. True iff the
    client's endpoint answered without a transport/HTTP error."""
    url = f'http://127.0.0.1:{port}{rest}'
    relay = urllib.request.Request(url, data=None, method=method)
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(relay, timeout=5) as r:
            r.read()
        return True
    except Exception:
        return False

def _dlog(msg):
    try:
        with open(DELIVER_LOG, 'a') as f:
            f.write(f'{ts(now_utc())} {msg}\n')
    except Exception:
        pass

def bridge_deliver(addr, guid_hex, method, rest):
    """One app-layer delivery attempt via kw-bridge. True iff the
    muse acked 200 — the ack, not the router's 'sent', is the
    delivery signal (a bound-but-deaf endpoint must not count)."""
    data = json.dumps({'to': addr, 'path': f'/{guid_hex}{rest}',
                       'method': method}).encode()
    relay = urllib.request.Request(BRIDGE_URL + '/deliver', data=data,
        method='POST', headers={'Content-Type': 'application/json'})
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(relay, timeout=15) as r:
            return json.loads(r.read() or b'{}').get('status') == 200
    except Exception:
        return False

def deliver(reg, guid_hex, method, rest):
    """Deliver one knock for a registration: certwire app-layer for
    opted-in services on registrations carrying a certwire address
    (certwire or nothing — a failed attempt returns False and the
    knock spools to the mailbox; there is no port fallback). The
    bound tunnel port serves registrations without a certwire
    address, as their primary transport. Mailbox entries spooled
    before guid_hex was recorded pass None and stay port-only."""
    service = rest.strip('/').split('/')[0].lower() if rest.strip('/') else ''
    addr = reg.get('certwire')
    if addr and guid_hex and service in CW_SERVICES:
        if bridge_deliver(addr, guid_hex, method, rest):
            _dlog(f'certwire ok {method} {rest} -> {addr}')
            return True
        _dlog(f'certwire failed {method} {rest} -> {addr}; no port fallback')
        return False
    ok = try_deliver(reg['port'], method, rest)
    _dlog(f"port {'ok' if ok else 'failed'} {method} {rest} -> {reg['port']}")
    return ok

def _stats(st, guid_hash):
    return st.setdefault('mailbox_stats', {}).setdefault(
        guid_hash, {'spooled': 0, 'delivered': 0, 'expired': 0, 'overflow': 0})

def spool_knock(guid_hash, guid_hex, method, rest):
    """Append a failed knock to the guid's mailbox (LOCK held by caller
    discipline: this takes LOCK itself). Overflow drops the OLDEST
    entry — a newer knock's pull subsumes it. guid_hex rides along so
    the flusher can rebuild the certwire app path (/<guid>/<service>);
    entries spooled before it was recorded lack 'g' and stay
    port-only."""
    with LOCK:
        st = load_state()
        box = st.setdefault('mailboxes', {}).setdefault(guid_hash, [])
        box.append({'m': method, 'p': rest, 'g': guid_hex,
                    'q': ts(now_utc()), 'n': 0})
        stats = _stats(st, guid_hash)
        stats['spooled'] += 1
        while len(box) > MAILBOX_MAX:
            box.pop(0)
            stats['overflow'] += 1
        save_state(st)

def mailbox_flush():
    """Every MAILBOX_FLUSH_SECS: expire old entries, and for each
    mailbox whose port is currently bound, deliver FIFO until the
    first failure. Delivery attempts run outside LOCK; a successful
    head is popped only if it is still the head."""
    while True:
        time.sleep(MAILBOX_FLUSH_SECS)
        try:
            bound = bound_ports()
            with LOCK:
                st = load_state()
            for guid_hash, box in list(st.get('mailboxes', {}).items()):
                if not box:
                    continue
                reg = st['registrations'].get(guid_hash)
                if not reg or parse_ts(reg['lease_expires']) < now_utc():
                    continue  # reaper owns teardown of dead registrations
                port = reg['port']
                cutoff = now_utc() - datetime.timedelta(seconds=MAILBOX_TTL_SECS)
                while box and parse_ts(box[0]['q']) < cutoff:
                    head = box.pop(0)
                    with LOCK:
                        st2 = load_state()
                        live = st2.get('mailboxes', {}).get(guid_hash, [])
                        if live and live[0] == head:
                            live.pop(0)
                            _stats(st2, guid_hash)['expired'] += 1
                            save_state(st2)
                if port not in bound and not reg.get('certwire'):
                    continue
                while box:
                    head = box[0]
                    if not deliver(reg, head.get('g'), head['m'], head['p']):
                        with LOCK:
                            st2 = load_state()
                            live = st2.get('mailboxes', {}).get(guid_hash, [])
                            if live and live[0]['q'] == head['q'] and live[0]['p'] == head['p']:
                                live[0]['n'] = live[0].get('n', 0) + 1
                                save_state(st2)
                        break
                    with LOCK:
                        st2 = load_state()
                        live = st2.get('mailboxes', {}).get(guid_hash, [])
                        if live and live[0]['q'] == head['q'] and live[0]['p'] == head['p']:
                            live.pop(0)
                            _stats(st2, guid_hash)['delivered'] += 1
                            save_state(st2)
                    box = box[1:]
        except Exception:
            continue

def reaper():
    """Every CULL_INTERVAL_SECS: refresh last-bound sightings, and
    tear down expired leases IN REVERSE — kill the connection, then
    strip the registration."""
    while True:
        time.sleep(CULL_INTERVAL_SECS)
        try:
            bound = bound_ports()
            kills = []
            with LOCK:
                st = load_state()
                changed = False
                for h, reg in list(st['registrations'].items()):
                    port = reg['port']
                    if port in bound:
                        reg['last_bound'] = ts(now_utc())
                        st['ports'][str(port)] = {'last_used': ts(now_utc())}
                        changed = True
                    if parse_ts(reg['lease_expires']) < now_utc():
                        kills.append(port)
                        del st['registrations'][h]
                        st.get('mailboxes', {}).pop(h, None)
                        changed = True
                if changed:
                    save_state(st)
            for port in kills:
                kill_port(port)
        except Exception:
            continue


CSS = "body{font-family:system-ui,sans-serif;margin:4rem auto;max-width:40rem;padding:0 1rem}h1{font-weight:600}p{color:#555}.btn{display:inline-block;background:#0081fb;color:#fff;padding:.7rem 1.4rem;border-radius:.5rem;text-decoration:none;font-weight:600}code{background:#f0f0f0;padding:.15rem .4rem;border-radius:.3rem}"

def page(title, inner):
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<style>{CSS}</style>
</head>
<body>
{inner}
</body>
</html>
""".encode()

class H(http.server.BaseHTTPRequestHandler):
    def _log(self):
        ts = datetime.datetime.now(datetime.timezone.utc).isoformat()
        src = self.headers.get('CF-Connecting-IP', self.client_address[0])
        ray = self.headers.get('CF-Ray', '-')
        host = self.headers.get('Host', '-')
        with open(LOG_PATH, 'a') as f:
            f.write(f'{ts} {self.command} {self.path} host={host} from {src} ray={ray}\n')
        return ts

    def _json(self, code, obj):
        self._send(code, json.dumps(obj).encode(), 'application/json')

    def _body_json(self):
        ln = int(self.headers.get('Content-Length') or 0)
        if ln <= 0 or ln > 65536:
            return {}
        try:
            return json.loads(self.rfile.read(ln).decode())
        except Exception:
            return {}

    # ---------- guid registration ----------
    def _register_challenge(self, qs):
        serial = (qs.get('serial') or [''])[0]
        if not serial.isdigit():
            self._json(400, {'error': 'serial required'})
            return
        nonce = secrets.token_urlsafe(32)
        with LOCK:
            st = load_state()
            st['challenges'][nonce] = {'serial': int(serial),
                                       'expires': ts(now_utc() + datetime.timedelta(seconds=CHALLENGE_TTL_SECS))}
            save_state(st)
        self._json(200, {'nonce': nonce,
                         'signing_string': f'knockwire-register-v1\n{serial}\n{nonce}'})

    def _register(self):
        req = self._body_json()
        cert_text = req.get('cert') or ''
        nonce = req.get('nonce') or ''
        sig_b64 = req.get('signature') or ''
        guid_hex = (req.get('guid') or '').strip().lower()
        cw_addr = (req.get('certwire') or '').strip()
        if cw_addr and ('/' not in cw_addr or ' ' in cw_addr
                         or len(cw_addr) > 128):
            cw_addr = ''
        try:
            mint_raw, revoked = trust()
        except Exception:
            self._json(502, {'error': 'certmint trust anchors unavailable'})
            return
        try:
            fields, identities, body, mint_sig = parse_cert(cert_text)
        except Exception:
            self._json(400, {'error': 'unparseable cert'})
            return
        try:
            Ed25519PublicKey.from_public_bytes(mint_raw).verify(base64.b64decode(mint_sig), body)
        except Exception:
            self._json(400, {'error': 'mint signature does not verify'})
            return
        guid_hash = fields.get('guid-hash')
        if not guid_hash:
            self._json(400, {'error': 'not a guid cert'})
            return
        serial = fields.get('serial', '')
        if not serial.isdigit():
            self._json(400, {'error': 'bad serial'})
            return
        if int(serial) in revoked:
            self._json(403, {'error': 'serial revoked'})
            return
        if parse_ts(fields['expires']) < now_utc():
            self._json(403, {'error': 'cert expired'})
            return
        try:
            guid_bytes = bytes.fromhex(guid_hex)
        except Exception:
            self._json(400, {'error': 'guid must be hex'})
            return
        if guid_hash_of(guid_bytes) != guid_hash:
            self._json(400, {'error': 'guid does not match cert'})
            return
        with LOCK:
            st = load_state()
            ch = st['challenges'].pop(nonce, None)
            if ch:
                save_state(st)
        if not ch or ch.get('serial') != int(serial) or parse_ts(ch['expires']) < now_utc():
            self._json(400, {'error': 'unknown or expired challenge'})
            return
        try:
            blob, raw = parse_openssh_key(fields['key'])
            Ed25519PublicKey.from_public_bytes(raw).verify(
                base64.b64decode(sig_b64),
                f'knockwire-register-v1\n{serial}\n{nonce}'.encode())
        except Exception:
            self._json(403, {'error': 'possession proof does not verify'})
            return
        # Allocate or renew, under the one lock.
        with LOCK:
            st = load_state()
            bound = bound_ports()
            lease_exp = ts(now_utc() + datetime.timedelta(seconds=LEASE_TTL_SECS))
            existing = st['registrations'].get(guid_hash)
            if existing:
                # Register while alive returns the same port — and a
                # lapsed lease re-adopts the port its connection may
                # still hold. Latest verified cert/key wins the record.
                port = existing['port']
                existing.update({'key': fields['key'],
                                 'key-fingerprint': fields['key-fingerprint'],
                                 'serial': int(serial),
                                 'lease_expires': lease_exp})
                if cw_addr:
                    existing['certwire'] = cw_addr
                st['ports'][str(port)] = {'last_used': ts(now_utc())}
                save_state(st)
                self._json(200, {'port': port, 'guid_hash': guid_hash,
                                 'lease_expires': lease_exp})
                return
            live_ports = {r['port'] for r in st['registrations'].values()
                          if parse_ts(r['lease_expires']) >= now_utc()}
            port = None
            for cand in range(PORT_POOL_START, PORT_POOL_END + 1):
                if cand in live_ports or cand in bound:
                    continue
                used = st['ports'].get(str(cand), {}).get('last_used')
                if used and parse_ts(used) + datetime.timedelta(seconds=PORT_COLLECT_SECS) > now_utc():
                    continue  # collected ports rest before reissue
                port = cand
                break
            if port is None:
                self._json(503, {'error': 'no ports available'})
                return
            st['registrations'][guid_hash] = {
                'port': port, 'key': fields['key'],
                'key-fingerprint': fields['key-fingerprint'],
                'serial': int(serial), 'lease_expires': lease_exp,
                'last_bound': None}
            if cw_addr:
                st['registrations'][guid_hash]['certwire'] = cw_addr
            st['ports'][str(port)] = {'last_used': ts(now_utc())}
            save_state(st)
        self._json(201, {'port': port, 'guid_hash': guid_hash,
                         'lease_expires': lease_exp})

    # ---------- knock relay: path only, everything else stripped ----------
    def _knock(self, guid_hex, rest):
        try:
            guid_hash = guid_hash_of(bytes.fromhex(guid_hex))
        except Exception:
            guid_hash = None
        reg = None
        if guid_hash:
            with LOCK:
                st = load_state()
            r = st['registrations'].get(guid_hash)
            if r and parse_ts(r['lease_expires']) >= now_utc():
                reg = r
        if reg is None:
            self._send(200, b'knockwire drop\n', 'text/plain')
            return
        # The delivered request is rebuilt from the path alone: no
        # body, no query, no fragment, no sender headers. Loopback is
        # never proxied. A failed delivery to a REGISTERED guid is
        # spooled to its mailbox for the flusher, not dropped.
        if deliver(reg, guid_hex, self.command, rest):
            self._send(200, b'knockwire knock\n', 'text/plain')
        else:
            spool_knock(guid_hash, guid_hex, self.command, rest)
            self._send(200, b'knockwire queued\n', 'text/plain')

    def _send(self, code, body, ctype='text/html; charset=utf-8', extra=None):
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        for k, v in (extra or []):
            self.send_header(k, v)
        self.end_headers()
        if self.command != 'HEAD':
            self.wfile.write(body)

    def _route(self):
        ts = self._log()
        host = (self.headers.get('Host') or '').split(':')[0].lower()
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        # Agent API plane (any host): guid registration.
        if path == '/v1/register/challenge' and self.command == 'GET':
            self._register_challenge(urllib.parse.parse_qs(parsed.query))
            return
        if path == '/v1/register' and self.command == 'POST':
            self._register()
            return
        if host == 'push.knockwire.net':
            # A knock is /<guid>/<service...>: deliver path-only, or
            # drop. Non-knock paths keep the doorbell stub.
            parts = path.split('/', 2)
            if len(parts) >= 2 and len(parts[1]) == 64 and \
                    all(c in '0123456789abcdef' for c in parts[1].lower()):
                rest = '/' + parts[2] if len(parts) > 2 and parts[2] else '/'
                self._knock(parts[1].lower(), rest)
                return
            self._send(200, f'knockwire hit {ts}\n'.encode(), 'text/plain')
            return
        if path in ('/', '/index.html'):
            inner = """<h1>knockwire</h1>
<p>knockwire is listening.</p>"""
            self._send(200, page('knockwire', inner))
            return

        self._send(404, b'not found\n', 'text/plain')

    do_GET = _route
    do_POST = _route
    do_HEAD = _route

threading.Thread(target=reaper, daemon=True).start()
threading.Thread(target=mailbox_flush, daemon=True).start()
http.server.ThreadingHTTPServer(('127.0.0.1', LISTEN_PORT), H).serve_forever()
