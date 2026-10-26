#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SepiPanel — پنل مدیریت WireGuard (تک‌فایل)
  • اینباند = یک اینترفیس وایرگارد (wg0, wg1, ...) با تمام تنظیمات
  • کلاینت = یک کاربر که می‌تواند عضو چند اینباند باشد (هر اینباند آی‌پی جدا)
  • لینک ساب برای هر کلاینت (base64 / raw / conf / json / صفحه وب با QR)
  • حجم، تاریخ انقضا، آمار ترافیک، آنلاین بودن، غیرفعال‌سازی خودکار

نصب (Ubuntu/Debian، با root):
    apt update && apt install -y wireguard wireguard-tools iptables iproute2 python3-pip
    pip3 install flask qrcode      # اگر خطای externally-managed دیدید: --break-system-packages
    python3 sepipanel.py
اجرا دائمی با systemd: انتهای همین فایل را ببینید.

اگر می‌خواهید اینباند AmneziaWG (مبهم‌سازی ضد DPI) داشته باشید، علاوه بر موارد بالا:
    add-apt-repository -y ppa:amnezia/ppa && apt install -y amneziawg amneziawg-tools
پورت/دامنه/HTTPS/مسیر مخفی/رمز را از تب «تنظیمات» عوض کنید. اگر قفل شدید:  python3 sepipanel.py --reset
"""
import uuid, urllib.request, zipfile, tempfile, string, os, re, io, sys, json, time, html, base64, secrets, sqlite3, hmac, hashlib, shutil, socket, ssl, ipaddress, subprocess, threading, logging, collections, platform, shlex
from urllib.parse import quote, urlsplit
from functools import wraps

from flask import Flask, request, jsonify, session, Response, abort, g

try:
    import qrcode, qrcode.image.svg
except Exception:  # QR اختیاری است
    qrcode = None

# ============================ تنظیمات (هاردکد) ============================
PANEL_HOST     = "0.0.0.0"
PANEL_PORT     = 8080
ADMIN_USER     = "admin"
ADMIN_PASS     = "ChangeMe-123"          # حتماً عوض کنید
WG_DIR         = "/etc/wireguard"
AWG_DIR        = "/etc/amnezia/amneziawg"   # اینباندهای AmneziaWG
DB_PATH        = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sepipanel.db")
STATS_INTERVAL = 15                      # ثانیه
PUBLIC_URL     = ""                      # مثلا https://panel.example.com ؛ خالی = خودکار
# ==========================================================================

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("sepipanel")

# ------------------------------ X25519 (بدون وابستگی) ------------------------------
_P = 2 ** 255 - 19
_BASE = (9).to_bytes(32, "little")


def x25519(k: bytes, u: bytes) -> bytes:
    k = bytearray(k); k[0] &= 248; k[31] &= 127; k[31] |= 64
    k = int.from_bytes(k, "little")
    x1 = int.from_bytes(u, "little") & ((1 << 255) - 1)
    x2, z2, x3, z3, swap = 1, 0, x1, 1, 0
    for t in range(254, -1, -1):
        kt = (k >> t) & 1
        swap ^= kt
        if swap:
            x2, x3 = x3, x2; z2, z3 = z3, z2
        swap = kt
        A = (x2 + z2) % _P; AA = A * A % _P
        B = (x2 - z2) % _P; BB = B * B % _P
        E = (AA - BB) % _P
        C = (x3 + z3) % _P; D = (x3 - z3) % _P
        DA = D * A % _P; CB = C * B % _P
        x3 = (DA + CB) ** 2 % _P
        z3 = x1 * ((DA - CB) ** 2) % _P
        x2 = AA * BB % _P
        z2 = E * (AA + 121665 * E) % _P
    if swap:
        x2, x3 = x3, x2; z2, z3 = z3, z2
    return (x2 * pow(z2, _P - 2, _P) % _P).to_bytes(32, "little")


def gen_private():
    k = bytearray(os.urandom(32)); k[0] &= 248; k[31] &= 127; k[31] |= 64
    return base64.b64encode(bytes(k)).decode()


def pub_from_private(priv):
    return base64.b64encode(x25519(base64.b64decode(priv), _BASE)).decode()


def gen_psk():
    return base64.b64encode(os.urandom(32)).decode()


def check_key(k, label="کلید"):
    try:
        if len(base64.b64decode(k, validate=True)) == 32:
            return k
    except Exception:
        pass
    raise Err(f"{label} نامعتبر است (باید base64 و ۳۲ بایت باشد)")


# ------------------------------ دیتابیس ------------------------------
LOCK = threading.RLock()
APPLY_LOCK = threading.RLock()
_db = sqlite3.connect(DB_PATH, check_same_thread=False, isolation_level=None)
_db.row_factory = sqlite3.Row
_db.execute("PRAGMA foreign_keys=ON")
_db.executescript("""
CREATE TABLE IF NOT EXISTS inbounds(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, remark TEXT DEFAULT '',
  enabled INTEGER DEFAULT 1, port INTEGER NOT NULL, private_key TEXT, public_key TEXT,
  address4 TEXT NOT NULL, address6 TEXT DEFAULT '', endpoint TEXT DEFAULT '', endpoint_port INTEGER DEFAULT 0,
  dns TEXT DEFAULT '', mtu INTEGER DEFAULT 0, table_ TEXT DEFAULT '', fwmark TEXT DEFAULT '',
  pre_up TEXT DEFAULT '', post_up TEXT DEFAULT '', pre_down TEXT DEFAULT '', post_down TEXT DEFAULT '',
  auto_rules INTEGER DEFAULT 1, nat_iface TEXT DEFAULT '', use_psk INTEGER DEFAULT 1,
  client_allowed_ips TEXT DEFAULT '0.0.0.0/0, ::/0', client_keepalive INTEGER DEFAULT 25,
  client_mtu INTEGER DEFAULT 0, created INTEGER);
CREATE TABLE IF NOT EXISTS clients(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, token TEXT UNIQUE NOT NULL,
  enabled INTEGER DEFAULT 1, reason TEXT DEFAULT '', private_key TEXT, public_key TEXT,
  limit_bytes INTEGER DEFAULT 0, up_bytes INTEGER DEFAULT 0, down_bytes INTEGER DEFAULT 0,
  expiry INTEGER DEFAULT 0, note TEXT DEFAULT '', created INTEGER, last_seen INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS client_inbound(
  client_id INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
  inbound_id INTEGER NOT NULL REFERENCES inbounds(id) ON DELETE CASCADE,
  ip4 TEXT, ip6 TEXT DEFAULT '', psk TEXT DEFAULT '', allowed_ips TEXT DEFAULT '',
  keepalive INTEGER DEFAULT -1, dns TEXT DEFAULT '', mtu INTEGER DEFAULT 0, extra_allowed TEXT DEFAULT '',
  last_rx INTEGER DEFAULT 0, last_tx INTEGER DEFAULT 0, last_hs INTEGER DEFAULT 0, endpoint TEXT DEFAULT '',
  PRIMARY KEY(client_id, inbound_id));
CREATE TABLE IF NOT EXISTS admins(
  id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE NOT NULL, pass_hash TEXT NOT NULL,
  name TEXT DEFAULT '', note TEXT DEFAULT '', enabled INTEGER DEFAULT 1,
  limit_bytes INTEGER DEFAULT 0, used_bytes INTEGER DEFAULT 0, expiry INTEGER DEFAULT 0,
  ver TEXT DEFAULT '', created INTEGER, last_login INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS nodes(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE NOT NULL, address TEXT NOT NULL, ssh_port INTEGER DEFAULT 22,
  ssh_user TEXT DEFAULT 'root', xray_bin TEXT DEFAULT '/usr/local/bin/xray', xray_ver TEXT DEFAULT '', note TEXT DEFAULT '', created INTEGER);
""")


def ensure_cols(table, cols):
    have = {r["name"] for r in _db.execute(f"PRAGMA table_info({table})")}
    for c, d in cols.items():
        if c not in have:
            _db.execute(f"ALTER TABLE {table} ADD COLUMN {c} {d}")


ensure_cols("inbounds", {"obf": "TEXT DEFAULT ''", "exclude_sub": "INTEGER DEFAULT 0",
                         "proto": "TEXT DEFAULT 'wg'", "psk": "TEXT DEFAULT ''",
                         "ovpn": "TEXT DEFAULT ''", "pki": "TEXT DEFAULT ''", "xcfg": "TEXT DEFAULT ''",
                         "node_id": "INTEGER DEFAULT 0"})
ensure_cols("client_inbound", {"l2tp_user": "TEXT DEFAULT ''", "l2tp_pass": "TEXT DEFAULT ''",
                               "ovpn_cn": "TEXT DEFAULT ''", "ovpn_crt": "TEXT DEFAULT ''", "ovpn_key": "TEXT DEFAULT ''",
                               "vuuid": "TEXT DEFAULT ''"})
ensure_cols("clients", {"reset_period": "TEXT DEFAULT ''", "last_reset": "INTEGER DEFAULT 0", "owner_id": "INTEGER DEFAULT 0", "ext_id": "TEXT DEFAULT ''"})
_db.execute("""CREATE TABLE IF NOT EXISTS api_keys(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, key_hash TEXT UNIQUE, prefix TEXT, admin_id INTEGER DEFAULT 0,
  enabled INTEGER DEFAULT 1, created INTEGER, last_used INTEGER DEFAULT 0)""")
ensure_cols("api_keys", {"limit_bytes": "INTEGER DEFAULT 0", "used_bytes": "INTEGER DEFAULT 0", "expiry": "INTEGER DEFAULT 0"})
ensure_cols("clients", {"key_id": "INTEGER DEFAULT 0"})       # کلید API که این کلاینت را ساخته (0 = از پنل)
try:
    _db.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_clients_ext ON clients(owner_id, ext_id) WHERE ext_id!=''")
except Exception:
    pass
try:
    os.chmod(DB_PATH, 0o600)
except OSError:
    pass


def q(sql, a=(), one=False):
    with LOCK:
        rows = _db.execute(sql, a).fetchall()
    return (rows[0] if rows else None) if one else rows


def x(sql, a=()):
    with LOCK:
        return _db.execute(sql, a).lastrowid


def setting(k, d=""):
    r = q("SELECT v FROM settings WHERE k=?", (k,), True)
    return r["v"] if r else d


def set_setting(k, v):
    x("INSERT INTO settings(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))


# ------------------------------ ابزارها ------------------------------
class Err(Exception):
    pass


def now():
    return int(time.time())


def oneline(s):
    return re.sub(r"[\r\n]+", " ", str(s or "")).strip()


def num(v, d=0, lo=None, hi=None, label="مقدار"):
    if v is None or v == "":
        return d
    try:
        n = int(float(v))
    except Exception:
        raise Err(f"{label} نامعتبر است")
    if (lo is not None and n < lo) or (hi is not None and n > hi):
        raise Err(f"{label} خارج از محدوده مجاز است")
    return n


def run(cmd, inp=None, timeout=40):
    try:
        p = subprocess.run(cmd, input=inp, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except FileNotFoundError:
        return 127, "", f"{cmd[0]} پیدا نشد"
    except Exception as e:
        return 1, "", str(e)


def clean_list(s):
    return ", ".join(p.strip() for p in re.split(r"[,\s]+", str(s or "")) if p.strip())


def check_cidrs(s, label):
    s = clean_list(s)
    for p in filter(None, s.split(", ")):
        try:
            ipaddress.ip_network(p, strict=False)
        except Exception:
            raise Err(f"{label}: «{p}» معتبر نیست")
    return s


def check_dns(s):
    s = clean_list(s)
    for p in filter(None, s.split(", ")):
        if not re.fullmatch(r"[A-Za-z0-9.:\-_]+", p):
            raise Err(f"DNS «{p}» معتبر نیست")
    return s


def lines(s):
    return [l.strip() for l in str(s or "").splitlines() if l.strip()]


def detect_iface():
    rc, o, _ = run(["ip", "route", "get", "1.1.1.1"])
    m = re.search(r"\bdev (\S+)", o or "")
    return m.group(1) if m else "eth0"


def obf_of(ib):
    try:
        return json.loads(ib["obf"]) if ib["obf"] else {}
    except Exception:
        return {}


def is_awg(ib):
    return bool(ib["obf"])


def is_l2tp(ib):
    try:
        return ib["proto"] == "l2tp"
    except (KeyError, IndexError):
        return False


def is_vless(ib):
    try:
        return ib["proto"] == "vless"
    except (KeyError, IndexError):
        return False


def is_ovpn(ib):
    try:
        return ib["proto"] == "ovpn"
    except (KeyError, IndexError):
        return False


def ib_node(ib):
    """id نودی که اینباند روی آن است؛ ۰ = همین سرور (پنل)"""
    try:
        return int(ib["node_id"] or 0)
    except (KeyError, IndexError, TypeError, ValueError):
        return 0


def rand_secret(n=12):
    a = string.ascii_letters + string.digits
    return "".join(secrets.choice(a) for _ in range(n))


def tools(ib):
    return ("awg", "awg-quick") if is_awg(ib) else ("wg", "wg-quick")


def conf_path(ib):
    return os.path.join(AWG_DIR if is_awg(ib) else WG_DIR, f"{ib['name']}.conf")


def svc(ib):
    return f"{tools(ib)[1]}@{ib['name']}"


def alloc(net, used, skip):
    for i, h in enumerate(net.hosts()):
        if i > 70000:
            break
        s = str(h)
        if s != skip and s not in used:
            return s
    raise Err("ساب‌نت پر شده است")


# ------------------------------ AmneziaWG ------------------------------
OBF_ORDER = ["jc", "jmin", "jmax", "s1", "s2", "s3", "s4", "h1", "h2", "h3", "h4", "i1", "i2", "i3", "i4", "i5",
             "hpk", "cpa", "rekey_after", "rekey_timeout", "reject_after", "keepalive_timeout", "max_hs"]
OBF_NAME = dict(jc="Jc", jmin="Jmin", jmax="Jmax", s1="S1", s2="S2", s3="S3", s4="S4", h1="H1", h2="H2", h3="H3",
                h4="H4", i1="I1", i2="I2", i3="I3", i4="I4", i5="I5", hpk="HeaderProtectionKey",
                cpa="ContentPaddingAddition", rekey_after="RekeyAfterTime", rekey_timeout="RekeyTimeout",
                reject_after="RejectAfterTime", keepalive_timeout="KeepaliveTimeout", max_hs="MaxHandshakeAttempts")
CPS_RE = re.compile(r"(<(b 0x([0-9a-fA-F]{2})+|r \d+|rc \d+|rd \d+|t|c)>)+")
OBF_RANGES = ["cpa", "rekey_after", "rekey_timeout", "reject_after", "keepalive_timeout", "max_hs"]


def obf_lines(ib):
    o = obf_of(ib)
    return [(OBF_NAME[k], o[k]) for k in OBF_ORDER if o.get(k)]


def gen_obf(ver="3"):
    """ver 1 = AWG 1.x | 2 = AWG 2.0 (S3/S4, بازه H، I1) | 3 = AWG 3.x کامل (Header Protection + padding + تایمرها)"""
    r = secrets.SystemRandom()
    jmin = r.randint(8, 80)
    s1, s2 = r.randint(15, 120), r.randint(15, 120)
    while s1 + 56 == s2:
        s2 = r.randint(15, 120)
    o = dict(jc=r.randint(4, 10), jmin=jmin, jmax=min(1280, jmin + r.randint(60, 260)), s1=s1, s2=s2)
    q4 = (2 ** 32 - 10) // 4
    bases = [5 + i * q4 + r.randint(0, q4 - 600000) for i in range(4)]
    r.shuffle(bases)
    if ver == "1":
        for i, b in enumerate(bases):
            o[f"h{i + 1}"] = str(b)
        return {k: str(v) for k, v in o.items()}
    o.update(s3=r.randint(15, 60), s4=r.randint(15, 60), i1=f"<r {r.randint(60, 140)}>")
    if ver == "3":
        # طبق مستندات Amnezia با Header Protection بهتر است H1-H4 مقدار استاندارد 1..4 بماند
        for i in range(4):
            o[f"h{i + 1}"] = str(i + 1)
        o["hpk"] = gen_psk()
        lo = r.randint(8, 20); o["cpa"] = f"{lo}-{lo + r.randint(10, 30)}"
        lo = r.randint(100, 115); o["rekey_after"] = f"{lo}-{lo + r.randint(5, 15)}"
        lo = r.randint(3, 4); o["rekey_timeout"] = f"{lo}-{lo + r.randint(1, 3)}"
        lo = r.randint(165, 175); o["reject_after"] = f"{lo}-{lo + r.randint(20, 70)}"
        lo = r.randint(10, 13); o["keepalive_timeout"] = f"{lo}-{lo + r.randint(3, 8)}"
        lo = r.randint(15, 18); o["max_hs"] = f"{lo}-{lo + r.randint(3, 6)}"
    else:
        for i, b in enumerate(bases):
            o[f"h{i + 1}"] = f"{b}-{b + r.randint(1000, 500000)}"
    return {k: str(v) for k, v in o.items()}


def _range(v, label, lo, hi):
    v = str(v or "").strip().replace(" ", "")
    if not v:
        return "", None
    m = re.fullmatch(r"(\d+)(?:-(\d+))?", v)
    if not m:
        raise Err(f"{label}: باید عدد یا بازه low-high باشد")
    a = int(m.group(1)); b = int(m.group(2) or a)
    if a > b or a < lo or b > hi:
        raise Err(f"{label}: مقدار باید بین {lo} و {hi} باشد و low ≤ high")
    return v, (a, b)


def parse_obf(d):
    d = {k: ("" if d.get(k) is None else str(d.get(k)).strip()) for k in OBF_ORDER}
    core = ["jc", "jmin", "jmax", "s1", "s2", "h1", "h2", "h3", "h4"]
    if any(not d[k] for k in core):          # پارامترهای اصلی خالی → خودکار ساخته شود
        g = gen_obf("1")
        for k in core:
            d[k] = d[k] or g[k]
    o = {}
    jc = num(d["jc"], 0, 1, 128, "Jc"); jmin = num(d["jmin"], 0, 0, 1280, "Jmin"); jmax = num(d["jmax"], 0, 1, 1280, "Jmax")
    if jmin >= jmax:
        raise Err("Jmin باید کوچکتر از Jmax باشد")
    s1 = num(d["s1"], 0, 0, 1132, "S1"); s2 = num(d["s2"], 0, 0, 1188, "S2")
    if s1 + 56 == s2:
        raise Err("S1 + 56 نباید با S2 برابر باشد")
    o.update(jc=str(jc), jmin=str(jmin), jmax=str(jmax), s1=str(s1), s2=str(s2))
    for k in ("s3", "s4"):
        if d[k]:
            o[k] = str(num(d[k], 0, 0, 1280, k.upper()))
    spans = []
    for k in ("h1", "h2", "h3", "h4"):
        v, sp = _range(d[k], k.upper(), 1, 2 ** 32 - 1)
        o[k] = v; spans.append(sp)
    spans.sort()
    for a, b in zip(spans, spans[1:]):
        if b[0] <= a[1]:
            raise Err("بازه‌های H1 تا H4 باید از هم جدا باشند و هم‌پوشانی نداشته باشند")
    for k in ("i1", "i2", "i3", "i4", "i5"):
        if d[k]:
            if not CPS_RE.fullmatch(d[k]):
                raise Err(f"{k.upper()}: فرمت بسته امضا نامعتبر است (مثال <r 100> یا <b 0xAABB><r 50><t>)")
            o[k] = d[k]
    if d["hpk"]:
        o["hpk"] = check_key(d["hpk"], "HeaderProtectionKey")
        for k in ("s1", "s2", "s3", "s4"):
            if int(o.get(k, 0)) < 12:
                raise Err("با HeaderProtectionKey همه‌ی S1 تا S4 باید حداقل ۱۲ باشند")
    for k in OBF_RANGES:
        v, _ = _range(d[k], OBF_NAME[k], 0, 65535)
        if v:
            o[k] = v
    return o


# ------------------------------ اینباند: اعتبارسنجی ------------------------------
IB_COLS = ["name", "remark", "port", "private_key", "public_key", "address4", "address6", "endpoint",
           "endpoint_port", "dns", "mtu", "table_", "fwmark", "pre_up", "post_up", "pre_down", "post_down",
           "auto_rules", "nat_iface", "use_psk", "client_allowed_ips", "client_keepalive", "client_mtu", "obf", "exclude_sub",
           "proto", "psk", "ovpn", "pki", "xcfg", "node_id"]


def inbound_defaults():
    names = {r["name"] for r in q("SELECT name FROM inbounds")}
    ports = {r["port"] for r in q("SELECT port FROM inbounds")}
    nets = [r["address4"].rsplit(".", 1)[0] for r in q("SELECT address4 FROM inbounds")]
    i = 0
    while f"wg{i}" in names:
        i += 1
    port = 51820
    while port in ports:
        port += 1
    n = 8
    while f"10.{n}.0" in nets:
        n += 1
    return dict(name=f"wg{i}", remark="", port=port, address4=f"10.{n}.0.1/24", address6="", private_key="",
                endpoint="", endpoint_port=0, dns="1.1.1.1, 1.0.0.1", mtu=1420, client_mtu=0,
                client_allowed_ips="0.0.0.0/0, ::/0", client_keepalive=25, use_psk=1, table_="", fwmark="",
                auto_rules=1, nat_iface="", pre_up="", post_up="", pre_down="", post_down="",
                address6_hint=f"fd42:42:{i}::1/64", exclude_sub=0, obf_enabled=0, obf={}, obf_ver="3",
                proto="wg", psk=secrets.token_urlsafe(9), ovpn=dict(OVPN_DEFAULT), ovpn_port=1194,
                xcfg=dict(XRAY_DEFAULT), xcfg_port=443)


OVPN_DIR, OVPN_RUN = "/etc/openvpn/server", "/run/openvpn-server"
OVPN_CIPHERS = ("AES-256-GCM", "AES-128-GCM", "CHACHA20-POLY1305", "AES-256-CBC", "AES-128-CBC")
OVPN_DEFAULT = dict(transport="udp", cipher="AES-256-GCM", keytype="ec", tlscrypt=1, redirect=1, routes="",
                    legacy=0, extra_server="", extra_client="")
OVPN_BLOCK = {"script-security", "up", "down", "plugin", "route-up", "route-pre-down", "ipchange", "learn-address",
              "auth-user-pass-verify", "client-connect", "client-disconnect", "tls-verify", "up-restart", "management",
              "config", "daemon", "log", "log-append", "writepid", "cd", "chroot", "setenv", "setenv-safe", "engine",
              "tmp-dir", "status", "client-config-dir", "ccd-exclusive", "dev", "dev-type", "port", "proto", "server",
              "ca", "cert", "key", "tls-crypt", "tls-auth", "dh", "remote", "client", "pull", "ifconfig-pool-persist"}


def ovpn_of(ib):
    try:
        o = json.loads(ib["ovpn"]) if ib["ovpn"] else {}
    except Exception:
        o = {}
    return {**OVPN_DEFAULT, **o}


def pki_of(ib):
    try:
        return json.loads(ib["pki"]) if ib["pki"] else {}
    except Exception:
        return {}


def _extra_lines(sv, label):
    out = []
    for ln in lines(sv):
        tok = ln.split()[0].lstrip("-").lower()
        if tok in OVPN_BLOCK or ln.startswith("<") or len(ln) > 300:
            raise Err(f"{label}: دستور «{tok}» مجاز نیست (توسط پنل مدیریت می‌شود یا ناامن است)")
        out.append(ln)
    return "\n".join(out)


def _ssl(args, timeout=90):
    rc, o, e = run(["openssl"] + args, timeout=timeout)
    if rc != 0:
        raise Err("openssl: " + ((e or o).strip()[-220:] or "خطا"))
    return o


def _newkey(kt):
    return ["-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1"] if kt == "ec" else ["-newkey", "rsa:2048"]


def ovpn_sign(pki, cn, server, kt):
    """گواهی تکی با CA اینباند؛ برمی‌گرداند (crt, key)"""
    if not shutil.which("openssl"):
        raise Err("openssl نصب نیست (apt install openssl)")
    with tempfile.TemporaryDirectory() as d:
        P = lambda n: os.path.join(d, n)
        for n, k in (("ca.crt", "ca_crt"), ("ca.key", "ca_key")):
            with open(P(n), "w") as f:
                f.write(pki[k])
        with open(P("ext"), "w") as f:
            f.write("basicConstraints=CA:FALSE\n" + ("keyUsage=digitalSignature,keyEncipherment,keyAgreement\nextendedKeyUsage=serverAuth\n"
                                                      if server else "keyUsage=digitalSignature\nextendedKeyUsage=clientAuth\n"))
        _ssl(["req", "-new"] + _newkey(kt) + ["-nodes", "-keyout", P("k"), "-out", P("r"), "-subj", f"/CN={cn}"])
        _ssl(["x509", "-req", "-in", P("r"), "-CA", P("ca.crt"), "-CAkey", P("ca.key"), "-set_serial", "0x" + secrets.token_hex(8),
              "-out", P("c"), "-days", "3650", "-sha256", "-extfile", P("ext")])
        return _read(P("c")), _read(P("k"))


def ovpn_make_pki(name, kt):
    if not shutil.which("openssl"):
        raise Err("openssl نصب نیست (apt install openssl)")
    with tempfile.TemporaryDirectory() as d:
        P = lambda n: os.path.join(d, n)
        _ssl(["req", "-x509"] + _newkey(kt) + ["-nodes", "-keyout", P("ca.key"), "-out", P("ca.crt"), "-days", "3650", "-sha256",
             "-subj", f"/CN=SepiPanel-CA-{name}", "-addext", "basicConstraints=critical,CA:TRUE",
             "-addext", "keyUsage=critical,keyCertSign,cRLSign"])
        pki = dict(ca_crt=_read(P("ca.crt")), ca_key=_read(P("ca.key")))
    pki["srv_crt"], pki["srv_key"] = ovpn_sign(pki, "server", True, kt)
    h = secrets.token_hex(256)
    pki["tc"] = "-----BEGIN OpenVPN Static key V1-----\n" + "\n".join(h[i:i + 32] for i in range(0, 512, 32)) \
                + "\n-----END OpenVPN Static key V1-----\n"
    return pki


def parse_ovpn(d, cur=None):
    cid = cur["id"] if cur else 0
    name = str(d.get("name", "")).strip()
    if not re.fullmatch(r"[A-Za-z0-9_=+.\-]{1,15}", name):
        raise Err("نام اینباند باید ۱ تا ۱۵ حرف انگلیسی/عدد/_ - . باشد")
    if q("SELECT 1 FROM inbounds WHERE name=? AND id!=?", (name, cid), True):
        raise Err("این نام قبلاً استفاده شده")
    port = num(d.get("port"), 0, 1, 65535, "پورت")
    if not port:
        raise Err("پورت لازم است")
    if q("SELECT 1 FROM inbounds WHERE port=? AND id!=? AND COALESCE(node_id,0)=0", (port, cid), True):
        raise Err("این پورت برای اینباند دیگری استفاده شده")
    if port in (500, 4500, 1701) and q("SELECT 1 FROM inbounds WHERE proto='l2tp'", (), True):
        raise Err("پورت‌های 500، 4500 و 1701 برای L2TP رزرو است")
    try:
        a4 = ipaddress.ip_interface(str(d.get("address4", "")).strip())
        assert a4.version == 4 and a4.network.prefixlen <= 29
    except Exception:
        raise Err("آدرس IPv4 نامعتبر است (مثال 10.10.0.1/24)")
    a4 = ipaddress.ip_interface(f"{a4.network.network_address + 1}/{a4.network.prefixlen}")   # سرور همیشه اولین آی‌پی ساب‌نت
    ov = d.get("ovpn") or {}
    old = ovpn_of(cur) if cur else dict(OVPN_DEFAULT)
    g = lambda k: ov.get(k, old.get(k))
    transport = str(g("transport") or "udp")
    if transport not in ("udp", "tcp"):
        raise Err("ترنسپورت باید udp یا tcp باشد")
    cipher = str(g("cipher") or "AES-256-GCM")
    if cipher not in OVPN_CIPHERS:
        raise Err("رمزنگاری نامعتبر است")
    kt = str(g("keytype") or "ec")
    if kt not in ("ec", "rsa"):
        raise Err("نوع کلید نامعتبر است")
    settings = dict(transport=transport, cipher=cipher, keytype=kt, tlscrypt=1 if g("tlscrypt") else 0,
                    redirect=1 if g("redirect") else 0, legacy=1 if g("legacy") else 0,
                    routes=check_cidrs(g("routes"), "مسیرهای اضافه"),
                    extra_server=_extra_lines(g("extra_server"), "دستورات سرور"),
                    extra_client=_extra_lines(g("extra_client"), "دستورات کلاینت"))
    ep = str(d.get("endpoint", "") or "").strip()
    if ep and not re.fullmatch(r"[A-Za-z0-9.\-:\[\]_]+", ep):
        raise Err("آدرس Endpoint نامعتبر است")
    mtu = num(d.get("mtu"), 0, 0, 1600, "MTU")
    if 0 < mtu < 576:
        raise Err("MTU باید حداقل ۵۷۶ باشد")
    nat = str(d.get("nat_iface", "") or "").strip()
    if nat and not re.fullmatch(r"[A-Za-z0-9_.\-]{1,15}", nat):
        raise Err("نام اینترفیس خروجی نامعتبر است")
    if cur and cur["pki"] and not d.get("regen_keys"):
        pki = cur["pki"]
    else:
        pki = json.dumps(ovpn_make_pki(name, kt))
    return dict(proto="ovpn", psk="", obf="", ovpn=json.dumps(settings), pki=pki, xcfg="",
                exclude_sub=1 if d.get("exclude_sub") else 0, name=name, remark=oneline(d.get("remark"))[:100],
                port=port, private_key="", public_key="", address4=str(a4), address6="", endpoint=ep,
                endpoint_port=num(d.get("endpoint_port"), 0, 0, 65535, "پورت Endpoint"), dns=check_dns(d.get("dns")),
                mtu=mtu, table_="", fwmark="", pre_up="", post_up="", pre_down="", post_down="",
                auto_rules=1 if d.get("auto_rules") else 0, nat_iface=nat, use_psk=0,
                client_allowed_ips="0.0.0.0/0, ::/0", client_keepalive=0, client_mtu=0)


def parse_l2tp(d, cur=None):
    cid = cur["id"] if cur else 0
    name = str(d.get("name", "")).strip()
    if not re.fullmatch(r"[A-Za-z0-9_=+.\-]{1,15}", name):
        raise Err("نام اینباند باید ۱ تا ۱۵ حرف انگلیسی/عدد/_ - . باشد")
    if q("SELECT 1 FROM inbounds WHERE name=? AND id!=?", (name, cid), True):
        raise Err("این نام قبلاً استفاده شده")
    if q("SELECT 1 FROM inbounds WHERE proto='l2tp' AND id!=?", (cid,), True):
        raise Err("فقط یک اینباند L2TP می‌توان ساخت (یک سرویس xl2tpd/IPsec روی سرور)؛ کلاینت‌های بیشتر را به همان اضافه کنید")
    if q("SELECT 1 FROM inbounds WHERE port=1701 AND id!=?", (cid,), True):
        raise Err("پورت 1701 برای اینباند دیگری استفاده شده")
    try:
        a4 = ipaddress.ip_interface(str(d.get("address4", "")).strip())
        assert a4.version == 4 and a4.network.prefixlen <= 29
    except Exception:
        raise Err("آدرس IPv4 نامعتبر است (مثال 10.9.0.1/24)")
    psk = str(d.get("psk") or "").strip() or (cur["psk"] if cur and cur["psk"] else secrets.token_urlsafe(9))
    if not re.fullmatch(r"[A-Za-z0-9._\-+=@#%^*!~]{6,64}", psk):
        raise Err("کلید IPsec باید ۶ تا ۶۴ کاراکتر از حروف انگلیسی/عدد/نمادهای ._-+=@#%^*!~ باشد")
    ep = str(d.get("endpoint", "") or "").strip()
    if ep and not re.fullmatch(r"[A-Za-z0-9.\-:\[\]_]+", ep):
        raise Err("آدرس Endpoint نامعتبر است")
    mtu = num(d.get("mtu"), 0, 0, 1500, "MTU")
    if 0 < mtu < 576:
        raise Err("MTU باید حداقل ۵۷۶ باشد")
    nat = str(d.get("nat_iface", "") or "").strip()
    if nat and not re.fullmatch(r"[A-Za-z0-9_.\-]{1,15}", nat):
        raise Err("نام اینترفیس خروجی نامعتبر است")
    return dict(proto="l2tp", psk=psk, obf="", ovpn="", pki="", xcfg="", exclude_sub=1 if d.get("exclude_sub") else 0,
                name=name, remark=oneline(d.get("remark"))[:100], port=1701, private_key="", public_key="",
                address4=str(a4), address6="", endpoint=ep, endpoint_port=0, dns=check_dns(d.get("dns")),
                mtu=mtu, table_="", fwmark="", pre_up="", post_up="", pre_down="", post_down="",
                auto_rules=1 if d.get("auto_rules") else 0, nat_iface=nat, use_psk=0,
                client_allowed_ips="0.0.0.0/0, ::/0", client_keepalive=0, client_mtu=0)


def _ib_node(d, cur=None):
    """نود اینباند: در ساخت از فرم می‌آید، بعد از ساخت قابل تغییر نیست"""
    if cur is not None:
        return ib_node(cur)
    nid = num(d.get("node_id"), 0, 0, None, "نود")
    if nid and not q("SELECT 1 FROM nodes WHERE id=?", (nid,), True):
        raise Err("نود انتخاب‌شده پیدا نشد")
    return nid


def parse_inbound(d, cur=None):
    proto = cur["proto"] if cur else str(d.get("proto") or "wg")
    nid = _ib_node(d, cur) if proto == "vless" else 0        # نود فقط برای VLESS (Xray) معنی دارد
    o = _parse_inbound_core(d, cur)
    o["node_id"] = nid
    return o


def _parse_inbound_core(d, cur=None):
    proto = cur["proto"] if cur else str(d.get("proto") or "wg")
    if proto not in ("wg", "l2tp", "ovpn", "vless"):
        raise Err("پروتکل نامعتبر است")
    if proto == "vless":
        return parse_vless(d, cur)
    if proto == "l2tp":
        return parse_l2tp(d, cur)
    if proto == "ovpn":
        return parse_ovpn(d, cur)
    cid = cur["id"] if cur else 0
    name = str(d.get("name", "")).strip()
    if not re.fullmatch(r"[A-Za-z0-9_=+.\-]{1,15}", name):
        raise Err("نام اینترفیس باید ۱ تا ۱۵ حرف انگلیسی/عدد/_ - . باشد")
    if q("SELECT 1 FROM inbounds WHERE name=? AND id!=?", (name, cid), True):
        raise Err("این نام اینترفیس قبلاً استفاده شده")
    port = num(d.get("port"), 0, 1, 65535, "پورت")
    if not port:
        raise Err("پورت لازم است")
    if q("SELECT 1 FROM inbounds WHERE port=? AND id!=? AND COALESCE(node_id,0)=0", (port, cid), True):
        raise Err("این پورت برای اینباند دیگری استفاده شده")
    try:
        a4 = ipaddress.ip_interface(str(d.get("address4", "")).strip())
        assert a4.version == 4 and a4.network.prefixlen <= 30
    except Exception:
        raise Err("آدرس IPv4 نامعتبر است (مثال 10.8.0.1/24)")
    a6s = str(d.get("address6", "") or "").strip()
    a6 = None
    if a6s:
        try:
            a6 = ipaddress.ip_interface(a6s)
            assert a6.version == 6 and a6.network.prefixlen <= 126
        except Exception:
            raise Err("آدرس IPv6 نامعتبر است (مثال fd42:42:0::1/64)")
    if cur:
        has = q("SELECT 1 FROM client_inbound WHERE inbound_id=?", (cid,), True)
        if has:
            if ipaddress.ip_interface(cur["address4"]).network != a4.network:
                raise Err("تا وقتی کلاینت دارد، ساب‌نت IPv4 قابل تغییر نیست (فقط IP سرور داخل همان ساب‌نت)")
            if cur["address6"] and a6 and ipaddress.ip_interface(cur["address6"]).network != a6.network:
                raise Err("تا وقتی کلاینت دارد، ساب‌نت IPv6 قابل تغییر نیست")
            used = {r["ip4"] for r in q("SELECT ip4 FROM client_inbound WHERE inbound_id=?", (cid,))}
            if str(a4.ip) in used:
                raise Err("IP سرور با IP یکی از کلاینت‌ها یکی است")
    priv = str(d.get("private_key", "") or "").strip()
    if cur and d.get("regen_keys"):
        priv = gen_private()
    elif priv:
        check_key(priv, "کلید خصوصی")
    elif cur:
        priv = cur["private_key"]
    else:
        priv = gen_private()
    ep = str(d.get("endpoint", "") or "").strip()
    if ep and not re.fullmatch(r"[A-Za-z0-9.\-:\[\]_]+", ep):
        raise Err("آدرس Endpoint نامعتبر است")
    mtu = num(d.get("mtu"), 0, 0, 9200, "MTU")
    cmtu = num(d.get("client_mtu"), 0, 0, 9200, "MTU کلاینت")
    if (0 < mtu < 576) or (0 < cmtu < 576):
        raise Err("MTU باید حداقل ۵۷۶ باشد")
    tbl = str(d.get("table_", "") or "").strip()
    if tbl and not re.fullmatch(r"off|auto|\d+|[A-Za-z0-9_\-]+", tbl):
        raise Err("مقدار Table نامعتبر است")
    fw = str(d.get("fwmark", "") or "").strip()
    if fw and not re.fullmatch(r"off|0x[0-9a-fA-F]+|\d+", fw):
        raise Err("مقدار FwMark نامعتبر است")
    nat = str(d.get("nat_iface", "") or "").strip()
    if nat and not re.fullmatch(r"[A-Za-z0-9_.\-]{1,15}", nat):
        raise Err("نام اینترفیس خروجی نامعتبر است")
    obf = parse_obf(d.get("obf") or {}) if d.get("obf_enabled") else {}
    if port in (500, 4500) and q("SELECT 1 FROM inbounds WHERE proto='l2tp'", (), True):
        raise Err("پورت 500 و 4500 برای IPsec اینباند L2TP رزرو است")
    return dict(
        proto="wg", psk="", ovpn="", pki="", xcfg="",
        obf=json.dumps(obf) if obf else "", exclude_sub=1 if d.get("exclude_sub") else 0,
        name=name, remark=oneline(d.get("remark"))[:100], port=port, private_key=priv,
        public_key=pub_from_private(priv), address4=str(a4), address6=str(a6) if a6 else "", endpoint=ep,
        endpoint_port=num(d.get("endpoint_port"), 0, 0, 65535, "پورت Endpoint"), dns=check_dns(d.get("dns")),
        mtu=mtu, table_=tbl, fwmark=fw,
        pre_up="\n".join(lines(d.get("pre_up"))), post_up="\n".join(lines(d.get("post_up"))),
        pre_down="\n".join(lines(d.get("pre_down"))), post_down="\n".join(lines(d.get("post_down"))),
        auto_rules=1 if d.get("auto_rules") else 0, nat_iface=nat, use_psk=1 if d.get("use_psk") else 0,
        client_allowed_ips=check_cidrs(d.get("client_allowed_ips") or "0.0.0.0/0, ::/0", "AllowedIPs کلاینت"),
        client_keepalive=num(d.get("client_keepalive"), 0, 0, 65535, "Keepalive"), client_mtu=cmtu)


# ------------------------------ تولید کانفیگ ------------------------------
def usage_state(c):
    if c["expiry"] and now() >= c["expiry"]:
        return "expired"
    if c["limit_bytes"] and (c["up_bytes"] + c["down_bytes"]) >= c["limit_bytes"]:
        return "limit"
    return "active"


def admin_state(a):
    if not a["enabled"]:
        return "disabled"
    if a["expiry"] and now() >= a["expiry"]:
        return "expired"
    if a["limit_bytes"] and a["used_bytes"] >= a["limit_bytes"]:
        return "limit"
    return "active"


ADM_STATE = {}
KEY_STATE = {}


def admin_inbounds(aid):
    return {r["inbound_id"] for r in q(
        "SELECT ci.inbound_id FROM client_inbound ci JOIN clients c ON c.id=ci.client_id WHERE c.owner_id=?", (aid,))}


def client_state(c):
    if not c["enabled"]:
        return c["reason"] or "disabled"
    st = usage_state(c)
    if st != "active":
        return st
    oid = c["owner_id"] if "owner_id" in c.keys() else 0
    if oid:
        a = q("SELECT * FROM admins WHERE id=?", (oid,), True)
        if a and admin_state(a) != "active":
            return "admin"      # حجم/اعتبار ادمین صاحب کلاینت تمام شده یا ادمین غیرفعال است
    kid = c["key_id"] if "key_id" in c.keys() else 0
    if kid:
        k = q("SELECT * FROM api_keys WHERE id=?", (kid,), True)
        if k and key_quota_state(k) != "active":
            return "key"        # حجم/زمان کلید API ساخنده‌ی کلاینت تمام شده
    return "active"


def auto_rule_lines(ib):
    out = ib["nat_iface"] or detect_iface()
    n4 = ipaddress.ip_interface(ib["address4"]).network
    up = ["sysctl -w net.ipv4.ip_forward=1",
          "iptables -I FORWARD -i %i -j ACCEPT", "iptables -I FORWARD -o %i -j ACCEPT",
          f"iptables -t nat -A POSTROUTING -s {n4} -o {out} -j MASQUERADE"]
    down = ["iptables -D FORWARD -i %i -j ACCEPT", "iptables -D FORWARD -o %i -j ACCEPT",
            f"iptables -t nat -D POSTROUTING -s {n4} -o {out} -j MASQUERADE"]
    if ib["address6"]:
        n6 = ipaddress.ip_interface(ib["address6"]).network
        up += ["sysctl -w net.ipv6.conf.all.forwarding=1",
               "ip6tables -I FORWARD -i %i -j ACCEPT", "ip6tables -I FORWARD -o %i -j ACCEPT",
               f"ip6tables -t nat -A POSTROUTING -s {n6} -o {out} -j MASQUERADE"]
        down += ["ip6tables -D FORWARD -i %i -j ACCEPT", "ip6tables -D FORWARD -o %i -j ACCEPT",
                 f"ip6tables -t nat -D POSTROUTING -s {n6} -o {out} -j MASQUERADE"]
    return up, down


def server_conf(ib, mask=False):
    L = ["[Interface]", f"# {oneline(ib['remark']) or ib['name']}"]
    L.append("Address = " + ib["address4"] + (", " + ib["address6"] if ib["address6"] else ""))
    L.append(f"ListenPort = {ib['port']}")
    L.append("PrivateKey = " + ("********" if mask else ib["private_key"]))
    if ib["mtu"]:
        L.append(f"MTU = {ib['mtu']}")
    if ib["table_"]:
        L.append(f"Table = {ib['table_']}")
    if ib["fwmark"]:
        L.append(f"FwMark = {ib['fwmark']}")
    for k, v in obf_lines(ib):
        L.append(f"{k} = {v}")
    au, ad = auto_rule_lines(ib) if ib["auto_rules"] else ([], [])
    for key, extra_first, auto in (("PreUp", lines(ib["pre_up"]), []), ("PostUp", au, lines(ib["post_up"])),
                                   ("PreDown", lines(ib["pre_down"]), []), ("PostDown", lines(ib["post_down"]), ad)):
        for cmd in extra_first + auto:
            L.append(f"{key} = {cmd}")
    rows = q("""SELECT c.*, ci.ip4, ci.ip6, ci.psk, ci.extra_allowed FROM client_inbound ci
                JOIN clients c ON c.id=ci.client_id WHERE ci.inbound_id=? ORDER BY c.id""", (ib["id"],))
    for r in rows:
        if client_state(r) != "active":
            continue
        allowed = [r["ip4"] + "/32"] + ([r["ip6"] + "/128"] if r["ip6"] else [])
        if r["extra_allowed"]:
            allowed += [p for p in r["extra_allowed"].split(", ") if p]
        L += ["", "[Peer]", f"# {oneline(r['name'])}", f"PublicKey = {r['public_key']}"]
        if r["psk"]:
            L.append("PresharedKey = " + ("********" if mask else r["psk"]))
        L.append("AllowedIPs = " + ", ".join(allowed))
    return "\n".join(L) + "\n"


def ep_host(ib):
    h = ib["endpoint"]
    if not h and ib_node(ib):
        n = q("SELECT address FROM nodes WHERE id=?", (ib_node(ib),), True)
        h = n["address"] if n else ""
    if not h:
        try:
            h = urlsplit("//" + request.host).hostname or "SERVER_IP"
        except Exception:
            h = "SERVER_IP"
    return h


def endpoint_str(ib):
    h = ep_host(ib)
    if ":" in h and not h.startswith("["):
        h = f"[{h}]"
    return f"{h}:{ib['endpoint_port'] or ib['port']}"


def link_params(ci, ib):
    addr = ci["ip4"] + "/32" + (f", {ci['ip6']}/128" if ci["ip6"] else "")
    dns = ci["dns"] or ib["dns"]
    mtu = ci["mtu"] or ib["client_mtu"] or ib["mtu"]
    ka = ib["client_keepalive"] if ci["keepalive"] < 0 else ci["keepalive"]
    allowed = ci["allowed_ips"] or ib["client_allowed_ips"] or "0.0.0.0/0, ::/0"
    return addr, dns, mtu, ka, allowed


def l2tp_info(c, ci, ib):
    return dict(type="L2TP/IPsec PSK", server=ep_host(ib), username=ci["l2tp_user"], password=ci["l2tp_pass"], psk=ib["psk"])


def build_conf(c, ci, ib):
    if is_vless(ib):
        return vless_link(c, ci, ib) + "\n"
    if is_ovpn(ib):
        return ovpn_client_conf(c, ci, ib)
    if is_l2tp(ib):
        i = l2tp_info(c, ci, ib)
        return (f"# L2TP/IPsec PSK — {oneline(c['name'])} @ {ib['name']}\nServer = {i['server']}\n"
                f"Username = {i['username']}\nPassword = {i['password']}\nIPsec PSK = {i['psk']}\n")
    addr, dns, mtu, ka, allowed = link_params(ci, ib)
    L = ["[Interface]", f"# {oneline(c['name'])} @ {ib['name']}", f"PrivateKey = {c['private_key']}", f"Address = {addr}"]
    if dns:
        L.append(f"DNS = {dns}")
    if mtu:
        L.append(f"MTU = {mtu}")
    for k, v in obf_lines(ib):
        L.append(f"{k} = {v}")
    L += ["", "[Peer]", f"PublicKey = {ib['public_key']}"]
    if ci["psk"]:
        L.append(f"PresharedKey = {ci['psk']}")
    L += [f"AllowedIPs = {allowed}", f"Endpoint = {endpoint_str(ib)}"]
    if ka:
        L.append(f"PersistentKeepalive = {ka}")
    return "\n".join(L) + "\n"


def build_uri(c, ci, ib):
    if is_vless(ib):
        return vless_link(c, ci, ib)
    addr, dns, mtu, ka, allowed = link_params(ci, ib)
    host = ep_host(ib)
    if ":" in host and not host.startswith("["):
        host = f"[{host}]"
    P = [("publickey", quote(ib["public_key"], safe="")), ("address", quote(addr.replace(" ", ""), safe=",/:"))]
    if ci["psk"]:
        P.append(("presharedkey", quote(ci["psk"], safe="")))
    if mtu:
        P.append(("mtu", str(mtu)))
    if ka:
        P.append(("keepalive", str(ka)))
    return (f"wireguard://{quote(c['private_key'], safe='')}@{host}:{ib['endpoint_port'] or ib['port']}?"
            + "&".join(f"{k}={v}" for k, v in P) + "#" + quote(f"{c['name']}-{ib['name']}"))


# ------------------------------ VLESS (Xray-core) ------------------------------
XRAY_BIN, XRAY_DIR = "/usr/local/bin/xray", "/etc/sepipanel/xray"
XRAY_UNIT = "/etc/systemd/system/sepipanel-xray@.service"
XRAY_TRANSPORTS = ("tcp", "ws", "grpc", "httpupgrade", "xhttp", "kcp")
XRAY_FP = ("chrome", "firefox", "safari", "ios", "android", "edge", "360", "qq", "random", "randomized", "")
XRAY_DEFAULT = dict(listen="0.0.0.0", transport="tcp", security="reality", flow="xtls-rprx-vision", packet_encoding="",
                    fp="chrome", reality_dest="www.microsoft.com:443", server_names="www.microsoft.com", short_ids="",
                    spider_x="/", reality_pub="", tls_mode="panel", tls_cert="", tls_key="", sni="", alpn="h2,http/1.1",
                    min_ver="1.2", reject_sni=0, allow_insecure=0, path="/", host="", service_name="", authority="",
                    multi_mode=0, xhttp_mode="auto", tcp_header="none", kcp_header="none", kcp_seed="",
                    fallback_dest="", fallback_xver=0, sniffing=1, route_only=0, block_bt=0, block_private=0,
                    domain_strategy="AsIs", tfo=0, extra_stream="")
PRIVATE_CIDRS = ["0.0.0.0/8", "10.0.0.0/8", "100.64.0.0/10", "127.0.0.0/8", "169.254.0.0/16", "172.16.0.0/12", "192.0.0.0/24",
                 "192.168.0.0/16", "198.18.0.0/15", "224.0.0.0/4", "240.0.0.0/4", "::1/128", "fc00::/7", "fe80::/10"]


def _x25519(k, u=9):
    """X25519 خالص پایتون (RFC 7748) تا ساخت کلید Reality به xray نیاز نداشته باشد"""
    p, a24 = 2 ** 255 - 19, 121665
    kb = bytearray(k); kb[0] &= 248; kb[31] &= 127; kb[31] |= 64
    k = int.from_bytes(kb, "little")
    x1, x2, z2, x3, z3, swap = u, 1, 0, u, 1, 0
    for t in range(254, -1, -1):
        kt = (k >> t) & 1
        swap ^= kt
        if swap:
            x2, x3, z2, z3 = x3, x2, z3, z2
        swap = kt
        A, B = (x2 + z2) % p, (x2 - z2) % p
        AA, BB = A * A % p, B * B % p
        E = (AA - BB) % p
        C, D = (x3 + z3) % p, (x3 - z3) % p
        DA, CB = D * A % p, C * B % p
        x3, z3 = (DA + CB) ** 2 % p, x1 * (DA - CB) ** 2 % p
        x2, z2 = AA * BB % p, E * (AA + a24 * E) % p
    if swap:
        x2, x3, z2, z3 = x3, x2, z3, z2
    return (x2 * pow(z2, p - 2, p) % p).to_bytes(32, "little")


def _b64u(b):
    return base64.urlsafe_b64encode(b).decode().rstrip("=")


def reality_keypair(priv_b64=""):
    if priv_b64:
        try:
            raw = base64.urlsafe_b64decode(priv_b64 + "=" * (-len(priv_b64) % 4))
            assert len(raw) == 32
        except Exception:
            raise Err("کلید خصوصی Reality نامعتبر است (باید base64url و ۴۳ کاراکتر باشد)")
    else:
        raw = bytearray(secrets.token_bytes(32)); raw[0] &= 248; raw[31] &= 127; raw[31] |= 64; raw = bytes(raw)
    return _b64u(raw), _b64u(_x25519(raw))


def xcfg_of(ib):
    try:
        o = json.loads(ib["xcfg"]) if ib["xcfg"] else {}
    except Exception:
        o = {}
    return {**XRAY_DEFAULT, **o}


def gen_short_id():
    return secrets.token_hex(8)


def check_reality_dest(host, port=443, sni=None, timeout=6):
    """از سمت این سرور به dest وصل می‌شود: TLS 1.3 و h2 داشته باشد (شرط Reality)"""
    host = str(host or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9.\-]{1,253}", host):
        raise Err("نام دامنه نامعتبر است")
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
    try:
        ctx.set_alpn_protocols(["h2", "http/1.1"])
    except Exception:
        pass
    t0 = time.time()
    try:
        with socket.create_connection((host, int(port)), timeout=timeout) as sk:
            with ctx.wrap_socket(sk, server_hostname=sni or host) as ss:
                ver, alpn = ss.version(), ss.selected_alpn_protocol()
    except Exception as e:
        return dict(ok=False, error=f"اتصال/هندشیک ناموفق: {str(e)[:120]}")
    ms = int((time.time() - t0) * 1000)
    good = ver == "TLSv1.3" and alpn == "h2"
    return dict(ok=good, tls=ver, alpn=alpn or "-", ms=ms,
                note="مناسب Reality است" if good else "برای Reality باید TLS 1.3 و h2 داشته باشد؛ دامنهٔ دیگری امتحان کنید")


def xray_bin():
    return shutil.which("xray") or (XRAY_BIN if os.path.exists(XRAY_BIN) else None)


def ensure_xray():
    if xray_bin():
        return ""
    arch = {"x86_64": "64", "amd64": "64", "aarch64": "arm64-v8a", "arm64": "arm64-v8a", "armv7l": "arm32-v7a",
            "i686": "32", "i386": "32", "s390x": "s390x"}.get(platform.machine().lower())
    if not arch:
        return f"معماری {platform.machine()} پشتیبانی نمی‌شود؛ xray را دستی نصب کنید"
    url = f"https://github.com/XTLS/Xray-core/releases/latest/download/Xray-linux-{arch}.zip"
    try:
        d = tempfile.mkdtemp()
        zp = os.path.join(d, "x.zip")
        with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "sepipanel"}), timeout=120) as r, open(zp, "wb") as f:
            shutil.copyfileobj(r, f)
        with zipfile.ZipFile(zp) as z:
            with z.open("xray") as src, open(XRAY_BIN + ".new", "wb") as dst:
                shutil.copyfileobj(src, dst)
        os.chmod(XRAY_BIN + ".new", 0o755)
        os.replace(XRAY_BIN + ".new", XRAY_BIN)
        shutil.rmtree(d, ignore_errors=True)
    except Exception as e:
        return f"دانلود Xray-core ناموفق بود ({str(e)[:140]}). دستی نصب کنید: bash -c \"$(curl -L https://github.com/XTLS/Xray-install/raw/main/install-release.sh)\" @ install"
    return "" if xray_bin() else "نصب Xray-core ناموفق بود"


def xray_unit_text(b):
    return f"""[Unit]
Description=SepiPanel Xray (%i)
After=network-online.target
Wants=network-online.target

[Service]
ExecStart={b} run -c {XRAY_DIR}/%i.json
Restart=on-failure
RestartSec=3
LimitNOFILE=1048576

[Install]
WantedBy=multi-user.target
"""


def ensure_xray_unit():
    b = xray_bin() or XRAY_BIN
    write_file(XRAY_UNIT, xray_unit_text(b), 0o644, backup=False)
    run(["systemctl", "daemon-reload"], timeout=20)


def xray_path(ib):
    return f"{XRAY_DIR}/{ib['name']}.json"


def xray_unit(ib):
    return f"sepipanel-xray@{ib['name']}"


def xray_up(ib):
    if ib_node(ib):
        return node_up(ib)           # وضعیت نود از آخرین بررسی SSH (در NODE_STATE) خوانده می‌شود
    return run(["systemctl", "is-active", "--quiet", xray_unit(ib)], timeout=8)[0] == 0


def xray_api_port(ib):
    used = {r["port"] for r in q("SELECT port FROM inbounds")}
    p = 31000 + int(ib["id"])
    while p in used:
        p += 1000
    return p


def xray_net(ib):
    return "udp" if xcfg_of(ib)["transport"] == "kcp" else "tcp"


def xray_email(cid, iid):
    return f"{cid}-{iid}@sp"


def _comma(s):
    return [p.strip() for p in re.split(r"[,\s]+", str(s or "")) if p.strip()]


def _selfsigned(cn, san):
    with tempfile.TemporaryDirectory() as d:
        P = lambda n: os.path.join(d, n)
        _ssl(["req", "-x509", "-newkey", "ec", "-pkeyopt", "ec_paramgen_curve:prime256v1", "-nodes", "-keyout", P("k"), "-out", P("c"),
              "-days", "3650", "-sha256", "-subj", f"/CN={cn}", "-addext", f"subjectAltName={san}"])
        return _read(P("c")), _read(P("k"))


def _is_ip(h):
    try:
        ipaddress.ip_address(h.strip("[]"))
        return True
    except ValueError:
        return False


def parse_vless(d, cur=None):
    cid = cur["id"] if cur else 0
    nid = _ib_node(d, cur)
    name = str(d.get("name", "")).strip()
    if not re.fullmatch(r"[A-Za-z0-9_=+.\-]{1,15}", name):
        raise Err("نام اینباند باید ۱ تا ۱۵ حرف انگلیسی/عدد/_ - . باشد")
    if q("SELECT 1 FROM inbounds WHERE name=? AND id!=?", (name, cid), True):
        raise Err("این نام قبلاً استفاده شده")
    port = num(d.get("port"), 0, 1, 65535, "پورت")
    if not port:
        raise Err("پورت لازم است")
    xv = d.get("xcfg") or {}
    old = xcfg_of(cur) if cur else dict(XRAY_DEFAULT)
    g = lambda k: xv.get(k, old.get(k, XRAY_DEFAULT[k]))
    strv = lambda k: str(g(k) if g(k) is not None else "").strip()
    flag = lambda k: 1 if g(k) in (True, 1, "1", "true", "on") else 0
    o = dict(XRAY_DEFAULT)
    o["transport"] = strv("transport") or "tcp"
    if o["transport"] not in XRAY_TRANSPORTS:
        raise Err("ترنسپورت نامعتبر است")
    o["security"] = strv("security") or "none"
    if o["security"] not in ("none", "tls", "reality"):
        raise Err("نوع امنیت نامعتبر است")
    t, sec = o["transport"], o["security"]
    net = "udp" if t == "kcp" else "tcp"
    if sec != "none" and t == "kcp":
        raise Err("mKCP از TLS/Reality پشتیبانی نمی‌کند؛ امنیت را none بگذارید")
    if sec == "reality" and t not in ("tcp", "grpc", "xhttp"):
        raise Err("Reality فقط با TCP، gRPC یا xHTTP کار می‌کند")
    # تداخل پورت
    pp = num(setting("panel_port"), PANEL_PORT, 1, 65535, "پورت پنل")
    if net == "tcp" and port == pp and not nid:
        raise Err("این پورت را خود پنل استفاده می‌کند")
    for r in q("SELECT * FROM inbounds WHERE id!=? AND port=? AND COALESCE(node_id,0)=?", (cid, port, nid)):
        rnet = "udp" if r["proto"] in ("wg", "l2tp") else (ovpn_of(r)["transport"] if r["proto"] == "ovpn" else xray_net(r))
        if rnet == net:
            raise Err(f"پورت {port}/{net} برای اینباند «{r['name']}» استفاده شده")
    if not nid and net == "udp" and port in (500, 4500, 1701) and q("SELECT 1 FROM inbounds WHERE proto='l2tp'", (), True):
        raise Err("پورت‌های 500، 4500 و 1701 برای L2TP رزرو است")
    lst = strv("listen") or "0.0.0.0"
    try:
        ipaddress.ip_address(lst)
    except ValueError:
        raise Err("آدرس listen باید IP معتبر باشد (0.0.0.0 یا ::)")
    o["listen"] = lst
    o["flow"] = strv("flow")
    if o["flow"] not in ("", "xtls-rprx-vision"):
        raise Err("flow نامعتبر است")
    if o["flow"] and not (t == "tcp" and sec in ("tls", "reality")):
        o["flow"] = ""          # Vision فقط روی TCP + TLS/Reality معنی دارد
    o["packet_encoding"] = strv("packet_encoding")
    if o["packet_encoding"] not in ("", "xudp", "packet"):
        raise Err("packetEncoding نامعتبر است")
    o["fp"] = strv("fp")
    if o["fp"] not in XRAY_FP:
        raise Err("fingerprint نامعتبر است")
    for k in ("path", "host", "service_name", "authority", "kcp_seed"):
        o[k] = oneline(strv(k))[:200]
    if t in ("ws", "httpupgrade", "xhttp") or (t == "tcp" and strv("tcp_header") == "http"):
        o["path"] = o["path"] or "/"
        if not o["path"].startswith("/"):
            raise Err("Path باید با / شروع شود")
    if o["host"] and not re.fullmatch(r"[A-Za-z0-9.\-,:_]{1,200}", o["host"]):
        raise Err("Host نامعتبر است")
    o["tcp_header"] = strv("tcp_header") or "none"
    if o["tcp_header"] not in ("none", "http"):
        raise Err("header تی‌سی‌پی نامعتبر است")
    o["kcp_header"] = strv("kcp_header") or "none"
    if o["kcp_header"] not in ("none", "srtp", "utp", "wechat-video", "dtls", "wireguard"):
        raise Err("header mKCP نامعتبر است")
    o["xhttp_mode"] = strv("xhttp_mode") or "auto"
    if o["xhttp_mode"] not in ("auto", "packet-up", "stream-up", "stream-one"):
        raise Err("حالت xHTTP نامعتبر است")
    o["multi_mode"] = flag("multi_mode")
    if t == "grpc" and not o["service_name"]:
        o["service_name"] = "grpc-" + secrets.token_hex(3)
    pki = pki_of(cur) if cur else {}
    regen = bool(d.get("regen_keys"))
    # --- TLS ---
    o["tls_mode"] = strv("tls_mode") or "panel"
    o["sni"] = strv("sni")
    o["alpn"] = ",".join(_comma(g("alpn")))
    o["min_ver"] = strv("min_ver") or "1.2"
    o["reject_sni"] = flag("reject_sni")
    o["allow_insecure"] = flag("allow_insecure")
    if o["sni"] and not re.fullmatch(r"[A-Za-z0-9.\-]{1,253}", o["sni"]):
        raise Err("SNI نامعتبر است")
    if o["min_ver"] not in ("1.0", "1.1", "1.2", "1.3"):
        raise Err("حداقل نسخه TLS نامعتبر است")
    for a in _comma(o["alpn"]):
        if a not in ("h3", "h2", "http/1.1"):
            raise Err("ALPN فقط h3 و h2 و http/1.1 می‌تواند باشد")
    if sec == "tls":
        if o["tls_mode"] not in ("panel", "files", "self"):
            raise Err("منبع گواهی نامعتبر است")
        if o["tls_mode"] == "panel":
            if not (setting("tls_cert") and setting("tls_key")):
                raise Err("گواهی پنل تنظیم نشده؛ از منوی sepipanel بخش Domain & SSL گواهی بگیرید یا «فایل گواهی» / «خودامضا» را انتخاب کنید")
        elif o["tls_mode"] == "files":
            o["tls_cert"], o["tls_key"] = strv("tls_cert"), strv("tls_key")
            for p_ in (o["tls_cert"], o["tls_key"]):
                if not p_.startswith("/") or (not nid and not os.path.isfile(p_)):      # روی نود، مسیر فایل مالِ خود نود است
                    raise Err(f"فایل گواهی روی سرور پیدا نشد: {p_ or '(خالی)'}")
        else:
            cn = o["sni"] or (cur["endpoint"] if cur and cur["endpoint"] else "") or "localhost"
            if regen or not pki.get("tls_crt") or pki.get("tls_cn") != cn:
                crt, key = _selfsigned(cn, ("IP:" if _is_ip(cn) else "DNS:") + cn.strip("[]"))
                pki["tls_crt"], pki["tls_key"], pki["tls_cn"] = crt, key, cn
                pki["tls_pcs"] = hashlib.sha256(ssl.PEM_cert_to_DER_cert(crt)).hexdigest()
            o["allow_insecure"] = 1       # گواهی خودامضا → کلاینت باید اعتبارسنجی را رد کند
    # --- Reality ---
    o["reality_dest"], o["server_names"], o["spider_x"] = strv("reality_dest"), "", strv("spider_x") or "/"
    if sec == "reality":
        dest = o["reality_dest"] or "www.microsoft.com:443"
        m = re.fullmatch(r"([A-Za-z0-9.\-\[\]:]+?)(?::(\d{1,5}))?", dest)
        if not m or (m.group(2) and not 1 <= int(m.group(2)) <= 65535):
            raise Err("Dest نامعتبر است (مثال www.microsoft.com:443)")
        o["reality_dest"] = dest if m.group(2) else dest + ":443"
        names = _comma(g("server_names")) or [m.group(1)]
        for n_ in names:
            if not re.fullmatch(r"(\*\.)?[A-Za-z0-9.\-]{1,253}", n_):
                raise Err(f"SNI «{n_}» نامعتبر است")
        o["server_names"] = ",".join(names)
        sids = _comma(g("short_ids")) or [gen_short_id()]
        for s_ in sids:
            if s_ != "" and not re.fullmatch(r"([0-9a-fA-F]{2}){1,8}", s_):
                raise Err("Short ID باید hex با تعداد زوج کاراکتر و حداکثر ۱۶ کاراکتر باشد")
        o["short_ids"] = ",".join(sids)
        want_priv = str(xv.get("reality_priv") or "").strip()
        if want_priv or regen or not pki.get("reality_priv"):
            pki["reality_priv"], o["reality_pub"] = reality_keypair(want_priv)
        else:
            o["reality_pub"] = old.get("reality_pub") or reality_keypair(pki["reality_priv"])[1]
        if not o["fp"]:
            o["fp"] = "chrome"
    # --- fallback ---
    o["fallback_dest"] = strv("fallback_dest")
    if o["fallback_dest"]:
        if not (t == "tcp" and sec == "tls"):
            raise Err("Fallback فقط روی TCP + TLS کار می‌کند")
        if not re.fullmatch(r"(\d{1,5}|[A-Za-z0-9.\-\[\]:/]+)", o["fallback_dest"]):
            raise Err("Fallback dest نامعتبر است (مثلاً 80 یا 127.0.0.1:8080)")
    o["fallback_xver"] = num(g("fallback_xver"), 0, 0, 2, "xver")
    o["sniffing"], o["route_only"] = flag("sniffing"), flag("route_only")
    o["block_bt"], o["block_private"], o["tfo"] = flag("block_bt"), flag("block_private"), flag("tfo")
    o["domain_strategy"] = strv("domain_strategy") or "AsIs"
    if o["domain_strategy"] not in ("AsIs", "UseIP", "UseIPv4", "UseIPv6"):
        raise Err("domainStrategy نامعتبر است")
    ex = str(g("extra_stream") or "").strip()
    if ex:
        try:
            j = json.loads(ex)
            assert isinstance(j, dict)
        except Exception:
            raise Err("JSON اضافهٔ streamSettings معتبر نیست (باید یک آبجکت JSON باشد)")
        o["extra_stream"] = json.dumps(j, ensure_ascii=False)
    ep = str(d.get("endpoint", "") or "").strip()
    if ep and not re.fullmatch(r"[A-Za-z0-9.\-:\[\]_]+", ep):
        raise Err("آدرس Endpoint نامعتبر است")
    return dict(proto="vless", psk="", obf="", ovpn="", pki=json.dumps(pki), xcfg=json.dumps(o, ensure_ascii=False),
                exclude_sub=1 if d.get("exclude_sub") else 0, name=name, remark=oneline(d.get("remark"))[:100],
                port=port, private_key="", public_key="", address4="0.0.0.0/32", address6="", endpoint=ep,
                endpoint_port=num(d.get("endpoint_port"), 0, 0, 65535, "پورت Endpoint"), dns="", mtu=0, table_="", fwmark="",
                pre_up="", post_up="", pre_down="", post_down="", auto_rules=1 if d.get("auto_rules") else 0, nat_iface="",
                use_psk=0, client_allowed_ips="0.0.0.0/0, ::/0", client_keepalive=0, client_mtu=0)


def _deep_merge(a, b):
    for k, v in b.items():
        if isinstance(v, dict) and isinstance(a.get(k), dict):
            _deep_merge(a[k], v)
        else:
            a[k] = v
    return a


def xray_users(ib):
    o = xcfg_of(ib)
    out = []
    for r in q("""SELECT c.*, ci.vuuid, ci.client_id AS cid2 FROM client_inbound ci JOIN clients c ON c.id=ci.client_id
                  WHERE ci.inbound_id=? ORDER BY c.id""", (ib["id"],)):
        if r["vuuid"] and client_state(r) == "active":
            u = {"id": r["vuuid"], "email": xray_email(r["cid2"], ib["id"]), "level": 0}
            if o["flow"]:
                u["flow"] = o["flow"]
            out.append(u)
    return out


def xray_build(ib):
    o, pki = xcfg_of(ib), pki_of(ib)
    t, sec = o["transport"], o["security"]
    tag, aport = f"in-{ib['id']}", xray_api_port(ib)
    st = {"network": t, "security": sec}
    if t == "tcp" and o["tcp_header"] == "http":
        req = {"path": [o["path"] or "/"]}
        if o["host"]:
            req["headers"] = {"Host": _comma(o["host"])}
        st["tcpSettings"] = {"header": {"type": "http", "request": req}}
    elif t == "ws":
        st["wsSettings"] = {"path": o["path"] or "/", **({"headers": {"Host": o["host"]}} if o["host"] else {})}
    elif t == "grpc":
        st["grpcSettings"] = {"serviceName": o["service_name"], "multiMode": bool(o["multi_mode"]),
                              **({"authority": o["authority"]} if o["authority"] else {})}
    elif t == "httpupgrade":
        st["httpupgradeSettings"] = {"path": o["path"] or "/", **({"host": o["host"]} if o["host"] else {})}
    elif t == "xhttp":
        st["xhttpSettings"] = {"path": o["path"] or "/", "mode": o["xhttp_mode"], **({"host": o["host"]} if o["host"] else {})}
    elif t == "kcp":
        st["kcpSettings"] = {"header": {"type": o["kcp_header"]}, **({"seed": o["kcp_seed"]} if o["kcp_seed"] else {})}
    if sec == "tls":
        ts = {"alpn": _comma(o["alpn"]), "minVersion": o["min_ver"], "rejectUnknownSni": bool(o["reject_sni"])}
        if o["sni"]:
            ts["serverName"] = o["sni"]
        if o["tls_mode"] == "self":
            ts["certificates"] = [{"certificate": pki["tls_crt"].strip().splitlines(), "key": pki["tls_key"].strip().splitlines()}]
        elif ib_node(ib) and o["tls_mode"] == "panel":      # روی نود فایل گواهی پنل وجود ندارد؛ محتوا داخل کانفیگ می‌رود
            ts["certificates"] = [{"certificate": (_read(setting("tls_cert")) or "").strip().splitlines(),
                                   "key": (_read(setting("tls_key")) or "").strip().splitlines()}]
        else:
            cf, kf = (setting("tls_cert"), setting("tls_key")) if o["tls_mode"] == "panel" else (o["tls_cert"], o["tls_key"])
            ts["certificates"] = [{"certificateFile": cf, "keyFile": kf}]
        st["tlsSettings"] = ts
    elif sec == "reality":
        st["realitySettings"] = {"show": False, "dest": o["reality_dest"], "xver": 0, "serverNames": _comma(o["server_names"]),
                                 "privateKey": pki.get("reality_priv", ""), "shortIds": _comma(o["short_ids"]) or [""]}
    if o["tfo"]:
        st["sockopt"] = {"tcpFastOpen": True}
    if o["extra_stream"]:
        _deep_merge(st, json.loads(o["extra_stream"]))
    settings = {"clients": xray_users(ib), "decryption": "none"}
    if o["fallback_dest"]:
        fd = o["fallback_dest"]
        settings["fallbacks"] = [{"dest": int(fd) if fd.isdigit() else fd, "xver": o["fallback_xver"]}]
    inbound = {"tag": tag, "listen": o["listen"], "port": ib["port"], "protocol": "vless", "settings": settings, "streamSettings": st}
    if o["sniffing"]:
        inbound["sniffing"] = {"enabled": True, "destOverride": ["http", "tls", "quic"], "routeOnly": bool(o["route_only"])}
    rules = [{"type": "field", "inboundTag": ["api"], "outboundTag": "api"}]
    if o["block_bt"]:
        rules.append({"type": "field", "protocol": ["bittorrent"], "outboundTag": "block"})
    if o["block_private"]:
        rules.append({"type": "field", "ip": PRIVATE_CIDRS, "outboundTag": "block"})
    return {"log": {"loglevel": "warning"}, "stats": {},
            "api": {"tag": "api", "services": ["StatsService", "HandlerService"]},
            "policy": {"levels": {"0": {"statsUserUplink": True, "statsUserDownlink": True}}},
            "inbounds": [{"tag": "api", "listen": "127.0.0.1", "port": aport, "protocol": "dokodemo-door",
                          "settings": {"address": "127.0.0.1"}}, inbound],
            "outbounds": [{"tag": "direct", "protocol": "freedom", "settings": {"domainStrategy": o["domain_strategy"]}},
                          {"tag": "block", "protocol": "blackhole"}],
            "routing": {"domainStrategy": "AsIs", "rules": rules}}


def xray_summary(ib):
    cfg = xray_build(ib)
    for i in cfg["inbounds"]:
        if i.get("protocol") == "vless":
            st = i["streamSettings"]
            if "realitySettings" in st:
                st["realitySettings"]["privateKey"] = "********"
            for c_ in st.get("tlsSettings", {}).get("certificates", []):
                if "key" in c_:
                    c_["key"] = ["********"]
            for u in i["settings"]["clients"]:
                u["id"] = u["id"][:8] + "-****"
    return json.dumps(cfg, indent=2, ensure_ascii=False)


def xray_shape(cfg):
    """کانفیگ بدون لیست کاربران؛ برای تشخیص اینکه فقط کاربرها عوض شده‌اند"""
    c = json.loads(json.dumps(cfg))
    for i in c.get("inbounds", []):
        if i.get("protocol") == "vless":
            i["settings"]["clients"] = []
    return c


def xray_fw(ib, add):
    net = xray_net(ib)
    r = ["INPUT", "-p", net, "--dport", str(ib["port"]), "-j", "ACCEPT"]
    exists = run(["iptables", "-C"] + r, timeout=8)[0] == 0
    if add and not exists:
        run(["iptables", "-I"] + r, timeout=8)
    elif not add and exists:
        run(["iptables", "-D"] + r, timeout=8)


def apply_vless(ib, restart=False):
    if ib_node(ib):
        return apply_vless_remote(ib, restart)
    name = ib["name"]
    if not ib["enabled"]:
        teardown(ib)
        return ""
    e = ensure_xray()
    if e:
        return f"{name}: {e}"
    try:
        cfg = xray_build(ib)
    except Exception as ex:
        return f"{name}: کانفیگ Xray ساخته نشد — {ex}"
    path = xray_path(ib)
    old = None
    try:
        old = json.loads(_read(path) or "")
    except Exception:
        old = None
    os.makedirs(XRAY_DIR, exist_ok=True)
    write_file(path, json.dumps(cfg, indent=2, ensure_ascii=False), 0o600, backup=False)
    rc, o_, e_ = run([xray_bin(), "run", "-test", "-c", path], timeout=30)
    if rc != 0:
        return f"{name}: کانفیگ Xray معتبر نیست — {(e_ or o_).strip()[-300:]}"
    ensure_xray_unit()
    if ib["auto_rules"]:
        xray_fw(ib, True)
    unit = xray_unit(ib)
    up = xray_up(ib)
    need = restart or not up or old is None or xray_shape(old) != xray_shape(cfg)
    if not need:
        old_ids = {u["id"] for i in old["inbounds"] if i.get("protocol") == "vless" for u in i["settings"]["clients"]}
        new = [u for u in cfg["inbounds"][1]["settings"]["clients"]]
        new_ids = {u["id"] for u in new}
        if old_ids - new_ids:
            need = True          # حذف کاربر → ری‌استارت تا اتصال‌های بازِ او قطع شود
        elif new_ids - old_ids:
            tmp = path + ".add"
            add = {"inbounds": [{"tag": cfg["inbounds"][1]["tag"], "protocol": "vless", "port": ib["port"],
                                 "listen": cfg["inbounds"][1]["listen"],
                                 "settings": {"clients": [u for u in new if u["id"] not in old_ids], "decryption": "none"}}]}
            write_file(tmp, json.dumps(add), 0o600, backup=False)
            rc, _, _ = run([xray_bin(), "api", "adu", f"-s=127.0.0.1:{cfg['inbounds'][0]['port']}", tmp], timeout=15)
            try:
                os.remove(tmp)
            except OSError:
                pass
            need = rc != 0
    if need:
        run(["systemctl", "enable", unit], timeout=15)
        rc, _, err = run(["systemctl", "restart", unit], timeout=40)
        if rc != 0:
            return f"{name}: راه‌اندازی Xray ناموفق بود — {err.strip()[-250:]} (journalctl -u {unit} -e)"
        time.sleep(0.8)
        if not xray_up(ib):
            return f"{name}: Xray بعد از اجرا متوقف شد (پورت {ib['port']} اشغال است؟) — journalctl -u {unit} -e"
    return ""


def vless_teardown(ib):
    if ib_node(ib):
        return vless_teardown_remote(ib)
    try:
        xray_fw(ib, False)
    except Exception:
        pass
    run(["systemctl", "disable", "--now", xray_unit(ib)], timeout=30)
    try:
        os.remove(xray_path(ib))
    except OSError:
        pass


def _vless_ingest(ib, out):
    """خروجی «xray api statsquery» یک اینباند را به مصرف کلاینت‌ها اضافه می‌کند (هم لوکال، هم نود)"""
    try:
        stats = json.loads(out).get("stat") or []
    except Exception:
        return
    per = {}
    for s_ in stats:
        m = re.fullmatch(r"user>>>(\d+)-(\d+)@sp>>>traffic>>>(uplink|downlink)", s_.get("name", ""))
        if m and int(m.group(2)) == ib["id"]:
            per.setdefault(int(m.group(1)), [0, 0])[0 if m.group(3) == "uplink" else 1] += int(s_.get("value") or 0)
    for cid_, (up_, dn_) in per.items():
        if up_ or dn_:
            x("UPDATE clients SET up_bytes=up_bytes+?, down_bytes=down_bytes+?, last_seen=? WHERE id=?", (up_, dn_, now(), cid_))
            x("UPDATE client_inbound SET last_hs=? WHERE client_id=? AND inbound_id=?", (now(), cid_, ib["id"]))
            x("UPDATE admins SET used_bytes=used_bytes+? WHERE id=(SELECT owner_id FROM clients WHERE id=?)", (up_ + dn_, cid_))


def collect_vless_stats():
    for ib in q("SELECT * FROM inbounds WHERE enabled=1 AND proto='vless' AND COALESCE(node_id,0)=0"):
        if not xray_bin() or not xray_up(ib):
            continue
        try:
            cfg = json.loads(_read(xray_path(ib)) or "")
            aport = cfg["inbounds"][0]["port"]
        except Exception:
            continue
        rc, out, _ = run([xray_bin(), "api", "statsquery", f"-s=127.0.0.1:{aport}", "-pattern", "user>>>", "-reset=true"], timeout=15)
        if rc != 0:
            continue
        _vless_ingest(ib, out)


def vless_link(c, ci, ib):
    o = xcfg_of(ib)
    t, sec = o["transport"], o["security"]
    host = ep_host(ib)
    if ":" in host and not host.startswith("["):
        host = f"[{host}]"
    P = [("encryption", "none"), ("type", t)]
    if t == "tcp" and o["tcp_header"] == "http":
        P += [("headerType", "http"), ("path", quote(o["path"] or "/", safe="")), ("host", quote(o["host"], safe=""))]
    elif t in ("ws", "httpupgrade", "xhttp"):
        P.append(("path", quote(o["path"] or "/", safe="")))
        if o["host"]:
            P.append(("host", quote(o["host"], safe="")))
        if t == "xhttp":
            P.append(("mode", o["xhttp_mode"]))
    elif t == "grpc":
        P += [("serviceName", quote(o["service_name"], safe="")), ("mode", "multi" if o["multi_mode"] else "gun")]
        if o["authority"]:
            P.append(("authority", quote(o["authority"], safe="")))
    elif t == "kcp":
        P.append(("headerType", o["kcp_header"]))
        if o["kcp_seed"]:
            P.append(("seed", quote(o["kcp_seed"], safe="")))
    P.append(("security", sec))
    if sec != "none" and o["flow"]:
        P.append(("flow", o["flow"]))
    if sec == "tls":
        P.append(("sni", o["sni"] or host.strip("[]")))
        if o["fp"]:
            P.append(("fp", o["fp"]))
        if o["alpn"]:
            P.append(("alpn", quote(o["alpn"], safe="")))
        if o["tls_mode"] == "self" and pki_of(ib).get("tls_pcs"):
            P.append(("pcs", pki_of(ib)["tls_pcs"]))      # pinnedPeerCertSha256 (Xray جدید)
        if o["allow_insecure"]:
            P.append(("allowInsecure", "1"))
    elif sec == "reality":
        P += [("sni", _comma(o["server_names"])[0]), ("fp", o["fp"] or "chrome"), ("pbk", o["reality_pub"]),
              ("sid", (_comma(o["short_ids"]) or [""])[0])]
        if o["spider_x"] and o["spider_x"] != "/":
            P.append(("spx", quote(o["spider_x"], safe="")))
    if o["packet_encoding"]:
        P.append(("packetEncoding", o["packet_encoding"]))
    return (f"vless://{ci['vuuid']}@{host}:{ib['endpoint_port'] or ib['port']}?" + "&".join(f"{k}={v}" for k, v in P)
            + "#" + quote(f"{c['name']}-{ib['name']}"))


# ------------------------------ OpenVPN (سرویس openvpn-server@<name>) ------------------------------
def ovpn_conf_path(ib):
    return f"{OVPN_DIR}/{ib['name']}.conf"


def ovpn_ccd(ib):
    return f"{OVPN_DIR}/{ib['name']}-ccd"


def ovpn_unit(ib):
    return f"openvpn-server@{ib['name']}"


def ovpn_up(ib):
    return run(["systemctl", "is-active", "--quiet", ovpn_unit(ib)], timeout=8)[0] == 0


def ensure_ovpn_pkgs():
    if shutil.which("openvpn") and shutil.which("openssl"):
        return ""
    if not shutil.which("apt-get"):
        return "openvpn نصب نیست؛ دستی نصب کنید"
    env = ["env", "DEBIAN_FRONTEND=noninteractive", "apt-get"]
    run(env + ["update", "-y"], timeout=180)
    rc, _, err = run(env + ["install", "-y", "openvpn", "openssl"], timeout=600)
    if rc != 0 or not shutil.which("openvpn"):
        return "نصب openvpn ناموفق بود: " + err.strip()[-250:]
    return ""


def ovpn_cipher_lines(o):
    c = o["cipher"]
    lst = ":".join([c] + [x_ for x_ in ("AES-256-GCM", "AES-128-GCM", "CHACHA20-POLY1305") if x_ != c])
    if o["legacy"]:
        return [f"ncp-ciphers {lst}", f"cipher {c}"]
    return [f"data-ciphers {lst}", f"data-ciphers-fallback {c}"]


def ovpn_server_conf(ib, mask=False):
    o, pki = ovpn_of(ib), pki_of(ib)
    net = ipaddress.ip_interface(ib["address4"]).network
    hid = "********\n"
    L = [f"# SepiPanel — {ib['name']}", f"port {ib['port']}", f"proto {o['transport']}", f"dev {ib['name']}", "dev-type tun",
         f"server {net.network_address} {net.netmask}", "topology subnet", "keepalive 10 120", "persist-key", "persist-tun",
         "dh none", "tls-version-min 1.2", "auth SHA256", "verb 3", "remote-cert-tls client"] + ovpn_cipher_lines(o)
    if o["transport"] == "udp":
        L.append("explicit-exit-notify 1")
    if ib["mtu"]:
        L += [f"tun-mtu {ib['mtu']}", f"mssfix {max(536, ib['mtu'] - 40)}"]
    L += [f"client-config-dir {ovpn_ccd(ib)}", "ccd-exclusive", f"status {OVPN_RUN}/status-{ib['name']}.log 5", "status-version 2",
          f"management {OVPN_RUN}/{ib['name']}.sock unix"]
    if o["redirect"]:
        L.append('push "redirect-gateway def1"')
    for dn in [d_ for d_ in re.split(r"[,\s]+", ib["dns"] or "") if re.fullmatch(r"\d+\.\d+\.\d+\.\d+", d_)]:
        L.append(f'push "dhcp-option DNS {dn}"')
    for r_ in filter(None, o["routes"].split(", ")):
        n = ipaddress.ip_network(r_, strict=False)
        if n.version == 4:
            L.append(f'push "route {n.network_address} {n.netmask}"')
    if o["extra_server"]:
        L.append(o["extra_server"])
    L += ["<ca>", pki["ca_crt"].strip(), "</ca>", "<cert>", pki["srv_crt"].strip(), "</cert>",
          "<key>", (hid.strip() if mask else pki["srv_key"].strip()), "</key>"]
    if o["tlscrypt"]:
        L += ["<tls-crypt>", (hid.strip() if mask else pki["tc"].strip()), "</tls-crypt>"]
    return "\n".join(L) + "\n"


def ovpn_client_conf(c, ci, ib):
    o, pki = ovpn_of(ib), pki_of(ib)
    host = ep_host(ib).strip("[]")
    L = [f"# {oneline(c['name'])} @ {ib['name']}", "client", "dev tun", f"proto {o['transport']}",
         f"remote {host} {ib['endpoint_port'] or ib['port']}", "resolv-retry infinite", "nobind", "persist-key", "persist-tun",
         "remote-cert-tls server", "auth SHA256", "tls-version-min 1.2", "verb 3"] + ovpn_cipher_lines(o)
    if ib["mtu"]:
        L += [f"tun-mtu {ib['mtu']}", f"mssfix {max(536, ib['mtu'] - 40)}"]
    if o["extra_client"]:
        L.append(o["extra_client"])
    L += ["<ca>", pki["ca_crt"].strip(), "</ca>", "<cert>", (ci["ovpn_crt"] or "").strip(), "</cert>",
          "<key>", (ci["ovpn_key"] or "").strip(), "</key>"]
    if o["tlscrypt"]:
        L += ["<tls-crypt>", pki["tc"].strip(), "</tls-crypt>"]
    return "\n".join(L) + "\n"


def ovpn_fw(ib, add):
    o = ovpn_of(ib)
    out = ib["nat_iface"] or detect_iface()
    net = ipaddress.ip_interface(ib["address4"]).network
    rules = [("filter", ["FORWARD", "-i", ib["name"], "-j", "ACCEPT"]), ("filter", ["FORWARD", "-o", ib["name"], "-j", "ACCEPT"]),
             ("nat", ["POSTROUTING", "-s", str(net), "-o", out, "-j", "MASQUERADE"]),
             ("filter", ["INPUT", "-p", o["transport"], "--dport", str(ib["port"]), "-j", "ACCEPT"])]
    if add:
        run(["sysctl", "-w", "net.ipv4.ip_forward=1"], timeout=8)
    for tbl, r in rules:
        exists = run(["iptables", "-t", tbl, "-C"] + r, timeout=8)[0] == 0
        if add and not exists:
            run(["iptables", "-t", tbl, "-A" if tbl == "nat" else "-I"] + r, timeout=8)
        elif not add and exists:
            run(["iptables", "-t", tbl, "-D"] + r, timeout=8)


def ovpn_mgmt(ib, cmds):
    """دستورهای management (مثل kill <CN>) را روی سوکت یونیکسی سرویس می‌فرستد"""
    if not cmds:
        return
    try:
        sk = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sk.settimeout(3)
        sk.connect(f"{OVPN_RUN}/{ib['name']}.sock")
        try:
            sk.recv(4096)
        except Exception:
            pass
        for c_ in cmds:
            sk.sendall((c_ + "\n").encode())
            time.sleep(0.05)
            try:
                sk.recv(4096)
            except Exception:
                pass
        sk.sendall(b"quit\n")
        sk.close()
    except Exception:
        pass


def ovpn_status(ib):
    """{CN: (real_addr, bytes_rx, bytes_tx)}؛ rx = از کلاینت (آپلود)"""
    p = f"{OVPN_RUN}/status-{ib['name']}.log"
    try:
        if time.time() - os.path.getmtime(p) > 40:
            return {}
    except OSError:
        return {}
    out = {}
    for ln in (_read(p) or "").splitlines():
        if ln.startswith("CLIENT_LIST,"):
            f = ln.split(",")
            if len(f) > 6:
                try:
                    out[f[1]] = (f[2], int(f[5]), int(f[6]))
                except ValueError:
                    pass
    return out


def apply_ovpn(ib, restart=False):
    name = ib["name"]
    if not ib["enabled"]:
        teardown(ib)
        return ""
    e = ensure_ovpn_pkgs()
    if e:
        return f"{name}: {e}"
    try:
        conf = ovpn_server_conf(ib)
    except Exception as ex:
        return f"{name}: کانفیگ OpenVPN ساخته نشد — {ex}"
    ch = write_file(ovpn_conf_path(ib), conf, 0o600)
    ccd = ovpn_ccd(ib)
    os.makedirs(ccd, exist_ok=True)
    os.chmod(ccd, 0o755)
    want = {}
    for r in q("""SELECT c.*, ci.ovpn_cn FROM client_inbound ci JOIN clients c ON c.id=ci.client_id
                  WHERE ci.inbound_id=?""", (ib["id"],)):
        if r["ovpn_cn"]:
            want[r["ovpn_cn"]] = client_state(r) == "active"
    for cn, act in want.items():
        write_file(os.path.join(ccd, cn), "# SepiPanel\n" if act else "disable\n", 0o644, backup=False)
    gone = []
    for fn in os.listdir(ccd):
        if fn not in want:
            gone.append(fn)
            try:
                os.remove(os.path.join(ccd, fn))
            except OSError:
                pass
    if ib["auto_rules"]:
        ovpn_fw(ib, True)
    if restart or ch or not ovpn_up(ib):
        run(["systemctl", "enable", ovpn_unit(ib)], timeout=15)
        rc, _, err = run(["systemctl", "restart", ovpn_unit(ib)], timeout=40)
        if rc != 0:
            return f"{name}: راه‌اندازی OpenVPN ناموفق بود — {err.strip()[-250:]} (journalctl -u {ovpn_unit(ib)} -e)"
    ovpn_mgmt(ib, ["kill " + cn for cn, act in want.items() if not act] + ["kill " + cn for cn in gone])
    return ""


def ovpn_teardown(ib):
    try:
        ovpn_fw(ib, False)
    except Exception:
        pass
    run(["systemctl", "disable", "--now", ovpn_unit(ib)], timeout=30)
    for p in (ovpn_conf_path(ib), f"{OVPN_RUN}/status-{ib['name']}.log"):
        try:
            os.remove(p)
        except OSError:
            pass
    shutil.rmtree(ovpn_ccd(ib), ignore_errors=True)


def collect_ovpn_stats():
    for ib in q("SELECT * FROM inbounds WHERE enabled=1 AND proto='ovpn'"):
        cur = ovpn_status(ib)
        for r in q("SELECT * FROM client_inbound WHERE inbound_id=? AND ovpn_cn!=''", (ib["id"],)):
            s_ = cur.get(r["ovpn_cn"])
            if not s_:
                if r["last_rx"] or r["last_tx"]:
                    x("UPDATE client_inbound SET last_rx=0, last_tx=0 WHERE client_id=? AND inbound_id=?", (r["client_id"], ib["id"]))
                continue
            real, rx, tx = s_
            drx = rx - r["last_rx"] if rx >= r["last_rx"] else rx
            dtx = tx - r["last_tx"] if tx >= r["last_tx"] else tx
            x("UPDATE client_inbound SET last_rx=?, last_tx=?, last_hs=?, endpoint=? WHERE client_id=? AND inbound_id=?",
              (rx, tx, now(), real, r["client_id"], ib["id"]))
            x("UPDATE clients SET last_seen=? WHERE id=?", (now(), r["client_id"]))
            if drx or dtx:
                x("UPDATE clients SET up_bytes=up_bytes+?, down_bytes=down_bytes+? WHERE id=?", (drx, dtx, r["client_id"]))
                x("UPDATE admins SET used_bytes=used_bytes+? WHERE id=(SELECT owner_id FROM clients WHERE id=?)",
                  (drx + dtx, r["client_id"]))


# ------------------------------ L2TP/IPsec (xl2tpd + strongSwan) ------------------------------
PPP_RUN = "/run/sepipanel-ppp"
BLK_B, BLK_E = "# BEGIN SEPIPANEL", "# END SEPIPANEL"
L2TP_FILES = dict(xl2tpd="/etc/xl2tpd/xl2tpd.conf", ppp="/etc/ppp/options.xl2tpd", chap="/etc/ppp/chap-secrets",
                  ipsec_conf="/etc/ipsec.conf", ipsec_secrets="/etc/ipsec.secrets",
                  up="/etc/ppp/ip-up.d/sepipanel", down="/etc/ppp/ip-down.d/sepipanel")


def _read(path):
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return None


def write_file(path, content, mode=0o600, backup=True):
    """فقط در صورت تغییر می‌نویسد؛ True = تغییر کرد. نسخه اصلی فایل یک‌بار با پسوند .orig نگه داشته می‌شود."""
    old = _read(path)
    if old == content:
        return False
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if backup and old is not None and BLK_B not in old and "SepiPanel" not in old and not os.path.exists(path + ".orig"):
        try:
            shutil.copy2(path, path + ".orig")
        except OSError:
            pass
    um = os.umask(0o077)
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    finally:
        os.umask(um)
    os.chmod(path, mode)
    return True


def write_block(path, body, mode=0o600, head=""):
    """بلوک مخصوص پنل را داخل فایل مشترک (chap-secrets, ipsec.conf, ...) می‌نویسد/حذف می‌کند و بقیه را دست‌نخورده می‌گذارد."""
    old = _read(path)
    if old is None and not body:
        return False
    base = re.sub(re.escape(BLK_B) + r".*?" + re.escape(BLK_E) + r"\n?", "", old if old is not None else head, flags=re.S)
    new = base
    if body:
        new = base.rstrip("\n") + ("\n" if base.strip() else "") + f"{BLK_B}\n{body.rstrip(chr(10))}\n{BLK_E}\n"
    return write_file(path, new, mode)


def ipsec_svc():
    for n in ("strongswan-starter", "strongswan", "ipsec"):
        if run(["systemctl", "cat", n + ".service"], timeout=8)[0] == 0:
            return n
    return None


def l2tp_up():
    s = ipsec_svc()
    return bool(s) and run(["systemctl", "is-active", "--quiet", "xl2tpd"], timeout=8)[0] == 0 \
        and run(["systemctl", "is-active", "--quiet", s], timeout=8)[0] == 0


def ensure_l2tp_pkgs():
    if shutil.which("xl2tpd") and shutil.which("ipsec"):
        return ""
    if not shutil.which("apt-get"):
        return "xl2tpd و strongswan نصب نیستند؛ دستی نصب کنید"
    env = ["env", "DEBIAN_FRONTEND=noninteractive", "apt-get"]
    run(env + ["update", "-y"], timeout=180)
    rc, _, err = run(env + ["install", "-y", "xl2tpd", "strongswan"], timeout=600)
    run(env + ["install", "-y", "strongswan-starter"], timeout=300)   # در بعضی نسخه‌ها جداست؛ خطایش مهم نیست
    if rc != 0 or not (shutil.which("xl2tpd") and shutil.which("ipsec")):
        return "نصب xl2tpd/strongswan ناموفق بود: " + err.strip()[-250:]
    return ""


def l2tp_pool(ib):
    net = ipaddress.ip_interface(ib["address4"])
    lo, hi, gw = int(net.network.network_address) + 1, int(net.network.broadcast_address) - 1, int(net.ip)
    if lo <= gw <= hi:
        if gw - lo > hi - gw:
            hi = gw - 1
        else:
            lo = gw + 1
    if lo > hi:
        raise Err("ساب‌نت L2TP برای رنج آی‌پی کوچک است")
    return str(ipaddress.ip_address(lo)), str(ipaddress.ip_address(hi)), str(net.ip)


def l2tp_fw(ib, add):
    out = ib["nat_iface"] or detect_iface()
    net = ipaddress.ip_interface(ib["address4"]).network
    rules = [("filter", ["FORWARD", "-i", "ppp+", "-j", "ACCEPT"]), ("filter", ["FORWARD", "-o", "ppp+", "-j", "ACCEPT"]),
             ("nat", ["POSTROUTING", "-s", str(net), "-o", out, "-j", "MASQUERADE"]),
             ("filter", ["INPUT", "-p", "udp", "-m", "multiport", "--dports", "500,4500", "-j", "ACCEPT"]),
             ("filter", ["INPUT", "-p", "esp", "-j", "ACCEPT"])]
    if add:
        run(["sysctl", "-w", "net.ipv4.ip_forward=1"], timeout=8)
    for tbl, r in rules:
        exists = run(["iptables", "-t", tbl, "-C"] + r, timeout=8)[0] == 0
        if add and not exists:
            run(["iptables", "-t", tbl, "-A" if tbl == "nat" else "-I"] + r, timeout=8)
        elif not add and exists:
            run(["iptables", "-t", tbl, "-D"] + r, timeout=8)


def ppp_sessions():
    """{username: ppp_iface} برای اتصال‌های زنده (فایل‌ها را اسکریپت ip-up می‌سازد)"""
    out = {}
    try:
        names = os.listdir(PPP_RUN)
    except OSError:
        return out
    live = {ln.split(":")[0].strip() for ln in _read("/proc/net/dev").splitlines()[2:]} if _read("/proc/net/dev") else set()
    for n in names:
        if n not in live:
            try:
                os.remove(os.path.join(PPP_RUN, n))
            except OSError:
                pass
            continue
        u = (_read(os.path.join(PPP_RUN, n)) or "").strip()
        if u:
            out[u] = n
    return out


def ppp_kick(iface):
    try:
        pid = int((_read(f"/var/run/{iface}.pid") or "0").split()[0])
        if pid > 1:
            os.kill(pid, 15)
    except Exception:
        pass


def l2tp_summary(ib):
    lo, hi, gw = l2tp_pool(ib)
    return (f"# L2TP/IPsec (xl2tpd + strongSwan) — {ib['name']}\nIPsec PSK = ********\nGateway = {gw}\n"
            f"Pool = {lo} - {hi}\nDNS = {ib['dns'] or '-'}\nMTU/MRU = {ib['mtu'] or 1400}\n"
            f"UDP 500, 4500 (IPsec) + 1701 (L2TP داخل IPsec)\n")


def apply_l2tp(ib, restart=False):
    name = ib["name"]
    if not ib["enabled"]:
        teardown(ib)
        return ""
    e = ensure_l2tp_pkgs()
    if e:
        return f"{name}: {e}"
    try:
        lo, hi, gw = l2tp_pool(ib)
    except Err as ex:
        return f"{name}: {ex}"
    dns4 = [d for d in re.split(r"[,\s]+", ib["dns"] or "") if re.fullmatch(r"\d+\.\d+\.\d+\.\d+", d)][:2]
    mtu = ib["mtu"] or 1400
    F = L2TP_FILES
    ch = write_file(F["xl2tpd"], "; SepiPanel — auto-generated\n[global]\nport = 1701\n\n[lns default]\n"
                    f"ip range = {lo}-{hi}\nlocal ip = {gw}\nrequire chap = yes\nrefuse pap = yes\n"
                    "require authentication = yes\nname = l2tpd\npppoptfile = /etc/ppp/options.xl2tpd\nlength bit = yes\n", 0o644)
    ch |= write_file(F["ppp"], "# SepiPanel — auto-generated\nipcp-accept-local\nipcp-accept-remote\nrefuse-pap\nrefuse-eap\n"
                     + "".join(f"ms-dns {d}\n" for d in dns4)
                     + f"noccp\nauth\nhide-password\nname l2tpd\nproxyarp\nlcp-echo-interval 30\nlcp-echo-failure 4\n"
                       f"mtu {mtu}\nmru {mtu}\n", 0o644)
    write_file(F["up"], "#!/bin/sh\n# SepiPanel\nmkdir -p /run/sepipanel-ppp\nprintf '%s' \"$PEERNAME\" > \"/run/sepipanel-ppp/$PPP_IFACE\"\nexit 0\n", 0o755)
    write_file(F["down"], "#!/bin/sh\n# SepiPanel\nrm -f \"/run/sepipanel-ppp/$PPP_IFACE\"\nexit 0\n", 0o755)
    # کاربران فعال
    active, lines_ = set(), []
    for r in q("""SELECT c.*, ci.l2tp_user, ci.l2tp_pass FROM client_inbound ci
                  JOIN clients c ON c.id=ci.client_id WHERE ci.inbound_id=? ORDER BY c.id""", (ib["id"],)):
        if r["l2tp_user"] and r["l2tp_pass"] and client_state(r) == "active":
            active.add(r["l2tp_user"])
            lines_.append(f'"{r["l2tp_user"]}" l2tpd "{r["l2tp_pass"]}" *')
    write_block(F["chap"], "\n".join(lines_), 0o600)
    # IPsec
    ch_ip = write_block(F["ipsec_conf"], (
        "conn sepi-l2tp\n    type=transport\n    authby=secret\n    rekey=no\n    keyingtries=%forever\n"
        "    left=%any\n    leftprotoport=17/1701\n    right=%any\n    rightprotoport=17/%any\n    ikev2=never\n"
        "    ike=aes256-sha1-modp2048,aes128-sha1-modp2048,aes256-sha256-modp2048,aes128-sha256-modp2048,"
        "aes256-sha1-modp1024,aes128-sha1-modp1024,3des-sha1-modp1024!\n"
        "    esp=aes256-sha1,aes128-sha1,aes256-sha256,aes128-sha256,3des-sha1!\n"
        "    ikelifetime=8h\n    keylife=1h\n    dpddelay=30\n    dpdtimeout=120\n    dpdaction=clear\n    auto=add"),
        0o644, head="config setup\n    uniqueids=no\n\n")
    ch_sec = write_block(F["ipsec_secrets"], f'%any %any : PSK "{ib["psk"]}"', 0o600)
    if ib["auto_rules"]:
        l2tp_fw(ib, True)
    svc_ip = ipsec_svc()
    if not svc_ip:
        return f"{name}: سرویس strongSwan پیدا نشد (apt install strongswan strongswan-starter)"
    if restart or ch_ip or ch_sec or run(["systemctl", "is-active", "--quiet", svc_ip], timeout=8)[0] != 0:
        run(["systemctl", "enable", svc_ip], timeout=15)
        rc, _, err = run(["systemctl", "restart", svc_ip], timeout=40)
        if rc != 0:
            return f"{name}: راه‌اندازی IPsec ناموفق بود — {err.strip()[-250:]}"
    else:
        run(["ipsec", "rereadsecrets"], timeout=10)
    if restart or ch or run(["systemctl", "is-active", "--quiet", "xl2tpd"], timeout=8)[0] != 0:
        run(["systemctl", "enable", "xl2tpd"], timeout=15)
        rc, _, err = run(["systemctl", "restart", "xl2tpd"], timeout=30)
        if rc != 0:
            return f"{name}: راه‌اندازی xl2tpd ناموفق بود — {err.strip()[-250:]}"
    for u, iface in ppp_sessions().items():     # کاربرِ غیرفعال/حذف‌شده/تمام‌شده قطع شود
        if u not in active:
            ppp_kick(iface)
    return ""


def l2tp_teardown(ib):
    try:
        l2tp_fw(ib, False)
    except Exception:
        pass
    for u, iface in ppp_sessions().items():
        ppp_kick(iface)
    F = L2TP_FILES
    write_block(F["chap"], "")
    write_block(F["ipsec_secrets"], "")
    if write_block(F["ipsec_conf"], ""):
        run(["ipsec", "reload"], timeout=10)
    run(["systemctl", "disable", "--now", "xl2tpd"], timeout=20)


def collect_l2tp_stats():
    ib = q("SELECT * FROM inbounds WHERE enabled=1 AND proto='l2tp'", (), True)
    if not ib:
        return
    sess = ppp_sessions()
    ctr = {}
    for ln in (_read("/proc/net/dev") or "").splitlines()[2:]:
        nm, _, rest = ln.partition(":")
        f = rest.split()
        if len(f) >= 9:
            ctr[nm.strip()] = (int(f[0]), int(f[8]))
    for r in q("SELECT * FROM client_inbound WHERE inbound_id=? AND l2tp_user!=''", (ib["id"],)):
        iface = sess.get(r["l2tp_user"])
        if not iface or iface not in ctr:
            if r["last_rx"] or r["last_tx"]:
                x("UPDATE client_inbound SET last_rx=0, last_tx=0 WHERE client_id=? AND inbound_id=?", (r["client_id"], ib["id"]))
            continue
        rx, tx = ctr[iface]
        drx = rx - r["last_rx"] if rx >= r["last_rx"] else rx
        dtx = tx - r["last_tx"] if tx >= r["last_tx"] else tx
        x("UPDATE client_inbound SET last_rx=?, last_tx=?, last_hs=? WHERE client_id=? AND inbound_id=?",
          (rx, tx, now(), r["client_id"], ib["id"]))
        x("UPDATE clients SET last_seen=? WHERE id=?", (now(), r["client_id"]))
        if drx or dtx:
            x("UPDATE clients SET up_bytes=up_bytes+?, down_bytes=down_bytes+? WHERE id=?", (drx, dtx, r["client_id"]))
            x("UPDATE admins SET used_bytes=used_bytes+? WHERE id=(SELECT owner_id FROM clients WHERE id=?)",
              (drx + dtx, r["client_id"]))


# ------------------------------ اعمال روی سیستم ------------------------------
def iface_up(ib):
    if is_l2tp(ib):
        return l2tp_up()
    if is_ovpn(ib):
        return ovpn_up(ib)
    if is_vless(ib):
        return xray_up(ib)
    return run([tools(ib)[0], "show", ib["name"]])[0] == 0


def teardown(ib):
    if is_l2tp(ib):
        return l2tp_teardown(ib)
    if is_ovpn(ib):
        return ovpn_teardown(ib)
    if is_vless(ib):
        return vless_teardown(ib)
    p = conf_path(ib)
    if iface_up(ib):
        if os.path.exists(p):
            run([tools(ib)[1], "down", p])
        else:
            run(["ip", "link", "del", ib["name"]])
    run(["systemctl", "disable", svc(ib)])
    try:
        os.remove(p)
    except OSError:
        pass


def write_conf(ib):
    p = conf_path(ib)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    old = os.umask(0o077)
    try:
        with open(p, "w") as f:
            f.write(server_conf(ib))
    finally:
        os.umask(old)
    os.chmod(p, 0o600)
    return p


def apply_inbound(iid, restart=False):
    """برمی‌گرداند: رشته‌ی خطا یا ''"""
    with APPLY_LOCK:
        ib = q("SELECT * FROM inbounds WHERE id=?", (iid,), True)
        if not ib:
            return ""
        name = ib["name"]
        if is_l2tp(ib):
            return apply_l2tp(ib, restart)
        if is_ovpn(ib):
            return apply_ovpn(ib, restart)
        if is_vless(ib):
            return apply_vless(ib, restart)
        wg, wgq = tools(ib)
        if not ib["enabled"]:
            teardown(ib)
            return ""
        up = iface_up(ib)
        if up and restart and os.path.exists(conf_path(ib)):
            run([wgq, "down", conf_path(ib)])
            up = False
        p = write_conf(ib)
        if not up:
            rc, _, err = run([wgq, "up", p])
            if rc != 0:
                return f"{name}: بالا آمدن اینترفیس ناموفق بود — {err.strip()[-300:]}"
            run(["systemctl", "enable", svc(ib)])
            return ""
        rc, stripped, err = run([wgq, "strip", p])
        if rc != 0:
            return f"{name}: {err.strip()[-300:]}"
        tmp = p + ".sync"
        old = os.umask(0o077)
        try:
            with open(tmp, "w") as f:
                f.write(stripped)
        finally:
            os.umask(old)
        rc, _, err = run([wg, "syncconf", name, tmp])
        try:
            os.remove(tmp)
        except OSError:
            pass
        return "" if rc == 0 else f"{name}: syncconf ناموفق — {err.strip()[-300:]}"


def apply_many(ids, restart=False):
    w = [apply_inbound(i, restart) for i in set(ids)]
    return " | ".join(s for s in w if s)


def sync_inbound_clients(iid):
    ib = q("SELECT * FROM inbounds WHERE id=?", (iid,), True)
    rows = q("SELECT * FROM client_inbound WHERE inbound_id=?", (iid,))
    srv4 = str(ipaddress.ip_interface(ib["address4"]).ip)
    if is_l2tp(ib):
        for r in rows:
            if not r["l2tp_user"] or not r["l2tp_pass"]:
                u = r["l2tp_user"]
                while not u or q("SELECT 1 FROM client_inbound WHERE l2tp_user=?", (u,), True):
                    u = "u" + secrets.token_hex(4)
                x("UPDATE client_inbound SET l2tp_user=?, l2tp_pass=?, ip4='', ip6='', psk='' WHERE client_id=? AND inbound_id=?",
                  (u, r["l2tp_pass"] or rand_secret(12), r["client_id"], iid))
        return srv4
    if is_vless(ib):
        for r in rows:
            if not r["vuuid"]:
                x("UPDATE client_inbound SET vuuid=?, ip4='', ip6='', psk='' WHERE client_id=? AND inbound_id=?",
                  (str(uuid.uuid4()), r["client_id"], iid))
        return srv4
    if is_ovpn(ib):
        pki, kt = pki_of(ib), ovpn_of(ib)["keytype"]
        for r in rows:
            if not (r["ovpn_cn"] and r["ovpn_crt"] and r["ovpn_key"]):
                cn = "c" + secrets.token_hex(6)
                crt, key = ovpn_sign(pki, cn, False, kt)
                x("UPDATE client_inbound SET ovpn_cn=?, ovpn_crt=?, ovpn_key=?, ip4='', ip6='', psk='' WHERE client_id=? AND inbound_id=?",
                  (cn, crt, key, r["client_id"], iid))
        return srv4
    used6 = {r["ip6"] for r in rows if r["ip6"]}
    for r in rows:
        ip6, psk = r["ip6"], r["psk"]
        if ib["address6"]:
            if not ip6:
                a6 = ipaddress.ip_interface(ib["address6"])
                ip6 = alloc(a6.network, used6, str(a6.ip)); used6.add(ip6)
        else:
            ip6 = ""
        if ib["use_psk"] and not psk:
            psk = gen_psk()
        elif not ib["use_psk"]:
            psk = ""
        if (ip6, psk) != (r["ip6"], r["psk"]):
            x("UPDATE client_inbound SET ip6=?, psk=? WHERE client_id=? AND inbound_id=?",
              (ip6, psk, r["client_id"], iid))
    return srv4


# ------------------------------ کلاینت‌ها ------------------------------
def norm_link(L):
    return dict(
        allowed_ips=check_cidrs(L.get("allowed_ips"), "AllowedIPs"),
        keepalive=num(L.get("keepalive"), -1, -1, 65535, "Keepalive"),
        dns=check_dns(L.get("dns")), mtu=num(L.get("mtu"), 0, 0, 9200, "MTU"),
        extra_allowed=check_cidrs(L.get("extra_allowed"), "Extra AllowedIPs"))


def add_or_update_link(cid, ib, L):
    if is_l2tp(ib) or is_ovpn(ib) or is_vless(ib):      # L2TP/OpenVPN/VLESS: تنظیم جدا ندارد؛ فقط یوزر/گواهی/UUID ساخته می‌شود
        if not q("SELECT 1 FROM client_inbound WHERE client_id=? AND inbound_id=?", (cid, ib["id"]), True):
            x("INSERT INTO client_inbound(client_id,inbound_id,ip4,keepalive) VALUES(?,?,'',-1)", (cid, ib["id"]))
        sync_inbound_clients(ib["id"])
        return
    n = norm_link(L)
    cur = q("SELECT * FROM client_inbound WHERE client_id=? AND inbound_id=?", (cid, ib["id"]), True)
    a4 = ipaddress.ip_interface(ib["address4"])
    used4 = {r["ip4"] for r in q("SELECT ip4 FROM client_inbound WHERE inbound_id=? AND client_id!=?", (ib["id"], cid))}
    want = str(L.get("ip4") or "").strip()
    if want:
        try:
            ip = ipaddress.ip_address(want)
            assert ip in a4.network.hosts() if a4.network.num_addresses <= 65536 else ip in a4.network
        except Exception:
            raise Err(f"IP «{want}» در ساب‌نت {ib['name']} معتبر نیست")
        if want == str(a4.ip) or want in used4:
            raise Err(f"IP «{want}» قبلاً استفاده شده")
        ip4 = want
    else:
        ip4 = cur["ip4"] if cur else alloc(a4.network, used4, str(a4.ip))
    if cur:
        x("""UPDATE client_inbound SET ip4=?, allowed_ips=?, keepalive=?, dns=?, mtu=?, extra_allowed=?
             WHERE client_id=? AND inbound_id=?""",
          (ip4, n["allowed_ips"], n["keepalive"], n["dns"], n["mtu"], n["extra_allowed"], cid, ib["id"]))
    else:
        x("""INSERT INTO client_inbound(client_id,inbound_id,ip4,allowed_ips,keepalive,dns,mtu,extra_allowed)
             VALUES(?,?,?,?,?,?,?,?)""",
          (cid, ib["id"], ip4, n["allowed_ips"], n["keepalive"], n["dns"], n["mtu"], n["extra_allowed"]))
    sync_inbound_clients(ib["id"])


def parse_client_basic(d):
    name = oneline(d.get("name"))[:64]
    if not name:
        raise Err("نام کلاینت لازم است")
    try:
        gb = float(d.get("limit_gb") or 0)
    except Exception:
        raise Err("حجم نامعتبر است")
    rp = str(d.get("reset_period") or "")
    if rp not in ("", "daily", "weekly", "monthly"):
        raise Err("بازه ریست ترافیک نامعتبر است")
    return dict(name=name, note=str(d.get("note") or "")[:500], limit_bytes=int(max(gb, 0) * 1024 ** 3),
                expiry=num(d.get("expiry"), 0, 0, None, "تاریخ انقضا"), reset_period=rp)


def save_links(cid, links):
    touched = set()
    ids = set()
    for L in links or []:
        ib = q("SELECT * FROM inbounds WHERE id=?", (num(L.get("inbound_id")),), True)
        if not ib:
            raise Err("اینباند انتخاب‌شده وجود ندارد")
        ids.add(ib["id"])
        add_or_update_link(cid, ib, L)
        touched.add(ib["id"])
    for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (cid,)):
        if r["inbound_id"] not in ids:
            x("DELETE FROM client_inbound WHERE client_id=? AND inbound_id=?", (cid, r["inbound_id"]))
            touched.add(r["inbound_id"])
    return touched


# ------------------------------ آمار و محدودیت‌ها ------------------------------
def collect_stats():
    changed = set()
    ibs = q("SELECT * FROM inbounds WHERE enabled=1")
    collect_l2tp_stats()
    collect_ovpn_stats()
    collect_vless_stats()
    for ib in ibs:
        if is_l2tp(ib) or is_ovpn(ib) or is_vless(ib):
            continue
        rc, out, _ = run([tools(ib)[0], "show", ib["name"], "dump"], timeout=10)
        if rc != 0:
            continue
        for ln in out.strip().splitlines()[1:]:
            f = ln.split("\t")
            if len(f) < 8:
                continue
            pub, ep, hs, rx, tx = f[0], f[2], int(f[4] or 0), int(f[5] or 0), int(f[6] or 0)
            r = q("""SELECT ci.*, c.id AS cid FROM client_inbound ci JOIN clients c ON c.id=ci.client_id
                     WHERE ci.inbound_id=? AND c.public_key=?""", (ib["id"], pub), True)
            if not r:
                continue
            drx = rx - r["last_rx"] if rx >= r["last_rx"] else rx
            dtx = tx - r["last_tx"] if tx >= r["last_tx"] else tx
            x("UPDATE client_inbound SET last_rx=?, last_tx=?, last_hs=?, endpoint=? WHERE client_id=? AND inbound_id=?",
              (rx, tx, hs or r["last_hs"], "" if ep == "(none)" else ep, r["cid"], ib["id"]))
            if drx or dtx:
                x("UPDATE clients SET up_bytes=up_bytes+?, down_bytes=down_bytes+? WHERE id=?", (drx, dtx, r["cid"]))
                x("UPDATE admins SET used_bytes=used_bytes+? WHERE id=(SELECT owner_id FROM clients WHERE id=?)",
                  (drx + dtx, r["cid"]))
                x("UPDATE api_keys SET used_bytes=used_bytes+? WHERE id=(SELECT key_id FROM clients WHERE id=?)",
                  (drx + dtx, r["cid"]))
            if hs:
                x("UPDATE clients SET last_seen=MAX(last_seen,?) WHERE id=?", (hs, r["cid"]))
    for c in q("SELECT * FROM clients WHERE reset_period!=''"):
        span = {"daily": 86400, "weekly": 7 * 86400, "monthly": 30 * 86400}.get(c["reset_period"])
        if span and now() - (c["last_reset"] or c["created"] or 0) >= span:
            x("UPDATE clients SET up_bytes=0, down_bytes=0, last_reset=? WHERE id=?", (now(), c["id"]))
            if not c["enabled"] and c["reason"] == "limit":
                x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (c["id"],))
                changed |= {r["inbound_id"] for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (c["id"],))}
    for c in q("SELECT * FROM clients WHERE enabled=1"):
        st = usage_state(c)
        if st != "active":
            x("UPDATE clients SET enabled=0, reason=? WHERE id=?", (st, c["id"]))
            changed |= {r["inbound_id"] for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (c["id"],))}
    for a in q("SELECT * FROM admins"):       # ادمینی که حجم/زمانش تمام شد یا تمدید شد → کلاینت‌هایش قطع/وصل شود
        st = admin_state(a)
        if ADM_STATE.get(a["id"], st) != st:
            changed |= admin_inbounds(a["id"])
        ADM_STATE[a["id"]] = st
    for k in q("SELECT * FROM api_keys"):     # کلیدی که حجم/زمانش تمام شد یا تمدید شد → کلاینت‌های ساخته‌شده با آن قطع/وصل شود
        st = key_quota_state(k)
        if KEY_STATE.get(k["id"], st) != st:
            changed |= key_inbounds(k["id"])
        KEY_STATE[k["id"]] = st
    if changed:
        w = apply_many(changed)
        if w:
            log.warning(w)


def stats_loop():
    while True:
        try:
            collect_stats()
            check_cert()
        except Exception:
            log.exception("stats")
        time.sleep(STATS_INTERVAL)


def reconcile():
    for ib in q("SELECT id FROM inbounds WHERE COALESCE(node_id,0)=0"):
        w = apply_inbound(ib["id"])
        if w:
            log.warning(w)


# ------------------------------ Flask ------------------------------
app = Flask(__name__)
try:
    app.json.ensure_ascii = False
except Exception:
    pass
_sk = setting("secret_key")
if not _sk:
    _sk = secrets.token_hex(32); set_setting("secret_key", _sk)
app.secret_key = _sk
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Strict", PERMANENT_SESSION_LIFETIME=7 * 86400)
FAILS = {}


def base_url():
    u = PUBLIC_URL or setting("public_url")
    if u:
        return u.rstrip("/")
    c = panel_cfg()
    if c["domain"]:
        tls = bool(tls_files())
        d = f"{'https' if tls else 'http'}://{c['domain']}"
        if (tls and c["port"] != 443) or (not tls and c["port"] != 80):
            d += f":{c['port']}"
        return d
    return request.host_url.rstrip("/")


def _who():
    """(role, admin_id) یا None. نشست‌های قدیمی بدون role همان مدیر اصلی‌اند."""
    if not session.get("u"):
        return None
    if session.get("role", "super") == "super":
        return ("super", 0) if session.get("v") == setting("sess_ver", "0") else None
    a = q("SELECT * FROM admins WHERE id=?", (session.get("aid"),), True)
    if not a or not a["enabled"] or not a["ver"] or session.get("av") != a["ver"]:
        return None
    return ("admin", a["id"])


KEYFAILS = {}


def _key_who(key):
    """کلید API → (role, admin_id)؛ نامعتبر = None؛ تلاش‌های بیش‌ازحد = 'rate'"""
    ip = request.remote_addr or "?"
    n, t = KEYFAILS.get(ip, (0, now()))
    if now() - t > 300:
        n, t = 0, now()
    if n >= 30:
        return "rate"
    r = q("SELECT * FROM api_keys WHERE key_hash=? AND enabled=1", (hashlib.sha256(key.encode()).hexdigest(),), True)
    who = None
    if r:
        if r["admin_id"]:
            a = q("SELECT * FROM admins WHERE id=?", (r["admin_id"],), True)
            if a and a["enabled"]:
                who = ("admin", a["id"], r["id"])
        else:
            who = ("super", 0, r["id"])
    if not who:
        KEYFAILS[ip] = (n + 1, t)
        return None
    if now() - (r["last_used"] or 0) > 60:
        x("UPDATE api_keys SET last_used=? WHERE id=?", (now(), r["id"]))
    return who


def _guard(super_only, allow_key=True):
    def deco(fn):
        @wraps(fn)
        def w(*a, **k):
            h = request.headers.get("Authorization", "")
            key = h[7:].strip() if h[:7].lower() == "bearer " else request.headers.get("X-API-Key", "").strip()
            if key:                      # درخواست با کلید API (بدون کوکی؛ CSRF موضوعیت ندارد) — فقط مسیرهای auth_any
                kw = _key_who(key)
                if kw == "rate":
                    return jsonify(error="تلاش‌های زیاد؛ چند دقیقه بعد دوباره امتحان کنید"), 429
                if not kw:
                    return jsonify(error="کلید API نامعتبر یا غیرفعال است"), 401
                if super_only or not allow_key:
                    return jsonify(error="این مسیر با کلید API در دسترس نیست"), 403
                g.role, g.aid, g.key_id, g.via_key = kw[0], kw[1], kw[2], True
                return fn(*a, **k)
            who = _who()
            if not who:
                return jsonify(error="auth"), 401
            if super_only and who[0] != "super":
                return jsonify(error="دسترسی ندارید"), 403
            if request.method != "GET" and request.headers.get("X-Requested-With") != "sepipanel":
                return jsonify(error="bad request"), 400
            g.role, g.aid = who
            return fn(*a, **k)
        return w
    return deco


auth = _guard(True)        # فقط مدیر اصلی (پیش‌فرض همه‌ی مسیرها)
auth_any = _guard(False)   # مدیر اصلی یا ادمین (فقط مسیرهای کلاینت)
auth_adm = _guard(False, False)   # مدیر اصلی یا ادمین، فقط با نشست پنل (نه با کلید API)


@app.errorhandler(Err)
def on_err(e):
    return jsonify(error=str(e)), 400


@app.errorhandler(Exception)
def on_exc(e):
    from werkzeug.exceptions import HTTPException
    if isinstance(e, HTTPException):
        if request.path.startswith("/api/v1/"):
            return jsonify(error={404: "پیدا نشد (یا مال حساب شما نیست)", 405: "متد نامعتبر"}.get(e.code, e.name)), e.code
        return e
    log.exception("unhandled")
    return jsonify(error=f"خطای داخلی: {e}"), 500


def body():
    return request.get_json(silent=True) or {}


def ser_inbound(r, ups):
    d = {k: r[k] for k in r.keys() if k not in ("private_key", "pki")}
    d["ovpn"] = ovpn_of(r) if is_ovpn(r) else {}
    d["xcfg"] = xcfg_of(r) if is_vless(r) else {}
    d["net"] = xray_net(r) if is_vless(r) else ""
    d["obf"] = obf_of(r); d["awg"] = is_awg(r); d["obf_enabled"] = 1 if is_awg(r) else 0
    d["up"] = r["name"] in ups
    d["clients"] = q("SELECT COUNT(*) n FROM client_inbound WHERE inbound_id=?", (r["id"],), True)["n"]
    return d


def ser_client(c):
    links = q("""SELECT ci.*, ib.name AS ib_name, ib.proto AS ib_proto FROM client_inbound ci JOIN inbounds ib ON ib.id=ci.inbound_id
                 WHERE ci.client_id=? ORDER BY ib.id""", (c["id"],))
    d = {k: c[k] for k in ("id", "name", "token", "enabled", "reason", "public_key", "limit_bytes", "up_bytes",
                           "down_bytes", "expiry", "note", "created", "last_seen", "reset_period", "owner_id", "ext_id")}
    d["state"] = client_state(c)
    d["sub_url"] = f"{base_url()}/sub/{c['token']}"
    d["online"] = any(l["last_hs"] and now() - l["last_hs"] < 180 for l in links)
    d["links"] = [dict(inbound_id=l["inbound_id"], ib_name=l["ib_name"], ip4=l["ip4"], ip6=l["ip6"],
                       allowed_ips=l["allowed_ips"], keepalive=l["keepalive"], dns=l["dns"], mtu=l["mtu"],
                       extra_allowed=l["extra_allowed"], last_hs=l["last_hs"], endpoint=l["endpoint"],
                       proto=l["ib_proto"] or "wg", l2tp_user=l["l2tp_user"], l2tp_pass=l["l2tp_pass"],
                       vuuid=l["vuuid"]) for l in links]
    for L_ in d["links"]:
        if L_["proto"] == "vless" and L_["vuuid"]:
            try:
                L_["vlink"] = vless_link(c, L_, q("SELECT * FROM inbounds WHERE id=?", (L_["inbound_id"],), True))
            except Exception:
                L_["vlink"] = ""
    return d


# ------------------------------ امنیت و تنظیمات پنل ------------------------------
RUN = {"port": PANEL_PORT, "tls": False, "cert_mtime": 0}


def hash_pw(p, salt=None, it=240000):
    salt = salt or secrets.token_hex(16)
    return f"pbkdf2${it}${salt}${hashlib.pbkdf2_hmac('sha256', p.encode(), salt.encode(), it).hex()}"


def check_pw(p, stored):
    try:
        _, it, salt, h = stored.split("$")
        return hmac.compare_digest(hashlib.pbkdf2_hmac("sha256", p.encode(), salt.encode(), int(it)).hex(), h)
    except Exception:
        return False


def admin_user():
    return setting("admin_user") or ADMIN_USER


def check_login(u, p):
    h = setting("admin_hash")
    ok_p = check_pw(p, h) if h else hmac.compare_digest(p.encode(), ADMIN_PASS.encode())
    return hmac.compare_digest(u.encode(), admin_user().encode()) & ok_p


def panel_cfg():
    return dict(port=num(setting("panel_port"), PANEL_PORT, 1, 65535), domain=setting("panel_domain"),
                path=setting("panel_path"), cert=setting("tls_cert"), key=setting("tls_key"),
                allowed_ips=setting("allowed_ips"))


def tls_files():
    c, k = setting("tls_cert"), setting("tls_key")
    return (c, k) if c and k and os.path.isfile(c) and os.path.isfile(k) else None


def panel_info():
    c = panel_cfg()
    tls = bool(tls_files())
    c.update(tls_on=tls, run_port=RUN["port"], user=admin_user(), default_pass=not setting("admin_hash"),
             restart_needed=(c["port"] != RUN["port"] or tls != RUN["tls"]), certbot=bool(shutil.which("certbot")))
    return c


def panel_url():
    c = panel_cfg(); tls = bool(tls_files())
    host = c["domain"] or (urlsplit("//" + request.host).hostname or "localhost")
    if ":" in host:
        host = f"[{host}]"
    d = f"{'https' if tls else 'http'}://{host}"
    if (tls and c["port"] != 443) or (not tls and c["port"] != 80):
        d += f":{c['port']}"
    return d + "/" + (c["path"] + "/" if c["path"] else "")


def port_free(port):
    s_ = socket.socket()
    try:
        s_.bind((PANEL_HOST, port))
        return True
    except OSError:
        return False
    finally:
        s_.close()


def restart_later(delay=1.2):
    def go():
        time.sleep(delay)
        os.execv(sys.executable, [sys.executable] + sys.argv)
    threading.Thread(target=go, daemon=True).start()


def check_cert():
    t = tls_files()
    if t and RUN["tls"] and RUN["cert_mtime"]:
        try:
            if os.path.getmtime(t[0]) != RUN["cert_mtime"]:
                log.info("گواهی تمدید شد؛ ری‌استارت پنل")
                restart_later(1)
        except OSError:
            pass


class PrefixMW:
    """مسیر مخفی پنل: همه چیز جز /sub/ فقط زیر /<path>/ در دسترس است"""
    def __init__(self, wsgi):
        self.wsgi = wsgi

    def __call__(self, env, start):
        pre = setting("panel_path")
        path = env.get("PATH_INFO", "")
        if pre and not path.startswith("/sub/"):
            p = "/" + pre
            if path == p or path.startswith(p + "/"):
                env["SCRIPT_NAME"] = p
                env["PATH_INFO"] = path[len(p):] or "/"
            else:
                start("404 Not Found", [("Content-Type", "text/plain")])
                return [b"Not Found"]
        return self.wsgi(env, start)


app.wsgi_app = PrefixMW(app.wsgi_app)


@app.before_request
def guard():
    if request.path.startswith("/sub/"):
        return
    allow = setting("allowed_ips")
    if allow:
        try:
            ip = ipaddress.ip_address(request.remote_addr or "")
            ok = any(ip in ipaddress.ip_network(n, strict=False) for n in allow.split(", ") if n)
        except Exception:
            ok = False
        if not ok:
            abort(403)


@app.after_request
def sec_headers(r):
    h = r.headers
    if request.path.startswith("/api/"):
        h["Cache-Control"] = "no-store"
    h.setdefault("X-Frame-Options", "DENY")
    h.setdefault("X-Content-Type-Options", "nosniff")
    h.setdefault("Referrer-Policy", "no-referrer")
    h.setdefault("X-Robots-Tag", "noindex, nofollow")
    if r.mimetype == "text/html":
        h["Content-Security-Policy"] = ("default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; "
                                       "img-src 'self' data:; frame-ancestors 'none'; base-uri 'none'; form-action 'self'")
    if RUN["tls"]:
        h["Strict-Transport-Security"] = "max-age=15552000"
    return r


@app.put("/api/panel")
@auth
def panel_save():
    d = body()
    port = num(d.get("port"), PANEL_PORT, 1, 65535, "پورت پنل")
    if port != RUN["port"] and not port_free(port):
        raise Err(f"پورت {port} روی سرور در حال استفاده است")
    domain = str(d.get("domain", "")).strip().lower()
    if domain and not re.fullmatch(r"[a-z0-9]([a-z0-9.\-]*[a-z0-9])?", domain):
        raise Err("دامنه نامعتبر است")
    path = str(d.get("path", "")).strip().strip("/")
    if path and (not re.fullmatch(r"[A-Za-z0-9_\-]{3,40}", path) or path in ("api", "sub")):
        raise Err("مسیر مخفی باید ۳ تا ۴۰ حرف انگلیسی/عدد/_/- باشد (و api یا sub نباشد)")
    cert, key = str(d.get("cert", "")).strip(), str(d.get("key", "")).strip()
    if cert or key:
        if not (cert and key):
            raise Err("مسیر گواهی و کلید هر دو لازم است")
        try:
            ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER).load_cert_chain(cert, key)
        except Exception as e:
            raise Err(f"گواهی/کلید معتبر نیست یا خوانده نمی‌شود: {e}")
    allow = check_cidrs(d.get("allowed_ips"), "IP مجاز")
    if allow:
        me = ipaddress.ip_address(request.remote_addr or "0.0.0.0")
        if not any(me in ipaddress.ip_network(n, strict=False) for n in allow.split(", ")):
            raise Err(f"آی‌پی فعلی شما ({me}) در لیست نیست؛ برای جلوگیری از قفل شدن ذخیره نشد")
    for k, v in (("panel_port", port), ("panel_domain", domain), ("panel_path", path), ("tls_cert", cert),
                 ("tls_key", key), ("allowed_ips", allow)):
        set_setting(k, v)
    return jsonify(ok=True, url=panel_url())


@app.post("/api/panel/restart")
@auth
def panel_restart():
    url = panel_url()
    restart_later()
    return jsonify(ok=True, url=url)


@app.post("/api/panel/cert")
@auth
def panel_cert():
    d = body()
    domain = str(d.get("domain", "")).strip().lower()
    email = str(d.get("email", "")).strip()
    if not re.fullmatch(r"([a-z0-9]([a-z0-9\-]*[a-z0-9])?\.)+[a-z]{2,}", domain):
        raise Err("دامنه نامعتبر است")
    if not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email):
        raise Err("ایمیل نامعتبر است")
    if not shutil.which("certbot"):
        raise Err("certbot نصب نیست: apt install certbot")
    rc, o, e = run(["certbot", "certonly", "--standalone", "--preferred-challenges", "http", "--non-interactive",
                    "--agree-tos", "-m", email, "-d", domain], timeout=240)
    if rc != 0:
        raise Err("certbot ناموفق بود (پورت 80 آزاد است؟ دامنه به این سرور اشاره می‌کند؟): " + (e or o).strip()[-350:])
    live = f"/etc/letsencrypt/live/{domain}"
    set_setting("tls_cert", f"{live}/fullchain.pem"); set_setting("tls_key", f"{live}/privkey.pem")
    set_setting("panel_domain", domain)
    return jsonify(ok=True)


@app.post("/api/panel/account")
@auth
def panel_account():
    d = body()
    if not check_login(admin_user(), str(d.get("current", ""))):
        raise Err("رمز فعلی اشتباه است")
    user = str(d.get("user") or admin_user()).strip()
    if not re.fullmatch(r"[A-Za-z0-9_.\-]{3,32}", user):
        raise Err("نام کاربری باید ۳ تا ۳۲ حرف انگلیسی/عدد باشد")
    if q("SELECT 1 FROM admins WHERE lower(username)=lower(?)", (user,), True):
        raise Err("این نام کاربری برای یکی از ادمین‌ها استفاده شده است")
    pw = str(d.get("password") or "")
    if pw:
        if len(pw) < 10 or pw == ADMIN_PASS:
            raise Err("رمز جدید باید حداقل ۱۰ کاراکتر و غیر از رمز پیش‌فرض باشد")
        set_setting("admin_hash", hash_pw(pw))
    set_setting("admin_user", user)
    v = secrets.token_hex(8)
    set_setting("sess_ver", v)          # همه‌ی نشست‌های دیگر باطل می‌شوند
    session["v"] = v
    return jsonify(ok=True)


@app.get("/api/obf/generate")
@auth
def obf_generate():
    return jsonify(gen_obf(request.args.get("v", "3") if request.args.get("v") in ("1", "2", "3") else "3"))


@app.get("/api/vless/check-dest")
@auth
def vless_check_dest():
    dest = str(request.args.get("dest", "")).strip()
    m = re.fullmatch(r"([A-Za-z0-9.\-]+)(?::(\d{1,5}))?", dest)
    if not m:
        raise Err("Dest نامعتبر است (مثال www.microsoft.com:443)")
    return jsonify(check_reality_dest(m.group(1), int(m.group(2) or 443)))


@app.get("/api/vless/keys")
@auth
def vless_keys():
    priv, pub = reality_keypair()
    return jsonify(private_key=priv, public_key=pub, short_id=gen_short_id(), uuid=str(uuid.uuid4()))


@app.post("/api/login")
def login():
    ip = request.remote_addr or "?"
    n, t = FAILS.get(ip, (0, now()))
    if now() - t > 300:
        n, t = 0, now()
    if n >= 6:
        return jsonify(error="تلاش‌های زیاد؛ چند دقیقه بعد دوباره امتحان کنید"), 429
    d = body()
    u, p = str(d.get("u", "")), str(d.get("p", ""))
    if check_login(u, p):
        FAILS.pop(ip, None)
        session.clear()
        session.permanent = True
        session["u"] = 1
        session["role"] = "super"
        session["v"] = setting("sess_ver", "0")
        return jsonify(ok=True, role="super")
    a = q("SELECT * FROM admins WHERE lower(username)=lower(?)", (u,), True)
    if a and check_pw(p, a["pass_hash"]):
        if not a["enabled"]:
            return jsonify(error="حساب شما غیرفعال شده است؛ با مدیر تماس بگیرید"), 403
        FAILS.pop(ip, None)
        session.clear()
        session.permanent = True
        session["u"] = 1
        session["role"] = "admin"
        session["aid"] = a["id"]
        session["av"] = a["ver"]
        x("UPDATE admins SET last_login=? WHERE id=?", (now(), a["id"]))
        return jsonify(ok=True, role="admin")
    FAILS[ip] = (n + 1, t)
    return jsonify(error="نام کاربری یا رمز اشتباه است"), 401


@app.post("/api/logout")
def logout():
    session.clear()
    return jsonify(ok=True)


# ------------------------------ تانل بک‌پک (BackPack) ------------------------------
# سمت ایران = [server] با نام N ؛ سمت خارج = [client] با نام N-kharej (همان قرارداد نام‌گذاری خود بک‌پک).
# پنل با SSH به سرور مقابل وصل می‌شود، بک‌پک را نصب می‌کند، کانفیگ و سرویس هر دو سمت را می‌نویسد
# و وضعیت را با «backpack tunnel status» می‌خواند.
BP_BIN = "/usr/local/bin/backpack"
BP_DIR = "/etc/backpack"
BP_REL = "https://github.com/AminMGMT/BackPack/releases/latest/download"
BP_NAME = re.compile(r"^[a-z0-9][a-z0-9-]{0,30}$")
BP_JOBS = collections.OrderedDict()
BP_MIN_TRAFFIC = 64 * 1024           # کمتر از این مقدار ترافیک جدید = «برقرار شد» ؛ بیشتر = «آنلاین»

with LOCK:
    _db.execute("""CREATE TABLE IF NOT EXISTS tunnels(
      name TEXT PRIMARY KEY, base TEXT, role TEXT, remote_ip TEXT, ssh_port INTEGER, ssh_user TEXT,
      remote_name TEXT, transport TEXT, tunnel_port INTEGER, ports TEXT, base_bytes INTEGER DEFAULT 0, created INTEGER)""")
ensure_cols("tunnels", {"iran_node": "INTEGER DEFAULT -1", "kharej_node": "INTEGER DEFAULT -1"})
# iran_node / kharej_node: هر سمت تانل → 0 = همین سرور (پنل) ، عدد مثبت = id نود ، -1 = سرور دستی با SSH (یا ردیف قدیمی)

BP_INSTALL = r"""
set -e
if [ -x /usr/local/bin/backpack ]; then echo "already: $(/usr/local/bin/backpack -v 2>&1 | head -1)"; exit 0; fi
case "$(uname -m)" in x86_64|amd64) A=amd64;; aarch64|arm64) A=arm64;; *) echo "معماری پشتیبانی نمی‌شود: $(uname -m)"; exit 1;; esac
T=$(mktemp -d); cd "$T"
F="backpack_linux_$A.tar.gz"
curl -fsSL --retry 2 --connect-timeout 10 --max-time 180 -o "$F" "%(rel)s/$F"
curl -fsSL --retry 2 --connect-timeout 10 --max-time 30 -o SHA256SUMS "%(rel)s/SHA256SUMS"
awk -v f="$F" '$2==f||$2=="*"f{print $1"  "f}' SHA256SUMS | sha256sum -c - >/dev/null
tar xzf "$F"
B=$(find . -type f -name backpack | head -1)
[ -n "$B" ] || { echo "فایل backpack داخل آرشیو نبود"; exit 1; }
mkdir -p /etc/backpack /root/BackPack/backups
install -m 0755 "$B" /usr/local/bin/backpack
echo /root/BackPack > /etc/backpack/install_path
cd /; rm -rf "$T"
echo "installed: $(/usr/local/bin/backpack -v 2>&1 | head -1)"
""" % {"rel": BP_REL}


class _Local:
    label = "این سرور"

    def run(self, script, timeout=120):
        return run(["bash", "-c", script], timeout=timeout)

    def put(self, path, data, mode=0o600):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, mode)
        with os.fdopen(fd, "wb") as f:
            f.write(data if isinstance(data, bytes) else data.encode())
        os.chmod(path, mode)

    def get(self, path):
        with open(path, "rb") as f:
            return f.read()

    def close(self):
        pass


class _Remote:
    label = "سرور مقابل"

    def __init__(self, host, port, user, pw, key=None):
        try:
            import paramiko
        except ImportError:
            run(["apt-get", "install", "-y", "python3-paramiko"], timeout=240)
            try:
                import paramiko
            except ImportError:
                raise Err("کتابخانه paramiko نصب نیست؛ روی سرور بزنید: apt install python3-paramiko")
        self.c = paramiko.SSHClient()
        self.c.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        try:
            kw = dict(pkey=_pkey(key)) if key else dict(password=pw)
            self.c.connect(host, port=port, username=user, timeout=15, banner_timeout=20,
                           auth_timeout=20, look_for_keys=False, allow_agent=False, **kw)
        except paramiko.AuthenticationException:
            raise Err("نام کاربری یا رمز SSH اشتباه است")
        except Exception as e:
            raise Err(f"اتصال SSH برقرار نشد: {e}")

    def run(self, script, timeout=120):
        si, so, se = self.c.exec_command("bash -s", timeout=timeout)
        si.write(script); si.channel.shutdown_write()
        out = so.read().decode(errors="replace")
        err = se.read().decode(errors="replace")
        return so.channel.recv_exit_status(), out, err

    def put(self, path, data, mode=0o600):
        self.run(f"mkdir -p {os.path.dirname(path)}")
        sf = self.c.open_sftp()
        try:
            with sf.open(path, "wb") as f:
                f.write(data if isinstance(data, bytes) else data.encode())
            sf.chmod(path, mode)
        finally:
            sf.close()

    def get(self, path):
        sf = self.c.open_sftp()
        try:
            with sf.open(path, "rb") as f:
                return f.read()
        finally:
            sf.close()

    def close(self):
        try:
            self.c.close()
        except Exception:
            pass


class _NodeSess:
    """جلسه روی یک نودِ ثبت‌شده؛ از اتصال کش‌شده‌ی نود (کلید پنل) استفاده می‌کند، پس رمز SSH نمی‌خواهد و بسته هم نمی‌شود"""

    def __init__(self, n):
        self.n = n
        self.label = f"نود «{n['name']}»"

    def run(self, script, timeout=120):
        return node_call(self.n, lambda s: s.run(script, timeout=timeout))

    def put(self, path, data, mode=0o600):
        return node_call(self.n, lambda s: s.put(path, data, mode))

    def get(self, path):
        return node_call(self.n, lambda s: s.get(path))

    def close(self):
        pass


def tun_ends(m):
    """(سمت ایران، سمت خارج) یک ردیف جدول tunnels؛ 0 = همین سرور، >0 = id نود، -1 = سرور دستی با SSH"""
    i = -1 if m["iran_node"] is None else int(m["iran_node"])
    k = -1 if m["kharej_node"] is None else int(m["kharej_node"])
    if i == -1 and k == -1:                     # ردیف‌های قدیمی (قبل از قابلیت نود)
        return (0, -1) if m["role"] == "iran" else (-1, 0)
    return i, k


def tun_host(m):
    """سمتی که وضعیت و دکمه‌های کارت از آن خوانده می‌شود: (end, نام سرویس). اولویت: همین سرور ← نود سمت ایران ← نود سمت خارج"""
    ie, ke = tun_ends(m)
    base = m["base"]
    if ie == 0:
        return 0, base
    if ke == 0:
        return 0, base + "-kharej"
    if ie > 0:
        return ie, base
    return ke, base + "-kharej"


def bp_toml_server(name, port, token, ports, udp):
    pl = "".join(f'    {json.dumps(p)},\n' for p in ports)
    return (f'# Generated by backpack — do not edit while the service is running.\n# name = "{name}"\n\n[server]\n'
            f'bind_addr = "0.0.0.0:{port}"\ntransport = "stealth"\npreset = "turbo"\ntoken = {json.dumps(token)}\n'
            f'channel_size = 4096\nkeepalive_period = 75\nnodelay = true\nheartbeat = 40\nlog_level = "info"\n'
            f'so_rcvbuf = 8388608\nso_sndbuf = 8388608\naccept_udp = {"true" if udp else "false"}\n'
            f'proxy_protocol = false\nsniffer = false\nports = [\n{pl}]\n')


def bp_toml_client(name, addr, token):
    return (f'# Generated by backpack — do not edit while the service is running.\n# name = "{name}"\n\n[client]\n'
            f'remote_addr = {json.dumps(addr)}\ntransport = "stealth"\npreset = "turbo"\ntoken = {json.dumps(token)}\n'
            f'connection_pool = 8\naggressive_pool = false\nkeepalive_period = 75\nnodelay = true\nretry_interval = 3\n'
            f'dial_timeout = 10\nlog_level = "info"\nso_rcvbuf = 8388608\nso_sndbuf = 8388608\nsniffer = false\n')


def bp_unit(name):
    return (f"[Unit]\nDescription=Backpack Tunnel ({name})\nAfter=network.target\n\n[Service]\nType=simple\n"
            f"ExecStart={BP_BIN} -c {BP_DIR}/{name}.toml\nRestart=always\nRestartSec=3\nLimitNOFILE=1048576\n\n"
            f"[Install]\nWantedBy=multi-user.target\n")


def bp_remove_script(name):
    return (f"systemctl disable --now backpack-{name} >/dev/null 2>&1; "
            f"rm -f /etc/systemd/system/backpack-{name}.service {BP_DIR}/{name}.toml {BP_DIR}/{name}.metrics.json; "
            f"systemctl daemon-reload")


def bp_status(name):
    rc, o, _ = run([BP_BIN, "tunnel", "status", name, "--json"], timeout=15)
    try:
        return json.loads(o)
    except Exception:
        return None


def bp_list():
    if not os.path.exists(BP_BIN):
        return None
    rc, o, _ = run([BP_BIN, "tunnel", "list", "--json"], timeout=20)
    try:
        d = json.loads(o)
    except Exception:
        return []
    if isinstance(d, dict):
        d = d.get("tunnels") or []
    return [t for t in d if isinstance(t, dict) and t.get("name")]


def bp_phase(t, base):
    if str(t.get("state")) != "online":
        return "down"
    tr = t.get("traffic") or {}
    total = int(tr.get("bytes_in") or 0) + int(tr.get("bytes_out") or 0)
    return "online" if total - int(base or 0) >= BP_MIN_TRAFFIC else "ready"


def bp_open_fw(sess, ports, udp):
    cmds = []
    for p in ports:
        p = p.replace("-", ":")
        cmds.append(f"ufw allow {p}/tcp >/dev/null")
        if udp:
            cmds.append(f"ufw allow {p}/udp >/dev/null")
    sess.run('command -v ufw >/dev/null && ufw status 2>/dev/null | grep -q "Status: active" && { '
             + "; ".join(cmds) + "; } || true", timeout=40)


def bp_status_on(sess, name):
    if isinstance(sess, _Local):
        return bp_status(name)
    rc, o, _ = sess.run(f"{BP_BIN} tunnel status {shlex.quote(name)} --json", timeout=25)
    try:
        return json.loads(o)
    except Exception:
        return None


def bp_job(j, d):
    """کار اصلی ساخت تانل؛ در یک ترد جدا اجرا می‌شود و مراحل را در j['steps'] می‌نویسد.
    هر سمت تانل می‌تواند همین سرور (0)، یک نودِ ثبت‌شده (>0، بدون رمز) یا یک سرور دستی با SSH (-1) باشد."""
    steps = j["steps"]
    made = []            # [(sess, service_name)] برای پاک‌سازی در صورت شکست
    rs = None
    loc = _Local()

    def step(t):
        s = {"t": t, "s": "run", "m": ""}
        steps.append(s)
        return s

    def ok(s, m=""):
        s["s"] = "ok"; s["m"] = m

    try:
        ie, ke = d["iran"], d["kharej"]
        base = d["name"]
        iname, kname = base, base + "-kharej"
        nodes = {}

        def mk(e):
            nonlocal rs
            if e == 0:
                return loc
            if e > 0:
                n = q("SELECT * FROM nodes WHERE id=?", (e,), True)
                if not n:
                    raise Err("نودِ انتخاب‌شده پیدا نشد")
                nodes[e] = n
                return _NodeSess(n)
            rs = _Remote(d["remote_ip"], d["ssh_port"], d["ssh_user"], d["ssh_pass"])
            return rs

        s = step("اتصال به سرورها")
        iran, kharej = mk(ie), mk(ke)
        info, msgs = {}, []
        for sess in (iran, kharej):
            if sess is loc:
                continue
            rc, o, e = sess.run('id -u; uname -m; echo "${SSH_CONNECTION%% *}"')
            f = o.split()
            if len(f) < 2 or f[0] != "0":
                raise Err(f"کاربر SSH روی {sess.label} باید root باشد")
            info[sess] = f
            msgs.append(f"{sess.label} ({f[1]})")
        ok(s, "متصل شد: " + "، ".join(msgs))

        # سمتی که پنل وضعیتش را بعداً می‌خواند: همین سرور، وگرنه یکی از نودها (سرور دستی بعد از ساخت در دسترس نیست)
        cand = [(ie, iran, iname), (ke, kharej, kname)]
        hend, hsess, hname = next((c for c in cand if c[0] == 0), None) or next(c for c in cand if c[0] > 0)

        s = step("بررسی تداخل نام و پورت")
        old = q("SELECT * FROM tunnels WHERE name=?", (hname,), True)
        if old and tun_host(old)[0] != hend:
            raise Err(f"یک تانل دیگر با نام «{hname}» در پنل ثبت شده؛ نام دیگری بدهید")
        for sess, nm in ((iran, iname), (kharej, kname)):
            if sess.run(f"test -e {BP_DIR}/{nm}.toml")[0] == 0:
                raise Err(f"روی {sess.label} از قبل تانلی با نام «{nm}» وجود دارد")
        rc, o, _ = iran.run("ss -Hltn | awk '{print $4}' | sed 's/.*://' | sort -u")
        busy = set(o.split())
        need = [str(d["tunnel_port"])] + [p.split("=")[0] for p in d["ports"] if p.split("=")[0].isdigit()]
        for p in need:
            if p in busy:
                raise Err(f"پورت {p} روی {iran.label} (سمت ایران) در حال استفاده است")
        ok(s)

        s = step("نصب بک‌پک روی هر دو سرور")
        res = {}
        for sess in (iran, kharej):
            rc, o, e = sess.run(BP_INSTALL, timeout=300)
            res[sess] = (rc == 0, (o + e).strip().splitlines()[-1:] or [""])
        if not res[iran][0] and not res[kharej][0]:
            raise Err("نصب بک‌پک روی هر دو سرور ناموفق بود: " + res[iran][1][0] + " | " + res[kharej][1][0])
        if not (res[iran][0] and res[kharej][0]):
            src, dst = (iran, kharej) if res[iran][0] else (kharej, iran)
            if src.run("uname -m")[1].strip() != dst.run("uname -m")[1].strip():
                raise Err(f"نصب روی {dst.label} نشد (به GitHub دسترسی ندارد) و معماری دو سرور فرق دارد")
            dst.run(f"mkdir -p {BP_DIR} /root/BackPack/backups")
            dst.put(BP_BIN, src.get(BP_BIN), 0o755)
            dst.run(f"echo /root/BackPack > {BP_DIR}/install_path")
            ok(s, f"روی {dst.label} از طریق کپی از {src.label} نصب شد")
        else:
            ok(s, "نصب شد")
        for sess in (iran, kharej):
            if sess.run(f"{BP_BIN} -v")[0] != 0:
                raise Err(f"بک‌پک روی {sess.label} اجرا نمی‌شود")

        s = step("ساخت کانفیگ و سرویس هر دو سمت")
        token = "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(64))
        if d["my_ip"]:
            my_ip = d["my_ip"]
        elif ie == 0:                       # آی‌پی پنل از دید سرور مقابل (SSH_CONNECTION)
            fk = info.get(kharej) or []
            my_ip = fk[2] if len(fk) > 2 else ""
        elif ie > 0:
            my_ip = nodes[ie]["address"]
        else:
            my_ip = d["remote_ip"]
        if not my_ip:
            raise Err("آی‌پی سرور ایران تشخیص داده نشد؛ در فرم وارد کنید")
        addr = f"[{my_ip}]:{d['tunnel_port']}" if ":" in my_ip else f"{my_ip}:{d['tunnel_port']}"
        plan = ((iran, iname, bp_toml_server(iname, d["tunnel_port"], token, d["ports"], d["udp"])),
                (kharej, kname, bp_toml_client(kname, addr, token)))
        for sess, nm, toml in plan:
            sess.put(f"{BP_DIR}/{nm}.toml", toml, 0o600)
            made.append((sess, nm))
            rc, o, e = sess.run(f"{BP_BIN} check -c {BP_DIR}/{nm}.toml")
            if rc != 0:
                raise Err(f"کانفیگ روی {sess.label} معتبر نیست: {(o + e).strip()[:300]}")
            sess.put(f"/etc/systemd/system/backpack-{nm}.service", bp_unit(nm), 0o644)
        ok(s)

        s = step("باز کردن پورت‌ها در فایروال (اگر ufw فعال باشد)")
        bp_open_fw(iran, [str(d["tunnel_port"])] + [p.split("=")[0] for p in d["ports"]], d["udp"])
        ok(s)

        s = step("راه‌اندازی سرویس‌ها (اول ایران، بعد خارج)")
        for sess, nm, _t in plan:
            rc, o, e = sess.run(f"systemctl daemon-reload && systemctl enable --now backpack-{nm}")
            if rc != 0:
                raise Err(f"راه‌اندازی سرویس روی {sess.label} ناموفق بود: {(o + e).strip()[:300]}")
        ok(s)

        s = step("انتظار برای برقراری تانل")
        t0, st = time.time(), None
        while time.time() - t0 < 75:
            try:
                st = bp_status_on(hsess, hname)
            except Err:
                st = None
            if st and st.get("state") == "online":
                break
            time.sleep(2)
        if st and st.get("state") == "online":
            tr = st.get("traffic") or {}
            bb = int(tr.get("bytes_in") or 0) + int(tr.get("bytes_out") or 0)
            ok(s, "تانل برقرار شد ✔")
            j["state"] = "done"
        else:
            s["s"] = "warn"
            s["m"] = "سرویس‌ها بالا آمدند ولی هنوز اتصال برقرار نشد: " + str((st or {}).get("detail") or "نامشخص")
            bb = 0
            j["state"] = "warn"
        role = "iran" if ie == 0 else "kharej" if ke == 0 else ""
        peer = ke if ie == 0 else ie if ke == 0 else ke
        remote_ip = d["remote_ip"] if -1 in (ie, ke) else (nodes[peer]["address"] if peer > 0 else "")
        x("""INSERT OR REPLACE INTO tunnels(name,base,role,remote_ip,ssh_port,ssh_user,remote_name,transport,tunnel_port,ports,base_bytes,created,iran_node,kharej_node)
             VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
          (hname, base, role, remote_ip, d["ssh_port"], d["ssh_user"], kname if hname == iname else iname, "stealth",
           d["tunnel_port"], ", ".join(d["ports"]), bb, now(), ie, ke))
        BP_NODE_CACHE.clear()
        made.clear()
    except Exception as e:
        log.warning("bp_job: %s", e)
        for s_ in steps:
            if s_["s"] == "run":
                s_["s"] = "err"; s_["m"] = str(e)
        if not steps or steps[-1]["s"] != "err":
            steps.append({"t": "خطا", "s": "err", "m": str(e)})
        for sess, nm in made:
            try:
                sess.run(bp_remove_script(nm))
            except Exception:
                pass
        j["state"] = "failed"
    finally:
        if rs:
            rs.close()


def bp_end(v, label):
    v = str(v or "").strip()
    if v == "local":
        return 0
    if v == "ssh":
        return -1
    m = re.fullmatch(r"node:(\d+)", v)
    if m:
        nid = int(m.group(1))
        if not q("SELECT 1 FROM nodes WHERE id=?", (nid,), True):
            raise Err(f"نودِ سمت {label} پیدا نشد")
        return nid
    raise Err(f"سرور سمت {label} را انتخاب کنید")


def bp_parse_new(d):
    iv, kv = d.get("iran"), d.get("kharej")
    if not iv and not kv:                       # سازگاری با فرم قدیمی (role + سرور مقابل با SSH)
        role = str(d.get("role") or "")
        if role not in ("iran", "kharej"):
            raise Err("سرور ایران و سرور خارج را انتخاب کنید")
        iv, kv = ("local", "ssh") if role == "iran" else ("ssh", "local")
    ie, ke = bp_end(iv, "ایران"), bp_end(kv, "خارج")
    if ie == ke:
        raise Err("فقط یکی از دو سمت می‌تواند سرور دستی (SSH) باشد" if ie == -1
                  else "سمت ایران و سمت خارج نباید یک سرور باشند")
    name = str(d.get("name") or "").strip().lower()
    if not BP_NAME.fullmatch(name) or name.endswith("-kharej"):
        raise Err("نام تانل: فقط حرف کوچک انگلیسی، عدد و - (حداکثر ۳۱ کاراکتر) و بدون -kharej در انتها")
    host, user, pw = "", "root", ""
    if -1 in (ie, ke):
        host = str(d.get("remote_ip") or "").strip()
        if not re.fullmatch(r"[A-Za-z0-9.\-:]{3,253}", host):
            raise Err("آی‌پی یا آدرس سرور دستی نامعتبر است")
        user = str(d.get("ssh_user") or "root").strip()
        if not re.fullmatch(r"[A-Za-z0-9_.\-]{1,32}", user):
            raise Err("نام کاربری SSH نامعتبر است")
        pw = str(d.get("ssh_pass") or "")
        if not pw:
            raise Err("رمز SSH سرور دستی را وارد کنید")
    my_ip = str(d.get("my_ip") or "").strip()
    if my_ip:
        try:
            ipaddress.ip_address(my_ip)
        except Exception:
            raise Err("آی‌پی عمومی سرور ایران نامعتبر است")
    ports = []
    for p in re.split(r"[,\s]+", str(d.get("ports") or "").strip()):
        if not p:
            continue
        m = re.fullmatch(r"(\d{1,5})(?:-(\d{1,5}))?(?:=([A-Za-z0-9.\-:\[\]]+))?", p)
        if not m or not all(1 <= int(v) <= 65535 for v in m.groups()[:2] if v):
            raise Err(f"پورت «{p}» نامعتبر است (نمونه: 443 یا 443,8443 یا 443=127.0.0.1:2096)")
        ports.append(p)
    if not ports:
        raise Err("حداقل یک پورت برای عبور از تانل وارد کنید")
    return dict(iran=ie, kharej=ke, name=name, remote_ip=host, my_ip=my_ip, ssh_user=user, ssh_pass=pw,
                ssh_port=num(d.get("ssh_port"), 22, 1, 65535, "پورت SSH"),
                tunnel_port=num(d.get("tunnel_port"), 8719, 1, 65535, "پورت تانل"), ports=ports, udp=bool(d.get("udp")))


BP_NODE_CACHE = {}       # id نود → (زمان، لیست تانل‌ها یا None، پیام خطا)؛ برای اینکه رفرش ۵ثانیه‌ی صفحه به SSH نودها فشار نیاورد


def bp_node_list(n):
    c = BP_NODE_CACHE.get(n["id"])
    if c and time.time() - c[0] < 8:
        return c[1], c[2]
    st = NODE_STATE.get(n["id"]) or {}
    if st and not st.get("ok", True):
        r = (time.time(), None, "نود در دسترس نیست: " + str(st.get("err") or "")[:120])
    else:
        try:
            rc, o, e = node_call(n, lambda s: s.run(
                f"if [ -x {BP_BIN} ]; then {BP_BIN} tunnel list --json; else echo '[]'; fi", timeout=25))
            try:
                dd = json.loads(o)
            except Exception:
                dd = []
            if isinstance(dd, dict):
                dd = dd.get("tunnels") or []
            r = (time.time(), [t for t in dd if isinstance(t, dict) and t.get("name")], "")
        except Err as e:
            r = (time.time(), None, str(e)[:160])
    BP_NODE_CACHE[n["id"]] = r
    return r[1], r[2]


@app.get("/api/tunnels")
@auth
def tun_list():
    lst = bp_list()
    rows = q("SELECT * FROM tunnels")
    nodes = {n["id"]: n for n in q("SELECT * FROM nodes")}

    def lab(e, m):
        if e == 0:
            return "این سرور"
        if e > 0:
            n = nodes.get(e)
            return f"نود «{n['name']}»" if n else "نودِ حذف‌شده"
        return m["remote_ip"] or "سرور دستی"

    def extra(m):
        ie, ke = tun_ends(m)
        peer = ke if ie == 0 else ie if ke == 0 else None
        return dict(managed=True, needs_pw=-1 in (ie, ke),
                    remote_ip=lab(peer, m) if peer is not None else "",
                    route=f"ایران: {lab(ie, m)} ← خارج: {lab(ke, m)}")

    local_meta, node_rows = {}, {}
    for r in rows:
        end, svc = tun_host(r)
        if end == 0:
            local_meta[r["name"]] = r
        else:
            node_rows.setdefault(end, []).append((svc, r))
    out = []
    for t in lst or []:
        m = local_meta.get(t["name"])
        t = dict(t)
        t["phase"] = bp_phase(t, m["base_bytes"] if m else 0)
        t["managed"], t["remote_ip"], t["host"] = bool(m), "", 0
        if m:
            t.update(extra(m))
        out.append(t)
    res = {}

    def fetch(n):
        res[n["id"]] = bp_node_list(n)

    ths = [threading.Thread(target=fetch, args=(nodes[e],), daemon=True) for e in node_rows if e in nodes]
    for th in ths:
        th.start()
    for th in ths:
        th.join(30)
    for e, items in node_rows.items():
        n = nodes.get(e)
        nl, err = res.get(e, (None, "" if n else "نودِ این تانل از پنل حذف شده"))
        for svc, r in items:
            t = next((a for a in (nl or []) if a["name"] == svc), None)
            if t is None:
                t = dict(name=svc, role="server" if svc == r["base"] else "client", state="unknown", transport="stealth",
                         detail=err or "تانل روی نود پیدا نشد")
            t = dict(t)
            t["phase"] = bp_phase(t, r["base_bytes"])
            t.update(extra(r))
            t["host"], t["host_name"] = e, (n["name"] if n else "حذف‌شده")
            out.append(t)
    return jsonify(installed=lst is not None, tunnels=out)


@app.post("/api/tunnels")
@auth
def tun_create():
    d = bp_parse_new(body())
    for j in BP_JOBS.values():
        if j["state"] == "run":
            raise Err("یک تانل دیگر در حال ساخت است؛ صبر کنید")
    jid = secrets.token_hex(6)
    j = {"state": "run", "steps": [], "name": d["name"]}
    BP_JOBS[jid] = j
    while len(BP_JOBS) > 20:
        BP_JOBS.popitem(last=False)
    threading.Thread(target=bp_job, args=(j, d), daemon=True).start()
    return jsonify(ok=True, job=jid)


@app.get("/api/tunnels/job/<jid>")
@auth
def tun_job(jid):
    j = BP_JOBS.get(jid)
    if not j:
        raise Err("کار پیدا نشد")
    return jsonify(state=j["state"], steps=j["steps"], name=j["name"])


def _tun_node(nid):
    n = q("SELECT * FROM nodes WHERE id=?", (nid,), True)
    if not n:
        raise Err("نودِ این تانل پیدا نشد")
    return n


@app.post("/api/tunnels/<name>/<action>")
@auth
def tun_action(name, action):
    if not BP_NAME.fullmatch(name) or action not in ("start", "stop", "restart"):
        raise Err("درخواست نامعتبر")
    nid = num(request.args.get("node"), 0, 0, None, "نود")
    if nid:
        n = _tun_node(nid)
        rc, o, e = node_call(n, lambda s: s.run(f"systemctl {action} backpack-{name}", timeout=40))
        BP_NODE_CACHE.pop(nid, None)
    else:
        rc, o, e = run(["systemctl", action, f"backpack-{name}"], timeout=40)
    if rc != 0:
        raise Err((e or o or "خطا").strip()[:300])
    return jsonify(ok=True)


@app.delete("/api/tunnels/<name>")
@auth
def tun_delete(name):
    if not BP_NAME.fullmatch(name):
        raise Err("نام نامعتبر")
    d = body()
    nid = num(request.args.get("node"), 0, 0, None, "نود")
    m = q("SELECT * FROM tunnels WHERE name=?", (name,), True)
    if m and tun_host(m)[0] != nid:
        m = None
    if not m:
        if nid:
            raise Err("تانل ثبت‌شده‌ی این نود پیدا نشد")
        run(["bash", "-c", bp_remove_script(name)], timeout=40)          # تانل بدون ثبت در پنل: فقط همین سرور
        return jsonify(ok=True, warn="")
    warn = []
    pw = str(d.get("ssh_pass") or "")
    ie, ke = tun_ends(m)
    for end, svc in ((ie, m["base"]), (ke, m["base"] + "-kharej")):
        rs = None
        try:
            if end == 0:
                run(["bash", "-c", bp_remove_script(svc)], timeout=40)
            elif end > 0:
                n = q("SELECT * FROM nodes WHERE id=?", (end,), True)
                if not n:
                    warn.append(f"نودِ سرویس «backpack-{svc}» از پنل حذف شده؛ آن را روی خود سرور پاک کنید")
                else:
                    node_call(n, lambda s, sv=svc: s.run(bp_remove_script(sv), timeout=40))
            elif pw:
                rs = _Remote(m["remote_ip"], m["ssh_port"], m["ssh_user"], pw)
                rs.run(bp_remove_script(svc))
            else:
                warn.append(f"سرویس «backpack-{svc}» روی سرور دستی حذف نشد؛ خودتان آن را حذف کنید")
        except Exception as e:
            warn.append(f"حذف «{svc}» ناموفق بود: {e}")
        finally:
            if rs:
                rs.close()
    BP_NODE_CACHE.clear()
    x("DELETE FROM tunnels WHERE name=?", (name,))
    return jsonify(ok=True, warn=" — ".join(warn))


# ------------------------------ نودها (Xray روی سرورهای دیگر) ------------------------------
# نود = یک سرور جدا که پنل با SSH به آن وصل می‌شود و اینباندهای VLESS را روی آن اجرا می‌کند.
# رمز SSH فقط یک‌بار (هنگام افزودن) برای نصب کلید پنل روی نود استفاده می‌شود و ذخیره نمی‌شود؛
# بعد از آن، پنل با همان کلید به نود وصل می‌شود. خود پنل هم «نود اصلی» حساب می‌شود (node_id=0).
NODE_JOBS = collections.OrderedDict()
NODE_STATE = {}            # id نود → dict(ok, ts, err, up={نام اینباند: bool}, ver)
NODE_DIRTY = set()         # اینباندهایی که اعمالشان روی نود نشد؛ بعد از وصل شدن نود دوباره امتحان می‌شود
_NODE_CONN, _NODE_LK, _NODE_G = {}, {}, threading.Lock()

XRAY_NODE_INSTALL = r"""
set -e
XB=$(command -v xray 2>/dev/null || true)
if [ -z "$XB" ] && [ -x /usr/local/bin/xray ]; then XB=/usr/local/bin/xray; fi
if [ -n "$XB" ]; then echo "BIN=$XB"; "$XB" version | head -1; exit 0; fi
case "$(uname -m)" in x86_64|amd64) A=64;; aarch64|arm64) A=arm64-v8a;; armv7l) A=arm32-v7a;; i686|i386) A=32;; s390x) A=s390x;; *) echo "معماری پشتیبانی نمی‌شود: $(uname -m)"; exit 3;; esac
command -v curl >/dev/null 2>&1 || { apt-get update -qq >/dev/null 2>&1 || true; apt-get install -y -qq curl ca-certificates >/dev/null 2>&1 || true; }
T=$(mktemp -d); cd "$T"
curl -fsSL --retry 2 --connect-timeout 10 --max-time 240 -o x.zip "https://github.com/XTLS/Xray-core/releases/latest/download/Xray-linux-$A.zip" || { echo "دانلود از GitHub ناموفق بود"; exit 4; }
if command -v unzip >/dev/null 2>&1; then unzip -o -q x.zip xray; else python3 -c "import zipfile; zipfile.ZipFile('x.zip').extract('xray')"; fi
install -m 0755 xray /usr/local/bin/xray
cd /; rm -rf "$T"
echo "BIN=/usr/local/bin/xray"; /usr/local/bin/xray version | head -1
"""


def _paramiko():
    try:
        import paramiko
    except ImportError:
        run(["apt-get", "install", "-y", "python3-paramiko"], timeout=240)
        try:
            import paramiko
        except ImportError:
            raise Err("کتابخانه paramiko نصب نیست؛ روی سرور بزنید: apt install python3-paramiko")
    return paramiko


def _pkey(pem):
    p = _paramiko()
    for cls in (p.ECDSAKey, p.RSAKey, p.Ed25519Key):
        try:
            return cls.from_private_key(io.StringIO(pem))
        except Exception:
            continue
    raise Err("کلید SSH پنل خوانده نشد")


def node_key():
    """کلید SSH مخصوص پنل (یک‌بار ساخته می‌شود)؛ کلید عمومی‌اش روی هر نود نصب می‌شود"""
    k = setting("node_ssh_key")
    if k:
        return k
    p = _paramiko()
    try:
        key = p.ECDSAKey.generate()
    except Exception:
        key = p.RSAKey.generate(3072)
    buf = io.StringIO()
    key.write_private_key(buf)
    set_setting("node_ssh_key", buf.getvalue())
    return buf.getvalue()


def node_pub():
    k = _pkey(node_key())
    return f"{k.get_name()} {k.get_base64()} sepipanel"


def _node_lock(nid):
    with _NODE_G:
        return _NODE_LK.setdefault(nid, threading.RLock())


def node_drop(nid):
    c = _NODE_CONN.pop(nid, None)
    if c is not None:
        c.close()


def node_sess(n):
    nid = n["id"]
    c = _NODE_CONN.get(nid)
    if c is not None:
        try:
            tr = c.c.get_transport()
            if tr is not None and tr.is_active():
                return c
        except Exception:
            pass
        node_drop(nid)
    c = _Remote(n["address"], n["ssh_port"], n["ssh_user"], None, key=node_key())
    _NODE_CONN[nid] = c
    return c


def node_call(n, fn):
    """fn(sess) را روی اتصال کش‌شدهٔ نود اجرا می‌کند؛ اگر اتصال افتاده بود یک‌بار دوباره وصل می‌شود"""
    with _node_lock(n["id"]):
        last = None
        for _ in range(2):
            s = node_sess(n)             # اتصال/احراز هویت ناموفق → Err
            try:
                return fn(s)
            except (socket.timeout, TimeoutError):
                node_drop(n["id"])
                raise Err(f"نود «{n['name']}» جواب نداد (timeout)")
            except Err:
                raise
            except Exception as e:
                last = e
                node_drop(n["id"])
                log.warning("node %s: %s", n["name"], e)
        raise Err(f"ارتباط با نود «{n['name']}» قطع شد: {str(last)[:150]}")


def node_up(ib):
    st = NODE_STATE.get(ib_node(ib)) or {}
    return bool((st.get("up") or {}).get(ib["name"]))


def node_fw_script(ib, add):
    net, port = xray_net(ib), int(ib["port"])
    ufw = "command -v ufw >/dev/null 2>&1 && ufw status 2>/dev/null | grep -q 'Status: active'"
    if add:
        return (f"command -v iptables >/dev/null 2>&1 && ! iptables -C INPUT -p {net} --dport {port} -j ACCEPT 2>/dev/null "
                f"&& iptables -I INPUT -p {net} --dport {port} -j ACCEPT; {ufw} && ufw allow {port}/{net} >/dev/null 2>&1; true")
    return (f"command -v iptables >/dev/null 2>&1 && while iptables -C INPUT -p {net} --dport {port} -j ACCEPT 2>/dev/null; "
            f"do iptables -D INPUT -p {net} --dport {port} -j ACCEPT; done; {ufw} && ufw delete allow {port}/{net} >/dev/null 2>&1; true")


def apply_vless_remote(ib, restart=False):
    """همان کار apply_vless ولی روی نود (از طریق SSH). برمی‌گرداند: رشته‌ی خطا یا ''"""
    name, nid = ib["name"], ib_node(ib)
    n = q("SELECT * FROM nodes WHERE id=?", (nid,), True)
    if not n:
        return f"{name}: نودِ این اینباند پیدا نشد"
    if not ib["enabled"]:
        vless_teardown_remote(ib)
        return ""
    try:
        cfg = xray_build(ib)
    except Exception as ex:
        return f"{name}: کانفیگ Xray ساخته نشد — {ex}"
    path, unit, xb = xray_path(ib), xray_unit(ib), n["xray_bin"] or XRAY_BIN
    new_path, add_path = path[:-5] + ".new.json", path[:-5] + ".add.json"      # پسوند .json لازم است تا Xray فرمت را بشناسد
    qp, qn, qa, qu, qx = (shlex.quote(v) for v in (path, new_path, add_path, unit, xb))
    text = json.dumps(cfg, indent=2, ensure_ascii=False)
    aport = cfg["inbounds"][0]["port"]
    new_users = cfg["inbounds"][1]["settings"]["clients"]

    def job(s):
        rc, o, _ = s.run(f"cat {qp} 2>/dev/null; echo '@@UP'; systemctl is-active --quiet {qu} && echo 1 || echo 0; "
                         f"echo '@@UNIT'; test -f {shlex.quote(XRAY_UNIT)} && echo 1 || echo 0")
        old_txt, _, tail = o.partition("@@UP")
        up_txt, _, unit_txt = tail.partition("@@UNIT")
        up, has_unit = up_txt.strip() == "1", unit_txt.strip() == "1"
        try:
            old = json.loads(old_txt) if old_txt.strip() else None
        except Exception:
            old = None
        s.put(new_path, text, 0o600)
        rc, o, e = s.run(f"{qx} run -test -c {qn}", timeout=40)
        if rc != 0:
            s.run(f"rm -f {qn}")
            return f"{name}: کانفیگ Xray روی نود معتبر نیست — {(e or o).strip()[-300:]}"
        s.run(f"mv -f {qn} {qp}")
        if not has_unit:
            s.put(XRAY_UNIT, xray_unit_text(xb), 0o644)
            s.run("systemctl daemon-reload")
        if ib["auto_rules"]:
            s.run(node_fw_script(ib, True))
        need = restart or not up or old is None or xray_shape(old) != xray_shape(cfg)
        if not need:
            old_ids = {u["id"] for i in old["inbounds"] if i.get("protocol") == "vless" for u in i["settings"]["clients"]}
            new_ids = {u["id"] for u in new_users}
            if old_ids - new_ids:
                need = True          # حذف کاربر → ری‌استارت تا اتصال‌های بازِ او قطع شود
            elif new_ids - old_ids:
                add = {"inbounds": [{"tag": cfg["inbounds"][1]["tag"], "protocol": "vless", "port": ib["port"],
                                     "listen": cfg["inbounds"][1]["listen"],
                                     "settings": {"clients": [u for u in new_users if u["id"] not in old_ids], "decryption": "none"}}]}
                s.put(add_path, json.dumps(add), 0o600)
                rc, _, _ = s.run(f"{qx} api adu -s=127.0.0.1:{aport} {qa}; r=$?; rm -f {qa}; exit $r", timeout=20)
                need = rc != 0
        if need:
            rc, o, e = s.run(f"systemctl enable {qu} >/dev/null 2>&1; systemctl restart {qu} || exit 1; sleep 1; "
                             f"systemctl is-active --quiet {qu} || exit 2", timeout=60)
            if rc == 1:
                return f"{name}: راه‌اندازی Xray روی نود ناموفق بود — {(e or o).strip()[-250:]} (journalctl -u {unit} -e)"
            if rc == 2:
                return f"{name}: Xray روی نود بعد از اجرا متوقف شد (پورت {ib['port']} اشغال است؟) — journalctl -u {unit} -e"
        return ""

    try:
        w = node_call(n, job)
    except Err as e:
        NODE_DIRTY.add(ib["id"])
        NODE_STATE[nid] = dict(NODE_STATE.get(nid) or {}, ok=False, ts=now(), err=str(e)[:200], up={})
        return f"{name}: {e} — بعد از وصل شدن نود دوباره اعمال می‌شود"
    NODE_DIRTY.discard(ib["id"])         # خطای کانفیگ/سرویس با تکرار درست نمی‌شود؛ فقط قطعی اتصال دوباره امتحان می‌شود
    if w:
        return w
    st = NODE_STATE.setdefault(nid, dict(ok=True, ts=now(), err="", up={}, ver=n["xray_ver"] or ""))
    st.setdefault("up", {})[name] = True
    return ""


def vless_teardown_remote(ib):
    nid = ib_node(ib)
    n = q("SELECT * FROM nodes WHERE id=?", (nid,), True)
    if not n:
        return
    path, unit = xray_path(ib), xray_unit(ib)
    script = (node_fw_script(ib, False) + f"; systemctl disable --now {shlex.quote(unit)} >/dev/null 2>&1; "
              f"rm -f {shlex.quote(path)} {shlex.quote(path[:-5] + '.new.json')} {shlex.quote(path[:-5] + '.add.json')}; true")
    try:
        node_call(n, lambda s: s.run(script, timeout=40))
    except Err as e:
        log.warning("teardown %s روی نود: %s", ib["name"], e)
    NODE_DIRTY.discard(ib["id"])
    ((NODE_STATE.get(nid) or {}).get("up") or {}).pop(ib["name"], None)


def node_probe(n):
    """یک اتصال SSH: نسخه‌ی Xray + وضعیت سرویس هر اینباند + آمار ترافیک؛ نتیجه در NODE_STATE"""
    nid, xb = n["id"], n["xray_bin"] or XRAY_BIN
    ibs = {r["name"]: r for r in q("SELECT * FROM inbounds WHERE node_id=? AND proto='vless' AND enabled=1", (nid,))}
    qx = shlex.quote(xb)
    parts = [f"echo '@@V'; {qx} version 2>/dev/null | head -1"]
    for ib in ibs.values():
        unit, path = shlex.quote(xray_unit(ib)), shlex.quote(xray_path(ib))
        parts.append(
            f"echo '@@I {ib['name']}'\n"
            f"if systemctl is-active --quiet {unit}; then echo 1; "
            f"P=$(grep -m1 -o '\"port\": *[0-9]*' {path} 2>/dev/null | grep -o '[0-9]*$'); "
            f"if [ -n \"$P\" ]; then {qx} api statsquery -s=127.0.0.1:$P -pattern 'user>>>' -reset=true 2>/dev/null || echo '{{}}'; "
            f"else echo '{{}}'; fi; else echo 0; fi")
    rc, out, err = node_call(n, lambda s: s.run("\n".join(parts), timeout=45))
    chunks = out.split("@@I ")
    m = re.search(r"@@V\s*\n([^\n]*)", chunks[0])
    ver_line = m.group(1).strip() if m else ""
    mv = re.match(r"Xray\s+(\S+)", ver_line)
    ver = mv.group(1) if mv else (n["xray_ver"] or "")
    up = {}
    for ch in chunks[1:]:
        nm, _, body_ = ch.partition("\n")
        nm = nm.strip()
        flag, _, js = body_.partition("\n")
        up[nm] = flag.strip() == "1"
        if up[nm] and nm in ibs and js.strip():
            _vless_ingest(ibs[nm], js)
    for nm in ibs:
        up.setdefault(nm, False)
    NODE_STATE[nid] = dict(ok=True, ts=now(), err="", up=up, ver=ver)
    if ver and ver != (n["xray_ver"] or ""):
        x("UPDATE nodes SET xray_ver=? WHERE id=?", (ver, nid))


def node_cycle(n):
    try:
        node_probe(n)
    except Exception as e:
        st = NODE_STATE.get(n["id"]) or {}
        NODE_STATE[n["id"]] = dict(st, ok=False, ts=now(), err=str(e)[:200], up={})
        node_drop(n["id"])
        return
    for r in q("SELECT id FROM inbounds WHERE node_id=?", (n["id"],)):
        if r["id"] in NODE_DIRTY:
            w = apply_inbound(r["id"])
            if w:
                log.warning(w)


def node_loop():
    time.sleep(3)
    for r in q("SELECT id FROM inbounds WHERE COALESCE(node_id,0)>0"):
        NODE_DIRTY.add(r["id"])          # بعد از ری‌استارت پنل، همه‌ی اینباندهای نودها یک‌بار با دیتابیس هماهنگ می‌شوند
    while True:
        try:
            ths = [threading.Thread(target=node_cycle, args=(n,), daemon=True) for n in q("SELECT * FROM nodes")]
            for t in ths:
                t.start()
            for t in ths:
                t.join(60)
        except Exception:
            log.exception("nodes")
        time.sleep(STATS_INTERVAL)


def ser_node(n):
    st = NODE_STATE.get(n["id"]) or {}
    ni = q("SELECT COUNT(*) c FROM inbounds WHERE node_id=?", (n["id"],), True)["c"]
    nc = q("""SELECT COUNT(DISTINCT ci.client_id) c FROM client_inbound ci JOIN inbounds i ON i.id=ci.inbound_id
              WHERE i.node_id=?""", (n["id"],), True)["c"]
    return dict(id=n["id"], name=n["name"], address=n["address"], ssh_port=n["ssh_port"], ssh_user=n["ssh_user"],
                note=n["note"], xray_ver=n["xray_ver"], created=n["created"], inbounds=ni, clients=nc,
                online=bool(st.get("ok")), checked=st.get("ts", 0), error=st.get("err", ""))


def node_unkey_script():
    b = shlex.quote(node_pub().split()[1])
    return (f"[ -f ~/.ssh/authorized_keys ] && {{ grep -vF {b} ~/.ssh/authorized_keys > ~/.ssh/authorized_keys.tmp; "
            f"cat ~/.ssh/authorized_keys.tmp > ~/.ssh/authorized_keys; rm -f ~/.ssh/authorized_keys.tmp; }}; true")


def node_parse(d, cur=None):
    nid = cur["id"] if cur else 0
    name = oneline(d.get("name"))[:40]
    if not name:
        raise Err("نام نود را وارد کنید")
    if q("SELECT 1 FROM nodes WHERE LOWER(name)=LOWER(?) AND id!=?", (name, nid), True):
        raise Err("این نام برای نود دیگری استفاده شده")
    addr = str(d.get("address") or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9.\-:]{3,253}", addr):
        raise Err("آی‌پی یا دامنه‌ی نود نامعتبر است")
    port = num(d.get("ssh_port"), 22, 1, 65535, "پورت SSH")
    if q("SELECT 1 FROM nodes WHERE address=? AND ssh_port=? AND id!=?", (addr, port, nid), True):
        raise Err("این سرور قبلاً به‌عنوان نود اضافه شده")
    return dict(name=name, address=addr, ssh_port=port, note=oneline(d.get("note"))[:100])


def node_job(j, d):
    """افزودن نود؛ در یک ترد جدا اجرا می‌شود و مراحل را در j['steps'] می‌نویسد."""
    steps = j["steps"]
    rs, key_added = None, False

    def step(t):
        s = {"t": t, "s": "run", "m": ""}
        steps.append(s)
        return s

    def ok(s, m=""):
        s["s"] = "ok"; s["m"] = m

    try:
        s = step("اتصال SSH با رمز")
        rs = _Remote(d["address"], d["ssh_port"], d["ssh_user"], d["ssh_pass"])
        rc, o, e = rs.run("id -u; uname -m; test -d /run/systemd/system && echo systemd || echo nosystemd; "
                          "cat /proc/sys/kernel/random/boot_id 2>/dev/null || echo none")
        f = o.split()
        if len(f) < 3 or f[0] != "0":
            raise Err("کاربر SSH باید root باشد")
        lb = (_read("/proc/sys/kernel/random/boot_id") or "").strip()
        if lb and len(f) > 3 and f[3] == lb:
            raise Err("این همان سروری است که پنل روی آن نصب است؛ خود پنل «نود اصلی» حساب می‌شود و لازم نیست اضافه شود")
        if f[2] != "systemd":
            raise Err("این سرور systemd ندارد؛ نود فقط روی لینوکس با systemd کار می‌کند")
        arch = f[1]
        ok(s, f"متصل شد ({arch})")

        s = step("نصب کلید پنل روی نود (رمز ذخیره نمی‌شود)")
        pub = node_pub()
        rc, o, e = rs.run("mkdir -p ~/.ssh && chmod 700 ~/.ssh && touch ~/.ssh/authorized_keys && chmod 600 ~/.ssh/authorized_keys && "
                          "{ [ ! -s ~/.ssh/authorized_keys ] || [ -z \"$(tail -c1 ~/.ssh/authorized_keys)\" ] || echo >> ~/.ssh/authorized_keys; } && "
                          f"{{ grep -qF {shlex.quote(pub.split()[1])} ~/.ssh/authorized_keys || echo {shlex.quote(pub)} >> ~/.ssh/authorized_keys; }}")
        if rc != 0:
            raise Err("نوشتن authorized_keys روی نود ناموفق بود: " + (o + e).strip()[:200])
        key_added = True
        rs.close(); rs = None
        try:
            rs = _Remote(d["address"], d["ssh_port"], d["ssh_user"], None, key=node_key())
        except Err:
            raise Err("ورود با کلید ممکن نشد؛ احتمالاً PubkeyAuthentication روی SSH نود غیرفعال است")
        ok(s, "ورود با کلید تأیید شد")

        s = step("بررسی و نصب Xray-core روی نود")
        rc, o, e = rs.run(XRAY_NODE_INSTALL, timeout=300)
        xb = "/usr/local/bin/xray"
        if rc == 4:               # نود به GitHub دسترسی ندارد → از روی پنل کپی می‌کنیم (اگر معماری یکی باشد)
            msg = ensure_xray()
            lb = xray_bin()
            if msg or not lb:
                raise Err("دانلود Xray روی نود ناموفق بود و روی پنل هم نشد: " + (msg or ""))
            norm = lambda a: {"x86_64": "x64", "amd64": "x64", "aarch64": "arm64", "arm64": "arm64"}.get(a.strip().lower(), a.strip().lower())
            if norm(platform.machine()) != norm(arch):
                raise Err(f"نود به GitHub دسترسی ندارد و معماری پنل ({platform.machine()}) با نود ({arch}) فرق دارد")
            with open(lb, "rb") as fh:
                rs.put(xb, fh.read(), 0o755)
            ok(s, "از روی پنل کپی شد (نود به GitHub دسترسی نداشت)")
        elif rc != 0:
            raise Err("نصب Xray ناموفق بود: " + (o + e).strip()[-250:])
        else:
            mb = re.search(r"^BIN=(\S+)$", o, re.M)
            xb = mb.group(1) if mb else xb
            vl = [ln for ln in o.splitlines() if ln and not ln.startswith("BIN=")]
            ok(s, vl[-1] if vl else "نصب شد")
        rc, o, e = rs.run(f"{shlex.quote(xb)} version | head -1")
        mv = re.match(r"Xray\s+(\S+)", o.strip())
        if rc != 0 or not mv:
            raise Err("Xray روی نود اجرا نمی‌شود: " + (o + e).strip()[:200])
        ver = mv.group(1)

        s = step("ساخت سرویس systemd و پوشه‌ی کانفیگ")
        rs.run(f"mkdir -p {shlex.quote(XRAY_DIR)}")
        rs.put(XRAY_UNIT, xray_unit_text(xb), 0o644)
        rc, o, e = rs.run("systemctl daemon-reload")
        if rc != 0:
            raise Err("systemctl daemon-reload ناموفق بود: " + (o + e).strip()[:200])
        ok(s)

        s = step("ثبت نود در پنل")
        nid = x("INSERT INTO nodes(name,address,ssh_port,ssh_user,xray_bin,xray_ver,note,created) VALUES(?,?,?,?,?,?,?,?)",
                (d["name"], d["address"], d["ssh_port"], d["ssh_user"], xb, ver, d["note"], now()))
        NODE_STATE[nid] = dict(ok=True, ts=now(), err="", up={}, ver=ver)
        ok(s, "نود آماده است؛ حالا می‌توانید روی آن اینباند VLESS بسازید")
        key_added = False
        j["state"] = "done"
    except Exception as e:
        log.warning("node_job: %s", e)
        for s_ in steps:
            if s_["s"] == "run":
                s_["s"] = "err"; s_["m"] = str(e)
        if not steps or steps[-1]["s"] != "err":
            steps.append({"t": "خطا", "s": "err", "m": str(e)})
        if key_added and rs:
            try:
                rs.run(node_unkey_script())
            except Exception:
                pass
        j["state"] = "failed"
    finally:
        if rs:
            rs.close()


@app.post("/api/nodes")
@auth
def node_create():
    d = body()
    v = node_parse(d)
    user = str(d.get("ssh_user") or "root").strip()
    if not re.fullmatch(r"[A-Za-z0-9_.\-]{1,32}", user):
        raise Err("نام کاربری SSH نامعتبر است")
    pw = str(d.get("ssh_pass") or "")
    if not pw:
        raise Err("رمز SSH نود را وارد کنید")
    for j in NODE_JOBS.values():
        if j["state"] == "run":
            raise Err("یک نود دیگر در حال اضافه شدن است؛ صبر کنید")
    jid = secrets.token_hex(6)
    j = {"state": "run", "steps": [], "name": v["name"]}
    NODE_JOBS[jid] = j
    while len(NODE_JOBS) > 20:
        NODE_JOBS.popitem(last=False)
    threading.Thread(target=node_job, args=(j, dict(v, ssh_user=user, ssh_pass=pw)), daemon=True).start()
    return jsonify(ok=True, job=jid)


@app.get("/api/nodes/job/<jid>")
@auth
def node_job_state(jid):
    j = NODE_JOBS.get(jid)
    if not j:
        raise Err("کار پیدا نشد")
    return jsonify(state=j["state"], steps=j["steps"], name=j["name"])


@app.put("/api/nodes/<int:nid>")
@auth
def node_update(nid):
    cur = q("SELECT * FROM nodes WHERE id=?", (nid,), True) or abort(404)
    v = node_parse(body(), cur)
    x("UPDATE nodes SET name=?, address=?, ssh_port=?, note=? WHERE id=?", (v["name"], v["address"], v["ssh_port"], v["note"], nid))
    if (v["address"], v["ssh_port"]) != (cur["address"], cur["ssh_port"]):
        node_drop(nid)
    return jsonify(ok=True)


@app.post("/api/nodes/<int:nid>/check")
@auth
def node_check(nid):
    n = q("SELECT * FROM nodes WHERE id=?", (nid,), True) or abort(404)
    try:
        node_probe(n)
    except Err as e:
        NODE_STATE[nid] = dict(NODE_STATE.get(nid) or {}, ok=False, ts=now(), err=str(e)[:200], up={})
        raise
    return jsonify(ok=True, node=ser_node(q("SELECT * FROM nodes WHERE id=?", (nid,), True)))


@app.delete("/api/nodes/<int:nid>")
@auth
def node_delete(nid):
    n = q("SELECT * FROM nodes WHERE id=?", (nid,), True) or abort(404)
    tuns = [r["name"] for r in q("SELECT * FROM tunnels") if nid in tun_ends(r)]
    if tuns:
        raise Err(f"این نود در تانل {', '.join(tuns)} استفاده شده؛ اول آن را از بخش «تانل» حذف کنید")
    ibs = q("SELECT * FROM inbounds WHERE node_id=?", (nid,))
    if ibs and request.args.get("force") != "1":
        raise Err(f"این نود {len(ibs)} اینباند دارد؛ با حذف نود، اینباندها و اتصال کلاینت‌ها به آن‌ها هم حذف می‌شود")
    for ib in ibs:
        vless_teardown_remote(ib)
        x("DELETE FROM inbounds WHERE id=?", (ib["id"],))
    warn = ""
    try:
        node_call(n, lambda s: s.run(f"rm -f {shlex.quote(XRAY_UNIT)}; rm -rf {shlex.quote(XRAY_DIR)}; systemctl daemon-reload; "
                                     + node_unkey_script(), timeout=40))
    except Err as e:
        warn = f"نود از پنل حذف شد ولی پاک‌سازی روی خود سرور انجام نشد ({e}). کلید «sepipanel» را از ~/.ssh/authorized_keys آن سرور دستی پاک کنید."
    node_drop(nid)
    NODE_STATE.pop(nid, None)
    x("DELETE FROM nodes WHERE id=?", (nid,))
    return jsonify(ok=True, warn=warn)


# ------------------------------ وضعیت سیستم (فقط مدیر اصلی) ------------------------------
PROC_START = time.time()
HIST = collections.deque(maxlen=180)      # ۱۸۰ نمونه × ۵ ثانیه = ۱۵ دقیقه اخیر
_PREV = {"cpu": None, "net": None}


def _rd(path):
    try:
        with open(path) as f:
            return f.read()
    except Exception:
        return ""


def _cpu_times():
    f = _rd("/proc/stat").split("\n", 1)[0].split()
    if len(f) < 5:
        return None
    v = [int(a) for a in f[1:9]]
    return sum(v), v[3] + (v[4] if len(v) > 4 else 0)


def _meminfo():
    d = {}
    for ln in _rd("/proc/meminfo").splitlines():
        k, _, v = ln.partition(":")
        try:
            d[k] = int(v.split()[0]) * 1024
        except Exception:
            pass
    return d


def _net_counters(excl):
    """(rx, tx) کارت‌های واقعی سرور و (rx, tx) اینترفیس‌های وایرگارد پنل"""
    rx = tx = wrx = wtx = 0
    for ln in _rd("/proc/net/dev").splitlines()[2:]:
        name, _, rest = ln.partition(":")
        f = rest.split()
        if len(f) < 9:
            continue
        name = name.strip()
        r, t = int(f[0]), int(f[8])
        if name in excl or name.startswith("ppp"):
            wrx += r; wtx += t
        elif name != "lo":
            rx += r; tx += t
    return rx, tx, wrx, wtx


def _sockets():
    c = lambda ps: sum(max(0, len(_rd(p).splitlines()) - 1) for p in ps)
    return c(("/proc/net/tcp", "/proc/net/tcp6")), c(("/proc/net/udp", "/proc/net/udp6"))


def sample():
    t = time.time()
    cur, prev, cpu = _cpu_times(), _PREV["cpu"], 0.0
    if cur and prev and cur[0] > prev[0]:
        cpu = round(max(0.0, 100 * (1 - (cur[1] - prev[1]) / (cur[0] - prev[0]))), 1)
    _PREV["cpu"] = cur
    excl = {r["name"] for r in q("SELECT name FROM inbounds")}
    n, pn, rate = _net_counters(excl), _PREV["net"], (0, 0, 0, 0)
    if pn and t > pn[0]:
        rate = [max(0, a - b) / (t - pn[0]) for a, b in zip(n, pn[1])]
    _PREV["net"] = (t, n)
    mi = _meminfo()
    tot = mi.get("MemTotal", 0)
    ram = round(100 * (tot - mi.get("MemAvailable", mi.get("MemFree", 0))) / tot, 1) if tot else 0
    tcp, udp = _sockets()
    HIST.append(dict(t=int(t), cpu=cpu, ram=ram, rx=rate[0], tx=rate[1], wrx=rate[2], wtx=rate[3], tcp=tcp, udp=udp))


def sys_loop():
    while True:
        try:
            sample()
        except Exception:
            log.exception("sysstat")
        time.sleep(5)


def _ips(excl):
    rc, o, _ = run(["ip", "-o", "addr", "show", "scope", "global"], timeout=5)
    out = []
    for ln in (o or "").splitlines():
        f = ln.split()
        if len(f) >= 4 and f[2] in ("inet", "inet6") and f[1] not in excl:
            out.append(dict(i=f[1], ip=f[3].split("/")[0]))
    return out


@app.get("/api/sys")
@auth
def sys_api():
    if not HIST:
        sample()
    ibs = q("SELECT name FROM inbounds")
    excl = {r["name"] for r in ibs}
    ups = up_ifaces()
    mi, ci = _meminfo(), _rd("/proc/cpuinfo")
    mm = re.search(r"model name\s*:\s*(.+)", ci)
    mhz = [float(v) for v in re.findall(r"cpu MHz\s*:\s*([\d.]+)", ci)]
    try:
        du = shutil.disk_usage("/")
    except Exception:
        du = (0, 0, 0)
    st = _rd("/proc/self/status")
    rss, thr = re.search(r"VmRSS:\s*(\d+)", st), re.search(r"Threads:\s*(\d+)", st)
    try:
        la = list(os.getloadavg())
    except Exception:
        la = [0, 0, 0]
    up = _rd("/proc/uptime").split()
    rx, tx, wrx, wtx = _net_counters(excl)
    cs = q("SELECT COUNT(*) n, COALESCE(SUM(up_bytes+down_bytes),0) u FROM clients", (), True)
    on = q("SELECT COUNT(DISTINCT client_id) n FROM client_inbound WHERE last_hs>?", (now() - 180,), True)["n"]
    return jsonify(
        host=socket.gethostname(), kernel=platform.release(), cores=os.cpu_count() or 1,
        model=mm.group(1).strip() if mm else "", mhz=round(sum(mhz) / len(mhz)) if mhz else 0,
        mem=dict(total=mi.get("MemTotal", 0), avail=mi.get("MemAvailable", mi.get("MemFree", 0)),
                 swap_total=mi.get("SwapTotal", 0), swap_free=mi.get("SwapFree", 0)),
        disk=dict(total=du[0], used=du[1], free=du[2]), load=la, uptime=float(up[0]) if up else 0,
        panel_up=time.time() - PROC_START,
        panel=dict(rss=int(rss.group(1)) * 1024 if rss else 0, threads=int(thr.group(1)) if thr else 0),
        net=dict(rx=rx, tx=tx, wrx=wrx, wtx=wtx), ips=_ips(excl),
        wg=dict(up=len([r for r in ibs if r["name"] in ups]), total=len(ibs), clients=cs["n"], online=on, usage=cs["u"]),
        hist=list(HIST))


def up_ifaces():
    ups = set()
    for t in ("wg", "awg"):
        rc, o, _ = run([t, "show", "interfaces"], timeout=10)
        if rc == 0:
            ups |= set(o.split())
    l = q("SELECT name FROM inbounds WHERE proto='l2tp' AND enabled=1")
    if l and l2tp_up():
        ups |= {r["name"] for r in l}
    for r in q("SELECT * FROM inbounds WHERE proto='ovpn' AND enabled=1"):
        if ovpn_up(r):
            ups.add(r["name"])
    for r in q("SELECT * FROM inbounds WHERE proto='vless' AND enabled=1"):
        if xray_up(r):
            ups.add(r["name"])
    return ups


def state_super():
    ups = up_ifaces()
    rc2, ver, _ = run(["wg", "--version"], timeout=5)
    rc3, aver, _ = run(["awg", "--version"], timeout=5)
    return jsonify(
        inbounds=[ser_inbound(r, ups) for r in q("SELECT * FROM inbounds ORDER BY id")],
        clients=[ser_client(c) for c in q("SELECT * FROM clients ORDER BY id DESC")],
        settings=dict(public_url=setting("public_url"), sub_title=setting("sub_title", "WireGuard"), sub_telegram=setting("sub_telegram", ""),
                      update_interval=int(setting("update_interval", "12") or 12)),
        role="super", admins=[ser_admin(a) for a in q("SELECT * FROM admins ORDER BY id DESC")],
        nodes=[ser_node(n) for n in q("SELECT * FROM nodes ORDER BY id")],
        defaults=inbound_defaults(), panel=panel_info(),
        server=dict(wg=(ver.strip() if rc2 == 0 else ""), awg=(aver.strip() if rc3 == 0 else ""), nat_iface=detect_iface(), qr=bool(qrcode),
                    now=now(), base=base_url()))


def ser_admin(a):
    d = {k: a[k] for k in ("id", "username", "name", "note", "enabled", "limit_bytes", "used_bytes", "expiry",
                           "created", "last_login")}
    d["state"] = admin_state(a)
    cs = q("SELECT COUNT(*) n, COALESCE(SUM(up_bytes+down_bytes),0) u, "
           "COALESCE(SUM(CASE WHEN last_seen>? THEN 1 ELSE 0 END),0) o FROM clients WHERE owner_id=?",
           (now() - 180, a["id"]), True)
    d["clients"], d["clients_used"], d["online"] = cs["n"], cs["u"], cs["o"]
    return d


def state_admin():
    a = q("SELECT * FROM admins WHERE id=?", (g.aid,), True)
    ups = up_ifaces()
    ibs = [dict(id=r["id"], name=r["name"], remark=r["remark"], address4=r["address4"], awg=is_awg(r), enabled=1,
                up=r["name"] in ups, exclude_sub=r["exclude_sub"], proto=r["proto"] or "wg", psk=r["psk"] if is_l2tp(r) else "",
                endpoint=r["endpoint"])
           for r in q("SELECT * FROM inbounds WHERE enabled=1 ORDER BY id")]
    return jsonify(role="admin", inbounds=ibs, me=ser_admin(a), settings={}, admins=[],
                   clients=[ser_client(c) for c in q("SELECT * FROM clients WHERE owner_id=? ORDER BY id DESC", (g.aid,))],
                   panel=dict(user=a["username"]), server=dict(qr=bool(qrcode), now=now(), base=base_url()))


@app.get("/api/state")
@auth_any
def state():
    if getattr(g, "via_key", False):
        return jsonify(error="با کلید API از /api/v1 استفاده کنید"), 403
    return state_super() if g.role == "super" else state_admin()


def owned(cid):
    """کلاینت را برمی‌گرداند؛ ادمین فقط به کلاینت‌های خودش دسترسی دارد."""
    c = q("SELECT * FROM clients WHERE id=?", (cid,), True) or abort(404)
    if g.role == "admin" and c["owner_id"] != g.aid:
        abort(404)
    return c


def require_active_admin():
    if g.role != "admin":
        return
    st = admin_state(q("SELECT * FROM admins WHERE id=?", (g.aid,), True))
    if st != "active":
        raise Err({"expired": "اعتبار حساب شما تمام شده", "limit": "حجم حساب شما تمام شده",
                   "disabled": "حساب شما غیرفعال است"}[st] + "؛ برای تمدید با مدیر تماس بگیرید")


def admin_links(cid, links):
    """لینک‌های کلاینت یک ادمین: فقط اینباندهای فعال؛ تنظیمات ویژه (IP/DNS/AllowedIPs...) را نمی‌تواند تغییر دهد."""
    def keep(cur):
        return dict(inbound_id=cur["inbound_id"], ip4=cur["ip4"], allowed_ips=cur["allowed_ips"], keepalive=cur["keepalive"],
                    dns=cur["dns"], mtu=cur["mtu"] or "", extra_allowed=cur["extra_allowed"])
    out, ids = [], set()
    for L in links or []:
        iid = num(L.get("inbound_id"))
        if iid in ids:
            continue
        if not q("SELECT 1 FROM inbounds WHERE id=? AND enabled=1", (iid,), True):
            raise Err("اینباند انتخاب‌شده فعال نیست یا وجود ندارد")
        ids.add(iid)
        cur = q("SELECT * FROM client_inbound WHERE client_id=? AND inbound_id=?", (cid, iid), True) if cid else None
        out.append(keep(cur) if cur else dict(inbound_id=iid))
    if cid:   # لینک به اینباندی که الان غیرفعال شده و ادمین نمی‌بیند، دست‌نخورده بماند
        for r in q("""SELECT ci.*, ib.enabled AS ib_en FROM client_inbound ci JOIN inbounds ib ON ib.id=ci.inbound_id
                      WHERE ci.client_id=?""", (cid,)):
            if r["inbound_id"] not in ids and not r["ib_en"]:
                out.append(keep(r))
    if not out:
        raise Err("حداقل یک اینباند انتخاب کنید")
    return out


# ------------------------------ مدیریت ادمین‌ها (فقط مدیر اصلی) ------------------------------
def parse_admin(d, cur=None):
    user = str(d.get("username") or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9_.\-]{3,32}", user):
        raise Err("نام کاربری ادمین باید ۳ تا ۳۲ حرف انگلیسی/عدد/_ . - باشد")
    if user.lower() == admin_user().lower():
        raise Err("این نام کاربری برای مدیر اصلی است")
    if q("SELECT 1 FROM admins WHERE lower(username)=lower(?) AND id!=?", (user, cur["id"] if cur else 0), True):
        raise Err("این نام کاربری قبلاً استفاده شده")
    pw = str(d.get("password") or "")
    if (not cur or pw) and len(pw) < 8:
        raise Err("رمز عبور باید حداقل ۸ کاراکتر باشد")
    try:
        gb = float(d.get("limit_gb") or 0)
    except Exception:
        raise Err("حجم نامعتبر است")
    if gb < 0:
        raise Err("حجم نمی‌تواند منفی باشد")
    return dict(username=user, password=pw, name=oneline(d.get("name"))[:64], note=str(d.get("note") or "")[:500],
                limit_bytes=int(gb * 1024 ** 3), expiry=num(d.get("expiry"), 0, 0, None, "تاریخ انقضا"))


@app.post("/api/admins")
@auth
def admin_create():
    o = parse_admin(body())
    aid = x("""INSERT INTO admins(username,pass_hash,name,note,enabled,limit_bytes,used_bytes,expiry,ver,created)
               VALUES(?,?,?,?,1,?,0,?,?,?)""",
            (o["username"], hash_pw(o["password"]), o["name"], o["note"], o["limit_bytes"], o["expiry"],
             secrets.token_hex(8), now()))
    return jsonify(ok=True, id=aid)


@app.put("/api/admins/<int:aid>")
@auth
def admin_update(aid):
    cur = q("SELECT * FROM admins WHERE id=?", (aid,), True) or abort(404)
    o = parse_admin(body(), cur)
    x("UPDATE admins SET username=?, name=?, note=?, limit_bytes=?, expiry=? WHERE id=?",
      (o["username"], o["name"], o["note"], o["limit_bytes"], o["expiry"], aid))
    if o["password"]:
        x("UPDATE admins SET pass_hash=?, ver=? WHERE id=?", (hash_pw(o["password"]), secrets.token_hex(8), aid))
    return jsonify(ok=True, warn=apply_many(admin_inbounds(aid)))


@app.delete("/api/admins/<int:aid>")
@auth
def admin_delete(aid):
    q("SELECT 1 FROM admins WHERE id=?", (aid,), True) or abort(404)
    ids = admin_inbounds(aid)
    if body().get("delete_clients"):
        x("DELETE FROM clients WHERE owner_id=?", (aid,))
    else:
        x("UPDATE clients SET owner_id=0 WHERE owner_id=?", (aid,))
    x("DELETE FROM api_keys WHERE admin_id=?", (aid,))
    x("DELETE FROM admins WHERE id=?", (aid,))
    ADM_STATE.pop(aid, None)
    return jsonify(ok=True, warn=apply_many(ids))


@app.post("/api/admins/<int:aid>/toggle")
@auth
def admin_toggle(aid):
    a = q("SELECT * FROM admins WHERE id=?", (aid,), True) or abort(404)
    x("UPDATE admins SET enabled=? WHERE id=?", (0 if a["enabled"] else 1, aid))
    return jsonify(ok=True, warn=apply_many(admin_inbounds(aid)))


@app.post("/api/admins/<int:aid>/reset-traffic")
@auth
def admin_reset_traffic(aid):
    q("SELECT 1 FROM admins WHERE id=?", (aid,), True) or abort(404)
    x("UPDATE admins SET used_bytes=0 WHERE id=?", (aid,))
    return jsonify(ok=True, warn=apply_many(admin_inbounds(aid)))


@app.post("/api/admins/<int:aid>/renew")
@auth
def admin_renew(aid):
    a = q("SELECT * FROM admins WHERE id=?", (aid,), True) or abort(404)
    d = body()
    try:
        gb = float(d.get("add_gb") or 0)
    except Exception:
        raise Err("حجم نامعتبر است")
    days = num(d.get("add_days"), 0, 0, 36500, "تعداد روز")
    if gb < 0:
        raise Err("حجم نمی‌تواند منفی باشد")
    lim, used, exp = a["limit_bytes"], a["used_bytes"], a["expiry"]
    if d.get("reset_usage"):
        used = 0
    if gb:
        lim = (lim or 0) + int(gb * 1024 ** 3)
    if d.get("reset_time"):
        if not days:
            raise Err("برای ریست زمان، تعداد روز را وارد کنید (از همین الان شمرده می‌شود)")
        exp = now() + days * 86400
    elif days:
        exp = (max(exp, now()) if exp else now()) + days * 86400
    x("UPDATE admins SET limit_bytes=?, used_bytes=?, expiry=? WHERE id=?", (lim, used, exp, aid))
    return jsonify(ok=True, warn=apply_many(admin_inbounds(aid)))


@app.post("/api/inbounds")
@auth
def inbound_create():
    o = parse_inbound(body())
    iid = x(f"INSERT INTO inbounds({','.join(IB_COLS)},enabled,created) VALUES({','.join('?' * len(IB_COLS))},1,?)",
            [o[c] for c in IB_COLS] + [now()])
    return jsonify(ok=True, id=iid, warn=apply_inbound(iid))


@app.put("/api/inbounds/<int:iid>")
@auth
def inbound_update(iid):
    cur = q("SELECT * FROM inbounds WHERE id=?", (iid,), True) or abort(404)
    o = parse_inbound(body(), cur)
    if cur["enabled"]:
        teardown(cur)   # با کانفیگ قدیمی پایین بیاید تا قوانین iptables قدیمی پاک شوند
    x(f"UPDATE inbounds SET {','.join(c + '=?' for c in IB_COLS)} WHERE id=?", [o[c] for c in IB_COLS] + [iid])
    if is_ovpn(cur) and body().get("regen_keys"):      # CA جدید → همه‌ی گواهی‌های کلاینت‌ها دوباره ساخته شود
        x("UPDATE client_inbound SET ovpn_cn='', ovpn_crt='', ovpn_key='' WHERE inbound_id=?", (iid,))
    sync_inbound_clients(iid)
    return jsonify(ok=True, warn=apply_inbound(iid, restart=True))


@app.delete("/api/inbounds/<int:iid>")
@auth
def inbound_delete(iid):
    cur = q("SELECT * FROM inbounds WHERE id=?", (iid,), True) or abort(404)
    teardown(cur)
    x("DELETE FROM inbounds WHERE id=?", (iid,))
    return jsonify(ok=True)


@app.post("/api/inbounds/<int:iid>/toggle")
@auth
def inbound_toggle(iid):
    cur = q("SELECT * FROM inbounds WHERE id=?", (iid,), True) or abort(404)
    x("UPDATE inbounds SET enabled=? WHERE id=?", (0 if cur["enabled"] else 1, iid))
    return jsonify(ok=True, warn=apply_inbound(iid, restart=True))


@app.post("/api/inbounds/<int:iid>/restart")
@auth
def inbound_restart(iid):
    q("SELECT 1 FROM inbounds WHERE id=?", (iid,), True) or abort(404)
    return jsonify(ok=True, warn=apply_inbound(iid, restart=True))


@app.get("/api/inbounds/<int:iid>/conf")
@auth
def inbound_conf(iid):
    ib = q("SELECT * FROM inbounds WHERE id=?", (iid,), True) or abort(404)
    return jsonify(conf=l2tp_summary(ib) if is_l2tp(ib) else ovpn_server_conf(ib, mask=True) if is_ovpn(ib) else xray_summary(ib) if is_vless(ib) else server_conf(ib, mask=True))


def create_clients(d):
    """ساخت یک یا چند کلاینت (مشترک بین پنل و API). برمی‌گرداند: (لیست id، پیام هشدار، آیا از قبل ساخته شده بود)"""
    b = parse_client_basic(d)
    count = num(d.get("count"), 1, 1, 200, "تعداد")
    ext = str(d.get("external_id") or "").strip()[:100]
    if ext and count != 1:
        raise Err("external_id فقط با count=1 کاربرد دارد")
    owner = g.aid if g.role == "admin" else 0
    kid = getattr(g, "key_id", 0)
    if kid:
        kr = q("SELECT * FROM api_keys WHERE id=?", (kid,), True)
        if kr and key_quota_state(kr) != "active":
            raise Err("حجم یا زمان این کلید API تمام شده؛ از پنل تمدیدش کنید")
    if ext:                                   # ایدمپوتنت: همان سفارش دوباره بیاید، کلاینت تکراری ساخته نمی‌شود
        old = q("SELECT id FROM clients WHERE ext_id=? AND owner_id=?", (ext, owner), True)
        if old:
            return [old["id"]], "", True
    links = d.get("links")
    if g.role == "admin":
        require_active_admin()
        links = admin_links(0, links)
    cids, touched = [], set()
    for i in range(count):
        priv = gen_private()
        name = b["name"] if count == 1 else f"{b['name']}-{i + 1}"
        try:
            cid = x("""INSERT INTO clients(name,token,enabled,private_key,public_key,limit_bytes,expiry,note,created,reset_period,last_reset,owner_id,ext_id,key_id)
                       VALUES(?,?,1,?,?,?,?,?,?,?,?,?,?,?)""",
                    (name, secrets.token_urlsafe(16), priv, pub_from_private(priv), b["limit_bytes"], b["expiry"], b["note"],
                     now(), b["reset_period"], now(), owner, ext, kid))
        except sqlite3.IntegrityError:        # دو درخواست هم‌زمان با یک external_id
            old = q("SELECT id FROM clients WHERE ext_id=? AND owner_id=?", (ext, owner), True) if ext else None
            if old:
                return [old["id"]], "", True
            raise
        try:
            touched |= save_links(cid, links)
        except Err:
            x("DELETE FROM clients WHERE id=?", (cid,))
            raise
        cids.append(cid)
    return cids, apply_many(touched), False


@app.post("/api/clients")
@auth_any
def client_create():
    cids, warn, _ = create_clients(body())
    out = dict(ok=True, warn=warn)
    if getattr(g, "via_key", False):
        out["clients"] = [ser_client(q("SELECT * FROM clients WHERE id=?", (c,), True)) for c in cids]
    return jsonify(out)


@app.put("/api/clients/<int:cid>")
@auth_any
def client_update(cid):
    cur = owned(cid)
    d = body()
    b = parse_client_basic(d)
    links = d.get("links")
    if g.role == "admin":
        require_active_admin()
        links = admin_links(cid, links)
    x("""UPDATE clients SET name=?, note=?, limit_bytes=?, expiry=?, reset_period=?,
         last_reset=CASE WHEN reset_period!=? THEN ? ELSE last_reset END WHERE id=?""",
      (b["name"], b["note"], b["limit_bytes"], b["expiry"], b["reset_period"], b["reset_period"], now(), cid))
    touched = save_links(cid, links)
    c = q("SELECT * FROM clients WHERE id=?", (cid,), True)
    if not c["enabled"] and c["reason"] in ("expired", "limit") and usage_state(c) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(touched))


def client_inbounds(cid):
    return {r["inbound_id"] for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (cid,))}


@app.delete("/api/v1/clients/<int:cid>")
@app.delete("/api/clients/<int:cid>")
@auth_any
def client_delete(cid):
    owned(cid)
    ids = client_inbounds(cid)
    x("DELETE FROM clients WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(ids))


@app.post("/api/clients/<int:cid>/toggle")
@auth_any
def client_toggle(cid):
    c = owned(cid)
    if c["enabled"]:
        x("UPDATE clients SET enabled=0, reason='disabled' WHERE id=?", (cid,))
    else:
        require_active_admin()
        if usage_state(c) != "active":
            raise Err("حجم یا اعتبار کلاینت تمام شده؛ اول تمدید یا ریست ترافیک کنید")
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


@app.post("/api/v1/clients/<int:cid>/reset-traffic")
@app.post("/api/clients/<int:cid>/reset-traffic")
@auth_any
def client_reset(cid):
    c = owned(cid)
    x("UPDATE clients SET up_bytes=0, down_bytes=0 WHERE id=?", (cid,))
    if not c["enabled"] and c["reason"] == "limit" and usage_state(q("SELECT * FROM clients WHERE id=?", (cid,), True)) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


@app.post("/api/v1/clients/<int:cid>/reset-token")
@app.post("/api/clients/<int:cid>/reset-token")
@auth_any
def client_reset_token(cid):
    owned(cid)
    x("UPDATE clients SET token=? WHERE id=?", (secrets.token_urlsafe(16), cid))
    return jsonify(ok=True)


@app.post("/api/clients/<int:cid>/regen-keys")
@auth_any
def client_regen(cid):
    owned(cid)
    priv = gen_private()
    x("UPDATE clients SET private_key=?, public_key=? WHERE id=?", (priv, pub_from_private(priv), cid))
    x("UPDATE client_inbound SET last_rx=0, last_tx=0 WHERE client_id=?", (cid,))
    for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (cid,)):
        ib = q("SELECT use_psk FROM inbounds WHERE id=?", (r["inbound_id"],), True)
        if ib["use_psk"]:
            x("UPDATE client_inbound SET psk=? WHERE client_id=? AND inbound_id=?", (gen_psk(), cid, r["inbound_id"]))
    x("""UPDATE client_inbound SET l2tp_pass=? WHERE client_id=? AND l2tp_user!=''""", (rand_secret(12), cid))
    x("UPDATE client_inbound SET vuuid='' WHERE client_id=? AND vuuid!=''", (cid,))
    for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=? AND ovpn_cn=''", (cid,)):
        if is_vless(q("SELECT proto FROM inbounds WHERE id=?", (r["inbound_id"],), True)):
            sync_inbound_clients(r["inbound_id"])
    ov_ids = [r["inbound_id"] for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=? AND ovpn_cn!=''", (cid,))]
    if ov_ids:      # گواهی جدید با CN جدید؛ گواهی قبلی دیگر در ccd نیست و رد می‌شود
        x("UPDATE client_inbound SET ovpn_cn='', ovpn_crt='', ovpn_key='' WHERE client_id=? AND ovpn_cn!=''", (cid,))
        for i_ in ov_ids:
            sync_inbound_clients(i_)
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


# ------------------------------ API عمومی (/api/v1) و کلیدهای API ------------------------------
# ربات تلگرام یا سایت با «کلید API» (هدر Authorization: Bearer ...) فقط کار با کلاینت‌ها را می‌تواند انجام دهد:
# ساخت، تمدید، فعال/غیرفعال، ریست ترافیک، حذف و خواندن لینک اشتراک. کلید هیچ‌وقت به تنظیمات، نودها، تانل و ادمین‌ها دسترسی ندارد.
def _v1_client(cid):
    return ser_client(q("SELECT * FROM clients WHERE id=?", (cid,), True))


@app.get("/api/v1/me")
@auth_any
def v1_me():
    out = dict(role=g.role)
    kr = q("SELECT * FROM api_keys WHERE id=?", (getattr(g, "key_id", 0),), True)
    if kr:
        out["key"] = ser_key(kr)
    if g.role == "admin":
        out["account"] = ser_admin(q("SELECT * FROM admins WHERE id=?", (g.aid,), True))
    return jsonify(out)


@app.get("/api/v1/inbounds")
@auth_any
def v1_inbounds():
    ups = up_ifaces()
    return jsonify(inbounds=[dict(id=r["id"], name=r["name"], remark=r["remark"], proto=r["proto"] or "wg", port=r["port"],
                                  node_id=ib_node(r), up=(r["name"] in ups) if not ib_node(r) else node_up(r))
                             for r in q("SELECT * FROM inbounds WHERE enabled=1 ORDER BY id")])


@app.get("/api/v1/clients")
@auth_any
def v1_clients():
    cond, args = [], []
    if g.role == "admin":
        cond.append("owner_id=?"); args.append(g.aid)
    for key, col in (("name", "name"), ("token", "token"), ("external_id", "ext_id")):
        v = request.args.get(key)
        if v:
            cond.append(f"{col}=?"); args.append(v)
    s = request.args.get("q")
    if s:
        cond.append("(name LIKE ? OR note LIKE ?)"); args += [f"%{s}%", f"%{s}%"]
    w = (" WHERE " + " AND ".join(cond)) if cond else ""
    limit = num(request.args.get("limit"), 50, 1, 200, "limit")
    offset = num(request.args.get("offset"), 0, 0, None, "offset")
    total = q("SELECT COUNT(*) n FROM clients" + w, tuple(args), True)["n"]
    rows = q("SELECT * FROM clients" + w + " ORDER BY id DESC LIMIT ? OFFSET ?", tuple(args) + (limit, offset))
    return jsonify(total=total, clients=[ser_client(c) for c in rows])


@app.get("/api/v1/clients/<int:cid>")
@auth_any
def v1_client_get(cid):
    return jsonify(client=ser_client(owned(cid)))


@app.post("/api/v1/clients")
@auth_any
def v1_client_create():
    d = dict(body())
    ibs = d.get("inbounds")
    if ibs is not None and not d.get("links"):
        if not isinstance(ibs, list) or not ibs:
            raise Err("inbounds باید لیست id اینباندها باشد؛ مثلاً [1, 2]")
        d["links"] = [dict(inbound_id=num(i, 0, 1, None, "id اینباند")) for i in ibs]
    if d.get("days") not in (None, "") and not d.get("expiry"):
        days = num(d.get("days"), 0, 0, 36500, "تعداد روز")
        d["expiry"] = now() + days * 86400 if days else 0
    cids, warn, existed = create_clients(d)
    return jsonify(ok=True, existing=existed, warn=warn, clients=[_v1_client(c) for c in cids]), (200 if existed else 201)


@app.post("/api/v1/clients/<int:cid>/renew")
@auth_any
def v1_client_renew(cid):
    """تمدید/تغییر: add_gb و add_days نسبی‌اند (منفی = کم کردن)؛ limit_gb و days مقدار مطلق؛ reset_traffic مصرف را صفر می‌کند"""
    c = owned(cid)
    d = body()
    if g.role == "admin":
        require_active_admin()
    lim, exp = c["limit_bytes"], c["expiry"]
    did = False
    if d.get("limit_gb") not in (None, ""):
        lim, did = _gb_bytes(d.get("limit_gb")), True
    if d.get("days") not in (None, ""):
        n = num(d.get("days"), 0, 0, 36500, "تعداد روز")
        exp, did = (now() + n * 86400 if n else 0), True
    if d.get("add_gb") not in (None, "", 0, "0"):
        try:
            lim = (lim or 0) + int(float(d.get("add_gb")) * 1024 ** 3)
        except Exception:
            raise Err("حجم نامعتبر است")
        if lim <= 0:
            raise Err("با این کم کردن حجم صفر یا منفی می‌شود؛ برای نامحدود limit_gb را 0 بدهید")
        did = True
    if d.get("add_days") not in (None, "", 0, "0"):
        n = num(d.get("add_days"), 0, -36500, 36500, "تعداد روز")
        exp, did = (max(exp, now()) if exp else now()) + n * 86400, True
    reset = bool(d.get("reset_traffic"))
    if not (did or reset):
        raise Err("حداقل یکی از add_gb ، add_days ، limit_gb ، days ، reset_traffic را بدهید")
    up, down = (0, 0) if reset else (c["up_bytes"], c["down_bytes"])
    x("UPDATE clients SET limit_bytes=?, expiry=?, up_bytes=?, down_bytes=? WHERE id=?", (lim, exp, up, down, cid))
    c2 = q("SELECT * FROM clients WHERE id=?", (cid,), True)
    if not c2["enabled"] and c2["reason"] in ("expired", "limit") and usage_state(c2) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)), client=_v1_client(cid))


@app.post("/api/v1/clients/<int:cid>/enable")
@auth_any
def v1_client_enable(cid):
    c = owned(cid)
    require_active_admin()
    if usage_state(c) != "active":
        raise Err("حجم یا اعتبار کلاینت تمام شده؛ اول renew بزنید")
    x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)), client=_v1_client(cid))


@app.post("/api/v1/clients/<int:cid>/disable")
@auth_any
def v1_client_disable(cid):
    owned(cid)
    x("UPDATE clients SET enabled=0, reason='disabled' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)), client=_v1_client(cid))


def key_quota_state(k):
    """وضعیت سهمیه‌ی کلید (غیرفعال بودن کلید حساب نمی‌شود؛ فقط حجم و زمان)"""
    if k["expiry"] and now() >= k["expiry"]:
        return "expired"
    if k["limit_bytes"] and k["used_bytes"] >= k["limit_bytes"]:
        return "limit"
    return "active"


def key_inbounds(kid):
    return {r["inbound_id"] for r in q(
        "SELECT ci.inbound_id FROM client_inbound ci JOIN clients c ON c.id=ci.client_id WHERE c.key_id=?", (kid,))}


def ser_key(r):
    a = q("SELECT username FROM admins WHERE id=?", (r["admin_id"],), True) if r["admin_id"] else None
    acc = ("ادمین: " + a["username"]) if a else ("ادمینِ حذف‌شده" if r["admin_id"] else "مدیر اصلی")
    st = "disabled" if not r["enabled"] else key_quota_state(r)
    return dict(id=r["id"], name=r["name"], prefix=r["prefix"], admin_id=r["admin_id"], account=acc,
                enabled=bool(r["enabled"]), created=r["created"], last_used=r["last_used"],
                limit_bytes=r["limit_bytes"], used_bytes=r["used_bytes"], expiry=r["expiry"], state=st,
                clients=q("SELECT COUNT(*) n FROM clients WHERE key_id=?", (r["id"],), True)["n"])


def _own_key(kid):
    r = q("SELECT * FROM api_keys WHERE id=?", (kid,), True) or abort(404)
    if g.role == "admin" and r["admin_id"] != g.aid:
        abort(404)
    return r


def _gb_bytes(v, label="حجم"):
    try:
        gb = float(v or 0)
    except Exception:
        raise Err(f"{label} نامعتبر است")
    if gb < 0:
        raise Err(f"{label} نمی‌تواند منفی باشد")
    return int(gb * 1024 ** 3)


@app.get("/api/apikeys")
@auth_adm
def apikey_list():
    if g.role == "admin":
        rows = q("SELECT * FROM api_keys WHERE admin_id=? ORDER BY id DESC", (g.aid,))
    else:
        rows = q("SELECT * FROM api_keys ORDER BY id DESC")
    return jsonify(keys=[ser_key(r) for r in rows])


@app.post("/api/apikeys")
@auth_adm
def apikey_create():
    d = body()
    name = oneline(d.get("name"))[:40]
    if not name:
        raise Err("یک نام برای کلید بنویسید")
    if g.role == "admin":
        require_active_admin()
        aid = g.aid                             # ادمین فقط برای خودش کلید می‌سازد
    else:
        aid = num(d.get("admin_id"), 0, 0, None, "ادمین")
        if aid and not q("SELECT 1 FROM admins WHERE id=?", (aid,), True):
            raise Err("ادمین انتخاب‌شده پیدا نشد")
    lim = _gb_bytes(d.get("limit_gb"), "حجم کلید")
    days = num(d.get("days"), 0, 0, 36500, "تعداد روز")
    key = "sp_" + secrets.token_urlsafe(32)
    x("INSERT INTO api_keys(name,key_hash,prefix,admin_id,enabled,created,last_used,limit_bytes,used_bytes,expiry) VALUES(?,?,?,?,1,?,0,?,0,?)",
      (name, hashlib.sha256(key.encode()).hexdigest(), key[:9], aid, now(), lim, now() + days * 86400 if days else 0))
    return jsonify(ok=True, key=key)          # فقط همین یک‌بار نمایش داده می‌شود؛ در دیتابیس فقط هش ذخیره است


@app.put("/api/apikeys/<int:kid>")
@auth_adm
def apikey_update(kid):
    """ویرایش نام و سهمیه‌ی کلید؛ limit_gb / days مقدار مطلق، add_gb / add_days تغییر نسبی (منفی = کم کردن)"""
    r = _own_key(kid)
    d = body()
    name = oneline(d.get("name") or r["name"])[:40]
    lim, exp, used = r["limit_bytes"], r["expiry"], r["used_bytes"]
    if d.get("limit_gb") not in (None, ""):
        lim = _gb_bytes(d.get("limit_gb"), "حجم کلید")
    if d.get("add_gb") not in (None, "", 0, "0"):
        try:
            lim = (lim or 0) + int(float(d.get("add_gb")) * 1024 ** 3)
        except Exception:
            raise Err("مقدار تغییر حجم نامعتبر است")
        if lim <= 0:
            raise Err("با این کم کردن حجم صفر یا منفی می‌شود؛ برای نامحدود limit_gb را 0 بدهید")
    if d.get("days") not in (None, ""):
        n = num(d.get("days"), 0, 0, 36500, "تعداد روز")
        exp = now() + n * 86400 if n else 0
    if d.get("add_days") not in (None, "", 0, "0"):
        n = num(d.get("add_days"), 0, -36500, 36500, "تغییر روز")
        exp = (max(exp, now()) if exp else now()) + n * 86400
    if d.get("reset_usage"):
        used = 0
    x("UPDATE api_keys SET name=?, limit_bytes=?, expiry=?, used_bytes=? WHERE id=?", (name, lim, exp, used, kid))
    KEY_STATE[kid] = key_quota_state(q("SELECT * FROM api_keys WHERE id=?", (kid,), True))
    return jsonify(ok=True, warn=apply_many(key_inbounds(kid)))      # کلاینت‌های این کلید با سهمیه‌ی جدید قطع/وصل می‌شوند


@app.post("/api/apikeys/<int:kid>/toggle")
@auth_adm
def apikey_toggle(kid):
    r = _own_key(kid)
    x("UPDATE api_keys SET enabled=? WHERE id=?", (0 if r["enabled"] else 1, kid))
    return jsonify(ok=True)


@app.delete("/api/apikeys/<int:kid>")
@auth_adm
def apikey_delete(kid):
    _own_key(kid)
    x("DELETE FROM api_keys WHERE id=?", (kid,))
    x("UPDATE clients SET key_id=0 WHERE key_id=?", (kid,))      # کلاینت‌ها می‌مانند، فقط دیگر به سهمیه‌ی این کلید وصل نیستند
    KEY_STATE.pop(kid, None)
    return jsonify(ok=True)


@app.get("/api/docs")
@auth_adm
def api_docs():
    return jsonify(html=api_docs_html(base_url()))


def api_docs_html(base):
    def code(s):
        return ('<div class="cb"><button class="s cp" onclick="copy(this.nextElementSibling.innerText)">کپی</button><pre><code>'
                + html.escape(s.strip("\n").replace("@@B@@", base)) + "</code></pre></div>")

    def ep(m, path, desc, params=(), ex=None, resp=None):
        cls = {"GET": "get", "POST": "post", "DELETE": "del"}[m]
        o = f'<div class="ep"><div><span class="m {cls}">{m}</span><code>{html.escape(path)}</code></div><p>{desc}</p>'
        if params:
            o += "<table><tr><th>پارامتر</th><th>توضیح</th></tr>" + "".join(
                f"<tr><td><code>{html.escape(a)}</code></td><td>{b}</td></tr>" for a, b in params) + "</table>"
        if ex:
            o += code(ex)
        if resp:
            o += '<p class="mut sm">نمونه پاسخ:</p>' + code(resp)
        return o + "</div>"

    H = []
    H.append("<h3>این بخش چه کاری می‌کند؟</h3><p>با API می‌توانید پنل را به ربات تلگرام، سایت یا هر نرم‌افزار دیگری وصل کنید تا فروش خودکار شود: مشتری پرداخت می‌کند ← ربات/سایت شما یک درخواست به پنل می‌فرستد ← پنل کلاینت را می‌سازد و <code>sub_url</code> (لینک اشتراک) را برمی‌گرداند ← شما همان لینک را به مشتری تحویل می‌دهید. تمدید، ریست ترافیک، غیرفعال‌سازی و حذف هم با همین API انجام می‌شود.</p>")
    H.append("<h3>شروع سریع</h3><ol>"
             "<li>(پیشنهادی) از تب «ادمین‌ها» یک ادمین مثلاً <code>bot</code> بسازید و برایش سقف حجم و زمان بگذارید. هرچه ربات بفروشد از همین سقف مصرف می‌شود؛ اگر کلید لو برود، خسارت از این سقف بیشتر نمی‌شود.</li>"
             "<li>بالای همین صفحه «+ کلید جدید» بزنید، همان ادمین را انتخاب کنید و کلید را کپی کنید. کلید فقط یک‌بار نمایش داده می‌شود و در پنل فقط هش آن ذخیره است.</li>"
             "<li>با دستور زیر امتحان کنید. اگر <code>role</code> برگشت، اتصال برقرار است:</li></ol>")
    H.append(code('curl -H "Authorization: Bearer sp_XXXXXXXX" @@B@@/api/v1/me'))
    H.append("<h3>احراز هویت و امنیت</h3><ul>"
             "<li>در هر درخواست یکی از این دو هدر را بفرستید: <code>Authorization: Bearer &lt;key&gt;</code> یا <code>X-API-Key: &lt;key&gt;</code>. هدر دیگری لازم نیست.</li>"
             "<li>کلید فقط به مسیرهای <code>/api/v1/…</code> (کلاینت‌ها و لیست اینباندها) دسترسی دارد؛ تنظیمات، نودها، تانل، ادمین‌ها و کلیدها با کلید در دسترس نیستند.</li>"
             "<li>کلید را فقط روی سرور ربات/سایت نگه دارید؛ هرگز در کد سمت کاربر (مرورگر، اپ) یا پیام تلگرام نگذارید.</li>"
             "<li>حتماً آدرس پنل HTTPS باشد (دامنه و گواهی را در تب «تنظیمات» بگذارید)، وگرنه کلید روی شبکه لو می‌رود.</li>"
             "<li>هر کلید می‌تواند سقف حجم و زمان مخصوص خودش را داشته باشد؛ فقط مصرف کلاینت‌هایی که با همان کلید ساخته شده‌اند از آن کم می‌شود. تمام شدن سقف کلید، ساخت جدید را رد می‌کند و کلاینت‌های همان کلید را قطع می‌کند (<code>state: key</code>)؛ با تمدید سقف از پنل خودکار وصل می‌شوند. ادمین‌ها از همین تب کلیدهای خودشان را می‌سازند و سقفشان را کم و زیاد می‌کنند.</li>"
             "<li>برای قطع دسترسی، کلید را «غیرفعال» یا «حذف» کنید؛ بلافاصله اثر می‌کند. تلاش با کلید اشتباه محدود می‌شود (بعد از چند بار، کد 429).</li></ul>")
    H.append("<h3>فرمت درخواست و پاسخ</h3><p>بدنه‌ی درخواست‌ها JSON است (<code>Content-Type: application/json</code>) و همه‌ی پاسخ‌ها JSON. زمان‌ها Unix timestamp به ثانیه‌اند (<code>expiry</code> برابر 0 یعنی بدون انقضا) و حجم‌ها به بایت (<code>limit_bytes</code> برابر 0 یعنی نامحدود). خطا همیشه به شکل <code>{\"error\": \"پیام\"}</code> با یکی از کدهای 400 (ورودی نامعتبر)، 401 (کلید نامعتبر)، 403، 404 (کلاینت پیدا نشد یا مال شما نیست) یا 429 برمی‌گردد. فیلد <code>warn</code> در پاسخ‌ها اگر پر باشد یعنی کلاینت ساخته/تغییر کرده ولی اعمالش روی یک اینباند خطا داشته.</p>")
    H.append("<h3>مرجع مسیرها</h3>")
    H.append(ep("GET", "/api/v1/me", "نقش کلید، سقف حجم/زمان و مصرف خودِ کلید (<code>key</code>) و برای کلید ادمین مصرف حساب ادمین (<code>account</code>) را نشان می‌دهد؛ برای چک کردن موجودی سهمیه‌ی ربات خوب است.",
                ex='curl -H "Authorization: Bearer $KEY" @@B@@/api/v1/me',
                resp='{"role": "admin", "key": {"name": "bot", "limit_bytes": 107374182400, "used_bytes": 52428800, "expiry": 1798000000, "state": "active", "clients": 12},\n "account": {"username": "bot", "limit_bytes": 1073741824000, "used_bytes": 52428800, "expiry": 0, "state": "active"}}'))
    H.append(ep("GET", "/api/v1/inbounds", "اینباندهای فعال را می‌دهد تا id هر اینباند را برای ساخت کلاینت بدانید (id را یک‌بار بردارید و در ربات ثابت بگذارید).",
                ex='curl -H "Authorization: Bearer $KEY" @@B@@/api/v1/inbounds',
                resp='{"inbounds": [{"id": 1, "name": "wg0", "remark": "", "proto": "wg", "port": 51820, "node_id": 0, "up": true},\n  {"id": 2, "name": "vless-de", "remark": "آلمان", "proto": "vless", "port": 443, "node_id": 1, "up": true}]}'))
    H.append(ep("POST", "/api/v1/clients", "یک کلاینت (یا چند تا) می‌سازد و همان لحظه کانفیگ را روی اینباندهای انتخاب‌شده اعمال می‌کند. اصلی‌ترین مسیر برای فروش.",
                params=[("name", "نام کلاینت (الزامی)؛ مثلاً <code>tg12345-1001</code>"),
                        ("inbounds", "لیست id اینباندها (الزامی)؛ مثلاً <code>[1, 2]</code>"),
                        ("limit_gb", "حجم به گیگابایت؛ 0 یا نفرستادن = نامحدود"),
                        ("days", "اعتبار به روز، از همین الان؛ 0 یا نفرستادن = بدون انقضا. (یا به‌جایش <code>expiry</code> = Unix timestamp)"),
                        ("external_id", "شناسه‌ی سفارش شما (پیشنهاد قوی). اگر همین سفارش دوباره بیاید (مثلاً درگاه دوبار callback بزند) کلاینت تکراری ساخته نمی‌شود و همان قبلی با <code>existing: true</code> برمی‌گردد."),
                        ("note", "یادداشت دلخواه (مثلاً آیدی تلگرام خریدار)"),
                        ("reset_period", "<code>daily</code> / <code>weekly</code> / <code>monthly</code> برای ریست خودکار ترافیک؛ خالی = بدون ریست"),
                        ("count", "تعداد کلاینت (پیش‌فرض 1، حداکثر 200)؛ با <code>external_id</code> فقط 1")],
                ex='curl -X POST @@B@@/api/v1/clients \\\n  -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" \\\n  -d \'{"name": "tg12345-1001", "limit_gb": 30, "days": 30, "inbounds": [1, 2], "external_id": "1001", "note": "tg:12345"}\'',
                resp='{"ok": true, "existing": false, "warn": "",\n "clients": [{"id": 12, "name": "tg12345-1001", "state": "active", "enabled": 1,\n   "limit_bytes": 32212254720, "up_bytes": 0, "down_bytes": 0, "expiry": 1795000000,\n   "token": "Ab3xYz...", "sub_url": "@@B@@/sub/Ab3xYz...", "ext_id": "1001",\n   "links": [{"inbound_id": 2, "ib_name": "vless-de", "proto": "vless", "vlink": "vless://..."}]}]}'))
    H.append(ep("GET", "/api/v1/clients", "لیست کلاینت‌ها (کلید ادمین فقط کلاینت‌های خودش را می‌بیند). برای نمایش وضعیت و مصرف به مشتری یا پیدا کردن کلاینت از روی سفارش.",
                params=[("external_id", "پیدا کردن کلاینت یک سفارش"), ("name", "نام دقیق"), ("token", "توکن داخل لینک اشتراک (مشتری لینکش را بفرستد، شما کلاینتش را پیدا کنید)"),
                        ("q", "جستجو در نام و یادداشت (مثلاً آیدی تلگرام)"), ("limit / offset", "صفحه‌بندی؛ پیش‌فرض 50، حداکثر 200")],
                ex='curl -H "Authorization: Bearer $KEY" "@@B@@/api/v1/clients?q=tg:12345"',
                resp='{"total": 1, "clients": [ {…مثل بالا…} ]}'))
    H.append(ep("GET", "/api/v1/clients/{id}", "اطلاعات و مصرف یک کلاینت. مصرف = <code>up_bytes + down_bytes</code>. <code>state</code> یکی از: <code>active</code>، <code>expired</code> (زمان تمام)، <code>limit</code> (حجم تمام)، <code>disabled</code>، <code>admin</code> (سقف ادمین صاحبش تمام شده).",
                ex='curl -H "Authorization: Bearer $KEY" @@B@@/api/v1/clients/12'))
    H.append(ep("POST", "/api/v1/clients/{id}/renew", "تمدید و تغییر حجم/زمان (کم و زیاد). هر ترکیبی از گزینه‌های زیر را می‌توانید بدهید؛ اگر کلاینت به‌خاطر اتمام حجم/زمان قطع شده بود و بعد از تغییر دوباره معتبر شود، خودکار وصل می‌شود.",
                params=[("add_days", "به روز اضافه می‌کند؛ منفی = کم می‌کند. اگر اعتبار هنوز مانده، از انتهای همان حساب می‌شود وگرنه از الان"),
                        ("add_gb", "به سقف حجم اضافه می‌کند؛ منفی = کم می‌کند (کلاینت نامحدود با این گزینه محدود می‌شود)"),
                        ("limit_gb / days", "مقدار مطلق: سقف حجم را دقیقاً این عدد می‌گذارد (0 = نامحدود) و اعتبار را از همین الان این‌قدر روز می‌کند (0 = بدون انقضا)"),
                        ("reset_traffic", "<code>true</code> = مصرف را صفر می‌کند. تمدید ماهانه‌ی معمول: <code>{\"add_days\": 30, \"reset_traffic\": true}</code>")],
                ex='curl -X POST @@B@@/api/v1/clients/12/renew \\\n  -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" \\\n  -d \'{"add_days": 30, "reset_traffic": true}\'',
                resp='{"ok": true, "warn": "", "client": {…کلاینت به‌روز…}}'))
    H.append(ep("POST", "/api/v1/clients/{id}/disable", "کلاینت را قطع می‌کند (قابل برگشت)."))
    H.append(ep("POST", "/api/v1/clients/{id}/enable", "کلاینت را دوباره وصل می‌کند؛ اگر حجم یا زمانش تمام شده باشد خطا می‌دهد و اول باید renew بزنید."))
    H.append(ep("POST", "/api/v1/clients/{id}/reset-traffic", "فقط مصرف را صفر می‌کند."))
    H.append(ep("POST", "/api/v1/clients/{id}/reset-token", "لینک اشتراک را عوض می‌کند و لینک قبلی از کار می‌افتد (وقتی مشتری لینکش را لو داده). لینک جدید را با GET همان کلاینت بخوانید."))
    H.append(ep("DELETE", "/api/v1/clients/{id}", "کلاینت را برای همیشه حذف می‌کند.",
                ex='curl -X DELETE -H "Authorization: Bearer $KEY" @@B@@/api/v1/clients/12'))
    H.append("<h3>لینک اشتراک (sub_url)</h3><p>همان <code>sub_url</code> را به مشتری بدهید. برنامه‌های کلاینت (V2Ray، Hiddify، Streisand، …) آن را به‌صورت اشتراک می‌خوانند و مرورگر یک صفحه‌ی زیبا با QR و آموزش نشان می‌دهد. پارامترهای اختیاری: <code>?format=raw</code> (لینک‌های خام)، <code>?format=json</code>، <code>?format=conf</code>، <code>?inbound=ID</code> (فقط یک اینباند). فایل تک‌تک: <code>/sub/&lt;token&gt;/&lt;inbound_id&gt;.conf</code> (یا <code>.ovpn</code>) و QR: <code>/sub/&lt;token&gt;/link.svg</code>. وقتی حجم/زمان کلاینت تمام شود لینک اشتراک 403 می‌دهد.</p>")
    H.append("<h3>الگوی فروش خودکار (پیشنهادی)</h3><ol>"
             "<li>مشتری در ربات/سایت پلن را انتخاب می‌کند و به درگاه پرداخت می‌رود؛ برای هر سفارش یک شناسه‌ی یکتا (<code>order_id</code>) در دیتابیس خودتان بسازید.</li>"
             "<li>در callback درگاه، پرداخت را حتماً با verify خود درگاه تأیید کنید (به پارامترهای callback اعتماد نکنید).</li>"
             "<li>بعد از تأیید، <code>POST /api/v1/clients</code> را با <code>external_id = order_id</code> صدا بزنید و <code>sub_url</code> را به مشتری بدهید. چون <code>external_id</code> دارید، تکرار callback خطری ندارد.</li>"
             "<li>تمدید: همان کلاینت را با <code>renew</code> تمدید کنید (id کلاینت را کنار سفارش ذخیره کنید یا با <code>external_id</code> پیدا کنید).</li>"
             "<li>اگر شبکه یا پنل خطا داد، همان درخواست را با همان <code>external_id</code> دوباره بفرستید؛ نتیجه یکی است.</li></ol>")
    H.append("<h3>نمونه کد: کتابخانه‌ی کوچک پایتون</h3><p>همه‌ی نمونه‌های بعدی از همین فایل استفاده می‌کنند؛ آن را به‌صورت <code>panel.py</code> کنار ربات بگذارید (<code>pip install requests</code>).</p>")
    H.append(code(r"""
import requests

PANEL = "@@B@@"
KEY = "sp_XXXXXXXX"          # فقط روی سرور ربات؛ بهتر است از متغیر محیطی بخوانید
INBOUNDS = [1, 2]            # id اینباندهایی که به مشتری داده می‌شود (از /api/v1/inbounds)

_s = requests.Session()
_s.headers["Authorization"] = "Bearer " + KEY


def call(method, path, **kw):
    r = _s.request(method, PANEL + "/api/v1" + path, timeout=60, **kw)
    try:
        data = r.json()
    except ValueError:
        raise RuntimeError("پاسخ نامعتبر از پنل: %s" % r.text[:200])
    if r.status_code >= 400:
        raise RuntimeError(data.get("error", "خطا"))
    return data


def create_client(name, gb, days, order_id, note=""):
    d = call("POST", "/clients", json={
        "name": name, "limit_gb": gb, "days": days, "inbounds": INBOUNDS,
        "external_id": str(order_id), "note": note})
    return d["clients"][0]


def renew_client(client_id, days=30, gb=0):
    body = {"add_days": days, "reset_traffic": True}
    if gb:
        body["add_gb"] = gb
    return call("POST", "/clients/%d/renew" % client_id, json=body)["client"]


def find_by_token(token):
    d = call("GET", "/clients", params={"token": token})
    return d["clients"][0] if d["clients"] else None


def usage_text(c):
    used = (c["up_bytes"] + c["down_bytes"]) / 1024 ** 3
    total = "نامحدود" if not c["limit_bytes"] else "%.1f گیگ" % (c["limit_bytes"] / 1024 ** 3)
    return "وضعیت: %s\nمصرف: %.2f گیگ از %s" % (c["state"], used, total)
"""))
    H.append("<h3>نمونه کد: ربات تلگرام (python-telegram-bot نسخه 20 به بالا)</h3><p>ربات پلن‌ها را نشان می‌دهد و بعد از «تأیید پرداخت» سرویس را می‌سازد. تابع‌های <code>make_payment_link</code> و <code>payment_ok</code> را با درگاه خودتان پر کنید؛ بقیه آماده است.</p>")
    H.append(code(r"""
# pip install "python-telegram-bot>=20" requests
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes
import panel                                   # فایل بالا

BOT_TOKEN = "123456:ABC..."
PLANS = {                                      # کد: (عنوان، گیگ، روز، قیمت)
    "p1": ("۳۰ گیگ - ۳۰ روزه", 30, 30, 150000),
    "p2": ("۱۰۰ گیگ - ۳۰ روزه", 100, 30, 350000),
}


def make_payment_link(user_id, plan, order_id):
    # اینجا سفارش را در دیتابیس خودتان ثبت کنید و لینک پرداخت درگاه را برگردانید
    return "https://pay.example.com/pay/%s" % order_id


def payment_ok(order_id):
    # اینجا با API درگاه (verify) چک کنید پرداخت واقعاً انجام شده؛ True / False
    return False


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    kb = [[InlineKeyboardButton("%s — %s تومان" % (t, format(p, ",")), callback_data="buy:" + k)]
          for k, (t, gb, d, p) in PLANS.items()]
    await update.message.reply_text("یک پلن انتخاب کنید:", reply_markup=InlineKeyboardMarkup(kb))


async def buy(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    plan = q.data.split(":")[1]
    order_id = "%d-%d" % (q.from_user.id, q.message.message_id)       # شناسه‌ی یکتای سفارش
    ctx.user_data["order"] = (order_id, plan)
    kb = [[InlineKeyboardButton("پرداخت کردم ✅", callback_data="paid")]]
    await q.message.reply_text("لینک پرداخت:\n" + make_payment_link(q.from_user.id, plan, order_id),
                               reply_markup=InlineKeyboardMarkup(kb))


async def paid(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    order = ctx.user_data.get("order")
    if not order or not payment_ok(order[0]):
        await q.message.reply_text("پرداخت هنوز تأیید نشده.")
        return
    order_id, plan = order
    title, gb, days, _ = PLANS[plan]
    c = panel.create_client("tg%d-%s" % (q.from_user.id, order_id), gb, days, order_id, note="tg:%d" % q.from_user.id)
    await q.message.reply_text("✅ سرویس شما آماده است\n%s\n\nلینک اشتراک (در برنامه‌ی V2Ray/Hiddify اضافه کنید):\n%s"
                               % (title, c["sub_url"]))


app = Application.builder().token(BOT_TOKEN).build()
app.add_handler(CommandHandler("start", start))
app.add_handler(CallbackQueryHandler(buy, pattern="^buy:"))
app.add_handler(CallbackQueryHandler(paid, pattern="^paid$"))
app.run_polling()
"""))
    H.append("<h3>نمونه کد: وب‌هوک پرداخت برای سایت (Flask)</h3><p>برای سایت یا ربات‌هایی که درگاه خودش callback می‌زند. این نمونه بعد از تأیید پرداخت سرویس را می‌سازد و لینک را با Bot API تلگرام برای مشتری می‌فرستد (به <code>pip install flask requests</code> نیاز دارد).</p>")
    H.append(code(r"""
from flask import Flask, request
import requests, panel

app = Flask(__name__)
BOT_TOKEN = "123456:ABC..."


def gateway_verify(form):
    # با API درگاه تأیید کنید؛ True / False
    return False


def get_order(order_id):
    # از دیتابیس خودتان: dict(id=..., tg_id=..., gb=30, days=30)
    raise NotImplementedError


@app.post("/payment/callback")
def callback():
    order = get_order(request.form["order_id"])
    if not gateway_verify(request.form):
        return "fail", 400
    # external_id = شناسه‌ی سفارش → اگر درگاه چند بار callback بزند فقط یک کلاینت ساخته می‌شود
    c = panel.create_client("web-%s" % order["id"], order["gb"], order["days"], order["id"], note="web")
    requests.post("https://api.telegram.org/bot%s/sendMessage" % BOT_TOKEN,
                  json={"chat_id": order["tg_id"], "text": "✅ سرویس شما آماده است:\n" + c["sub_url"]}, timeout=20)
    return "ok"
"""))
    H.append("<h3>نمونه‌ی کوتاه Node.js و PHP</h3>")
    H.append(code(r"""
// Node 18+
const r = await fetch("@@B@@/api/v1/clients", {
  method: "POST",
  headers: { Authorization: "Bearer " + process.env.PANEL_KEY, "Content-Type": "application/json" },
  body: JSON.stringify({ name: "web-1001", limit_gb: 30, days: 30, inbounds: [1, 2], external_id: "1001" }),
});
const data = await r.json();
if (!r.ok) throw new Error(data.error);
console.log(data.clients[0].sub_url);
"""))
    H.append(code(r"""
<?php
$ch = curl_init("@@B@@/api/v1/clients");
curl_setopt_array($ch, [
  CURLOPT_POST => true, CURLOPT_RETURNTRANSFER => true,
  CURLOPT_HTTPHEADER => ["Authorization: Bearer " . getenv("PANEL_KEY"), "Content-Type: application/json"],
  CURLOPT_POSTFIELDS => json_encode(["name" => "web-1001", "limit_gb" => 30, "days" => 30, "inbounds" => [1, 2], "external_id" => "1001"]),
]);
$data = json_decode(curl_exec($ch), true);
echo $data["clients"][0]["sub_url"];
"""))
    H.append("<h3>نکات مهم</h3><ul>"
             "<li>سرور ربات/سایت باید به آدرس پنل دسترسی داشته باشد؛ اگر پنل پشت فایروال است، آی‌پی سرور ربات را در فایروال باز کنید.</li>"
             "<li>کلیدی که به ادمین وصل است فقط همان ادمین را می‌بیند: کلاینت‌هایی که با آن می‌سازید به نام همان ادمین ثبت می‌شوند و از سقف حجم/زمانش مصرف می‌کنند. اگر سقف ادمین تمام شود ساخت جدید خطا می‌دهد و کلاینت‌هایش هم قطع می‌شوند؛ از تب «ادمین‌ها» تمدیدش کنید.</li>"
             "<li>اگر حذف ادمین را بزنید، کلیدهای وصل‌شده به او هم حذف می‌شوند.</li>"
             "<li>ساخت کلاینت روی اینباند وایرگارد و OpenVPN و L2TP هم ممکن است؛ اما برای فروش، اینباندهای VLESS روی نودها معمولاً راحت‌ترین‌اند چون لینک ساب همه‌ی لوکیشن‌ها را در یک لینک جمع می‌کند.</li>"
             "<li>مسیرهای قدیمی‌تر <code>/api/clients/…</code> هم با کلید کار می‌کنند، ولی پایدارِ مستند <code>/api/v1</code> است.</li></ul>")
    return "".join(H)


@app.put("/api/settings")
@auth
def settings_save():
    d = body()
    u = str(d.get("public_url", "")).strip()
    if u and not re.fullmatch(r"https?://[^\s/]+(/\S*)?", u):
        raise Err("آدرس پنل باید با http:// یا https:// شروع شود")
    set_setting("public_url", u)
    set_setting("sub_title", oneline(d.get("sub_title")) or "WireGuard")
    tgv = re.sub(r"^(https?://)?(t\.me/|telegram\.me/)?@?", "", str(d.get("sub_telegram", "")).strip()).strip("/")
    if tgv and not re.fullmatch(r"[A-Za-z0-9_]{3,64}", tgv):
        raise Err("آیدی تلگرام فقط شامل حرف انگلیسی، عدد و _ باشد (مثلاً sepiamDigee)")
    set_setting("sub_telegram", tgv)
    set_setting("update_interval", num(d.get("update_interval"), 12, 1, 720, "بازه آپدیت"))
    return jsonify(ok=True)


# ------------------------------ لینک ساب ------------------------------
def sub_data(token):
    c = q("SELECT * FROM clients WHERE token=?", (token,), True) or abort(404)
    rows = q("""SELECT ci.*, ib.id AS ibid FROM client_inbound ci JOIN inbounds ib ON ib.id=ci.inbound_id
                WHERE ci.client_id=? AND ib.enabled=1 AND ib.exclude_sub=0 ORDER BY ib.id""", (c["id"],))
    out = []
    for ci in rows:
        ib = q("SELECT * FROM inbounds WHERE id=?", (ci["ibid"],), True)
        out.append((ci, ib))
    return c, out


def qr_svg(text):
    if not qrcode:
        abort(404)
    img = qrcode.make(text, image_factory=qrcode.image.svg.SvgPathImage, box_size=8, border=2)
    buf = io.BytesIO(); img.save(buf)
    return Response(buf.getvalue(), mimetype="image/svg+xml", headers={"Cache-Control": "no-store"})


def qr_data_uri(text):
    if not qrcode:
        return ""
    try:
        img = qrcode.make(text, image_factory=qrcode.image.svg.SvgPathImage, box_size=8, border=2)
        buf = io.BytesIO(); img.save(buf)
        return "data:image/svg+xml;base64," + base64.b64encode(buf.getvalue()).decode()
    except Exception:
        return ""


def fmt_b(n):
    n = float(n or 0)
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or u == "TB":
            if u == "B":
                return f"{int(n)} B"
            return f"{n:.2f}".rstrip("0").rstrip(".") + f" {u}"
        n /= 1024


def g2j(gy, gm, gd):
    """میلادی به شمسی"""
    gdm = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    if gy > 1600:
        jy = 979; gy -= 1600
    else:
        jy = 0; gy -= 621
    gy2 = gy + 1 if gm > 2 else gy
    days = 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400 - 80 + gd + gdm[gm - 1]
    jy += 33 * (days // 12053); days %= 12053
    jy += 4 * (days // 1461); days %= 1461
    if days > 365:
        jy += (days - 1) // 365; days = (days - 1) % 365
    if days < 186:
        jm = 1 + days // 31; jd = 1 + days % 31
    else:
        jm = 7 + (days - 186) // 30; jd = 1 + (days - 186) % 30
    return jy, jm, jd


def jalali_str(ts):
    lt = time.localtime(ts)
    jy, jm, jd = g2j(lt.tm_year, lt.tm_mon, lt.tm_mday)
    return f"{jy}/{jm:02d}/{jd:02d}", time.strftime("%H:%M", lt)


def ago_fa(ts):
    if not ts:
        return "هنوز متصل نشده‌اید"
    d = max(0, now() - ts)
    if d < 180:
        return "هم‌اکنون"
    if d < 3600:
        return f"{d // 60} دقیقه پیش"
    if d < 86400:
        return f"{d // 3600} ساعت پیش"
    return f"{d // 86400} روز پیش"


def tg_id():
    return re.sub(r"[^A-Za-z0-9_]", "", setting("sub_telegram", ""))


_IC = {
    "shield": '<path d="M12 3l7 3v5c0 5-3.2 8.4-7 10-3.8-1.6-7-5-7-10V6z"/><path d="M9 12l2 2 4-4"/>',
    "shieldx": '<path d="M12 3l7 3v5c0 5-3.2 8.4-7 10-3.8-1.6-7-5-7-10V6z"/><path d="M9.5 9.5l5 5M14.5 9.5l-5 5"/>',
    "signal": '<path d="M5 20v-4M10 20v-8M15 20V8M20 20V4"/>',
    "db": '<ellipse cx="12" cy="6" rx="7" ry="3"/><path d="M5 6v6c0 1.7 3.1 3 7 3s7-1.3 7-3V6M5 12v6c0 1.7 3.1 3 7 3s7-1.3 7-3v-6"/>',
    "up": '<circle cx="12" cy="12" r="9"/><path d="M12 16V8M8.5 11.5L12 8l3.5 3.5"/>',
    "down": '<circle cx="12" cy="12" r="9"/><path d="M12 8v8M8.5 12.5L12 16l3.5-3.5"/>',
    "box": '<path d="M12 3l8 4.5v9L12 21l-8-4.5v-9z"/><path d="M4 7.5l8 4.5 8-4.5M12 12v9"/>',
    "cal": '<rect x="4" y="5" width="16" height="15" rx="3"/><path d="M8 3v4M16 3v4M4 10h16"/>',
    "clock": '<circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/>',
    "link": '<path d="M10 14a4 4 0 0 0 5.7 0l3-3a4 4 0 0 0-5.7-5.7l-1 1"/><path d="M14 10a4 4 0 0 0-5.7 0l-3 3A4 4 0 0 0 11 18.7l1-1"/>',
    "copy": '<rect x="8" y="8" width="12" height="12" rx="3"/><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"/>',
    "qr": '<rect x="4" y="4" width="6" height="6" rx="1"/><rect x="14" y="4" width="6" height="6" rx="1"/><rect x="4" y="14" width="6" height="6" rx="1"/><path d="M14 14h2v2h-2zM18 14h2v2M14 18h2v2M18 18h2v2"/>',
    "dl": '<path d="M12 4v11M7.5 11L12 15.5 16.5 11M5 20h14"/>',
    "plus": '<circle cx="12" cy="12" r="9"/><path d="M12 8v8M8 12h8"/>',
    "arrow": '<path d="M19 12H5M11 6l-6 6 6 6"/>',
    "file": '<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5M9 13h6M9 17h6"/>',
    "code": '<path d="M8 8l-4 4 4 4M16 8l4 4-4 4M13.5 6l-3 12"/>',
    "tg": '<path d="M21 4L3 11l6 2 2 6 3-4 5 3z"/>',
    "net": '<circle cx="12" cy="12" r="9"/><path d="M3 12h18M12 3c3 3 3 15 0 18M12 3c-3 3-3 15 0 18"/>',
}


def _ic(n):
    return ('<svg class="i" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" '
            f'stroke-linecap="round" stroke-linejoin="round">{_IC[n]}</svg>')


SUB_LOGO = ('<svg viewBox="0 0 64 64" width="46" height="46"><defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1">'
            '<stop offset="0" stop-color="#7aa2ff"/><stop offset="1" stop-color="#6a3df0"/></linearGradient></defs>'
            '<path d="M32 4L8 14v16c0 15 10 25 24 30 14-5 24-15 24-30V14z" fill="url(#lg)"/>'
            '<path d="M45 19L21 30l8.5 3.2L33 44l5-8 7 2.2z" fill="#0b1330"/></svg>')

SUB_BG = ('<svg class="bgm" viewBox="0 0 560 340" preserveAspectRatio="xMidYMin slice" aria-hidden="true"><defs>'
          '<linearGradient id="sk" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#141a46"/>'
          '<stop offset=".55" stop-color="#5a4686"/><stop offset=".82" stop-color="#e0805f" stop-opacity=".8"/>'
          '<stop offset="1" stop-color="#070d1c" stop-opacity="0"/></linearGradient>'
          '<radialGradient id="sn" cx=".5" cy=".5" r=".5"><stop offset="0" stop-color="#ffd9a0"/>'
          '<stop offset="1" stop-color="#ffb070" stop-opacity="0"/></radialGradient>'
          '<linearGradient id="fd" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#070d1c" stop-opacity="0"/>'
          '<stop offset="1" stop-color="#070d1c"/></linearGradient></defs>'
          '<rect width="560" height="340" fill="url(#sk)"/><circle cx="430" cy="236" r="70" fill="url(#sn)"/>'
          '<path d="M0 250l60-52 40 30 70-80 60 70 50-40 70 66 55-50 60 62 40-34 55 52v96H0z" fill="#161b3f" opacity=".85"/>'
          '<path d="M0 290l80-46 60 38 80-62 70 58 70-48 80 60 60-44 60 50v94H0z" fill="#0c1230"/>'
          '<rect y="200" width="560" height="140" fill="url(#fd)"/></svg>')

SUB_CSS = r""":root{color-scheme:dark;--bg:#070d1c;--card:rgba(15,24,50,.74);--line:rgba(130,160,255,.16);--tx:#eaf0ff;--mut:#8fa0c4;--ac:#4f7cff;--ac2:#7a5cff;--ok:#34d399;--warn:#fbbf24;--bad:#f87171}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}html{background:var(--bg)}
body{margin:0;min-height:100vh;font:15px/1.7 Vazirmatn,Vazir,IRANSans,"Segoe UI",Tahoma,system-ui,sans-serif;color:var(--tx);position:relative;overflow-x:hidden;
background:radial-gradient(110% 50% at 50% 0,#1d2358 0,#0d1533 42%,var(--bg) 75%)}
.bgm{position:absolute;top:0;left:0;width:100%;height:340px;z-index:0;pointer-events:none}
.w{position:relative;z-index:1;max-width:580px;margin:0 auto;padding:24px 14px 36px}
.logo{display:flex;align-items:center;justify-content:center;gap:10px;direction:ltr;margin-top:8px}
.logo b{font:700 40px/1 "Segoe UI",system-ui,sans-serif;letter-spacing:-1.5px}.logo b span{color:#5b8cff}
.tag{text-align:center;color:#c3cdea;font-size:13px;letter-spacing:.6px;direction:ltr;margin-top:6px}
.hi{text-align:center;margin:34px 0 2px;font-size:19px;font-weight:800}
.hs{text-align:center;color:var(--mut);font-size:13px}
.who{display:flex;justify-content:center;margin-top:8px}.who span{background:rgba(79,124,255,.14);border:1px solid var(--line);border-radius:999px;padding:2px 14px;font-size:13px;color:#c9d6ff}
.card{background:var(--card);-webkit-backdrop-filter:blur(14px);backdrop-filter:blur(14px);border:1px solid var(--line);border-radius:20px;padding:16px;margin-top:14px;box-shadow:0 12px 40px rgba(0,0,0,.35)}
.i{width:20px;height:20px;flex:none}
.ct{display:flex;align-items:center;gap:8px;font-weight:700;margin-bottom:12px}.ct .i{color:#6f94ff}.ct em{margin-inline-start:auto;font-style:normal;font-size:12px;color:var(--mut);font-weight:400}
.stt{display:flex;align-items:center;gap:14px}
.sh{width:62px;height:62px;border-radius:50%;display:grid;place-items:center;flex:none;color:var(--ok);background:rgba(52,211,153,.1);border:2px solid rgba(52,211,153,.35);box-shadow:0 0 28px rgba(52,211,153,.18)}
.sh .i{width:32px;height:32px}.sh.bad{color:var(--bad);background:rgba(248,113,113,.1);border-color:rgba(248,113,113,.35);box-shadow:0 0 28px rgba(248,113,113,.18)}
.stt h3{margin:0;font-size:16px;display:flex;gap:8px;align-items:center;flex-wrap:wrap}.stt p{margin:2px 0 0;color:var(--mut);font-size:13px;line-height:1.6}
.bd{font-size:12px;font-weight:700;padding:1px 12px;border-radius:999px;background:rgba(52,211,153,.16);color:var(--ok)}.bd.bad{background:rgba(248,113,113,.16);color:var(--bad)}.bd.warn{background:rgba(251,191,36,.16);color:var(--warn)}
.sig{margin-inline-start:auto;width:42px;height:42px;border-radius:12px;display:grid;place-items:center;color:var(--ok);background:rgba(52,211,153,.08);flex:none}.sig.bad{color:var(--mut);background:rgba(143,160,196,.08)}
.bar{height:10px;border-radius:6px;background:rgba(120,150,255,.14);overflow:hidden}.bar i{display:block;height:100%;border-radius:6px;background:linear-gradient(90deg,#3b6cf6,#6f94ff);transition:width .8s}
.bar.w1 i{background:linear-gradient(90deg,#d99a06,#fbbf24)}.bar.w2 i{background:linear-gradient(90deg,#dc3b3b,#f87171)}.bar.inf i{opacity:.35;background:repeating-linear-gradient(135deg,#3b6cf6 0 10px,#5b86ff 10px 20px)}
.g3{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-top:14px}
.sc{min-width:0}.sc .v{display:flex;align-items:center;gap:6px;font-weight:700;font-size:15px;white-space:nowrap}.sc .v .i{color:#6f94ff;width:18px;height:18px}.sc small{display:block;color:var(--mut);font-size:12px;margin-top:0}
.ud{display:flex;justify-content:space-between;gap:8px;margin-top:12px;padding-top:10px;border-top:1px dashed var(--line);font-size:12.5px;color:var(--mut)}.ud b{color:var(--tx)}
.ex{display:flex;align-items:center;gap:12px}.exi{width:46px;height:46px;border-radius:14px;display:grid;place-items:center;background:rgba(79,124,255,.14);color:#8aa9ff;flex:none}.exi .i{width:24px;height:24px}
.ex h4{margin:0;font-size:15px}.ex p{margin:0;color:var(--mut);font-size:13.5px;direction:ltr;text-align:right;white-space:nowrap}
.dl{flex:none;margin-inline-start:auto;display:flex;align-items:center;gap:6px;background:rgba(79,124,255,.14);color:#9db6ff;border:1px solid var(--line);padding:4px 10px;border-radius:12px;font-size:12.5px;white-space:nowrap}.dl .i{width:16px;height:16px}.dl b{font-size:16px;color:#fff}
.dl.warn{color:var(--warn);background:rgba(251,191,36,.1)}.dl.bad{color:var(--bad);background:rgba(248,113,113,.1)}
.lk{display:flex;gap:8px;align-items:stretch}
.box{flex:1;min-width:0;direction:ltr;text-align:left;background:rgba(6,12,30,.7);border:1px solid var(--line);border-radius:12px;padding:10px 12px;font:12.5px/1.5 ui-monospace,Consolas,monospace;color:#cfe0ff;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;display:flex;align-items:center}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:7px;border:1px solid var(--line);background:rgba(79,124,255,.12);color:#dbe5ff;border-radius:12px;padding:9px 14px;font:inherit;font-size:13.5px;cursor:pointer;text-decoration:none;white-space:nowrap;transition:.15s}
.btn:hover{background:rgba(79,124,255,.24)}.btn:active{transform:scale(.97)}.btn .i{width:18px;height:18px}
.btn.p{background:linear-gradient(90deg,#3b6cf6,#6f55f0);border-color:transparent;color:#fff;box-shadow:0 6px 20px rgba(79,100,255,.35)}.btn.p:hover{filter:brightness(1.1)}
.btn.sq{padding:9px 12px}.btn.big{width:100%;padding:13px 16px;font-size:15px;margin-top:12px;justify-content:space-between}
.apps{display:grid;grid-template-columns:repeat(5,1fr);gap:6px;margin-top:12px}
.app{display:flex;flex-direction:column;align-items:center;gap:5px;padding:10px 2px;border-radius:14px;border:1px solid var(--line);background:rgba(10,18,42,.6);color:#cfd9f5;text-decoration:none;font-size:11px;min-width:0;transition:.15s}
.app:hover{background:rgba(79,124,255,.16)}.app i{width:30px;height:30px;border-radius:9px;display:grid;place-items:center;font:700 14px/1 "Segoe UI",sans-serif;font-style:normal;color:#fff}
.qrb{display:none;margin-top:12px;text-align:center}.qrb.open{display:block}.qrb img{width:230px;max-width:100%;background:#fff;padding:12px;border-radius:16px;box-shadow:0 8px 30px rgba(0,0,0,.4)}.qrb small{display:block;color:var(--mut);margin-top:8px}
.ibh{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:12px}.ibh h3{margin:0;font-size:16px}.ibh small{color:var(--mut)}
.tg2{font-size:11px;padding:0 10px;border-radius:999px;background:rgba(122,92,255,.18);color:#b9a8ff;border:1px solid rgba(122,92,255,.3)}
.inf2{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:12px}.inf2 div{background:rgba(6,12,30,.5);border:1px solid var(--line);border-radius:12px;padding:6px 10px;min-width:0}
.inf2 .cc{grid-column:1/-1}.inf2 .cl{cursor:pointer;position:relative;padding-inline-end:30px}.inf2 .cl .cpi{position:absolute;inset-inline-end:8px;top:50%;transform:translateY(-50%);opacity:.65}.inf2 .cl .cpi svg{width:15px;height:15px}.inf2 .cl:active{background:rgba(79,124,255,.18)}.inf2 small{display:block;color:var(--mut);font-size:11.5px;direction:ltr;text-align:left}.inf2 b{display:block;direction:ltr;text-align:left;font:600 12.5px ui-monospace,Consolas,monospace;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.acts{display:flex;gap:8px;flex-wrap:wrap}.acts .btn{flex:1 1 auto}
details{margin-top:12px;border:1px solid var(--line);border-radius:12px;background:rgba(6,12,30,.45)}details summary{cursor:pointer;padding:10px 12px;font-size:13.5px;color:#c9d6ff;display:flex;align-items:center;gap:8px;list-style:none}
details summary::-webkit-details-marker{display:none}details summary .i{width:18px;height:18px;color:#6f94ff}details summary:after{content:"";margin-inline-start:auto;width:8px;height:8px;border-inline-end:2px solid var(--mut);border-bottom:2px solid var(--mut);transform:rotate(45deg);transition:.2s}details[open] summary:after{transform:rotate(-135deg)}
pre{direction:ltr;text-align:left;margin:0;padding:12px;border-top:1px solid var(--line);color:#cfe0ff;font:12.5px/1.55 ui-monospace,Consolas,monospace;white-space:pre-wrap;word-break:break-all;max-height:300px;overflow:auto;user-select:all}
.dc{padding:0 12px 12px}.dc .btn{width:100%;margin-top:10px}
.warnb{margin-top:10px;font-size:12.5px;color:#fcd98a;background:rgba(251,191,36,.08);border:1px solid rgba(251,191,36,.22);border-radius:12px;padding:8px 12px}
.off{text-align:center;color:var(--mut)}.off p{margin:4px 0 0}
.ft{display:flex;align-items:center;justify-content:center;gap:12px;margin-top:26px;color:var(--mut);font-size:12px;text-decoration:none}
.ft .c{width:42px;height:42px;border-radius:50%;background:#2aa1e6;display:grid;place-items:center;color:#fff;flex:none}.ft .c .i{width:22px;height:22px;fill:#fff}
.ft b{display:block;color:var(--tx);font-size:16px;direction:ltr;text-align:right;font-weight:600}
.cr{text-align:center;color:#56648a;font-size:11px;margin-top:18px;direction:ltr}
#toast{position:fixed;left:50%;bottom:28px;transform:translate(-50%,30px);background:#1a2650;border:1px solid var(--line);color:#fff;padding:9px 20px;border-radius:999px;font-size:13.5px;opacity:0;pointer-events:none;transition:.25s;z-index:9}#toast.show{opacity:1;transform:translate(-50%,0)}
@media(max-width:400px){.logo b{font-size:34px}.g3{gap:4px}.sc .v{font-size:13.5px}.lk{flex-wrap:wrap}.lk .box{flex-basis:100%}.lk .btn{flex:1}}"""

SUB_JS = r"""function T(m){var t=document.getElementById('toast');t.textContent=m;t.className='show';clearTimeout(window._t);window._t=setTimeout(function(){t.className=''},1800)}
function cp(id){var t=document.getElementById(id).textContent;
if(navigator.clipboard&&window.isSecureContext){navigator.clipboard.writeText(t).then(function(){T('کپی شد ✓')},fb)}else fb();
function fb(){var a=document.createElement('textarea');a.value=t;a.style.position='fixed';a.style.opacity=0;document.body.appendChild(a);a.select();try{document.execCommand('copy');T('کپی شد ✓')}catch(e){T('کپی نشد؛ دستی انتخاب کنید')}a.remove()}}
function qt(id){document.getElementById(id).classList.toggle('open')}"""

_APPS = [("Hiddify", "H", "#3b82f6,#6366f1", "hiddify://import/{u}#{n}"),
         ("sing-box", "S", "#14b8a6,#0ea5e9", "sing-box://import-remote-profile?url={q}#{n}"),
         ("v2rayNG", "V", "#8b5cf6,#d946ef", "v2rayng://install-sub?url={q}&name={n}"),
         ("Streisand", "St", "#f59e0b,#ef4444", "streisand://import/{u}"),
         ("NekoBox", "N", "#ec4899,#f43f5e", "sn://subscription?url={q}&name={n}")]


def sub_page(c, items, base):
    E = html.escape
    used = (c["up_bytes"] or 0) + (c["down_bytes"] or 0)
    lim = c["limit_bytes"] or 0
    st = client_state(c)
    tok = c["token"]
    sub = f"{base}/sub/{tok}"
    title = setting("sub_title", "WireGuard")
    tg = tg_id()
    active = st == "active"
    online = active and c["last_seen"] and now() - c["last_seen"] < 180

    # --- وضعیت ---
    if active:
        badge, bcls = "فعال", ""
        msg = ("شما در حال حاضر به اینترنت متصل هستید." if online
               else f"اشتراک شما فعال است · آخرین اتصال: {ago_fa(c['last_seen'])}")
    else:
        badge, bcls = {"expired": ("منقضی شده", "bad"), "limit": ("حجم تمام شده", "bad")}.get(st, ("غیرفعال", "bad"))
        msg = {"expired": "مدت اشتراک شما به پایان رسیده است.",
               "limit": "حجم اشتراک شما تمام شده است."}.get(st, "اشتراک شما توسط مدیر غیرفعال شده است.")
    # --- حجم ---
    pct = min(100.0, used * 100 / lim) if lim else 0.0
    bc = "inf" if not lim else ("w2" if pct >= 90 else "w1" if pct >= 70 else "")
    left = max(0, lim - used) if lim else 0
    ltr = lambda s: f"<span dir='ltr'>{E(s)}</span>"
    def cell(cid, k, v, wide=False):      # خانهٔ اطلاعات با قابلیت کپی با یک لمس
        return (f"<div class='cl{' cc' if wide else ''}' onclick=\"cp('{cid}')\"><small>{E(k)} · لمس برای کپی</small>"
                f"<b id='{cid}'>{E(str(v))}</b><i class='cpi'>{_ic('copy')}</i></div>")
    ic_s = lambda n: _ic(n).replace('class="i"', 'class="i" style="width:14px;height:14px;vertical-align:-2px"')
    # --- انقضا ---
    if c["expiry"]:
        jd, jt = jalali_str(c["expiry"])
        days = -(-(c["expiry"] - now()) // 86400)
        if days <= 0:
            dchip, dcls = "منقضی شده", "bad"
        else:
            dchip, dcls = f"<b>{days}</b> روز مانده", ("bad" if days <= 3 else "warn" if days <= 7 else "")
        ex_html = f"<h4>تاریخ انقضا</h4><p>{jd} · {jt}</p>"
    else:
        dchip, dcls, ex_html = "بدون محدودیت زمانی", "", "<h4>تاریخ انقضا</h4><p style='direction:rtl'>نامحدود</p>"

    h = ["<!doctype html><html lang='fa' dir='rtl'><head><meta charset='utf-8'>",
         "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'><meta name='theme-color' content='#070d1c'>",
         f"<title>{E(c['name'])} — Sepi-panel</title><style>{SUB_CSS}</style></head><body>{SUB_BG}<div class='w'>",
         f"<div class='logo'>{SUB_LOGO}<b>Sepi<span>-panel</span></b></div><div class='tag'>Fast &nbsp;·&nbsp; Stable &nbsp;·&nbsp; Secure</div>",
         "<div class='hi'>به پنل کاربری سپی خوش آمدید</div>",
         f"<div class='hs'>{E(title)} · اتصال پایدار، تجربه‌ای بهتر</div>",
         f"<div class='who'><span>{E(c['name'])}</span></div>",
         f"<section class='card'><div class='stt'><div class='sh {bcls}'>{_ic('shield' if active else 'shieldx')}</div>"
         f"<div><h3>وضعیت اتصال <span class='bd {bcls}'>{badge}</span></h3><p>{E(msg)}</p></div>"
         f"<div class='sig {'' if online else 'bad'}'>{_ic('signal')}</div></div></section>",
         f"<section class='card'><div class='ct'>{_ic('db')}<span>حجم مصرفی</span><em dir='ltr'>{pct:.0f}%</em></div>"
         f"<div class='bar {bc}'><i style='width:{(pct if lim else 100):.1f}%'></i></div>"
         "<div class='g3'>"
         f"<div class='sc'><div class='v'>{_ic('box')}<b>{ltr(fmt_b(lim)) if lim else 'نامحدود'}</b></div><small>کل حجم</small></div>"
         f"<div class='sc'><div class='v'>{_ic('db')}<b>{ltr(fmt_b(left)) if lim else '∞'}</b></div><small>باقی مانده</small></div>"
         f"<div class='sc'><div class='v'>{_ic('up')}<b>{ltr(fmt_b(used))}</b></div><small>مصرف شده</small></div></div>"
         f"<div class='ud'><span>{ic_s('down')} دانلود: <b>{ltr(fmt_b(c['down_bytes']))}</b></span>"
         f"<span>{ic_s('up')} آپلود: <b>{ltr(fmt_b(c['up_bytes']))}</b></span></div></section>",
         f"<section class='card'><div class='ex'><div class='exi'>{_ic('cal')}</div><div>{ex_html}</div>"
         f"<div class='dl {dcls}'>{_ic('clock')}<span>{dchip}</span></div></div></section>"]

    if not active:
        h.append("<section class='card off'><b>برای تمدید یا فعال‌سازی با پشتیبانی در ارتباط باشید.</b>"
                 + (f"<p>تلگرام: <span dir='ltr'>@{E(tg)}</span></p>" if tg else "") + "</section>")
    else:
        # --- لینک ساب ---
        qs = qr_data_uri(sub)
        nm = quote(f"{title}-{c['name']}")
        apps = "".join(
            f"<a class='app' href='{E(a[3].format(u=sub, q=quote(sub, safe=''), n=nm))}'><i style='background:linear-gradient(135deg,{a[2]})'>{a[1]}</i>{a[0]}</a>"
            for a in _APPS)
        h.append(f"<section class='card'><div class='ct'>{_ic('link')}<span>لینک اشتراک (Subscription)</span></div>"
                 f"<div class='lk'><div class='box' id='sl'>{E(sub)}</div>"
                 f"<button class='btn p' onclick=\"cp('sl')\">{_ic('copy')}کپی</button>"
                 + (f"<button class='btn sq' onclick=\"qt('qs')\" aria-label='QR'>{_ic('qr')}</button>" if qs else "")
                 + "</div>"
                 + (f"<div class='qrb' id='qs'><img src='{qs}' alt='QR'><small>با اپ کلاینت اسکن کنید تا اشتراک اضافه شود</small></div>" if qs else "")
                 + f"<div class='apps'>{apps}</div>"
                 f"<a class='btn p big' href='{E(_APPS[0][3].format(u=sub, q=quote(sub, safe=''), n=nm))}'>"
                 f"<span style='display:flex;gap:8px;align-items:center'>{_ic('plus')}افزودن به کلاینت</span>{_ic('arrow')}</a>"
                 "<div class='warnb' style='margin-top:12px'>این لینک را برای دیگران ارسال نکنید؛ با آن می‌توان از اشتراک شما استفاده کرد.</div></section>")
        # --- کانفیگ‌ها ---
        for i, (ci, ib) in enumerate(items):
            if is_vless(ib):
                xo = xcfg_of(ib)
                lk = vless_link(c, ci, ib)
                qv = qr_data_uri(lk)
                sn = _comma(xo["server_names"])[0] if xo["security"] == "reality" else (xo["sni"] or "")
                info = [("Server", endpoint_str(ib)), ("Transport", xo["transport"].upper()), ("Security", xo["security"].upper())]
                if sn:
                    info.append(("SNI", sn))
                if xo["flow"]:
                    info.append(("Flow", xo["flow"]))
                info.append(("UUID", ci["vuuid"]))
                cells = "".join(cell(f"v{i}_{j}", k, v, k == "UUID") for j, (k, v) in enumerate(info))
                h.append(f"<section class='card'><div class='ibh'><h3>{E(ib['name'])}</h3><span class='tg2'>VLESS</span>"
                         + (f"<small>{E(ib['remark'])}</small>" if ib["remark"] else "") + "</div>"
                         f"<div class='inf2'>{cells}</div><div class='acts'>"
                         f"<button class='btn p' onclick=\"cp('u{i}')\">{_ic('link')}کپی لینک کانفیگ</button>"
                         + (f"<button class='btn' onclick=\"qt('q{i}')\">{_ic('qr')}QR کد</button>" if qv else "")
                         + "</div>"
                         + (f"<div class='qrb' id='q{i}'><img src='{qv}' alt='QR'><small>در اپ v2rayNG / Hiddify / Streisand / Shadowrocket اسکن کنید</small></div>" if qv else "")
                         + f"<details><summary>{_ic('link')}لینک کانفیگ <span dir='ltr'>(vless://)</span></summary><pre id='u{i}'>{E(lk)}</pre></details></section>")
                continue
            if is_ovpn(ib):
                ov = ovpn_of(ib)
                cells = "".join(cell(f"o{i}_{j}", k, v) for j, (k, v) in
                                enumerate((("Server", endpoint_str(ib)), ("Transport", ov["transport"].upper()), ("Cipher", ov["cipher"]))))
                h.append(f"<section class='card'><div class='ibh'><h3>{E(ib['name'])}</h3><span class='tg2'>OpenVPN</span>"
                         + (f"<small>{E(ib['remark'])}</small>" if ib["remark"] else "") + "</div>"
                         f"<div class='inf2'>{cells}</div><div class='acts'>"
                         f"<a class='btn p' href='/sub/{tok}/{ib['id']}.ovpn'>{_ic('dl')}فایل کانفیگ <span dir='ltr'>(.ovpn)</span></a>"
                         f"<button class='btn' onclick=\"cp('cf{i}')\">{_ic('copy')}کپی کانفیگ</button></div>"
                         f"<details><summary>{_ic('code')}متن کامل کانفیگ</summary><pre id='cf{i}'>{E(build_conf(c, ci, ib))}</pre></details>"
                         "<div class='warnb'>فایل .ovpn را در اپ OpenVPN Connect (اندروید/iOS/ویندوز/مک) یا بخش OpenVPN مودم/روتر وارد کنید.</div></section>")
                continue
            if is_l2tp(ib):
                li = l2tp_info(c, ci, ib)
                cells = "".join(cell(f"l{i}{k}", lbl, li[k], True)
                                for k, lbl in (("server", "Server"), ("username", "Username"), ("password", "Password"), ("psk", "IPsec Pre-shared key")))
                allt = (f"Server: {li['server']}\nUsername: {li['username']}\nPassword: {li['password']}\nIPsec PSK: {li['psk']}")
                h.append(f"<section class='card'><div class='ibh'><h3>{E(ib['name'])}</h3><span class='tg2'>L2TP/IPsec</span>"
                         + (f"<small>{E(ib['remark'])}</small>" if ib["remark"] else "") + "</div>"
                         f"<div class='inf2'>{cells}</div>"
                         f"<div class='acts'><button class='btn p' onclick=\"cp('la{i}')\">{_ic('copy')}کپی همهٔ اطلاعات</button></div>"
                         f"<pre id='la{i}' style='display:none'>{E(allt)}</pre>"
                         "<div class='warnb'>در مودم/روتر یا گوشی، نوع VPN را «L2TP/IPsec PSK» انتخاب کنید و مقادیر بالا را وارد کنید. "
                         "اپ خاص لازم نیست.</div></section>")
                continue
            conf = build_conf(c, ci, ib)
            awg = is_awg(ib)
            uri = "" if awg else build_uri(c, ci, ib)
            addr, dns, mtu, ka, allowed = link_params(ci, ib)
            qc = qr_data_uri(conf)
            info = [("Endpoint", endpoint_str(ib)), ("IP", addr.split(",")[0].strip())]
            if dns:
                info.append(("DNS", dns))
            if mtu:
                info.append(("MTU", str(mtu)))
            cells = "".join(cell(f"w{i}_{j}", k, v) for j, (k, v) in enumerate(info))
            h.append(f"<section class='card'><div class='ibh'><h3>{E(ib['name'])}</h3>"
                     f"<span class='tg2'>{'AmneziaWG' if awg else 'WireGuard'}</span>"
                     + (f"<small>{E(ib['remark'])}</small>" if ib["remark"] else "") + "</div>"
                     f"<div class='inf2'>{cells}</div><div class='acts'>"
                     f"<a class='btn p' href='/sub/{tok}/{ib['id']}.conf'>{_ic('dl')}فایل کانفیگ <span dir='ltr'>(.conf)</span></a>"
                     f"<button class='btn' onclick=\"cp('cf{i}')\">{_ic('copy')}کپی کانفیگ</button>"
                     + (f"<button class='btn' onclick=\"cp('u{i}')\">{_ic('link')}کپی لینک کانفیگ</button>" if uri else "")
                     + (f"<button class='btn' onclick=\"qt('q{i}')\">{_ic('qr')}QR کد</button>" if qc else "")
                     + "</div>"
                     + (f"<div class='qrb' id='q{i}'><img src='{qc}' alt='QR'><small>در اپ WireGuard"
                        f"{' / AmneziaWG' if awg else ''} اسکن کنید</small></div>" if qc else "")
                     + (f"<details><summary>{_ic('link')}لینک کانفیگ <span dir='ltr'>(wireguard://)</span></summary><pre id='u{i}'>{E(uri)}</pre></details>" if uri else "")
                     + f"<details><summary>{_ic('code')}متن کامل کانفیگ</summary><pre id='cf{i}'>{E(conf)}</pre></details>"
                     + ("<div class='warnb'>این اینباند AmneziaWG است؛ فقط با اپ AmneziaWG (فایل .conf یا QR) کار می‌کند و در لینک ساب قرار نمی‌گیرد.</div>" if awg else "")
                     + "</section>")
        if not items:
            h.append("<section class='card off'>هنوز کانفیگی به اشتراک شما اضافه نشده است.</section>")

    if tg:
        h.append(f"<a class='ft' href='https://t.me/{E(tg)}' target='_blank' rel='noopener'><div class='c'>{_ic('tg')}</div>"
                 f"<div>کانال تلگرام ما را دنبال کنید<b>@{E(tg)}</b></div></a>")
    h.append(f"<div class='cr'>Sepi-panel</div></div><div id='toast'></div><script>{SUB_JS}</script></body></html>")
    return "".join(h)


@app.get("/sub/<token>")
def sub(token):
    c, items = sub_data(token)
    fmt = request.args.get("format", "")
    ua = request.headers.get("User-Agent", "")
    if not fmt and "text/html" in request.headers.get("Accept", "") and "Mozilla" in ua:
        fmt = "html"
    if fmt == "html":
        return Response(sub_page(c, items, base_url()), mimetype="text/html")
    if client_state(c) != "active":
        return Response("subscription inactive", status=403, mimetype="text/plain")
    only = request.args.get("inbound")
    if only:
        items = [(ci, ib) for ci, ib in items if str(ib["id"]) == only]
    title = setting("sub_title", "WireGuard")
    hdr = {
        "Subscription-Userinfo": f"upload={c['up_bytes']}; download={c['down_bytes']}; total={c['limit_bytes']}; expire={c['expiry']}",
        "Profile-Update-Interval": setting("update_interval", "12"),
        "Profile-Web-Page-Url": f"{base_url()}/sub/{c['token']}?format=html",
        "Profile-Title": "base64:" + base64.b64encode(f"{title} - {c['name']}".encode()).decode(),
        "Cache-Control": "no-store"}
    if fmt == "conf":
        txt = "\n".join(f"# ===== {ib['name']} =====\n{build_conf(c, ci, ib)}" for ci, ib in items)
        return Response(txt, mimetype="text/plain; charset=utf-8", headers=hdr)
    if fmt == "json":
        return Response(json.dumps([dict(inbound=ib["name"], awg=is_awg(ib), proto=ib["proto"],
                                         uri=(None if is_awg(ib) or is_l2tp(ib) or is_ovpn(ib) else build_uri(c, ci, ib)),
                                         l2tp=(l2tp_info(c, ci, ib) if is_l2tp(ib) else None), conf=build_conf(c, ci, ib))
                                    for ci, ib in items], ensure_ascii=False), mimetype="application/json", headers=hdr)
    uris = "\n".join(build_uri(c, ci, ib) for ci, ib in items if not is_awg(ib) and not is_l2tp(ib) and not is_ovpn(ib))
    if fmt == "raw":
        return Response(uris, mimetype="text/plain; charset=utf-8", headers=hdr)
    return Response(base64.b64encode(uris.encode()).decode(), mimetype="text/plain; charset=utf-8", headers=hdr)


def sub_one(token, iid):
    c, items = sub_data(token)
    if client_state(c) != "active":
        abort(403)
    for ci, ib in items:
        if ib["id"] == iid:
            if is_l2tp(ib):
                abort(404)      # L2TP فایل کانفیگ/QR ندارد
            return c, ci, ib
    abort(404)


@app.get("/sub/<token>/<int:iid>.conf")
@app.get("/sub/<token>/<int:iid>.ovpn")
def sub_conf(token, iid):
    c, ci, ib = sub_one(token, iid)
    fn = re.sub(r"[^A-Za-z0-9_.\-]", "_", f"{ib['name']}-{c['id']}") + (".ovpn" if is_ovpn(ib) else ".txt" if is_vless(ib) else ".conf")
    return Response(build_conf(c, ci, ib), mimetype="text/plain; charset=utf-8",
                    headers={"Content-Disposition": f'attachment; filename="{fn}"', "Cache-Control": "no-store"})


@app.get("/sub/<token>/<int:iid>.svg")
def sub_qr(token, iid):
    c, ci, ib = sub_one(token, iid)
    if is_ovpn(ib):
        abort(404)      # فایل OpenVPN برای QR بزرگ است
    return qr_svg(vless_link(c, ci, ib) if is_vless(ib) else build_conf(c, ci, ib))


@app.get("/sub/<token>/link.svg")
def sub_link_qr(token):
    sub_data(token)
    return qr_svg(f"{base_url()}/sub/{token}")


@app.get("/")
def index():
    return Response(INDEX_HTML, mimetype="text/html")


# ------------------------------ رابط کاربری ------------------------------
INDEX_HTML = r"""<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>SepiPanel</title><meta name="color-scheme" content="dark">
<style>
:root{color-scheme:dark;--bg:#0a1120;--side:#0c1424;--card:#101a2e;--card2:#16233d;--field:#15213a;--ink:#e8eef9;--mut:#8b9cb8;--line:#1b2840;--acc:#2563eb;--acc2:#1d4ed8;--ok:#22c55e;--warn:#f59e0b;--bad:#ef4444;--off:#64748b;--pur:#a855f7;--sky:#3b82f6}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:14.5px/1.7 Vazirmatn,IRANSans,Tahoma,"Segoe UI",sans-serif}
button,input,select,textarea{font:inherit;color:inherit}
a{color:#60a5fa}
::-webkit-scrollbar{width:8px;height:8px}::-webkit-scrollbar-thumb{background:#243453;border-radius:8px}
svg.ic{width:1em;height:1em;flex:none;stroke:currentColor;fill:none;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}
/* ---- layout ---- */
.shell{display:grid;grid-template-columns:250px minmax(0,1fr);min-height:100vh}
.side{background:var(--side);border-inline-end:1px solid var(--line);position:sticky;top:0;height:100vh;overflow:auto}
.brand{height:66px;display:flex;align-items:center;gap:12px;padding:0 20px;border-bottom:1px solid var(--line)}
.brand .lg{width:38px;height:38px;border-radius:11px;background:rgba(37,99,235,.16);color:var(--sky);display:grid;place-items:center;font-size:22px}
.brand b{font-size:17px;display:block;line-height:1.3}.brand small{display:block;color:var(--mut);font-size:11.5px;line-height:1.3}
.nav{padding:18px 12px;display:flex;flex-direction:column;gap:6px}
.nav button{display:flex;align-items:center;gap:12px;background:none;border:0;color:#cbd5e8;padding:11px 14px;border-radius:10px;cursor:pointer;text-align:start;font-size:14.5px;transition:.15s}
.nav button .ic{font-size:19px}
.nav button:hover{background:var(--card)}
.stp{display:flex;gap:10px;align-items:flex-start;padding:7px 0;font-size:14px}.stp i{font-style:normal;width:20px;text-align:center;color:var(--mut)}.stp.ok i{color:var(--ok)}.stp.err i{color:var(--bad)}.stp.warn i{color:var(--warn)}.stp small{display:block;color:var(--mut);font-size:12px;white-space:pre-wrap;word-break:break-word}
.nav button.on{background:var(--acc);color:#fff;box-shadow:0 6px 20px rgba(37,99,235,.35)}
.main{min-width:0}
.tb{height:66px;display:flex;align-items:center;justify-content:space-between;gap:10px;padding:0 24px;border-bottom:1px solid var(--line);background:var(--side)}
.usr{display:flex;align-items:center;gap:10px}.usr b{display:block;font-size:14px;line-height:1.3}.usr small{display:flex;align-items:center;gap:5px;color:var(--mut);font-size:11.5px;line-height:1.3}
.usr small i{width:7px;height:7px;border-radius:50%;background:var(--ok)}
.av{width:40px;height:40px;border-radius:50%;background:linear-gradient(135deg,#1e3a6e,#2563eb);display:grid;place-items:center;font-size:20px;color:#dbe7ff}
.sm{font-size:12px}
.wrap{max-width:1080px;margin:0 auto;padding:30px 24px 50px}
h1.pt{margin:0 0 2px;font-size:26px;line-height:1.5}p.ps{margin:0 0 24px;color:var(--mut);font-size:13.5px}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:16px;margin-bottom:22px}
.st{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:18px 20px}
.st .si{font-size:30px;display:block;line-height:1;margin-bottom:14px}
.st span.l{display:block;color:var(--mut);font-size:13.5px}.st b{font-size:26px;line-height:1.5}
.si.g{color:var(--ok)}.si.p{color:var(--pur)}.si.bl{color:var(--sky)}.si.o{color:var(--warn)}
.bar2{display:flex;justify-content:space-between;align-items:center;margin-bottom:14px;gap:8px;flex-wrap:wrap}
/* ---- buttons ---- */
button.p,.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;background:var(--acc);color:#fff;border:0;border-radius:9px;padding:9px 18px;cursor:pointer;text-decoration:none;font-size:14px;box-shadow:0 4px 14px rgba(37,99,235,.28);transition:.15s}
button.p:hover,.btn:hover{background:var(--acc2)}
button.s{background:var(--card2);border:1px solid var(--line);border-radius:8px;padding:5px 12px;cursor:pointer;font-size:13px;color:#d3def0;transition:.15s}
button.s:hover{border-color:var(--sky);color:#fff}button.s.d{color:#f87171}button.s.d:hover{border-color:var(--bad)}
button:disabled{opacity:.5;cursor:not-allowed}
/* ---- cards ---- */
.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:18px 20px;margin-bottom:14px}
.card.up{border-inline-start:3px solid var(--acc)}
.ch{display:flex;align-items:center;gap:10px;font-weight:700;font-size:15px;margin-bottom:18px}.ch .ic{font-size:18px;color:var(--mut)}
.sgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,380px),1fr));gap:16px;align-items:start}.sgrid .card{margin:0}
.row{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap}
.card h3{margin:0;font-size:16px}.card h3 small{color:var(--mut);font-weight:400;margin-inline-start:6px;font-size:12.5px}
.meta{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:3px 14px;margin:10px 0;color:var(--mut);font-size:13px}
.meta b{color:var(--ink);font-weight:600;direction:ltr;unicode-bidi:embed}
.acts{display:flex;gap:8px;flex-wrap:wrap;margin-top:10px}
.b{font-size:12px;padding:1px 11px;border-radius:12px;color:#cbd5e1;background:rgba(100,116,139,.22);border:1px solid rgba(100,116,139,.35)}
.b.ok{color:#4ade80;background:rgba(34,197,94,.13);border-color:rgba(34,197,94,.35)}
.b.warn{color:#fbbf24;background:rgba(245,158,11,.13);border-color:rgba(245,158,11,.35)}
.b.bad{color:#f87171;background:rgba(239,68,68,.13);border-color:rgba(239,68,68,.35)}
.pg{height:6px;background:#1b2a47;border-radius:3px;overflow:hidden;margin:8px 0}.pg i{display:block;height:100%;background:linear-gradient(90deg,#2563eb,#60a5fa);border-radius:3px}
.tag{display:inline-block;background:var(--card2);border:1px solid var(--line);border-radius:6px;padding:0 8px;font-size:12.5px;margin:0 0 3px 4px;direction:ltr;color:#c3d1ea}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--off);margin-inline-end:7px}.dot.on{background:var(--ok);box-shadow:0 0 0 3px rgba(34,197,94,.18)}
/* ---- forms ---- */
.fg{margin-bottom:12px}.fg label{display:block;font-size:13px;color:var(--mut);margin-bottom:4px}.fg small{display:block;color:var(--mut);font-size:12px;margin-top:3px;opacity:.85}
.fg input:not([type=checkbox]),.fg select,.fg textarea{width:100%;padding:9px 12px;border:1px solid var(--line);border-radius:9px;background:var(--field);color:var(--ink);direction:ltr;text-align:left;outline:0;transition:.15s}
.fg input:focus,.fg select:focus,.fg textarea:focus{border-color:var(--sky);box-shadow:0 0 0 3px rgba(59,130,246,.18)}
.fg input::placeholder,.fg textarea::placeholder{color:#55688a}
.fg select{appearance:none;-webkit-appearance:none;background-image:url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='12' height='8' viewBox='0 0 12 8'><path d='M1 1l5 5 5-5' fill='none' stroke='%238b9cb8' stroke-width='1.6' stroke-linecap='round'/></svg>");background-repeat:no-repeat;background-position:left 12px center;padding-left:32px}
.fg select option{background:#101a2e}
.fg textarea{min-height:62px;font-family:ui-monospace,Consolas,monospace;font-size:13px}
input[type=date]{color-scheme:dark}
input[type=checkbox]{appearance:none;-webkit-appearance:none;flex:none;width:42px;height:24px;border-radius:12px;background:#33415a;position:relative;cursor:pointer;transition:.2s;margin:0}
input[type=checkbox]::after{content:"";position:absolute;top:3px;inset-inline-start:21px;width:18px;height:18px;border-radius:50%;background:#e2e8f0;transition:.2s}
input[type=checkbox]:checked{background:var(--acc)}input[type=checkbox]:checked::after{inset-inline-start:3px;background:#fff}
.chk{display:flex!important;flex-direction:row-reverse;justify-content:space-between;align-items:center;gap:12px;color:var(--ink)!important;font-size:14px!important;margin-bottom:0!important;cursor:pointer}
.lk{border:1px solid var(--line);background:#0d172a;border-radius:11px;padding:10px 12px;margin-bottom:10px}
.lk details{margin-top:8px}.lk summary{cursor:pointer;color:var(--mut);font-size:13px}
.g2{display:grid;grid-template-columns:1fr 1fr;gap:0 12px;margin-top:8px}
pre.cf{direction:ltr;text-align:left;background:#0a1322;border:1px solid var(--line);color:#cfe0ff;border-radius:10px;padding:12px;overflow:auto;font:12.5px/1.5 ui-monospace,Consolas,monospace;white-space:pre-wrap;word-break:break-all}
/* ---- modal / toast / login ---- */
.ov{position:fixed;inset:0;background:rgba(3,8,18,.72);backdrop-filter:blur(4px);display:flex;align-items:flex-start;justify-content:center;overflow:auto;padding:24px 10px;z-index:9}
.md{background:var(--card);border:1px solid var(--line);border-radius:16px;max-width:660px;width:100%;padding:20px 22px;box-shadow:0 24px 60px rgba(0,0,0,.5)}
.md h2{margin:0 0 14px;font-size:18px}.md h4{margin:18px 0 8px;color:#60a5fa;font-size:14px;border-bottom:1px solid var(--line);padding-bottom:5px}
.mfoot{display:flex;gap:8px;justify-content:flex-end;margin-top:16px}
#toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);z-index:20;display:flex;flex-direction:column;gap:6px;align-items:center}
#toast div{background:#1a2742;border:1px solid #2a3b5e;color:#fff;padding:9px 16px;border-radius:10px;max-width:90vw;box-shadow:0 8px 24px rgba(0,0,0,.4)}#toast div.e{background:#3a1519;border-color:#7f1d1d}
.login{max-width:360px;margin:12vh auto;background:var(--card);border:1px solid var(--line);border-radius:16px;padding:26px;box-shadow:0 24px 60px rgba(0,0,0,.4)}
.login .lg2{width:52px;height:52px;border-radius:14px;background:rgba(37,99,235,.16);color:var(--sky);display:grid;place-items:center;font-size:28px;margin:0 auto 12px}
.login h1{margin:0 0 18px;font-size:20px;text-align:center}.login button.p{width:100%}
.empty{color:var(--mut);text-align:center;padding:36px 0;background:var(--card);border:1px dashed var(--line);border-radius:14px}
.mut{color:var(--mut)}img.qr{width:210px;max-width:100%;display:block;margin:10px auto;background:#fff;padding:10px;border-radius:12px}
.wrap.nosta .stats{display:none}
.sg4{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:14px;margin-bottom:14px}
.sg2{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,400px),1fr));gap:14px;margin-bottom:14px}
.sg2 .card{margin:0}
.gc{display:flex;align-items:center;gap:14px;background:var(--card);border:1px solid var(--line);border-radius:14px;padding:14px 16px;min-width:0}
.gr{width:88px;height:88px;flex:none}.gt{fill:var(--ink);font:700 21px Tahoma,sans-serif}
.gc>div{min-width:0}.gc .gl{display:block;color:var(--mut);font-size:12.5px}.gc b{display:block;font-size:15px;direction:ltr;text-align:right}.gc small{display:block;color:var(--mut);font-size:12px;line-height:1.5}
.ch2{position:relative;margin:8px 0}.ch2 svg{width:100%;height:150px;display:block}.ch2 .mx{position:absolute;top:0;left:2px;font-size:11px;color:var(--mut)}
.seg{display:inline-flex;background:var(--field);border:1px solid var(--line);border-radius:9px;padding:2px}.seg button{background:none;border:0;padding:3px 12px;border-radius:7px;cursor:pointer;font-size:13px;color:var(--mut)}.seg button.on{background:var(--acc);color:#fff}
.pills{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0 2px}.pl{font-size:13px;padding:2px 12px;border-radius:12px;direction:ltr}.pl.a{background:rgba(56,189,248,.14);color:#7dd3fc}.pl.b2{background:rgba(167,139,250,.14);color:#c4b5fd}
.trio{display:grid;grid-template-columns:repeat(3,1fr);gap:10px;border-top:1px solid var(--line);padding-top:10px;margin-top:6px}.trio small{display:block;color:var(--mut);font-size:12px}.trio b{font-size:15px;direction:ltr;display:block;text-align:right}
.split{display:flex;height:8px;border-radius:5px;overflow:hidden;background:#1b2a47;margin:8px 0}.split i{display:block;height:100%}
.kv{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px}.kv div{background:var(--field);border:1px solid var(--line);border-radius:10px;padding:8px 12px}.kv small{display:block;color:var(--mut);font-size:12px}.kv b{font-size:15px;direction:ltr;display:block;text-align:right}
.ipl{display:flex;flex-wrap:wrap;gap:8px}.ipl span{background:var(--field);border:1px solid var(--line);border-radius:8px;padding:2px 10px;direction:ltr;font:12.5px ui-monospace,Consolas,monospace;transition:filter .2s}.ipl.hid span{filter:blur(6px);user-select:none}
.tl{display:flex;gap:8px;align-items:center;flex-wrap:wrap;flex:1;min-width:0}
.srch{flex:1;min-width:150px;max-width:340px;direction:rtl;text-align:right}
.cl{background:var(--card);border:1px solid var(--line);border-radius:12px;overflow:hidden}
.cr2{display:grid;grid-template-columns:minmax(0,1.5fr) minmax(0,1fr) minmax(0,1fr) auto;gap:6px 16px;align-items:center;padding:9px 14px;border-bottom:1px solid var(--line);border-inline-start:3px solid transparent;transition:background .15s}
.cr2:last-child{border-bottom:0}.cr2:hover{background:rgba(59,130,246,.05)}.cr2.on{border-inline-start-color:var(--acc)}
.cr2 .c1 b{display:flex;align-items:center;font-size:14px;line-height:1.5;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.cr2 small{display:block;color:var(--mut);font-size:12px;line-height:1.5;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.cr2 .nm{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0}
.own{flex:none;margin-inline-start:8px;font-size:11.5px;font-weight:400;padding:0 9px;border-radius:12px;color:#d8b4fe;background:rgba(168,85,247,.15);border:1px solid rgba(168,85,247,.4)}
.cr2 .tg{margin-top:2px;line-height:1.3}.cr2 .tag{font-size:11.5px;padding:0 6px;margin:0 0 2px 3px}
.cr2 .c2 .pg{margin:0 0 3px}.cr2 .c3{display:flex;flex-direction:column;align-items:flex-start;gap:2px}
.cr2 .acts{margin:0;gap:5px;flex-wrap:nowrap}.cr2 .acts .s{padding:3px 9px;font-size:12px;white-space:nowrap}
.pgr{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;margin-top:12px}
.pgb{display:flex;gap:5px;flex-wrap:wrap;align-items:center}.pgb .s{min-width:32px;padding:4px 10px}.pgb .s.cur{background:var(--acc);border-color:var(--acc);color:#fff}
@media(max-width:1000px){.cr2{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}.cr2 .c4{grid-column:1/-1}.cr2 .acts{flex-wrap:wrap}}
.fsel{background:var(--field);border:1px solid var(--line);border-radius:9px;padding:8px 12px;color:var(--ink);outline:0;max-width:60vw}
:focus-visible{outline:2px solid var(--sky);outline-offset:2px}
@media(max-width:860px){
 .shell{grid-template-columns:1fr}.side{position:static;height:auto;border-inline-end:0;border-bottom:1px solid var(--line)}
 .brand{height:56px}.nav{flex-direction:row;overflow-x:auto;padding:8px 10px}.nav button{white-space:nowrap;padding:9px 13px}
 .tb{height:56px;padding:0 14px}.wrap{padding:20px 14px 40px}h1.pt{font-size:22px}}
@media(max-width:520px){.g2{grid-template-columns:1fr}}
.dk h3{margin:24px 0 8px;font-size:16px}.dk p,.dk li{line-height:1.9;font-size:14px}.dk ol,.dk ul{padding-right:22px;margin:6px 0}
.dk code{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12.5px}.dk p code,.dk li code,.dk td code{background:rgba(130,160,255,.13);padding:1px 6px;border-radius:5px;direction:ltr;unicode-bidi:embed}
.dk .cb{position:relative;margin:8px 0}.dk pre{direction:ltr;text-align:left;background:#050a16;border:1px solid var(--line);border-radius:10px;padding:12px;overflow:auto;line-height:1.6;margin:0}.dk .cp{position:absolute;top:6px;left:6px;z-index:1;opacity:.85}
.dk .ep{border:1px solid var(--line);border-radius:12px;padding:12px 14px;margin:12px 0;background:var(--card)}.dk .m{display:inline-block;min-width:54px;text-align:center;font-weight:700;border-radius:6px;padding:1px 8px;margin-left:8px;font-size:12px;direction:ltr}
.dk .m.get{background:rgba(52,211,153,.18);color:var(--ok)}.dk .m.post{background:rgba(79,124,255,.2);color:#8fb0ff}.dk .m.del{background:rgba(248,113,113,.18);color:var(--bad)}
.dk table{width:100%;border-collapse:collapse;font-size:13px;margin:6px 0}.dk td,.dk th{border-bottom:1px solid var(--line);padding:6px 8px;text-align:right;vertical-align:top}.dk th{color:var(--mut);font-weight:600}
</style></head><body><div id="app"></div><div id="toast"></div>
<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmtB=n=>{n=+n||0;const u=['B','KB','MB','GB','TB'];let i=0;while(n>=1024&&i<4){n/=1024;i++}return n.toFixed(i?2:0)+' '+u[i]};
const fmtD=t=>t?new Date(t*1000).toLocaleDateString('fa-IR'):'نامحدود';
const ago=t=>{if(!t)return 'هرگز';const s=Math.max(0,S.server.now-t+((Date.now()/1000)-S.local));if(s<90)return 'همین الان';if(s<3600)return Math.floor(s/60)+' دقیقه پیش';if(s<86400)return Math.floor(s/3600)+' ساعت پیش';return Math.floor(s/86400)+' روز پیش'};
const BASE=location.pathname.replace(/\/+$/,'');
let S=null,TAB='cli',CF='all';
function toast(m,e){const d=document.createElement('div');d.textContent=m;if(e)d.className='e';$('#toast').appendChild(d);setTimeout(()=>d.remove(),e?7000:2500)}
async function api(p,m='GET',b){const r=await fetch(BASE+'/api'+p,{method:m,headers:{'Content-Type':'application/json','X-Requested-With':'sepipanel'},body:b?JSON.stringify(b):undefined});
 if(r.status==401){showLogin();throw new Error('نیاز به ورود')}
 const d=await r.json().catch(()=>({}));if(!r.ok)throw new Error(d.error||r.statusText);return d}
async function act(fn,msg){try{const r=await fn();if(r&&r.warn)toast(r.warn,1);else if(msg)toast(msg);await load();return true}catch(e){toast(e.message,1);return false}}
function copy(t){if(navigator.clipboard&&isSecureContext)navigator.clipboard.writeText(t);else{const a=document.createElement('textarea');a.value=t;document.body.appendChild(a);a.select();document.execCommand('copy');a.remove()}toast('کپی شد')}
const IC={
 api:'<path d="m16 18 6-6-6-6M8 6l-6 6 6 6"/>',
 tun:'<path d="M3 20V11a9 9 0 0 1 18 0v9"/><path d="M7 20v-8a5 5 0 0 1 10 0v8M3 20h18"/>',
 users:'<path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M22 21v-2a4 4 0 0 0-3-3.87M16 3.13a4 4 0 0 1 0 7.75"/>',
 layers:'<path d="m12 2 10 5-10 5L2 7z"/><path d="m2 17 10 5 10-5M2 12l10 5 10-5"/>',
 settings:'<path d="M12.22 2h-.44a2 2 0 0 0-2 2v.18a2 2 0 0 1-1 1.73l-.43.25a2 2 0 0 1-2 0l-.15-.08a2 2 0 0 0-2.73.73l-.22.38a2 2 0 0 0 .73 2.73l.15.1a2 2 0 0 1 1 1.72v.51a2 2 0 0 1-1 1.74l-.15.09a2 2 0 0 0-.73 2.73l.22.38a2 2 0 0 0 2.73.73l.15-.08a2 2 0 0 1 2 0l.43.25a2 2 0 0 1 1 1.73V20a2 2 0 0 0 2 2h.44a2 2 0 0 0 2-2v-.18a2 2 0 0 1 1-1.73l.43-.25a2 2 0 0 1 2 0l.15.08a2 2 0 0 0 2.73-.73l.22-.39a2 2 0 0 0-.73-2.73l-.15-.08a2 2 0 0 1-1-1.74v-.5a2 2 0 0 1 1-1.74l.15-.09a2 2 0 0 0 .73-2.73l-.22-.38a2 2 0 0 0-2.73-.73l-.15.08a2 2 0 0 1-2 0l-.43-.25a2 2 0 0 1-1-1.73V4a2 2 0 0 0-2-2z"/><circle cx="12" cy="12" r="3"/>',
 logout:'<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4M16 17l5-5-5-5M21 12H9"/>',
 server:'<rect x="2" y="2" width="20" height="8" rx="2"/><rect x="2" y="14" width="20" height="8" rx="2"/><path d="M6 6h.01M6 18h.01"/>',
 pulse:'<path d="M22 12h-4l-3 9L9 3l-3 9H2"/>',
 db:'<ellipse cx="12" cy="5" rx="9" ry="3"/><path d="M3 5v14c0 1.7 4 3 9 3s9-1.3 9-3V5M3 12c0 1.7 4 3 9 3s9-1.3 9-3"/>',
 shield:'<path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/>',
 globe:'<circle cx="12" cy="12" r="10"/><path d="M2 12h20M12 2a15 15 0 0 1 0 20 15 15 0 0 1 0-20z"/>',
 link:'<path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71"/>',
 info:'<circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/>',
 save:'<path d="M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2z"/><path d="M17 21v-8H7v8M7 3v5h8"/>',
 user:'<path d="M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2"/><circle cx="12" cy="7" r="4"/>',
 admin:'<path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/><circle cx="12" cy="10" r="2.2"/><path d="M8.2 16.2c.8-1.6 2.1-2.2 3.8-2.2s3 .6 3.8 2.2"/>'};
const ic=n=>`<svg class="ic" viewBox="0 0 24 24" aria-hidden="true">${IC[n]||''}</svg>`;
function showLogin(){staStop();$('#app').innerHTML=`<div class="login"><div class="lg2">${ic('shield')}</div><h1>ورود به SepiPanel</h1><div class="fg"><label>نام کاربری</label><input id="lu" autocomplete="username"></div>
<div class="fg"><label>رمز عبور</label><input id="lp" type="password" autocomplete="current-password"></div><button class="p" onclick="doLogin()">ورود</button></div>`;
 $('#lp').onkeydown=e=>{if(e.key==='Enter')doLogin()}}
async function doLogin(){try{await api('/login','POST',{u:$('#lu').value,p:$('#lp').value});load()}catch(e){toast(e.message,1)}}
async function load(){try{S=await api('/state');S.local=Date.now()/1000;render()}catch(e){if(e.message!=='نیاز به ورود')toast(e.message,1)}}
const STL={active:['فعال','ok'],disabled:['غیرفعال',''],expired:['منقضی','bad'],limit:['اتمام حجم','bad'],admin:['غیرفعال (ادمین)','bad'],key:['غیرفعال (سقف کلید)','bad']};
const NAV=[['sta','وضعیت','pulse','وضعیت لحظه‌ای سرور و وایرگارد: CPU، رم، دیسک، سرعت شبکه و اتصال‌ها.'],['cli','کلاینت‌ها','users','هر کلاینت می‌تواند عضو چند اینباند باشد.'],['inb','اینباندها','layers','هر اینباند یک اینترفیس وایرگارد است.'],['nod','نودها','server','نود = سرور جداگانه با لوکیشن خودش. اینباندهای VLESS روی هر نود ساخته می‌شوند و همه در یک لینک ساب جمع می‌شوند.'],['adm','ادمین‌ها','admin','ادمین‌ها فقط کلاینت می‌سازند و کلاینت‌های خودشان را مدیریت می‌کنند؛ برای هرکدام حجم و زمان تعیین کنید.'],['set','تنظیمات','settings','دامنه، پورت، حساب مدیر و تنظیمات اشتراک پنل را از اینجا مدیریت کنید.']];
NAV.push(['api','API و مستندات','api','اتصال پنل به ربات تلگرام یا سایت برای فروش خودکار: کلید API بسازید و طبق مستندات زیر کلاینت بسازید، تمدید کنید و لینک اشتراک را تحویل بدهید.']);
NAV.push(['tun','تانل','tun','ساخت و مدیریت تانل BackPack بین سرور ایران و خارج؛ هر سمت می‌تواند همین سرور، یکی از نودها یا سرور دیگری با SSH باشد.']);
const NAV_A=[['cli','کلاینت‌ها','users','کلاینت‌های خودتان را اینجا بسازید و مدیریت کنید.'],['api','API و مستندات','api','کلید API خودتان را بسازید، سقف حجم و زمانش را کم و زیاد کنید و ربات یا سایتتان را وصل کنید؛ مصرف فقط از کلاینت‌هایی که با همان کلید ساخته می‌شوند کم می‌شود.']];
const isA=()=>S&&S.role==='admin';
function render(){
 const NV=isA()?NAV_A:NAV;if(!NV.find(n=>n[0]==TAB))TAB='cli';
 const on=S.clients.filter(c=>c.online).length,tot=S.clients.reduce((a,c)=>a+c.up_bytes+c.down_bytes,0),cur=NV.find(n=>n[0]==TAB);
 $('#app').innerHTML=`<div class="shell"><aside class="side"><div class="brand"><span class="lg">${ic('shield')}</span><div><b>SepiPanel</b><small>مدیریت WireGuard</small></div></div>
 <nav class="nav">${NV.map(([k,l,i])=>`<button class="${TAB==k?'on':''}" onclick="TAB='${k}';render()">${ic(i)}<span>${l}</span></button>`).join('')}<button onclick="logout()">${ic('logout')}<span>خروج</span></button></nav></aside>
 <div class="main"><header class="tb"><span class="mut sm">${isA()?'پنل ادمین':esc(S.server.wg||'wireguard-tools یافت نشد!')}</span><div class="usr"><span class="av">${ic('user')}</span><div><b>${esc(S.panel.user)}</b><small><i></i>آنلاین</small></div></div></header>
 <div class="wrap${TAB=='sta'?' nosta':''}"><h1 class="pt">${cur[1]}</h1><p class="ps">${cur[3]}</p>
 <div class="stats"><div class="st"><span class="si g">${ic('server')}</span><span class="l">اینباند فعال</span><b>${isA()?S.inbounds.length:S.inbounds.filter(i=>i.up).length+' / '+S.inbounds.length}</b></div>
 <div class="st"><span class="si p">${ic('users')}</span><span class="l">کلاینت‌ها</span><b>${S.clients.length}</b></div>
 <div class="st"><span class="si bl">${ic('pulse')}</span><span class="l">آنلاین</span><b>${on}</b></div>
 <div class="st"><span class="si o">${ic('db')}</span><span class="l">مصرف کل</span><b>${fmtB(tot)}</b></div></div>
 ${TAB=='inb'?inbHTML():TAB=='cli'?cliHTML():TAB=='adm'?admHTML():TAB=='sta'?staHTML():TAB=='api'?apiHTML():TAB=='tun'?tunHTML():TAB=='nod'?nodHTML():setHTML()}</div></div></div>`;if(TAB==='sta')staStart();else staStop()}
async function logout(){await api('/logout','POST');showLogin()}
/* ---------- API و مستندات ---------- */
let APK=null,APD=null;
const apiDt=t=>t?new Date(t*1000).toLocaleString('fa-IR'):'هرگز';
const KST={active:['فعال','ok'],disabled:['غیرفعال','bad'],expired:['منقضی','bad'],limit:['اتمام حجم','bad']};
function apiHTML(){setTimeout(apiLoad,0);return `<div class="bar2"><span class="mut sm">کلید API به ربات تلگرام یا سایت شما اجازه می‌دهد کلاینت بسازد، تمدید کند و لینک اشتراک را تحویل بدهد.</span><button class="p" onclick="apiNew()">+ کلید جدید</button></div><div id="apiBox">${apiBody()}</div><div id="apiDoc" class="dk">${APD||'<div class="empty">در حال بارگذاری مستندات…</div>'}</div>`}
async function apiLoad(){if(TAB!=='api')return;try{APK=await api('/apikeys')}catch(e){toast(e.message,1);return}const b=$('#apiBox');if(b)b.innerHTML=apiBody();
 if(!APD){try{APD=(await api('/docs')).html}catch(e){toast(e.message,1);return}const d=$('#apiDoc');if(d)d.innerHTML=APD}}
function apiBody(){if(!APK)return '';return APK.keys.map(k=>{const st=KST[k.state]||[k.state,''],pct=k.limit_bytes?Math.min(100,k.used_bytes*100/k.limit_bytes):0;
 return `<article class="card ${k.state=='active'?'up':''}"><div class="row"><h3>${esc(k.name)}<small dir="ltr">${esc(k.prefix)}…</small></h3><span class="b ${st[1]}">${st[0]}</span></div>${k.limit_bytes?`<div class="pg"><i style="width:${pct}%"></i></div>`:''}
 <div class="meta">${isA()?'':`<span>حساب: <b>${esc(k.account)}</b></span>`}<span>کلاینت‌های ساخته‌شده: <b>${k.clients}</b></span><span>مصرف: <b>${fmtB(k.used_bytes)}</b> / <b>${k.limit_bytes?fmtB(k.limit_bytes):'نامحدود'}</b></span><span>باقی‌مانده: <b>${k.limit_bytes?fmtB(Math.max(0,k.limit_bytes-k.used_bytes)):'نامحدود'}</b></span><span>انقضا: <b style="direction:rtl">${k.expiry?apiDt(k.expiry):'بدون انقضا'}</b></span><span>آخرین استفاده: <b>${apiDt(k.last_used)}</b></span></div>
 <div class="acts"><button class="s" onclick="apiEdit(${k.id})">ویرایش سهمیه</button><button class="s" onclick="apiTog(${k.id})">${k.enabled?'غیرفعال‌سازی':'فعال‌سازی'}</button><button class="s d" onclick="apiDel(${k.id})">حذف</button></div></article>`}).join('')||'<div class="empty">هنوز کلیدی نساخته‌اید.</div>'}
function apiNew(){const ads=isA()?[]:(S.admins||[]).filter(a=>a.enabled);
 const m=modal(`<h2>کلید API جدید</h2><div id="apF"><div class="g2"><div class="fg"><label>نام کلید (مثلاً ربات تلگرام)</label><input id="ap_nm"></div>
 ${isA()?'':`<div class="fg"><label>این کلید با کدام حساب کار کند؟</label><select id="ap_ad"><option value="0">مدیر اصلی — دسترسی کامل به همه‌ی کلاینت‌ها</option>${ads.map(a=>`<option value="${a.id}">ادمین: ${esc(a.username)} — فقط کلاینت‌های خودش</option>`).join('')}</select></div>`}
 <div class="fg"><label>سقف حجم این کلید (گیگ، 0 = نامحدود)</label><input id="ap_gb" dir="ltr" value="0"></div><div class="fg"><label>اعتبار کلید (روز، 0 = بدون انقضا)</label><input id="ap_dy" dir="ltr" value="0"></div></div>
 <small class="mut">مصرف این سقف فقط از کلاینت‌هایی کم می‌شود که با همین کلید ساخته شوند. بعداً هر وقت خواستید سقف را کم و زیاد کنید.${isA()?'':' برای ربات فروش بهتر است یک ادمین جدا با سقف حجم و زمان بسازید و کلید را به او وصل کنید.'}</small></div>
 <div class="mfoot"><button class="s" id="ap_c">بستن</button><button class="p" id="ap_s">ساخت کلید</button></div>`);
 m.querySelector('#ap_c').onclick=()=>{m.remove();apiLoad()};
 m.querySelector('#ap_s').onclick=async()=>{const g=i=>m.querySelector('#'+i);try{const r=await api('/apikeys','POST',{name:g('ap_nm').value.trim(),admin_id:g('ap_ad')?g('ap_ad').value:0,limit_gb:g('ap_gb').value,days:g('ap_dy').value});
  g('apF').innerHTML=`<div class="b ok">کلید ساخته شد. همین حالا کپی کنید؛ دوباره نمایش داده نمی‌شود.</div><pre dir="ltr" style="user-select:all;word-break:break-all;white-space:pre-wrap;margin:10px 0;padding:10px;background:#050a16;border-radius:8px">${esc(r.key)}</pre><button class="s" onclick="copy('${esc(r.key)}')">کپی کلید</button>`;g('ap_s').remove()}catch(e){toast(e.message,1)}}}
function apiEdit(id){const k=APK.keys.find(x=>x.id==id);if(!k)return;
 const m=modal(`<h2>سهمیه‌ی کلید «${esc(k.name)}»</h2><div class="g2"><div class="fg"><label>نام کلید</label><input id="ae_nm" value="${esc(k.name)}"></div>
 <div class="fg"><label>سقف حجم (گیگ، 0 = نامحدود)</label><input id="ae_gb" dir="ltr" value="${k.limit_bytes?+(k.limit_bytes/1073741824).toFixed(2):0}"><small>مصرف فعلی: ${fmtB(k.used_bytes)}</small></div>
 <div class="fg"><label>اضافه / کم کردن حجم (گیگ، منفی = کم)</label><input id="ae_ag" dir="ltr" placeholder="مثلاً 50 یا -10"></div>
 <div class="fg"><label>اضافه / کم کردن روز (منفی = کم)</label><input id="ae_ad" dir="ltr" placeholder="مثلاً 30 یا -5"><small>انقضای فعلی: ${k.expiry?apiDt(k.expiry):'بدون انقضا'}</small></div></div>
 <label class="chk"><span>مصرف کلید صفر شود</span><input type="checkbox" id="ae_ru"></label>
 <small class="mut" style="display:block;margin-top:8px">اگر هم «سقف حجم» و هم «اضافه/کم» را پر کنید، اول سقف جدید گذاشته و بعد تغییر اعمال می‌شود. با تمام شدن سقف، کلاینت‌های ساخته‌شده با این کلید قطع می‌شوند و با افزایش سقف خودکار وصل می‌شوند.</small>
 <div class="mfoot"><button class="s" id="ae_c">بستن</button><button class="p" id="ae_s">ذخیره</button></div>`);
 m.querySelector('#ae_c').onclick=()=>m.remove();
 m.querySelector('#ae_s').onclick=async()=>{const g=i=>m.querySelector('#'+i).value.trim();const b={name:g('ae_nm'),limit_gb:g('ae_gb'),reset_usage:m.querySelector('#ae_ru').checked};
  if(g('ae_ag'))b.add_gb=g('ae_ag');if(g('ae_ad'))b.add_days=g('ae_ad');
  try{const r=await api('/apikeys/'+id,'PUT',b);toast(r.warn||'ذخیره شد',!!r.warn);m.remove();apiLoad()}catch(e){toast(e.message,1)}}}
async function apiTog(id){try{await api('/apikeys/'+id+'/toggle','POST');apiLoad()}catch(e){toast(e.message,1)}}
async function apiDel(id){if(!confirm('این کلید حذف شود؟ هر ربات یا سایتی که از آن استفاده می‌کند از کار می‌افتد؛ کلاینت‌های ساخته‌شده می‌مانند.'))return;try{await api('/apikeys/'+id,'DELETE');apiLoad()}catch(e){toast(e.message,1)}}
/* ---------- تانل (BackPack) ---------- */
let TUN=null,TUNT=null;
const TPH={online:['آنلاین','ok'],ready:['برقرار شد','warn'],down:['قطع','bad']};
function tunHTML(){setTimeout(tunLoad,0);return `<div class="bar2"><span class="mut sm">تانل بین سرور ایران و خارج با BackPack؛ هر سمت می‌تواند همین سرور یا یکی از نودها باشد. «برقرار شد» یعنی اتصال دو سرور باز است؛ «آنلاین» یعنی ترافیک هم از آن رد شده.</span><button class="p" onclick="tunNew()">+ تانل جدید</button></div><div id="tunBox">${tunBody()}</div>`}
async function tunLoad(){clearTimeout(TUNT);if(TAB!=='tun')return;try{TUN=await api('/tunnels')}catch(e){if(e.message!=='نیاز به ورود')toast(e.message,1);TUNT=setTimeout(tunLoad,8000);return}const b=$('#tunBox');if(b)b.innerHTML=tunBody();TUNT=setTimeout(tunLoad,5000)}
function tunBody(){
 if(!TUN)return '<div class="empty">در حال بارگذاری…</div>';
 if(!TUN.installed&&!TUN.tunnels.length)return '<div class="empty">بک‌پک روی این سرور نصب نیست؛ با «تانل جدید» خودکار نصب می‌شود.</div>';
 return TUN.tunnels.map(t=>{const p=TPH[t.phase]||TPH.down,tr=t.traffic||{},srv=t.role==='server',n=esc(t.name),h=t.host||0;
  return `<article class="card ${t.phase=='online'?'up':''}"><div class="row"><h3>${n}<small>${srv?'سرور ایران':'کلاینت خارج'}</small> <span class="tag">${esc(t.transport)}</span>${h?` <span class="tag">روی نود: ${esc(t.host_name)}</span>`:''}</h3><span class="b ${p[1]}">${p[0]}</span></div>
  <div class="meta"><span>وضعیت: <b>${esc(t.detail||t.state||'—')}</b></span><span>آدرس: <b style="direction:ltr;display:inline-block">${esc(t.addr||'—')}</b></span>${t.ports&&t.ports.length?`<span>پورت‌ها: <b>${esc(t.ports.join(', '))}</b></span>`:''}${t.route?`<span>مسیر: <b>${esc(t.route)}</b></span>`:t.remote_ip?`<span>سرور مقابل: <b>${esc(t.remote_ip)}</b></span>`:''}<span>ترافیک: <b>↓ ${fmtB(tr.bytes_in)} · ↑ ${fmtB(tr.bytes_out)}</b></span>${t.uptime?`<span>آپ‌تایم ۷ روز: <b>${esc(t.uptime.percent)}٪</b></span>`:''}</div>
  <div class="acts"><button class="s" onclick="tunAct('${n}','restart',${h})">ری‌استارت</button><button class="s" onclick="tunAct('${n}','stop',${h})">توقف</button><button class="s" onclick="tunAct('${n}','start',${h})">شروع</button><button class="s d" onclick="tunDel('${n}',${!!t.needs_pw},${h})">حذف</button></div></article>`}).join('')||'<div class="empty">هنوز تانلی نساخته‌اید.</div>'}
async function tunAct(n,a,h){try{await api('/tunnels/'+n+'/'+a+(h?'?node='+h:''),'POST');toast('انجام شد');tunLoad()}catch(e){toast(e.message,1)}}
async function tunDel(n,pwNeed,h){if(!confirm(`تانل ${n} حذف شود؟ (هر دو سمت تانل پاک می‌شود)`))return;let pw='';if(pwNeed){pw=prompt('یکی از دو سمت یک سرور دستی با SSH است؛ برای حذف آن سمت، رمز SSH را وارد کنید (خالی = فقط بقیه حذف شوند):');if(pw===null)return}
 try{const r=await api('/tunnels/'+n+(h?'?node='+h:''),'DELETE',{ssh_pass:pw});toast(r.warn||'حذف شد',!!r.warn);tunLoad()}catch(e){toast(e.message,1)}}
function tunSides(){const a=$('#tn_ir').value,b=$('#tn_kh').value,ssh=a==='ssh'||b==='ssh';
 $('#tn_sshw').style.display=ssh?'':'none';$('#tn_rl').textContent=a==='ssh'?'آی‌پی سرور ایران':'آی‌پی سرور خارج';
 for(const [id,o] of [['tn_ir',b],['tn_kh',a]]){const op=$('#'+id).querySelector('option[value=ssh]');if(op)op.disabled=o==='ssh'}
 $('#tn_same').style.display=a===b&&a!=='ssh'?'':'none'}
function tunNew(){
 const rp=8000+Math.floor(Math.random()*2000),nd=S.nodes||[];
 const opts=sel=>`<option value="local"${sel==='local'?' selected':''}>این سرور (پنل)</option>`+nd.map(n=>`<option value="node:${n.id}"${sel==='node:'+n.id?' selected':''}>نود: ${esc(n.name)} (${esc(n.address)})</option>`).join('')+`<option value="ssh"${sel==='ssh'?' selected':''}>سرور دیگر (با SSH)</option>`;
 const m=modal(`<h2>تانل جدید (BackPack)</h2><div id="tnF">
 <div class="g2"><div class="fg"><label>سرور ایران (سمتی که پورت‌ها روی آن باز می‌شوند)</label><select id="tn_ir" onchange="tunSides()">${opts('local')}</select></div>
 <div class="fg"><label>سرور خارج</label><select id="tn_kh" onchange="tunSides()">${opts(nd.length?'node:'+nd[0].id:'ssh')}</select></div></div>
 <div class="b bad" id="tn_same" style="display:none;margin-bottom:8px">سمت ایران و خارج نباید یک سرور باشند.</div>
 <div id="tn_sshw" style="display:none"><div class="g2"><div class="fg"><label id="tn_rl">آی‌پی سرور خارج</label><input id="tn_ip" dir="ltr" placeholder="1.2.3.4"></div><div class="fg"><label>پورت SSH</label><input id="tn_sp" dir="ltr" value="22"></div>
 <div class="fg"><label>یوزرنیم SSH (باید root باشد)</label><input id="tn_su" dir="ltr" value="root"></div><div class="fg"><label>رمز SSH</label><input id="tn_pw" type="password" dir="ltr" autocomplete="off"></div></div></div>
 <div class="g2"><div class="fg"><label>نام تانل</label><input id="tn_nm" dir="ltr" value="tun1"></div><div class="fg"><label>پورت تانل (روی سرور ایران)</label><input id="tn_tp" dir="ltr" value="${rp}"></div></div>
 <div class="fg"><label>پورت‌های عبوری (روی سرور ایران باز می‌شوند)</label><input id="tn_ports" dir="ltr" placeholder="443  یا  443,8443  یا  443=127.0.0.1:2096"><small>کاربران به این پورت‌های سرور ایران وصل می‌شوند و ترافیک به همان پورت روی سرور خارج می‌رسد.</small></div>
 <div class="fg" id="tn_myw"><label>آی‌پی عمومی سرور ایران (اختیاری)</label><input id="tn_my" dir="ltr"><small>خالی = خودکار: برای این سرور از دید سرور مقابل، برای نود آدرس خود نود.</small></div>
 <label class="chk"><span>عبور UDP هم فعال باشد (مثلاً برای وایرگارد)</span><input type="checkbox" id="tn_udp"></label>
 <small class="mut" style="display:block;margin-top:10px">نودها با کلید پنل وصل می‌شوند و رمز نمی‌خواهند. مراحل خودکار: اتصال ← بررسی نام و پورت ← نصب بک‌پک روی دو سرور ← ساخت کانفیگ و سرویس ← فایروال ← راه‌اندازی ← انتظار برای برقراری تانل.</small></div>
 <div class="mfoot"><button class="s" id="tn_c">بستن</button><button class="p" id="tn_s">شروع ساخت تانل</button></div>`);
 tunSides();
 m.querySelector('#tn_c').onclick=()=>{m.remove();tunLoad()};
 m.querySelector('#tn_s').onclick=async()=>{const g=i=>m.querySelector('#'+i);
  const b={iran:g('tn_ir').value,kharej:g('tn_kh').value,remote_ip:g('tn_ip').value.trim(),ssh_port:g('tn_sp').value,ssh_user:g('tn_su').value.trim(),ssh_pass:g('tn_pw').value,name:g('tn_nm').value.trim(),tunnel_port:g('tn_tp').value,ports:g('tn_ports').value,my_ip:g('tn_my').value.trim(),udp:g('tn_udp').checked};
  try{const r=await api('/tunnels','POST',b);tunProg(m,r.job)}catch(e){toast(e.message,1)}}}
function tunProg(m,job){const box=m.querySelector('#tnF');m.querySelector('#tn_s').remove();
 const loop=async()=>{if(!document.body.contains(m))return;let d;try{d=await api('/tunnels/job/'+job)}catch(e){toast(e.message,1);return}
  box.innerHTML=d.steps.map(s=>`<div class="stp ${s.s}"><i>${s.s=='ok'?'✔':s.s=='err'?'✖':s.s=='warn'?'!':'…'}</i><div>${esc(s.t)}${s.m?`<small>${esc(s.m)}</small>`:''}</div></div>`).join('')+
  (d.state=='done'?'<div class="b ok" style="margin-top:10px">تانل برقرار شد. به‌محض عبور ترافیک، وضعیتش «آنلاین» می‌شود.</div>':d.state=='warn'?'<div class="b warn" style="margin-top:10px">ساخته شد ولی هنوز وصل نشده؛ وضعیت را در لیست تانل‌ها دنبال کنید.</div>':d.state=='failed'?'<div class="b bad" style="margin-top:10px">ساخت تانل ناموفق بود و تغییرات برگردانده شد.</div>':'');
  if(d.state=='run')setTimeout(loop,1500);else tunLoad()};loop()}
/* ---------- نودها ---------- */
const nodName=id=>{if(!id)return 'این سرور';const n=(S.nodes||[]).find(x=>x.id==id);return n?n.name:'#'+id};
const NODF=[{k:'name',l:'نام نود',h:'فقط یک برچسب است؛ هر وقت خواستید عوضش کنید.'},{k:'note',l:'توضیح / لوکیشن (اختیاری)',rtl:1},{k:'address',l:'آدرس نود (IP یا دامنه)',h:'همین آدرس برای SSH و برای لینک کلاینت‌ها استفاده می‌شود (مگر در اینباند «آدرس عمومی» دیگری بگذارید).'},{k:'ssh_port',l:'پورت SSH',t:'number'}];
function nodHTML(){
 const li=S.inbounds.filter(i=>!i.node_id),ids=new Set(li.map(i=>i.id)),lc=S.clients.filter(c=>c.links.some(l=>ids.has(l.inbound_id))).length;
 return `<div class="bar2"><span class="mut sm">هر نود یک سرور جداست؛ موقع ساخت اینباند VLESS نود را انتخاب می‌کنید و همه‌ی آن‌ها در یک لینک ساب جمع می‌شوند.</span><button class="p" onclick="nodNew()">+ نود جدید</button></div>
 <article class="card up"><div class="row"><h3>این سرور<small>نود اصلی (پنل)</small></h3><span class="b ok">آنلاین</span></div><div class="meta"><span>اینباندها: <b>${li.length}</b></span><span>کلاینت‌ها: <b>${lc}</b></span></div></article>`
 +(S.nodes||[]).map(n=>`<article class="card ${n.online?'up':''}"><div class="row"><h3>${esc(n.name)}<small>${esc(n.note)}</small>${n.xray_ver?` <span class="tag">Xray ${esc(n.xray_ver)}</span>`:''}</h3><span class="b ${n.online?'ok':'bad'}">${n.online?'آنلاین':'قطع'}</span></div>
 <div class="meta"><span>آدرس: <b style="direction:ltr;display:inline-block">${esc(n.address)}</b></span><span>SSH: <b style="direction:ltr;display:inline-block">${esc(n.ssh_user)}@:${n.ssh_port}</b></span><span>اینباندها: <b>${n.inbounds}</b></span><span>کلاینت‌ها: <b>${n.clients}</b></span>${!n.online&&n.error?`<span style="color:#f87171">${esc(n.error)}</span>`:''}</div>
 <div class="acts"><button class="s" onclick="nodNewInb(${n.id})">+ اینباند روی این نود</button><button class="s" onclick="nodEdit(${n.id})">ویرایش</button><button class="s" onclick="nodCheck(${n.id})">بررسی اتصال</button><button class="s d" onclick="nodDel(${n.id})">حذف</button></div></article>`).join('')
 +((S.nodes||[]).length?'':'<div class="empty">هنوز نودی اضافه نکرده‌اید. با «نود جدید» اطلاعات SSH سرور را بدهید؛ بقیه‌ی کارها خودکار انجام می‌شود.</div>')}
function nodNewInb(id){newInb({proto:'vless',node_id:String(id)})}
function nodEdit(id){const n=S.nodes.find(x=>x.id==id);formModal('ویرایش نود '+esc(n.name),NODF,{...n},true,o=>act(()=>api('/nodes/'+id,'PUT',o),'ذخیره شد'))}
async function nodCheck(id){try{toast('در حال بررسی…');await api('/nodes/'+id+'/check','POST');toast('اتصال به نود برقرار است');await load()}catch(e){toast(e.message,1);load()}}
async function nodDel(id){const n=S.nodes.find(x=>x.id==id);if(!confirm(n.inbounds?`نود «${n.name}» همراه با ${n.inbounds} اینباندش حذف شود؟ کلاینت‌ها از این اینباندها جدا می‌شوند.`:`نود «${n.name}» حذف شود؟`))return;
 try{const r=await api('/nodes/'+id+(n.inbounds?'?force=1':''),'DELETE');toast(r.warn||'حذف شد',!!r.warn);await load()}catch(e){toast(e.message,1)}}
function nodNew(){
 const m=modal(`<h2>نود جدید</h2><div id="ndF"><div class="g2"><div class="fg"><label>نام نود</label><input id="nd_nm" placeholder="مثلاً آلمان"></div><div class="fg"><label>توضیح / لوکیشن (اختیاری)</label><input id="nd_note"></div>
 <div class="fg"><label>آی‌پی یا دامنه‌ی سرور نود</label><input id="nd_ip" dir="ltr" placeholder="1.2.3.4"></div><div class="fg"><label>پورت SSH</label><input id="nd_sp" dir="ltr" value="22"></div>
 <div class="fg"><label>یوزرنیم SSH (باید root باشد)</label><input id="nd_su" dir="ltr" value="root"></div><div class="fg"><label>رمز SSH</label><input id="nd_pw" type="password" dir="ltr" autocomplete="off"></div></div>
 <small class="mut" style="display:block;margin-top:10px">مراحل خودکار: اتصال SSH ← نصب کلید پنل روی نود (رمز ذخیره نمی‌شود و بعدش با کلید وصل می‌شود) ← نصب Xray-core ← ساخت سرویس ← ثبت نود.</small></div>
 <div class="mfoot"><button class="s" id="nd_c">بستن</button><button class="p" id="nd_s">شروع افزودن نود</button></div>`);
 m.querySelector('#nd_c').onclick=()=>{m.remove();load()};
 m.querySelector('#nd_s').onclick=async()=>{const g=i=>m.querySelector('#'+i);
  const b={name:g('nd_nm').value.trim(),note:g('nd_note').value.trim(),address:g('nd_ip').value.trim(),ssh_port:g('nd_sp').value,ssh_user:g('nd_su').value.trim(),ssh_pass:g('nd_pw').value};
  try{const r=await api('/nodes','POST',b);nodProg(m,r.job)}catch(e){toast(e.message,1)}}}
function nodProg(m,job){const box=m.querySelector('#ndF');m.querySelector('#nd_s').remove();
 const loop=async()=>{if(!document.body.contains(m))return;let d;try{d=await api('/nodes/job/'+job)}catch(e){toast(e.message,1);return}
  box.innerHTML=d.steps.map(s=>`<div class="stp ${s.s}"><i>${s.s=='ok'?'✔':s.s=='err'?'✖':s.s=='warn'?'!':'…'}</i><div>${esc(s.t)}${s.m?`<small>${esc(s.m)}</small>`:''}</div></div>`).join('')+
  (d.state=='done'?'<div class="b ok" style="margin-top:10px">نود اضافه شد. حالا موقع ساخت اینباند VLESS می‌توانید آن را انتخاب کنید.</div>':d.state=='failed'?'<div class="b bad" style="margin-top:10px">افزودن نود ناموفق بود.</div>':'');
  if(d.state=='run')setTimeout(loop,1500);else load()};loop()}
/* ---------- اینباندها ---------- */
function inbHTML(){return `<div class="bar2"><span></span><button class="p" onclick="newInb()">+ اینباند جدید</button></div>`+
 (S.inbounds.map(i=>`<article class="card ${i.up?'up':''}"><div class="row"><h3>${esc(i.name)}<small>${esc(i.remark)}</small>${i.awg?' <span class="tag">AmneziaWG</span>':''}${i.proto==='l2tp'?' <span class="tag">L2TP/IPsec</span>':''}${i.proto==='ovpn'?' <span class="tag">OpenVPN</span>':''}${i.proto==='vless'?' <span class="tag">VLESS</span>':''}${i.node_id?` <span class="tag">نود: ${esc(nodName(i.node_id))}</span>`:''}${i.exclude_sub?' <span class="tag">خارج از ساب</span>':''}</h3>
 <span class="b ${i.enabled?(i.up?'ok':'warn'):''}">${i.enabled?(i.up?'بالا':'پایین (خطا؟)'):'غیرفعال'}</span></div>
 <div class="meta"><span>پورت: <b>${i.proto==='l2tp'?'500, 4500/udp':i.proto==='ovpn'?i.port+'/'+esc(i.ovpn.transport):i.proto==='vless'?i.port+'/'+i.net:i.port+'/udp'}</b></span>${i.proto==='vless'?'':`<span>IPv4: <b>${esc(i.address4)}</b></span>`}${i.address6?`<span>IPv6: <b>${esc(i.address6)}</b></span>`:''}
 <span>Endpoint: <b>${esc(i.endpoint||'(آدرس پنل)')}${i.endpoint_port?':'+i.endpoint_port:''}</b></span><span>DNS: <b>${esc(i.dns||'—')}</b></span>
 <span>MTU: <b>${i.mtu||'پیش‌فرض'}</b></span><span>کلاینت: <b>${i.clients}</b></span>
 ${i.proto==='l2tp'?`<span style="cursor:pointer" onclick="copy('${esc(i.psk)}')">IPsec PSK: <b>${esc(i.psk)}</b></span>`:i.proto==='ovpn'?`<span>رمزنگاری: <b>${esc(i.ovpn.cipher)}</b></span>${i.ovpn.tlscrypt?'<span>tls-crypt</span>':''}`:i.proto==='vless'?`<span>${esc(i.xcfg.transport)} + <b>${esc(i.xcfg.security)}</b></span>${i.xcfg.flow?`<span>${esc(i.xcfg.flow)}</span>`:''}${i.xcfg.security==='reality'?`<span style="cursor:pointer" onclick="copy('${esc(i.xcfg.reality_pub)}')">Public Key: <b>${esc((i.xcfg.reality_pub||'').slice(0,12))}…</b></span><span>SNI: <b>${esc((i.xcfg.server_names||'').split(',')[0])}</b></span>`:''}`:`<span style="cursor:pointer" onclick="copy('${esc(i.public_key)}')">کلید عمومی: <b>${esc(i.public_key.slice(0,12))}…</b></span>`}</div>
 <div class="acts"><button class="s" onclick="editInb(${i.id})">ویرایش</button><button class="s" onclick="showConf(${i.id})">کانفیگ سرور</button>
 <button class="s" onclick="act(()=>api('/inbounds/${i.id}/restart','POST'),'ری‌استارت شد')">ری‌استارت</button>
 <button class="s" onclick="act(()=>api('/inbounds/${i.id}/toggle','POST'))">${i.enabled?'غیرفعال‌سازی':'فعال‌سازی'}</button>
 <button class="s d" onclick="delInb(${i.id},'${esc(i.name)}')">حذف</button></div></article>`).join('')||'<div class="empty">هنوز اینباندی نساخته‌اید. اول یکی بسازید، بعد کلاینت اضافه کنید.</div>')}
const OBF=[['jc','Jc (تعداد بسته‌های junk)','پیشنهادی ۴ تا ۱۲'],['jmin','Jmin (حداقل اندازه junk)',''],['jmax','Jmax (حداکثر اندازه junk)','باید از Jmin بزرگتر باشد'],
 ['s1','S1 (پدینگ بسته init)',''],['s2','S2 (پدینگ بسته response)','S1+56 نباید با S2 برابر باشد'],['s3','S3 (پدینگ cookie)','AWG 2.0 به بعد'],['s4','S4 (پدینگ transport)','AWG 2.0 به بعد'],
 ['h1','H1 (magic header)','عدد یا بازه low-high'],['h2','H2 (magic header)',''],['h3','H3 (magic header)',''],['h4','H4 (magic header)','بازه‌ها نباید هم‌پوشانی داشته باشند'],
 ['i1','I1 (بسته امضا)','اختیاری — مثال <r 100>'],['i2','I2 (بسته امضا)',''],['i3','I3 (بسته امضا)',''],['i4','I4 (بسته امضا)',''],['i5','I5 (بسته امضا)',''],
 ['hpk','HeaderProtectionKey','کلید base64 ۳۲ بایتی؛ روی سرور و کلاینت باید یکی باشد؛ خالی = خاموش'],['cpa','ContentPaddingAddition','عدد یا بازه، مثلا 13-28'],
 ['rekey_after','RekeyAfterTime (ثانیه)','مثلا 101-114'],['rekey_timeout','RekeyTimeout (ثانیه)','مثلا 3-6'],['reject_after','RejectAfterTime (ثانیه)','مثلا 166-241'],
 ['keepalive_timeout','KeepaliveTimeout (ثانیه)','مثلا 12-20'],['max_hs','MaxHandshakeAttempts','مثلا 15-21']];
const AWG_FIELDS=[{s:'مبهم‌سازی AmneziaWG (ضد DPI)',p:'wg'},
 {p:'wg',k:'obf_enabled',l:'فعال‌سازی AmneziaWG برای این اینباند',t:'check',h:'سرور باید amneziawg-tools نصب داشته باشد و کلاینت‌ها اپ AmneziaWG بزنند؛ اپ WireGuard معمولی به این اینباند وصل نمی‌شود.'},
 {p:'wg',k:'obf_ver',l:'نسخه پارامترها برای ساخت خودکار',t:'select',opts:[['3','3.x — کامل (Header Protection + padding + تایمرها)'],['2','2.0 — S3/S4 + بازه H + I1'],['1','1.x — فقط Jc/Jmin/Jmax/S1/S2/H1-H4']]},
 {p:'wg',t:'btn',l:'ساخت دوباره پارامترها',on:'genObf()'},
 ...OBF.map(([k,l,h])=>({k:'o_'+k,l,h,p:'wg'}))];
async function testDest(){try{const d=$('#f_x_reality_dest').value||'www.microsoft.com:443';toast('در حال تست…');const r=await api('/vless/check-dest?dest='+encodeURIComponent(d));toast(r.ok?`✔ ${r.tls} · ${r.alpn} · ${r.ms}ms — ${r.note}`:(r.error||`✘ ${r.tls||''} ${r.alpn||''} — ${r.note||''}`),!r.ok)}catch(e){toast(e.message,1)}}
async function genObf(){try{const r=await api('/obf/generate?v='+$('#f_obf_ver').value);for(const [k] of OBF){const e=$('#f_o_'+k);if(e)e.value=r[k]||''}$('#f_obf_enabled').checked=true;toast('پارامترهای جدید ساخته شد')}catch(e){toast(e.message,1)}}
const XFP=['chrome','firefox','safari','ios','android','edge','360','qq','random','randomized',''];
const INB=[{s:'اصلی'},
 {k:'proto',l:'پروتکل',t:'select',opts:[['wg','WireGuard'],['l2tp','L2TP/IPsec — برای مودم، روتر و گوشی (بدون نیاز به اپ)'],['ovpn','OpenVPN — اپ OpenVPN، مودم و روتر (UDP/TCP)'],['vless','VLESS — Xray (Reality / TLS / WS / gRPC / xHTTP / mKCP)']],lock:1,h:'پروتکل بعد از ساخت اینباند قابل تغییر نیست. از L2TP فقط یک اینباند می‌شود ساخت.'},
 {k:'node_id',l:'نود (سروری که این اینباند روی آن ساخته می‌شود)',t:'select',p:'vless',lock:1,opts:()=>[['0','این سرور (پنل اصلی)'],...(S.nodes||[]).map(n=>[String(n.id),esc(n.name)+' — '+esc(n.address)])],h:'بعد از ساخت قابل تغییر نیست. روی نود، گواهی «پنل» عیناً به نود کپی می‌شود و مسیر «فایل گواهی» باید روی خود نود باشد. لینک کلاینت‌ها به آدرس همان نود می‌رود.'},
 {k:'name',l:'نام اینباند',h:'مثل wg0 یا l2tp — حداکثر ۱۵ حرف انگلیسی'},{k:'remark',l:'توضیح',rtl:1},
 {k:'port',l:'پورت',t:'number',p:'wg ovpn vless',h:'وایرگارد UDP است؛ OpenVPN پیش‌فرض 1194 (برای عبور از فیلتر می‌توانید TCP/443 بگذارید)'},{k:'address4',l:'آدرس سرور IPv4 / ساب‌نت',ph:'10.8.0.1/24',p:'wg l2tp ovpn',h:'در L2TP: آی‌پی گیت‌وی داخل VPN؛ بقیه‌ی رنج به کلاینت‌ها داده می‌شود'},
 {k:'psk',l:'کلید IPsec (Pre-shared key)',p:'l2tp',h:'همه‌ی کلاینت‌ها همین کلید را در مودم/روتر وارد می‌کنند. پورت‌های UDP ‏500 و 4500 را در فایروال باز کنید.'},
 {k:'address6',l:'آدرس سرور IPv6 (اختیاری)',ph:'fd42:42:0::1/64',h:'خالی = بدون IPv6',p:'wg'},
 {k:'private_key',l:'کلید خصوصی سرور',h:'خالی = ساخت خودکار (در ویرایش: خالی = بدون تغییر)',p:'wg'},
 {k:'regen_keys',l:'ساخت دوباره کلید سرور / CA (کلاینت‌ها باید کانفیگ جدید بگیرند)',t:'check',edit:1,p:'wg ovpn vless'},
 {s:'اتصال کلاینت‌ها'},
 {k:'endpoint',l:'آدرس عمومی سرور (Endpoint)',h:'IP یا دامنه. خالی = همان آدرسی که پنل با آن باز شده'},
 {k:'endpoint_port',l:'پورت Endpoint',t:'number',h:'۰ = همان پورت listen (برای پورت‌فوروارد/NAT/CDN). در VLESS: پورتی که داخل لینک کلاینت می‌آید',p:'wg ovpn vless'},
 {k:'dns',l:'DNS کلاینت',ph:'1.1.1.1, 1.0.0.1',p:'wg l2tp ovpn'},{k:'client_mtu',l:'MTU کلاینت',t:'number',h:'۰ = همان MTU سرور',p:'wg'},
 {k:'client_allowed_ips',l:'AllowedIPs کلاینت',h:'0.0.0.0/0, ::/0 = تمام ترافیک از تونل',p:'wg'},
 {k:'client_keepalive',l:'PersistentKeepalive (ثانیه)',t:'number',h:'۰ = خاموش، ۲۵ = پیشنهادی پشت NAT',p:'wg'},
 {k:'use_psk',l:'PresharedKey جداگانه برای هر کلاینت (امنیت بیشتر)',t:'check',p:'wg'},
 {k:'exclude_sub',l:'حذف از اشتراک‌ها (کلاینت‌ها این اینباند را در لینک ساب نمی‌بینند)',t:'check'},
 {s:'تنظیمات OpenVPN',p:'ovpn'},
 {k:'v_transport',l:'ترنسپورت',t:'select',p:'ovpn',opts:[['udp','UDP — سریع‌تر (پیشنهادی)'],['tcp','TCP — برای شبکه‌های محدود، مثلاً پورت 443']]},
 {k:'v_cipher',l:'رمزنگاری دیتا',t:'select',p:'ovpn',opts:[['AES-256-GCM','AES-256-GCM (پیشنهادی)'],['AES-128-GCM','AES-128-GCM'],['CHACHA20-POLY1305','CHACHA20-POLY1305 (موبایل/مودم بدون AES سخت‌افزاری)'],['AES-256-CBC','AES-256-CBC (قدیمی)'],['AES-128-CBC','AES-128-CBC (قدیمی)']]},
 {k:'v_keytype',l:'نوع کلید گواهی‌ها',t:'select',p:'ovpn',opts:[['ec','EC prime256v1 — سبک و سریع'],['rsa','RSA 2048 — سازگار با دستگاه‌های قدیمی']],h:'روی اینباند موجود فقط با «ساخت دوباره کلید» اعمال می‌شود.'},
 {k:'v_tlscrypt',l:'tls-crypt (پنهان‌سازی هندشیک و مقاومت در برابر DPI/پروب)',t:'check',p:'ovpn'},
 {k:'v_redirect',l:'تمام ترافیک کلاینت از VPN عبور کند (redirect-gateway)',t:'check',p:'ovpn'},
 {k:'v_routes',l:'مسیرهای اضافه برای کلاینت (CIDR، با کاما)',p:'ovpn',ph:'192.168.1.0/24',h:'اگر بالا فعال نیست، فقط همین شبکه‌ها از VPN می‌روند.'},
 {k:'v_legacy',l:'سازگاری با کلاینت‌های قدیمی (OpenVPN 2.3 و مودم‌های قدیمی: ncp-ciphers)',t:'check',p:'ovpn'},
 {k:'v_extra_server',l:'دستورات اضافه سرور (هر خط یک دستور)',t:'textarea',p:'ovpn',h:'دستورات خطرناک مثل script-security/up/plugin مسدودند.'},
 {k:'v_extra_client',l:'دستورات اضافه کلاینت (هر خط یک دستور)',t:'textarea',p:'ovpn',h:'مثلاً: compress / tun-mtu / http-proxy'},
 {s:'تنظیمات VLESS (Xray-core)',p:'vless'},
 {k:'x_transport',l:'ترنسپورت (Network)',t:'select',p:'vless',opts:[['tcp','TCP (RAW) — با Reality/Vision بهترین حالت'],['ws','WebSocket — پشت CDN'],['grpc','gRPC'],['httpupgrade','HTTPUpgrade'],['xhttp','xHTTP (SplitHTTP) — جدیدترین'],['kcp','mKCP (UDP)']]},
 {k:'x_security',l:'امنیت (Security)',t:'select',p:'vless',opts:[['reality','Reality — بدون نیاز به دامنه و گواهی (پیشنهادی)'],['tls','TLS — با دامنه و گواهی'],['none','بدون رمزنگاری (فقط پشت CDN/پروکسی)']],h:'Reality فقط با TCP، gRPC و xHTTP کار می‌کند؛ mKCP فقط بدون امنیت.'},
 {k:'x_flow',l:'Flow',t:'select',p:'vless',w:'x_transport=tcp,x_security=tls|reality',opts:[['xtls-rprx-vision','xtls-rprx-vision (پیشنهادی)'],['','بدون flow']]},
 {k:'x_fp',l:'Fingerprint کلاینت (uTLS)',t:'select',p:'vless',w:'x_security=tls|reality',opts:XFP.map(a=>[a,a||'بدون'])},
 {k:'x_packet_encoding',l:'Packet Encoding',t:'select',p:'vless',opts:[['','پیش‌فرض'],['xudp','xudp (پیشنهادی برای UDP/بازی)'],['packet','packet']]},
 {s:'Reality',p:'vless',w:'x_security=reality'},
 {k:'x_reality_dest',l:'Dest (سایت مقصد برای Reality)',p:'vless',w:'x_security=reality',ph:'www.microsoft.com:443',h:'سایتی که TLS 1.3 و h2 داشته باشد و در کشور شما فیلتر نباشد.'},
 {t:'btn',l:'تست Dest (TLS1.3 / h2)',on:'testDest()',p:'vless',w:'x_security=reality'},
 {k:'x_server_names',l:'SNI ها (serverNames، با کاما)',p:'vless',w:'x_security=reality',ph:'www.microsoft.com',h:'خالی = همان دامین Dest. اولین مورد در لینک کلاینت می‌آید.'},
 {k:'x_short_ids',l:'Short IDها (با کاما)',p:'vless',w:'x_security=reality',h:'خالی = ساخت خودکار. hex زوج، ۲ تا ۱۶ کاراکتر.'},
 {k:'x_spider_x',l:'SpiderX',p:'vless',w:'x_security=reality',ph:'/'},
 {k:'x_reality_priv',l:'کلید خصوصی Reality (اختیاری)',p:'vless',w:'x_security=reality',h:'خالی = ساخت خودکار / بدون تغییر. کلید عمومی در کارت اینباند نمایش داده می‌شود.'},
 {s:'TLS',p:'vless',w:'x_security=tls'},
 {k:'x_tls_mode',l:'منبع گواهی',t:'select',p:'vless',w:'x_security=tls',opts:[['panel','گواهی پنل (دامنهٔ ثبت‌شده در sepipanel)'],['files','فایل‌های گواهی روی سرور'],['self','خودامضا (برای تست/پشت CDN)']]},
 {k:'x_tls_cert',l:'مسیر fullchain.pem',p:'vless',w:'x_security=tls,x_tls_mode=files',ph:'/etc/letsencrypt/live/example.com/fullchain.pem'},
 {k:'x_tls_key',l:'مسیر privkey.pem',p:'vless',w:'x_security=tls,x_tls_mode=files',ph:'/etc/letsencrypt/live/example.com/privkey.pem'},
 {k:'x_sni',l:'SNI',p:'vless',w:'x_security=tls',ph:'example.com',h:'خالی = آدرس سرور'},
 {k:'x_alpn',l:'ALPN (با کاما)',p:'vless',w:'x_security=tls',ph:'h2,http/1.1'},
 {k:'x_min_ver',l:'حداقل نسخه TLS',t:'select',p:'vless',w:'x_security=tls',opts:[['1.2','1.2'],['1.3','1.3'],['1.1','1.1'],['1.0','1.0']]},
 {k:'x_reject_sni',l:'رد SNI ناشناخته (rejectUnknownSni)',t:'check',p:'vless',w:'x_security=tls'},
 {k:'x_allow_insecure',l:'کلاینت اعتبارسنجی گواهی را رد کند (allowInsecure)',t:'check',p:'vless',w:'x_security=tls'},
 {s:'جزئیات ترنسپورت',p:'vless'},
 {k:'x_tcp_header',l:'Header TCP',t:'select',p:'vless',w:'x_transport=tcp',opts:[['none','none'],['http','http (استتار HTTP)']]},
 {k:'x_path',l:'Path',p:'vless',w:'x_transport=ws|httpupgrade|xhttp|tcp',ph:'/'},
 {k:'x_host',l:'Host',p:'vless',w:'x_transport=ws|httpupgrade|xhttp|tcp',h:'برای WS/CDN معمولاً همان دامنه'},
 {k:'x_xhttp_mode',l:'حالت xHTTP',t:'select',p:'vless',w:'x_transport=xhttp',opts:[['auto','auto'],['packet-up','packet-up'],['stream-up','stream-up'],['stream-one','stream-one']]},
 {k:'x_service_name',l:'Service Name (gRPC)',p:'vless',w:'x_transport=grpc',h:'خالی = تصادفی'},
 {k:'x_authority',l:'Authority (gRPC)',p:'vless',w:'x_transport=grpc'},
 {k:'x_multi_mode',l:'Multi Mode (gRPC)',t:'check',p:'vless',w:'x_transport=grpc'},
 {k:'x_kcp_header',l:'Header mKCP',t:'select',p:'vless',w:'x_transport=kcp',opts:[['none','none'],['srtp','srtp'],['utp','utp'],['wechat-video','wechat-video'],['dtls','dtls'],['wireguard','wireguard']]},
 {k:'x_kcp_seed',l:'Seed (mKCP)',p:'vless',w:'x_transport=kcp'},
 {s:'Fallback، Sniffing و مسیریابی',p:'vless'},
 {k:'x_fallback_dest',l:'Fallback Dest (فقط TCP + TLS)',p:'vless',w:'x_transport=tcp,x_security=tls',ph:'80 یا 127.0.0.1:8080',h:'درخواست‌های غیر VLESS به این مقصد می‌روند (مثلاً یک وب‌سایت).'},
 {k:'x_fallback_xver',l:'Fallback xver (PROXY protocol)',t:'number',p:'vless',w:'x_transport=tcp,x_security=tls'},
 {k:'x_sniffing',l:'Sniffing (تشخیص http/tls/quic)',t:'check',p:'vless'},
 {k:'x_route_only',l:'Route Only (فقط برای مسیریابی)',t:'check',p:'vless',w:'x_sniffing=1'},
 {k:'x_block_bt',l:'مسدود کردن BitTorrent',t:'check',p:'vless',h:'نیاز به Sniffing فعال دارد.'},
 {k:'x_block_private',l:'مسدود کردن آی‌پی‌های خصوصی/محلی (جلوگیری از دسترسی به شبکهٔ سرور)',t:'check',p:'vless'},
 {k:'x_domain_strategy',l:'Domain Strategy خروجی',t:'select',p:'vless',opts:[['AsIs','AsIs'],['UseIP','UseIP'],['UseIPv4','UseIPv4'],['UseIPv6','UseIPv6']]},
 {k:'x_listen',l:'Listen',p:'vless',ph:'0.0.0.0',h:'برای IPv6 هم: ::'},
 {k:'x_tfo',l:'TCP Fast Open',t:'check',p:'vless'},
 {k:'x_extra_stream',l:'JSON اضافه برای streamSettings (پیشرفته)',t:'textarea',p:'vless',h:'مثلاً {"sockopt":{"tcpKeepAliveIdle":300}} — با تنظیمات بالا ادغام می‌شود.'},
 {s:'پیشرفته (سرور)'},

 {k:'mtu',l:'MTU اینترفیس سرور',t:'number',p:'wg l2tp ovpn',h:'۰ = پیش‌فرض (وایرگارد 1420، L2TP ‏1400، OpenVPN خودکار)'},
 {k:'table_',l:'Table',ph:'off | auto | عدد',h:'خالی = پیش‌فرض wg-quick',p:'wg'},{k:'fwmark',l:'FwMark',ph:'0xca6c | off',p:'wg'},
 {k:'auto_rules',l:'قوانین فایروال خودکار (در VLESS: باز کردن پورت در iptables؛ در بقیه NAT + فوروارد)',t:'check'},
 {k:'nat_iface',l:'اینترفیس خروجی اینترنت',ph:'خودکار',p:'wg l2tp ovpn'},
 {k:'pre_up',l:'PreUp (هر خط یک دستور)',t:'textarea',p:'wg'},{k:'post_up',l:'PostUp',t:'textarea',p:'wg'},
 {k:'pre_down',l:'PreDown',t:'textarea',p:'wg'},{k:'post_down',l:'PostDown',t:'textarea',p:'wg'},
 ...AWG_FIELDS];
function fieldHTML(f,v,edit){const h=fieldInner(f,v,edit);return (f.p||f.w)&&h?`<div ${f.p?`data-p="${f.p}"`:''} ${f.w?`data-w="${f.w}"`:''}>${h}</div>`:h}
function fieldInner(f,v,edit){
 if(f.s)return `<h4>${f.s}</h4>`;if(f.edit&&!edit)return '';if(f.t==='btn')return `<div class="fg"><button type="button" class="s" onclick="${f.on}">${f.l}</button></div>`;
 let val=v[f.k];if(val==null)val='';const id='f_'+f.k;const h=f.h?`<small>${f.h}</small>`:'';
 if(f.t==='check')return `<div class="fg"><label class="chk"><input type="checkbox" id="${id}" ${val?'checked':''}> ${f.l}</label>${h}</div>`;
 if(f.t==='select')return `<div class="fg"><label>${f.l}</label><select id="${id}" ${f.lock&&edit?'disabled':''}>${(typeof f.opts==='function'?f.opts():f.opts).map(([a,b])=>`<option value="${a}" ${String(val)===a?'selected':''}>${b}</option>`).join('')}</select>${h}</div>`;
 if(f.t==='textarea')return `<div class="fg"><label>${f.l}</label><textarea id="${id}" spellcheck="false">${esc(val)}</textarea>${h}</div>`;
 return `<div class="fg"><label>${f.l}</label><input id="${id}" type="${f.t==='number'?'number':f.t||'text'}" value="${esc(val)}" placeholder="${esc(f.ph||'')}" ${f.rtl?'style="direction:rtl;text-align:right"':''}>${h}</div>`}
function collect(fields,edit){const o={};for(const f of fields){if(f.s||f.t==='btn'||(f.edit&&!edit))continue;const e=$('#f_'+f.k);const v=f.t==='check'?e.checked:e.value;if(f.k.startsWith('o_')){(o.obf=o.obf||{})[f.k.slice(2)]=v}else if(f.k.startsWith('v_')){(o.ovpn=o.ovpn||{})[f.k.slice(2)]=v}else if(f.k.startsWith('x_')){(o.xcfg=o.xcfg||{})[f.k.slice(2)]=v}else o[f.k]=v}return o}
function modal(html){const m=document.createElement('div');m.className='ov';m.innerHTML=`<div class="md">${html}</div>`;m.addEventListener('mousedown',e=>{if(e.target===m)m.remove()});document.body.appendChild(m);return m}
function formModal(title,fields,vals,edit,onSave){
 const m=modal(`<h2>${title}</h2>${fields.map(f=>fieldHTML(f,vals,edit)).join('')}<div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">${ic('save')}ذخیره</button></div>`);
 m.querySelector('#mc').onclick=()=>m.remove();
 const ps=m.querySelector('#f_proto');
 if(ps){const g=k=>m.querySelector('#f_'+k);const w={port:g('port')&&g('port').value,mtu:g('mtu')&&g('mtu').value};
   const DM={wg:{name:g('name')&&g('name').value,port:w.port,mtu:w.mtu},l2tp:{name:'l2tp',mtu:'1400'},ovpn:{name:'ovpn',port:'1194',mtu:'0'},vless:{name:'vless',port:'443'}};
   const val=k=>{const e=g(k);return e?(e.type==='checkbox'?(e.checked?'1':'0'):e.value):''};
   const okW=w=>!w||w.split(',').every(c=>{const [k,vs]=c.split('=');return vs.split('|').includes(val(k))});
   const ap=()=>{m.querySelectorAll('[data-p],[data-w]').forEach(e=>e.style.display=((!e.dataset.p||e.dataset.p.split(' ').includes(ps.value))&&okW(e.dataset.w))?'':'none');
     if(!edit){const d=DM[ps.value];for(const k of ['name','port','mtu']){const e=g(k);if(e&&d[k]!=null&&(k!=='name'||/^(wg\d*|l2tp|ovpn|vless)$/.test(e.value)))e.value=d[k]}}};
   ps.onchange=ap;m.addEventListener('change',ap);ap()}
 m.querySelector('#ms').onclick=async()=>{if(await onSave(collect(fields,edit)))m.remove()}}
function newInb(pre={}){const d=S.defaults;formModal('اینباند جدید',INB,{...d,obf_ver:'3',proto:'wg',...Object.fromEntries(Object.entries(d.ovpn||{}).map(([k,v])=>['v_'+k,v])),...Object.fromEntries(Object.entries(d.xcfg||{}).map(([k,v])=>['x_'+k,v])),...pre},false,o=>act(()=>api('/inbounds','POST',o),'اینباند ساخته شد'))}
function editInb(id){const i=S.inbounds.find(x=>x.id==id);formModal('ویرایش اینباند '+esc(i.name),INB,{...i,private_key:'',obf_ver:'3',...Object.fromEntries(Object.entries(i.obf||{}).map(([k,v])=>['o_'+k,v])),...Object.fromEntries(Object.entries(i.ovpn||{}).map(([k,v])=>['v_'+k,v])),...Object.fromEntries(Object.entries(i.xcfg||{}).map(([k,v])=>['x_'+k,v])),x_reality_priv:''},true,o=>act(()=>api('/inbounds/'+id,'PUT',o),'ذخیره شد'))}
function delInb(id,n){if(confirm(`اینباند ${n} و اتصال همه کلاینت‌هایش حذف شود؟`))act(()=>api('/inbounds/'+id,'DELETE'),'حذف شد')}
async function showConf(id){try{const r=await api('/inbounds/'+id+'/conf');const m=modal(`<h2>کانفیگ سرور</h2><pre class="cf">${esc(r.conf)}</pre><div class="mfoot"><button class="s" id="x">بستن</button></div>`);m.querySelector('#x').onclick=()=>m.remove()}catch(e){toast(e.message,1)}}
/* ---------- کلاینت‌ها ---------- */
const admName=id=>{const a=(S.admins||[]).find(x=>x.id==id);return a?a.username:'#'+id};
const dleft=e=>e?' ('+Math.max(0,Math.ceil((e-Date.now()/1000)/86400))+' روز مانده)':'';
function meCard(){const m=S.me;if(!m)return '';const u=m.used_bytes,pct=m.limit_bytes?Math.min(100,u*100/m.limit_bytes):0,st=STL[m.state]||[m.state,''];
 return `<div class="card ${m.state=='active'?'up':''}"><div class="row"><h3>${esc(m.name||m.username)}<small>حساب ادمین</small></h3><span class="b ${st[1]}">${st[0]}</span></div><div class="pg"><i style="width:${pct}%"></i></div>
 <div class="meta"><span>حجم مصرفی: <b>${fmtB(u)}</b> / <b>${m.limit_bytes?fmtB(m.limit_bytes):'نامحدود'}</b></span><span>باقی‌مانده: <b>${m.limit_bytes?fmtB(Math.max(0,m.limit_bytes-u)):'نامحدود'}</b></span>
 <span>انقضا: <b style="direction:rtl">${fmtD(m.expiry)}${dleft(m.expiry)}</b></span></div>
 ${m.state!='active'?'<div style="color:#f87171">حجم یا اعتبار حساب شما تمام شده؛ کلاینت‌های شما تا تمدید توسط مدیر غیرفعال‌اند.</div>':''}</div>`}
let CQ='',CP=1,CPS=20;
const rndName=()=>{const a='abcdefghjkmnpqrstuvwxyz23456789';return [...crypto.getRandomValues(new Uint8Array(8))].map(b=>a[b%a.length]).join('')};
function cliFiltered(){const k=CQ.trim().toLowerCase();return S.clients.filter(c=>(isA()||CF==='all'||(CF==='0'?!c.owner_id:String(c.owner_id)===CF))&&(!k||(c.name+' '+(c.note||'')+' '+(c.owner_id&&!isA()?admName(c.owner_id):'')+' '+c.links.map(l=>l.ip4).join(' ')).toLowerCase().includes(k)))}
function cliRow(c){const u=c.up_bytes+c.down_bytes,pct=c.limit_bytes?Math.min(100,u*100/c.limit_bytes):0,st=STL[c.state]||[c.state,''];
 const own=!isA()&&c.owner_id?`<span class="own" title="این کلاینت را ادمین ${esc(admName(c.owner_id))} ساخته است">ساخته‌شده توسط: ${esc(admName(c.owner_id))}</span>`:'';
 const tags=c.links.map(l=>`<span class="tag" title="${esc(l.ip4)}">${esc(l.ib_name)}</span>`).join('')||'<span class="mut sm">بدون اینباند</span>';
 return `<div class="cr2 ${c.state=='active'?'on':''}"><div class="c1"><b><span class="dot ${c.online?'on':''}" title="آخرین اتصال: ${ago(c.last_seen)}"></span><span class="nm">${esc(c.name)}</span>${own}</b>${c.note?`<small>${esc(c.note)}</small>`:''}<div class="tg">${tags}</div></div>
 <div class="c2"><div class="pg"><i style="width:${pct}%"></i></div><small>${fmtB(u)} / ${c.limit_bytes?fmtB(c.limit_bytes):'نامحدود'}</small></div>
 <div class="c3"><span class="b ${st[1]}">${st[0]}</span><small style="direction:rtl">${c.expiry?fmtD(c.expiry)+dleft(c.expiry):'بدون انقضا'}</small></div>
 <div class="c4 acts"><button class="s" onclick="subModal(${c.id})">ساب / QR</button><button class="s" onclick="editCli(${c.id})">ویرایش</button>
 <button class="s" onclick="act(()=>api('/clients/${c.id}/toggle','POST'))">${c.enabled?'غیرفعال':'فعال'}</button>
 <button class="s" onclick="act(()=>api('/clients/${c.id}/reset-traffic','POST'),'ترافیک ریست شد')">ریست</button>
 <button class="s d" onclick="delCli(${c.id},'${esc(c.name)}')">حذف</button></div></div>`}
function pager(total){const pages=Math.max(1,Math.ceil(total/CPS)),nums=[];
 for(let i=1;i<=pages;i++){if(i==1||i==pages||Math.abs(i-CP)<=1)nums.push(i);else if(nums[nums.length-1]!=='…')nums.push('…')}
 const nav=pages>1?`<button class="s" ${CP<=1?'disabled':''} onclick="goP(${CP-1})">قبلی</button>`+nums.map(n=>n==='…'?'<span class="mut">…</span>':`<button class="s ${n==CP?'cur':''}" onclick="goP(${n})">${n}</button>`).join('')+`<button class="s" ${CP>=pages?'disabled':''} onclick="goP(${CP+1})">بعدی</button>`:'';
 return `<div class="pgr"><span class="mut sm">${(CP-1)*CPS+1}–${Math.min(total,CP*CPS)} از ${total} کلاینت</span><div class="pgb">${nav}</div>
 <label class="mut sm">تعداد در هر صفحه <select class="fsel" onchange="CPS=+this.value;CP=1;$('#clist').innerHTML=cliList()">${[10,20,50,100].map(n=>`<option ${n==CPS?'selected':''}>${n}</option>`).join('')}</select></label></div>`}
function cliList(){const f=cliFiltered(),pages=Math.max(1,Math.ceil(f.length/CPS));if(CP>pages)CP=pages;
 if(!f.length)return `<div class="empty">${S.clients.length?'کلاینتی با این مشخصات پیدا نشد.':'کلاینتی وجود ندارد.'}</div>`;
 return `<div class="cl">${f.slice((CP-1)*CPS,CP*CPS).map(cliRow).join('')}</div>`+pager(f.length)}
function setQ(v){CQ=v;CP=1;$('#clist').innerHTML=cliList()}
function goP(n){CP=n;$('#clist').innerHTML=cliList();$('#ctool').scrollIntoView({behavior:'smooth',block:'start'})}
function cliHTML(){return (isA()?meCard():'')+`<div class="bar2" id="ctool"><div class="tl"><input id="cq" class="fsel srch" type="search" dir="auto" placeholder="جستجوی نام کلاینت…" value="${esc(CQ)}" oninput="setQ(this.value)" autocomplete="off">
 ${isA()||!S.admins.length?'':`<select class="fsel" onchange="CF=this.value;CP=1;render()"><option value="all">همه کلاینت‌ها</option><option value="0" ${CF==='0'?'selected':''}>مدیر اصلی</option>${S.admins.map(a=>`<option value="${a.id}" ${CF==String(a.id)?'selected':''}>ادمین: ${esc(a.username)}</option>`).join('')}</select>`}</div>
 <button class="p" onclick="newCli()">+ کلاینت جدید</button></div><div id="clist">${cliList()}</div>`}
const CLI=[{k:'name',l:'نام کلاینت',rtl:1},{k:'count',l:'تعداد (ساخت گروهی؛ نام‌ها شماره‌دار می‌شوند)',t:'number',create:1},
 {k:'note',l:'یادداشت',rtl:1},{k:'limit_gb',l:'محدودیت حجم (گیگابایت)',t:'number',h:'۰ = نامحدود'},
 {k:'reset_period',l:'ریست خودکار ترافیک',t:'select',opts:[['','هرگز'],['daily','روزانه'],['weekly','هفتگی'],['monthly','ماهانه (هر ۳۰ روز)']]}];
function linkBlock(ib,L){const v=L||{};const f=(k,l,ph)=>`<div class="fg"><label>${l}</label><input class="l_${k}" value="${esc(v[k]??'')}" placeholder="${ph||''}"></div>`;
 return `<div class="lk" data-ib="${ib.id}"><label class="chk"><input type="checkbox" class="lkc" ${L?'checked':''}> <b>${esc(ib.name)}</b> <span class="mut">${esc(ib.remark)}${ib.proto==='vless'?'':' · '+esc(ib.address4)}</span>${ib.proto==='l2tp'?' <span class="tag">L2TP</span>':''}${ib.proto==='ovpn'?' <span class="tag">OpenVPN</span>':''}${ib.proto==='vless'?' <span class="tag">VLESS</span>':''}${ib.node_id?` <span class="tag">${esc(nodName(ib.node_id))}</span>`:''}</label>
 <details ${isA()||ib.proto!=='wg'?'hidden':''}><summary>تنظیمات ویژه این کلاینت در این اینباند</summary><div class="g2">${f('ip4','IPv4 ثابت','خودکار')}${f('allowed_ips','AllowedIPs کلاینت','پیش‌فرض اینباند')}
 ${f('keepalive','Keepalive','پیش‌فرض اینباند (۰=خاموش)')}${f('dns','DNS','پیش‌فرض اینباند')}${f('mtu','MTU','پیش‌فرض اینباند')}${f('extra_allowed','AllowedIPs اضافه سمت سرور','مثلا 192.168.50.0/24')}</div></details></div>`}
function cliModal(title,c){const vals=c?{...c,limit_gb:c.limit_bytes?+(c.limit_bytes/1024**3).toFixed(3):0}:{limit_gb:0,count:1};
 const fields=CLI.filter(f=>!f.create||!c);
 const m=modal(`<h2>${title}</h2>${fields.map(f=>fieldHTML(f,vals,!!c)).join('')}
 <div class="fg"><label>تاریخ انقضا</label><input type="date" id="f_exp" value="${c&&c.expiry?new Date(c.expiry*1000).toISOString().slice(0,10):''}">
 <div style="margin-top:4px"><button class="s" type="button" data-d="30">+۳۰ روز</button> <button class="s" type="button" data-d="90">+۹۰ روز</button> <button class="s" type="button" data-d="0">نامحدود</button></div></div>
 <h4>اینباندها</h4>${S.inbounds.length?S.inbounds.map(ib=>{const L=c&&c.links.find(l=>l.inbound_id==ib.id);return linkBlock(ib,L?{...L,keepalive:L.keepalive<0?'':L.keepalive,mtu:L.mtu||''}:(!c&&ib.enabled?{}:null))}).join(''):'<div class="mut">اول یک اینباند بسازید.</div>'}
 <div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">${ic('save')}ذخیره</button></div>`);
 m.querySelectorAll('[data-d]').forEach(b=>b.onclick=()=>{const d=+b.dataset.d;const e=m.querySelector('#f_exp');if(!d){e.value='';return}const base=c&&c.expiry*1000>Date.now()?c.expiry*1000:Date.now();e.value=new Date(base+d*864e5).toISOString().slice(0,10)});
 m.querySelector('#mc').onclick=()=>m.remove();
 {const ni=m.querySelector('#f_name');if(ni){const w=document.createElement('div');w.style.cssText='display:flex;gap:8px;align-items:center';ni.parentNode.insertBefore(w,ni);w.appendChild(ni);ni.style.flex='1';ni.style.minWidth='0';
  const rb=document.createElement('button');rb.type='button';rb.className='s';rb.style.whiteSpace='nowrap';rb.textContent='🎲 رندوم';rb.onclick=()=>{ni.value=rndName()};w.appendChild(rb)}}
 m.querySelector('#ms').onclick=async()=>{const o=collect(fields,!!c);const ev=m.querySelector('#f_exp').value;o.expiry=ev?Math.floor(new Date(ev+'T23:59:59').getTime()/1000):0;
  o.links=[...m.querySelectorAll('.lk')].filter(b=>b.querySelector('.lkc').checked).map(b=>{const g=k=>b.querySelector('.l_'+k).value.trim();return{inbound_id:+b.dataset.ib,ip4:g('ip4'),allowed_ips:g('allowed_ips'),keepalive:g('keepalive'),dns:g('dns'),mtu:g('mtu'),extra_allowed:g('extra_allowed')}});
  if(await act(()=>api(c?'/clients/'+c.id:'/clients',c?'PUT':'POST',o),'ذخیره شد'))m.remove()}}
function newCli(){cliModal('کلاینت جدید',null)}
function editCli(id){cliModal('ویرایش کلاینت',S.clients.find(x=>x.id==id))}
function delCli(id,n){if(confirm(`کلاینت ${n} حذف شود؟`))act(()=>api('/clients/'+id,'DELETE'),'حذف شد')}
function subModal(id){const c=S.clients.find(x=>x.id==id);const u=c.sub_url;
 const m=modal(`<h2>اشتراک ${esc(c.name)}</h2><div class="fg"><label>لینک ساب (Hiddify / v2rayN / NekoBox / sing-box)</label><input readonly value="${esc(u)}" onclick="this.select()"></div>
 ${S.server.qr?`<img class="qr" src="/sub/${c.token}/link.svg" alt="QR">`:'<div class="mut">برای QR دستور pip install qrcode را اجرا کنید.</div>'}
 <div class="acts"><button class="s" id="b1">کپی لینک</button><button class="s" onclick="window.open('${esc(u)}?format=html')">صفحه اشتراک</button>
 <button class="s" onclick="window.open('${esc(u)}?format=conf')">همه کانفیگ‌ها (.conf)</button><button class="s" onclick="window.open('${esc(u)}?format=raw')">لینک‌های wireguard://</button></div>
 <h4>دانلود تک‌تک</h4><div class="acts">${c.links.filter(l=>l.proto==='wg'||l.proto==='ovpn').map(l=>`<a class="btn" href="/sub/${c.token}/${l.inbound_id}.${l.proto==='ovpn'?'ovpn':'conf'}">${esc(l.ib_name)}.${l.proto==='ovpn'?'ovpn':'conf'}</a>`).join('')||'<span class="mut">—</span>'}</div>
 ${c.links.filter(l=>l.proto==='vless').map(l=>`<h4>${esc(l.ib_name)} — VLESS</h4><div class="acts"><button class="btn" onclick="copy(this.dataset.v)" data-v="${esc(l.vlink||'')}">کپی لینک vless://</button></div>`).join('')}
 ${c.links.filter(l=>l.proto==='l2tp').map(l=>{const ib=S.inbounds.find(x=>x.id==l.inbound_id)||{};const cv=(k,v)=>`<span style="cursor:pointer" onclick="copy('${esc(v)}')">${k}: <b>${esc(v)}</b></span>`;
  return `<h4>${esc(l.ib_name)} — L2TP/IPsec</h4><div class="meta">${cv('Server',ib.endpoint||location.hostname)}${cv('Username',l.l2tp_user)}${cv('Password',l.l2tp_pass)}${cv('IPsec PSK',ib.psk||'')}</div>`}).join('')}
 <h4>امنیت</h4><div class="acts"><button class="s d" id="b2">ساخت لینک ساب جدید</button><button class="s d" id="b3">ساخت دوباره کلیدهای کلاینت</button></div>
 <div class="mfoot"><button class="s" id="x">بستن</button></div>`);
 m.querySelector('#b1').onclick=()=>copy(u);m.querySelector('#x').onclick=()=>m.remove();
 m.querySelector('#b2').onclick=async()=>{if(confirm('لینک قبلی از کار می‌افتد. ادامه؟')&&await act(()=>api('/clients/'+id+'/reset-token','POST'),'لینک جدید ساخته شد'))m.remove()};
 m.querySelector('#b3').onclick=async()=>{if(confirm('کلیدهای کلاینت عوض می‌شود و کانفیگ‌های قبلی کار نمی‌کنند. ادامه؟')&&await act(()=>api('/clients/'+id+'/regen-keys','POST'),'کلیدها عوض شد'))m.remove()}}
/* ---------- وضعیت ---------- */
let SY=null,SYV='srv',SHOWIP=false,STI=null;
const dur=s=>{s=Math.floor(s||0);const d=Math.floor(s/86400),h=Math.floor(s%86400/3600),m=Math.floor(s%3600/60);return d?`${d} روز و ${h} ساعت`:h?`${h} ساعت و ${m} دقیقه`:`${m} دقیقه`};
async function staPoll(){try{SY=await api('/sys');staPaint()}catch(e){}}
function staStart(){staStop();if(SY)staPaint();staPoll();STI=setInterval(staPoll,5000)}
function staStop(){if(STI){clearInterval(STI);STI=null}}
function staHTML(){return '<div id="sta"><div class="empty">در حال بارگذاری…</div></div>'}
function lchart(k,ser,fmt,fix){const W=600,H=150,n=Math.max(2,...ser.map(s=>s.d.length)),mx=fix||Math.max(1,...ser.flatMap(s=>s.d))*1.12;
 const X=(i,len)=>((n-len+i)*W/(n-1)).toFixed(1),Y=v=>(H-3-(Math.min(v,mx)/mx)*(H-8)).toFixed(1);
 const defs=ser.map((s,i)=>`<linearGradient id="${k}${i}" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="${s.c}" stop-opacity=".32"/><stop offset="1" stop-color="${s.c}" stop-opacity="0"/></linearGradient>`).join('');
 const grid=[.25,.5,.75].map(f=>`<line x1="0" x2="${W}" y1="${(H*f).toFixed(1)}" y2="${(H*f).toFixed(1)}" stroke="#223356" stroke-dasharray="3 5" vector-effect="non-scaling-stroke"/>`).join('');
 const body=ser.map((s,i)=>{if(s.d.length<2)return '';const pts=s.d.map((v,j)=>X(j,s.d.length)+','+Y(v)).join(' L');
  return `<path d="M${pts} L${W},${H} L${X(0,s.d.length)},${H}Z" fill="url(#${k}${i})"/><path d="M${pts}" fill="none" stroke="${s.c}" stroke-width="2" stroke-linejoin="round" vector-effect="non-scaling-stroke"/>`}).join('');
 return `<div class="ch2" dir="ltr"><span class="mx">${fmt(mx)}</span><svg viewBox="0 0 ${W} ${H}" preserveAspectRatio="none"><defs>${defs}</defs>${grid}${body}</svg></div>`}
function gauge(label,pct,main,sub){const r=38,C=2*Math.PI*r,col=pct>=90?'var(--bad)':pct>=70?'var(--warn)':'var(--ok)';
 return `<div class="gc"><svg viewBox="0 0 100 100" class="gr"><circle cx="50" cy="50" r="${r}" fill="none" stroke="#1b2a47" stroke-width="9"/><circle cx="50" cy="50" r="${r}" fill="none" stroke="${col}" stroke-width="9" stroke-linecap="round" stroke-dasharray="${(C*pct/100).toFixed(1)} ${C.toFixed(1)}" transform="rotate(-90 50 50)"/><text x="50" y="56" text-anchor="middle" class="gt">${Math.round(pct)}%</text></svg>
 <div><span class="gl">${label}</span><b>${main}</b><small>${sub}</small></div></div>`}
function staPaint(){const e=$('#sta'),y=SY;if(!e||!y)return;
 const h=y.hist||[],ls=h[h.length-1]||{cpu:0,ram:0,rx:0,tx:0,wrx:0,wtx:0,tcp:0,udp:0},col=k=>h.map(x=>x[k]);
 const m=y.mem,mu=m.total-m.avail,sw=m.swap_total-m.swap_free,pc=(a,b)=>b?Math.min(100,a*100/b):0;
 const span=h.length>1?Math.max(1,Math.round((h[h.length-1].t-h[0].t)/60)):0,wg=SYV==='wg';
 const U=wg?'wrx':'tx',D=wg?'wtx':'rx',lu=wg?'آپلود کاربران':'ارسال',ld=wg?'دانلود کاربران':'دریافت';
 const tot=wg?[y.net.wrx,y.net.wtx]:[y.net.tx,y.net.rx],pk=Math.max(0,...h.map(x=>x[U]+x[D]));
 const sp=v=>fmtB(v)+'/s',tt=ls.tcp+ls.udp;
 e.innerHTML=`<div class="sg4">
 ${gauge('پردازنده',ls.cpu,'Load '+y.load.map(v=>v.toFixed(2)).join(' · '),`${y.cores} هسته${y.mhz?' · '+(y.mhz/1000).toFixed(2)+' GHz':''}`)}
 ${gauge('حافظه (RAM)',pc(mu,m.total),fmtB(mu),'از '+fmtB(m.total))}
 ${gauge('Swap',pc(sw,m.swap_total),m.swap_total?fmtB(sw):'—',m.swap_total?'از '+fmtB(m.swap_total):'فعال نیست')}
 ${gauge('دیسک',pc(y.disk.used,y.disk.total),fmtB(y.disk.used),`آزاد ${fmtB(y.disk.free)} از ${fmtB(y.disk.total)}`)}</div>
 <div class="card"><div class="row"><div class="ch" style="margin:0">${ic('pulse')}ترافیک و سرعت شبکه</div>
  <div class="seg"><button class="${wg?'':'on'}" onclick="SYV='srv';staPaint()">کل سرور</button><button class="${wg?'on':''}" onclick="SYV='wg';staPaint()">وایرگارد</button></div></div>
  <div class="pills"><span class="pl a">↓ ${ld}: ${sp(ls[D])}</span><span class="pl b2">↑ ${lu}: ${sp(ls[U])}</span></div>
  ${lchart('tr',[{d:col(D),c:'#38bdf8'},{d:col(U),c:'#a78bfa'}],sp)}
  <div class="trio"><div><small>${lu} (مجموع)</small><b>${fmtB(tot[0])}</b></div><div><small>${ld} (مجموع)</small><b>${fmtB(tot[1])}</b></div><div><small>اوج در ${span} دقیقه اخیر</small><b>${sp(pk)}</b></div></div></div>
 <div class="sg2" style="margin-top:14px"><div class="card"><div class="ch">${ic('server')}تاریخچه CPU و RAM <span class="mut sm">(${span} دقیقه اخیر)</span></div>
  <div class="pills"><span class="pl" style="background:rgba(245,158,11,.14);color:#fbbf24">CPU ${ls.cpu.toFixed(1)}%</span><span class="pl" style="background:rgba(34,197,94,.14);color:#4ade80">RAM ${ls.ram.toFixed(1)}%</span></div>
  ${lchart('hs',[{d:col('cpu'),c:'#f59e0b'},{d:col('ram'),c:'#22c55e'}],v=>Math.round(v)+'%',100)}</div>
 <div class="card"><div class="ch">${ic('globe')}اتصال‌های باز</div><div style="font-size:26px;font-weight:700;line-height:1.3">${tt} <small class="mut" style="font-size:13px;font-weight:400">سوکت</small></div>
  <div class="split"><i style="width:${tt?ls.tcp*100/tt:0}%;background:#60a5fa"></i><i style="width:${tt?ls.udp*100/tt:0}%;background:#f472b6"></i></div>
  <div class="pills" style="margin-top:0"><span class="pl" style="background:rgba(96,165,250,.14);color:#93c5fd">TCP ${ls.tcp}</span><span class="pl" style="background:rgba(244,114,182,.14);color:#f9a8d4">UDP ${ls.udp}</span></div>
  ${lchart('sk',[{d:h.map(x=>x.tcp+x.udp),c:'#60a5fa'}],v=>Math.round(v))}</div></div>
 <div class="sg2"><div class="card"><div class="ch">${ic('shield')}وایرگارد</div><div class="kv">
  <div><small>اینباند فعال</small><b>${y.wg.up} / ${y.wg.total}</b></div><div><small>کلاینت‌ها</small><b>${y.wg.clients}</b></div>
  <div><small>آنلاین</small><b>${y.wg.online}</b></div><div><small>مصرف کل کلاینت‌ها</small><b>${fmtB(y.wg.usage)}</b></div></div></div>
 <div class="card"><div class="ch">${ic('info')}سرور و پنل</div><div class="kv">
  <div><small>روشن بودن سرور</small><b style="direction:rtl">${dur(y.uptime)}</b></div><div><small>اجرای پنل</small><b style="direction:rtl">${dur(y.panel_up)}</b></div>
  <div><small>RAM پنل</small><b>${fmtB(y.panel.rss)}</b></div><div><small>Thread پنل</small><b>${y.panel.threads}</b></div>
  <div><small>هاست</small><b>${esc(y.host)}</b></div><div><small>کرنل</small><b>${esc(y.kernel)}</b></div></div>
  ${y.model?`<div class="mut sm" style="direction:ltr;text-align:left;margin-top:8px">${esc(y.model)}</div>`:''}</div></div>
 <div class="card"><div class="row"><div class="ch" style="margin:0">${ic('globe')}آدرس‌های سرور</div><button class="s" onclick="SHOWIP=!SHOWIP;staPaint()">${SHOWIP?'مخفی کردن':'نمایش'}</button></div>
  <div class="ipl ${SHOWIP?'':'hid'}" style="margin-top:12px">${y.ips.map(a=>`<span>${esc(a.ip)} <small class="mut">${esc(a.i)}</small></span>`).join('')||'<span class="mut">—</span>'}</div></div>`}
/* ---------- ادمین‌ها ---------- */
function admHTML(){return `<div class="bar2"><span></span><button class="p" onclick="admModal(null)">+ ادمین جدید</button></div>`+
 (S.admins.map(a=>{const pct=a.limit_bytes?Math.min(100,a.used_bytes*100/a.limit_bytes):0,st=STL[a.state]||[a.state,''];
 return `<article class="card ${a.state=='active'?'up':''}"><div class="row"><h3><span class="dot ${a.online?'on':''}"></span>${esc(a.username)}<small>${esc(a.name)} ${esc(a.note)}</small></h3><span class="b ${st[1]}">${st[0]}</span></div>
 <div class="pg"><i style="width:${pct}%"></i></div>
 <div class="meta"><span>مصرف: <b>${fmtB(a.used_bytes)}</b> / <b>${a.limit_bytes?fmtB(a.limit_bytes):'نامحدود'}</b></span><span>باقی‌مانده: <b>${a.limit_bytes?fmtB(Math.max(0,a.limit_bytes-a.used_bytes)):'نامحدود'}</b></span>
 <span>انقضا: <b style="direction:rtl">${fmtD(a.expiry)}${dleft(a.expiry)}</b></span><span>کلاینت‌ها: <b>${a.clients}</b> (آنلاین ${a.online})</span><span>آخرین ورود: <b style="direction:rtl">${ago(a.last_login)}</b></span></div>
 <div class="acts"><button class="s" onclick="renewAdm(${a.id})">تمدید / افزودن</button><button class="s" onclick="admModal(${a.id})">ویرایش</button>
 <button class="s" onclick="if(confirm('مصرف حجم این ادمین صفر شود؟'))act(()=>api('/admins/${a.id}/reset-traffic','POST'),'حجم ریست شد')">ریست حجم</button>
 <button class="s" onclick="CF='${a.id}';TAB='cli';render()">کلاینت‌ها</button>
 <button class="s" onclick="act(()=>api('/admins/${a.id}/toggle','POST'))">${a.enabled?'غیرفعال‌سازی':'فعال‌سازی'}</button>
 <button class="s d" onclick="delAdm(${a.id},'${esc(a.username)}')">حذف</button></div></article>`}).join('')||'<div class="empty">هنوز ادمینی نساخته‌اید.</div>')}
function admModal(id){const a=id?S.admins.find(x=>x.id==id):null;const v=a||{username:'',name:'',note:'',limit_bytes:0,expiry:0};const gb=v.limit_bytes?+(v.limit_bytes/1024**3).toFixed(3):0;
 const m=modal(`<h2>${a?'ویرایش ادمین':'ادمین جدید'}</h2>
 <div class="fg"><label>نام کاربری ورود</label><input id="ad_u" value="${esc(v.username)}" autocomplete="off"></div>
 <div class="fg"><label>رمز عبور${a?' (خالی = بدون تغییر)':''}</label><input id="ad_p" autocomplete="new-password" placeholder="حداقل ۸ کاراکتر"><div style="margin-top:4px"><button class="s" type="button" id="ad_r">ساخت رمز تصادفی</button></div></div>
 <div class="fg"><label>نام نمایشی</label><input id="ad_n" value="${esc(v.name)}" style="direction:rtl;text-align:right"></div>
 <div class="fg"><label>یادداشت</label><input id="ad_t" value="${esc(v.note)}" style="direction:rtl;text-align:right"></div>
 <div class="fg"><label>سقف حجم کل (گیگابایت)</label><input id="ad_g" type="number" step="any" value="${gb}"><small>۰ = نامحدود. ترافیک مصرفی همهٔ کلاینت‌های این ادمین از این سقف کم می‌شود؛ با تمام‌شدن آن، کلاینت‌هایش قطع می‌شوند.</small></div>
 <div class="fg"><label>تاریخ انقضا</label><input type="date" id="ad_e" value="${v.expiry?new Date(v.expiry*1000).toISOString().slice(0,10):''}"><small>خالی = نامحدود. بعد از انقضا کلاینت‌های ادمین قطع می‌شوند.</small>
 <div style="margin-top:4px"><button class="s" type="button" data-d="30">+۳۰ روز</button> <button class="s" type="button" data-d="90">+۹۰ روز</button> <button class="s" type="button" data-d="0">نامحدود</button></div></div>
 <div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">${ic('save')}ذخیره</button></div>`);
 m.querySelector('#ad_r').onclick=()=>{m.querySelector('#ad_p').value=[...crypto.getRandomValues(new Uint8Array(12))].map(b=>'abcdefghjkmnpqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ23456789'[b%55]).join('')};
 m.querySelectorAll('[data-d]').forEach(b=>b.onclick=()=>{const d=+b.dataset.d,e=m.querySelector('#ad_e');if(!d){e.value='';return}const base=a&&a.expiry*1000>Date.now()?a.expiry*1000:Date.now();e.value=new Date(base+d*864e5).toISOString().slice(0,10)});
 m.querySelector('#mc').onclick=()=>m.remove();
 m.querySelector('#ms').onclick=async()=>{const ev=m.querySelector('#ad_e').value;const o={username:m.querySelector('#ad_u').value.trim(),password:m.querySelector('#ad_p').value,name:m.querySelector('#ad_n').value,note:m.querySelector('#ad_t').value,limit_gb:m.querySelector('#ad_g').value,expiry:ev?Math.floor(new Date(ev+'T23:59:59').getTime()/1000):0};
  if(await act(()=>api(a?'/admins/'+a.id:'/admins',a?'PUT':'POST',o),'ذخیره شد'))m.remove()}}
function renewAdm(id){const a=S.admins.find(x=>x.id==id);
 formModal('تمدید / افزودن — '+esc(a.username),[{s:`وضعیت فعلی: مصرف ${fmtB(a.used_bytes)} از ${a.limit_bytes?fmtB(a.limit_bytes):'نامحدود'} · انقضا ${fmtD(a.expiry)}`},
  {k:'add_gb',l:'افزودن حجم (گیگابایت)',t:'number',h:'به سقف حجم فعلی اضافه می‌شود'},
  {k:'add_days',l:'افزودن زمان (روز)',t:'number',h:'به تاریخ انقضای فعلی اضافه می‌شود؛ اگر منقضی شده یا نامحدود بوده، از امروز شمرده می‌شود'},
  {k:'reset_usage',l:'ریست حجم مصرفی (مصرف از صفر شروع شود)',t:'check'},
  {k:'reset_time',l:'ریست زمان (به‌جای افزودن، روزهای بالا از همین الان شمرده شود)',t:'check'}],{add_gb:0,add_days:0},false,
  o=>act(()=>api('/admins/'+id+'/renew','POST',o),'انجام شد'))}
function delAdm(id,n){if(!confirm(`ادمین ${n} حذف شود؟`))return;const dc=confirm('کلاینت‌های این ادمین هم حذف شوند؟\nتأیید = حذف کلاینت‌ها   |   انصراف = انتقال به مدیر اصلی');act(()=>api('/admins/'+id,'DELETE',{delete_clients:dc}),'حذف شد')}
/* ---------- تنظیمات ---------- */
function setHTML(){const s=S.settings,p=S.panel,sv=S.server;return `
${p.default_pass?`<div class="card" style="border-inline-start:4px solid var(--bad)"><b>هشدار امنیتی:</b> رمز پیش‌فرض داخل فایل هنوز فعال است. همین حالا از «حساب مدیر» عوضش کن.</div>`:''}
${p.restart_needed?`<div class="card" style="border-inline-start:4px solid var(--warn)">تغییر پورت/HTTPS ذخیره شده ولی هنوز اعمال نشده. <button class="p" onclick="restartPanel()">ری‌استارت پنل</button></div>`:''}
<div class="sgrid"><div class="card"><div class="ch">${ic('globe')}دامنه، پورت و HTTPS پنل</div>
 <div class="fg"><label>دامنه پنل</label><input id="p_dom" value="${esc(p.domain)}" placeholder="panel.example.com"><small>رکورد A دامنه باید به IP همین سرور اشاره کند. لینک‌های ساب با این دامنه ساخته می‌شوند.</small></div>
 <div class="g2"><div class="fg"><label>پورت پنل</label><input id="p_port" type="number" value="${p.port}"></div>
 <div class="fg"><label>مسیر مخفی (اختیاری)</label><input id="p_path" value="${esc(p.path)}" placeholder="مثلا x7k2q9"></div></div>
 <div class="fg"><label>مسیر فایل گواهی (fullchain.pem)</label><input id="p_cert" value="${esc(p.cert)}" placeholder="/etc/letsencrypt/live/panel.example.com/fullchain.pem"></div>
 <div class="fg"><label>مسیر کلید خصوصی (privkey.pem)</label><input id="p_key" value="${esc(p.key)}"></div>
 <div class="fg"><label>فقط این IPها به پنل دسترسی داشته باشند (اختیاری)</label><input id="p_allow" value="${esc(p.allowed_ips)}" placeholder="1.2.3.4, 10.0.0.0/8"><small>لینک‌های ساب مشمول این محدودیت نیستند. پشت پروکسی معکوس از این گزینه استفاده نکن. اگر قفل شدی: python3 sepipanel.py --reset</small></div>
 <div class="acts"><button class="p" onclick="savePanel()">${ic('save')}ذخیره تغییرات</button><button class="s" onclick="restartPanel()">ری‌استارت پنل</button></div>
 <h4>گواهی رایگان Let's Encrypt</h4>
 <div class="fg"><label>ایمیل</label><input id="p_mail" placeholder="you@example.com"></div>
 <button class="s" onclick="issueCert()" ${p.certbot?'':'disabled'}>دریافت گواهی با certbot</button>
 <div><small class="mut">${p.certbot?'پورت 80 باید آزاد باشد. بعد از دریافت، پنل را ری‌استارت کن.':'certbot نصب نیست: apt install certbot'}</small></div></div>
<div class="card"><div class="ch">${ic('shield')}حساب مدیر</div>
 <div class="fg"><label>رمز فعلی</label><input id="a_cur" type="password" autocomplete="current-password"></div>
 <div class="fg"><label>نام کاربری</label><input id="a_user" value="${esc(p.user)}"></div>
 <div class="fg"><label>رمز جدید (حداقل ۱۰ کاراکتر؛ خالی = بدون تغییر)</label><input id="a_new" type="password" autocomplete="new-password"></div>
 <button class="p" onclick="saveAcct()">${ic('save')}ذخیره تغییرات</button> <small class="mut">بعد از تغییر، نشست‌های دیگر بسته می‌شوند.</small></div>
<div class="card"><div class="ch">${ic('link')}تنظیمات اشتراک</div>
 <div class="fg"><label>آدرس عمومی پنل برای لینک ساب (اختیاری)</label><input id="s_u" value="${esc(s.public_url)}" placeholder="https://panel.example.com"><small>خالی = از دامنه‌ی بالا یا آدرس فعلی ساخته می‌شود. پشت nginx/کلودفلر پر کن.</small></div>
 <div class="fg"><label>عنوان اشتراک</label><input id="s_t" value="${esc(s.sub_title)}"></div>
 <div class="fg"><label>کانال تلگرام (نمایش در صفحهٔ ساب؛ اختیاری)</label><input id="s_tg" dir="ltr" value="${esc(s.sub_telegram||'')}" placeholder="sepiamDigee"></div>
 <div class="fg"><label>بازه آپدیت خودکار در اپ کلاینت (ساعت)</label><input id="s_i" type="number" value="${s.update_interval}"></div>
 <button class="p" onclick="saveSet()">${ic('save')}ذخیره تغییرات</button></div>
<div class="card"><div class="ch">${ic('info')}اطلاعات سرور</div><div class="meta"><span>WireGuard: <b>${esc(sv.wg||'نصب نیست')}</b></span><span>AmneziaWG: <b>${esc(sv.awg||'نصب نیست')}</b></span><span>اینترفیس خروجی: <b>${esc(sv.nat_iface)}</b></span><span>QR: <b>${sv.qr?'فعال':'نصب نیست'}</b></span><span>HTTPS: <b>${p.tls_on?'فعال':'خاموش'}</b></span></div></div></div>`}
function saveSet(){act(()=>api('/settings','PUT',{public_url:$('#s_u').value,sub_title:$('#s_t').value,sub_telegram:$('#s_tg').value,update_interval:$('#s_i').value}),'ذخیره شد')}
function savePanel(){act(()=>api('/panel','PUT',{domain:$('#p_dom').value,port:$('#p_port').value,path:$('#p_path').value,cert:$('#p_cert').value,key:$('#p_key').value,allowed_ips:$('#p_allow').value}),'ذخیره شد')}
async function restartPanel(){if(!confirm('پنل ری‌استارت می‌شود و به آدرس جدید می‌روید. ادامه؟'))return;try{const r=await api('/panel/restart','POST');toast('در حال ری‌استارت…');setTimeout(()=>{location.href=r.url},3500)}catch(e){toast(e.message,1)}}
function issueCert(){toast('در حال گرفتن گواهی… (تا ۲ دقیقه)');act(()=>api('/panel/cert','POST',{domain:$('#p_dom').value,email:$('#p_mail').value}),'گواهی ساخته شد؛ پنل را ری‌استارت کنید')}
async function saveAcct(){try{await api('/panel/account','POST',{current:$('#a_cur').value,user:$('#a_user').value,password:$('#a_new').value});toast('ذخیره شد');$('#a_cur').value='';$('#a_new').value='';await load()}catch(e){toast(e.message,1)}}
load();setInterval(()=>{if(S&&TAB!=='set'&&!document.querySelector('.ov')&&TAB!=='sta'&&document.activeElement!==$('#cq'))load()},20000);
</script></body></html>"""


# ------------------------------ CLI (برای دستور sepipanel در ترمینال) ------------------------------
def cli_url(host=""):
    c = panel_cfg(); tls = bool(tls_files())
    h = c["domain"] or host or "SERVER_IP"
    if ":" in h and not h.startswith("["):
        h = f"[{h}]"
    u = f"{'https' if tls else 'http'}://{h}"
    if (tls and c["port"] != 443) or (not tls and c["port"] != 80):
        u += f":{c['port']}"
    return u + "/" + (c["path"] + "/" if c["path"] else "")


def cli(args):
    cmd = args[0] if args else "info"
    a = args[1:]
    c = panel_cfg()
    try:
        if cmd == "info":
            tls = tls_files()
            print(f"URL            : {cli_url(os.environ.get('WG_IP', ''))}")
            print(f"Username       : {admin_user()}")
            print(f"Password       : {'(changed - not shown)' if setting('admin_hash') else ADMIN_PASS + '  (default from file)'}")
            print(f"Port           : {c['port']}")
            print(f"Domain         : {c['domain'] or '-'}")
            print(f"Secret path    : /{c['path']}" if c["path"] else "Secret path    : -")
            print(f"HTTPS          : {'ON  (' + tls[0] + ')' if tls else 'OFF'}")
            print(f"Allowed IPs    : {c['allowed_ips'] or 'any'}")
            print(f"Inbounds       : {q('SELECT COUNT(*) n FROM inbounds', (), True)['n']}")
            print(f"Clients        : {q('SELECT COUNT(*) n FROM clients', (), True)['n']}")
        elif cmd == "get":
            k = a[0] if a else ""
            tls = bool(tls_files())
            vals = dict(port=c["port"], domain=c["domain"], path=c["path"], tls="1" if tls else "0",
                        user=admin_user(), default_pass="0" if setting("admin_hash") else "1",
                        cert=c["cert"], allowed=c["allowed_ips"], url=cli_url(os.environ.get("WG_IP", "")))
            print(vals.get(k, ""))
        elif cmd == "set-port":
            p = num(a[0] if a else "", 0, 1, 65535, "port")
            if not p:
                raise Err("usage: set-port <1-65535>")
            if p != c["port"] and not port_free(p):
                raise Err(f"port {p} is already in use on this server")
            set_setting("panel_port", p); print(f"Panel port set to {p}")
        elif cmd == "set-domain":
            d = (a[0] if a else "").strip().lower()
            if d in ("-", "none"):
                d = ""
            if d and not re.fullmatch(r"[a-z0-9]([a-z0-9.\-]*[a-z0-9])?", d):
                raise Err("invalid domain")
            set_setting("panel_domain", d); print(f"Domain set to: {d or '(none)'}")
        elif cmd == "set-path":
            p = (a[0] if a else "").strip().strip("/")
            if p == "random":
                p = secrets.token_hex(6)
            if p in ("-", "none"):
                p = ""
            if p and (not re.fullmatch(r"[A-Za-z0-9_\-]{3,40}", p) or p in ("api", "sub")):
                raise Err("path must be 3-40 chars of A-Z a-z 0-9 _ - (and not 'api' or 'sub')")
            set_setting("panel_path", p); print(f"Secret path set to: /{p}" if p else "Secret path removed")
        elif cmd in ("set-user", "set-pass"):
            v = a[0] if a else ""
            if cmd == "set-user":
                if not re.fullmatch(r"[A-Za-z0-9_.\-]{3,32}", v):
                    raise Err("username must be 3-32 chars of A-Z a-z 0-9 _ . -")
                set_setting("admin_user", v)
            else:
                if len(v) < 10 or v == ADMIN_PASS:
                    raise Err("password must be at least 10 characters and not the default")
                set_setting("admin_hash", hash_pw(v))
            set_setting("sess_ver", secrets.token_hex(8)); print("Saved. All logged-in sessions were invalidated.")
        elif cmd == "set-cert":
            if len(a) < 2:
                raise Err("usage: set-cert <fullchain.pem> <privkey.pem>")
            try:
                ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER).load_cert_chain(a[0], a[1])
            except Exception as e:
                raise Err(f"certificate/key not valid: {e}")
            set_setting("tls_cert", a[0]); set_setting("tls_key", a[1]); print("HTTPS enabled")
        elif cmd == "clear-cert":
            set_setting("tls_cert", ""); set_setting("tls_key", ""); print("HTTPS disabled")
        elif cmd == "set-allow":
            v = (a[0] if a else "").strip()
            v = "" if v in ("-", "none", "any") else check_cidrs(v, "allowed IPs")
            set_setting("allowed_ips", v); print(f"Allowed IPs: {v or 'any'}")
        elif cmd == "reset":
            for k in ("panel_port", "panel_domain", "panel_path", "tls_cert", "tls_key", "allowed_ips", "admin_user", "admin_hash"):
                x("DELETE FROM settings WHERE k=?", (k,))
            set_setting("sess_ver", secrets.token_hex(8))
            print(f"Security settings reset. Login: {ADMIN_USER} / password written in the file, port {PANEL_PORT}.")
        else:
            raise Err(f"unknown command: {cmd}")
    except Err as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    return 0


# ------------------------------ اجرا ------------------------------
def main():
    if "--cli" in sys.argv:
        sys.exit(cli(sys.argv[sys.argv.index("--cli") + 1:]))
    if "--reset" in sys.argv:
        for k in ("panel_port", "panel_domain", "panel_path", "tls_cert", "tls_key", "allowed_ips", "admin_user", "admin_hash"):
            x("DELETE FROM settings WHERE k=?", (k,))
        set_setting("sess_ver", secrets.token_hex(8))
        print(f"تنظیمات امنیتی ریست شد. ورود با {ADMIN_USER} و رمز داخل فایل، پورت {PANEL_PORT}.")
        return
    if os.geteuid() != 0 and os.name != "nt":
        log.warning("برای مدیریت اینترفیس‌های وایرگارد باید با root اجرا شود")
    c = panel_cfg()
    tls = tls_files()
    if (c["cert"] or c["key"]) and not tls:
        log.warning("فایل گواهی/کلید پیدا نشد؛ پنل بدون HTTPS بالا می‌آید")
    RUN.update(port=c["port"], tls=bool(tls), cert_mtime=os.path.getmtime(tls[0]) if tls else 0)
    app.config["SESSION_COOKIE_SECURE"] = bool(tls)
    threading.Thread(target=reconcile, daemon=True).start()
    threading.Thread(target=stats_loop, daemon=True).start()
    threading.Thread(target=sys_loop, daemon=True).start()
    threading.Thread(target=node_loop, daemon=True).start()
    log.info("SepiPanel روی %s://%s:%s/%s", "https" if tls else "http", PANEL_HOST, c["port"], c["path"])
    app.run(host=PANEL_HOST, port=c["port"], threaded=True, ssl_context=tls)


if __name__ == "__main__":
    main()

# ---------------------------------------------------------------------------
# اجرای دائمی (systemd) — فایل /etc/systemd/system/sepipanel.service
#   [Unit]
#   Description=SepiPanel
#   After=network-online.target
#   [Service]
#   WorkingDirectory=/opt/sepipanel
#   ExecStart=/usr/bin/python3 /opt/sepipanel/sepipanel.py
#   Restart=always
#   [Install]
#   WantedBy=multi-user.target
# سپس: systemctl daemon-reload && systemctl enable --now sepipanel
# پیشنهاد: پشت nginx/caddy با HTTPS بگذارید و PUBLIC_URL را تنظیم کنید.
# ---------------------------------------------------------------------------
