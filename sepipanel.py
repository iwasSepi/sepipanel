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
import os, re, io, sys, json, time, html, base64, secrets, sqlite3, hmac, hashlib, shutil, socket, ssl, ipaddress, subprocess, threading, logging
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
""")


def ensure_cols(table, cols):
    have = {r["name"] for r in _db.execute(f"PRAGMA table_info({table})")}
    for c, d in cols.items():
        if c not in have:
            _db.execute(f"ALTER TABLE {table} ADD COLUMN {c} {d}")


ensure_cols("inbounds", {"obf": "TEXT DEFAULT ''", "exclude_sub": "INTEGER DEFAULT 0"})
ensure_cols("clients", {"reset_period": "TEXT DEFAULT ''", "last_reset": "INTEGER DEFAULT 0", "owner_id": "INTEGER DEFAULT 0"})
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
           "auto_rules", "nat_iface", "use_psk", "client_allowed_ips", "client_keepalive", "client_mtu", "obf", "exclude_sub"]


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
                address6_hint=f"fd42:42:{i}::1/64", exclude_sub=0, obf_enabled=0, obf={}, obf_ver="3")


def parse_inbound(d, cur=None):
    cid = cur["id"] if cur else 0
    name = str(d.get("name", "")).strip()
    if not re.fullmatch(r"[A-Za-z0-9_=+.\-]{1,15}", name):
        raise Err("نام اینترفیس باید ۱ تا ۱۵ حرف انگلیسی/عدد/_ - . باشد")
    if q("SELECT 1 FROM inbounds WHERE name=? AND id!=?", (name, cid), True):
        raise Err("این نام اینترفیس قبلاً استفاده شده")
    port = num(d.get("port"), 0, 1, 65535, "پورت")
    if not port:
        raise Err("پورت لازم است")
    if q("SELECT 1 FROM inbounds WHERE port=? AND id!=?", (port, cid), True):
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
    return dict(
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


def build_conf(c, ci, ib):
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


# ------------------------------ اعمال روی سیستم ------------------------------
def iface_up(ib):
    return run([tools(ib)[0], "show", ib["name"]])[0] == 0


def teardown(ib):
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
    for ib in ibs:
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
    for ib in q("SELECT id FROM inbounds"):
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


def _guard(super_only):
    def deco(fn):
        @wraps(fn)
        def w(*a, **k):
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


@app.errorhandler(Err)
def on_err(e):
    return jsonify(error=str(e)), 400


@app.errorhandler(Exception)
def on_exc(e):
    from werkzeug.exceptions import HTTPException
    if isinstance(e, HTTPException):
        return e
    log.exception("unhandled")
    return jsonify(error=f"خطای داخلی: {e}"), 500


def body():
    return request.get_json(silent=True) or {}


def ser_inbound(r, ups):
    d = {k: r[k] for k in r.keys() if k != "private_key"}
    d["obf"] = obf_of(r); d["awg"] = is_awg(r); d["obf_enabled"] = 1 if is_awg(r) else 0
    d["up"] = r["name"] in ups
    d["clients"] = q("SELECT COUNT(*) n FROM client_inbound WHERE inbound_id=?", (r["id"],), True)["n"]
    return d


def ser_client(c):
    links = q("""SELECT ci.*, ib.name AS ib_name FROM client_inbound ci JOIN inbounds ib ON ib.id=ci.inbound_id
                 WHERE ci.client_id=? ORDER BY ib.id""", (c["id"],))
    d = {k: c[k] for k in ("id", "name", "token", "enabled", "reason", "public_key", "limit_bytes", "up_bytes",
                           "down_bytes", "expiry", "note", "created", "last_seen", "reset_period", "owner_id")}
    d["state"] = client_state(c)
    d["sub_url"] = f"{base_url()}/sub/{c['token']}"
    d["online"] = any(l["last_hs"] and now() - l["last_hs"] < 180 for l in links)
    d["links"] = [dict(inbound_id=l["inbound_id"], ib_name=l["ib_name"], ip4=l["ip4"], ip6=l["ip6"],
                       allowed_ips=l["allowed_ips"], keepalive=l["keepalive"], dns=l["dns"], mtu=l["mtu"],
                       extra_allowed=l["extra_allowed"], last_hs=l["last_hs"], endpoint=l["endpoint"]) for l in links]
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


def state_super():
    ups = set()
    for t in ("wg", "awg"):
        rc, o, _ = run([t, "show", "interfaces"], timeout=10)
        if rc == 0:
            ups |= set(o.split())
    rc2, ver, _ = run(["wg", "--version"], timeout=5)
    rc3, aver, _ = run(["awg", "--version"], timeout=5)
    return jsonify(
        inbounds=[ser_inbound(r, ups) for r in q("SELECT * FROM inbounds ORDER BY id")],
        clients=[ser_client(c) for c in q("SELECT * FROM clients ORDER BY id DESC")],
        settings=dict(public_url=setting("public_url"), sub_title=setting("sub_title", "WireGuard"), sub_telegram=setting("sub_telegram", ""),
                      update_interval=int(setting("update_interval", "12") or 12)),
        role="super", admins=[ser_admin(a) for a in q("SELECT * FROM admins ORDER BY id DESC")],
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
    ups = set()
    for t in ("wg", "awg"):
        rc, o, _ = run([t, "show", "interfaces"], timeout=10)
        if rc == 0:
            ups |= set(o.split())
    ibs = [dict(id=r["id"], name=r["name"], remark=r["remark"], address4=r["address4"], awg=is_awg(r), enabled=1,
                up=r["name"] in ups, exclude_sub=r["exclude_sub"])
           for r in q("SELECT * FROM inbounds WHERE enabled=1 ORDER BY id")]
    return jsonify(role="admin", inbounds=ibs, me=ser_admin(a), settings={}, admins=[],
                   clients=[ser_client(c) for c in q("SELECT * FROM clients WHERE owner_id=? ORDER BY id DESC", (g.aid,))],
                   panel=dict(user=a["username"]), server=dict(qr=bool(qrcode), now=now(), base=base_url()))


@app.get("/api/state")
@auth_any
def state():
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
    return jsonify(conf=server_conf(ib, mask=True))


@app.post("/api/clients")
@auth_any
def client_create():
    d = body()
    b = parse_client_basic(d)
    count = num(d.get("count"), 1, 1, 200, "تعداد")
    links, owner = d.get("links"), 0
    if g.role == "admin":
        require_active_admin()
        links, owner = admin_links(0, links), g.aid
    touched = set()
    for i in range(count):
        priv = gen_private()
        name = b["name"] if count == 1 else f"{b['name']}-{i + 1}"
        cid = x("""INSERT INTO clients(name,token,enabled,private_key,public_key,limit_bytes,expiry,note,created,reset_period,last_reset,owner_id)
                   VALUES(?,?,1,?,?,?,?,?,?,?,?,?)""",
                (name, secrets.token_urlsafe(16), priv, pub_from_private(priv), b["limit_bytes"], b["expiry"], b["note"],
                 now(), b["reset_period"], now(), owner))
        try:
            touched |= save_links(cid, links)
        except Err:
            x("DELETE FROM clients WHERE id=?", (cid,))
            raise
    return jsonify(ok=True, warn=apply_many(touched))


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


@app.post("/api/clients/<int:cid>/reset-traffic")
@auth_any
def client_reset(cid):
    c = owned(cid)
    x("UPDATE clients SET up_bytes=0, down_bytes=0 WHERE id=?", (cid,))
    if not c["enabled"] and c["reason"] == "limit" and usage_state(q("SELECT * FROM clients WHERE id=?", (cid,), True)) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


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
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


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
.inf2 small{display:block;color:var(--mut);font-size:11.5px;direction:ltr;text-align:left}.inf2 b{display:block;direction:ltr;text-align:left;font:600 12.5px ui-monospace,Consolas,monospace;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
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
            cells = "".join(f"<div><small>{k}</small><b>{E(v)}</b></div>" for k, v in info)
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
        return Response(json.dumps([dict(inbound=ib["name"], awg=is_awg(ib), uri=(None if is_awg(ib) else build_uri(c, ci, ib)), conf=build_conf(c, ci, ib))
                                    for ci, ib in items], ensure_ascii=False), mimetype="application/json", headers=hdr)
    uris = "\n".join(build_uri(c, ci, ib) for ci, ib in items if not is_awg(ib))
    if fmt == "raw":
        return Response(uris, mimetype="text/plain; charset=utf-8", headers=hdr)
    return Response(base64.b64encode(uris.encode()).decode(), mimetype="text/plain; charset=utf-8", headers=hdr)


def sub_one(token, iid):
    c, items = sub_data(token)
    if client_state(c) != "active":
        abort(403)
    for ci, ib in items:
        if ib["id"] == iid:
            return c, ci, ib
    abort(404)


@app.get("/sub/<token>/<int:iid>.conf")
def sub_conf(token, iid):
    c, ci, ib = sub_one(token, iid)
    fn = re.sub(r"[^A-Za-z0-9_.\-]", "_", f"{ib['name']}-{c['id']}") + ".conf"
    return Response(build_conf(c, ci, ib), mimetype="text/plain; charset=utf-8",
                    headers={"Content-Disposition": f'attachment; filename="{fn}"', "Cache-Control": "no-store"})


@app.get("/sub/<token>/<int:iid>.svg")
def sub_qr(token, iid):
    c, ci, ib = sub_one(token, iid)
    return qr_svg(build_conf(c, ci, ib))


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
function showLogin(){$('#app').innerHTML=`<div class="login"><div class="lg2">${ic('shield')}</div><h1>ورود به SepiPanel</h1><div class="fg"><label>نام کاربری</label><input id="lu" autocomplete="username"></div>
<div class="fg"><label>رمز عبور</label><input id="lp" type="password" autocomplete="current-password"></div><button class="p" onclick="doLogin()">ورود</button></div>`;
 $('#lp').onkeydown=e=>{if(e.key==='Enter')doLogin()}}
async function doLogin(){try{await api('/login','POST',{u:$('#lu').value,p:$('#lp').value});load()}catch(e){toast(e.message,1)}}
async function load(){try{S=await api('/state');S.local=Date.now()/1000;render()}catch(e){if(e.message!=='نیاز به ورود')toast(e.message,1)}}
const STL={active:['فعال','ok'],disabled:['غیرفعال',''],expired:['منقضی','bad'],limit:['اتمام حجم','bad'],admin:['غیرفعال (ادمین)','bad']};
const NAV=[['cli','کلاینت‌ها','users','هر کلاینت می‌تواند عضو چند اینباند باشد.'],['inb','اینباندها','layers','هر اینباند یک اینترفیس وایرگارد است.'],['adm','ادمین‌ها','admin','ادمین‌ها فقط کلاینت می‌سازند و کلاینت‌های خودشان را مدیریت می‌کنند؛ برای هرکدام حجم و زمان تعیین کنید.'],['set','تنظیمات','settings','دامنه، پورت، حساب مدیر و تنظیمات اشتراک پنل را از اینجا مدیریت کنید.']];
const NAV_A=[['cli','کلاینت‌ها','users','کلاینت‌های خودتان را اینجا بسازید و مدیریت کنید.']];
const isA=()=>S&&S.role==='admin';
function render(){
 const NV=isA()?NAV_A:NAV;if(!NV.find(n=>n[0]==TAB))TAB='cli';
 const on=S.clients.filter(c=>c.online).length,tot=S.clients.reduce((a,c)=>a+c.up_bytes+c.down_bytes,0),cur=NV.find(n=>n[0]==TAB);
 $('#app').innerHTML=`<div class="shell"><aside class="side"><div class="brand"><span class="lg">${ic('shield')}</span><div><b>SepiPanel</b><small>مدیریت WireGuard</small></div></div>
 <nav class="nav">${NV.map(([k,l,i])=>`<button class="${TAB==k?'on':''}" onclick="TAB='${k}';render()">${ic(i)}<span>${l}</span></button>`).join('')}<button onclick="logout()">${ic('logout')}<span>خروج</span></button></nav></aside>
 <div class="main"><header class="tb"><span class="mut sm">${isA()?'پنل ادمین':esc(S.server.wg||'wireguard-tools یافت نشد!')}</span><div class="usr"><span class="av">${ic('user')}</span><div><b>${esc(S.panel.user)}</b><small><i></i>آنلاین</small></div></div></header>
 <div class="wrap"><h1 class="pt">${cur[1]}</h1><p class="ps">${cur[3]}</p>
 <div class="stats"><div class="st"><span class="si g">${ic('server')}</span><span class="l">اینباند فعال</span><b>${isA()?S.inbounds.length:S.inbounds.filter(i=>i.up).length+' / '+S.inbounds.length}</b></div>
 <div class="st"><span class="si p">${ic('users')}</span><span class="l">کلاینت‌ها</span><b>${S.clients.length}</b></div>
 <div class="st"><span class="si bl">${ic('pulse')}</span><span class="l">آنلاین</span><b>${on}</b></div>
 <div class="st"><span class="si o">${ic('db')}</span><span class="l">مصرف کل</span><b>${fmtB(tot)}</b></div></div>
 ${TAB=='inb'?inbHTML():TAB=='cli'?cliHTML():TAB=='adm'?admHTML():setHTML()}</div></div></div>`}
async function logout(){await api('/logout','POST');showLogin()}
/* ---------- اینباندها ---------- */
function inbHTML(){return `<div class="bar2"><span></span><button class="p" onclick="newInb()">+ اینباند جدید</button></div>`+
 (S.inbounds.map(i=>`<article class="card ${i.up?'up':''}"><div class="row"><h3>${esc(i.name)}<small>${esc(i.remark)}</small>${i.awg?' <span class="tag">AmneziaWG</span>':''}${i.exclude_sub?' <span class="tag">خارج از ساب</span>':''}</h3>
 <span class="b ${i.enabled?(i.up?'ok':'warn'):''}">${i.enabled?(i.up?'بالا':'پایین (خطا؟)'):'غیرفعال'}</span></div>
 <div class="meta"><span>پورت: <b>${i.port}/udp</b></span><span>IPv4: <b>${esc(i.address4)}</b></span>${i.address6?`<span>IPv6: <b>${esc(i.address6)}</b></span>`:''}
 <span>Endpoint: <b>${esc(i.endpoint||'(آدرس پنل)')}${i.endpoint_port?':'+i.endpoint_port:''}</b></span><span>DNS: <b>${esc(i.dns||'—')}</b></span>
 <span>MTU: <b>${i.mtu||'پیش‌فرض'}</b></span><span>کلاینت: <b>${i.clients}</b></span>
 <span style="cursor:pointer" onclick="copy('${esc(i.public_key)}')">کلید عمومی: <b>${esc(i.public_key.slice(0,12))}…</b></span></div>
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
const AWG_FIELDS=[{s:'مبهم‌سازی AmneziaWG (ضد DPI)'},
 {k:'obf_enabled',l:'فعال‌سازی AmneziaWG برای این اینباند',t:'check',h:'سرور باید amneziawg-tools نصب داشته باشد و کلاینت‌ها اپ AmneziaWG بزنند؛ اپ WireGuard معمولی به این اینباند وصل نمی‌شود.'},
 {k:'obf_ver',l:'نسخه پارامترها برای ساخت خودکار',t:'select',opts:[['3','3.x — کامل (Header Protection + padding + تایمرها)'],['2','2.0 — S3/S4 + بازه H + I1'],['1','1.x — فقط Jc/Jmin/Jmax/S1/S2/H1-H4']]},
 {t:'btn',l:'ساخت دوباره پارامترها',on:'genObf()'},
 ...OBF.map(([k,l,h])=>({k:'o_'+k,l,h}))];
async function genObf(){try{const r=await api('/obf/generate?v='+$('#f_obf_ver').value);for(const [k] of OBF){const e=$('#f_o_'+k);if(e)e.value=r[k]||''}$('#f_obf_enabled').checked=true;toast('پارامترهای جدید ساخته شد')}catch(e){toast(e.message,1)}}
const INB=[{s:'اصلی'},
 {k:'name',l:'نام اینترفیس',h:'مثل wg0 — حداکثر ۱۵ حرف انگلیسی'},{k:'remark',l:'توضیح',rtl:1},
 {k:'port',l:'پورت (UDP)',t:'number'},{k:'address4',l:'آدرس سرور IPv4 / ساب‌نت',ph:'10.8.0.1/24'},
 {k:'address6',l:'آدرس سرور IPv6 (اختیاری)',ph:'fd42:42:0::1/64',h:'خالی = بدون IPv6'},
 {k:'private_key',l:'کلید خصوصی سرور',h:'خالی = ساخت خودکار (در ویرایش: خالی = بدون تغییر)'},
 {k:'regen_keys',l:'ساخت دوباره کلید سرور (کلاینت‌ها باید کانفیگ جدید بگیرند)',t:'check',edit:1},
 {s:'اتصال کلاینت‌ها'},
 {k:'endpoint',l:'آدرس عمومی سرور (Endpoint)',h:'IP یا دامنه. خالی = همان آدرسی که پنل با آن باز شده'},
 {k:'endpoint_port',l:'پورت Endpoint',t:'number',h:'۰ = همان پورت listen (برای پورت‌فوروارد/NAT)'},
 {k:'dns',l:'DNS کلاینت',ph:'1.1.1.1, 1.0.0.1'},{k:'client_mtu',l:'MTU کلاینت',t:'number',h:'۰ = همان MTU سرور'},
 {k:'client_allowed_ips',l:'AllowedIPs کلاینت',h:'0.0.0.0/0, ::/0 = تمام ترافیک از تونل'},
 {k:'client_keepalive',l:'PersistentKeepalive (ثانیه)',t:'number',h:'۰ = خاموش، ۲۵ = پیشنهادی پشت NAT'},
 {k:'use_psk',l:'PresharedKey جداگانه برای هر کلاینت (امنیت بیشتر)',t:'check'},
 {k:'exclude_sub',l:'حذف از اشتراک‌ها (کلاینت‌ها این اینباند را در لینک ساب نمی‌بینند)',t:'check'},
 {s:'پیشرفته (سرور)'},
 {k:'mtu',l:'MTU اینترفیس سرور',t:'number',h:'۰ = پیش‌فرض (معمولاً 1420 مناسب است)'},
 {k:'table_',l:'Table',ph:'off | auto | عدد',h:'خالی = پیش‌فرض wg-quick'},{k:'fwmark',l:'FwMark',ph:'0xca6c | off'},
 {k:'auto_rules',l:'قوانین NAT و فوروارد خودکار (iptables + ip_forward)',t:'check'},
 {k:'nat_iface',l:'اینترفیس خروجی اینترنت',ph:'خودکار'},
 {k:'pre_up',l:'PreUp (هر خط یک دستور)',t:'textarea'},{k:'post_up',l:'PostUp',t:'textarea'},
 {k:'pre_down',l:'PreDown',t:'textarea'},{k:'post_down',l:'PostDown',t:'textarea'},
 ...AWG_FIELDS];
function fieldHTML(f,v,edit){
 if(f.s)return `<h4>${f.s}</h4>`;if(f.edit&&!edit)return '';if(f.t==='btn')return `<div class="fg"><button type="button" class="s" onclick="${f.on}">${f.l}</button></div>`;
 let val=v[f.k];if(val==null)val='';const id='f_'+f.k;const h=f.h?`<small>${f.h}</small>`:'';
 if(f.t==='check')return `<div class="fg"><label class="chk"><input type="checkbox" id="${id}" ${val?'checked':''}> ${f.l}</label>${h}</div>`;
 if(f.t==='select')return `<div class="fg"><label>${f.l}</label><select id="${id}">${f.opts.map(([a,b])=>`<option value="${a}" ${String(val)===a?'selected':''}>${b}</option>`).join('')}</select>${h}</div>`;
 if(f.t==='textarea')return `<div class="fg"><label>${f.l}</label><textarea id="${id}" spellcheck="false">${esc(val)}</textarea>${h}</div>`;
 return `<div class="fg"><label>${f.l}</label><input id="${id}" type="${f.t==='number'?'number':f.t||'text'}" value="${esc(val)}" placeholder="${esc(f.ph||'')}" ${f.rtl?'style="direction:rtl;text-align:right"':''}>${h}</div>`}
function collect(fields,edit){const o={};for(const f of fields){if(f.s||f.t==='btn'||(f.edit&&!edit))continue;const e=$('#f_'+f.k);const v=f.t==='check'?e.checked:e.value;if(f.k.startsWith('o_')){(o.obf=o.obf||{})[f.k.slice(2)]=v}else o[f.k]=v}return o}
function modal(html){const m=document.createElement('div');m.className='ov';m.innerHTML=`<div class="md">${html}</div>`;m.addEventListener('mousedown',e=>{if(e.target===m)m.remove()});document.body.appendChild(m);return m}
function formModal(title,fields,vals,edit,onSave){
 const m=modal(`<h2>${title}</h2>${fields.map(f=>fieldHTML(f,vals,edit)).join('')}<div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">${ic('save')}ذخیره</button></div>`);
 m.querySelector('#mc').onclick=()=>m.remove();
 m.querySelector('#ms').onclick=async()=>{if(await onSave(collect(fields,edit)))m.remove()}}
function newInb(){const d=S.defaults;formModal('اینباند جدید',INB,{...d,obf_ver:'3'},false,o=>act(()=>api('/inbounds','POST',o),'اینباند ساخته شد'))}
function editInb(id){const i=S.inbounds.find(x=>x.id==id);formModal('ویرایش اینباند '+esc(i.name),INB,{...i,private_key:'',obf_ver:'3',...Object.fromEntries(Object.entries(i.obf||{}).map(([k,v])=>['o_'+k,v]))},true,o=>act(()=>api('/inbounds/'+id,'PUT',o),'ذخیره شد'))}
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
 return `<div class="lk" data-ib="${ib.id}"><label class="chk"><input type="checkbox" class="lkc" ${L?'checked':''}> <b>${esc(ib.name)}</b> <span class="mut">${esc(ib.remark)} · ${esc(ib.address4)}</span></label>
 <details ${isA()?'hidden':''}><summary>تنظیمات ویژه این کلاینت در این اینباند</summary><div class="g2">${f('ip4','IPv4 ثابت','خودکار')}${f('allowed_ips','AllowedIPs کلاینت','پیش‌فرض اینباند')}
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
 <h4>دانلود تک‌تک</h4><div class="acts">${c.links.map(l=>`<a class="btn" href="/sub/${c.token}/${l.inbound_id}.conf">${esc(l.ib_name)}.conf</a>`).join('')||'<span class="mut">—</span>'}</div>
 <h4>امنیت</h4><div class="acts"><button class="s d" id="b2">ساخت لینک ساب جدید</button><button class="s d" id="b3">ساخت دوباره کلیدهای کلاینت</button></div>
 <div class="mfoot"><button class="s" id="x">بستن</button></div>`);
 m.querySelector('#b1').onclick=()=>copy(u);m.querySelector('#x').onclick=()=>m.remove();
 m.querySelector('#b2').onclick=async()=>{if(confirm('لینک قبلی از کار می‌افتد. ادامه؟')&&await act(()=>api('/clients/'+id+'/reset-token','POST'),'لینک جدید ساخته شد'))m.remove()};
 m.querySelector('#b3').onclick=async()=>{if(confirm('کلیدهای کلاینت عوض می‌شود و کانفیگ‌های قبلی کار نمی‌کنند. ادامه؟')&&await act(()=>api('/clients/'+id+'/regen-keys','POST'),'کلیدها عوض شد'))m.remove()}}
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
load();setInterval(()=>{if(S&&TAB!=='set'&&!document.querySelector('.ov')&&document.activeElement!==$('#cq'))load()},20000);
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
