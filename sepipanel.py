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

from flask import Flask, request, jsonify, session, Response, abort

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
CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY, v TEXT);
""")


def ensure_cols(table, cols):
    have = {r["name"] for r in _db.execute(f"PRAGMA table_info({table})")}
    for c, d in cols.items():
        if c not in have:
            _db.execute(f"ALTER TABLE {table} ADD COLUMN {c} {d}")


ensure_cols("inbounds", {"obf": "TEXT DEFAULT ''", "exclude_sub": "INTEGER DEFAULT 0"})
ensure_cols("clients", {"reset_period": "TEXT DEFAULT ''", "last_reset": "INTEGER DEFAULT 0"})
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


def client_state(c):
    if not c["enabled"]:
        return c["reason"] or "disabled"
    return usage_state(c)


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


def auth(fn):
    @wraps(fn)
    def w(*a, **k):
        if not session.get("u") or session.get("v") != setting("sess_ver", "0"):
            return jsonify(error="auth"), 401
        if request.method != "GET" and request.headers.get("X-Requested-With") != "sepipanel":
            return jsonify(error="bad request"), 400
        return fn(*a, **k)
    return w


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
                           "down_bytes", "expiry", "note", "created", "last_seen", "reset_period")}
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
    ok_p = check_pw(p, h) if h else hmac.compare_digest(p, ADMIN_PASS)
    return hmac.compare_digest(u, admin_user()) & ok_p


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
    ok = check_login(str(d.get("u", "")), str(d.get("p", "")))
    if not ok:
        FAILS[ip] = (n + 1, t)
        return jsonify(error="نام کاربری یا رمز اشتباه است"), 401
    FAILS.pop(ip, None)
    session.permanent = True
    session["u"] = 1
    session["v"] = setting("sess_ver", "0")
    return jsonify(ok=True)


@app.post("/api/logout")
def logout():
    session.clear()
    return jsonify(ok=True)


@app.get("/api/state")
@auth
def state():
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
        settings=dict(public_url=setting("public_url"), sub_title=setting("sub_title", "WireGuard"),
                      update_interval=int(setting("update_interval", "12") or 12)),
        defaults=inbound_defaults(), panel=panel_info(),
        server=dict(wg=(ver.strip() if rc2 == 0 else ""), awg=(aver.strip() if rc3 == 0 else ""), nat_iface=detect_iface(), qr=bool(qrcode),
                    now=now(), base=base_url()))


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
@auth
def client_create():
    d = body()
    b = parse_client_basic(d)
    count = num(d.get("count"), 1, 1, 200, "تعداد")
    touched = set()
    for i in range(count):
        priv = gen_private()
        name = b["name"] if count == 1 else f"{b['name']}-{i + 1}"
        cid = x("""INSERT INTO clients(name,token,enabled,private_key,public_key,limit_bytes,expiry,note,created,reset_period,last_reset)
                   VALUES(?,?,1,?,?,?,?,?,?,?,?)""",
                (name, secrets.token_urlsafe(16), priv, pub_from_private(priv), b["limit_bytes"], b["expiry"], b["note"],
                 now(), b["reset_period"], now()))
        try:
            touched |= save_links(cid, d.get("links"))
        except Err:
            x("DELETE FROM clients WHERE id=?", (cid,))
            raise
    return jsonify(ok=True, warn=apply_many(touched))


@app.put("/api/clients/<int:cid>")
@auth
def client_update(cid):
    cur = q("SELECT * FROM clients WHERE id=?", (cid,), True) or abort(404)
    d = body()
    b = parse_client_basic(d)
    x("""UPDATE clients SET name=?, note=?, limit_bytes=?, expiry=?, reset_period=?,
         last_reset=CASE WHEN reset_period!=? THEN ? ELSE last_reset END WHERE id=?""",
      (b["name"], b["note"], b["limit_bytes"], b["expiry"], b["reset_period"], b["reset_period"], now(), cid))
    touched = save_links(cid, d.get("links"))
    c = q("SELECT * FROM clients WHERE id=?", (cid,), True)
    if not c["enabled"] and c["reason"] in ("expired", "limit") and usage_state(c) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(touched))


def client_inbounds(cid):
    return {r["inbound_id"] for r in q("SELECT inbound_id FROM client_inbound WHERE client_id=?", (cid,))}


@app.delete("/api/clients/<int:cid>")
@auth
def client_delete(cid):
    q("SELECT 1 FROM clients WHERE id=?", (cid,), True) or abort(404)
    ids = client_inbounds(cid)
    x("DELETE FROM clients WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(ids))


@app.post("/api/clients/<int:cid>/toggle")
@auth
def client_toggle(cid):
    c = q("SELECT * FROM clients WHERE id=?", (cid,), True) or abort(404)
    if c["enabled"]:
        x("UPDATE clients SET enabled=0, reason='disabled' WHERE id=?", (cid,))
    else:
        if usage_state(c) != "active":
            raise Err("حجم یا اعتبار کلاینت تمام شده؛ اول تمدید یا ریست ترافیک کنید")
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


@app.post("/api/clients/<int:cid>/reset-traffic")
@auth
def client_reset(cid):
    c = q("SELECT * FROM clients WHERE id=?", (cid,), True) or abort(404)
    x("UPDATE clients SET up_bytes=0, down_bytes=0 WHERE id=?", (cid,))
    if not c["enabled"] and c["reason"] == "limit" and usage_state(q("SELECT * FROM clients WHERE id=?", (cid,), True)) == "active":
        x("UPDATE clients SET enabled=1, reason='' WHERE id=?", (cid,))
    return jsonify(ok=True, warn=apply_many(client_inbounds(cid)))


@app.post("/api/clients/<int:cid>/reset-token")
@auth
def client_reset_token(cid):
    q("SELECT 1 FROM clients WHERE id=?", (cid,), True) or abort(404)
    x("UPDATE clients SET token=? WHERE id=?", (secrets.token_urlsafe(16), cid))
    return jsonify(ok=True)


@app.post("/api/clients/<int:cid>/regen-keys")
@auth
def client_regen(cid):
    q("SELECT 1 FROM clients WHERE id=?", (cid,), True) or abort(404)
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


def fmt_b(n):
    n = float(n or 0)
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or u == "TB":
            return f"{n:.2f} {u}" if u != "B" else f"{int(n)} B"
        n /= 1024


SUB_CSS = """body{margin:0;font:15px/1.7 Vazirmatn,Tahoma,sans-serif;background:#eef1f4;color:#14202b}
.w{max-width:720px;margin:0 auto;padding:20px 14px 60px}h1{font-size:20px;margin:6px 0 2px}
.m{color:#5b6b7a;font-size:13px}.bar{height:8px;background:#d9dfe5;border-radius:4px;overflow:hidden;margin:8px 0}
.bar i{display:block;height:100%;background:#9b1c24}.c{background:#fff;border:1px solid #d5dce3;border-radius:8px;padding:14px;margin-top:14px}
pre{direction:ltr;text-align:left;background:#f4f6f8;border:1px solid #e0e5ea;border-radius:6px;padding:10px;overflow:auto;font:12.5px/1.5 ui-monospace,Consolas,monospace;white-space:pre-wrap;word-break:break-all}
img{width:200px;max-width:100%;background:#fff;display:block;margin:8px auto}a.b,button{display:inline-block;background:#9b1c24;color:#fff;border:0;border-radius:6px;padding:7px 14px;font:inherit;text-decoration:none;cursor:pointer;margin:2px 0 2px 6px}
code{direction:ltr;unicode-bidi:embed;word-break:break-all}.bad{color:#9b1c24;font-weight:700}"""


def sub_page(c, items, base):
    E = html.escape
    used = c["up_bytes"] + c["down_bytes"]
    st = client_state(c)
    pct = min(100, used * 100 / c["limit_bytes"]) if c["limit_bytes"] else 0
    exp = time.strftime("%Y-%m-%d", time.localtime(c["expiry"])) if c["expiry"] else "نامحدود"
    tok = c["token"]
    h = [f"<!doctype html><html lang=fa dir=rtl><head><meta charset=utf-8><meta name=viewport content='width=device-width,initial-scale=1'>"
         f"<title>{E(c['name'])}</title><style>{SUB_CSS}</style></head><body><div class=w>",
         f"<h1>{E(c['name'])}</h1><div class=m>{E(setting('sub_title', 'WireGuard'))}</div>"]
    if st != "active":
        h.append(f"<p class=bad>این اشتراک فعال نیست ({ {'expired': 'منقضی شده', 'limit': 'حجم تمام شده'}.get(st, 'غیرفعال') }).</p>")
    h.append(f"<div class=c><div class=m>مصرف: <b>{fmt_b(used)}</b> از <b>{fmt_b(c['limit_bytes']) if c['limit_bytes'] else 'نامحدود'}</b>"
             f" &nbsp;|&nbsp; انقضا: <b>{exp}</b></div>")
    if c["limit_bytes"]:
        h.append(f"<div class=bar><i style='width:{pct:.1f}%'></i></div>")
    sub = f"{base}/sub/{tok}"
    h.append(f"<div class=m style='margin-top:8px'>لینک ساب (برای Hiddify / v2rayN / NekoBox / sing-box):</div>"
             f"<pre id=sl>{E(sub)}</pre><button onclick=\"cp('sl')\">کپی لینک ساب</button></div>")
    if qrcode:
        h.append(f"<div class=c><img src='/sub/{tok}/link.svg' alt=QR></div>")
    if st == "active":
        for i, (ci, ib) in enumerate(items):
            conf = build_conf(c, ci, ib)
            uri = "" if is_awg(ib) else build_uri(c, ci, ib)
            h.append(f"<div class=c><b>{E(ib['name'])}</b> <span class=m>{E(ib['remark'])}</span>"
                     f"<pre id=cf{i}>{E(conf)}</pre>")
            if qrcode:
                h.append(f"<img src='/sub/{tok}/{ib['id']}.svg' alt=QR>")
            if is_awg(ib):
                h.append("<div class=m>این اینباند AmneziaWG است؛ فقط با اپ AmneziaWG (فایل .conf یا QR) کار می‌کند.</div>")
            h.append(f"<a class=b href='/sub/{tok}/{ib['id']}.conf'>دانلود .conf</a>"
                     f"<button onclick=\"cp('cf{i}')\">کپی کانفیگ</button>"
                     + ("" if is_awg(ib) else f"<button onclick=\"cp('u{i}')\">کپی لینک wireguard://</button>"
                        f"<pre id=u{i} style='display:none'>{E(uri)}</pre>") + "</div>")
    h.append("<script>function cp(i){var t=document.getElementById(i).innerText;if(navigator.clipboard&&isSecureContext)navigator.clipboard.writeText(t);"
             "else{var a=document.createElement('textarea');a.value=t;document.body.appendChild(a);a.select();document.execCommand('copy');a.remove()}"
             "alert('کپی شد')}</script></div></body></html>")
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
<meta name="viewport" content="width=device-width,initial-scale=1"><title>SepiPanel</title>
<style>
:root{--bg:#eef1f4;--card:#fff;--ink:#14202b;--mut:#5b6b7a;--line:#d5dce3;--acc:#9b1c24;--acc2:#7a141b;--ok:#1d7a4d;--warn:#a86a00;--off:#7b8794}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.7 Vazirmatn,Tahoma,"Segoe UI",sans-serif}
button,input,select,textarea{font:inherit;color:inherit}
a{color:var(--acc)}
.top{display:flex;align-items:center;justify-content:space-between;padding:12px 16px;background:#14202b;color:#fff}
.top b{font-size:17px;letter-spacing:.2px}.top button{background:transparent;border:1px solid #4b5b6b;color:#fff}
.wrap{max-width:980px;margin:0 auto;padding:14px}
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin-bottom:14px}
.st{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
.st span{display:block;color:var(--mut);font-size:12.5px}.st b{font-size:20px}
.tabs{display:flex;gap:4px;border-bottom:2px solid var(--line);margin-bottom:14px}
.tabs button{background:none;border:0;padding:9px 16px;cursor:pointer;color:var(--mut);border-bottom:3px solid transparent;margin-bottom:-2px}
.tabs button.on{color:var(--acc);border-color:var(--acc);font-weight:700}
.bar2{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;gap:8px;flex-wrap:wrap}
button.p,.btn{background:var(--acc);color:#fff;border:0;border-radius:6px;padding:7px 14px;cursor:pointer}
button.p:hover{background:var(--acc2)}
button.s{background:#fff;border:1px solid var(--line);border-radius:6px;padding:4px 10px;cursor:pointer;font-size:13px}
button.s:hover{border-color:var(--acc);color:var(--acc)}button.s.d{color:var(--acc)}
.card{background:var(--card);border:1px solid var(--line);border-inline-start:4px solid var(--off);border-radius:8px;padding:12px 14px;margin-bottom:10px}
.card.up{border-inline-start-color:var(--acc)}
.row{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap}
.card h3{margin:0;font-size:16px}.card h3 small{color:var(--mut);font-weight:400;margin-inline-start:6px}
.meta{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:2px 14px;margin:8px 0;color:var(--mut);font-size:13px}
.meta b{color:var(--ink);font-weight:600;direction:ltr;unicode-bidi:embed}
.acts{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}
.b{font-size:12px;padding:1px 9px;border-radius:10px;color:#fff;background:var(--off)}.b.ok{background:var(--ok)}.b.warn{background:var(--warn)}.b.bad{background:var(--acc)}
.pg{height:6px;background:#dde3e9;border-radius:3px;overflow:hidden;margin:6px 0}.pg i{display:block;height:100%;background:var(--acc)}
.tag{display:inline-block;background:#e8edf2;border-radius:4px;padding:0 7px;font-size:12.5px;margin:0 0 3px 4px;direction:ltr}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--off);margin-inline-end:5px}.dot.on{background:var(--ok)}
.ov{position:fixed;inset:0;background:rgba(10,18,26,.55);display:flex;align-items:flex-start;justify-content:center;overflow:auto;padding:20px 10px;z-index:9}
.md{background:#fff;border-radius:10px;max-width:640px;width:100%;padding:16px 18px}
.md h2{margin:0 0 10px;font-size:18px}.md h4{margin:16px 0 6px;color:var(--acc);font-size:14px;border-bottom:1px solid var(--line);padding-bottom:3px}
.fg{margin-bottom:9px}.fg label{display:block;font-size:13px;color:var(--mut)}.fg small{color:var(--mut);font-size:12px}
.fg input:not([type=checkbox]),.fg select,.fg textarea{width:100%;padding:6px 9px;border:1px solid var(--line);border-radius:6px;background:#fff;direction:ltr;text-align:left}
.fg textarea{min-height:58px;font-family:ui-monospace,Consolas,monospace;font-size:13px}
.chk{display:flex!important;align-items:center;gap:7px;color:var(--ink)!important;font-size:14px!important}
.lk{border:1px solid var(--line);border-radius:6px;padding:8px 10px;margin-bottom:8px}
.lk details{margin-top:6px}.lk summary{cursor:pointer;color:var(--mut);font-size:13px}
.g2{display:grid;grid-template-columns:1fr 1fr;gap:0 10px}
pre.cf{direction:ltr;text-align:left;background:#f4f6f8;border:1px solid #e0e5ea;border-radius:6px;padding:10px;overflow:auto;font:12.5px/1.5 ui-monospace,Consolas,monospace;white-space:pre-wrap;word-break:break-all}
.mfoot{display:flex;gap:8px;justify-content:flex-end;margin-top:14px}
#toast{position:fixed;bottom:16px;left:50%;transform:translateX(-50%);z-index:20;display:flex;flex-direction:column;gap:6px;align-items:center}
#toast div{background:#14202b;color:#fff;padding:8px 14px;border-radius:6px;max-width:90vw}#toast div.e{background:var(--acc)}
.login{max-width:340px;margin:12vh auto;background:#fff;border:1px solid var(--line);border-radius:10px;padding:20px}
.login h1{margin:0 0 12px;font-size:20px}.empty{color:var(--mut);text-align:center;padding:30px 0}
.mut{color:var(--mut)}img.qr{width:210px;max-width:100%;display:block;margin:8px auto;background:#fff}
:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
@media(max-width:520px){.g2{grid-template-columns:1fr}}
</style></head><body><div id="app"></div><div id="toast"></div>
<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmtB=n=>{n=+n||0;const u=['B','KB','MB','GB','TB'];let i=0;while(n>=1024&&i<4){n/=1024;i++}return n.toFixed(i?2:0)+' '+u[i]};
const fmtD=t=>t?new Date(t*1000).toLocaleDateString('fa-IR'):'نامحدود';
const ago=t=>{if(!t)return 'هرگز';const s=Math.max(0,S.server.now-t+((Date.now()/1000)-S.local));if(s<90)return 'همین الان';if(s<3600)return Math.floor(s/60)+' دقیقه پیش';if(s<86400)return Math.floor(s/3600)+' ساعت پیش';return Math.floor(s/86400)+' روز پیش'};
const BASE=location.pathname.replace(/\/+$/,'');
let S=null,TAB='cli';
function toast(m,e){const d=document.createElement('div');d.textContent=m;if(e)d.className='e';$('#toast').appendChild(d);setTimeout(()=>d.remove(),e?7000:2500)}
async function api(p,m='GET',b){const r=await fetch(BASE+'/api'+p,{method:m,headers:{'Content-Type':'application/json','X-Requested-With':'sepipanel'},body:b?JSON.stringify(b):undefined});
 if(r.status==401){showLogin();throw new Error('نیاز به ورود')}
 const d=await r.json().catch(()=>({}));if(!r.ok)throw new Error(d.error||r.statusText);return d}
async function act(fn,msg){try{const r=await fn();if(r&&r.warn)toast(r.warn,1);else if(msg)toast(msg);await load();return true}catch(e){toast(e.message,1);return false}}
function copy(t){if(navigator.clipboard&&isSecureContext)navigator.clipboard.writeText(t);else{const a=document.createElement('textarea');a.value=t;document.body.appendChild(a);a.select();document.execCommand('copy');a.remove()}toast('کپی شد')}
function showLogin(){$('#app').innerHTML=`<div class="login"><h1>ورود به SepiPanel</h1><div class="fg"><label>نام کاربری</label><input id="lu" autocomplete="username"></div>
<div class="fg"><label>رمز عبور</label><input id="lp" type="password" autocomplete="current-password"></div><button class="p" style="width:100%" onclick="doLogin()">ورود</button></div>`;
 $('#lp').onkeydown=e=>{if(e.key==='Enter')doLogin()}}
async function doLogin(){try{await api('/login','POST',{u:$('#lu').value,p:$('#lp').value});load()}catch(e){toast(e.message,1)}}
async function load(){try{S=await api('/state');S.local=Date.now()/1000;render()}catch(e){if(e.message!=='نیاز به ورود')toast(e.message,1)}}
const STL={active:['فعال','ok'],disabled:['غیرفعال',''],expired:['منقضی','bad'],limit:['اتمام حجم','bad']};
function render(){
 const on=S.clients.filter(c=>c.online).length,tot=S.clients.reduce((a,c)=>a+c.up_bytes+c.down_bytes,0);
 $('#app').innerHTML=`<div class="top"><b>SepiPanel</b><span class="mut" style="color:#9fb0c0;font-size:12px">${esc(S.server.wg||'wireguard-tools یافت نشد!')}</span><button class="s" onclick="logout()">خروج</button></div>
 <div class="wrap"><div class="stats"><div class="st"><span>اینباند فعال</span><b>${S.inbounds.filter(i=>i.up).length} / ${S.inbounds.length}</b></div>
 <div class="st"><span>کلاینت‌ها</span><b>${S.clients.length}</b></div><div class="st"><span>آنلاین</span><b>${on}</b></div><div class="st"><span>مصرف کل</span><b>${fmtB(tot)}</b></div></div>
 <div class="tabs">${[['cli','کلاینت‌ها'],['inb','اینباندها'],['set','تنظیمات']].map(([k,l])=>`<button class="${TAB==k?'on':''}" onclick="TAB='${k}';render()">${l}</button>`).join('')}</div>
 ${TAB=='inb'?inbHTML():TAB=='cli'?cliHTML():setHTML()}</div>`}
async function logout(){await api('/logout','POST');showLogin()}
/* ---------- اینباندها ---------- */
function inbHTML(){return `<div class="bar2"><span class="mut">هر اینباند یک اینترفیس وایرگارد است</span><button class="p" onclick="newInb()">+ اینباند جدید</button></div>`+
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
 const m=modal(`<h2>${title}</h2>${fields.map(f=>fieldHTML(f,vals,edit)).join('')}<div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">ذخیره</button></div>`);
 m.querySelector('#mc').onclick=()=>m.remove();
 m.querySelector('#ms').onclick=async()=>{if(await onSave(collect(fields,edit)))m.remove()}}
function newInb(){const d=S.defaults;formModal('اینباند جدید',INB,{...d,obf_ver:'3'},false,o=>act(()=>api('/inbounds','POST',o),'اینباند ساخته شد'))}
function editInb(id){const i=S.inbounds.find(x=>x.id==id);formModal('ویرایش اینباند '+esc(i.name),INB,{...i,private_key:'',obf_ver:'3',...Object.fromEntries(Object.entries(i.obf||{}).map(([k,v])=>['o_'+k,v]))},true,o=>act(()=>api('/inbounds/'+id,'PUT',o),'ذخیره شد'))}
function delInb(id,n){if(confirm(`اینباند ${n} و اتصال همه کلاینت‌هایش حذف شود؟`))act(()=>api('/inbounds/'+id,'DELETE'),'حذف شد')}
async function showConf(id){try{const r=await api('/inbounds/'+id+'/conf');const m=modal(`<h2>کانفیگ سرور</h2><pre class="cf">${esc(r.conf)}</pre><div class="mfoot"><button class="s" id="x">بستن</button></div>`);m.querySelector('#x').onclick=()=>m.remove()}catch(e){toast(e.message,1)}}
/* ---------- کلاینت‌ها ---------- */
function cliHTML(){return `<div class="bar2"><span class="mut">هر کلاینت می‌تواند عضو چند اینباند باشد</span><button class="p" onclick="newCli()">+ کلاینت جدید</button></div>`+
 (S.clients.map(c=>{const u=c.up_bytes+c.down_bytes,pct=c.limit_bytes?Math.min(100,u*100/c.limit_bytes):0,st=STL[c.state]||[c.state,''];
 return `<article class="card ${c.state=='active'?'up':''}"><div class="row"><h3><span class="dot ${c.online?'on':''}"></span>${esc(c.name)}<small>${esc(c.note)}</small></h3><span class="b ${st[1]}">${st[0]}</span></div>
 <div class="pg"><i style="width:${c.limit_bytes?pct:0}%"></i></div>
 <div class="meta"><span>مصرف: <b>${fmtB(u)}</b> / <b>${c.limit_bytes?fmtB(c.limit_bytes):'نامحدود'}</b></span><span>↑ ${fmtB(c.up_bytes)} &nbsp; ↓ ${fmtB(c.down_bytes)}</span>
 <span>انقضا: <b style="direction:rtl">${fmtD(c.expiry)}</b></span><span>آخرین اتصال: <b style="direction:rtl">${ago(c.last_seen)}</b></span></div>
 <div>${c.links.map(l=>`<span class="tag">${esc(l.ib_name)} · ${esc(l.ip4)}</span>`).join('')||'<span class="mut">بدون اینباند</span>'}</div>
 <div class="acts"><button class="s" onclick="subModal(${c.id})">لینک ساب / QR</button><button class="s" onclick="editCli(${c.id})">ویرایش</button>
 <button class="s" onclick="act(()=>api('/clients/${c.id}/toggle','POST'))">${c.enabled?'غیرفعال‌سازی':'فعال‌سازی'}</button>
 <button class="s" onclick="act(()=>api('/clients/${c.id}/reset-traffic','POST'),'ترافیک ریست شد')">ریست ترافیک</button>
 <button class="s d" onclick="delCli(${c.id},'${esc(c.name)}')">حذف</button></div></article>`}).join('')||'<div class="empty">کلاینتی وجود ندارد.</div>')}
const CLI=[{k:'name',l:'نام کلاینت',rtl:1},{k:'count',l:'تعداد (ساخت گروهی؛ نام‌ها شماره‌دار می‌شوند)',t:'number',create:1},
 {k:'note',l:'یادداشت',rtl:1},{k:'limit_gb',l:'محدودیت حجم (گیگابایت)',t:'number',h:'۰ = نامحدود'},
 {k:'reset_period',l:'ریست خودکار ترافیک',t:'select',opts:[['','هرگز'],['daily','روزانه'],['weekly','هفتگی'],['monthly','ماهانه (هر ۳۰ روز)']]}];
function linkBlock(ib,L){const v=L||{};const f=(k,l,ph)=>`<div class="fg"><label>${l}</label><input class="l_${k}" value="${esc(v[k]??'')}" placeholder="${ph||''}"></div>`;
 return `<div class="lk" data-ib="${ib.id}"><label class="chk"><input type="checkbox" class="lkc" ${L?'checked':''}> <b>${esc(ib.name)}</b> <span class="mut">${esc(ib.remark)} · ${esc(ib.address4)}</span></label>
 <details><summary>تنظیمات ویژه این کلاینت در این اینباند</summary><div class="g2">${f('ip4','IPv4 ثابت','خودکار')}${f('allowed_ips','AllowedIPs کلاینت','پیش‌فرض اینباند')}
 ${f('keepalive','Keepalive','پیش‌فرض اینباند (۰=خاموش)')}${f('dns','DNS','پیش‌فرض اینباند')}${f('mtu','MTU','پیش‌فرض اینباند')}${f('extra_allowed','AllowedIPs اضافه سمت سرور','مثلا 192.168.50.0/24')}</div></details></div>`}
function cliModal(title,c){const vals=c?{...c,limit_gb:c.limit_bytes?+(c.limit_bytes/1024**3).toFixed(3):0}:{limit_gb:0,count:1};
 const fields=CLI.filter(f=>!f.create||!c);
 const m=modal(`<h2>${title}</h2>${fields.map(f=>fieldHTML(f,vals,!!c)).join('')}
 <div class="fg"><label>تاریخ انقضا</label><input type="date" id="f_exp" value="${c&&c.expiry?new Date(c.expiry*1000).toISOString().slice(0,10):''}">
 <div style="margin-top:4px"><button class="s" type="button" data-d="30">+۳۰ روز</button> <button class="s" type="button" data-d="90">+۹۰ روز</button> <button class="s" type="button" data-d="0">نامحدود</button></div></div>
 <h4>اینباندها</h4>${S.inbounds.length?S.inbounds.map(ib=>{const L=c&&c.links.find(l=>l.inbound_id==ib.id);return linkBlock(ib,L?{...L,keepalive:L.keepalive<0?'':L.keepalive,mtu:L.mtu||''}:(!c&&ib.enabled?{}:null))}).join(''):'<div class="mut">اول یک اینباند بسازید.</div>'}
 <div class="mfoot"><button class="s" id="mc">انصراف</button><button class="p" id="ms">ذخیره</button></div>`);
 m.querySelectorAll('[data-d]').forEach(b=>b.onclick=()=>{const d=+b.dataset.d;const e=m.querySelector('#f_exp');if(!d){e.value='';return}const base=c&&c.expiry*1000>Date.now()?c.expiry*1000:Date.now();e.value=new Date(base+d*864e5).toISOString().slice(0,10)});
 m.querySelector('#mc').onclick=()=>m.remove();
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
/* ---------- تنظیمات ---------- */
function setHTML(){const s=S.settings,p=S.panel,sv=S.server;return `
${p.default_pass?`<div class="card" style="border-inline-start-color:var(--acc)"><b>هشدار امنیتی:</b> رمز پیش‌فرض داخل فایل هنوز فعال است. همین حالا از «حساب مدیر» عوضش کن.</div>`:''}
${p.restart_needed?`<div class="card" style="border-inline-start-color:var(--warn)">تغییر پورت/HTTPS ذخیره شده ولی هنوز اعمال نشده. <button class="p" onclick="restartPanel()">ری‌استارت پنل</button></div>`:''}
<div class="card" style="max-width:640px"><h3>دامنه، پورت و HTTPS پنل</h3><br>
 <div class="fg"><label>دامنه پنل</label><input id="p_dom" value="${esc(p.domain)}" placeholder="panel.example.com"><small>رکورد A دامنه باید به IP همین سرور اشاره کند. لینک‌های ساب با این دامنه ساخته می‌شوند.</small></div>
 <div class="g2"><div class="fg"><label>پورت پنل</label><input id="p_port" type="number" value="${p.port}"></div>
 <div class="fg"><label>مسیر مخفی (اختیاری)</label><input id="p_path" value="${esc(p.path)}" placeholder="مثلا x7k2q9"></div></div>
 <div class="fg"><label>مسیر فایل گواهی (fullchain.pem)</label><input id="p_cert" value="${esc(p.cert)}" placeholder="/etc/letsencrypt/live/panel.example.com/fullchain.pem"></div>
 <div class="fg"><label>مسیر کلید خصوصی (privkey.pem)</label><input id="p_key" value="${esc(p.key)}"></div>
 <div class="fg"><label>فقط این IPها به پنل دسترسی داشته باشند (اختیاری)</label><input id="p_allow" value="${esc(p.allowed_ips)}" placeholder="1.2.3.4, 10.0.0.0/8"><small>لینک‌های ساب مشمول این محدودیت نیستند. پشت پروکسی معکوس از این گزینه استفاده نکن. اگر قفل شدی: python3 sepipanel.py --reset</small></div>
 <div class="acts"><button class="p" onclick="savePanel()">ذخیره</button><button class="s" onclick="restartPanel()">ری‌استارت پنل</button></div>
 <h4>گواهی رایگان Let's Encrypt</h4>
 <div class="fg"><label>ایمیل</label><input id="p_mail" placeholder="you@example.com"></div>
 <button class="s" onclick="issueCert()" ${p.certbot?'':'disabled'}>دریافت گواهی با certbot</button>
 <div><small class="mut">${p.certbot?'پورت 80 باید آزاد باشد. بعد از دریافت، پنل را ری‌استارت کن.':'certbot نصب نیست: apt install certbot'}</small></div></div>
<div class="card" style="max-width:640px"><h3>حساب مدیر</h3><br>
 <div class="fg"><label>رمز فعلی</label><input id="a_cur" type="password" autocomplete="current-password"></div>
 <div class="fg"><label>نام کاربری</label><input id="a_user" value="${esc(p.user)}"></div>
 <div class="fg"><label>رمز جدید (حداقل ۱۰ کاراکتر؛ خالی = بدون تغییر)</label><input id="a_new" type="password" autocomplete="new-password"></div>
 <button class="p" onclick="saveAcct()">ذخیره</button> <small class="mut">بعد از تغییر، نشست‌های دیگر بسته می‌شوند.</small></div>
<div class="card" style="max-width:640px"><h3>تنظیمات اشتراک</h3><br>
 <div class="fg"><label>آدرس عمومی پنل برای لینک ساب (اختیاری)</label><input id="s_u" value="${esc(s.public_url)}" placeholder="https://panel.example.com"><small>خالی = از دامنه‌ی بالا یا آدرس فعلی ساخته می‌شود. پشت nginx/کلودفلر پر کن.</small></div>
 <div class="fg"><label>عنوان اشتراک</label><input id="s_t" value="${esc(s.sub_title)}"></div>
 <div class="fg"><label>بازه آپدیت خودکار در اپ کلاینت (ساعت)</label><input id="s_i" type="number" value="${s.update_interval}"></div>
 <button class="p" onclick="saveSet()">ذخیره</button></div>
<div class="card" style="max-width:640px"><h3>اطلاعات سرور</h3><div class="meta"><span>WireGuard: <b>${esc(sv.wg||'نصب نیست')}</b></span><span>AmneziaWG: <b>${esc(sv.awg||'نصب نیست')}</b></span><span>اینترفیس خروجی: <b>${esc(sv.nat_iface)}</b></span><span>QR: <b>${sv.qr?'فعال':'نصب نیست'}</b></span><span>HTTPS: <b>${p.tls_on?'فعال':'خاموش'}</b></span></div></div>`}
function saveSet(){act(()=>api('/settings','PUT',{public_url:$('#s_u').value,sub_title:$('#s_t').value,update_interval:$('#s_i').value}),'ذخیره شد')}
function savePanel(){act(()=>api('/panel','PUT',{domain:$('#p_dom').value,port:$('#p_port').value,path:$('#p_path').value,cert:$('#p_cert').value,key:$('#p_key').value,allowed_ips:$('#p_allow').value}),'ذخیره شد')}
async function restartPanel(){if(!confirm('پنل ری‌استارت می‌شود و به آدرس جدید می‌روید. ادامه؟'))return;try{const r=await api('/panel/restart','POST');toast('در حال ری‌استارت…');setTimeout(()=>{location.href=r.url},3500)}catch(e){toast(e.message,1)}}
function issueCert(){toast('در حال گرفتن گواهی… (تا ۲ دقیقه)');act(()=>api('/panel/cert','POST',{domain:$('#p_dom').value,email:$('#p_mail').value}),'گواهی ساخته شد؛ پنل را ری‌استارت کنید')}
async function saveAcct(){try{await api('/panel/account','POST',{current:$('#a_cur').value,user:$('#a_user').value,password:$('#a_new').value});toast('ذخیره شد');$('#a_cur').value='';$('#a_new').value='';await load()}catch(e){toast(e.message,1)}}
load();setInterval(()=>{if(S&&TAB!=='set'&&!document.querySelector('.ov'))load()},20000);
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
