#!/usr/bin/env bash
# SepiPanel — نصب خودکار تک‌خطی
# نصب:    bash <(curl -fsSL https://raw.githubusercontent.com/iwasSepi/sepipanel/main/install.sh)
# آپدیت:  همان دستور بالا را دوباره اجرا کنید (دیتابیس و رمز حفظ می‌شود)
# حذف:    sepipanel uninstall   (یا: bash <(curl -fsSL .../install.sh) uninstall)
# منو:    sepipanel
# متغیرها: PORT=8080  AWG=1 (نصب AmneziaWG)  XRAY=1 (نصب Xray-core برای VLESS؛ وگرنه موقع ساخت اینباند VLESS خودکار دانلود می‌شود)  OVPN=1 (نصب OpenVPN؛ وگرنه موقع ساخت اینباند خودکار نصب می‌شود)  L2TP=1 (نصب xl2tpd+strongSwan؛ وگرنه موقع ساخت اینباند L2TP خودکار نصب می‌شود)  BRANCH=main
set -euo pipefail

# ====== اینجا را با ریپوی خودتان عوض کنید ======
REPO="${REPO:-iwasSepi/sepipanel}"
BRANCH="${BRANCH:-main}"
# ===============================================

DIR=/opt/sepipanel
SVC=/etc/systemd/system/sepipanel.service
PORT_SET="${PORT:-}"
PORT="${PORT:-8080}"
RAW="https://raw.githubusercontent.com/${REPO}/${BRANCH}/sepipanel.py"

[ "$(id -u)" -eq 0 ] || { echo "لطفاً با root اجرا کنید (sudo -i)"; exit 1; }

if [ "${1:-}" = "uninstall" ]; then
  systemctl disable --now sepipanel 2>/dev/null || true
  rm -f "$SVC"; systemctl daemon-reload
  echo "سرویس حذف شد. پوشهٔ $DIR (شامل دیتابیس) نگه داشته شد؛ برای پاک‌کردن کامل: rm -rf $DIR"
  exit 0
fi

command -v apt-get >/dev/null || { echo "فقط Ubuntu/Debian پشتیبانی می‌شود"; exit 1; }
export DEBIAN_FRONTEND=noninteractive

echo ">> نصب پیش‌نیازها..."
apt-get update -y
apt-get install -y wireguard wireguard-tools iptables iproute2 python3 python3-pip python3-flask python3-qrcode curl ca-certificates certbot

# اگر نسخه‌های apt موجود نبود، با pip نصب شود
python3 -c "import flask" 2>/dev/null || pip3 install flask --break-system-packages
python3 -c "import qrcode" 2>/dev/null || pip3 install qrcode --break-system-packages || true

if [ "${AWG:-0}" = "1" ]; then
  echo ">> نصب AmneziaWG..."
  apt-get install -y software-properties-common
  add-apt-repository -y ppa:amnezia/ppa || true
  apt-get update -y
  apt-get install -y amneziawg amneziawg-tools || echo "نصب AmneziaWG ناموفق بود؛ ادامه بدون آن"
fi

if [ "${L2TP:-0}" = "1" ]; then
  echo ">> نصب L2TP/IPsec..."
  apt-get install -y xl2tpd strongswan || echo "نصب xl2tpd/strongswan ناموفق بود؛ ادامه بدون آن"
  apt-get install -y strongswan-starter || true
fi

if [ "${OVPN:-0}" = "1" ]; then
  echo ">> نصب OpenVPN..."
  apt-get install -y openvpn openssl || echo "نصب openvpn ناموفق بود؛ ادامه بدون آن"
fi

if [ "${XRAY:-0}" = "1" ] && [ ! -x /usr/local/bin/xray ]; then
  echo ">> نصب Xray-core..."
  python3 - <<'PYX' || echo "نصب Xray ناموفق بود؛ هنگام ساخت اینباند VLESS دوباره تلاش می‌شود"
import platform, urllib.request, zipfile, tempfile, os, shutil
a = {"x86_64": "64", "amd64": "64", "aarch64": "arm64-v8a", "arm64": "arm64-v8a", "armv7l": "arm32-v7a"}[platform.machine().lower()]
d = tempfile.mkdtemp(); z = d + "/x.zip"
urllib.request.urlretrieve(f"https://github.com/XTLS/Xray-core/releases/latest/download/Xray-linux-{a}.zip", z)
with zipfile.ZipFile(z) as f, f.open("xray") as src, open("/usr/local/bin/xray", "wb") as dst:
    shutil.copyfileobj(src, dst)
os.chmod("/usr/local/bin/xray", 0o755)
PYX
fi

echo ">> دانلود پنل..."
mkdir -p "$DIR"
OLD_PASS=""
if [ -f "$DIR/sepipanel.py" ]; then
  OLD_PASS="$(grep -m1 '^ADMIN_PASS' "$DIR/sepipanel.py" | sed -E 's/^ADMIN_PASS[^"]*"([^"]*)".*/\1/')"
  OLD_PORT="$(grep -m1 '^PANEL_PORT' "$DIR/sepipanel.py" | sed -E 's/^PANEL_PORT[^0-9]*([0-9]+).*/\1/')"
  [ -n "${OLD_PORT:-}" ] && [ -z "${PORT_SET:-}" ] && PORT="${OLD_PORT}"
fi
curl -fsSL "$RAW" -o "$DIR/sepipanel.py.new"
mv "$DIR/sepipanel.py.new" "$DIR/sepipanel.py"
chmod 600 "$DIR/sepipanel.py"

# دستور ترمینال: sepipanel
curl -fsSL "https://raw.githubusercontent.com/${REPO}/${BRANCH}/sepipanel.sh" -o /usr/local/bin/sepipanel
chmod +x /usr/local/bin/sepipanel
echo "${REPO} ${BRANCH}" > "$DIR/.repo"
FRESH=0; [ -z "$OLD_PASS" ] && FRESH=1

# رمز تصادفی (در آپدیت رمز قبلی حفظ می‌شود)
if [ -n "$OLD_PASS" ] && [ "$OLD_PASS" != "ChangeMe-123" ]; then
  PASS="$OLD_PASS"
else
  PASS="$(head -c 24 /dev/urandom | base64 | tr -dc 'A-Za-z0-9' | head -c 16)"
fi
sed -i -E "s|^ADMIN_PASS[[:space:]]*=.*|ADMIN_PASS     = \"${PASS}\"|" "$DIR/sepipanel.py"
sed -i -E "s|^PANEL_PORT[[:space:]]*=.*|PANEL_PORT     = ${PORT}|" "$DIR/sepipanel.py"

echo ">> ساخت سرویس systemd..."
cat > "$SVC" <<UNIT
[Unit]
Description=SepiPanel
After=network-online.target
Wants=network-online.target

[Service]
WorkingDirectory=$DIR
ExecStart=/usr/bin/python3 $DIR/sepipanel.py
Restart=always
RestartSec=3

[Install]
WantedBy=multi-user.target
UNIT
systemctl daemon-reload
systemctl enable sepipanel >/dev/null 2>&1
if [ "$FRESH" = "1" ] && [ -z "$(python3 "$DIR/sepipanel.py" --cli get path)" ]; then
  python3 "$DIR/sepipanel.py" --cli set-path random >/dev/null   # مسیر مخفی تصادفی
fi
systemctl restart sepipanel

sleep 2
IP="$(curl -4 -fsS --max-time 5 https://api.ipify.org 2>/dev/null || hostname -I | awk '{print $1}')"
export WG_IP="$IP"
CLI="python3 $DIR/sepipanel.py --cli"
FPORT="$($CLI get port)"
if [ "$($CLI get default_pass)" = "1" ]; then SHOWPASS="$PASS"; else SHOWPASS="(توسط شما تغییر کرده)"; fi
if command -v ufw >/dev/null && ufw status 2>/dev/null | grep -q "Status: active"; then
  ufw allow "${FPORT}/tcp" >/dev/null || true
fi

if systemctl is-active --quiet sepipanel; then
  echo
  echo "=========================================="
  echo " SepiPanel نصب شد ✔"
  echo " آدرس:      $($CLI get url)"
  echo " نام کاربری: $($CLI get user)"
  echo " رمز:       ${SHOWPASS}"
  echo "=========================================="
  echo " منوی مدیریت در ترمینال:  sepipanel"
  echo " (تغییر پورت/دامنه/SSL/رمز/مسیر مخفی، بکاپ، آپدیت و ...)"
  echo " لاگ:   journalctl -u sepipanel -f"
  echo " نکته: پورت‌های UDP اینباندهای وایرگارد را هم در فایروال/پنل هاستینگ باز کنید."
  echo "       برای اینباند L2TP پورت‌های UDP ‏500 و 4500 و برای OpenVPN و VLESS پورت اینباند را باز کنید (یا گزینهٔ فایروال خودکار را فعال کنید)."
else
  echo "سرویس بالا نیامد؛ لاگ: journalctl -u sepipanel -e"
  exit 1
fi
