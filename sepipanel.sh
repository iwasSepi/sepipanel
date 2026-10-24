#!/usr/bin/env bash
# SepiPanel — terminal management menu (installed as /usr/local/bin/sepipanel)
# Usage:  sepipanel            -> interactive menu
#         sepipanel info | start | stop | restart | status | log | update | uninstall

DIR=/opt/sepipanel
PY="python3 $DIR/sepipanel.py --cli"
SVC=sepipanel
R=$'\e[31m'; G=$'\e[32m'; Y=$'\e[33m'; B=$'\e[36m'; N=$'\e[0m'

[ "$(id -u)" -eq 0 ] || { echo "${R}Run as root (sudo sepipanel)${N}"; exit 1; }
[ -f "$DIR/sepipanel.py" ] || { echo "${R}SepiPanel is not installed in $DIR${N}"; exit 1; }

pub_ip() { curl -4 -fsS --max-time 5 https://api.ipify.org 2>/dev/null || hostname -I | awk '{print $1}'; }
cli() { WG_IP="${WG_IP:-$(pub_ip)}" $PY "$@"; }
pause() { echo; read -rp "Press Enter to continue..." _; }
ok()  { echo "${G}$*${N}"; }
err() { echo "${R}$*${N}"; }
restart_svc() { systemctl restart $SVC && sleep 1.5 && { systemctl is-active --quiet $SVC && ok "Panel restarted." || err "Panel failed to start: journalctl -u $SVC -e"; }; }
ask() { local v; read -rp "$1" v; echo "$v"; }

fw_open() {  # $1=port $2=proto
  command -v ufw >/dev/null && ufw status 2>/dev/null | grep -q "Status: active" && ufw allow "$1/$2" >/dev/null && echo "ufw: opened $1/$2"
}
fw_close() {
  command -v ufw >/dev/null && ufw status 2>/dev/null | grep -q "Status: active" && ufw delete allow "$1/$2" >/dev/null 2>&1
}

show_info() {
  echo "${B}---------------- Panel info ----------------${N}"
  cli info
  echo "${B}--------------------------------------------${N}"
  systemctl is-active --quiet $SVC && ok "Service: running" || err "Service: NOT running"
}

change_credentials() {
  echo "1) Change username   2) Change password   3) Both   0) Back"
  case "$(ask 'Select: ')" in
    1) u=$(ask 'New username: '); cli set-user "$u" && restart_svc ;;
    2) read -rsp "New password (min 10 chars): " p; echo; cli set-pass "$p" && restart_svc ;;
    3) u=$(ask 'New username: '); read -rsp "New password (min 10 chars): " p; echo
       cli set-user "$u" && cli set-pass "$p" && restart_svc ;;
  esac
}

change_port() {
  old=$(cli get port)
  echo "Current port: $old"
  p=$(ask 'New port (1-65535, empty = cancel): ')
  [ -z "$p" ] && return
  if cli set-port "$p"; then
    fw_open "$p" tcp; [ "$old" != "$p" ] && fw_close "$old" tcp
    restart_svc
    echo; cli info | head -1
  fi
}

ssl_for_domain() {
  d=$(ask 'Domain (must point to this server, port 80 must be free): ')
  [ -z "$d" ] && return
  e=$(ask 'Email for Let'"'"'s Encrypt: ')
  command -v certbot >/dev/null || { apt-get update -y && apt-get install -y certbot; }
  fw_open 80 tcp
  if certbot certonly --standalone --preferred-challenges http --non-interactive --agree-tos -m "$e" -d "$d"; then
    cli set-domain "$d" && cli set-cert "/etc/letsencrypt/live/$d/fullchain.pem" "/etc/letsencrypt/live/$d/privkey.pem" && restart_svc
    echo; cli info | head -1
  else
    err "certbot failed. Check DNS (A record -> this server) and that port 80 is reachable and free."
  fi
}

change_domain() {
  echo "1) New domain + get free SSL (Let's Encrypt)"
  echo "2) Set domain only (no SSL changes)"
  echo "3) Remove domain"
  echo "4) Use my own certificate files"
  echo "5) Disable HTTPS"
  echo "6) Renew certificate now"
  echo "0) Back"
  case "$(ask 'Select: ')" in
    1) ssl_for_domain ;;
    2) d=$(ask 'Domain: '); cli set-domain "$d" && restart_svc ;;
    3) cli set-domain - && restart_svc ;;
    4) c=$(ask 'Path to fullchain.pem: '); k=$(ask 'Path to privkey.pem: '); cli set-cert "$c" "$k" && restart_svc ;;
    5) cli clear-cert && restart_svc ;;
    6) certbot renew --force-renewal && restart_svc ;;
  esac
}

change_path() {
  echo "Current: /$(cli get path)"
  echo "1) Random secret path   2) Custom path   3) Remove path   0) Back"
  case "$(ask 'Select: ')" in
    1) cli set-path random && restart_svc; echo; cli info | head -1 ;;
    2) p=$(ask 'Path (A-Z a-z 0-9 _ -): '); cli set-path "$p" && restart_svc; echo; cli info | head -1 ;;
    3) cli set-path - && restart_svc ;;
  esac
}

change_allow() {
  echo "Current: $(cli get allowed)"
  echo "Only these IPs/CIDRs will be able to open the panel (client /sub/ links stay public)."
  echo "${Y}Warning: a wrong value can lock you out. Fix with option 'Reset security settings'.${N}"
  v=$(ask 'IPs/CIDRs comma-separated (empty = cancel, - = allow all): ')
  [ -z "$v" ] && return
  cli set-allow "$v" && restart_svc
}

reset_security() {
  [ "$(ask 'Reset port/domain/path/SSL/IP-limit/login to defaults? (y/N): ')" = "y" ] || return
  cli reset && restart_svc && { echo; cli info; }
}

backup_db() {
  mkdir -p /root/sepipanel-backups
  f="/root/sepipanel-backups/sepipanel-$(date +%F-%H%M%S).db"
  python3 - "$DIR/sepipanel.db" "$f" <<'PYEOF'
import sqlite3, sys
s = sqlite3.connect(sys.argv[1]); d = sqlite3.connect(sys.argv[2]); s.backup(d); d.close(); s.close()
PYEOF
  chmod 600 "$f"; ok "Backup saved: $f"
}

restore_db() {
  ls -1 /root/sepipanel-backups 2>/dev/null
  f=$(ask 'Full path of backup file to restore (empty = cancel): ')
  [ -f "$f" ] || { [ -n "$f" ] && err "File not found"; return; }
  systemctl stop $SVC
  cp "$DIR/sepipanel.db" "$DIR/sepipanel.db.before-restore" 2>/dev/null
  cp "$f" "$DIR/sepipanel.db"; chmod 600 "$DIR/sepipanel.db"
  systemctl start $SVC && ok "Restored."
}

enable_bbr() {
  if sysctl net.ipv4.tcp_congestion_control 2>/dev/null | grep -q bbr; then ok "BBR is already enabled."; return; fi
  grep -q "tcp_congestion_control=bbr" /etc/sysctl.conf 2>/dev/null || {
    echo "net.core.default_qdisc=fq" >> /etc/sysctl.conf
    echo "net.ipv4.tcp_congestion_control=bbr" >> /etc/sysctl.conf; }
  sysctl -p >/dev/null 2>&1
  sysctl net.ipv4.tcp_congestion_control | grep -q bbr && ok "BBR enabled." || err "BBR not available on this kernel."
}

open_ports() {
  p=$(ask 'Port number to open: '); pr=$(ask 'Protocol (tcp/udp) [udp]: '); pr=${pr:-udp}
  case "$p$pr" in *[!0-9a-z]*|"") err "Invalid"; return;; esac
  fw_open "$p" "$pr" || echo "ufw is not active (nothing changed). If you use another firewall/cloud panel, open it there."
}

do_update() {
  r=$(cat $DIR/.repo 2>/dev/null)
  [ -z "$r" ] && { err "Repo info not found ($DIR/.repo)."; return; }
  set -- $r
  echo "Updating from github.com/$1 ($2) ..."
  REPO="$1" BRANCH="$2" bash <(curl -fsSL "https://raw.githubusercontent.com/$1/$2/install.sh")
}

do_uninstall() {
  [ "$(ask 'Remove the panel service and the sepipanel command? (y/N): ')" = "y" ] || return
  systemctl disable --now $SVC 2>/dev/null; rm -f /etc/systemd/system/sepipanel.service; systemctl daemon-reload
  ok "Service removed. Data kept in $DIR (delete with: rm -rf $DIR). WireGuard configs are untouched."
  rm -f /usr/local/bin/sepipanel; exit 0
}

menu() {
  while true; do
    clear
    st=$(systemctl is-active --quiet $SVC && echo "${G}running${N}" || echo "${R}stopped${N}")
    echo "${B}=============== SepiPanel ===============${N}"
    echo " Status: $st"
    echo "  1) Show panel info (URL / login / port)"
    echo "  2) Change username / password"
    echo "  3) Change panel port"
    echo "  4) Domain & SSL (new domain, certificate, HTTPS)"
    echo "  5) Secret path (hide the panel URL)"
    echo "  6) Restrict panel to specific IPs"
    echo "  7) Reset security settings (if locked out)"
    echo " ---------------------------------------"
    echo "  8) Start      9) Stop      10) Restart"
    echo " 11) Service status        12) View logs (live)"
    echo " ---------------------------------------"
    echo " 13) Backup database       14) Restore database"
    echo " 15) Enable BBR            16) Open firewall port"
    echo " 17) Update panel          18) Uninstall"
    echo "  0) Exit"
    echo "${B}=======================================${N}"
    case "$(ask 'Select: ')" in
      1) show_info; pause ;;
      2) change_credentials; pause ;;
      3) change_port; pause ;;
      4) change_domain; pause ;;
      5) change_path; pause ;;
      6) change_allow; pause ;;
      7) reset_security; pause ;;
      8) systemctl start $SVC && ok "Started."; pause ;;
      9) systemctl stop $SVC && ok "Stopped."; pause ;;
      10) restart_svc; pause ;;
      11) systemctl status $SVC --no-pager; pause ;;
      12) journalctl -u $SVC -f -n 50 ;;
      13) backup_db; pause ;;
      14) restore_db; pause ;;
      15) enable_bbr; pause ;;
      16) open_ports; pause ;;
      17) do_update; pause ;;
      18) do_uninstall ;;
      0) exit 0 ;;
    esac
  done
}

case "${1:-menu}" in
  menu)      menu ;;
  info)      show_info ;;
  start)     systemctl start $SVC && ok "Started." ;;
  stop)      systemctl stop $SVC && ok "Stopped." ;;
  restart)   restart_svc ;;
  status)    systemctl status $SVC --no-pager ;;
  log|logs)  journalctl -u $SVC -f -n 50 ;;
  update)    do_update ;;
  uninstall) do_uninstall ;;
  backup)    backup_db ;;
  reset)     reset_security ;;
  *) echo "Usage: sepipanel [info|start|stop|restart|status|log|update|backup|reset|uninstall]" ;;
esac
