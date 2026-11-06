#!/usr/bin/env bash
# Управление предприятием: установка и обновление одной командой.
#
#   bash install.sh [домен] [--email почта] [--port 80] [--mode shared|server] [--branch main]
#
# Режим выбирается сам:
#   shared — виртуальный хостинг без прав root (reg.ru и т. п.): Node.js в ~/node,
#            код в ~/sed-zakazy, данные в ~/sed-zakazy-data, запуск через Passenger (.htaccess).
#   server — свой сервер с root: Node.js в /opt/node, код в /opt/sed-zakazy,
#            данные в /var/lib/sed-zakazy, служба systemd и nginx.
#            Без домена сайт открывается по IP сервера (http://IP), без сертификата.
#            С доменом и --email дополнительно выпускается HTTPS-сертификат Let's Encrypt.
#
# Повторный запуск обновляет код (git pull) и перезапускает приложение. Данные не трогаются.
# Репозиторий публичный, токен не нужен. Для приватной копии задайте GITHUB_TOKEN (право чтения).
set -euo pipefail

# Run from a temporary copy: updating the code rewrites this very file, and bash reads scripts lazily.
SELF="${BASH_SOURCE[0]:-}"
if [ -n "$SELF" ] && [ -f "$SELF" ] && [ -z "${SED_RUNNING_COPY:-}" ]; then
  export SED_SELF_DIR="${SED_SELF_DIR:-$(cd "$(dirname "$SELF")" && pwd)}"
  SED_RUNNING_COPY="$(mktemp)"; cp "$SELF" "$SED_RUNNING_COPY"; export SED_RUNNING_COPY
  exec bash "$SED_RUNNING_COPY" "$@"
fi
[ -n "${SED_RUNNING_COPY:-}" ] && trap 'rm -f "$SED_RUNNING_COPY"' EXIT
ORIG_ARGS=("$@")

REPO="${SED_REPO:-https://github.com/pptkaa-del/sed-zakazy.git}"
BRANCH="main"
DOMAIN=""
EMAIL=""
HTTP_PORT=80
MODE=""
NODE_NEW="20.18.1"
NODE_OLD="16.20.2"

say()  { printf '\033[1;34m==>\033[0m %s\n' "$*"; }
ok()   { printf '\033[1;32m  ✓\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m  !\033[0m %s\n' "$*"; }
die()  { printf '\033[1;31mОшибка:\033[0m %s\n' "$*" >&2; exit 1; }

while [ $# -gt 0 ]; do
  case "$1" in
    --email)  EMAIL="${2:-}"; shift 2 ;;
    --mode)   MODE="${2:-}"; shift 2 ;;
    --branch) BRANCH="${2:-}"; shift 2 ;;
    --port)   HTTP_PORT="${2:-}"; shift 2 ;;
    -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) die "Неизвестный параметр $1" ;;
    *)  DOMAIN="$1"; shift ;;
  esac
done
DOMAIN="${DOMAIN#http://}"; DOMAIN="${DOMAIN#https://}"; DOMAIN="${DOMAIN%%/*}"

if [ -z "$MODE" ]; then
  if [ "$(id -u)" = 0 ]; then MODE=server; else MODE=shared; fi
fi
[ "$MODE" = shared ] || [ "$MODE" = server ] || die "--mode должен быть shared или server"
[ "$MODE" = server ] && [ "$(id -u)" != 0 ] && die "Режим server нужно запускать от root: sudo bash install.sh ..."

for c in curl tar git; do command -v "$c" >/dev/null || NEED_PKGS="${NEED_PKGS:-} $c"; done

# ---------- helpers ----------
glibc_ok() {   # true when glibc >= 2.28 (needed by Node.js 18+)
  local v; v="$(ldd --version 2>/dev/null | head -1 | grep -oE '[0-9]+\.[0-9]+$' || true)"
  [ -n "$v" ] || return 0
  [ "$(printf '%s\n2.28\n' "$v" | sort -V | head -1)" = "2.28" ]
}
node_arch() {
  case "$(uname -m)" in
    x86_64|amd64) echo x64 ;;
    aarch64|arm64) echo arm64 ;;
    *) die "Архитектура $(uname -m) не поддерживается" ;;
  esac
}
node_major() { "$1" -e 'console.log(process.versions.node.split(".")[0])' 2>/dev/null || echo 0; }
install_node() {   # $1 = target dir
  local dir="$1" ver arch name tmp
  if glibc_ok; then ver="$NODE_NEW"; else ver="$NODE_OLD"; warn "Старая glibc на сервере, ставлю Node.js $ver"; fi
  arch="$(node_arch)"; name="node-v$ver-linux-$arch"
  tmp="$(mktemp -d)"
  say "Скачиваю Node.js $ver"
  curl -fsSL "https://nodejs.org/dist/v$ver/$name.tar.xz" -o "$tmp/node.tar.xz" || die "Не удалось скачать Node.js"
  tar xf "$tmp/node.tar.xz" -C "$tmp" || die "Не удалось распаковать Node.js (нужен xz)"
  rm -rf "$dir"; mkdir -p "$(dirname "$dir")"; mv "$tmp/$name" "$dir"; rm -rf "$tmp"
  "$dir/bin/node" -v >/dev/null || die "Node.js не запускается на этом сервере"
  ok "Node.js $("$dir/bin/node" -v) в $dir"
}
repo_url_with_token() {
  if [ -n "${GITHUB_TOKEN:-}" ]; then echo "$REPO" | sed "s#https://#https://x-access-token:${GITHUB_TOKEN}@#"; else echo "$REPO"; fi
}
fetch_code() {   # $1 = app dir, $2 = owner (optional, server mode)
  local dir="$1"
  if [ -f "$dir/server.js" ] && [ -d "$dir/.git" ]; then
    say "Обновляю код в $dir"
    local src=origin; [ -n "${GITHUB_TOKEN:-}" ] && src="$(repo_url_with_token)"
    git -C "$dir" fetch --quiet "$src" "$BRANCH" || die "git fetch не удался. Для приватного репозитория задайте GITHUB_TOKEN"
    git -C "$dir" reset --quiet --hard FETCH_HEAD
  elif [ -f "$dir/server.js" ]; then
    warn "$dir уже содержит приложение без git, оставляю как есть"
  else
    say "Скачиваю код из $REPO"
    [ -e "$dir" ] && [ -n "$(ls -A "$dir" 2>/dev/null)" ] && die "Папка $dir занята другими файлами"
    git clone --quiet --depth 1 --branch "$BRANCH" "$(repo_url_with_token)" "$dir" \
      || die "git clone не удался. Для приватного репозитория: GITHUB_TOKEN=токен bash install.sh ..."
    git -C "$dir" remote set-url origin "$REPO"
  fi
  ok "Версия: $(git -C "$dir" log -1 --format='%h %cd' --date=short 2>/dev/null || echo 'без git')"
}
reexec_if_changed() {   # $1 = app dir: continue with the freshly downloaded install.sh
  local new="$1/install.sh"
  { [ -z "${SED_REEXEC:-}" ] && [ -f "$new" ]; } || return 0
  if [ -n "${SED_RUNNING_COPY:-}" ] && cmp -s "$new" "$SED_RUNNING_COPY"; then return 0; fi
  [ -n "${SED_RUNNING_COPY:-}" ] && say "Скрипт установки обновился, продолжаю новой версией"
  rm -f "${SED_RUNNING_COPY:-}"
  SED_REEXEC=1 SED_SELF_DIR="$1" SED_RUNNING_COPY="" exec bash "$new" "${ORIG_ARGS[@]+"${ORIG_ARGS[@]}"}"
}
set_env() {   # $1 file, $2 key, $3 value — add or replace KEY=value
  local f="$1" k="$2" v="$3"
  touch "$f"
  if grep -qE "^#? *$k=" "$f"; then sed -i "s#^\#\? *$k=.*#$k=$v#" "$f"; else echo "$k=$v" >> "$f"; fi
}
smoke_test() {   # $1 node, $2 app dir — start on a random port with throwaway data, then stop
  local log data; log="$(mktemp)"; data="$(mktemp -d)"
  ( cd "$2" && PORT=0 HOST=127.0.0.1 DATA_DIR="$data" timeout 5 "$1" server.js >"$log" 2>&1 ) || true
  rm -rf "$data"
  if grep -q 'запущен' "$log"; then ok "Приложение запускается"; rm -f "$log"
  else cat "$log" >&2; rm -f "$log"; die "Приложение не запустилось, текст ошибки выше"; fi
}
wait_http() {   # $1 url, then extra curl args — up to 15 s
  local i; for i in $(seq 1 30); do curl -fs -o /dev/null "$@" && return 0; sleep 0.5; done; return 1
}

# ======================================================================
if [ "$MODE" = shared ]; then
  say "Режим: виртуальный хостинг (без root)"
  [ -n "${NEED_PKGS:-}" ] && die "На хостинге нет программ:${NEED_PKGS}. Обратитесь в поддержку хостинга"

  if [ -z "$DOMAIN" ] && [ -d "$HOME/www" ]; then
    mapfile -t SITES < <(ls -1 "$HOME/www" 2>/dev/null)
    if [ "${#SITES[@]}" = 1 ]; then DOMAIN="${SITES[0]}"; ok "Сайт: $DOMAIN"
    else die "Укажите домен: bash install.sh ваш-домен.ru  (папки сайтов: ${SITES[*]:-нет})"; fi
  fi
  [ -n "$DOMAIN" ] || die "Укажите домен: bash install.sh ваш-домен.ru"
  [ -d "$HOME/www/$DOMAIN" ] || die "Нет папки сайта ~/www/$DOMAIN. Добавьте домен в панели хостинга. Есть: $(ls ~/www 2>/dev/null | tr '\n' ' ')"

  # Node.js
  NODE=""
  if command -v node >/dev/null && [ "$(node_major "$(command -v node)")" -ge 16 ]; then NODE="$(command -v node)"
  elif [ -x "$HOME/node/bin/node" ] && [ "$(node_major "$HOME/node/bin/node")" -ge 16 ]; then NODE="$HOME/node/bin/node"
  else install_node "$HOME/node"; NODE="$HOME/node/bin/node"; fi
  ok "Node.js: $NODE ($("$NODE" -v))"
  export PATH="$(dirname "$NODE"):$PATH"
  if [ "$NODE" = "$HOME/node/bin/node" ] && ! grep -qs 'node/bin' "$HOME/.bashrc"; then
    echo 'export PATH="$HOME/node/bin:$PATH"' >> "$HOME/.bashrc"
    grep -qs bashrc "$HOME/.bash_profile" || echo '[ -f ~/.bashrc ] && . ~/.bashrc' >> "$HOME/.bash_profile"
    ok "Node.js добавлен в PATH (~/.bashrc)"
  fi

  # code
  SELF_DIR="${SED_SELF_DIR:-$(pwd)}"
  APP_DIR="$HOME/sed-zakazy"
  if [ -f "$SELF_DIR/server.js" ] && [ "$SELF_DIR" != "$APP_DIR" ]; then
    case "$SELF_DIR" in "$HOME/www"*) die "Код лежит внутри папки сайта ($SELF_DIR). Перенесите его в ~/sed-zakazy" ;; esac
    APP_DIR="$SELF_DIR"
  fi
  fetch_code "$APP_DIR"
  reexec_if_changed "$APP_DIR"
  smoke_test "$NODE" "$APP_DIR"

  say "Подключаю приложение к сайту через Passenger"
  bash "$APP_DIR/deploy/regru-setup.sh" "$DOMAIN" | sed 's/^/    /'

  say "Проверяю сайт"
  sleep 2
  code=""
  for proto in https http; do
    code="$(curl -s -o /dev/null -w '%{http_code}' --max-time 30 "$proto://$DOMAIN/api/setup" || true)"
    [ "$code" = 200 ] && break
  done
  if [ "$code" = 200 ]; then
    ok "Сайт отвечает: $proto://$DOMAIN"
    if [ "$proto" = https ]; then set_env "$APP_DIR/sed.env" COOKIE_SECURE 1; touch "$APP_DIR/tmp/restart.txt"; ok "Включена защищённая cookie (HTTPS)"
    else warn "Сайт работает только по http. Выпустите SSL-сертификат в панели хостинга и запустите скрипт ещё раз"; fi
  else
    warn "Сайт пока не отвечает (код ${code:-нет ответа}). Проверьте, что домен направлен на хостинг, и откройте его в браузере"
    warn "Если видна ошибка 500, уточните у поддержки хостинга, доступен ли Node.js (Passenger) на тарифе"
  fi

  echo
  say "Готово. Откройте https://$DOMAIN и создайте администратора, если ещё не создан."
  echo "    Обновить: bash $APP_DIR/install.sh $DOMAIN"
  echo "    Данные:   $HOME/sed-zakazy-data (сохраняйте в резервных копиях)"
  exit 0
fi

# ======================================================================
say "Режим: свой сервер (root)"
command -v systemctl >/dev/null && [ -d /run/systemd/system ] || die "Нужен systemd. Для серверов без него используйте Docker (см. README)"

PKG=""
if command -v apt-get >/dev/null; then PKG=apt; elif command -v dnf >/dev/null; then PKG=dnf; elif command -v yum >/dev/null; then PKG=yum; fi
pkg_install() {
  [ -n "$PKG" ] || die "Не найден менеджер пакетов. Установите вручную: $*"
  say "Устанавливаю пакеты: $*"
  case "$PKG" in
    apt) DEBIAN_FRONTEND=noninteractive apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq "$@" >/dev/null ;;
    dnf|yum) "$PKG" install -y -q "$@" >/dev/null ;;
  esac
}
command -v xz >/dev/null || NEED_PKGS="${NEED_PKGS:-} xz-utils"
[ -n "${NEED_PKGS:-}" ] && pkg_install $(echo $NEED_PKGS | sed "s/xz-utils/$([ "$PKG" = apt ] && echo xz-utils || echo xz)/")

APP_DIR=/opt/sed-zakazy
DATA_DIR=/var/lib/sed-zakazy
SVC=sed-zakazy
APP_PORT="${SED_PORT:-3000}"

NODE=/opt/node/bin/node
if [ ! -x "$NODE" ] || [ "$(node_major "$NODE")" -lt 16 ]; then install_node /opt/node; fi
ok "Node.js: $NODE ($("$NODE" -v))"

id sed >/dev/null 2>&1 || { useradd --system --home-dir "$DATA_DIR" --shell /usr/sbin/nologin sed; ok "Создан системный пользователь sed"; }
fetch_code "$APP_DIR"
reexec_if_changed "$APP_DIR"
mkdir -p "$DATA_DIR"; chown -R sed:sed "$DATA_DIR"; chmod 700 "$DATA_DIR"
ENV_FILE="$APP_DIR/sed.env"
set_env "$ENV_FILE" DATA_DIR "$DATA_DIR"
set_env "$ENV_FILE" HOST 127.0.0.1
set_env "$ENV_FILE" PORT "$APP_PORT"
smoke_test "$NODE" "$APP_DIR"

cat > /etc/systemd/system/$SVC.service <<EOF
[Unit]
Description=Управление предприятием
After=network.target

[Service]
Type=simple
User=sed
WorkingDirectory=$APP_DIR
ExecStart=$NODE server.js
Restart=on-failure
NoNewPrivileges=true
ProtectSystem=strict
ProtectHome=true
PrivateTmp=true
ReadWritePaths=$DATA_DIR

[Install]
WantedBy=multi-user.target
EOF
systemctl daemon-reload
systemctl enable --quiet $SVC
systemctl restart $SVC
if wait_http "http://127.0.0.1:$APP_PORT/api/setup"; then ok "Служба $SVC работает на 127.0.0.1:$APP_PORT"
else journalctl -u $SVC -n 30 --no-pager >&2; die "Служба не отвечает, журнал выше"; fi

[[ "$HTTP_PORT" =~ ^[0-9]+$ ]] || die "--port должен быть числом"
command -v nginx >/dev/null || pkg_install nginx
CONF_NAME="${DOMAIN:-sed-zakazy}"
if [ -d /etc/nginx/sites-available ]; then NGX="/etc/nginx/sites-available/$CONF_NAME.conf"; LINK="/etc/nginx/sites-enabled/$CONF_NAME.conf"
else NGX="/etc/nginx/conf.d/$CONF_NAME.conf"; LINK=""; fi
LISTEN="$HTTP_PORT"; SERVER_NAME="${DOMAIN:-_}"
if [ -z "$DOMAIN" ]; then
  # No domain: answer on the server's IP. The stock "Welcome to nginx" site would win, so switch it off.
  if [ -L /etc/nginx/sites-enabled/default ] && [ "$HTTP_PORT" = 80 ]; then
    rm /etc/nginx/sites-enabled/default; ok "Отключена стандартная страница nginx (sites-enabled/default)"
  fi
  if ! grep -rqs "listen.*\b$HTTP_PORT\b.*default_server" /etc/nginx/nginx.conf /etc/nginx/conf.d /etc/nginx/sites-enabled --exclude="$CONF_NAME.conf"; then
    LISTEN="$HTTP_PORT default_server"
  else
    warn "В nginx уже есть другой сайт по умолчанию на порту $HTTP_PORT. Укажите домен или другой порт: --port 8080"
  fi
fi
if [ -f "$NGX" ] && grep -q 'managed by Certbot' "$NGX"; then
  ok "Конфигурация nginx с сертификатом уже есть, не трогаю: $NGX"
else
  cat > "$NGX" <<EOF
# Управление предприятием — создано install.sh
server {
    listen $LISTEN;
    server_name $SERVER_NAME;
    client_max_body_size 55m;
    proxy_request_buffering off;
    location / {
        proxy_pass http://127.0.0.1:$APP_PORT;
        proxy_set_header Host \$host;
        proxy_set_header X-Forwarded-For \$remote_addr;
        proxy_set_header X-Forwarded-Proto \$scheme;
        proxy_read_timeout 600s;
    }
}
EOF
  [ -n "$LINK" ] && ln -sf "$NGX" "$LINK"
  ok "Конфигурация nginx: $NGX"
fi
nginx -t -q || die "Ошибка в конфигурации nginx (nginx -t)"
systemctl enable --quiet nginx; systemctl reload nginx 2>/dev/null || systemctl restart nginx
if command -v ufw >/dev/null && ufw status 2>/dev/null | grep -q 'Status: active'; then
  ufw allow "$HTTP_PORT/tcp" >/dev/null && ok "Брандмауэр ufw: открыт порт $HTTP_PORT"
fi
if wait_http "http://127.0.0.1:$HTTP_PORT/api/setup" -H "Host: ${DOMAIN:-localhost}"; then ok "nginx передаёт запросы приложению (порт $HTTP_PORT)"
else warn "nginx на порту $HTTP_PORT не отвечает приложением. Проверьте: nginx -T | grep -n listen"; fi

HTTPS=no
if [ -n "$EMAIL" ] && [ -z "$DOMAIN" ]; then
  warn "Сертификат выпускается только для домена, --email без домена пропущен"
elif [ -n "$EMAIL" ]; then
  if ! command -v certbot >/dev/null; then
    if [ "$PKG" = apt ]; then pkg_install certbot python3-certbot-nginx; else pkg_install certbot python3-certbot-nginx || true; fi
  fi
  say "Получаю сертификат Let's Encrypt для $DOMAIN"
  if certbot --nginx -d "$DOMAIN" --non-interactive --agree-tos -m "$EMAIL" --redirect --quiet; then
    HTTPS=yes; ok "HTTPS включён"
  else
    warn "Сертификат не выпущен. Проверьте, что A-запись $DOMAIN указывает на этот сервер и открыт порт 80, затем запустите скрипт снова"
  fi
elif grep -qs 'managed by Certbot' "$NGX"; then HTTPS=yes; fi

if [ "$HTTPS" = yes ]; then set_env "$ENV_FILE" COOKIE_SECURE 1; else set_env "$ENV_FILE" COOKIE_SECURE 0; fi
systemctl restart $SVC
wait_http "http://127.0.0.1:$APP_PORT/api/setup" || warn "Служба долго не отвечает после перезапуска: journalctl -u $SVC -n 50"

PORT_SUFFIX=""; [ "$HTTP_PORT" = 80 ] || PORT_SUFFIX=":$HTTP_PORT"
if [ -n "$DOMAIN" ]; then ADDR="$DOMAIN$PORT_SUFFIX"
else ADDR="$(hostname -I 2>/dev/null | awk '{print $1}')$PORT_SUFFIX"; [ "$ADDR" = "$PORT_SUFFIX" ] && ADDR="IP-адрес-сервера$PORT_SUFFIX"; fi
ARGS="${DOMAIN:+ $DOMAIN}"; [ "$HTTP_PORT" = 80 ] || ARGS="$ARGS --port $HTTP_PORT"

echo
if [ "$HTTPS" = yes ]; then say "Готово. Откройте https://$ADDR и создайте администратора, если ещё не создан."
else say "Готово. Откройте http://$ADDR и создайте администратора, если ещё не создан."
  [ -z "$DOMAIN" ] && echo "    Если у сервера есть внешний IP, отличный от показанного, используйте его."
fi
echo "    Обновить:  sudo ${GITHUB_TOKEN:+GITHUB_TOKEN=токен }bash $APP_DIR/install.sh$ARGS"
echo "    Журнал:    journalctl -u $SVC -f"
echo "    Данные:    $DATA_DIR (сохраняйте в резервных копиях)"
