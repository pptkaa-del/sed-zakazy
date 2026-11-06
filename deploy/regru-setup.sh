#!/bin/bash
# Настройка на виртуальном хостинге reg.ru (Apache + Passenger).
# Запуск по SSH:  bash ~/sed-zakazy/deploy/regru-setup.sh sed.example.ru
set -e

DOMAIN="$1"
if [ -z "$DOMAIN" ]; then
  echo "Укажите домен сайта: bash $0 sed.example.ru"; exit 1
fi

APP_DIR="$(cd "$(dirname "$0")/.." && pwd)"
WWW="$HOME/www/$DOMAIN"
DATA="$HOME/sed-zakazy-data"

if [ ! -d "$WWW" ]; then
  echo "Не найдена папка сайта $WWW."
  echo "Добавьте домен в панели хостинга или проверьте имя: ls ~/www"
  exit 1
fi
case "$APP_DIR" in
  "$WWW"*) echo "Приложение лежит внутри папки сайта ($APP_DIR). Перенесите папку sed-zakazy в домашнюю: mv \"$APP_DIR\" ~/"; exit 1 ;;
esac

NODE="$(command -v node || true)"
if [ -z "$NODE" ]; then
  echo "Node.js не найден. Установите его через nvm (см. README, раздел reg.ru) и запустите скрипт снова."; exit 1
fi
if ! "$NODE" -e 'process.exit(+process.versions.node.split(".")[0] >= 16 ? 0 : 1)'; then
  echo "Нужен Node.js 16 или новее, сейчас $("$NODE" -v)."; exit 1
fi
NODE="$(readlink -f "$NODE")"

if [ -f "$WWW/.htaccess" ] && ! grep -qE '^# (Документооборот по заказам|Управление предприятием)' "$WWW/.htaccess"; then
  cp "$WWW/.htaccess" "$WWW/.htaccess.bak.$(date +%Y%m%d-%H%M%S)"
  echo "Прежний .htaccess сохранён рядом с суффиксом .bak"
fi
cat > "$WWW/.htaccess" <<EOF
# Управление предприятием: Node.js через Passenger
PassengerAppRoot $APP_DIR
PassengerAppType node
PassengerStartupFile server.js
PassengerNodejs $NODE
EOF

# A placeholder index.html / index.php in the site folder would be served instead of the app.
for f in "$WWW"/index.html "$WWW"/index.htm "$WWW"/index.php; do
  if [ -f "$f" ]; then mv "$f" "$f.bak"; echo "Заглушка $(basename "$f") переименована в $(basename "$f").bak"; fi
done

mkdir -p "$DATA" "$APP_DIR/tmp"
chmod 700 "$DATA"
if [ ! -f "$APP_DIR/sed.env" ]; then
  printf 'DATA_DIR=%s\n# После выпуска SSL-сертификата раскомментируйте:\n# COOKIE_SECURE=1\n' "$DATA" > "$APP_DIR/sed.env"
fi
touch "$APP_DIR/tmp/restart.txt"

echo
echo "Готово."
echo "  Приложение:  $APP_DIR"
echo "  Данные:      $DATA"
echo "  Node.js:     $NODE ($("$NODE" -v))"
echo "  .htaccess:   $WWW/.htaccess"
echo
echo "Откройте https://$DOMAIN и создайте администратора."
echo "Перезапуск после обновления файлов: touch $APP_DIR/tmp/restart.txt"
