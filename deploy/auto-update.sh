#!/usr/bin/env bash
# Управление предприятием: автообновление.
# Проверяет GitHub и, если вышла новая версия, запускает install.sh с теми же
# параметрами, что и при установке (они сохранены в .install-args).
# Запускается раз в минуту: на своём сервере таймером systemd, на хостинге — cron.
set -uo pipefail

APP_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$APP_DIR" || exit 0
[ -d .git ] || exit 0

# не запускаться второй раз, пока идёт обновление
if command -v flock >/dev/null; then
  exec 9>"${TMPDIR:-/tmp}/sed-zakazy-update-$(id -u).lock"
  flock -n 9 || exit 0
fi

BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)"
[ "$BRANCH" = HEAD ] && BRANCH=main
SRC=origin
[ -n "${GITHUB_TOKEN:-}" ] && SRC="$(git remote get-url origin | sed "s#https://#https://x-access-token:${GITHUB_TOKEN}@#")"

timeout 50 git fetch --quiet "$SRC" "$BRANCH" 2>/dev/null || exit 0
NEW="$(git rev-parse FETCH_HEAD)"; OLD="$(git rev-parse HEAD)"
[ "$NEW" = "$OLD" ] && exit 0

echo "$(date '+%F %T') обновление ${OLD:0:7} → ${NEW:0:7}"
ARGS=()
if [ -f .install-args ]; then while IFS= read -r a; do [ -n "$a" ] && ARGS+=("$a"); done < .install-args; fi
export SED_AUTO_UPDATE=1
bash "$APP_DIR/install.sh" "${ARGS[@]+"${ARGS[@]}"}" </dev/null
