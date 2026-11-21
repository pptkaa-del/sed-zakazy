#!/usr/bin/env bash
# Управление предприятием: автообновление.
# Проверяет GitHub и, если вышла новая версия, запускает install.sh с теми же
# параметрами, что и при установке (они сохранены в .install-args).
# Запускается раз в минуту: на своём сервере таймером systemd, на хостинге — cron.
set -uo pipefail

APP_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$APP_DIR" || exit 0

# не запускаться второй раз, пока идёт обновление
if command -v flock >/dev/null; then
  exec 9>"${TMPDIR:-/tmp}/sed-zakazy-update-$(id -u).lock"
  flock -n 9 || exit 0
fi

ARGS=()
if [ -f .install-args ]; then while IFS= read -r a; do [ -n "$a" ] && ARGS+=("$a"); done < .install-args; fi
export SED_AUTO_UPDATE=1

# installed from an archive (--archive): a new version is a changed archive
ARCH=""; for i in "${!ARGS[@]}"; do [ "${ARGS[$i]}" = "--archive" ] && ARCH="${ARGS[$((i + 1))]:-}"; done
if [ -n "$ARCH" ]; then
  if printf '%s' "$ARCH" | grep -qiE '^https?://'; then
    # cheap check first: the headers of the file (ETag, Last-Modified, size); the file itself is taken only when they change
    HEAD="$(timeout 30 curl -fsSIL "$ARCH" 2>/dev/null | tr -d '\r' | grep -iE '^(etag|last-modified|content-length):' | sort | tr '\n' ' ')" || exit 0
    [ -n "$HEAD" ] && [ -f .archive-head ] && [ "$HEAD" = "$(cat .archive-head)" ] && exit 0
    TMP="$(mktemp)"; timeout 300 curl -fsSL -o "$TMP" "$ARCH" 2>/dev/null || { rm -f "$TMP"; exit 0; }
  else
    [ -f "$ARCH" ] || exit 0; HEAD=""; TMP="$(mktemp)"; cp "$ARCH" "$TMP"
  fi
  NEW="$(sha256sum "$TMP" | cut -c1-64)"; rm -f "$TMP"
  if [ "$NEW" != "$(cat .archive-sum 2>/dev/null)" ]; then
    echo "$(date '+%F %T') обновление из архива → ${NEW:0:12}"
    bash "$APP_DIR/install.sh" "${ARGS[@]+"${ARGS[@]}"}" </dev/null || exit 0
  fi
  [ -n "$HEAD" ] && printf '%s' "$HEAD" > .archive-head
  exit 0
fi

[ -d .git ] || exit 0
BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)"
[ "$BRANCH" = HEAD ] && BRANCH=main
SRC=origin
[ -n "${GITHUB_TOKEN:-}" ] && SRC="$(git remote get-url origin | sed "s#https://#https://x-access-token:${GITHUB_TOKEN}@#")"

timeout 50 git fetch --quiet "$SRC" "$BRANCH" 2>/dev/null || exit 0
NEW="$(git rev-parse FETCH_HEAD)"; OLD="$(git rev-parse HEAD)"
[ "$NEW" = "$OLD" ] && exit 0

echo "$(date '+%F %T') обновление ${OLD:0:7} → ${NEW:0:7}"
bash "$APP_DIR/install.sh" "${ARGS[@]+"${ARGS[@]}"}" </dev/null
