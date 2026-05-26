#!/bin/bash
set -euo pipefail

NODE_URL="${NODE_URL:-http://127.0.0.1:8420}"
BOT_URL="${BOT_URL:-http://127.0.0.1:8080}"
ENV_FILE="${ENV_FILE:-/etc/dregg/discord-bot.env}"

echo "=== Dregg Discord bot preflight ==="

if [[ ! -f "$ENV_FILE" ]]; then
  echo "missing environment file: $ENV_FILE" >&2
  exit 1
fi

for key in DISCORD_TOKEN DISCORD_APP_ID BOT_SECRET FEDERATION_ID; do
  if ! grep -Eq "^${key}=.+" "$ENV_FILE"; then
    echo "missing required $key in $ENV_FILE" >&2
    exit 1
  fi
done

if grep -Eq '^DEVNET_API_TOKEN=.+' "$ENV_FILE"; then
  DEVNET_API_TOKEN="$(awk -F= '$1 == "DEVNET_API_TOKEN" { print substr($0, index($0,"=")+1) }' "$ENV_FILE")"
else
  DEVNET_API_TOKEN=""
fi

echo "checking node status..."
status="$(curl -fsS "$NODE_URL/status")"
if ! jq -e '.healthy == true' >/dev/null <<<"$status"; then
  echo "node is reachable but not healthy: $status" >&2
  exit 1
fi

echo "checking node explorer receipts surface..."
receipts="$(curl -fsS "$NODE_URL/api/receipts")"
if ! jq -e 'type == "array"' >/dev/null <<<"$receipts"; then
  echo "node /api/receipts did not return a JSON array: $receipts" >&2
  exit 1
fi

echo "checking node activity event surface..."
events="$(curl -fsS "$NODE_URL/api/events?since_height=0&limit=1")"
if ! jq -e 'type == "array"' >/dev/null <<<"$events"; then
  echo "node /api/events did not return a JSON array: $events" >&2
  exit 1
fi

echo "checking node auth/unlock..."
if [[ -n "$DEVNET_API_TOKEN" ]]; then
  cipherclerk="$(curl -fsS -H "Authorization: Bearer $DEVNET_API_TOKEN" "$NODE_URL/cipherclerk")"
  if ! jq -e '.unlocked == true' >/dev/null <<<"$cipherclerk"; then
    echo "node cipherclerk is not unlocked: $cipherclerk" >&2
    exit 1
  fi
else
  echo "missing DEVNET_API_TOKEN in $ENV_FILE" >&2
  exit 1
fi

echo "checking bot federations..."
curl -fsS "$BOT_URL/api/federations" >/dev/null

echo "checking bot app catalog..."
apps="$(curl -fsS "$BOT_URL/api/apps")"
if ! jq -e 'length > 0' >/dev/null <<<"$apps"; then
  echo "bot app catalog is empty" >&2
  exit 1
fi

echo "checking bot cells..."
curl -fsS "$BOT_URL/api/cells" >/dev/null

echo "checking bot receipts..."
curl -fsS "$BOT_URL/api/receipts/recent" >/dev/null

echo "preflight passed"
