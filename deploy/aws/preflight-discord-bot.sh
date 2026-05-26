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

echo "checking node status..."
curl -fsS "$NODE_URL/status" >/dev/null

echo "checking bot federations..."
curl -fsS "$BOT_URL/api/federations" >/dev/null

echo "checking bot cells..."
curl -fsS "$BOT_URL/api/cells" >/dev/null

echo "checking bot receipts..."
curl -fsS "$BOT_URL/api/receipts/recent" >/dev/null

echo "preflight passed"
