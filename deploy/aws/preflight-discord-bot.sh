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
if ! jq -e '(.public_key | type == "string" and length == 64)' >/dev/null <<<"$status"; then
  echo "node status is missing a 32-byte public_key: $status" >&2
  exit 1
fi

echo "checking node explorer receipts surface..."
receipts="$(curl -fsS "$NODE_URL/api/receipts")"
if ! jq -e 'type == "array"' >/dev/null <<<"$receipts"; then
  echo "node /api/receipts did not return a JSON array: $receipts" >&2
  exit 1
fi
if ! jq -e 'all(.[]; (.receipt_hash | type == "string" and length == 64) and (.turn_hash | type == "string" and length == 64) and (.chain_index | type == "number") and (.chain_head | type == "boolean") and (.has_witness | type == "boolean") and (.witness_count | type == "number"))' >/dev/null <<<"$receipts"; then
  echo "node /api/receipts returned entries without chain/hash/witness fields: $receipts" >&2
  exit 1
fi
head_receipt="$(jq -r 'map(select(.chain_head == true)) | .[0].receipt_hash // empty' <<<"$receipts")"
if [[ -n "$head_receipt" ]]; then
  witnesses="$(curl -fsS "$NODE_URL/api/receipts/$head_receipt/witnesses")"
  if ! jq -e '(.receipt_hash | type == "string" and length == 64) and (.witness_count | type == "number") and (.witnessed_receipts | type == "array")' >/dev/null <<<"$witnesses"; then
    echo "node receipt witness endpoint returned an unexpected shape: $witnesses" >&2
    exit 1
  fi
fi

echo "checking node activity event surface..."
events="$(curl -fsS "$NODE_URL/api/events?since_height=0&limit=1")"
if ! jq -e 'type == "array"' >/dev/null <<<"$events"; then
  echo "node /api/events did not return a JSON array: $events" >&2
  exit 1
fi
if ! jq -e 'all(.[]; (.height | type == "number") and (.turn_hash | type == "string") and (.cell_id | type == "string") and (.effects | type == "array") and (.timestamp | type == "number") and (.proof_status | type == "string"))' >/dev/null <<<"$events"; then
  echo "node /api/events returned entries without committed-event fields: $events" >&2
  exit 1
fi

echo "checking node auth/unlock..."
if [[ -n "$DEVNET_API_TOKEN" ]]; then
  cipherclerk="$(curl -fsS -H "Authorization: Bearer $DEVNET_API_TOKEN" "$NODE_URL/cipherclerk")"
  if ! jq -e '.unlocked == true' >/dev/null <<<"$cipherclerk"; then
    echo "node cipherclerk is not unlocked: $cipherclerk" >&2
    exit 1
  fi
  encryption_key="$(curl -fsS -H "Authorization: Bearer $DEVNET_API_TOKEN" "$NODE_URL/api/turns/encryption-key")"
  if ! jq -e '(.executor_x25519_public | type == "string" and length == 64) and (.derivation_domain == "dregg-turn-unsealer-v1")' >/dev/null <<<"$encryption_key"; then
    echo "node encrypted-turn key discovery is not wired: $encryption_key" >&2
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
