#!/bin/sh
# Unlock the local gateway cipherclerk after systemd starts dregg-node, and
# persist the current bearer token for local services that call protected APIs.
set -eu

if [ -z "${DEVNET_PASSWORD:-}" ]; then
  exit 0
fi

write_token_env() {
  file="$1"
  token="$2"

  if [ -z "$token" ] || [ ! -f "$file" ] || [ ! -w "$file" ]; then
    return 0
  fi

  dir="$(dirname "$file")"
  tmp="$(mktemp "$dir/.env.XXXXXX")"
  grep -v '^DEVNET_API_TOKEN=' "$file" >"$tmp" || true
  printf 'DEVNET_API_TOKEN=%s\n' "$token" >>"$tmp"
  chmod --reference="$file" "$tmp" 2>/dev/null || chmod 600 "$tmp"
  chown --reference="$file" "$tmp" 2>/dev/null || true
  mv "$tmp" "$file"
}

for _ in $(seq 1 20); do
  response="$(jq -n --arg passphrase "$DEVNET_PASSWORD" '{passphrase:$passphrase}' \
    | curl -fsS -X POST \
      -H "content-type: application/json" \
      --data @- \
      http://127.0.0.1:8420/cipherclerk/unlock 2>/dev/null || true)"
  if [ -n "$response" ] && [ "$(printf '%s' "$response" | jq -r '.success // false')" = "true" ]; then
    token="$(printf '%s' "$response" | jq -r '.bearer_token // empty')"
    write_token_env /etc/dregg/node.env "$token"
    write_token_env /etc/dregg/discord-bot.env "$token"
    exit 0
  fi
  sleep 1
done

exit 1
