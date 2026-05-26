#!/bin/sh
# Unlock the local gateway cipherclerk after systemd starts dregg-node.
set -eu

if [ -z "${DEVNET_PASSWORD:-}" ]; then
  exit 0
fi

for _ in $(seq 1 20); do
  if jq -n --arg passphrase "$DEVNET_PASSWORD" '{passphrase:$passphrase}' \
    | curl -fsS -X POST \
      -H "content-type: application/json" \
      --data @- \
      http://127.0.0.1:8420/cipherclerk/unlock >/dev/null
  then
    exit 0
  fi
  sleep 1
done

exit 1
