#!/bin/bash
# dregg gateway node + Discord bot update path. This script intentionally
# refuses to discard local changes on the host.
set -euo pipefail

REPO_DIR="${REPO_DIR:-/opt/dregg}"
ENV_FILE="${ENV_FILE:-/etc/dregg/discord-bot.env}"

echo "=== Updating dregg gateway node and Discord bot ==="

cd "$REPO_DIR"
git fetch origin main

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "refusing to update: $REPO_DIR has local changes" >&2
  echo "commit, stash, or inspect them before deploying" >&2
  exit 1
fi

git merge --ff-only origin/main

if [[ ! -f "$ENV_FILE" ]]; then
  echo "missing bot env file: $ENV_FILE" >&2
  echo "copy deploy/aws/discord-bot.env.example to $ENV_FILE and fill secrets" >&2
  exit 1
fi

echo "Building..."
cargo build --release -p dregg-node -p dregg-discord-bot

echo "Installing systemd units..."
sudo cp deploy/aws/dregg-gateway.service /etc/systemd/system/dregg-gateway.service
sudo cp deploy/aws/dregg-discord-bot.service /etc/systemd/system/dregg-discord-bot.service
sudo systemctl daemon-reload

echo "Restarting gateway..."
sudo systemctl restart dregg-gateway

echo "Restarting Discord bot..."
sudo install -d -o dregg -g dregg /var/lib/dregg-discord-bot
sudo systemctl restart dregg-discord-bot

echo "Updating Caddyfile if needed..."
if ! diff -q deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile >/dev/null 2>&1; then
  sudo cp deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile
  sudo systemctl reload caddy
fi

echo "Running preflight..."
deploy/aws/preflight-discord-bot.sh

echo "=== Update complete ==="
sudo systemctl status dregg-gateway --no-pager -l | head -20
sudo systemctl status dregg-discord-bot --no-pager -l | head -20
