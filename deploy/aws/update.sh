#!/bin/bash
# pyana gateway node — pull latest and rebuild
set -euo pipefail

echo "=== Updating pyana gateway node ==="

cd /opt/pyana
git fetch origin main
git reset --hard origin/main

echo "Building..."
cargo build --release -p pyana-node

echo "Restarting service..."
sudo systemctl restart pyana-gateway

# Update static site assets
sudo cp -r site/explorer/* /opt/pyana/site/explorer/ 2>/dev/null || true
sudo cp -r site/playground/* /opt/pyana/site/playground/ 2>/dev/null || true

# Check if Caddyfile changed
if ! diff -q deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile &>/dev/null; then
  echo "Caddyfile changed, reloading Caddy..."
  sudo cp deploy/aws/caddy/Caddyfile /etc/caddy/Caddyfile
  sudo systemctl reload caddy
fi

echo "=== Update complete ==="
echo "Check status: sudo systemctl status pyana-gateway"
sudo systemctl status pyana-gateway --no-pager -l | head -20
