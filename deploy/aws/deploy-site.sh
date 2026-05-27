#!/bin/bash
# Build and publish the static ./site bundle on the AWS devnet host.
set -euo pipefail

REPO_DIR="${REPO_DIR:-/opt/dregg}"
SITE_DIR="$REPO_DIR/site"

echo "=== Deploying dregg static site ==="

cd "$SITE_DIR"

if [[ "${BUILD_WEB_ARTIFACTS:-0}" == "1" && -x "$REPO_DIR/scripts/build-web-artifacts.sh" ]]; then
  "$REPO_DIR/scripts/build-web-artifacts.sh"
elif command -v npm >/dev/null 2>&1; then
  if [[ ! -d node_modules ]]; then
    npm ci
  fi
  npm run build
else
  echo "npm not found; using prebuilt $SITE_DIR/dist"
fi

if [[ ! -f "$SITE_DIR/dist/index.html" || ! -f "$SITE_DIR/dist/explorer/index.html" ]]; then
  echo "site build did not produce expected dist files" >&2
  exit 1
fi

sudo install -d -o "$(id -un)" -g "$(id -gn)" "$SITE_DIR/dist"

echo "Installing Caddyfile..."
sudo cp "$REPO_DIR/deploy/aws/caddy/Caddyfile" /etc/caddy/Caddyfile
sudo caddy validate --config /etc/caddy/Caddyfile
sudo systemctl reload caddy

echo "=== Site deployed ==="
echo "Explorer: https://devnet.dregg.fg-goose.online/explorer/"
echo "Site:     https://devnet.dregg.fg-goose.online/"
