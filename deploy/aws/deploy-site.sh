#!/bin/bash
# Build and publish the static ./site bundle on the AWS devnet host.
set -euo pipefail

REPO_DIR="${REPO_DIR:-/opt/dregg}"
SITE_DIR="$REPO_DIR/site"
DIST_DIR="$SITE_DIR/dist"
MANIFEST="$DIST_DIR/artifacts-manifest.json"

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

if [[ ! -f "$DIST_DIR/index.html" || ! -f "$DIST_DIR/explorer/index.html" ]]; then
  echo "site build did not produce expected dist files" >&2
  exit 1
fi

for artifact in \
  "$DIST_DIR/pkg/dregg_wasm.js" \
  "$DIST_DIR/pkg/dregg_wasm_bg.wasm" \
  "$DIST_DIR/extension/dregg-cipherclerk.zip" \
  "$DIST_DIR/extension/dregg-cipherclerk-firefox.xpi"
do
  if [[ ! -s "$artifact" ]]; then
    echo "missing required web artifact: $artifact" >&2
    echo "run ./scripts/build-web-artifacts.sh locally, then rsync site/dist/ to this host" >&2
    exit 1
  fi
done

if [[ ! -f "$MANIFEST" ]]; then
  echo "missing artifact manifest: $MANIFEST" >&2
  echo "run ./scripts/build-web-artifacts.sh before deploy" >&2
  exit 1
fi

sudo install -d -o "$(id -un)" -g "$(id -gn)" "$DIST_DIR"

echo "Installing Caddyfile..."
sudo cp "$REPO_DIR/deploy/aws/caddy/Caddyfile" /etc/caddy/Caddyfile
sudo caddy validate --config /etc/caddy/Caddyfile
sudo systemctl reload caddy

echo "=== Site deployed ==="
echo "Explorer: https://devnet.dregg.fg-goose.online/explorer/"
echo "Site:     https://devnet.dregg.fg-goose.online/"
