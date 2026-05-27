#!/usr/bin/env bash
# Build browser-facing artifacts in dependency order:
#   1. wasm/pkg for the site runtime
#   2. extension/dist packages and extension WASM
#   3. site/dist, including fresh wasm/pkg and extension downloads
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "=== Building wasm/pkg ==="
wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

echo "=== Refreshing site/pkg from wasm/pkg ==="
rm -rf "$ROOT/site/pkg/dregg_wasm"* "$ROOT/site/pkg/package.json" "$ROOT/site/pkg/.gitignore"
cp -R "$ROOT/wasm/pkg/." "$ROOT/site/pkg/"

echo "=== Building extension scripts and packages ==="
(cd "$ROOT/extension" && npm run build && ./build.sh package)

echo "=== Publishing extension downloads into site/extension ==="
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-cipherclerk.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-wallet.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-firefox.xpi" "$ROOT/site/extension/dregg-cipherclerk-firefox.xpi"

echo "=== Building site/dist ==="
(cd "$ROOT/site" && npm run build)

echo "=== Web artifacts ready ==="
echo "Site:      $ROOT/site/dist"
echo "WASM:      $ROOT/site/dist/pkg/dregg_wasm.js"
echo "Extension: $ROOT/site/dist/extension/dregg-cipherclerk.zip"
