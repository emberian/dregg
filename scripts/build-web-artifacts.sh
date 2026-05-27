#!/usr/bin/env bash
# Build browser-facing artifacts in dependency order:
#   1. wasm/pkg for the site runtime
#   2. extension/dist packages and extension WASM
#   3. site/dist, including fresh wasm/pkg and extension downloads
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/site/dist/artifacts-manifest.json"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

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

echo "=== Writing artifact manifest ==="
cat >"$MANIFEST" <<JSON
{
  "schema": "dregg-web-artifacts-v1",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "artifacts": {
    "pkg/dregg_wasm.js": {
      "bytes": $(wc -c <"$ROOT/site/dist/pkg/dregg_wasm.js" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/pkg/dregg_wasm.js")"
    },
    "pkg/dregg_wasm_bg.wasm": {
      "bytes": $(wc -c <"$ROOT/site/dist/pkg/dregg_wasm_bg.wasm" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/pkg/dregg_wasm_bg.wasm")"
    },
    "extension/dregg-cipherclerk.zip": {
      "bytes": $(wc -c <"$ROOT/site/dist/extension/dregg-cipherclerk.zip" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/extension/dregg-cipherclerk.zip")"
    },
    "extension/dregg-cipherclerk-firefox.xpi": {
      "bytes": $(wc -c <"$ROOT/site/dist/extension/dregg-cipherclerk-firefox.xpi" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/extension/dregg-cipherclerk-firefox.xpi")"
    }
  }
}
JSON

echo "=== Web artifacts ready ==="
echo "Site:      $ROOT/site/dist"
echo "WASM:      $ROOT/site/dist/pkg/dregg_wasm.js"
echo "Extension: $ROOT/site/dist/extension/dregg-cipherclerk.zip"
echo "Manifest:  $MANIFEST"
