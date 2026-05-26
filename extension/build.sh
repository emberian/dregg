#!/usr/bin/env bash
# Build, validate, and package the Dragon's Egg Cipherclerk extension.
#
# Usage:
#   ./build.sh          — Build WASM + validate + package
#   ./build.sh wasm     — Only build WASM
#   ./build.sh package  — Only validate + package (skip WASM build)
#   ./build.sh lint     — Run web-ext lint (requires: npm i -g web-ext)
#
# Requirements:
#   - cargo, wasm-bindgen-cli (cargo install wasm-bindgen-cli)
#   - zip (for .zip/.xpi packaging)
#   - web-ext (optional, for Mozilla extension linting)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WASM_CRATE="$PROJECT_ROOT/wasm"
TARGET_DIR="$PROJECT_ROOT/target"
WASM_OUT="$TARGET_DIR/wasm32-unknown-unknown/release/dregg_wasm.wasm"
DIST_DIR="$SCRIPT_DIR/dist"

COMMAND="${1:-all}"

# ---------------------------------------------------------------------------
# Step 1: Build WASM
# ---------------------------------------------------------------------------

build_wasm() {
  echo "[1/4] Building dregg-wasm (release, wasm32-unknown-unknown)..."
  cargo build \
    --manifest-path "$WASM_CRATE/Cargo.toml" \
    -p dregg-wasm \
    --target wasm32-unknown-unknown \
    --release

  if [ ! -f "$WASM_OUT" ]; then
    echo "ERROR: Expected output not found at $WASM_OUT"
    exit 1
  fi

  echo "[2/4] Running wasm-bindgen (--target no-modules for Firefox compat)..."
  wasm-bindgen "$WASM_OUT" \
    --out-dir "$SCRIPT_DIR" \
    --target no-modules \
    --no-typescript \
    --omit-default-module-path

  if [ -f "$SCRIPT_DIR/dregg_wasm_bg.wasm" ] && [ -f "$SCRIPT_DIR/dregg_wasm.js" ]; then
    WASM_SIZE=$(wc -c < "$SCRIPT_DIR/dregg_wasm_bg.wasm" | tr -d ' ')
    echo "  WASM output:"
    echo "    $SCRIPT_DIR/dregg_wasm.js"
    echo "    $SCRIPT_DIR/dregg_wasm_bg.wasm ($WASM_SIZE bytes)"
  else
    echo "ERROR: wasm-bindgen did not produce expected outputs."
    ls -la "$SCRIPT_DIR"/dregg_wasm* 2>/dev/null || true
    exit 1
  fi
}

# ---------------------------------------------------------------------------
# Step 2: Validate manifest
# ---------------------------------------------------------------------------

validate_manifest() {
  echo "[3/4] Validating manifest.json..."

  if [ ! -f "$SCRIPT_DIR/manifest.json" ]; then
    echo "ERROR: manifest.json not found"
    exit 1
  fi

  # Check JSON is well-formed.
  if ! python3 -c "import json; json.load(open('$SCRIPT_DIR/manifest.json'))" 2>/dev/null; then
    if ! node -e "JSON.parse(require('fs').readFileSync('$SCRIPT_DIR/manifest.json','utf8'))" 2>/dev/null; then
      echo "ERROR: manifest.json is not valid JSON"
      exit 1
    fi
  fi

  # Check required fields.
  local manifest_version
  manifest_version=$(python3 -c "import json; print(json.load(open('$SCRIPT_DIR/manifest.json')).get('manifest_version',''))" 2>/dev/null || echo "")
  if [ "$manifest_version" != "3" ]; then
    echo "WARNING: manifest_version is not 3 (got: $manifest_version)"
  fi

  # Check no "type": "module" in background (Firefox compat).
  if grep -q '"type".*:.*"module"' "$SCRIPT_DIR/manifest.json"; then
    echo "ERROR: manifest.json contains \"type\": \"module\" in background — Firefox incompatible"
    exit 1
  fi

  # Check all referenced files exist.
  # P2-1: the manifest points to dist/* — validate those, not legacy root .js
  # duplicates.
  local missing=0
  for file in dist/background.js dist/content.js dist/page.js popup.html dist/popup-script.js settings.html settings-script.js; do
    if [ ! -f "$SCRIPT_DIR/$file" ]; then
      echo "  WARNING: Referenced file missing: $file"
      missing=$((missing + 1))
    fi
  done

  if [ "$missing" -eq 0 ]; then
    echo "  Manifest valid. All referenced files present."
  else
    echo "  Manifest valid but $missing referenced file(s) missing."
  fi
}

# ---------------------------------------------------------------------------
# Step 3: Package extension
# ---------------------------------------------------------------------------

package_extension() {
  echo "[4/4] Packaging extension..."

  mkdir -p "$DIST_DIR"

  # Files to include in the package.
  # P2-1: ship only the TS-compiled dist/ scripts for background/content/page/popup,
  # not the legacy root .js files. Static popup HTML + their dedicated JS still ship
  # from the root (they're not TS-built today).
  local FILES=(
    manifest.json
    dist/background.js
    dist/content.js
    dist/page.js
    popup.html
    dist/popup-script.js
    settings.html
    settings-script.js
    provision.html
    provision.js
    recovery.html
    recovery.js
    confirm-intent.html
    confirm-intent-script.js
    disclosure-picker.html
    disclosure-picker.js
    origin-permission.html
    origin-permission-script.js
    share-capability.html
    share-capability.js
    bip39_english.txt
  )

  # Add WASM files if they exist.
  if [ -f "$SCRIPT_DIR/dregg_wasm.js" ]; then
    FILES+=(dregg_wasm.js)
  fi
  if [ -f "$SCRIPT_DIR/dregg_wasm_bg.wasm" ]; then
    FILES+=(dregg_wasm_bg.wasm)
  fi

  # Build the file list (only include files that actually exist).
  local EXISTING_FILES=()
  for f in "${FILES[@]}"; do
    if [ -f "$SCRIPT_DIR/$f" ]; then
      EXISTING_FILES+=("$f")
    fi
  done

  # Chrome: .zip
  local ZIP_NAME="dregg-cipherclerk-chrome.zip"
  (cd "$SCRIPT_DIR" && zip -q -r "$DIST_DIR/$ZIP_NAME" "${EXISTING_FILES[@]}")
  local ZIP_SIZE
  ZIP_SIZE=$(wc -c < "$DIST_DIR/$ZIP_NAME" | tr -d ' ')
  echo "  Chrome package: $DIST_DIR/$ZIP_NAME ($ZIP_SIZE bytes)"

  # Firefox: .xpi (same format as zip, different extension)
  local XPI_NAME="dregg-cipherclerk-firefox.xpi"
  cp "$DIST_DIR/$ZIP_NAME" "$DIST_DIR/$XPI_NAME"
  echo "  Firefox package: $DIST_DIR/$XPI_NAME ($ZIP_SIZE bytes)"

  echo ""
  echo "Done. Packages in: $DIST_DIR/"
}

# ---------------------------------------------------------------------------
# Step 4 (optional): Lint with web-ext
# ---------------------------------------------------------------------------

lint_extension() {
  if ! command -v web-ext &>/dev/null; then
    echo "web-ext not found. Install with: npm install -g web-ext"
    echo "Skipping lint."
    return 0
  fi

  echo "Running web-ext lint..."
  web-ext lint --source-dir "$SCRIPT_DIR" --self-hosted || true
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

case "$COMMAND" in
  wasm)
    build_wasm
    ;;
  package)
    validate_manifest
    package_extension
    ;;
  lint)
    lint_extension
    ;;
  all)
    build_wasm
    validate_manifest
    package_extension
    echo ""
    echo "Extension built and packaged successfully."
    echo "Load in Chrome: chrome://extensions > Load unpacked > $SCRIPT_DIR"
    echo "Load in Firefox: about:debugging > This Firefox > Load Temporary Add-on > $DIST_DIR/$XPI_NAME"
    ;;
  *)
    echo "Usage: $0 [wasm|package|lint|all]"
    exit 1
    ;;
esac
