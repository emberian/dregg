#!/usr/bin/env bash
# Build the self-contained renter verifier page.
#
#   1. compile grain-verify-wasm to wasm (getrandom wasm_js backend, selected by
#      .cargo/config.toml for the wasm32 target);
#   2. regenerate the sample fixtures (native gen-fixture bin);
#   3. inline the wasm + glue + fixtures into ONE web/grain-verify.html
#      (build_web.py) — no external network, CSP-safe.
#
# Result: grain-verify-wasm/web/grain-verify.html — open it in any browser.
set -euo pipefail
cd "$(dirname "$0")"

echo "==> compiling wasm (wasm-pack --target web)"
wasm-pack build --target web --out-dir pkg --out-name grain_verify_wasm

echo "==> regenerating sample fixtures"
( cd .. && cargo run -q -p grain-verify-wasm --bin gen-fixture )

echo "==> inlining into web/grain-verify.html"
python3 build_web.py

echo "==> done: web/grain-verify.html"
