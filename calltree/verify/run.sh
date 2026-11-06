#!/usr/bin/env bash
# One command, offline: build the Lean checker and the extractor, then verify a recorded call tree.
#   calltree/verify/run.sh [recording] [policy] [root]
# Defaults: the committed GLM fixture, its policy and its root. Needs elan (Lean 4.30 + the
# mathlib cache for the first `lake build`, which only builds the core-only checker) and cargo.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
rec="${1:-$here/../fixtures/glm.recording.json}"
pol="${2:-$here/../fixtures/glm.policy.json}"
root="${3:-$(cat "$here/../fixtures/glm.root")}"
(cd "$repo/metatheory" && lake build calltree-check >/dev/null)
(cd "$here" && cargo build --release -q)
exec "$here/target/release/dregg-calltree-verify" \
  --recording "$rec" --policy "$pol" --root "$root" \
  --extra-root "tool.calltree.invalid=$here/../fixtures/tool-root.der" \
  --checker "$repo/metatheory/.lake/build/bin/calltree-check"
