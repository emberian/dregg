#!/usr/bin/env bash
# bootstrap.sh — from a fresh clone to a working verified-executor build, one command.
#
#   ./scripts/bootstrap.sh
#
# What this does (idempotent — every step skips itself when already satisfied):
#   1. checks the toolchain prerequisites (cargo, elan/lake) and TEACHES the fix when absent;
#   2. checks the mathlib checkout the Lean build requires (metatheory/lakefile.toml pins
#      mathlib as a LOCAL PATH dependency — a fresh machine does not have it);
#   3. `lake build`s the verified executor's FFI module (incremental; the FIRST run compiles
#      mathlib and takes a long time — see the note printed at that step);
#   4. seeds dregg-lean-ffi/libdregg_lean.a (the static archive of the compiled Lean kernel;
#      ~6000 objects, one-time — afterwards `cargo build` keeps it fresh automatically);
#   5. verifies the result by running the FFI smoke binary: Rust calls the PROVED Lean
#      kernel over the C ABI and asserts conservation/authority round-trips.
#
# Without this, `cargo build` still SUCCEEDS — but in a degraded "marshal-only" mode where
# `lean_available()` is false and the node falls back to the unverified Rust executor.
# The whole point of dregg is that the verified Lean executor IS the executor; run this once.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"

step()  { printf '\n==> %s\n' "$*"; }
die()   { printf '\nFATAL: %s\n' "$*" >&2; exit 1; }

# ── 1. prerequisites ─────────────────────────────────────────────────────────
step "Checking prerequisites"

command -v cargo >/dev/null 2>&1 || die "cargo not on PATH.
  Install Rust via rustup:  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  (the repo's rust-toolchain.toml pins the exact toolchain; rustup picks it up automatically)"

command -v lake >/dev/null 2>&1 || die "lake (the Lean 4 build tool) not on PATH.
  Install elan (the Lean toolchain manager):
      curl https://elan.lean-lang.org/elan-init.sh -sSf | sh     # or: brew install elan-init
  then re-open your shell (elan puts ~/.elan/bin on PATH) and re-run this script.
  elan will auto-install the pinned toolchain ($(cat "$META/lean-toolchain" 2>/dev/null || echo 'see metatheory/lean-toolchain')) on first use."

echo "  cargo: $(command -v cargo)"
echo "  lake:  $(command -v lake)"

# ── 2. the mathlib path dependency ───────────────────────────────────────────
# metatheory/lakefile.toml requires mathlib as a LOCAL PATH dependency (it avoids
# re-resolving the registry on every build). A fresh machine must put a mathlib
# checkout at that path, at the pinned revision, BEFORE any lake command works.
step "Checking the mathlib path dependency"

MATHLIB_REL="$(sed -n 's/^path = "\(.*\)"/\1/p' "$META/lakefile.toml" | head -1)"
[ -n "$MATHLIB_REL" ] || die "could not read the mathlib path from $META/lakefile.toml"
# An absolute pin must not be joined onto $META — "$META//abs/path" exists on nobody's
# machine (the FATAL a repointed-to-absolute lakefile used to produce here). Relative
# pins resolve against metatheory/, matching lake.
case "$MATHLIB_REL" in
  /*) MATHLIB_DIR="$MATHLIB_REL" ;;
  *)  MATHLIB_DIR="$META/$MATHLIB_REL" ;;
esac
# The pinned revision is named in the lakefile comment (a 40-hex sha).
MATHLIB_REV="$(grep -oE '[0-9a-f]{40}' "$META/lakefile.toml" | head -1 || true)"

# lake resolves the dependency from lake-manifest.json, NOT the lakefile: a lakefile
# repoint with a stale manifest passes every check below and then fails the lake build
# with a path this script never looked at ("package directory not found: <old pin>").
# Catch the disagreement here, where the fix can be taught.
MANIFEST="$META/lake-manifest.json"
if [ -f "$MANIFEST" ]; then
  MANIFEST_DIR="$(awk '/"name": "mathlib"/{f=1} f && /"dir":/{sub(/.*"dir": "/,""); sub(/",?.*/,""); print; exit}' "$MANIFEST")"
  if [ -n "$MANIFEST_DIR" ] && [ "$MANIFEST_DIR" != "$MATHLIB_REL" ]; then
    die "mathlib path DISAGREEMENT between the lakefile and the lake manifest:
      metatheory/lakefile.toml       pins   path = \"$MATHLIB_REL\"
      metatheory/lake-manifest.json  locks  \"dir\": \"$MANIFEST_DIR\"

  lake resolves the dependency from the MANIFEST, so the lakefile pin alone never
  takes effect — the lake build below would fail with:
      error: mathlib: package directory not found: $MANIFEST_DIR

  Fix: point BOTH files at the same mathlib checkout (edit the \"dir\" of the mathlib
  entry in metatheory/lake-manifest.json to match the lakefile), then re-run."
  fi
fi

if [ ! -f "$MATHLIB_DIR/lakefile.lean" ]; then
  die "mathlib checkout MISSING at: $MATHLIB_DIR
  (metatheory/lakefile.toml pins mathlib as the local path '$MATHLIB_REL' — relative
  pins resolve against metatheory/. With the repo's default pin that expects the
  sibling layout <root>/src/dregg + <root>/src/mathlib4; an absolute pin is honored
  as-is. Nothing Lean builds until it exists.)

  Put it there at the pinned revision:
      git clone https://github.com/leanprover-community/mathlib4 \"$MATHLIB_DIR\"
      git -C \"$MATHLIB_DIR\" checkout ${MATHLIB_REV:-<the rev named in metatheory/lakefile.toml>}
      ( cd \"$MATHLIB_DIR\" && lake exe cache get )   # prebuilt mathlib artifacts; HIGHLY recommended

  then re-run this script. ('lake exe cache get' downloads mathlib's prebuilt build
  products; without it the first build compiles mathlib from source — hours.)"
fi
if [ -n "$MATHLIB_REV" ] && command -v git >/dev/null 2>&1 && [ -d "$MATHLIB_DIR/.git" ]; then
  HAVE_REV="$(git -C "$MATHLIB_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
  if [ "$HAVE_REV" != "$MATHLIB_REV" ]; then
    echo "  WARNING: mathlib checkout is at $HAVE_REV"
    echo "           but metatheory/lakefile.toml pins  $MATHLIB_REV"
    echo "           A mismatched mathlib usually fails the lake build; if it does:"
    echo "               git -C \"$MATHLIB_DIR\" checkout $MATHLIB_REV"
  else
    echo "  mathlib: $MATHLIB_DIR @ $HAVE_REV (matches the pin)"
  fi
else
  echo "  mathlib: $MATHLIB_DIR (present)"
fi

# ── 3. build the verified executor (Lean → C facets) ────────────────────────
step "lake build Dregg2.Exec.FFI (incremental; FIRST run compiles mathlib — long)"
( cd "$META" && lake build Dregg2.Exec.FFI ) \
  || die "lake build failed. Common causes:
  * mathlib checkout at the wrong revision (see the pin check above);
  * a partial earlier build — re-running this script resumes it (lake is incremental)."

# ── 4. seed the static archive (one-time) ────────────────────────────────────
if [ -f "$ARCH" ]; then
  step "libdregg_lean.a already present ($(du -h "$ARCH" | cut -f1 | tr -d ' ')) — skipping the seed"
  echo "  (this seed is read-only; cargo build copies it into OUT_DIR and keeps THAT copy's"
  echo "   Dregg2 objects fresh automatically. To re-seed from scratch — only needed when the"
  echo "   toolchain/mathlib pin changes — delete it and re-run, or run"
  echo "   dregg-lean-ffi/scripts/seed-dregg2-closure.sh directly.)"
else
  step "Seeding dregg-lean-ffi/libdregg_lean.a (one-time; compiles the whole closure)"
  "$ROOT/dregg-lean-ffi/scripts/seed-dregg2-closure.sh"
fi

# ── 5. verify: Rust calls the proved Lean kernel for real ───────────────────
step "Verification: cargo builds the FFI crate and the smoke binary round-trips the kernel"
CHECK_LOG="$(mktemp)"
# NOTE: the verification MUST pass `--features lean-lib` — that feature is what
# links `libdregg_lean.a` (without it the crate builds the degraded "marshal-only"
# path, and the smoke binary `dregg-lean-ffi` has `required-features = ["lean-lib"]`
# so it won't even be selected). Omitting the flag here false-fails a kernel that
# is in fact linkable (the Lunar Town Council Fork-B finding, 2026-06-22).
if ! ( cd "$ROOT" && cargo build -p dregg-lean-ffi --features lean-lib 2>&1 | tee "$CHECK_LOG" ); then
  die "cargo build -p dregg-lean-ffi --features lean-lib failed — see output above."
fi
if grep -q "marshal-only" "$CHECK_LOG"; then
  die "the FFI crate still built MARSHAL-ONLY (the Lean kernel is not linked).
  Read the cargo warnings above — they name the exact missing piece."
fi
( cd "$ROOT" && cargo run -q -p dregg-lean-ffi --features lean-lib --bin dregg-lean-ffi ) \
  || die "the FFI smoke binary failed — the linked Lean kernel did not round-trip."

step "DONE. The verified Lean executor is linked and answering."
echo "  Next: QUICKSTART.md (build the CLI, run a node, run the demo)."
