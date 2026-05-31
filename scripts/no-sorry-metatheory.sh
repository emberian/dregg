#!/usr/bin/env bash
# WF-ZERO-SORRY — CI guard: forbid `sorry` in the dregg2 metatheory FOREVER.
#
# Background: the metatheory (`metatheory/`, a Lean4 / mathlib corpus built via
# `metatheory/lakefile.toml`) is dregg2's machine-checked theory. A `sorry`
# anywhere in it silently turns a "PROVED" keystone into an unproven hole — the
# whole point of the corpus is that there are none. The previous phase
# (WF-ZERO-SORRY) retired the last 3 by-design sorries; the corpus is at ZERO.
#
# This is the COMPREHENSIVE net. There are two complementary layers:
#
#   (a) THIS SCRIPT — the textual / build-warning guard. It runs the real
#       `lake build` and FAILS if Lean emits ANY `declaration uses \`sorry\``
#       warning (Lean 4.30 quotes the word in BACKTICKS, not single quotes —
#       see the CRITICAL note below), or if the build mentions `sorryAx`.
#       Because Lean emits that warning for EVERY declaration that closes a
#       goal with `sorry`, `admit`, or `sorryAx`, this catches such a hole
#       ANYWHERE in the corpus, whether or not it is pinned in
#       `Dregg2/Claims.lean`. This is the whole-corpus guarantee.
#
#   (b) `metatheory/Dregg2/Claims.lean` — the build-ENFORCED Lean assertion
#       layer. It pins keystones with `#assert_axioms` (per-decl) and
#       `#assert_namespace_axioms` (per-namespace), each ELABORATING TO AN
#       ERROR if the named decl/namespace transitively depends on `sorryAx`.
#       That layer is STRONGER (it proves there is no *transitive/inherited*
#       sorry, even one hidden behind a renamed lemma) but is only as wide as
#       its pin list — it is per-decl/per-namespace, NOT whole-corpus. The
#       honest division of labor: (b) is deep-but-targeted, (a) here is the
#       broad textual net that needs no enumeration to stay comprehensive.
#
# Run from the repo root: `scripts/no-sorry-metatheory.sh`
# In CI, `elan`/`lake` are installed by the leanprover/lean-action step (or the
# elan path is exported); locally export `PATH=$HOME/.elan/bin:$PATH` first.

set -uo pipefail

ROOT="${1:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
META="$ROOT/metatheory"

# Locate lake. Prefer one already on PATH (CI installs it there); fall back to
# the conventional elan location used on dev machines.
if command -v lake >/dev/null 2>&1; then
    LAKE="$(command -v lake)"
elif [ -x "$HOME/.elan/bin/lake" ]; then
    LAKE="$HOME/.elan/bin/lake"
    export PATH="$HOME/.elan/bin:$PATH"
else
    echo "no-sorry-metatheory.sh: FATAL — could not find \`lake\`."
    echo "  Install the elan toolchain (leanprover/lean-action) or put lake on PATH."
    exit 2
fi

echo "no-sorry-metatheory.sh: using lake at $LAKE"
echo "no-sorry-metatheory.sh: building $META ..."

LOG="$(mktemp -t metatheory-build.XXXXXX.log)"
trap 'rm -f "$LOG"' EXIT

# Build the whole corpus. We capture the exit code explicitly — a head/tail
# pipe would MASK it — and we keep the full log for the grep below.
( cd "$META" && "$LAKE" build ) > "$LOG" 2>&1
build_status=$?

# ── Layer (a.1): the `sorry`-warning net (the comprehensive one). ──────────
# Lean prints this warning for EVERY declaration closed with `sorry`, `admit`,
# OR `sorryAx` — `admit` and `sorryAx` both elaborate through the `sorry`
# machinery and emit the identical warning (verified: a `by admit` proof emits
# `declaration uses \`sorry\``). So this single grep is the whole-corpus net
# covering all three.
#
# CRITICAL — the quoting. Lean 4.30 wraps the word in BACKTICKS:
#   `declaration uses ` + backtick + `sorry` + backtick`
# NOT single quotes. A guard grepping for `declaration uses 'sorry'` (single
# quotes) would NEVER match and would be a TOOTHLESS no-op. We therefore match
# with a `.` wildcard for the surrounding quote char, so the guard keeps its
# teeth across Lean versions that use either backticks or single quotes.
sorry_warnings=$(grep -cE "declaration uses .sorry." "$LOG")

# ── Layer (a.2): defensive `sorryAx` net (build output). ───────────────────
# `sorryAx` can also surface by name via `#print axioms` / `#assert_axioms`
# lines. The Claims.lean ledger already turns an INHERITED `sorryAx` into a
# hard build ERROR; we additionally fail loudly here on any literal mention of
# the constant name in the build log, belt-and-suspenders.
sorryax_hits=$(grep -cE "sorryAx" "$LOG")

fail=0

if [ "$build_status" -ne 0 ]; then
    echo
    echo "no-sorry-metatheory.sh: the metatheory \`lake build\` FAILED (exit $build_status)."
    echo "  A green build is a precondition for the zero-sorry guarantee."
    echo "  --- last 40 lines of build log ---"
    tail -n 40 "$LOG"
    fail=1
fi

if [ "$sorry_warnings" -gt 0 ]; then
    echo
    echo "no-sorry-metatheory.sh: FOUND $sorry_warnings \`sorry\`/\`admit\` warning(s)."
    echo "  The dregg2 metatheory must remain at ZERO sorry. Offending decls:"
    grep -nE "declaration uses .sorry." "$LOG" | sed 's/^/    /'
    fail=1
fi

if [ "$sorryax_hits" -gt 0 ]; then
    echo
    echo "no-sorry-metatheory.sh: FOUND $sorryax_hits \`sorryAx\` mention(s) in the build output."
    grep -nE "sorryAx" "$LOG" | sed 's/^/    /'
    fail=1
fi

if [ "$fail" -ne 0 ]; then
    echo
    echo "no-sorry-metatheory.sh: GUARD TRIPPED. Do not merge a metatheory with a sorry."
    exit 1
fi

echo "no-sorry-metatheory.sh: ok — metatheory built clean with ZERO sorry / admit / sorryAx."
exit 0
