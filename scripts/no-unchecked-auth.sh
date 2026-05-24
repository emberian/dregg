#!/usr/bin/env bash
# P2.F — CI grep guard: forbid `Authorization::Unchecked` outside of
# test code and a small, explicitly-listed escape-hatch surface.
#
# Background: the DSL audit (P0 #1) found that production framework code
# was constructing actions with `Authorization::Unchecked`, effectively
# making them unauthenticated. P2.A introduced a typestate ActionBuilder
# whose only path to that variant is the loudly-named
# `new_unchecked_for_tests` constructor. This script keeps the audit
# honest by tripwiring any new production-code reintroduction of the
# literal.
#
# Pass/fail policy:
#   - Lines in `.rs` files anywhere under a `tests/` directory: ALLOWED
#   - Lines in `*tests*.rs` files (e.g. `tests.rs`, `proptest_*.rs`,
#     `*_test.rs`): ALLOWED
#   - Comment lines (`//`, `///`, `//!`): ALLOWED (talking about it is fine)
#   - Match arms (`Authorization::Unchecked =>`): ALLOWED (handler code
#     must dispatch on the variant somewhere)
#   - The enum variant definition itself: ALLOWED
#   - Lines guarded by `!matches!` / `debug_assert!` / `assert!` /
#     `refusing` / `Refusing` (defensive checks): ALLOWED
#   - Files on the ALLOWLIST below: ALLOWED with reason
#   - Everything else: FAIL.
#
# Run from the repo root: `scripts/no-unchecked-auth.sh`

set -euo pipefail
shopt -s extglob

# Files that legitimately reference the literal in production code.
# Each entry needs a one-line reason. Touching this list should require
# a code review.
ALLOWLIST_FILE_PATTERNS=(
    # The typestate's escape hatch -- the *only* documented path to
    # Unchecked authorization, named loudly enough that nobody can
    # accidentally invoke it in production.
    "turn/src/builder.rs"
    # The Effect-VM / executor path that *consumes* the variant when
    # routing CapTP wire messages. The cryptographic legitimacy is
    # established off-band (swiss-number / handoff). Tracked as a P3
    # follow-up: replace with a typed `BridgedFromWire` authorization.
    "wire/src/captp_routing.rs"
    # The action.rs enum definition itself plus its match-arm handlers
    # in the executor / forest -- variant must be referenced somewhere.
    "turn/src/action.rs"
    "turn/src/executor.rs"
    "turn/src/eventual.rs"
    "turn/src/pending.rs"
    # The four-layer lowering uses `!matches!` defensive guards against
    # the variant slipping through SealedTurn.
    "intent/src/lowering.rs"
    # `coord/src/tests.rs` is a test fixture file living in src/.
    "coord/src/tests.rs"
    # protocol-tests is an entire crate of test scaffolding.
    "protocol-tests/src"
    # cross-federation test scaffolding in teasting/.
    "teasting/tests"
    # The legacy LegacyActionBuilder still emits Unchecked; the
    # migration off it is tracked separately. Lives in builder.rs which
    # is already allowlisted above.

    # ─── Migration baseline (P2.F) ────────────────────────────────────
    # The following files contain pre-existing `Authorization::Unchecked`
    # usages from before the DSL hardening landed. The full migration
    # off the legacy `&mut`-chain builder is a deliberate follow-up
    # commit AFTER the P2 / P3 / P4 parallel slate lands. These files
    # are grandfathered for now; the guard's job today is to prevent
    # *net-new* production sites, not to ratchet existing ones in a
    # single commit.
    "apps/gallery/src/artwork.rs"
    "apps/gallery/src/settlement.rs"
    "apps/bounty-board/src/payment.rs"
    "demo-agent/examples"
    "intent/src/fulfillment.rs"
    "node/src/api.rs"
    "node/src/mcp.rs"
    "sdk/src/committed_turn.rs"
    "sdk/src/runtime.rs"
    "sdk/src/wallet.rs"
    "tests/src/every_variant_roundtrip.rs"
    "app-framework/src/authorizer.rs"
    # `app-framework/src/escrow.rs` is NOT allowlisted: P0f migrated it to
    # the Authorizer-injected constructor, leaving only comments that
    # reference the literal (which the comment skip handles).
    # SDK-consensus demo: a CLI scaffold whose entire purpose is end-to-end
    # plumbing demos against the in-memory engine. Tracked as a follow-up
    # migration alongside the other demo-agent examples.
    "demo/sdk-consensus/src/main.rs"
)

ROOT="${1:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"

cd "$ROOT"

# Substring we are scanning for, assembled at runtime so this script
# itself does not contain the literal token.
NEEDLE=$(printf 'Authorization%s%s' '::' 'Unchecked')

offenders=()

# shellcheck disable=SC2207
files=($(git ls-files '*.rs' 2>/dev/null || find . -name '*.rs' -type f))

for file in "${files[@]}"; do
    # Skip test-shaped paths.
    case "$file" in
        */tests/*) continue ;;
        */test/*) continue ;;
    esac
    base=$(basename "$file")
    case "$base" in
        tests.rs|test.rs|*_test.rs|*_tests.rs|proptest_*.rs|*_proptest.rs) continue ;;
    esac

    # Skip allowlisted files / directories.
    skip=false
    for allowed in "${ALLOWLIST_FILE_PATTERNS[@]}"; do
        case "$file" in
            "$allowed"|"$allowed"/*|*/"$allowed"|*/"$allowed"/*)
                skip=true; break ;;
        esac
    done
    $skip && continue

    # Walk the file line by line.
    lineno=0
    while IFS= read -r line; do
        lineno=$((lineno + 1))
        case "$line" in
            *"$NEEDLE"*) ;;
            *) continue ;;
        esac

        trimmed=${line##+([[:space:]])}
        # Skip comment lines.
        case "$trimmed" in
            //*|/\**) continue ;;
        esac
        # Skip match arms.
        case "$trimmed" in
            *"$NEEDLE"*"=>"*) continue ;;
        esac
        # Skip the enum variant definition (just the identifier with
        # nothing on either side beyond punctuation).
        case "$trimmed" in
            "$NEEDLE,") continue ;;
            "$NEEDLE") continue ;;
        esac
        # Skip defensive guards.
        case "$line" in
            *"!matches!"*|*"debug_assert"*|*"refusing"*|*"Refusing"*) continue ;;
        esac

        offenders+=("$file:$lineno: $line")
    done < "$file"
done

if [ ${#offenders[@]} -gt 0 ]; then
    echo "no-unchecked-auth.sh: production code references the forbidden literal."
    echo
    printf '  %s\n' "${offenders[@]}"
    echo
    echo "If the use is legitimate production scaffolding (e.g. a deliberate"
    echo "wire-layer bridging surface), add the file to ALLOWLIST_FILE_PATTERNS"
    echo "with a reason. Otherwise use a real Authorization variant."
    exit 1
fi

echo "no-unchecked-auth.sh: ok"
exit 0
