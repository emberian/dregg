#!/usr/bin/env bash
# Run every scenario script in scenarios/ in order. Aggregates pass/fail
# into a single exit code. Does NOT start or stop the devnet — assumes
# `./start_devnet.sh` was already invoked.

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/lib/common.sh"

if [ ! -f "$STATE_DIR/.devnet-up" ]; then
    devnet_warn "no devnet sentinel at $STATE_DIR/.devnet-up — did you run ./start_devnet.sh?"
fi

SCENARIOS=(
    cross_fed_handoff
    federation_attestation
    bilateral_transfer
    intent_match_cross_fed
    peer_exchange_bypass
)

total=${#SCENARIOS[@]}
passed=0
failed_names=()

for s in "${SCENARIOS[@]}"; do
    devnet_step "=== running scenarios/$s.sh ==="
    if "$HERE/scenarios/$s.sh"; then
        passed=$((passed + 1))
    else
        failed_names+=("$s")
    fi
done

devnet_step "summary: $passed/$total scenarios passed"
if [ "$passed" -eq "$total" ]; then
    devnet_ok "ALL SCENARIOS PASS"
    exit 0
else
    for f in "${failed_names[@]}"; do
        devnet_fail "FAILED: $f"
    done
    exit 1
fi
