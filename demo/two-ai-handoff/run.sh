#!/usr/bin/env bash
# Two-AI capability handoff demo. See README.md for the 10-step flow.
#
# Exit codes:
#   0   demo passed (or "scaffolding green" while blockers prevent full PASS)
#   N>0 demo failed at step N (matches the step numbering in README.md)

set -u  # do NOT set -e — we want to capture failures and report PASS/FAIL.
set -o pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
STATE_DIR="$HERE/state"
LOG_DIR="$STATE_DIR/logs"
PY="${PYTHON:-python3}"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

color_red()   { printf '\033[31m%s\033[0m' "$*"; }
color_green() { printf '\033[32m%s\033[0m' "$*"; }
color_dim()   { printf '\033[2m%s\033[0m' "$*"; }

step()  { printf '\n[demo] step %s — %s\n' "$1" "$2"; }
ok()    { printf '       %s %s\n' "$(color_green ok)" "$*"; }
warn()  { printf '       %s %s\n' "$(color_dim '~ ')" "$*"; }
fail()  { printf '       %s %s\n' "$(color_red FAIL)" "$*"; }

reset_state() {
    rm -rf "$STATE_DIR"
    mkdir -p "$LOG_DIR"
    mkdir -p "$STATE_DIR/alice-node-data" \
             "$STATE_DIR/bob-node-data" \
             "$STATE_DIR/charlie-node-data"
}

# Build pyana-node + pyana-verifier, retrying once after 60s on cargo failure
# (matches the no-worktree concurrent-cargo policy).
build_node() {
    local log="$LOG_DIR/cargo-build.log"
    echo "[demo] building pyana-node + pyana-verifier (logs: $log)…"
    if ( cd "$REPO_ROOT" && cargo build -p pyana-node -p pyana-verifier ) > "$log" 2>&1; then
        ok "cargo build ok"
        return 0
    fi
    echo "       cargo build failed; sleeping 60s and retrying once (concurrent-cargo policy)"
    sleep 60
    if ( cd "$REPO_ROOT" && cargo build -p pyana-node -p pyana-verifier ) > "$log" 2>&1; then
        ok "cargo build ok (after retry)"
        return 0
    fi
    fail "cargo build failed twice; see $log"
    return 1
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

cd "$HERE"
reset_state

# ── Step 1: setup ──────────────────────────────────────────────────────────
step 1 "setup (node binary build, scratch dirs)"
if ! build_node; then
    echo
    fail "demo failed at step 1 (build)"
    exit 1
fi
NODE_BIN="$REPO_ROOT/target/debug/pyana-node"
VERIFIER_BIN="$REPO_ROOT/target/debug/pyana-verifier"
if [ ! -x "$NODE_BIN" ]; then
    fail "pyana-node not at $NODE_BIN"
    exit 1
fi
if [ ! -x "$VERIFIER_BIN" ]; then
    fail "pyana-verifier not at $VERIFIER_BIN"
    exit 1
fi
ok "node binary:     $NODE_BIN"
ok "verifier binary: $VERIFIER_BIN"

# ── Pre-step 2: have Bob create his identity so Alice can grant to it ──────
# (Step 2 in the spec is "Alice becomes a cell"; but the grant in step 3
#  targets Bob's pk, so we need Bob's identity first. We perform it as a
#  prelude to step 2.)
step 2 "alice + bob become cells (alice via alice.py, bob via bob.py --identity)"
BOB_ID_JSON=$("$PY" "$HERE/bob.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/bob-node-data" \
    --state-dir "$STATE_DIR" \
    --mode identity 2>"$LOG_DIR/bob.identity.stderr.log")
bob_rc=$?
if [ $bob_rc -ne 0 ]; then
    fail "bob.py --identity exited $bob_rc; see $LOG_DIR/bob.identity.stderr.log"
    exit 2
fi
BOB_PK=$(echo "$BOB_ID_JSON" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["bob_pk"])')
BOB_CELL=$(echo "$BOB_ID_JSON" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["bob_cell"])')
ok "bob pk = ${BOB_PK:0:16}…"

# ── Step 3 + 5 + 10: alice (cell, grant, bearer cap, compress) ─────────────
step 3 "alice creates cell, grants TRANSFER_ONLY to bob, exports bearer cap"
ALICE_OUT=$("$PY" "$HERE/alice.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/alice-node-data" \
    --state-dir "$STATE_DIR" \
    --bob-pk "$BOB_PK" \
    --bob-cell "$BOB_CELL" 2>"$LOG_DIR/alice.stderr.log")
alice_rc=$?
if [ $alice_rc -ne 0 ]; then
    fail "alice.py exited $alice_rc; see $LOG_DIR/alice.stderr.log"
    exit $alice_rc
fi
ALICE_PK=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["alice_pk"])')
GRANT_TURN=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["grant_turn_hash"])')
ok "grant turn = ${GRANT_TURN:0:16}…"
ok "handoff URI written to $STATE_DIR/handoff.uri"

# ── Step 4: charlie verifies the grant proof ───────────────────────────────
step 4 "charlie verifies grant turn proof (independent process)"
# Charlie runs after step 7 (so he can verify both proofs in one pass).
# Keep this as a logical marker; the real verify happens at step 8 below.
warn "deferred until step 8 (single charlie invocation verifies both proofs)"

# ── Step 6 + 7: bob enlivens and exercises ─────────────────────────────────
step 6 "bob receives URI out-of-band, enlivens"
step 7 "bob exercises the cap (Transfer)"
BOB_OUT=$("$PY" "$HERE/bob.py" \
    --node-bin "$NODE_BIN" \
    --data-dir "$STATE_DIR/bob-node-data" \
    --state-dir "$STATE_DIR" \
    --mode exercise \
    --amount 100 2>"$LOG_DIR/bob.exercise.stderr.log")
bob_rc=$?
if [ $bob_rc -ne 0 ]; then
    fail "bob.py exercise exited $bob_rc; see $LOG_DIR/bob.exercise.stderr.log"
    # don't exit — we still want to run charlie + summary
    EXERCISE_OK=0
else
    EXERCISE_OK=1
    EXERCISE_TURN=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["exercise_turn_hash"])')
    ok "exercise turn = ${EXERCISE_TURN:0:16}…"
fi

# ── Step 8: charlie verifies both proofs ───────────────────────────────────
step 8 "charlie verifies both proofs (independent binary: pyana-verifier)"
# Alice's grant tool and Bob's exercise tool now emit effect_vm_proof_hex +
# effect_vm_public_inputs, and the python scripts write them to disk as
# state/{grant,exercise}.proof.json. Charlie shells out to the pyana-verifier
# binary (NOT pyana-node) — different binary, different crate dependencies,
# zero shared prover state.
CHARLIE_OUT=$("$PY" "$HERE/charlie.py" \
    --verifier-bin "$VERIFIER_BIN" \
    --state-dir "$STATE_DIR" 2>"$LOG_DIR/charlie.stderr.log")
charlie_rc=$?
if [ $charlie_rc -ne 0 ]; then
    fail "charlie.py exited $charlie_rc; see $LOG_DIR/charlie.stderr.log"
fi
GRANT_VERIFIED=$(echo "$CHARLIE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("grant_verified", False))' 2>/dev/null || echo False)
EXERCISE_VERIFIED=$(echo "$CHARLIE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("exercise_verified", False))' 2>/dev/null || echo False)
REPLAY_CHAIN_VERIFIED=$(echo "$CHARLIE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("replay_chain_verified", False))' 2>/dev/null || echo False)
REPLAY_CHAIN_SUMMARY=$(echo "$CHARLIE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("replay_chain_summary", ""))' 2>/dev/null || echo "")
[ "$GRANT_VERIFIED" = "True" ]    && ok "grant proof verified by charlie"    || warn "grant proof NOT verified (see blockers)"
[ "$EXERCISE_VERIFIED" = "True" ] && ok "exercise proof verified by charlie" || warn "exercise proof NOT verified (see blockers)"
[ "$REPLAY_CHAIN_VERIFIED" = "True" ] && ok "replay-chain (WitnessedReceipt v1) verified: $REPLAY_CHAIN_SUMMARY" \
                                     || warn "replay-chain NOT verified: $REPLAY_CHAIN_SUMMARY"

# ── Step 9: receipt chain links grant -> exercise ──────────────────────────
step 9 "receipt chain links grant -> exercise"
# BLOCKER-7: alice's chain and bob's chain are separate today. Once
# previous_receipt_hash is threaded, this step should walk one chain.
# For scaffolding purposes, we just record both chains.
warn "skipped (blocker 7: receipt chain linkage not threaded across agents)"

# ── Step 10: alice exports IVC-compressed state ────────────────────────────
step 10 "alice exports IVC-compressed history"
COMPRESS_OK=$(echo "$ALICE_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin)["compress_history"]["ok"])' 2>/dev/null || echo False)
if [ "$COMPRESS_OK" = "True" ]; then
    ok "history compressed and self-verifies"
else
    warn "compress_history not green (blocker 8)"
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

echo
echo "[demo] ─── summary ─────────────────────────────────────────────────"

# Post-condition checks against expected.json. Each is a (label, ok) tuple.
declare -a CHECKS_LABEL
declare -a CHECKS_OK
add_check() { CHECKS_LABEL+=("$1"); CHECKS_OK+=("$2"); }

# Required to consider the scaffolding "wired".
add_check "step 2 (alice + bob created)"                     1
add_check "step 3 (grant turn committed)"                    1
add_check "step 5 (bearer cap created, URI dropped to disk)" 1
add_check "step 7 (bob exercised the cap)"                   "$EXERCISE_OK"

# Currently-blocked checks (will flip to 1 when blockers are addressed).
GRANT_VER_OK=0;    [ "$GRANT_VERIFIED" = "True" ]    && GRANT_VER_OK=1
EXERCISE_VER_OK=0; [ "$EXERCISE_VERIFIED" = "True" ] && EXERCISE_VER_OK=1
add_check "step 4/8 (charlie verifies grant proof)"          "$GRANT_VER_OK"
add_check "step 4/8 (charlie verifies exercise proof)"       "$EXERCISE_VER_OK"

# WitnessedReceipt v1.D — replay-chain end-to-end (see WITNESSED-RECEIPT-CHAIN-DESIGN.md §8).
REPLAY_OK=0; [ "$REPLAY_CHAIN_VERIFIED" = "True" ] && REPLAY_OK=1
add_check "WitnessedReceipt v1 replay-chain verdict (pyana-verifier replay-chain)" "$REPLAY_OK"

# Observable balance deltas on Bob's ledger (expected.json transfer_amount=100).
#
# Net bob delta = +100 (Transfer credit) - 10_000 (turn fee paid by bob's
# cell as the agent of the turn). Net = -9900. The Transfer effect actually
# moved 100 from alice to bob; the fee is a separate executor charge.
BOB_DELTA=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("bob_balance_delta", 0))' 2>/dev/null || echo 0)
ALICE_STUB_BAL=$(echo "$BOB_OUT" | "$PY" -c 'import json,sys;print(json.load(sys.stdin).get("alice_stub_balance", 0))' 2>/dev/null || echo 0)
BOB_DELTA_OK=0; [ "$BOB_DELTA" = "-9900" ] && BOB_DELTA_OK=1
# The remote-stub for alice is pre-funded to 1_000_000 in the exercise tool;
# after the Transfer 100 we expect 999_900.
ALICE_STUB_OK=0; [ "$ALICE_STUB_BAL" = "999900" ] && ALICE_STUB_OK=1
add_check "Transfer effect credited bob (net delta -9900 = +100 - 10000 fee)"  "$BOB_DELTA_OK"
add_check "Transfer effect debited alice stub (1_000_000 -> 999_900)"           "$ALICE_STUB_OK"

# Per-agent receipt chain export: expected.json receipt_chain.exportable
# requires each agent's chain to include the turn they just committed.
ALICE_CHAIN_HAS_GRANT=$(echo "$ALICE_OUT" | "$PY" -c '
import json, sys
d = json.load(sys.stdin)
grant = d.get("grant_turn_hash", "")
chain = d.get("receipt_chain", {}).get("receipts", [])
print("1" if any(r.get("turn_hash") == grant for r in chain) else "0")
' 2>/dev/null || echo 0)
BOB_CHAIN_HAS_EXERCISE=$(echo "$BOB_OUT" | "$PY" -c '
import json, sys
d = json.load(sys.stdin)
ex = d.get("exercise_turn_hash", "")
chain = d.get("receipt_chain", {}).get("receipts", [])
print("1" if any(r.get("turn_hash") == ex for r in chain) else "0")
' 2>/dev/null || echo 0)
add_check "alice's receipt chain contains the grant turn"     "$ALICE_CHAIN_HAS_GRANT"
add_check "bob's receipt chain contains the exercise turn"    "$BOB_CHAIN_HAS_EXERCISE"

PASS=1
for i in "${!CHECKS_LABEL[@]}"; do
    if [ "${CHECKS_OK[$i]}" = "1" ]; then
        printf '       %s %s\n' "$(color_green PASS)" "${CHECKS_LABEL[$i]}"
    else
        printf '       %s %s\n' "$(color_red FAIL)" "${CHECKS_LABEL[$i]}"
        PASS=0
    fi
done

echo
if [ $PASS -eq 1 ]; then
    printf '%s — two-AI handoff complete\n' "$(color_green '[demo] PASS')"
    exit 0
else
    printf '%s — see Blockers section in README.md\n' "$(color_red '[demo] FAIL')"
    echo "       artifacts: $STATE_DIR/"
    echo "       node logs: $LOG_DIR/"
    exit 1
fi
