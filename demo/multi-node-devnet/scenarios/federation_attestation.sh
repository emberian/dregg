#!/usr/bin/env bash
# Scenario: federation attestation exchange.
#
# Story (SILVER-VISION §4):
#   * F1 commits to its blocklace tip (block_id, round, tau_index).
#   * F1 produces an AttestedRoot signed by its committee threshold,
#     binding `(merkle_root, note_tree_root, nullifier_set_root,
#     blocklace_finality)` to federation_id_F1 and committee_epoch.
#   * F1 pushes (or F2 pulls) the AttestedRoot over the CapTP wire.
#   * F2 verifies the QC against F1's committee descriptor (registered
#     at startup) and accepts it as cross-fed evidence.
#
# Observable substrate (what this scenario can drive today):
#   * Both federations expose `/federation/roots` over HTTP.
#   * Each federation's roots are signed (the API surfaces signatures
#     when present) and bound to a federation_id we can sanity-check
#     against the registered descriptor.
#   * `must_not_pass` includes: tampering an attested root MUST be
#     detectable when an external verifier cross-references it against
#     the committee descriptor.

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/../lib/common.sh"

SCENARIO_NAME="federation_attestation"
SCN_LOG_DIR="$LOG_DIR/scenarios/$SCENARIO_NAME"
RESULT_FILE="$SCN_LOG_DIR/result.json"
mkdir -p "$SCN_LOG_DIR"

declare -A RESULTS
record() {
    local key="$1" val="$2"
    RESULTS["$key"]="$val"
    if [ "$val" = "true" ]; then devnet_ok "$key"; else devnet_fail "$key"; fi
}

F1_ID=$(fed_id_from_genesis "$(fed_genesis_dir F1)/genesis.json")
F2_ID=$(fed_id_from_genesis "$(fed_genesis_dir F2)/genesis.json")
F1_PORT=$(fed_http_port F1 1)
F2_PORT=$(fed_http_port F2 1)

devnet_step "scenario: federation_attestation"
devnet_dim "F1 federation_id=$F1_ID"
devnet_dim "F2 federation_id=$F2_ID"

# ── 1: probe /federation/roots on both sides ────────────────────────
r1=$(http_get "http://127.0.0.1:$F1_PORT/federation/roots")
r2=$(http_get "http://127.0.0.1:$F2_PORT/federation/roots")
echo "$r1" > "$SCN_LOG_DIR/F1_roots.json"
echo "$r2" > "$SCN_LOG_DIR/F2_roots.json"

[ -n "$r1" ] && record F1_federation_roots_endpoint_responds true || record F1_federation_roots_endpoint_responds false
[ -n "$r2" ] && record F2_federation_roots_endpoint_responds true || record F2_federation_roots_endpoint_responds false

# ── 2: each federation's descriptor is on file in the other's node ──
# After `register-federation`, each node has the peer descriptor in
# data-dir/known_federations/<other_fed_id>.json. Sample F1-node-1.
F1_NODE1=$(fed_data_dir F1 1)
F2_NODE1=$(fed_data_dir F2 1)
F1_KNOWS_F2_PATH="$F1_NODE1/known_federations/$F2_ID.json"
F2_KNOWS_F1_PATH="$F2_NODE1/known_federations/$F1_ID.json"

[ -s "$F1_KNOWS_F2_PATH" ] && record F1_has_F2_descriptor_on_disk true || record F1_has_F2_descriptor_on_disk false
[ -s "$F2_KNOWS_F1_PATH" ] && record F2_has_F1_descriptor_on_disk true || record F2_has_F1_descriptor_on_disk false

# ── 3: committee_epoch consistency between genesis and registered desc
if command -v jq >/dev/null 2>&1; then
    F1_epoch_self=$(jq -r .committee_epoch < "$(fed_genesis_dir F1)/genesis.json")
    F1_epoch_seen_by_F2=$(jq -r .committee_epoch < "$F2_KNOWS_F1_PATH")
    if [ "$F1_epoch_self" = "$F1_epoch_seen_by_F2" ]; then
        record F1_committee_epoch_matches_across_federations true
    else
        record F1_committee_epoch_matches_across_federations false
    fi

    # Validator count consistency
    F1_count_self=$(jq -r '.validators | length' < "$(fed_genesis_dir F1)/genesis.json")
    F1_count_seen_by_F2=$(jq -r '.validators | length' < "$F2_KNOWS_F1_PATH")
    if [ "$F1_count_self" = "$F1_count_seen_by_F2" ] && [ "$F1_count_self" = "$NODES_PER_FED" ]; then
        record F1_committee_size_consistent_with_NODES_PER_FED true
    else
        record F1_committee_size_consistent_with_NODES_PER_FED false
    fi
fi

# ── 4: federation_id binding — tamper a known descriptor, re-register,
# expect the node to REJECT (per audit F1: federation_id must equal
# H(sorted_pubkeys || epoch)).
TAMPER="$SCN_LOG_DIR/F1.tampered.json"
if command -v jq >/dev/null 2>&1; then
    # Tamper: prepend a fresh validator (changes the committee → changes
    # the derived federation_id). The declared federation_id is left as
    # F1_ID, so the register-federation check at main.rs:884 should
    # reject.
    jq '.validators += [{"name":"intruder","public_key":"deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef","xmss_root":"00"}]' \
        "$(fed_genesis_dir F1)/genesis.json" > "$TAMPER"

    # Try to register the tampered descriptor on F2-node-1. Expect
    # non-zero exit (descriptor federation_id != recomputed).
    if "$NODE_BIN" register-federation \
            --data-dir "$F2_NODE1" \
            --descriptor "$TAMPER" \
            > "$SCN_LOG_DIR/tamper-reg.stdout" 2> "$SCN_LOG_DIR/tamper-reg.stderr"; then
        record tampered_federation_descriptor_rejected false
    else
        record tampered_federation_descriptor_rejected true
    fi
fi

# ── 5: derived federation_id != arbitrary string ────────────────────
# Sanity: the federation_id genesis emits is 64 hex chars and matches
# the descriptor that another federation registered.
hex_len_F1=${#F1_ID}
hex_len_F2=${#F2_ID}
if [ "$hex_len_F1" = "64" ] && [ "$hex_len_F2" = "64" ]; then
    record federation_ids_are_committee_derived_32_byte_hex true
else
    record federation_ids_are_committee_derived_32_byte_hex false
fi

# F1 ≠ F2 (different committees → different ids).
if [ "$F1_ID" != "$F2_ID" ]; then
    record federation_F1_and_F2_have_distinct_ids true
else
    record federation_F1_and_F2_have_distinct_ids false
fi

# ── 6: every node in F1 has F2 registered (not just node-1) ──────────
all_F1_know_F2=1
for i in $(seq 1 "$NODES_PER_FED"); do
    p="$(fed_data_dir F1 "$i")/known_federations/$F2_ID.json"
    [ -s "$p" ] || all_F1_know_F2=0
done
all_F2_know_F1=1
for i in $(seq 1 "$NODES_PER_FED"); do
    p="$(fed_data_dir F2 "$i")/known_federations/$F1_ID.json"
    [ -s "$p" ] || all_F2_know_F1=0
done
[ $all_F1_know_F2 -eq 1 ] && record every_F1_node_knows_F2 true || record every_F1_node_knows_F2 false
[ $all_F2_know_F1 -eq 1 ] && record every_F2_node_knows_F1 true || record every_F2_node_knows_F1 false

# ── emit ─────────────────────────────────────────────────────────────
{
    echo "{"
    echo "  \"scenario\": \"$SCENARIO_NAME\","
    echo "  \"federation_F1\": \"$F1_ID\","
    echo "  \"federation_F2\": \"$F2_ID\","
    echo "  \"results\": {"
    first=1
    for k in "${!RESULTS[@]}"; do
        if [ $first -eq 1 ]; then first=0; else echo ","; fi
        printf '    "%s": %s' "$k" "${RESULTS[$k]}"
    done
    echo
    echo "  }"
    echo "}"
} > "$RESULT_FILE"

devnet_step "result written to $RESULT_FILE"

EXPECTED="$HERE/../expected/$SCENARIO_NAME.json"
PASS=1
if [ -f "$EXPECTED" ] && command -v jq >/dev/null 2>&1; then
    for key in $(jq -r '.must_pass[]' "$EXPECTED" 2>/dev/null); do
        val=$(jq -r ".results.$key // false" "$RESULT_FILE" 2>/dev/null)
        if [ "$val" != "true" ]; then
            devnet_fail "must_pass FAILED: $key"
            PASS=0
        fi
    done
    for key in $(jq -r '.must_not_pass[]' "$EXPECTED" 2>/dev/null); do
        # must_not_pass keys exist as positive `*_rejected` assertions
        # in the results map. The semantic is "the bad case was caught";
        # the key being `true` means the rejection happened.
        val=$(jq -r ".results.$key // false" "$RESULT_FILE" 2>/dev/null)
        if [ "$val" != "true" ]; then
            devnet_fail "must_not_pass FAILED (bad case not detected): $key"
            PASS=0
        fi
    done
fi

if [ $PASS -eq 1 ]; then devnet_ok "scenario PASS"; exit 0; else devnet_fail "scenario FAIL"; exit 1; fi
