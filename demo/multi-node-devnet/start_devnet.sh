#!/usr/bin/env bash
# Boot the multi-node, multi-federation devnet:
#
#   F1: 3 nodes (F1-node-1, F1-node-2, F1-node-3)
#   F2: 3 nodes (F2-node-1, F2-node-2, F2-node-3)
#
# Each node:
#   * has its own data-dir (state/F<X>/node-<I>)
#   * has its own HTTP API + gossip ports (see lib/common.sh)
#   * is seeded from a federation-wide genesis.json so the
#     federation_id is committee-derived (H(sorted_pubkeys || epoch=0))
#   * gossip-peers the other two nodes in its own federation
#
# After boot the two federations cross-register: each federation
# ingests the other's federation_descriptor (a copy of genesis.json) via
# `pyana-node register-federation`, populating
# known_federations/<other_fed_id>.json on every node in the local
# federation. This is the SILVER-VISION §0.2 out-of-band trust step.
#
# Exit code 0 on green; non-zero on any boot failure with hints in
# state/logs/*.log.
#
# NO CARGO INVOCATIONS. Build the binary out-of-band.

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/lib/common.sh"

mkdir -p "$STATE_DIR" "$LOG_DIR" "$PID_DIR"

require_node_bin || exit 1

# ── Step 1: generate per-federation genesis ─────────────────────────
devnet_step "step 1 — generate genesis for each federation"

for fed in "${FEDERATIONS[@]}"; do
    gdir=$(fed_genesis_dir "$fed")
    if [ -d "$gdir" ] && [ -f "$gdir/genesis.json" ]; then
        devnet_dim "$fed: reusing existing genesis at $gdir"
        continue
    fi
    mkdir -p "$gdir"
    if "$NODE_BIN" genesis \
            --validators "$NODES_PER_FED" \
            --epoch-length 1000 \
            --checkpoint-interval 100 \
            --output "$gdir" \
            > "$LOG_DIR/$fed-genesis.log" 2>&1; then
        fid=$(fed_id_from_genesis "$gdir/genesis.json")
        devnet_ok "$fed genesis ok (federation_id=${fid:0:16}…)"
    else
        devnet_fail "$fed genesis failed; see $LOG_DIR/$fed-genesis.log"
        exit 1
    fi
done

# ── Step 2: initialize per-node data-dirs ───────────────────────────
devnet_step "step 2 — initialize per-node data directories"

for fed in "${FEDERATIONS[@]}"; do
    gdir=$(fed_genesis_dir "$fed")
    for i in $(seq 1 "$NODES_PER_FED"); do
        ddir=$(fed_data_dir "$fed" "$i")
        mkdir -p "$ddir"

        # genesis.json + .devnet marker shared across the federation
        cp "$gdir/genesis.json" "$ddir/genesis.json"
        cp "$gdir/.devnet" "$ddir/.devnet" 2>/dev/null || true

        # per-node signing key. genesis emits node-{0..N-1}.key —
        # map node-{1..N} (1-based) to node-{0..N-1} (genesis 0-based)
        zero_idx=$((i - 1))
        if [ -f "$gdir/node-$zero_idx.key" ]; then
            cp "$gdir/node-$zero_idx.key" "$ddir/node.key"
            chmod 600 "$ddir/node.key" 2>/dev/null || true
        else
            devnet_warn "$fed node-$i: no key file at $gdir/node-$zero_idx.key"
        fi

        devnet_dim "$fed node-$i  data-dir=$ddir  http=$(fed_http_port $fed $i)  gossip=$(fed_gossip_port $fed $i)"
    done
done

# ── Step 3: cross-register peer federation descriptors ──────────────
# Each node of F1 needs to know F2's committee descriptor (and vice
# versa) so cross-federation handoff certs / federation receipts
# verify. Bilateral by design.
devnet_step "step 3 — cross-register peer federation descriptors (bilateral trust root)"

for fed in "${FEDERATIONS[@]}"; do
    for other in "${FEDERATIONS[@]}"; do
        [ "$fed" = "$other" ] && continue
        other_genesis="$(fed_genesis_dir "$other")/genesis.json"
        if [ ! -f "$other_genesis" ]; then
            devnet_fail "missing $other genesis at $other_genesis"
            exit 1
        fi
        for i in $(seq 1 "$NODES_PER_FED"); do
            ddir=$(fed_data_dir "$fed" "$i")
            log="$LOG_DIR/$fed-node-$i-register-$other.log"
            if "$NODE_BIN" register-federation \
                    --data-dir "$ddir" \
                    --descriptor "$other_genesis" \
                    > "$log" 2>&1; then
                devnet_dim "$fed node-$i ← registered $other"
            else
                devnet_fail "$fed node-$i: register-federation failed; see $log"
                exit 1
            fi
        done
    done
done
devnet_ok "all nodes know both federations"

# ── Step 4: launch the nodes ────────────────────────────────────────
devnet_step "step 4 — launch all $((${#FEDERATIONS[@]} * NODES_PER_FED)) nodes"

# stop_devnet.sh consults PID_DIR; touch a sentinel so callers can tell
# devnet-running from devnet-cleaned.
touch "$STATE_DIR/.devnet-up"

# Default: keep each federation in solo mode so a single-node sub-quorum
# can produce blocks during the demo. Real BFT (`--federation-mode full`)
# requires the threshold-many nodes to be live before anything finalises;
# devnet uses solo for fast iteration but the topology supports the
# full-mode upgrade once gossip stabilises.
FEDERATION_MODE="${FEDERATION_MODE:-solo}"

for fed in "${FEDERATIONS[@]}"; do
    for i in $(seq 1 "$NODES_PER_FED"); do
        port=$(fed_http_port "$fed" "$i")
        gport=$(fed_gossip_port "$fed" "$i")
        ddir=$(fed_data_dir "$fed" "$i")
        peers=$(fed_peers_csv "$fed" "$i")
        log=$(fed_log_file "$fed" "$i")
        pidfile=$(fed_pid_file "$fed" "$i")

        # 1-based external, 0-based for node_index internally
        zero_idx=$((i - 1))

        # Already running? Bail.
        if [ -f "$pidfile" ] && kill -0 "$(cat "$pidfile")" 2>/dev/null; then
            devnet_warn "$fed node-$i already running (pid $(cat "$pidfile")); skip"
            continue
        fi

        "$NODE_BIN" run \
            --port "$port" \
            --bind 127.0.0.1 \
            --gossip-port "$gport" \
            --federation-peers "$peers" \
            --data-dir "$ddir" \
            --key-file node.key \
            --node-index "$zero_idx" \
            --federation-size "$NODES_PER_FED" \
            --federation-mode "$FEDERATION_MODE" \
            --consensus blocklace \
            --enable-faucet \
            > "$log" 2>&1 &
        echo $! > "$pidfile"
        devnet_dim "$fed node-$i pid=$(cat "$pidfile") http=$port gossip=$gport"
    done
done

# ── Step 5: readiness probe ─────────────────────────────────────────
devnet_step "step 5 — wait for HTTP readiness"

ready_all=1
for fed in "${FEDERATIONS[@]}"; do
    for i in $(seq 1 "$NODES_PER_FED"); do
        port=$(fed_http_port "$fed" "$i")
        if wait_for_port "$port" 30; then
            devnet_ok "$fed node-$i listening on :$port"
        else
            devnet_fail "$fed node-$i never came up on :$port; see $(fed_log_file "$fed" "$i")"
            ready_all=0
        fi
    done
done

if [ "$ready_all" -ne 1 ]; then
    devnet_fail "not all nodes came up; run ./stop_devnet.sh to clean up"
    exit 2
fi

# ── Step 6: report the canonical federation IDs ─────────────────────
devnet_step "step 6 — devnet topology summary"
for fed in "${FEDERATIONS[@]}"; do
    fid=$(fed_id_from_genesis "$(fed_genesis_dir $fed)/genesis.json")
    echo "         $fed federation_id = $fid"
    for i in $(seq 1 "$NODES_PER_FED"); do
        port=$(fed_http_port "$fed" "$i")
        echo "           $fed-node-$i  http=http://127.0.0.1:$port  pid=$(cat "$(fed_pid_file $fed $i)" 2>/dev/null || echo ?)"
    done
done

devnet_step "devnet UP — see state/logs/ for per-node tracing"
echo "  scenarios/cross_fed_handoff.sh"
echo "  scenarios/federation_attestation.sh"
echo "  scenarios/bilateral_transfer.sh"
echo "  scenarios/intent_match_cross_fed.sh"
echo "  scenarios/peer_exchange_bypass.sh"
echo
echo "  ./stop_devnet.sh   # graceful shutdown"
echo "  ./reset_devnet.sh  # shutdown + wipe state"
