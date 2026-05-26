#!/usr/bin/env bash
# Common shell library for the multi-node devnet.
#
# Sourced by start_devnet.sh, stop_devnet.sh, reset_devnet.sh, and the
# scenarios/*.sh scripts. Holds the topology constants and helper
# functions. Greenfield — improve don't degrade: this is the single
# source of truth for ports, data-dirs, and per-federation layout.

# Resolve repo + devnet root regardless of caller.
if [ -z "${DEVNET_ROOT:-}" ]; then
    DEVNET_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fi
if [ -z "${REPO_ROOT:-}" ]; then
    REPO_ROOT="$(cd "$DEVNET_ROOT/../.." && pwd)"
fi

STATE_DIR="${STATE_DIR:-$DEVNET_ROOT/state}"
LOG_DIR="${LOG_DIR:-$STATE_DIR/logs}"
PID_DIR="${PID_DIR:-$STATE_DIR/pids}"

# Pre-built node binary location. NO CARGO INVOCATIONS in this lane —
# the operator builds pyana-node out-of-band (e.g. via the existing
# demo/two-ai-handoff/run.sh build step, or a separate "make build"
# loop). start_devnet.sh checks that the binary exists and bails with
# a helpful message if not.
#
# Ease-by-default: prefer debug (for active dev), fall back to release
# (common after `cargo build --release`). Operator can still override
# NODE_BIN/VERIFIER_BIN.
if [ -z "${NODE_BIN:-}" ]; then
    if [ -x "$REPO_ROOT/target/debug/pyana-node" ]; then
        NODE_BIN="$REPO_ROOT/target/debug/pyana-node"
    elif [ -x "$REPO_ROOT/target/release/pyana-node" ]; then
        NODE_BIN="$REPO_ROOT/target/release/pyana-node"
    fi
fi
if [ -z "${VERIFIER_BIN:-}" ]; then
    if [ -x "$REPO_ROOT/target/debug/pyana-verifier" ]; then
        VERIFIER_BIN="$REPO_ROOT/target/debug/pyana-verifier"
    elif [ -x "$REPO_ROOT/target/release/pyana-verifier" ]; then
        VERIFIER_BIN="$REPO_ROOT/target/release/pyana-verifier"
    fi
fi

# ── Topology ────────────────────────────────────────────────────────
#
# Two federations, three nodes each. The "F<X>_N<I>" naming is the
# canonical short-form used in scenario scripts and expected/*.json.
#
# Port layout (devnet, all loopback). Range conventions:
#   F1 HTTP API:   78{11,12,13}      gossip: 79{11,12,13}
#   F2 HTTP API:   78{21,22,23}      gossip: 79{21,22,23}
#
# These are chosen so a single grep of `78[12][123]` reveals every
# federation port without aliasing the docker/relay/MCP ranges in use
# elsewhere in the tree.
FEDERATIONS=(F1 F2)
NODES_PER_FED=3

# HTTP API port for federation $1 node-index $2 (1-based).
fed_http_port() {
    local fed="$1" idx="$2"
    case "$fed" in
        F1) echo $((7810 + idx)) ;;
        F2) echo $((7820 + idx)) ;;
        *)  echo "" ; return 1 ;;
    esac
}

# Gossip port for federation $1 node-index $2 (1-based).
fed_gossip_port() {
    local fed="$1" idx="$2"
    case "$fed" in
        F1) echo $((7910 + idx)) ;;
        F2) echo $((7920 + idx)) ;;
        *)  echo "" ; return 1 ;;
    esac
}

# Per-node data directory.
fed_data_dir() {
    local fed="$1" idx="$2"
    echo "$STATE_DIR/$fed/node-$idx"
}

# Federation-wide genesis output directory (created by genesis subcommand
# before the per-node data-dirs are populated from it).
fed_genesis_dir() {
    local fed="$1"
    echo "$STATE_DIR/$fed/genesis"
}

# PID file for federation $1 node-index $2.
fed_pid_file() {
    local fed="$1" idx="$2"
    echo "$PID_DIR/$fed-node-$idx.pid"
}

# Log files.
fed_log_file() {
    local fed="$1" idx="$2"
    echo "$LOG_DIR/$fed-node-$idx.log"
}

# Comma-separated gossip peer string for federation $fed excluding node $self_idx.
fed_peers_csv() {
    local fed="$1" self_idx="$2"
    local out=""
    for j in $(seq 1 "$NODES_PER_FED"); do
        if [ "$j" != "$self_idx" ]; then
            local p
            p=$(fed_gossip_port "$fed" "$j")
            if [ -n "$out" ]; then out="$out,"; fi
            out="${out}127.0.0.1:$p"
        fi
    done
    echo "$out"
}

# ── Logging helpers ──────────────────────────────────────────────────

color_red()   { printf '\033[31m%s\033[0m' "$*"; }
color_green() { printf '\033[32m%s\033[0m' "$*"; }
color_yel()   { printf '\033[33m%s\033[0m' "$*"; }
color_dim()   { printf '\033[2m%s\033[0m' "$*"; }

devnet_step()  { printf '\n[devnet] %s\n' "$*"; }
devnet_ok()    { printf '         %s %s\n' "$(color_green ok)" "$*"; }
devnet_warn()  { printf '         %s %s\n' "$(color_yel '~~')" "$*"; }
devnet_fail()  { printf '         %s %s\n' "$(color_red FAIL)" "$*"; }
devnet_dim()   { printf '         %s\n' "$(color_dim "$*")"; }

# Synthetic-warning accumulator. Scenarios source this file, so
# SYNTHETIC_WARNINGS is a single global array visible to every
# sourcing script. Use synthetic_warn() instead of a bare devnet_warn()
# whenever an assertion passes on synthetic constants rather than live
# devnet data — the array is flushed into result.json as
# "synthetic_warnings": [...] so CI can distinguish synthetic-true from
# live-true via `jq '.synthetic_warnings | length'`.
SYNTHETIC_WARNINGS=()
synthetic_warn() {
    local msg="$*"
    devnet_warn "$msg"
    SYNTHETIC_WARNINGS+=("$msg")
}

# Emit the synthetic_warnings JSON array fragment (no trailing comma).
# Caller is responsible for surrounding context in the result.json block.
emit_synthetic_warnings_json() {
    local i n
    n=${#SYNTHETIC_WARNINGS[@]}
    printf '  "synthetic_warnings": ['
    if [ "$n" -eq 0 ]; then
        printf ']'
        return
    fi
    printf '\n'
    for (( i=0; i<n; i++ )); do
        # Escape backslashes and double-quotes for JSON string safety.
        local escaped
        escaped="${SYNTHETIC_WARNINGS[$i]//\\/\\\\}"
        escaped="${escaped//\"/\\\"}"
        if [ $((i + 1)) -lt "$n" ]; then
            printf '    "%s",\n' "$escaped"
        else
            printf '    "%s"\n' "$escaped"
        fi
    done
    printf '  ]'
}

# Wait for a TCP port to accept connections. $1 = port, $2 = max-secs.
wait_for_port() {
    local port="$1" max_secs="${2:-20}"
    local i=0
    while [ $i -lt "$max_secs" ]; do
        if (echo > /dev/tcp/127.0.0.1/"$port") 2>/dev/null; then
            return 0
        fi
        sleep 1
        i=$((i + 1))
    done
    return 1
}

# Curl helper with timeout; prints body or empty on failure.
http_get() {
    local url="$1"
    curl -sS --max-time 5 "$url" 2>/dev/null || echo ""
}

# Check that the node binary exists, fail with guidance if not.
require_node_bin() {
    if [ ! -x "$NODE_BIN" ]; then
        devnet_fail "node binary not found at $NODE_BIN"
        devnet_dim "build it out-of-band (NO cargo in this lane). For instance:"
        devnet_dim "  cd $REPO_ROOT && cargo build -p pyana-node"
        devnet_dim "or rely on demo/two-ai-handoff/run.sh's build step."
        return 1
    fi
    return 0
}

# Check that the verifier binary exists (optional, only for some scenarios).
have_verifier_bin() {
    [ -x "$VERIFIER_BIN" ]
}

# Read the federation_id from a genesis.json. Requires `jq`. If `jq`
# isn't present the caller can fall back to grep, but every scenario
# uses jq for receipt walking anyway.
fed_id_from_genesis() {
    local genesis_json="$1"
    if command -v jq >/dev/null 2>&1; then
        jq -r .federation_id < "$genesis_json"
    else
        # crude fallback
        grep -o '"federation_id"\s*:\s*"[^"]*"' "$genesis_json" \
            | head -n1 \
            | sed 's/.*"\([^"]*\)"$/\1/'
    fi
}
