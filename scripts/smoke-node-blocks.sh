#!/usr/bin/env bash
#
# smoke-node-blocks.sh — prove a solo dregg-node produces REAL blocks.
#
# Starts a single-node (committee-of-one) dregg-node with the blocklace
# consensus engine, lets it run long enough to produce several heartbeat
# blocks on its production cadence, then queries the read API and asserts:
#
#   1. /api/blocklace/blocks returns a height-ordered list of blocks.
#   2. The max height advances past 1 (the chain made real progress over time).
#   3. Blocks above genesis carry NON-ZERO parent hashes (prev_hash), i.e. the
#      blocklace DAG has real predecessor links — not the hardcoded zero the
#      wasm get_federation_block binding falls back to.
#   4. /api/block/<height> serves an individual block whose prev_hash matches
#      the predecessor recorded in the list (real, consistent parent linkage).
#
# Exit non-zero on any failed assertion. Designed to run in CI.
#
# Usage: scripts/smoke-node-blocks.sh [PORT]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PORT="${1:-8420}"
GOSSIP_PORT=$((PORT + 1000))
CADENCE_MS=500          # fast cadence so the test is quick
RUN_SECONDS=6           # long enough for ~10 heartbeat blocks
DATA_DIR="$(mktemp -d)"

# Prefer a release binary if present (faster startup); fall back to debug.
DREGG="$PROJECT_ROOT/target/release/dregg-node"
if [ ! -x "$DREGG" ]; then
  DREGG="$PROJECT_ROOT/target/debug/dregg-node"
fi
if [ ! -x "$DREGG" ]; then
  echo "Building dregg-node (debug) ..."
  (cd "$PROJECT_ROOT" && cargo build -p dregg-node)
  DREGG="$PROJECT_ROOT/target/debug/dregg-node"
fi

NODE_PID=""
cleanup() {
  if [ -n "$NODE_PID" ] && kill -0 "$NODE_PID" 2>/dev/null; then
    kill "$NODE_PID" 2>/dev/null || true
    wait "$NODE_PID" 2>/dev/null || true
  fi
  rm -rf "$DATA_DIR"
}
trap cleanup EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }

echo "=== dregg-node solo block-production smoke test ==="
echo "binary:    $DREGG"
echo "data dir:  $DATA_DIR"
echo "api port:  $PORT  gossip port: $GOSSIP_PORT"
echo "cadence:   ${CADENCE_MS}ms  run: ${RUN_SECONDS}s"
echo ""

# Initialize the data directory (generates a node key).
"$DREGG" init --data-dir "$DATA_DIR" >/dev/null

# Start the node: solo committee-of-one, blocklace consensus, fast cadence.
"$DREGG" run \
  --data-dir "$DATA_DIR" \
  --port "$PORT" \
  --gossip-port "$GOSSIP_PORT" \
  --federation-size 1 \
  --federation-mode solo \
  --consensus blocklace \
  --block-cadence-ms "$CADENCE_MS" \
  >"$DATA_DIR/node.log" 2>&1 &
NODE_PID=$!

# Wait for the HTTP API to come up.
echo "Waiting for HTTP API ..."
for _ in $(seq 1 40); do
  if curl -fsS "http://127.0.0.1:$PORT/status" >/dev/null 2>&1; then
    break
  fi
  if ! kill -0 "$NODE_PID" 2>/dev/null; then
    echo "--- node.log ---"; cat "$DATA_DIR/node.log" || true
    fail "node exited before the API came up"
  fi
  sleep 0.25
done
curl -fsS "http://127.0.0.1:$PORT/status" >/dev/null 2>&1 || {
  echo "--- node.log ---"; cat "$DATA_DIR/node.log" || true
  fail "HTTP API never became reachable"
}

# Let the cadence produce several blocks.
echo "Letting the node produce blocks for ${RUN_SECONDS}s ..."
sleep "$RUN_SECONDS"

# ── Query the block list ───────────────────────────────────────────────────
echo ""
echo "=== GET /api/blocklace/blocks ==="
BLOCKS_JSON="$(curl -fsS "http://127.0.0.1:$PORT/api/blocklace/blocks")"
echo "$BLOCKS_JSON" | python3 -m json.tool 2>/dev/null | head -60 || echo "$BLOCKS_JSON"

COUNT="$(echo "$BLOCKS_JSON" | python3 -c 'import sys,json; print(len(json.load(sys.stdin)))')"
MAX_HEIGHT="$(echo "$BLOCKS_JSON" | python3 -c 'import sys,json; b=json.load(sys.stdin); print(max((x["height"] for x in b), default=0))')"
echo ""
echo "block count: $COUNT   max height: $MAX_HEIGHT"

[ "$COUNT" -ge 2 ] || fail "expected >= 2 blocks, got $COUNT"
[ "$MAX_HEIGHT" -gt 1 ] || fail "expected max height > 1, got $MAX_HEIGHT (chain did not advance over time)"

# ── Assert non-zero parent hashes for non-genesis blocks ───────────────────
ZERO="0000000000000000000000000000000000000000000000000000000000000000"
NONZERO_PARENTS="$(echo "$BLOCKS_JSON" | python3 -c '
import sys, json
blocks = json.load(sys.stdin)
zero = "0"*64
# every block at height > 1 must have a real (non-zero) prev_hash
bad = [b["height"] for b in blocks if b["height"] > 1 and b["prev_hash"] == zero]
nonzero = [b for b in blocks if b["prev_hash"] != zero]
print(len(nonzero))
if bad:
    sys.stderr.write("blocks with zero parent above genesis: %r\n" % bad)
    sys.exit(3)
')" || fail "found non-genesis blocks with zero parent hash"
echo "blocks with non-zero parent hash: $NONZERO_PARENTS"
[ "$NONZERO_PARENTS" -ge 1 ] || fail "no block carried a real (non-zero) parent hash"

# ── Fetch one block by height and check parent consistency ─────────────────
echo ""
echo "=== GET /api/block/$MAX_HEIGHT ==="
BLOCK_JSON="$(curl -fsS "http://127.0.0.1:$PORT/api/block/$MAX_HEIGHT")"
echo "$BLOCK_JSON" | python3 -m json.tool 2>/dev/null || echo "$BLOCK_JSON"

echo "$BLOCK_JSON" | python3 -c '
import sys, json
b = json.load(sys.stdin)
zero = "0"*64
assert b["height"] > 1, "tip height should be > 1"
assert b["block_hash"] and b["block_hash"] != zero, "block_hash must be a real hash"
assert b["prev_hash"] != zero, "tip block prev_hash must be non-zero (real parent link)"
assert len(b["predecessors"]) >= 1, "tip block must record >= 1 predecessor"
assert b["prev_hash"] == b["predecessors"][0], "prev_hash must equal first predecessor"
print("tip block OK: height=%d hash=%s.. prev=%s.. kind=%s round=%s" % (
    b["height"], b["block_hash"][:12], b["prev_hash"][:12], b["kind"], b["finality_round"]))
' || fail "tip block failed parent-linkage assertions"

echo ""
echo "PASS: solo dregg-node produced real blocks with advancing height and real parent hashes."
