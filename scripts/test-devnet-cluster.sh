#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PYANA="$PROJECT_ROOT/target/release/pyana-node"

if [ ! -x "$PYANA" ]; then
  echo "ERROR: pyana-node binary not found at $PYANA"
  echo "Run: cargo build --release -p pyana-node"
  exit 1
fi

echo "=== Pyana Devnet Cluster Test ==="
echo ""

# Generate fresh devnet genesis
DEVNET_DIR=$(mktemp -d)
echo "Generating 3-validator devnet in $DEVNET_DIR ..."
"$PYANA" genesis --validators 3 --output "$DEVNET_DIR"

echo "Genesis generated. Contents:"
ls "$DEVNET_DIR"
echo ""

# Each node needs its own data directory (redb locks the DB file exclusively).
# We create per-node dirs with a symlink to the shared genesis.json and a copy of the key.
for i in 0 1 2; do
  NODE_DIR="$DEVNET_DIR/run-node-$i"
  mkdir -p "$NODE_DIR"
  cp "$DEVNET_DIR/genesis.json" "$NODE_DIR/genesis.json"
  cp "$DEVNET_DIR/node-$i.key" "$NODE_DIR/node.key"
done

BOUNTY_BOARD="$PROJECT_ROOT/target/release/pyana-bounty-board"
COMPUTE_EXCHANGE="$PROJECT_ROOT/target/release/compute-exchange"

cleanup() {
  echo ""
  echo "Cleaning up..."
  kill $PID0 $PID1 $PID2 $PID_BB $PID_CE 2>/dev/null || true
  wait $PID0 $PID1 $PID2 $PID_BB $PID_CE 2>/dev/null || true
  rm -rf "$DEVNET_DIR"
  echo "Done."
}
trap cleanup EXIT

# All nodes peer with each other for a fully-meshed gossip topology.
# Node 0 starts first and binds its gossip port; nodes 1 and 2 connect to it.
# Node 0 also lists nodes 1 and 2 as peers so it will initiate connections
# once they are available (the gossip layer retries).

echo "Starting Node 0 (HTTP :8420, gossip :9420) ..."
"$PYANA" run \
  --data-dir "$DEVNET_DIR/run-node-0" \
  --key-file node.key \
  --node-index 0 \
  --federation-size 3 \
  --port 8420 \
  --gossip-port 9420 \
  --bind 127.0.0.1 \
  --federation-peers 127.0.0.1:9421,127.0.0.1:9422 \
  --enable-faucet &
PID0=$!

# Give node 0 a moment to bind its gossip port before peers try to connect
sleep 1

echo "Starting Node 1 (HTTP :8421, gossip :9421) ..."
"$PYANA" run \
  --data-dir "$DEVNET_DIR/run-node-1" \
  --key-file node.key \
  --node-index 1 \
  --federation-size 3 \
  --port 8421 \
  --gossip-port 9421 \
  --bind 127.0.0.1 \
  --federation-peers 127.0.0.1:9420 &
PID1=$!

echo "Starting Node 2 (HTTP :8422, gossip :9422) ..."
"$PYANA" run \
  --data-dir "$DEVNET_DIR/run-node-2" \
  --key-file node.key \
  --node-index 2 \
  --federation-size 3 \
  --port 8422 \
  --gossip-port 9422 \
  --bind 127.0.0.1 \
  --federation-peers 127.0.0.1:9420,127.0.0.1:9421 &
PID2=$!

echo ""
echo "Waiting for nodes to start..."
sleep 4

# Health checks — the status endpoint is /status (returns 200 + JSON)
echo ""
echo "=== Health Checks ==="
PASS=0
FAIL=0

for i in 0 1 2; do
  PORT=$((8420 + i))
  HTTP_CODE=$(curl -s -o /dev/null -w "%{http_code}" "http://127.0.0.1:$PORT/status" 2>/dev/null)
  if [ "$HTTP_CODE" = "200" ]; then
    STATUS=$(curl -s "http://127.0.0.1:$PORT/status")
    echo "Node $i (port $PORT): OK [$STATUS]"
    PASS=$((PASS + 1))
  else
    echo "Node $i (port $PORT): FAILED (HTTP $HTTP_CODE)"
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "=== Peer Connectivity ==="
# After gossip connects, peer_count in /status should be > 0 for nodes with peers
for i in 0 1 2; do
  PORT=$((8420 + i))
  STATUS=$(curl -s "http://127.0.0.1:$PORT/status" 2>/dev/null || echo "{}")
  echo "Node $i: $STATUS"
done

echo ""
echo "=== Starting Apps (bounty-board + compute-exchange) ==="
# Apps fetch federation root from the running node — no --dev flag needed.
if [ -x "$BOUNTY_BOARD" ]; then
  echo "Starting bounty-board (HTTP :3030, node: 127.0.0.1:8420) ..."
  "$BOUNTY_BOARD" --node-url "http://127.0.0.1:8420" --listen "127.0.0.1:3030" &
  PID_BB=$!
  sleep 1
  BB_CODE=$(curl -s -o /dev/null -w "%{http_code}" "http://127.0.0.1:3030/health" 2>/dev/null)
  if [ "$BB_CODE" = "200" ]; then
    echo "  bounty-board: OK"
  else
    echo "  bounty-board: FAILED (HTTP $BB_CODE)"
  fi
else
  echo "  bounty-board binary not found, skipping (build with: cargo build --release -p pyana-bounty-board)"
  PID_BB=""
fi

if [ -x "$COMPUTE_EXCHANGE" ]; then
  echo "Starting compute-exchange (HTTP :3040, node: 127.0.0.1:8420) ..."
  "$COMPUTE_EXCHANGE" --node-url "http://127.0.0.1:8420" --listen "127.0.0.1:3040" &
  PID_CE=$!
  sleep 1
  CE_CODE=$(curl -s -o /dev/null -w "%{http_code}" "http://127.0.0.1:3040/health" 2>/dev/null)
  if [ "$CE_CODE" = "200" ]; then
    echo "  compute-exchange: OK"
  else
    echo "  compute-exchange: FAILED (HTTP $CE_CODE)"
  fi
else
  echo "  compute-exchange binary not found, skipping (build with: cargo build --release -p compute-exchange)"
  PID_CE=""
fi

echo ""
echo "=== Faucet Test (Node 0) ==="
# The faucet requires a 64-char hex recipient (cell ID).
RECIPIENT="deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
FAUCET_RESP=$(curl -s -X POST "http://127.0.0.1:8420/api/faucet" \
  -H "Content-Type: application/json" \
  -d "{\"recipient\": \"$RECIPIENT\", \"amount\": 100}" 2>&1)
echo "Faucet response: $FAUCET_RESP"

if echo "$FAUCET_RESP" | grep -q '"success":true'; then
  echo ""
  echo "=== Propagation Check (wait 3s for gossip) ==="
  sleep 3
  for i in 0 1 2; do
    PORT=$((8420 + i))
    BLOCK=$(curl -s "http://127.0.0.1:$PORT/status" 2>/dev/null || echo "{}")
    echo "Node $i status: $BLOCK"
  done
fi

echo ""
echo "=== Results ==="
echo "Nodes healthy: $PASS/3"
echo "Nodes failed:  $FAIL/3"

if [ "$FAIL" -eq 0 ]; then
  echo ""
  echo "SUCCESS: All 3 nodes started and responded to health checks."
  exit 0
else
  echo ""
  echo "FAILURE: $FAIL node(s) did not respond."
  exit 1
fi
