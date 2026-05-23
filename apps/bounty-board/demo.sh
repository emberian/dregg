#!/usr/bin/env bash
# demo.sh — End-to-end bounty-board workflow against local devnet.
#
# Prerequisites:
#   1. Devnet running (pyana-node on port 8420)
#   2. Bounty board running: cargo run -p pyana-bounty-board
#
# Usage:
#   chmod +x demo.sh && ./demo.sh

set -euo pipefail

BASE_URL="${BOUNTY_BOARD_URL:-http://127.0.0.1:3030}"

echo "=== Pyana Bounty Board Demo ==="
echo "Target: $BASE_URL"
echo ""

# --- Health check ---
echo "--- Health Check ---"
curl -s "$BASE_URL/health" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/health"
echo ""

# --- Advance height so deadlines work ---
echo "--- Advancing block height to 10 ---"
curl -s -X POST "$BASE_URL/admin/height" \
  -H "Content-Type: application/json" \
  -d '{"delta": 10}' | python3 -m json.tool 2>/dev/null || true
echo ""

# --- Create a bounty (no qualification required) ---
echo "--- Creating bounty: 'Implement Merkle proof helper' (no qualification) ---"
# Use a deterministic issuer cell for demo purposes.
ISSUER_CELL="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

RESULT=$(curl -s -X POST "$BASE_URL/bounties" \
  -H "Content-Type: application/json" \
  -d "{
    \"title\": \"Implement Merkle proof helper\",
    \"description\": \"Write a helper function that generates and verifies Merkle inclusion proofs for the note tree.\",
    \"reward_amount\": 5000,
    \"reward_asset\": 1,
    \"deadline_height\": 1000,
    \"qualification\": \"None\",
    \"tags\": [\"rust\", \"crypto\", \"beginner\"],
    \"issuer_cell\": \"$ISSUER_CELL\",
    \"reward_token\": null
  }")

echo "$RESULT" | python3 -m json.tool 2>/dev/null || echo "$RESULT"
BOUNTY_ID=$(echo "$RESULT" | python3 -c "import sys,json; print(json.load(sys.stdin)['id'])" 2>/dev/null || echo "")
echo ""

# --- Create a second bounty (federation membership required) ---
echo "--- Creating bounty: 'Audit escrow logic' (federation member required) ---"
RESULT2=$(curl -s -X POST "$BASE_URL/bounties" \
  -H "Content-Type: application/json" \
  -d "{
    \"title\": \"Audit escrow logic\",
    \"description\": \"Security review of the conditional turn escrow implementation. Must be a federation member.\",
    \"reward_amount\": 25000,
    \"reward_asset\": 1,
    \"deadline_height\": 2000,
    \"qualification\": \"FederationMember\",
    \"tags\": [\"security\", \"audit\", \"advanced\"],
    \"issuer_cell\": \"$ISSUER_CELL\",
    \"reward_token\": null
  }")

echo "$RESULT2" | python3 -m json.tool 2>/dev/null || echo "$RESULT2"
echo ""

# --- List all bounties ---
echo "--- Listing all bounties ---"
curl -s "$BASE_URL/bounties" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties"
echo ""

# --- Filter by tag ---
echo "--- Listing bounties tagged 'rust' ---"
curl -s "$BASE_URL/bounties?tag=rust" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties?tag=rust"
echo ""

# --- Claim the first bounty (no qualification needed, so empty proof is fine) ---
if [ -n "$BOUNTY_ID" ]; then
  echo "--- Claiming bounty $BOUNTY_ID ---"
  # Worker commitment: hash(worker_key || randomness) — using a deterministic value for demo.
  WORKER_COMMITMENT="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

  CLAIM_RESULT=$(curl -s -X POST "$BASE_URL/bounties/$BOUNTY_ID/claim" \
    -H "Content-Type: application/json" \
    -d "{
      \"bounty_id\": \"$BOUNTY_ID\",
      \"worker_commitment\": [187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187],
      \"qualification_proof\": null
    }")
  echo "$CLAIM_RESULT" | python3 -m json.tool 2>/dev/null || echo "$CLAIM_RESULT"
  echo ""

  # --- Submit work ---
  echo "--- Submitting work for bounty $BOUNTY_ID ---"
  SUBMIT_RESULT=$(curl -s -X POST "$BASE_URL/bounties/$BOUNTY_ID/submit" \
    -H "Content-Type: application/json" \
    -d "{
      \"bounty_id\": \"$BOUNTY_ID\",
      \"worker_commitment\": [187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187],
      \"completion_evidence\": {\"ExternalProof\": {\"url\": \"https://github.com/pyana-dev/breadstuffs/pull/42\", \"hash\": [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]}},
      \"completion_proof\": [1,2,3,4,5,6,7,8]
    }")
  echo "$SUBMIT_RESULT" | python3 -m json.tool 2>/dev/null || echo "$SUBMIT_RESULT"
  echo ""

  # --- Approve (issuer approves, triggering payment) ---
  echo "--- Issuer approving bounty $BOUNTY_ID ---"
  APPROVE_RESULT=$(curl -s -X POST "$BASE_URL/bounties/$BOUNTY_ID/approve" \
    -H "Content-Type: application/json" \
    -d "{
      \"bounty_id\": \"$BOUNTY_ID\",
      \"issuer_cell\": \"$ISSUER_CELL\"
    }")
  echo "$APPROVE_RESULT" | python3 -m json.tool 2>/dev/null || echo "$APPROVE_RESULT"
  echo ""

  # --- Check final status ---
  echo "--- Final bounty status ---"
  curl -s "$BASE_URL/bounties/$BOUNTY_ID/status" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties/$BOUNTY_ID/status"
  echo ""
fi

# --- Final health check showing bounty counts ---
echo "--- Final Health Check ---"
curl -s "$BASE_URL/health" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/health"
echo ""

echo "=== Demo Complete ==="
