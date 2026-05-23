#!/usr/bin/env bash
# demo.sh — End-to-end bounty-board workflow against local devnet.
#
# This script exercises the bounty board's HTTP API using curl.
# For the REAL privacy-preserving flow with STARK proofs, see:
#   cargo run -p pyana-bounty-board --example devnet_demo
#
# Prerequisites:
#   1. Devnet running (pyana-node on port 8420)
#   2. Bounty board running: cargo run -p pyana-bounty-board -- --node-url http://127.0.0.1:8420
#
# Usage:
#   chmod +x demo.sh && ./demo.sh
#
# =============================================================================
# PRIVACY MODEL OVERVIEW
# =============================================================================
#
# The bounty board demonstrates privacy-preserving work marketplace operations:
#
# 1. ANONYMITY: Workers claim bounties using a "blinded commitment" —
#    a Poseidon2 hash of their public key + random nonce. The issuer cannot
#    determine which federation member is doing the work.
#
# 2. UNLINKABILITY: Each claim uses DIFFERENT randomness, so the same worker
#    claiming multiple bounties produces unrelated commitments. The board cannot
#    correlate claims to the same worker.
#
# 3. QUALIFICATION WITHOUT IDENTITY: Workers prove they meet requirements
#    (e.g., "I am a federation member") via STARK proofs that reveal NOTHING
#    about their identity. The proof shows set membership without revealing
#    WHICH member. This demo uses curl (no proof generation), but the Rust
#    example (devnet_demo) generates real STARK proofs.
#
# 4. ATOMIC PAYMENT: On approval, the reward is released via conditional turns.
#    The worker reveals their identity only at delivery time (or never, if the
#    delivery artifact is itself anonymous).
#
# =============================================================================

set -euo pipefail

BASE_URL="${BOUNTY_BOARD_URL:-http://127.0.0.1:3030}"

echo "=== Pyana Bounty Board Demo (curl) ==="
echo "Target: $BASE_URL"
echo ""
echo "NOTE: This script exercises the HTTP API without generating real proofs."
echo "      For the full privacy-preserving flow with STARK proofs, run:"
echo "        cargo run -p pyana-bounty-board --example devnet_demo"
echo ""

# =============================================================================
# Step 1: Health check — verify the board is running and show federation state
# =============================================================================
echo "--- [1] Health Check ---"
echo "    Purpose: Verify the board is running, check federation root status."
echo "    The federation root is the Merkle root of all members; proofs are"
echo "    verified against this root."
echo ""
curl -s "$BASE_URL/health" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/health"
echo ""

# =============================================================================
# Step 2: Advance block height (devnet utility)
# =============================================================================
echo "--- [2] Advancing block height to 10 ---"
echo "    Purpose: Set up a height so deadlines are in the future."
echo ""
curl -s -X POST "$BASE_URL/admin/height" \
  -H "Content-Type: application/json" \
  -d '{"delta": 10}' | python3 -m json.tool 2>/dev/null || true
echo ""

# =============================================================================
# Step 3: Create a bounty (no qualification required)
# =============================================================================
echo "--- [3] Creating bounty: 'Implement Merkle proof helper' ---"
echo "    Qualification: None (anyone can claim)"
echo "    Privacy: Even with no qualification proof required, the worker's"
echo "    identity is hidden behind the blinded commitment. The issuer posts"
echo "    the bounty but cannot predict who will claim it."
echo ""

# Deterministic issuer cell for demo purposes.
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

# =============================================================================
# Step 4: Create a bounty requiring federation membership
# =============================================================================
echo "--- [4] Creating bounty: 'Audit escrow logic' (federation member required) ---"
echo "    Qualification: FederationMember"
echo "    Privacy: To claim this bounty, a worker must present a STARK proof"
echo "    demonstrating federation membership. The proof proves set membership"
echo "    WITHOUT revealing which member the worker is. The verifier learns only"
echo "    that 'some valid member wants to claim this bounty.'"
echo ""

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

# =============================================================================
# Step 5: List bounties (public discovery)
# =============================================================================
echo "--- [5] Listing all bounties ---"
echo "    Purpose: Bounties are publicly discoverable. Workers browse them"
echo "    before deciding to commit resources. No identity is revealed by browsing."
echo ""
curl -s "$BASE_URL/bounties" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties"
echo ""

# =============================================================================
# Step 6: Filter by tag
# =============================================================================
echo "--- [6] Listing bounties tagged 'rust' ---"
echo "    Purpose: Filtering is also anonymous — no session or identity required."
echo ""
curl -s "$BASE_URL/bounties?tag=rust" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties?tag=rust"
echo ""

# =============================================================================
# Step 7: Claim the first bounty (no qualification needed)
# =============================================================================
if [ -n "$BOUNTY_ID" ]; then
  echo "--- [7] Claiming bounty $BOUNTY_ID ---"
  echo "    Privacy: The worker presents a BLINDED COMMITMENT instead of their"
  echo "    public key. This commitment is: Poseidon2(worker_key || randomness)."
  echo "    The issuer CANNOT reverse this hash to learn the worker's identity."
  echo "    Each claim uses fresh randomness, so even the board cannot link"
  echo "    multiple claims to the same worker."
  echo ""
  echo "    Worker commitment (blinded): bbbb...bbbb"
  echo "    (In the real flow, this would be a proper Poseidon2 hash)"
  echo ""

  CLAIM_RESULT=$(curl -s -X POST "$BASE_URL/bounties/$BOUNTY_ID/claim" \
    -H "Content-Type: application/json" \
    -d "{
      \"bounty_id\": \"$BOUNTY_ID\",
      \"worker_commitment\": [187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187,187],
      \"qualification_proof\": null
    }")
  echo "$CLAIM_RESULT" | python3 -m json.tool 2>/dev/null || echo "$CLAIM_RESULT"
  echo ""

  # ===========================================================================
  # Step 8: Submit work
  # ===========================================================================
  echo "--- [8] Submitting work for bounty $BOUNTY_ID ---"
  echo "    Privacy: The worker submits using the SAME commitment from the claim."
  echo "    This proves continuity (same worker who claimed is now submitting)"
  echo "    without revealing identity. The completion evidence is hashed for"
  echo "    integrity, but the work product itself can be delivered out-of-band."
  echo ""

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

  # ===========================================================================
  # Step 9: Approve (issuer approves, triggering atomic payment)
  # ===========================================================================
  echo "--- [9] Issuer approving bounty $BOUNTY_ID ---"
  echo "    Privacy: Only the issuer (identified by their cell ID) can approve."
  echo "    Approval triggers ATOMIC payment via conditional turns:"
  echo "    the reward is released to the worker in a single indivisible step."
  echo "    The payment receipt is a cryptographic proof that transfer occurred."
  echo ""

  APPROVE_RESULT=$(curl -s -X POST "$BASE_URL/bounties/$BOUNTY_ID/approve" \
    -H "Content-Type: application/json" \
    -d "{
      \"bounty_id\": \"$BOUNTY_ID\",
      \"issuer_cell\": \"$ISSUER_CELL\"
    }")
  echo "$APPROVE_RESULT" | python3 -m json.tool 2>/dev/null || echo "$APPROVE_RESULT"
  echo ""

  # ===========================================================================
  # Step 10: Check final status
  # ===========================================================================
  echo "--- [10] Final bounty status ---"
  echo "    The bounty should now be in 'Paid' state with a receipt hash."
  echo ""
  curl -s "$BASE_URL/bounties/$BOUNTY_ID/status" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/bounties/$BOUNTY_ID/status"
  echo ""
fi

# =============================================================================
# Step 11: Final health check showing aggregated bounty counts
# =============================================================================
echo "--- [11] Final Health Check ---"
curl -s "$BASE_URL/health" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/health"
echo ""

echo "=== Demo Complete ==="
echo ""
echo "What was demonstrated:"
echo "  - Bounty creation with qualification requirements"
echo "  - Anonymous claiming via blinded commitments"
echo "  - Work submission with proof-of-completion"
echo "  - Atomic payment release on approval"
echo ""
echo "For the REAL privacy-preserving flow with STARK proofs, run:"
echo "  cargo run -p pyana-bounty-board --example devnet_demo"
