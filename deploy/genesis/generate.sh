#!/bin/bash
# Generate devnet genesis state
# Run once to create initial state, or re-run to reset devnet.
#
# Prerequisites:
#   - Rust toolchain (for pyana-node binary)
#   - openssl (fallback key generation)
#
# Usage:
#   cd deploy/genesis
#   ./generate.sh
#
# To regenerate from scratch (wipes existing keys):
#   ./generate.sh --force
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
  FORCE=1
fi

# Check for existing keys
if [[ -d keys && $FORCE -eq 0 ]]; then
  echo "ERROR: keys/ directory already exists."
  echo "  Use --force to regenerate (this will invalidate all existing state)."
  exit 1
fi

echo "=== Generating devnet genesis state ==="

mkdir -p keys secrets

# --- Validator keys ---
echo ""
echo "--- Validator keys ---"
VALIDATORS=3
for i in $(seq 0 $((VALIDATORS - 1))); do
  KEY_FILE="keys/node-${i}.key"
  PUB_FILE="keys/node-${i}.pub"

  if command -v pyana-node &>/dev/null; then
    echo "  [pyana-node] Generating validator key node-${i}..."
    pyana-node keygen --output "$KEY_FILE"
  else
    echo "  [openssl] Generating validator key node-${i}..."
    openssl genpkey -algorithm ed25519 -outform DER 2>/dev/null | tail -c 32 > "$KEY_FILE"
  fi

  chmod 600 "$KEY_FILE"

  # Extract public key (first 32 bytes of Ed25519 public from private)
  if command -v pyana-node &>/dev/null; then
    pyana-node pubkey --key "$KEY_FILE" > "$PUB_FILE"
  else
    # openssl extraction of Ed25519 public from DER private
    openssl pkey -outform DER -pubout 2>/dev/null < <(
      printf '\x30\x2e\x02\x01\x00\x30\x05\x06\x03\x2b\x65\x70\x04\x22\x04\x20'
      cat "$KEY_FILE"
    ) | tail -c 32 | xxd -p -c 64 > "$PUB_FILE"
  fi

  echo "    Private: $KEY_FILE"
  echo "    Public:  $(cat "$PUB_FILE" 2>/dev/null || echo '[generation pending]')"
done

# --- Account keys ---
echo ""
echo "--- Account keys ---"
ACCOUNTS=(alice bob carol dave eve faucet treasury relay nameservice bridge-operator)
for name in "${ACCOUNTS[@]}"; do
  KEY_FILE="keys/${name}.key"
  PUB_FILE="keys/${name}.pub"

  if command -v pyana-node &>/dev/null; then
    echo "  [pyana-node] Generating account key: ${name}..."
    pyana-node keygen --output "$KEY_FILE"
  else
    echo "  [openssl] Generating account key: ${name}..."
    openssl genpkey -algorithm ed25519 -outform DER 2>/dev/null | tail -c 32 > "$KEY_FILE"
  fi

  chmod 600 "$KEY_FILE"

  if command -v pyana-node &>/dev/null; then
    pyana-node pubkey --key "$KEY_FILE" > "$PUB_FILE"
  else
    openssl pkey -outform DER -pubout 2>/dev/null < <(
      printf '\x30\x2e\x02\x01\x00\x30\x05\x06\x03\x2b\x65\x70\x04\x22\x04\x20'
      cat "$KEY_FILE"
    ) | tail -c 32 | xxd -p -c 64 > "$PUB_FILE"
  fi

  echo "    ${name}: $KEY_FILE"
done

# --- Generate federation ID ---
echo ""
echo "--- Federation ID ---"
FED_ID="devnet-$(openssl rand -hex 16)"
echo "  Federation: $FED_ID"
echo "$FED_ID" > secrets/federation_id

# --- Compute routes commitment ---
echo ""
echo "--- Routes commitment ---"
ROUTES_HASH=$(sha256sum routes.json 2>/dev/null | cut -d' ' -f1 || shasum -a 256 routes.json | cut -d' ' -f1)
echo "  Commitment: $ROUTES_HASH"

# --- Assemble final genesis.json with real keys ---
echo ""
echo "--- Assembling genesis.json ---"

# If pyana-node is available, use its genesis subcommand for a proper build
if command -v pyana-node &>/dev/null; then
  echo "  Using pyana-node genesis command..."
  pyana-node genesis \
    --validators "$VALIDATORS" \
    --epoch-length 100 \
    --checkpoint-interval 10 \
    --output .
  echo "  genesis.json written by pyana-node."
else
  echo "  pyana-node not found; using template genesis.json with placeholder keys."
  echo "  NOTE: Run 'cargo build --release -p pyana-node' then re-run to get real keys."
fi

# --- Write .devnet marker ---
echo "# Devnet genesis directory" > .devnet
echo "# Generated: $(date -Iseconds)" >> .devnet
echo "# Federation: $FED_ID" >> .devnet

# --- Summary ---
echo ""
echo "=== Genesis state generated ==="
echo ""
echo "Files:"
echo "  genesis.json     — federation genesis state"
echo "  accounts.json    — account manifest"
echo "  apps.json        — deployed application manifest"
echo "  routes.json      — DFA route table"
echo "  keys/            — Ed25519 keypairs (DO NOT COMMIT)"
echo "  secrets/         — federation secrets (DO NOT COMMIT)"
echo ""
echo "Deploy with:"
echo "  scp genesis.json devnet.pyana.fg-goose.online:/opt/pyana-data/"
echo "  ssh devnet.pyana.fg-goose.online sudo systemctl restart pyana-gateway"
echo ""
echo "Or use the deploy script:"
echo "  ./deploy/aws/update.sh"
echo ""
echo "WARNING: These keys are for DEVNET use only. Do NOT use in production."
