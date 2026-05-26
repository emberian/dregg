#!/bin/bash
# Generate devnet genesis state using the canonical dregg-node genesis command.
#
# Usage:
#   cd deploy/genesis
#   ./generate.sh
#
# To regenerate from scratch (removes previously generated devnet files):
#   ./generate.sh --force
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
  FORCE=1
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--force]" >&2
  exit 2
fi

cd "$SCRIPT_DIR"

generated_glob=(node-*.key node-*.env)
existing_generated=()
for path in genesis.json .devnet "${generated_glob[@]}"; do
  if [[ -e "$path" ]]; then
    existing_generated+=("$path")
  fi
done

if [[ ${#existing_generated[@]} -gt 0 && $FORCE -eq 0 ]]; then
  echo "ERROR: generated genesis files already exist:"
  printf '  %s\n' "${existing_generated[@]}"
  echo "Use --force to regenerate (this will invalidate existing devnet state)."
  exit 1
fi

if [[ $FORCE -eq 1 ]]; then
  rm -f genesis.json .devnet node-*.key node-*.env
  rm -rf keys secrets
fi

echo "=== Generating devnet genesis state ==="
echo "Using cargo run --release -p dregg-node -- genesis"

cd "$REPO_DIR"
cargo run --release -p dregg-node -- genesis \
  --validators 3 \
  --epoch-length 100 \
  --checkpoint-interval 10 \
  --output "$SCRIPT_DIR"

echo ""
echo "=== Genesis state generated ==="
echo ""
echo "Files:"
echo "  deploy/genesis/genesis.json  federation genesis state"
echo "  deploy/genesis/.devnet       devnet marker"
echo "  deploy/genesis/node-*.key    validator private keys (DO NOT COMMIT)"
echo "  deploy/genesis/node-*.env    validator environment files"
echo ""
echo "Deploy with:"
echo "  scp deploy/genesis/genesis.json devnet.dregg.fg-goose.online:/opt/dregg-data/"
echo "  ssh devnet.dregg.fg-goose.online sudo systemctl restart dregg-gateway"
echo ""
echo "Or use the deploy script:"
echo "  ./deploy/aws/update.sh"
echo ""
echo "WARNING: These keys are for DEVNET use only. Do NOT use in production."
