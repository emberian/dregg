#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_ROOT"

echo "Generating devnet configuration..."
cargo run --release -p pyana-node -- genesis --validators 4 --output docker/devnet-config/

echo ""
echo "Building Docker image..."
docker compose -f docker/docker-compose.yml build

echo ""
echo "Starting 4-node devnet..."
docker compose -f docker/docker-compose.yml up -d

echo ""
echo "Devnet is running!"
echo "  Node 0 API: http://localhost:8420  (faucet enabled)"
echo "  Node 1 API: http://localhost:8421"
echo "  Node 2 API: http://localhost:8422"
echo "  Node 3 API: http://localhost:8423"
echo "  Explorer:   http://localhost:3000"
echo ""
echo "Faucet usage:"
echo "  curl -X POST http://localhost:8420/api/faucet \\"
echo "    -H 'Content-Type: application/json' \\"
echo "    -d '{\"recipient\": \"<64-hex-chars>\", \"amount\": 1000}'"
echo ""
echo "To stop: docker compose -f docker/docker-compose.yml down"
echo "To view logs: docker compose -f docker/docker-compose.yml logs -f"
