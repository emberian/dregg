#!/usr/bin/env bash
# Build multi-arch images for all services (amd64 + arm64 for Graviton).
#
# Usage:
#   ./docker/build-multiarch.sh              # build all
#   ./docker/build-multiarch.sh node         # build only node
#   ./docker/build-multiarch.sh --push       # build + push to registry
#
# Prerequisites:
#   docker buildx create --name pyana-builder --use
#   docker buildx inspect --bootstrap

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REGISTRY="${REGISTRY:-ghcr.io/pyana-dev/breadstuffs}"
PLATFORMS="${PLATFORMS:-linux/amd64,linux/arm64}"

PUSH_FLAG=""
TARGETS=("node" "gallery" "discharge-gateway")

for arg in "$@"; do
    case "$arg" in
        --push) PUSH_FLAG="--push" ;;
        node|gallery|discharge-gateway) TARGETS=("$arg") ;;
    esac
done

echo "Building for platforms: $PLATFORMS"
echo "Targets: ${TARGETS[*]}"
echo "Registry: $REGISTRY"
echo ""

for target in "${TARGETS[@]}"; do
    echo "==> Building pyana-${target}..."
    docker buildx build \
        --platform "$PLATFORMS" \
        --target "$target" \
        --tag "${REGISTRY}/pyana-${target}:latest" \
        --file "$SCRIPT_DIR/Dockerfile" \
        $PUSH_FLAG \
        "$REPO_ROOT"
    echo ""
done

echo "Done."
