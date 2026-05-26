#!/bin/bash
# Backward-compatible entrypoint for the combined gateway + Discord bot update.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "$SCRIPT_DIR/update.sh"
