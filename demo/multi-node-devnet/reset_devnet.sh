#!/usr/bin/env bash
# Hard reset: stop the devnet (if running) and wipe `state/` entirely.
# Use before re-running a scenario from a clean slate, or to discard a
# stuck/half-booted devnet.
#
# NOTE: this is intentionally aggressive — it removes genesis + keys +
# logs + ledger state. The next `start_devnet.sh` produces *new*
# federation_ids because committee keys are regenerated. Per the
# greenfield posture, there is no on-disk shape to preserve.

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/lib/common.sh"

# Stop first (idempotent).
"$HERE/stop_devnet.sh" || true

if [ -d "$STATE_DIR" ]; then
    devnet_step "wiping state directory $STATE_DIR"
    rm -rf "$STATE_DIR"
    devnet_ok "state cleared"
else
    devnet_dim "no state directory to clean"
fi
