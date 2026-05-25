#!/usr/bin/env bash
# Graceful shutdown of the multi-node devnet. Sends SIGTERM to every
# pid in state/pids/, waits up to 5s, escalates to SIGKILL.
#
# Idempotent: safe to run when no devnet is up.

set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/lib/common.sh"

if [ ! -d "$PID_DIR" ]; then
    devnet_dim "no PID_DIR at $PID_DIR — nothing to stop"
    exit 0
fi

devnet_step "stopping devnet (TERM then KILL after 5s)"

stopped_any=0
for pidfile in "$PID_DIR"/*.pid; do
    [ -f "$pidfile" ] || continue
    pid=$(cat "$pidfile" 2>/dev/null || echo "")
    name=$(basename "$pidfile" .pid)
    if [ -z "$pid" ]; then
        rm -f "$pidfile"
        continue
    fi
    if kill -0 "$pid" 2>/dev/null; then
        kill -TERM "$pid" 2>/dev/null || true
        devnet_dim "$name (pid=$pid) ← SIGTERM"
        stopped_any=1
    else
        devnet_dim "$name (pid=$pid) already gone"
        rm -f "$pidfile"
    fi
done

# Wait up to 5s for graceful exit.
for _ in 1 2 3 4 5; do
    all_gone=1
    for pidfile in "$PID_DIR"/*.pid; do
        [ -f "$pidfile" ] || continue
        pid=$(cat "$pidfile" 2>/dev/null || echo "")
        if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
            all_gone=0
        fi
    done
    [ "$all_gone" = "1" ] && break
    sleep 1
done

# Escalate any survivors.
for pidfile in "$PID_DIR"/*.pid; do
    [ -f "$pidfile" ] || continue
    pid=$(cat "$pidfile" 2>/dev/null || echo "")
    name=$(basename "$pidfile" .pid)
    if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
        devnet_warn "$name (pid=$pid) did not exit on TERM; sending KILL"
        kill -KILL "$pid" 2>/dev/null || true
    fi
    rm -f "$pidfile"
done

rm -f "$STATE_DIR/.devnet-up"

if [ "$stopped_any" = "1" ]; then
    devnet_ok "devnet stopped"
else
    devnet_dim "no live processes; pidfiles cleaned"
fi
