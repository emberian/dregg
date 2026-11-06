#!/usr/bin/env bash
# Streaming receipts over a live Claude Code transcript (initiative 11).
#
#   ./run.sh <transcript.jsonl> <out_dir> [every=100] [follow_s=60]
#
# Starts the producer (Rust: tail + MMR + window cut; Lean `stream-check produce` computes each
# receipt, the Rust frontier cross-checks its root) and the follower (Lean `stream-check follow`,
# the only acceptor) side by side. The producer follows the transcript until it has been idle for
# follow_s seconds. Both run detached with PID files in <out_dir>; stop them by those PIDs only.
# At the end it audits a range from the last root alone and tampers with copies to show refusals.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
input="$1"; out="$2"; every="${3:-100}"; follow="${4:-60}"
checker="$repo/metatheory/.lake/build/bin/stream-check"
monitor="$repo/target/release/stream-monitor"
[ -x "$checker" ] || (cd "$repo/metatheory" && lake build stream-check)
[ -x "$monitor" ] || (cd "$repo" && cargo build -p dregg-query --release --bin stream-monitor)
[ -e "$out/receipts" ] && { echo "$out already has receipts; pick a fresh dir" >&2; exit 2; }
mkdir -p "$out"

nohup "$monitor" run --input "$input" --dir "$out" --checker "$checker" --every "$every" \
  --follow "$follow" > "$out/monitor.log" 2>&1 &
echo $! > "$out/monitor.pid"
nohup "$checker" follow "$out" $((follow + 30)) > "$out/follow.log" 2>&1 &
echo $! > "$out/follow.pid"
echo "producer pid $(cat "$out/monitor.pid"), follower pid $(cat "$out/follow.pid"); logs in $out"

wait "$(cat "$out/monitor.pid")" || { echo "producer failed:"; tail "$out/monitor.log"; exit 1; }
wait "$(cat "$out/follow.pid")" || { echo "follower REFUSED:"; tail -3 "$out/follow.log"; exit 1; }
tail -1 "$out/monitor.log"; tail -1 "$out/follow.log"

n=$(tail -1 "$out/follow.log" | awk '{print $4}')

# The publisher: an independent read of the SOURCE transcript's first n lines, not of the windows.
head -n "$n" "$input" > "$out/source-prefix.jsonl"
anchor=$("$checker" root "$out/source-prefix.jsonl" | awk '{print $2}')
echo "published root of the source's first $n lines: $anchor"
"$checker" verify "$out" --anchor "$anchor" | tail -1

lo=$(( n / 2 )); hi=$(( lo + 2 ))
"$monitor" audit --dir "$out" --lo "$lo" --hi "$hi" --root "$anchor"

# Tamper, three ways, on copies.
t="$out/tamper"; rm -rf "$t"; mkdir -p "$t"
refused() { if "$checker" verify "$@" > "$1.log"; then echo "NOT REFUSED (bug)"; else grep -m1 REFUSE "$1.log"; fi; }
copy() { mkdir -p "$1"; cp -R "$out/windows" "$out/receipts" "$1/"; }
# (1) the server deletes an entry from window 1 and keeps the honest receipts
copy "$t/drop"; sed -i.bak '2d' "$t/drop/windows/w000001.jsonl"; rm "$t/drop/windows/w000001.jsonl.bak"
echo "dropped entry, honest receipts:     $(refused "$t/drop")"
# (2) windows 1 and 2 swapped
copy "$t/swap"
if [ -e "$out/windows/w000002.jsonl" ]; then
  cp "$out/windows/w000002.jsonl" "$t/swap/windows/w000001.jsonl"
  cp "$out/windows/w000001.jsonl" "$t/swap/windows/w000002.jsonl"
fi
echo "swapped windows:                    $(refused "$t/swap")"
# (3) the PRODUCER drops an entry before cutting windows and recomputes every receipt honestly:
#     the chain checks, and only the anchor catches it (`anchored_is_genuine`).
mkdir -p "$t/reproduce/windows"; cp "$out"/windows/*.jsonl "$t/reproduce/windows/"
sed -i.bak '2d' "$t/reproduce/windows/w000001.jsonl"; rm "$t/reproduce/windows/w000001.jsonl.bak"
k=1; while [ -e "$t/reproduce/windows/$(printf 'w%06d.jsonl' $k)" ]; do "$checker" produce "$t/reproduce" > /dev/null; k=$((k+1)); done
echo "producer-side drop, chain alone:    $("$checker" verify "$t/reproduce" | tail -1 | cut -c1-60)"
echo "producer-side drop, anchored:       $(refused "$t/reproduce" --anchor "$anchor")"
