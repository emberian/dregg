#!/usr/bin/env bash
# Export the demo session (root + every sub-agent) with `cv export --format json --redact`.
# The sub-agent list is the one demo (b) projected (datalog-governance/data/transcript.json), so
# both demos read the same 73 transcripts. Output: corpus/exports/{root.json,sub/agent-<id>.json}.
# The exports contain tool inputs and stay out of git (.gitignore).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
session=e3ba49ed-a526-4ecd-8807-58b73757aaca
out="$here/corpus/exports"
mkdir -p "$out/sub"
cv export "$session" --format json --redact --frozen > "$out/root.json" 2> "$out/root.redact.txt"
python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1]))
for t in d["transcripts"]:
    if t["agent"] != "root":
        print(t["agent"])
' "$here/../datalog-governance/data/transcript.json" > "$out/agents.txt"
while read -r a; do
  cv export "agent-$a" --format json --redact --frozen > "$out/sub/agent-$a.json" 2> "$out/sub/agent-$a.redact.txt"
done < "$out/agents.txt"
echo "exported root + $(wc -l < "$out/agents.txt" | tr -d ' ') sub-agents to $out"
