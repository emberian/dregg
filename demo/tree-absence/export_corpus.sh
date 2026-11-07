#!/usr/bin/env bash
# Export the demo session (root + every sub-agent) with `cv export --format json --redact`.
# The sub-agent list comes from a LOCAL projection of the same session made by
# demo/datalog-governance/project_transcript.py (no longer in the repository: session-derived data
# stays out of git); pass its path as TRANSCRIPT. Output: corpus/exports/{root.json,sub/agent-<id>.json}.
# The exports contain tool inputs and stay out of git (.gitignore).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
session=e3ba49ed-a526-4ecd-8807-58b73757aaca
transcript="${TRANSCRIPT:?set TRANSCRIPT to a local project_transcript.py output for $session}"
out="$here/corpus/exports"
mkdir -p "$out/sub"
cv export "$session" --format json --redact --frozen > "$out/root.json" 2> "$out/root.redact.txt"
python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1]))
for t in d["transcripts"]:
    if t["agent"] != "root":
        print(t["agent"])
' "$transcript" > "$out/agents.txt"
while read -r a; do
  cv export "agent-$a" --format json --redact --frozen > "$out/sub/agent-$a.json" 2> "$out/sub/agent-$a.redact.txt"
done < "$out/agents.txt"
echo "exported root + $(wc -l < "$out/agents.txt" | tr -d ' ') sub-agents to $out"
