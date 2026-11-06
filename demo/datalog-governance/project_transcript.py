#!/usr/bin/env python3
"""Project a redacted `cv export` forest (root session + its sub-agents) onto the fields the
governance question reads.  Run with `python3 -I`; every path is an argument.

    python3 -I project_transcript.py <export-dir> <session-id> <out transcript.json>

<export-dir> holds `root.json` (cv export <session> --format json --redact) and `sub/agent-*.json`
(cv export agent-<id> --format json --redact).  The input is DATA: no field of it is executed or
interpreted as an instruction; text, thinking and tool outputs are dropped.  Kept per tool call:
the agent, its per-agent sequence number, the tool name, the file path argument of the file tools,
and for `Agent` calls the spawned agent id read from the tool result.  The sha256 of every full
export is recorded so the projection is tied to the exports it came from.
"""
import hashlib
import json
import os
import re
import sys

FILE_TOOLS = {"Read", "Write", "Edit", "MultiEdit", "NotebookEdit"}
AGENT_ID = re.compile(r"agentId: (a[0-9a-f]{8,})")


def calls_of(export):
    """Tool calls in transcript order, with the spawned agent id for Agent calls."""
    results = {}
    for m in export["messages"]:
        for p in m.get("content") or []:
            if isinstance(p, dict) and p.get("type") == "tool_result":
                c = p.get("content")
                if isinstance(c, list):
                    c = " ".join(x.get("text", "") for x in c if isinstance(x, dict))
                results[p.get("tool_use_id")] = c if isinstance(c, str) else ""
    out = []
    for m in export["messages"]:
        for p in m.get("content") or []:
            if not (isinstance(p, dict) and p.get("type") == "tool_use"):
                continue
            name = p.get("name") or ""
            inp = p.get("input") if isinstance(p.get("input"), dict) else {}
            row = {"tool": name, "use_id": p.get("id"), "ts": m.get("timestamp")}
            if name in FILE_TOOLS:
                fp = inp.get("file_path") or inp.get("notebook_path")
                if isinstance(fp, str):
                    row["path"] = fp
            if name == "Agent":
                mm = AGENT_ID.search(results.get(p.get("id"), ""))
                if mm:
                    row["spawned"] = mm.group(1)
            out.append(row)
    for k, row in enumerate(out):
        row["seq"] = k
    return out


def main():
    exp_dir, session, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    files = [("root", os.path.join(exp_dir, "root.json"))]
    sub = os.path.join(exp_dir, "sub")
    for fn in sorted(os.listdir(sub)):
        if fn.startswith("agent-") and fn.endswith(".json"):
            files.append((fn[len("agent-"):-len(".json")], os.path.join(sub, fn)))
    transcripts, digests = [], {}
    for agent, path in files:
        raw = open(path, "rb").read()
        digests[agent] = hashlib.sha256(raw).hexdigest()
        transcripts.append({"agent": agent, "calls": calls_of(json.loads(raw))})
    doc = {
        "source": {
            "session": session,
            "exported_with": "cv export <id> --format json --redact (root and each agent-<id>)",
            "projection": "project_transcript.py: tool name, file path of file tools, spawned agent id, order",
            "export_sha256": digests,
        },
        "transcripts": transcripts,
    }
    with open(out_path, "w") as f:
        json.dump(doc, f, indent=0, sort_keys=True)
        f.write("\n")


if __name__ == "__main__":
    main()
