#!/usr/bin/env python3
"""Flatten a projected transcript into Datalog facts.  Run with `python3 -I`; paths are arguments.

    python3 -I extract_edb.py <transcript.json> <program.json> <out edb.json>

Facts (predicate numbers in program.json "preds"; every value an integer):
  tool_call(id, agent, tool, seq)   one per tool call; id is a global occurrence number, so two
                                    identical calls stay two facts (exact SET count = event count)
  writes(id, path)                  Write / Edit / MultiEdit / NotebookEdit with a file path
  edits(id, path)                   the same, without Write (a modification, not a creation)
  reads(id, path)                   Read with a file path
  spawned(child, parent, seq)       parent's Agent call at its step `seq` launched `child`
  next(agent, s, s+1)               consecutive steps of one agent (the order the rules read)
  forbidden_prefix(dir)             the policy's directories
  prefix_of(path, dir)              every ancestor directory of every WRITTEN path
  name(sid, utf8)                   every string id with its UTF-8 bytes as one big-endian integer,
                                    so the EDB root binds what each id means
Strings (agents, tools, paths, dirs) are interned as 1_000_000 + k in first-seen order.
"""
import json
import sys


def main():
    tr = json.load(open(sys.argv[1]))
    prog = json.load(open(sys.argv[2]))
    out = sys.argv[3]
    P = prog["preds"]
    strings = {}

    def sid(s):
        if s not in strings:
            strings[s] = 1_000_000 + len(strings)
        return strings[s]

    facts = []
    have = set()

    def add(p, *args):
        f = (P[p], tuple(args))
        if f not in have:
            have.add(f)
            facts.append(f)

    agents = {t["agent"] for t in tr["transcripts"]}
    gid = 0
    written = []
    for t in tr["transcripts"]:
        a = sid(t["agent"])
        calls = t["calls"]
        for c in calls:
            gid += 1
            add("tool_call", gid, a, sid(c["tool"]), c["seq"])
            path = c.get("path")
            if path is not None:
                if c["tool"] == "Read":
                    add("reads", gid, sid(path))
                else:
                    add("writes", gid, sid(path))
                    if c["tool"] != "Write":
                        add("edits", gid, sid(path))
                    written.append(path)
            child = c.get("spawned")
            if child is not None and child in agents:
                add("spawned", sid(child), a, c["seq"])
        for k in range(len(calls) - 1):
            add("next", a, k, k + 1)
    for d in prog["forbidden_prefixes"]:
        add("forbidden_prefix", sid(d))
    for path in written:
        parts = path.split("/")
        for k in range(1, len(parts)):
            add("prefix_of", sid(path), sid("/".join(parts[:k]) + "/"))
    for s, i in strings.items():
        add("name", i, int.from_bytes(s.encode("utf-8"), "big"))
    json.dump({"facts": [[p, list(a)] for p, a in facts]}, open(out, "w"))
    open(out, "a").write("\n")
    unspawned = sorted(a for a in agents if a != "root" and
                       not any(f[0] == P["spawned"] and f[1][0] == strings[a] for f in facts))
    print(f"extract: {len(tr['transcripts'])} transcripts, {gid} tool calls, {len(facts)} facts, "
          f"{len(strings)} strings; sub-agents with no resolved spawn: {len(unspawned)}")


if __name__ == "__main__":
    main()
