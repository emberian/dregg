#!/usr/bin/env python3
"""Exact language check between two complete byte tables: `complement` mode says L(a) is the
complement of L(b), by search over every reachable state pair. Run with python3 -I."""
import json, sys
a, b, mode = json.load(open(sys.argv[1])), json.load(open(sys.argv[2])), sys.argv[3]
def step(t, s, x): 
    i = s * 256 + x
    return t["transitions"][i] if i < len(t["transitions"]) else 0
seen, todo = set(), [(a["start"], b["start"])]
acc_a, acc_b = set(a["accepting"]), set(b["accepting"])
while todo:
    p = todo.pop()
    if p in seen: continue
    seen.add(p)
    ia, ib = p[0] in acc_a, p[1] in acc_b
    if (mode == "complement" and ia == ib) or (mode == "equal" and ia != ib):
        print(f"DIFFER at state pair {p}"); sys.exit(1)
    for x in range(256):
        todo.append((step(a, p[0], x), step(b, p[1], x)))
print(f"{mode}: {len(seen)} reachable state pairs agree")
