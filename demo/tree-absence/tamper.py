#!/usr/bin/env python3
"""Negative controls for a corpus certificate: each mutation must be REFUSED by tree-check.
Run with python3 -I.   tamper.py <cert.json> <kind> <out.json>
kinds: count+1, count-1, swap-records, refute-wrong-path, swap-table-digests, drop-record"""
import json, sys
c = json.load(open(sys.argv[1]))
kind, st, rc = sys.argv[2], None, None
st, rc = c["statement"], c["receipt"]
recs = rc["records"]
if kind == "count+1":
    st["count"] += 1
elif kind == "count-1":
    st["count"] -= 1
elif kind == "swap-records":
    recs[0], recs[1] = recs[1], recs[0]          # mmr_root left as stated
elif kind == "refute-wrong-path":
    # a record refuted at conjunct 1 (input/command); claim the same opening refutes conjunct 0 (name)
    r = next(r for r in recs if "refute" in r and r["refute"]["j"] == 1)
    r["refute"]["j"] = 0
elif kind == "swap-table-digests":
    q = st["query"]
    q[0]["table_digest"], q[1]["table_digest"] = q[1]["table_digest"], q[0]["table_digest"]
elif kind == "drop-record":
    recs.pop(0)
    st["n"] -= 1
else:
    sys.exit(f"unknown kind {kind}")
json.dump(c, open(sys.argv[3], "w"))
