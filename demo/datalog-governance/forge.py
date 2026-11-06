#!/usr/bin/env python3
"""Make the falsifier certificates for the demo (each must be REFUSED by datalog-check).
Run with `python3 -I`; paths are arguments.

    python3 -I forge.py <program.json> <certificate.json> <out-dir>

  open-lower.json   stratum 0's trace without its prior_touch firings, stratum 1 then derives every
                    sub-agent edit as blind_edit and the statement claims that count: the lower
                    stratum is not closed (the StratifiedCert falsifier (c), on real data).
  wrong-count.json  the honest certificate claiming count + 1.
  dropped-fact.json the honest certificate with one reads(...) fact removed from the EDB and the
                    statement's root left as committed: the root no longer matches.
"""
import copy
import json
import os
import sys


def main():
    prog = json.load(open(sys.argv[1]))
    doc = json.load(open(sys.argv[2]))
    out = sys.argv[3]
    P = prog["preds"]
    rules = prog["program"]
    # 1. open lower stratum
    d = copy.deepcopy(doc)
    prior = {i for i, r in enumerate(rules) if r["head"]["pred"] == P["prior_touch"]}
    s0 = [[f for f in rd if f[0] not in prior] for rd in d["certificate"]["traces"][0]]
    d["certificate"]["traces"][0] = [rd for rd in s0 if rd]
    edits = [f for f in d["certificate"]["edb"] if f[0] == P["edits"]]
    tc = {f[1][0]: f[1] for f in d["certificate"]["edb"] if f[0] == P["tool_call"]}
    spawned = {f[1][0]: f[1] for f in d["certificate"]["edb"] if f[0] == P["spawned"]}
    blind_rule = next(i for i, r in enumerate(rules) if r["head"]["pred"] == P["blind_edit"])
    viol_rule = next(i for i, r in enumerate(rules) if r["head"]["pred"] == P["violation"]
                     and r["body"][0]["pos"]["pred"] == P["blind_edit"])
    r1, r2 = [], []
    for f in edits:
        w, p = f[1]
        _, a, t, s = tc[w]
        if a not in spawned:
            continue
        _, q, k = spawned[a]
        r1.append([blind_rule, [w, p, a, t, s, q, k]])
        r2.append([viol_rule, [w]])
    d["certificate"]["traces"][1] = [r1, r2]
    d["statement"]["count"] = len(r1)
    json.dump(d, open(os.path.join(out, "open-lower.json"), "w"))
    # 2. wrong count
    d = copy.deepcopy(doc)
    d["statement"]["count"] += 1
    json.dump(d, open(os.path.join(out, "wrong-count.json"), "w"))
    # 3. dropped EDB fact
    d = copy.deepcopy(doc)
    k = next(i for i, f in enumerate(d["certificate"]["edb"]) if f[0] == P["reads"])
    del d["certificate"]["edb"][k]
    json.dump(d, open(os.path.join(out, "dropped-fact.json"), "w"))
    print(f"forge: open-lower claims count {len(r1)} (the honest count is {doc['statement']['count']})")


if __name__ == "__main__":
    main()
