#!/usr/bin/env python3
"""The honest prover: semi-naive stratified evaluation that LOGS its firings, then the checker input.
Run with `python3 -I`; paths are arguments.

    python3 -I prove.py <program.json> <edb.json> <out certificate.json>

Per stratum, a firing is logged only when it adds a new fact; its positive atoms are in the
database at that moment and its negated atoms are absent from the database the lower strata left
(the frozen lower model) — exactly what `StratifiedCert.replayS` replays.  The statement's root is
the MMR root of the EDB computed HERE, independently of the Lean checker (Python `hashlib` SHAKE256,
the same framed encoding as `DatalogCheck.lean`); the checker recomputes it and must agree.
"""
import hashlib
import json
import sys
from collections import defaultdict


# ---- the hash and the MMR root (mirrors DatalogCheck.leafHash and MMR.mroot) ----
def _nb(n):
    return n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""


def enc(xs):
    out = [len(xs).to_bytes(8, "big")]
    for x in xs:
        m = _nb(abs(x))
        out.append(bytes([1 if x < 0 else 0]) + len(m).to_bytes(4, "big") + m)
    return b"".join(out)


def leaf_hash(xs):
    return int.from_bytes(hashlib.shake_256(b"dregg.datalog.mmr.v1\x00" + enc(xs)).digest(32), "big")


def flatten(facts):
    out = []
    for p, args in facts:
        out += [p, len(args)] + list(args)
    return out


def mroot(leaves):
    peaks = []  # youngest first: (height, hash)
    for v in leaves:
        t = (0, leaf_hash([v]))
        while peaks and peaks[0][0] == t[0]:
            s = peaks.pop(0)
            t = (t[0] + 1, leaf_hash([s[1], t[1]]))
        peaks.insert(0, t)
    acc = leaf_hash([])
    for h, hv in reversed(peaks):
        acc = leaf_hash([hv, acc])
    return acc


def program_digest(prog, strata):
    def term(t):
        return [0, t["var"]] if "var" in t else [1, t["const"]]

    def atom(a):
        return [a["pred"], len(a["args"])] + [x for t in a["args"] for x in term(t)]

    out = [len(prog)]
    for r in prog:
        out += atom(r["head"]) + [len(r["body"])]
        for l in r["body"]:
            out += ([0] + atom(l["pos"])) if "pos" in l else ([1] + atom(l["neg"]))
    out += [len(strata)]
    for S in strata:
        out += [len(S)] + list(S)
    return int.from_bytes(hashlib.shake_256(b"dregg.datalog.program.v1\x00" + enc(out)).digest(32), "big")


# ---- evaluation ----
def var_bound(r):
    vs = [t["var"] for a in [r["head"]] + [l.get("pos") or l.get("neg") for l in r["body"]]
          for t in a["args"] if "var" in t]
    return max(vs) + 1 if vs else 0


class DB:
    def __init__(self, facts):
        self.order, self.set = [], set()
        self.by_pred = defaultdict(list)
        self.by_arg = defaultdict(list)
        for f in facts:
            self.add(f)

    def add(self, f):
        if f in self.set:
            return False
        self.set.add(f)
        self.order.append(f)
        self.by_pred[f[0]].append(f)
        for i, v in enumerate(f[1]):
            self.by_arg[(f[0], i, v)].append(f)
        return True


def candidates(db, atom, s, restrict=None):
    pool = None
    for i, t in enumerate(atom["args"]):
        v = t.get("const") if "const" in t else s.get(t["var"])
        if v is not None:
            pool = db.by_arg.get((atom["pred"], i, v), [])
            break
    if pool is None:
        pool = db.by_pred.get(atom["pred"], [])
    if restrict is not None:
        pool = [f for f in pool if f in restrict]
    return pool


def match(atom, f, s):
    if f[0] != atom["pred"] or len(f[1]) != len(atom["args"]):
        return None
    s2 = dict(s)
    for t, v in zip(atom["args"], f[1]):
        if "const" in t:
            if t["const"] != v:
                return None
        elif s2.setdefault(t["var"], v) != v:
            return None
    return s2


def ground(atom, s):
    return (atom["pred"], tuple(t["const"] if "const" in t else s[t["var"]] for t in atom["args"]))


def solutions(db, pos, s, delta_at=None, delta=None):
    if not pos:
        yield s
        return
    j = len(pos) - 1
    first = pos[0]
    k = 0 if delta_at is None else delta_at
    # evaluate atoms in order; the delta-restricted one uses `delta`
    def rec(i, s):
        if i == len(pos):
            yield s
            return
        restrict = delta if i == delta_at else None
        for f in candidates(db, pos[i], s, restrict):
            s2 = match(pos[i], f, s)
            if s2 is not None:
                yield from rec(i + 1, s2)
    yield from rec(0, s)


def main():
    prog_doc = json.load(open(sys.argv[1]))
    edb = [(p, tuple(a)) for p, a in json.load(open(sys.argv[2]))["facts"]]
    prog, strata = prog_doc["program"], prog_doc["strata"]
    db = DB(edb)
    traces, stats = [], []
    for S in strata:
        lower = set(db.set)
        heads = {prog[i]["head"]["pred"] for i in S}
        rounds, delta, first = [], None, True
        while True:
            rnd, new = [], set()
            for i in S:
                r = prog[i]
                pos = [l["pos"] for l in r["body"] if "pos" in l]
                negs = [l["neg"] for l in r["body"] if "neg" in l]
                vb = var_bound(r)
                if first:
                    sites = [None]
                else:
                    sites = [j for j, a in enumerate(pos) if a["pred"] in heads]
                for site in sites:
                    for s in list(solutions(db, pos, {}, site, delta)):
                        if any(ground(a, s) in lower for a in negs):
                            continue
                        h = ground(r["head"], s)
                        if h in db.set:
                            continue
                        subst = [s[v] for v in range(vb)]
                        db.add(h)
                        new.add(h)
                        rnd.append([i, subst])
            first = False
            if not rnd:
                break
            rounds.append(rnd)
            delta = new
        traces.append(rounds)
        stats.append((len(rounds), sum(len(r) for r in rounds)))
    pred = prog_doc["counted_pred"]
    count = sum(1 for f in db.order if f[0] == pred)
    root = mroot(flatten(edb))
    big = lambda x: x if abs(x) < 2 ** 53 else hex(x) if x >= 0 else "-" + hex(-x)
    doc = {
        "statement": {"program": prog, "strata": strata, "root": hex(root), "pred": pred, "count": count},
        "certificate": {
            "edb": [[p, [big(x) for x in a]] for p, a in edb],
            "traces": traces,
        },
    }
    json.dump(doc, open(sys.argv[3], "w"))
    open(sys.argv[3], "a").write("\n")
    print(f"prove: {len(edb)} EDB facts -> {len(db.order)} facts; per stratum (rounds, firings) {stats}; "
          f"count(pred {pred}) = {count}")
    print(f"prove: program digest 0x{program_digest(prog, strata):064x}")
    print(f"prove: EDB root      0x{root:064x}")
    viol = [f for f in db.order if f[0] == pred]
    json.dump({"violations": [list(f[1]) for f in viol]}, open(sys.argv[3] + ".violations", "w"))


if __name__ == "__main__":
    main()
