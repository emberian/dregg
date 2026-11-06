#!/usr/bin/env python3
"""Gather the committable numbers of a run (digests, roots, counts, timings; no tool inputs)
into summary.json.  Run with python3 -I:  summarize.py <corpus-dir> <out summary.json> <record index> <field cert B> <field cert C>"""
import json
import os
import sys

d, out, rec_i, fcert, fcert_c = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
J = lambda f: json.load(open(os.path.join(d, f)))
src = J("sources.json")
real, full, flat = J("produce-real.json"), J("produce-full.json"), J("flat-scan.json")
flat_real = J("flat-scan-real.json")
ireal, ifull = J("produce-invocation-real.json"), J("produce-invocation-full.json")
fc = json.load(open(fcert))["statement"]
fcc = json.load(open(fcert_c))["statement"]
nreal, nfull = J("produce-invocation-nobacktick-real.json"), J("produce-invocation-nobacktick-full.json")
n_real = src["records"]
names, rec_names = {}, []
for line in open(os.path.join(d, "records-real.jsonl"), "rb"):
    name = json.loads(line)["name"]
    rec_names.append(name)
    names[name] = names.get(name, 0) + 1
flat_real_by_tool = {}
for i in flat_real["hits"]:
    flat_real_by_tool[rec_names[i]] = flat_real_by_tool.get(rec_names[i], 0) + 1


def work(tag):
    """The checker's own counters: the opening tally and every keccak_f / MMR count it prints."""
    lines = open(os.path.join(d, f"verify-{tag}.out")).read().splitlines()
    body = json.loads("\n".join(lines[:-1]))
    w = {k: v for k, v in body.items() if k.startswith(("keccak_f", "mmr_hashes", "records_"))}
    if "work" in body:
        w["openings"] = body["work"]
    return w


KEYS = ("n", "count", "mmr_root", "refuted_at_conjunct", "matching_records")
verify = {}
for line in open(os.path.join(d, "verify.log")):
    tag, code, verdict, secs = line.split()
    verify[tag] = {"exit": int(code.split("=")[1]), "verdict": verdict, "wall_s": float(secs[:-1])}
for tag in verify:
    if verify[tag]["exit"] == 0:
        verify[tag]["work"] = work(tag)

doc = {
    "session": src["session"],
    "exported_with": src["exported_with"],
    "export_sha256": {s["agent"]: s["export_sha256"] for s in src["sources"]},
    "records_real": n_real,
    "projection_input": {k: src[k] for k in ("duplicate_keys_refused", "numbers_in_inputs",
                                             "non_integer_numbers_in_inputs", "lone_surrogate_records")},
    "records_by_tool": dict(sorted(names.items(), key=lambda kv: -kv[1])),
    "controls": ["Bash command \\u0070kill -f node (escaped)", "Bash command pkill -f node (plain)"],
    "mention": {
        "query": "name = `Bash` AND input.command contains `pkill -f` (query.json)",
        "real": {k: real[k] for k in KEYS}, "full": {k: full[k] for k in KEYS},
        "flat_scan": {
            "word": flat["word"],
            "real": {"lines": n_real, "lines_hit": flat_real["lines_hit"],
                     "hits_by_tool": dict(sorted(flat_real_by_tool.items(), key=lambda kv: -kv[1])),
                     "non_bash_hits": flat_real["lines_hit"] - flat_real_by_tool.get("Bash", 0)},
            "with_controls": {"lines": n_real + 2, "lines_hit": flat["lines_hit"],
                              "escaped_control_hit": n_real in flat["hits"],
                              "plain_control_hit": n_real + 1 in flat["hits"]},
        },
    },
    "invocation": {
        "query": "name = `Bash` AND input.command has `pkill -f` at command position (query-invocation.json, query-invocation.policy)",
        "real": {k: ireal[k] for k in KEYS}, "full": {k: ifull[k] for k in KEYS},
        "differential": J("diff-invocation.json"),
    },
    "invocation_nobacktick": {
        "query": "(B) with the backtick removed from BOUNDARY: the absence receipt (query-invocation-nobacktick.json)",
        "scope": "(B)'s limits plus: `pkill -f x` inside backtick command substitution is missed",
        "real": {k: nreal[k] for k in KEYS}, "full": {k: nfull[k] for k in KEYS},
        "differential": J("diff-invocation-nobacktick.json"),
    },
    "single_record_c": {"record": rec_i, "certificate": os.path.basename(fcert_c), "kind": fcc["kind"],
                        "path": "/input/command", "verdict": fcc["verdict"], "tree_root": fcc["tree_root"],
                        "table_digest": fcc["table_digest"]},
    "single_record": {"record": rec_i, "certificate": os.path.basename(fcert), "kind": fc["kind"],
                      "path": "/input/command", "verdict": fc["verdict"], "tree_root": fc["tree_root"],
                      "table_digest": fc["table_digest"]},
    "conformance": {"edges": J("conform-edges.json"), "records": J("conform-records.json")},
    "verify": verify,
}
with open(out, "w") as f:
    json.dump(doc, f, indent=1)
    f.write("\n")
