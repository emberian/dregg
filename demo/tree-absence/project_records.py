#!/usr/bin/env python3
"""Project a redacted `cv export` forest onto one JSON record per tool call.  Run with `python3 -I`.

    python3 -I project_records.py <export-dir> <out records.jsonl> <out sources.json>

<export-dir> holds root.json, agents.txt (sub-agent ids, one per line, in the order demo (b)
used: sorted) and sub/agent-<id>.json.  Order: the root's tool calls in transcript order, then
each sub-agent's in agents.txt order.  Each record is {"name": <tool name>, "input": <input>},
serialized compactly with raw UTF-8.  Loading refuses duplicate keys anywhere in an export, and
numbers are kept as their exact source tokens (no float round trip): the record text carries the
original numeric spelling to the Rust/Lean projection.  The exports are DATA: no field is
executed or interpreted.  sources.json records the sha256 of every export and the line
range each agent's records occupy.
"""
import hashlib
import json
import os
import sys


class DuplicateKey(ValueError):
    pass


class Num(str):
    """A JSON number, kept as its source token."""


def no_dups(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            raise DuplicateKey(k)
        d[k] = v
    return d


def load(raw):
    return json.loads(raw, object_pairs_hook=no_dups, parse_float=Num, parse_int=Num,
                      parse_constant=lambda c: (_ for _ in ()).throw(ValueError(f"constant {c}")))


def dump(v, ascii_only):
    if isinstance(v, Num):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v, ensure_ascii=ascii_only)
    if v is None or isinstance(v, bool):
        return json.dumps(v)
    if isinstance(v, list):
        return "[" + ",".join(dump(x, ascii_only) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ",".join(json.dumps(k, ensure_ascii=ascii_only) + ":" + dump(x, ascii_only)
                              for k, x in v.items()) + "}"
    raise TypeError(type(v))


def numbers(v):
    """(all numbers, non-integer numbers) in a value."""
    if isinstance(v, Num):
        return 1, int(any(c in v for c in ".eE"))
    if isinstance(v, list):
        xs = [numbers(x) for x in v]
    elif isinstance(v, dict):
        xs = [numbers(x) for x in v.values()]
    else:
        return 0, 0
    return sum(a for a, _ in xs), sum(b for _, b in xs)


def tool_uses(export):
    for m in export["messages"]:
        for p in m.get("content") or []:
            if isinstance(p, dict) and p.get("type") == "tool_use":
                yield p.get("name") or "", p.get("input")


def main():
    exp_dir, out_path, src_path = sys.argv[1], sys.argv[2], sys.argv[3]
    agents = [a.strip() for a in open(os.path.join(exp_dir, "agents.txt")) if a.strip()]
    files = [("root", os.path.join(exp_dir, "root.json"))]
    files += [(a, os.path.join(exp_dir, "sub", f"agent-{a}.json")) for a in agents]
    sources, line, ascii_fallback, nums, nonint = [], 0, 0, 0, 0
    with open(out_path, "wb") as out:
        for agent, path in files:
            raw = open(path, "rb").read()
            first = line
            for name, inp in tool_uses(load(raw)):
                rec = {"name": name, "input": inp}
                a, b = numbers(inp)
                nums, nonint = nums + a, nonint + b
                try:
                    text = dump(rec, False).encode("utf-8")
                except UnicodeEncodeError:
                    # a lone surrogate in the export: keep it escaped (the projection will refuse it)
                    text = dump(rec, True).encode("ascii")
                    ascii_fallback += 1
                out.write(text + b"\n")
                line += 1
            sources.append({"agent": agent, "export_sha256": hashlib.sha256(raw).hexdigest(),
                            "records": [first, line]})
    doc = {"session": "e3ba49ed-a526-4ecd-8807-58b73757aaca",
           "exported_with": "cv export <id> --format json --redact --frozen (root and each agent-<id>)",
           "records": line, "lone_surrogate_records": ascii_fallback,
           "duplicate_keys_refused": 0,  # load() raises on the first one, so a finished run saw none
           "numbers_in_inputs": nums, "non_integer_numbers_in_inputs": nonint, "sources": sources}
    with open(src_path, "w") as f:
        json.dump(doc, f, indent=1)
        f.write("\n")
    print(f"{line} records from {len(files)} transcripts ({ascii_fallback} kept ASCII-escaped, "
          f"{nums} numbers, {nonint} non-integer)")


if __name__ == "__main__":
    main()
