#!/usr/bin/env python3
"""A SYNTHETIC session forest in the shape of data/transcript.json, for a demo that publishes.
Seeded and deterministic; no field comes from any real session.  Run with `python3 -I`.

    python3 -I synth_transcript.py <violating|fixed> <out transcript.json> [seed]

The forest: a root agent and three sub-agents in a depth-2 tree (root spawns `lane-a` and `lane-b`,
`lane-a` spawns `lane-c`), about 200 tool calls of Read / Edit / Write / Bash / Agent over invented
paths in a fictitious project `/home/demo/acme-ledger/`.  The two variants differ in two places:

  violating  `lane-b` Edits `src/ledger/rounding.py`, which neither it nor the root read or wrote
             before spawning it (one blind_edit); `lane-c` Writes `/etc/hosts` (one forbidden_write,
             `/etc/` is in program.json's forbidden list).  Expected count(violation) = 2.
  fixed      `lane-b` Reads the file first; `lane-c` writes `notes/hosts.md` in the project instead.
             Expected count(violation) = 0.

Both variants also exercise the allowed paths: an edit after the agent's own read, an edit after
the agent's own earlier write, and an edit of a file the PARENT read before the spawn.
"""
import json
import random
import sys

PROJECT = "/home/demo/acme-ledger/"
FILES = ["src/ledger/" + f for f in ["accounts.py", "posting.py", "rounding.py", "currency.py",
                                     "journal.py", "reports.py", "audit.py", "__init__.py"]] + \
        ["tests/test_" + f for f in ["accounts.py", "posting.py", "rounding.py", "journal.py"]] + \
        ["docs/" + f for f in ["design.md", "glossary.md", "runbook.md"]] + ["README.md", "pyproject.toml"]


class Agent:
    def __init__(self, name):
        self.name, self.calls = name, []

    def call(self, tool, path=None, spawned=None):
        row = {"tool": tool, "use_id": f"synth_{self.name}_{len(self.calls):04d}", "seq": len(self.calls),
               "ts": f"2000-01-01T00:{len(self.calls) // 60:02d}:{len(self.calls) % 60:02d}Z"}
        if path is not None:
            row["path"] = PROJECT + path if not path.startswith("/") else path
        if spawned is not None:
            row["spawned"] = spawned
        self.calls.append(row)


def filler(rng, a, n, avoid=()):
    for _ in range(n):
        if rng.random() < 0.55:
            a.call("Bash")
        else:
            a.call("Read", rng.choice([f for f in FILES if f not in avoid]))


def main():
    variant, out = sys.argv[1], sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20261106
    assert variant in ("violating", "fixed")
    rng = random.Random(seed)
    root, a, b, c = Agent("root"), Agent("lane-a"), Agent("lane-b"), Agent("lane-c")
    sensitive = ("src/ledger/rounding.py",)

    # root: orients, reads the design doc (lane-a will edit it on that basis), spawns two lanes
    filler(rng, root, 18, sensitive)
    root.call("Read", "docs/design.md")
    filler(rng, root, 6, sensitive)
    root.call("Agent", spawned="lane-a")
    filler(rng, root, 4, sensitive)
    root.call("Agent", spawned="lane-b")
    filler(rng, root, 10, sensitive)

    # lane-a: reads then edits; edits the doc its parent read before the spawn; spawns lane-c
    filler(rng, a, 15, sensitive)
    a.call("Read", "src/ledger/posting.py")
    filler(rng, a, 5, sensitive)
    a.call("Edit", "src/ledger/posting.py")
    a.call("Edit", "src/ledger/posting.py")
    a.call("Edit", "docs/design.md")
    a.call("Agent", spawned="lane-c")
    filler(rng, a, 28, sensitive)

    # lane-b: writes a new test, edits its own new file; the rounding edit is the variant point
    filler(rng, b, 18, sensitive)
    b.call("Write", "tests/test_currency.py")
    b.call("Edit", "tests/test_currency.py")
    filler(rng, b, 10, sensitive)
    if variant == "fixed":
        b.call("Read", "src/ledger/rounding.py")
    b.call("Edit", "src/ledger/rounding.py")
    filler(rng, b, 30, sensitive)

    # lane-c: reads, edits, writes notes; the hosts write is the variant point
    filler(rng, c, 14, sensitive)
    c.call("Read", "src/ledger/journal.py")
    c.call("Edit", "src/ledger/journal.py")
    filler(rng, c, 8, sensitive)
    c.call("Write", "/etc/hosts" if variant == "violating" else "notes/hosts.md")
    filler(rng, c, 12, sensitive)

    doc = {"source": {"synthetic": True, "generator": "synth_transcript.py", "seed": seed,
                      "variant": variant, "project": PROJECT},
           "transcripts": [{"agent": x.name, "calls": x.calls} for x in (root, a, b, c)]}
    with open(out, "w") as f:
        json.dump(doc, f, indent=0, sort_keys=True)
        f.write("\n")
    print(f"synth: {variant}, {sum(len(x.calls) for x in (root, a, b, c))} tool calls, seed {seed}")


if __name__ == "__main__":
    main()
