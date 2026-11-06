#!/usr/bin/env python3
"""check-mathlib-intact.py — the shared Mathlib tree is present, pinned, and populated.

⚑ WHY THIS EXISTS (2026-08-09, twice in one evening). `~/src/mathlib4` was wiped
twice on this box.  `metatheory/.lake/packages/mathlib` is a SYMLINK into it, so a
wipe does not present as "a dependency is missing" — every mathlib-importing build
dies on

    object file '.../Mathlib/Algebra/Ring/Defs.olean' does not exist

which reads exactly like a proof failure.  A lane spent real time believing its own
module was broken.  Both restores cost ~10 min (`git clone --filter=blob:none` at the
pinned rev + `lake exe cache get`, 8105 oleans).  This gate turns a bogus proof error
into a one-line diagnosis.

⚠ THE KNOWN DESTROYER, and why the tree's own scripts are NOT it.  `rsync --delete`
ate this exact path on 2026-07-28 (`scripts/pbuild:636-648` records it: emptied
`metatheory/.lake/packages/mathlib`, removed `.lake/build`, 223 olean dirs -> 0).
`pbuild` was hardened afterwards with explicit `P` protect rules and is now the only
real `rsync --delete` in `scripts/` — the other matches are comments and a self-test
that simulates deletion with `rm -f`.  `reclaim-space.sh` is clean too: its `find`
has no `-L`, so it does not follow the symlink, and `rm -rf` on a symlink takes the
LINK, not the target.  MEASURED 2026-08-10.  So the destroyer is outside this repo:
an older `pbuild` on another host, another agent session, or a `lake` invocation that
takes `packages/`.  ⚑ This gate does not identify the culprit.  It makes the DAMAGE
legible at the moment it matters, which is the part that kept costing hours.

⚠ AND IT IS NOT "MAKE IT READ-ONLY".  Lake writes into this tree by design:
`lake exe cache get` populates it, an imported module the cache does not cover is
BUILT there, and a rev bump adds oleans.  A read-only bind would break the restore
path and every on-demand build.  The invariant is not immutability — it is that
LAKE writes to it and nothing else deletes through it.

⚑ MTIME PROVES NOTHING HERE, so this gate does not look at it.  `lake exe cache get`
unpacks with the cache's ORIGINAL timestamps, so a tree restored ten minutes ago
reports oleans "written" weeks back.  I read that as "nothing has touched it in three
days" before checking `.git`'s birth time and finding the clone was hours old.
Count and pin are the honest signals; age is not.

Exit 0 = intact.  Exit 1 = a finding, with what to run.
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

# The pinned rev lives in the lakefile's manifest; this is the fallback identity for
# the message only.  A DIFFERENT rev is not a failure here — a MISSING tree is.
EXPECTED_REV_PREFIX = "56a00585"
TOOLCHAIN = "v4.35.0"

# 8105 oleans under .lake/build/lib at the pinned rev (measured 2026-08-10).  The band
# is wide on purpose: a rev bump moves this legitimately, and a gate that fires on
# ordinary drift is a gate people stop reading.  A wipe lands at ~0, which is what we
# are actually catching.
MIN_OLEANS = 4000

REPO = Path(__file__).resolve().parent.parent
LINK = REPO / "metatheory" / ".lake" / "packages" / "mathlib"

RESTORE = f"""  git clone --filter=blob:none https://github.com/leanprover-community/mathlib4 ~/src/mathlib4
  cd ~/src/mathlib4 && git checkout {EXPECTED_REV_PREFIX} && elan override set {TOOLCHAIN}
  lake exe cache get          # ~10 min, ~8100 oleans"""


def fail(msg: str, *, restore: bool = False) -> int:
    print(f"check-mathlib-intact: FAIL — {msg}")
    if restore:
        print("\n  restore:\n" + RESTORE)
    return 1


def main() -> int:
    # The symlink is the thing every build actually resolves through.  Check it first:
    # if it is dangling, the error a lane sees is the misleading one this gate exists for.
    if not LINK.is_symlink() and not LINK.exists():
        return fail(
            f"{LINK} is absent — every mathlib-importing build will die on a missing\n"
            "  olean that LOOKS like a proof failure.",
            restore=True,
        )

    target = LINK.resolve()
    if not target.exists():
        return fail(
            f"{LINK} is a DANGLING symlink -> {target}\n"
            "  ⚑ This is the 2026-08-09 wipe signature.  Builds will report a missing\n"
            "  .olean, which reads as a broken proof.  It is not.",
            restore=True,
        )

    if not (target / ".git").exists():
        return fail(f"{target} exists but is not a git checkout", restore=True)

    rev = subprocess.run(
        ["git", "-C", str(target), "rev-parse", "--short=10", "HEAD"],
        capture_output=True, text=True,
    ).stdout.strip()

    oleans = sum(1 for _ in (target / ".lake" / "build" / "lib").rglob("*.olean")) \
        if (target / ".lake" / "build" / "lib").is_dir() else 0

    if oleans < MIN_OLEANS:
        return fail(
            f"{target} @ {rev or '?'} holds only {oleans} oleans (expected >= {MIN_OLEANS}).\n"
            "  ⚑ The tree is present but UNPOPULATED — `lake exe cache get` was never run,\n"
            "  or something deleted through the symlink.  Builds will fail on missing\n"
            "  oleans and the errors will look like proof failures.",
            restore=True,
        )

    note = "" if rev.startswith(EXPECTED_REV_PREFIX) else \
        f"  (note: rev {rev} != pinned {EXPECTED_REV_PREFIX}; not a failure, but if a\n" \
        f"   build reports an absent olean, a rev bump needs `lake exe cache get`.)\n"
    print(f"check-mathlib-intact: OK — {target} @ {rev}, {oleans} oleans")
    if note:
        print(note, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
