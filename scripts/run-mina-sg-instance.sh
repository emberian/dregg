#!/usr/bin/env bash
# run-mina-sg-instance.sh — build the rung-5h INSTANCE differential on demand.
#
# WHY THIS SCRIPT EXISTS. The `MinaWrapSg*` family proves `sg == ⟨s, srs.g⟩` over all 32,768 real
# generators for Mina devnet block 539508. It is a KAT about ONE BLOCK, and each chunk peaks near
# 75 GB elaborating. Rooted in `Dregg2.lean` it made `lake build Dregg2` impossible to finish —
# the root reached 10444/10448 and earlyoom SIGTERM'd a chunk at 1212 s (exit 143) — which meant
# `#floor_ratchet` could never return an unqualified verdict. So the family is allowlisted out of
# the root (see `scripts/lean-orphans-allow.txt`) and lives here instead.
#
# ⚠ These modules' `#assert_axioms` and `#guard`s run NOWHERE ELSE. If you change rung 5h, the
# extractor, or `srs.g`, RUN THIS — nothing else will catch you.
#
# The four `MinaWrapSgChunk*` modules (the kernel `decide` of the MSM in 32 slices) were
# retired 2026-11-06, see metatheory/docs/MINA-PICKLES-RESCUE.md; the native pin is `mina_sg_bench` and `Dregg2.Bridge.MinaWrapSgWeld`.
#
# Budget: expect tens of GB per chunk and a long wall time. Run it on a QUIET box, one chunk at a
# time, which is why the loop is serial rather than a single `lake build` of all of them.
set -euo pipefail
LANE="${1:?usage: run-mina-sg-instance.sh <hbox-lane>}"
MODS=(PastaIpaFold MinaWrapSrsG MinaWrapSgParts MinaWrapSgCore)
for m in "${MODS[@]}"; do
  echo "=== $m ==="
  scripts/hbuild "$LANE" "cd metatheory && lake build Dregg2.Circuit.Emit.$m"
done
echo "run-mina-sg-instance: all ${#MODS[@]} modules built."
