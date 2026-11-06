# VK-REGEN CONTROLS — superseded 2026-11-06

The acknowledgement ceremony this note described is gone. The `DREGG_VK_REGEN_ACK` /
`DREGG_VK_REGEN_ALLOW_DIRTY` environment gate, `--stamp-existing` and `--verify-provenance --strict`
were deleted from `scripts/emit_descriptors.py`. The decision and the evidence for it are in
`docs/automata/SUBSTRATE-DECISION.md` §9, row 4, including the codex round 3 amendments. The
previous text is in git history (`git log -- docs/VK-REGEN-CONTROLS.md`).

What replaced the ceremony is automatic and runs as scripts:

| control | where |
|---|---|
| The emit refuses (exit 3) when any file in the emitters' transitive Lean closure or the lake configuration is uncommitted, and with `--rev <sha>` it refuses unless the checkout is that commit. There is no override. | `scripts/emit_descriptors.py` (`require_committed_emit_source`, `require_checkout_at`) |
| Every byte-changing or stamp-short emission writes `circuit/descriptors/PROVENANCE.json` (tree hash, repo HEAD, toolchain, emitter list, `emitter_closure_clean`, per-file sha256) with no operator. | `install_and_stamp` |
| Committed bytes must match the committed stamp, the stamp must not record `source_dirty=true`, and it must be a Lean witness (`mode` = `emit`). | `python3 scripts/emit_descriptors.py --verify-provenance --rev HEAD` (`local-gates.sh` row `provenance`; red-proof `provenance-red`) |
| The by-name routing table, the checked-in `by-name/` set and the stamp must cover each other, and every committed reference must have a committed target. | `--verify-by-name-routing`, run by `scripts/git-hooks/pre-commit` when `metatheory/EmitByName.lean` or `circuit/descriptors/by-name/` is staged |
| The checked-in bytes must be what Lean emits at that revision. | `scripts/check-descriptor-drift.sh --rev HEAD` |

The canonical emit host is a clean clone at a committed revision: `docs/automata/BUILD.md`,
section "Emit and stamp (C2)".
