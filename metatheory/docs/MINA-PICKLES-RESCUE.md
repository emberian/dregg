# Mina / Pickles / Kimchi rescue: census, measured elaboration cost, decisions

Living document of the rescue lane (2026-11-06). Trigger: the automata deputy's stamp chain found
single Mina modules that need more than 12 GB to elaborate (`docs/automata/BUILD.md` at the repo
root, "hbox memory for the emitter closure").

## How things are measured

dregg-build2 (`ssh bb2`, user `build`), clone at `/home/build/mina-rescue/bs` made from
`git archive origin/main metatheory` (mathlib `1c2b90b1` packages copied from the deputy's clone,
no hard links). Every number is `/usr/bin/time -v` "Maximum resident set size" and wall time of one
`lake env lean <file>` (deps already built), run under `swarm-build` with `SWARM_MEM_MAX=32G`/`40G`.
Bisection is by prefix cuts of the module (the file up to a section header plus `end <ns>`), so a
section's cost is the difference between two cuts. `trace.profiler` was tried once and is not usable
on these files: on `MinaBodyPreimageBitsAir` the profile text reached 7.5 GB and the run was killed
at the 40 GB cap; it did name the first heavy declaration (below) before dying.

Imports alone cost 3.6 GB (Mathlib plus the emitter closure), so "under 4 GB" is not reachable
for any module in this cone without changing its imports; the target used is "within ~2 GB of the
import floor and under about a minute".

## Census (first pass)

179 modules match `Mina*`, `Pickles*`, `Kimchi*` under `metatheory/Dregg2/` (`Bridge/`,
`Circuit/Emit/`, and `MinaBridgeGuards`, `PicklesSynthesis`). Roughly 66k of their lines are the two
SRS literal files (`MinaStepSrsG` 65,688 lines, `MinaWrapSrsG` 32,838). Consumers outside Lean:
descriptors emitted through `EmitByName.lean` into `circuit/descriptors/by-name/`, read by
`circuit-prove/src/mina_body_preimage_adapter.rs`, `turn/src/executor/mina_head_verifier.rs`
(shipped executor code) and tests named `mina_*` under `circuit/tests/`. The fixtures under
`metatheory/fixtures/kimchi-extractors` and the `pickles-*-harness` fixture directories are the extractors and harnesses the gold values
came from; they stay.

Nothing in the two modules measured so far is a retirement candidate: both emit descriptors that
shipped Rust code includes by path. The per-module table (lines, emitted descriptors, Lean importers,
Rust consumers split src/test, last touched) will be added here when the census script finishes.

## Measured: the two modules over 12 GB

| module | before | after | cause | decision |
|---|---|---|---|---|
| `MinaBodyPreimageBitsAir` | 25.9 GB, 6:16 | 5.6 GB, 0:50 | `bodyBitsAir_pinsTied := by decide`: the O(pins x legs) tie scan, 1,518 pins over 4,239 legs, evaluated in the elaborator's `whnf` (213 s of profile). Second: seven `rfl` checks over the assembled leg list and emitted descriptor, also evaluated in the elaborator (3.1 GB). | rescued, `7c90a9b60` |
| `MinaWrapCommitStages` | 15.7 GB, 5:22 | (in progress) | §6b/§6c `decide`s that recompute 41 + 47 + 8 full 255-bit scalar multiplications and modular inverses over block 539508's real points, once per theorem. Cuts: through §6a 3.7 GB / 5 s; through §6b 8.2 GB / 2:00; through §6c 15.2 GB / 4:48. | rescue in progress |

### `MinaBodyPreimageBitsAir` bisection

| prefix | peak RSS | wall |
|---|---|---|
| imports only | 3.6 GB | 0:03 |
| original file | 25.9 GB | 6:16 |
| new `pinsTied` proof, through §3 | 8.5 GB | 0:24 |
| new `pinsTied`, whole file | 8.7 GB | 0:56 |
| + `decide +kernel` for the seven `rfl` checks, through `pinsTied` | 4.4 GB | 0:32 |
| + same, whole file (landed) | 5.6 GB | 0:50 |

What changed: proofs only. `bodyBitsAir_pinsTied` now exhibits each pin's reader
(`fieldLimbsLeg f` for a field pin, `limbLeg e k` for a limb pin) from the index lists and scans
nothing; the `rfl` checks are `decide +kernel` (same proposition, kernel-only evaluation, no
`Lean.ofReduceBool`). No statement or definition changed. The emitted
`circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json` is byte-identical (emitted from
the rebuilt olean and compared with `cmp`). Downstream `MinaBodyPreimageSeams` rebuilt green
(4.2 GB). A cross-model review (codex, gpt-6-astra, read-only) found no change of statement,
definition, axiom set or descriptor.

## Diagnosis pattern

Both heavy modules share one shape: a `decide` or `rfl` over a large concrete object that Lean
evaluates in the elaborator (`Meta.whnf`/`isDefEq`), which is far hungrier than the kernel. The
rescues, in order of preference:

1. Prove the fact structurally when it holds by construction (the tie verdict).
2. Where evaluation is the honest proof, let the kernel do it: `decide +kernel`.
3. Where several theorems re-evaluate the same expensive value, evaluate it once into a named
   equation with a literal and rewrite the others with it.
