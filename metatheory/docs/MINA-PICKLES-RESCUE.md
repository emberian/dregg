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
shipped Rust code includes by path. The full table is in the appendix at the end.

How to read the census columns: `E.` is `Dregg2.Circuit.Emit.`, `B.` is `Dregg2.Bridge.`. "In default
build" means reachable by imports from the lakefile's `defaultTargets` roots (166 of 179). "Rust
consumers" lists crates whose sources include one of the module's `EmitByName` descriptor files
(`src:` or `test:`); "named in" means the module name appears in that crate's comments or strings
only. 17 modules emit through `EmitByName.lean`; the rest feed the dedicated emitters
(`MinaBodyBitsEmit.lean`, `EmitCommitStages.lean`, `MinaChainEmit.lean` and the others at the
`metatheory/` root) or are imported on the path to them. Taken 2026-11-06 from the working tree.

## Measured: the two modules over 12 GB

| module | before | after | cause | decision |
|---|---|---|---|---|
| `MinaBodyPreimageBitsAir` | 25.9 GB, 6:16 | 5.6 GB, 0:50 | `bodyBitsAir_pinsTied := by decide`: the O(pins x legs) tie scan, 1,518 pins over 4,239 legs, evaluated in the elaborator's `whnf` (213 s of profile). Second: seven `rfl` checks over the assembled leg list and emitted descriptor, also evaluated in the elaborator (3.1 GB). | rescued, `7c90a9b60` |
| `MinaWrapCommitStages` | 15.7 GB, 5:22 (iteration lane cold profile: 17.3 GiB) | 9.4 GB, 1:53 | Six theorems about `PUBLIC_TERMS_NOMINAL` each re-ran the forty 255-bit scalar multiplications behind it inside their own `decide`. Cuts before: through §6a 3.7 GB; §6b 8.2 GB; §6c 15.2 GB. After: §6b 7.0 GB; §6c 7.9 GB; §8c's ladder tie verdict adds the last 1.5 GB. | rescued, `e4919780a` |

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

### `MinaWrapCommitStages` fix

`PUBLIC_TERMS_NOMINAL_VALUE` is the 41-point list written out (values from `#eval`), and
`PUBLIC_TERMS_NOMINAL_eq_value : PUBLIC_TERMS_NOMINAL = PUBLIC_TERMS_NOMINAL_VALUE` is checked once
by `decide +kernel`. The six theorems rewrite with it and decide on the literal. Every other
`decide` in the module is `decide +kernel`. The descriptors are built from the unchanged
definitions; all six (`mina-commit-pub`, `-f`, `-ft`, `-agg`, `-ladder`, `-xi`) are byte-identical
to `circuit/descriptors/by-name`. Not done: the 47-term `XI_TERMS` fold and the §8c ladder still
cost about 2 GB above the floor; splitting them per term would bring the module near 6 GB.

## Compiled evaluation (ember's policy, 2026-11-06)

Ember: "we DO trust the lean system ... this present hybrid is the worst of both tradeoffs." Facts
about concrete data (block 539508's values, leg lists, descriptor counts, scalar multiplications)
are checked by compiled evaluation, `native_decide`, pinned `#assert_compiled` (they rest on
`Lean.ofReduceBool`); general theorems stay kernel-proved and `#assert_axioms`-clean. Applied per
module, one check after each fix (dregg-build2, deps warm, import floor 3.6 GB):

- A theorem is switched only if it is closed (no hypotheses), its proof is a `decide`/`rfl`
  evaluation, and no other declaration cites it; cited ones were switched only where the citing
  proofs are themselves about concrete data, and then the axiom checks moved their pins. The
  converter used is the lane's scratch `nativize.py`; every pin change was confirmed by the
  `#assert_*` commands in the module, not by hand.
- A descriptor whose `TiedAir` verdicts are compiled carries those proofs in its value, so its
  shape theorems (width, PI count) and its `CertifiedRefines` certificate are pinned
  `#assert_compiled` as well (`MinaWrapOpeningSched`). Where a module's every theorem is compiled,
  the namespace pin (which refuses to pass vacuously) is replaced by a comment
  (`MinaWrapAggregationGate`, `MinaWrapGroupGate`).
- Evaluation is interpreted (the lib has no `precompileModules`), so memory falls to the floor but
  wall time does not always fall: `MinaFinalizeScalarsWeld` takes 8 minutes at 3.7 GB.

## Landed (for the stamp rerun; the Codex deputy sequences it)

| SHA | module | after (peak, wall) | note |
|---|---|---|---|
| `7c90a9b60`, `5d4edcf75` | `MinaBodyPreimageBitsAir` | 4.4 GB, 0:08 (was 25.9 GB, 6:16) | structural `pinsTied`; counts compiled; descriptor bytes identical |
| `e4919780a`, `e601f3b13` | `MinaWrapCommitStages` | 3.7 GB, 0:11 (was 15.7 GB, 5:22) | structural ladder tie; 26 block facts compiled; six descriptors identical |
| `5b89f003b`, `3b93ccac4` | `MinaWrapOpeningGate` | 6.4 GB, 0:32 (iteration lane: 14.6 GiB) | `opening_relation_holds`, `b0_is_the_b_polynomial` stay kernel (cited by kernel proofs) |
| `f6c2e607e`, `ff4ce647d` | `PastaCurveScheduled` | 4.0 GB, 0:18 (iteration lane: 11.9 GiB) | `mainRailOk`/`pinsTied` stay kernel (certificates) |
| `367c5c694` | `MinaWrapPublicCommGate` | 7.3 GB, 1:09 | two cited theorems stay kernel |
| `99afa2cd8` | `MinaFinalizeScalars` | 4.5 GB, 1:54 | |
| `d023d84b5` | `MinaFinalizeScalarsWeld` | 3.7 GB, 8:03 | interpreted evaluation is the wall time |
| `26e39b3e8` | `MinaWrapXiEndoLift` | 9.1 GB, 1:12 (was 9.5 GB) | the machine-run theorem and `endoAir_pinsTied` are cited, still kernel |
| `90f5d3ebe` | `MinaWrapClosingScheduled` | 5.7 GB, 0:46 | 18 facts (the commit message says 19) |
| `549e83ef9` | `MinaWrapVerifierAir` | 4.9 GB, 0:13 | |
| `931e2aa52` | `MinaWrapXiAggregateMsm` | 3.8 GB, 0:08 | not in the default build |
| `a697eaeb1` | `MinaWrapXiBasisWeld` | 5.1 GB, 0:14 | not in the default build |
| `fe93cfdf2` | `MinaWrapXiScalarWeld` | 3.7 GB, 0:06 | not in the default build |
| `9bfac8b7b` | `MinaPhase1TapeBinding` | 3.7 GB, 0:04 | |
| `a8830db91` | `MinaWrapVkDigestChain` | 3.7 GB, 0:04 | |
| `40f1db6fc` | `MinaBodyHashRelimbAir` | 4.0 GB, 0:06 | |
| `9453dad41` | `MinaWrapAggregationGate` | 3.6 GB, 0:05 | every theorem compiled |
| `a02093815` | `MinaWrapGroupGate` | 3.6 GB, 0:04 | every theorem compiled |
| `afc144857` | `MinaAccumulatorAir` | 11.6 GB, 1:54 | §8a-§8b kernel defeq proofs over the routed block are the remaining 7.6 GB (the "12.0" in its commit title is an earlier failing variant, not a before) |
| `392812d12` | `MinaWrapOpeningSched` | 3.8 GB, 0:41 | `TiedAir` verdicts compiled; certificate pinned `#assert_compiled` |
| `28326f20b` | retired `MinaWrapSgChunk0`..`3` | | |

## Downstream check (one `lake build` of every Lean importer of the changed modules, bb2, at `392812d12`)

Green: `MinaWrapClosingAir`, `MinaWrapClosingScheduled`, `MinaAccumulatorSrsDemo`, `MinaWrapCommitMachine`,
`PastaMsmBucketed`, `FtCommWeld`, `MinaWrapPublicCommData`, `Bridge.MinaStepPrevCommitments`,
`MinaBodyHashRelimbSeams`, `MinaSeams`, `KimchiStepMainPins19d`, `MinaWrapXiScalarWeld`,
`MinaWrapPublicInputFromHeader`, `MinaOpeningCheckWeld`, `MinaBodyPreimageSeams`, `AirCrossRow`,
`AirSelectorForcing`, and every changed module itself (22:33 wall, 11.6 GB peak).

Red, not from this lane: `KimchiStepMainPins01`, `03`, `05`, `10`, `12`, `14` fail their own `#guard`s and
`native_decide`s (values, e.g. `classCells posS (vGx shapeSmoke)).length == 5` is false). This lane
changed proofs only, never a definition, so it cannot move an evaluated value; the reds block
`Dregg2.MinaBridgeGuards`, which imports them. Reported to the root.

## Earlier steps, superseded by the above

- `MinaWrapOpeningGate` at `5b89f003b`: every `decide` was `decide +kernel`, 7.9 GB.
- `PastaCurveScheduled` at `f6c2e607e`: `scheduled_columns_fit` split into per-family and per-op
  kernel checks, 6.6 GB; `decide +kernel` alone and `Elab.async false` had left it at 11.7 GB.
  `ff4ce647d` replaced the split with one compiled check.

## Decisions only ember can make

- `MinaWrapSgChunk0`..`3`: **retired 2026-11-06 on ember's word** ("lets retire that stuff").
  Record: 61 lines each, zero Lean importers, no Rust consumer, not in the default build (excluded
  from the root since 2026-07-29 because each chunk peaked near 75 GB and one was killed by
  earlyoom), so nothing built or checked them. What they proved, `sg == <s, srs.g>` over the
  32,768 generators of block 539508 by kernel `decide` in 32 slices, stays pinned by compiled
  evaluation: the `mina_sg_bench` executable (self-checking in both polarities) and
  `Dregg2.Bridge.MinaWrapSgWeld`. `MinaWrapSgCore` and `MinaWrapSgParts` stay (the weld and the
  on-demand script `scripts/run-mina-sg-instance.sh` use them). Entries removed from
  `scripts/lean-orphans-allow.txt`, `scripts/guard-modules-baseline.txt` and
  `scripts/elab-cost-baseline.tsv`; Lean docstrings that mention the chunks by name
  (`Bridge.MinaWrapSg`, `Bridge.MinaWrapSgWeld`, `MinaWrapSgCore`, `PastaMsmSliced`,
  `Verify.FloorPole`) were left as they are so no rooted module rebuilds for a comment.
- Nothing else in the census is a retirement candidate so far: the modules either feed
  `circuit/descriptors/by-name` (17 of them, through `EmitByName.lean`), the dedicated emitters, or
  Lean importers on the path to those.

## Diagnosis pattern

Both heavy modules share one shape: a `decide` or `rfl` over a large concrete object that Lean
evaluates in the elaborator (`Meta.whnf`/`isDefEq`), which is far hungrier than the kernel. The
rescues, in order of preference:

1. Prove the fact structurally when it holds by construction (the tie verdict).
2. Where evaluation is the honest proof, let the kernel do it: `decide +kernel`.
3. Where several theorems re-evaluate the same expensive value, evaluate it once into a named
   equation with a literal and rewrite the others with it.

## Appendix: census, 2026-11-06

| module | lines | Lean importers | in default build | last touched | descriptors via `EmitByName` | Rust consumers |
|---|---|---|---|---|---|---|
| `B.MinaAccountOpening` | 563 | 2 | yes | 2026-07-31 |  | named in src:dregg-lean-ffi |
| `B.MinaAccountOpeningRealBlock` | 114 | 1 | yes | 2026-07-30 |  | named in src:dregg-lean-ffi |
| `B.MinaBinprot` | 924 | 3 | yes | 2026-07-30 |  | named in src:bridge, src:dregg-lean-ffi, src:metatheory, src:turn |
| `B.MinaBinprotRealBlock` | 464 | 2 | yes | 2026-07-30 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.MinaChainSelection` | 1038 | 5 | yes | 2026-07-29 |  | named in src:bridge, src:dregg-lean-ffi, src:metatheory |
| `B.MinaChainSelectionDifferential` | 140 | 1 | yes | 2026-07-29 |  | named in src:metatheory |
| `B.MinaCheckpoint` | 605 | 1 | yes | 2026-07-30 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.MinaForkChoiceGate` | 384 | 4 | yes | 2026-07-30 |  | named in src:bridge, src:dregg-lean-ffi, src:turn |
| `B.MinaMultiBlockConformance` | 656 | 3 | yes | 2026-08-02 |  |  |
| `B.MinaPackInjective` | 482 | 2 | yes | 2026-08-08 |  | named in test:circuit |
| `B.MinaSelectionVectors` | 287 | 2 | yes | 2026-07-29 |  | named in src:metatheory |
| `B.MinaSlidingWindow` | 1557 | 2 | yes | 2026-07-29 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.MinaStateHashDerive` | 537 | 7 | yes | 2026-07-30 |  | named in src:bridge, src:circuit, src:dregg-lean-ffi, src:turn, test:circuit, test:circuit-prove |
| `B.MinaStateHashPackPrice` | 234 | 3 | yes | 2026-08-09 |  | named in test:circuit-prove |
| `B.MinaStateHashRealBlock` | 263 | 2 | yes | 2026-07-30 |  | named in test:circuit-prove |
| `B.MinaStateHashWordGate` | 1116 | 2 | yes | 2026-08-02 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.MinaStepPrevCommitments` | 327 | 2 | yes | 2026-08-10 |  | named in src:metatheory |
| `B.MinaVrfThreshold` | 418 | 1 | yes | 2026-07-29 |  |  |
| `B.MinaWrapChallenges` | 438 | 3 | yes | 2026-07-30 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.MinaWrapChallengesWeld` | 237 | 2 | yes | 2026-08-10 |  | named in src:bridge |
| `B.MinaWrapDeferred` | 465 | 4 | yes | 2026-07-30 |  | named in src:metatheory |
| `B.MinaWrapDeferredWeld` | 633 | 2 | yes | 2026-08-02 |  | named in src:metatheory |
| `B.MinaWrapFtEval0` | 599 | 8 | yes | 2026-07-30 |  | named in src:dregg-lean-ffi, src:metatheory |
| `B.MinaWrapFtEval0Weld` | 778 | 2 | yes | 2026-08-10 |  | named in src:bridge |
| `B.MinaWrapPublicInput` | 424 | 2 | yes | 2026-07-30 |  | named in src:bridge |
| `B.MinaWrapSg` | 263 | 2 | yes | 2026-07-30 |  | named in src:metatheory |
| `B.MinaWrapSgWeld` | 248 | 1 | no | 2026-07-30 |  | named in src:metatheory |
| `B.PicklesProofChainGate` | 489 | 3 | yes | 2026-07-29 |  | named in src:bridge, src:dregg-lean-ffi |
| `B.PicklesR3BranchDataDiff` | 133 | 1 | yes | 2026-07-31 |  |  |
| `B.PicklesStatementDiff` | 346 | 1 | yes | 2026-08-01 |  |  |
| `B.PicklesStepStatementDiff` | 242 | 1 | yes | 2026-08-01 |  |  |
| `B.PicklesWrapShapeGate` | 481 | 2 | yes | 2026-08-08 |  | named in src:bridge, src:dregg-lean-ffi |
| `E.KimchiArena` | 375 | 3 | yes | 2026-08-05 |  |  |
| `E.KimchiAssertEqual` | 753 | 4 | yes | 2026-08-05 |  | named in src:metatheory |
| `E.KimchiCellCommit` | 709 | 3 | yes | 2026-07-30 |  |  |
| `E.KimchiCircuitJson` | 261 | 12 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiComposeMSM` | 229 | 2 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiComposeStepFragment` | 712 | 4 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiConditionalCircuit` | 418 | 1 | yes | 2026-08-05 |  |  |
| `E.KimchiCustomGates` | 175 | 8 | yes | 2026-08-01 |  |  |
| `E.KimchiDag` | 2448 | 1 | yes | 2026-07-28 |  | named in test:circuit-prove |
| `E.KimchiEffectIncNonce` | 699 | 3 | yes | 2026-07-30 |  |  |
| `E.KimchiGadgets` | 455 | 3 | yes | 2026-08-05 |  |  |
| `E.KimchiLower` | 631 | 5 | yes | 2026-07-28 |  | named in test:circuit-prove |
| `E.KimchiPartition` | 248 | 1 | yes | 2026-07-28 |  |  |
| `E.KimchiPlacement` | 679 | 21 | yes | 2026-08-05 |  | named in src:metatheory, src:tools |
| `E.KimchiPoseidon2` | 939 | 3 | yes | 2026-07-31 |  |  |
| `E.KimchiPoseidonGate` | 378 | 1 | yes | 2026-07-27 |  | named in src:bridge, src:metatheory |
| `E.KimchiPreimageCircuit` | 541 | 3 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiRealProofGate` | 410 | 1 | yes | 2026-08-02 |  | named in src:metatheory |
| `E.KimchiRecursionGate` | 356 | 1 | yes | 2026-07-28 |  |  |
| `E.KimchiRender` | 128 | 1 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiRenderCompleteAdd` | 208 | 7 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiRenderEndoMul` | 202 | 5 | yes | 2026-08-06 |  |  |
| `E.KimchiRenderEndoMulScalar` | 157 | 4 | yes | 2026-08-06 |  |  |
| `E.KimchiRenderPoseidon` | 160 | 5 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiRenderPublicInput` | 343 | 4 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.KimchiRenderVarBaseMul` | 196 | 6 | yes | 2026-08-06 |  |  |
| `E.KimchiRootAirEval` | 592 | 1 | yes | 2026-07-28 |  |  |
| `E.KimchiStepMain` | 1188 | 2 | yes | 2026-08-09 |  | named in src:metatheory |
| `E.KimchiStepMainCore` | 6879 | 5 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiStepMainField` | 166 | 2 | yes | 2026-08-02 |  |  |
| `E.KimchiStepMainFixture` | 1065 | 26 | yes | 2026-08-09 |  | named in src:metatheory |
| `E.KimchiStepMainPins01` | 413 | 1 | yes | 2026-08-09 |  | named in src:metatheory |
| `E.KimchiStepMainPins02` | 269 | 1 | yes | 2026-08-03 |  |  |
| `E.KimchiStepMainPins03` | 280 | 1 | yes | 2026-08-09 |  |  |
| `E.KimchiStepMainPins04` | 271 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiStepMainPins05` | 228 | 1 | yes | 2026-08-09 |  |  |
| `E.KimchiStepMainPins06` | 285 | 1 | yes | 2026-08-09 |  |  |
| `E.KimchiStepMainPins07` | 289 | 1 | yes | 2026-08-03 |  |  |
| `E.KimchiStepMainPins08` | 236 | 1 | yes | 2026-08-11 |  |  |
| `E.KimchiStepMainPins09` | 271 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiStepMainPins10` | 296 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiStepMainPins11` | 250 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiStepMainPins12` | 310 | 1 | yes | 2026-08-11 |  |  |
| `E.KimchiStepMainPins13` | 633 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiStepMainPins14` | 272 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiStepMainPins15` | 188 | 1 | yes | 2026-08-03 |  |  |
| `E.KimchiStepMainPins16` | 280 | 1 | yes | 2026-08-03 |  |  |
| `E.KimchiStepMainPins17` | 272 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiStepMainPins18` | 307 | 1 | yes | 2026-08-03 |  |  |
| `E.KimchiStepMainPins19` | 397 | 2 | yes | 2026-08-11 |  |  |
| `E.KimchiStepMainPins19d` | 328 | 1 | yes | 2026-08-11 |  |  |
| `E.KimchiStepProverChoice` | 567 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiStepStatementPins` | 381 | 1 | yes | 2026-08-10 |  | named in src:metatheory |
| `E.KimchiStepWrapChain` | 1402 | 3 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiStepWrapChainFixture` | 279 | 7 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiStepWrapChainKey` | 64 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiTarget` | 487 | 4 | yes | 2026-07-28 |  |  |
| `E.KimchiTyp` | 1214 | 2 | yes | 2026-08-06 |  |  |
| `E.KimchiVerify` | 1516 | 23 | yes | 2026-08-08 |  | named in src:bridge, src:dregg-lean-ffi, src:metatheory |
| `E.KimchiWrapFinalizeSpongeGate` | 395 | 1 | yes | 2026-08-07 |  | named in src:metatheory |
| `E.KimchiWrapHackDigest` | 333 | 2 | yes | 2026-08-07 |  | named in src:metatheory |
| `E.KimchiWrapMain` | 843 | 6 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiWrapMainCore` | 6302 | 5 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiWrapMainField` | 1735 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiWrapMainFixture` | 219 | 13 | yes | 2026-08-06 |  |  |
| `E.KimchiWrapMainPins01` | 342 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiWrapMainPins02` | 65 | 1 | yes | 2026-08-05 |  |  |
| `E.KimchiWrapMainPins03` | 227 | 1 | yes | 2026-08-05 |  |  |
| `E.KimchiWrapMainPins04` | 270 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiWrapMainPins05` | 173 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiWrapMainPins06` | 122 | 1 | yes | 2026-08-05 |  |  |
| `E.KimchiWrapMainPins07` | 154 | 1 | yes | 2026-08-06 |  |  |
| `E.KimchiWrapMainPins08` | 221 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiWrapMainPins09` | 489 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiWrapMainPins10` | 299 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiWrapMainPins11` | 391 | 1 | yes | 2026-08-07 |  |  |
| `E.KimchiWrapMainPins12` | 862 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.KimchiWrapProverChoice` | 269 | 1 | yes | 2026-08-08 |  |  |
| `E.MinaAccumulatorAir` | 2326 | 7 | yes | 2026-08-11 | `mina-accumulator-seg.json`, `mina-accumulator-final.json`, `mina-accumulator-routed.json` | src:circuit-prove, test:circuit · named in src:bridge, src:circuit, src:recursion-verify, test:circuit-prove |
| `E.MinaAccumulatorSrsDemo` | 189 | 2 | no | 2026-08-07 | `mina-accumulator-srs.json`, `mina-accumulator-head.json`, `mina-accumulator-head-genesis.json` | test:circuit |
| `E.MinaBlockFqTranscript` | 562 | 5 | yes | 2026-08-10 | `pasta-fq-wraplink.json` | src:turn, test:circuit, test:circuit-prove · named in src:circuit-prove, test:recursion-verify |
| `E.MinaBodyHashRelimbAir` | 1037 | 4 | yes | 2026-08-11 | `dregg-mina-bodyhash-relimb-v1.json` | test:circuit, test:circuit-prove |
| `E.MinaBodyHashRelimbSeams` | 665 | 3 | yes | 2026-08-11 |  | named in src:circuit-prove, test:circuit, test:circuit-prove |
| `E.MinaBodyPreimageBitsAir` | 911 | 4 | yes | 2026-11-06 | `dregg-mina-body-preimage-bits-v1.json` | src:circuit-prove, test:circuit · named in src:turn |
| `E.MinaBodyPreimageSeams` | 658 | 3 | yes | 2026-08-11 |  | named in src:circuit-prove, src:turn, test:circuit-prove |
| `E.MinaFinalizeScalars` | 506 | 2 | yes | 2026-08-09 |  | named in test:circuit |
| `E.MinaFinalizeScalarsProg` | 896 | 2 | yes | 2026-08-09 |  | named in test:circuit |
| `E.MinaFinalizeScalarsWeld` | 257 | 2 | yes | 2026-08-09 |  |  |
| `E.MinaFixtureEmit` | 239 | 2 | yes | 2026-08-05 | `mina-fixture.json` | src:circuit, test:circuit |
| `E.MinaOpeningCheckWeld` | 314 | 1 | yes | 2026-08-03 |  |  |
| `E.MinaPhase1Chain` | 611 | 6 | yes | 2026-08-10 | `pasta-fp-chainlink.json` | src:circuit, src:circuit-prove, test:circuit, test:circuit-prove |
| `E.MinaPhase1TapeBinding` | 458 | 2 | yes | 2026-08-06 |  | named in test:circuit |
| `E.MinaPhase2Chain` | 393 | 6 | yes | 2026-08-10 | `pasta-fq-chainlink.json` | src:circuit, src:circuit-prove, test:circuit, test:circuit-prove · named in src:turn, test:recursion-verify |
| `E.MinaPreambleLegsAir` | 643 | 3 | yes | 2026-08-10 | `dregg-mina-preamble-legs-v1.json` | test:circuit |
| `E.MinaRealBlockGate` | 299 | 7 | yes | 2026-07-28 |  | named in src:bridge, src:dregg-lean-ffi, src:metatheory, test:circuit, test:circuit-prove, test:turn |
| `E.MinaRealBlockTranscript` | 489 | 9 | yes | 2026-07-28 |  | named in src:bridge, src:dregg-lean-ffi, src:metatheory, test:circuit |
| `E.MinaSeams` | 1442 | 4 | yes | 2026-08-11 |  | named in src:circuit-prove, src:turn, test:circuit, test:circuit-prove |
| `E.MinaStateBodyHashChain` | 629 | 4 | yes | 2026-08-07 |  | named in src:circuit-prove, src:turn, test:circuit, test:circuit-prove |
| `E.MinaStateQuery` | 795 | 2 | yes | 2026-07-28 |  |  |
| `E.MinaStepOwnAccumulator` | 47 | 1 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.MinaStepSrsG` | 65688 | 2 | no | 2026-08-05 |  |  |
| `E.MinaStepSrsLagrange` | 175 | 2 | yes | 2026-08-04 |  | named in src:metatheory |
| `E.MinaStepSrsLagrangePin` | 88 | 1 | yes | 2026-08-03 |  |  |
| `E.MinaWrapAggregationData` | 147 | 5 | yes | 2026-08-09 |  |  |
| `E.MinaWrapAggregationGate` | 80 | 3 | yes | 2026-08-09 |  | named in test:circuit |
| `E.MinaWrapClosingAir` | 1264 | 3 | yes | 2026-08-11 |  | named in src:circuit-prove, test:circuit, test:circuit-prove |
| `E.MinaWrapClosingScheduled` | 713 | 2 | yes | 2026-08-10 |  |  |
| `E.MinaWrapCommitMachine` | 1077 | 2 | yes | 2026-08-06 |  | named in test:circuit |
| `E.MinaWrapCommitStages` | 1111 | 4 | yes | 2026-08-10 | `mina-commit-pub.json`, `mina-commit-f.json`, `mina-commit-ft.json`, `mina-commit-agg.json`, `mina-commit-ladder.json`, `mina-commit-xi.json` | test:circuit |
| `E.MinaWrapConjunctionAir` | 1594 | 7 | yes | 2026-08-10 | `mina-wrap-conjunction.json`, `mina-wrap-conjunction-unthreaded.json` | src:circuit, src:circuit-prove, test:circuit · named in src:turn, test:circuit-prove |
| `E.MinaWrapDeferredWords` | 404 | 2 | yes | 2026-08-11 |  | named in src:metatheory |
| `E.MinaWrapGroupData` | 145 | 3 | yes | 2026-08-09 |  |  |
| `E.MinaWrapGroupGate` | 177 | 4 | yes | 2026-08-09 |  | named in src:bridge, src:metatheory, test:circuit |
| `E.MinaWrapHackDummySg` | 124 | 3 | yes | 2026-08-10 |  | named in src:metatheory |
| `E.MinaWrapOpeningGate` | 384 | 3 | yes | 2026-08-10 |  | named in src:bridge, src:circuit, src:circuit-prove, src:turn, test:circuit, test:circuit-prove |
| `E.MinaWrapOpeningGateData` | 366 | 10 | yes | 2026-08-10 |  |  |
| `E.MinaWrapOpeningSched` | 757 | 1 | no | 2026-08-10 |  | named in src:circuit-prove, test:circuit, test:circuit-prove |
| `E.MinaWrapOpeningWeld` | 44 | 1 | yes | 2026-08-10 |  |  |
| `E.MinaWrapOwnVerifierKey` | 93 | 2 | yes | 2026-08-10 |  | named in src:metatheory |
| `E.MinaWrapProofDeferredWords` | 176 | 2 | yes | 2026-08-07 |  | named in src:metatheory |
| `E.MinaWrapPublicCommData` | 186 | 6 | yes | 2026-08-09 |  |  |
| `E.MinaWrapPublicCommGate` | 169 | 3 | yes | 2026-08-09 |  | named in src:bridge, src:metatheory, test:circuit |
| `E.MinaWrapPublicInputFromHeader` | 104 | 2 | yes | 2026-07-29 |  | named in src:bridge, src:dregg-lean-ffi |
| `E.MinaWrapSgChunk0` | 61 | 0 | no | 2026-07-28 |  |  |
| `E.MinaWrapSgChunk1` | 61 | 0 | no | 2026-07-28 |  |  |
| `E.MinaWrapSgChunk2` | 61 | 0 | no | 2026-07-28 |  |  |
| `E.MinaWrapSgChunk3` | 61 | 0 | no | 2026-07-28 |  |  |
| `E.MinaWrapSgCore` | 205 | 4 | no | 2026-08-10 |  | named in src:bridge |
| `E.MinaWrapSgParts` | 40 | 2 | no | 2026-07-28 |  | named in src:metatheory |
| `E.MinaWrapSrsG` | 32838 | 8 | yes | 2026-07-28 |  | named in src:bridge, src:circuit, src:metatheory, test:bridge, test:circuit |
| `E.MinaWrapVerifierAir` | 1323 | 6 | yes | 2026-08-10 | `pasta-alu-sound.json`, `pasta-alu-fq-sound.json`, `pasta-alu-sz.json`, `pasta-alu-fq-sz.json` | test:circuit, test:circuit-prove · named in src:circuit-prove, src:turn |
| `E.MinaWrapVerifierProgram` | 1270 | 4 | yes | 2026-08-10 | `pasta-sbox-prog.json`, `pasta-sbox-prog-1k.json` | test:circuit |
| `E.MinaWrapVerifierSponge` | 1240 | 6 | yes | 2026-08-10 | `pasta-fq-round.json`, `pasta-fq-absorb.json` | test:circuit · named in test:circuit-prove |
| `E.MinaWrapVerifierSpongeFp` | 688 | 4 | yes | 2026-08-10 | `pasta-fp-round.json`, `pasta-fp-absorb.json` | src:circuit, src:turn, test:circuit, test:circuit-prove · named in src:circuit-prove |
| `E.MinaWrapVkDigestChain` | 755 | 2 | yes | 2026-08-06 |  | named in src:bridge, src:circuit-prove, test:circuit |
| `E.MinaWrapXiAggregateMsm` | 448 | 3 | no | 2026-08-09 | `mina-xi-aggregate-msm.json` | test:circuit |
| `E.MinaWrapXiBasisWeld` | 391 | 0 | no | 2026-08-05 |  | named in test:circuit |
| `E.MinaWrapXiEndoLift` | 506 | 5 | yes | 2026-08-10 | `mina-xi-endo-lift.json` | src:circuit-prove, test:circuit · named in test:circuit-prove |
| `E.MinaWrapXiScalarWeld` | 276 | 1 | no | 2026-08-05 |  | named in test:circuit |
| `E.PicklesDerivePlonkRealGate` | 164 | 1 | yes | 2026-07-28 |  |  |
| `E.PicklesFinalize` | 915 | 5 | yes | 2026-07-28 |  | named in src:metatheory |
| `E.PicklesRecursion` | 1298 | 7 | yes | 2026-07-28 |  | named in src:bridge, src:metatheory |
| `E.PicklesStepStatement` | 424 | 1 | yes | 2026-08-06 |  | named in src:metatheory |
| `E.PicklesTranscriptBinding` | 808 | 2 | yes | 2026-07-28 |  | named in test:circuit-prove |
| `E.PicklesVerifyPreamble` | 763 | 3 | yes | 2026-08-08 |  | named in src:bridge |
| `Dregg2.MinaBridgeGuards` | 109 | 0 | yes | 2026-08-08 |  |  |
| `Dregg2.PicklesSynthesis` | 185 | 0 | yes | 2026-08-06 |  |  |
