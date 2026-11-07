# Remaining AIR authorship: structural audit and cutover map

2026-11-06, Codex gpt-6-astra. Initiative register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**.

[READ] marks inspected source; [MEASURED] marks structural query results; [INFERRED] marks conclusions or proposed work. This is a bounded audit of the remaining constructors after the initial eight static-leaf migrations described in `AIR-GENERATOR-GROUNDING.md`, not a repository-wide declaration of C9 completion. Note-spend consolidation is owned by the generator lane and is intentionally not duplicated here. No builds, tests, remote jobs, or git mutations were performed for this audit.

## Follow-through in this cycle

[READ, MEASURED] The recommendations below now have three additional landings. `9773903d3`
consolidates both note-spend consumers onto the existing fixed Lean artifact and adds a jointly
inhabited semantic bridge. `000ce3b99` removes the discarded UMem descriptor from both cohort
staging paths while preserving the arbitrary-domain compatibility producer. `247ebb4b9`
generates the depth-uniform binary membership block, consumes it from Rust, and proves its
actual-height binary path semantics with a full witness and final-row refusal control.
Eleven production constructors have been removed; the UMem staging simplification is not
counted as another removal because its compatibility constructor remains.

The binary block preserves the existing ten constraints. Its seven-constraint comparator is
an intentionally weakened control, not a newly discovered production bug. Its public digest
remains scalar and its name's depth is not an admission check on proof height. The UMem
consumers still include Rust-authored weld transformations downstream; removing the temporary
metadata carrier does not discharge those. Native integration is recorded separately in the
binary/UMem reports and the deputy report. The original audit rows below remain a precise map
of the source before these follow-through changes, not a claim that they are still untouched.

[READ, MEASURED] 2026-11-07, direct-logic front end (lane G): `compile_logic_program` no longer
authors a constraint. It sends canonical source bytes to `Dregg2.Logic.DirectLogicProgramIR2`
(`lake exe direct_logic_compile`, or `metatheory/scripts/direct-logic-compile-interp.sh` without a
native build) and parses the reply; the law1 row for `circuit/src/direct_logic_frontend.rs` went
3 -> 0 and was deleted. The Lean source language now carries everything the Rust compiler added:
one-hot enumeration gates, quantifier expansion with the same balanced folds, the BLAKE3 source
name and the padding column. `program_sound` / `program_complete` are over that exact descriptor;
`booleanOnly_accepts_twoHot` / `program_refuses_twoHot` are the control showing why replacing only
the Boolean polynomial would have been weaker. Differential over the 18 existing test and benchmark
programs: identical relations, widths, one-hot/accept gates, names and refusals; only the
booleanity rendering changed. Open: a native build of the executable pulls the whole Mathlib C
closure (no box holds those objects today), so the in-process route (an `@[export]` in the
`dregg-lean-ffi` archive implementing `LogicCompiler`) versus a shipped executable is undecided.

## Count the right object

[READ] The original `degg-research/experiments/air-census/air_census.sh` counts textual `EffectVmDescriptor2 {` occurrences. Its 111 hits in 51 files include return signatures, decoder code, comments and tests inside source files. A struct-expression count is better, but still omits modifications to an existing descriptor and other constraint dialects. The generator grounding note records the separate structural counts for that original 51-path set.

[READ] The current `circuit-prove/tests/law1_enforcement_gate.rs` covers **five**, not three, dialects: symbolic assertions; evaluator closures; `ConstraintExpr` constructors; direct `LeanExpr`/`VmConstraint`/`VmConstraint2` trees; and `air_accepts` predicates. Its scope is repository-wide `src/` trees. The three-dialect description in `docs/CIRCUITS-FROM-PROOFS.md` is stale. The ratchet deliberately counts test code too, and a baseline is an upper bound rather than a discharge certificate. Its prose claim that `CustomLeafEncoding` proves the deployed lowerer is also stale; the Lean theorem explicitly says otherwise.

[MEASURED] AST inspection of `impl_item` nodes in `circuit/src` and `circuit-prove/src`, filtering the implemented trait to `Air<…>`, found **14 actual p3 AIR implementations**:

| Role | Implementations | Consequence |
|---|---|---|
| Descriptor/DSL interpreters: 6 | `descriptor_ir2::{Ir2Air,Ir2UniAir}`; `lean_descriptor_air::{LeanDescriptorAir,EffectVmDescriptorAir}`; `dsl/dsl_p3_air::DslP3Air`; `circuit-prove/lean_lookup_air::LeanLookupAir` | Their `assert_*` calls interpret an input grammar. They require interpreter/refinement review, not a generated descriptor in place of every assertion. DSL source authors remain a separate question. |
| Explicit `cfg(test)` AIRs: 4 | `plonky3_prover::{MinimalDegree7Air,MulAir7,MinimalDegreeNAir}`; `dregg_outer_config::ToyFibAir` | Test fixtures, not deployed statement authors. The generic `MinimalDegreeNAir` is missed by the original simple text pattern. |
| Smoke scaffolds: 2 | `plonky3_recursion::AggregationAir`; `effect_vm_p3_air::EffectVmShapeAir` | The first proves endpoint continuity without its advertised hash fold; the second intentionally checks only an Effect-VM-shaped subset. Neither is a substitute for a production proof statement. |
| Retained statement-specific AIRs: 2 | `bilateral_aggregation_air::{CrossSideExistenceAir,BundleTreeFoldAir}` | Real authored algebra remains, but live wrappers already consume `EffectVmEmitCrossSide` / `EffectVmEmitBundleFold` JSON. The retained implementations are layout/trace/test debt, not evidence that these deployed legs lack Lean sources. |

[MEASURED] `sg -p '$B.assert_zero($$$)' -l rust circuit/src circuit-prove/src` found 67 actual call expressions across eight files. This is only the `assert_zero` dialect and includes tests; it is not 67 distinct constraints or AIR families. The original `mina_fixture_emit.rs` implementation hit is documentary text, not a surviving p3 implementation. The AST query also needs to distinguish an implemented `RecursableAir` trait from an `Air` bound in its `where` clause.

[READ] A second trait dialect survives: `constraint_prover::Air` with `Constraint { eval: Box::new(…) }`. `merkle_types::MerkleAir`, `committed_threshold::CommittedThresholdAir`, and `dsl/fold::FoldAir` author concrete statement equations. `derivation_air::DerivationAir` instead wraps `ConstraintExpr::evaluate_with_tables`; the source algebra is in `dsl/derivation.rs::derivation_circuit_descriptor`. These must not disappear from the inventory just because the p3 survey is clean. Their exported legacy APIs are not evidence of deployed use; the law1 ledger classifies FoldAir as test-only. Production reachability of every older closure API was not established by this bounded audit.

## Remaining constructor / consumer map

| Rust source and actual consumer | Existing Lean source and precise coverage | Remaining prerequisite |
|---|---|---|
| `circuit/src/membership_descriptor_general.rs::membership_descriptor_of_depth`; live `descriptor_by_name` prefix dispatch uses `.map(membership_descriptor_of_depth)` | `AdjacencyMembershipEmit` supplies the chip tuple convention; `MerkleMembershipEmit` / `MerkleMembershipRefine` cover a different fixed, 4-ary shape. `MembershipDepthGeneralRung2::{foldNode4_inj,membership_depth_general_sound}` are functional **4-ary** path-fold theorems, with injectivity/domain-separation hypotheses. They do not establish the Rust binary descriptor's row semantics. | The binary block is **depth-uniform**: depth changes its name, not gates. Generate the 13-column/2-PI block once, retain the naming policy, and prove actual row ordering, last-row gates and continuity. Prove a binary arbitrary-height SAT-to-path theorem; do not cite the 4-ary fold theorem as that bridge. Separately audit its broad injectivity premises under the standing statement gate. |
| `circuit/src/whole_image_fold.rs::whole_image_fold_descriptor`; own prove/verify wrappers; observed external wrapper calls are tests | `WholeImageFoldRealization::{wholeBoundaryFold8,padImtRoot8_binds_or_ghost_or_collides,crossCellRead_wholeImage8}` describes the deployed-shape indexed, padded, eight-lane heap root. Its scope explicitly leaves sparse-vs-dense equivalence and the AIR bridge open. | This constructor is **static**, not parameterized. A Lean AST generator can replace it, but a useful statement must derive the intended sorted-insert chain from its real `MapOp`/window/boundary constraints. Existing root-model theorems alone do not do so. No production activation should be inferred from converting this test-facing wrapper. |
| `circuit/src/direct_logic_frontend.rs::compile_logic_program`; executable `bin/direct_logic_live_benchmark.rs` and public API | `Logic/FiniteLogicDescriptorIR2::{compileDescriptor,source_sound,source_complete,canonical_trace_iff,certifyLive}` already constructs actual IR2. Soundness consumes `CanonicalLogicSatisfied2`; completeness constructs a real one-row witness. `Metatheory/DirectLogicBoolGraphDescriptorIR2` is an alternative materialized low-degree backend. | Highest-value existing semantic core for a reusable cutover. Transport the source AST to the existing Lean compiler through an owned executable/FFI route. Rust currently adds finite-domain one-hot constraints, quantifier expansion, source-hash identity and width-at-least-one behavior; reconcile/prove those, rather than replacing only the Boolean polynomial. No callable compiler export was found in the inspected FFI/routing paths. |
| `circuit/src/custom_leaf_lowering.rs::{cellprogram_to_descriptor2,lower_cellprogram}`; `circuit-prove/{custom_leaf_adapter,dsl_leaf_adapter}` and `turn/executor/{atomic,membership_verifier}` | `CustomLeafEncoding::{encodeLocal,encodeTransition,encodePiBinding,cell_to_descriptor_faithful}` models a subset. The theorem's own comment explicitly says **Lean mirror, not deployed Rust lowering** and calls it a carrier-reduction: `CellLocalHolds` is the emitted body's modular vanishing. `encodePiBinding_not_complete` records the every-row to first-row mismatch. | Real source-language compiler work: chip-lane allocation, hash arities, paired seed/chain handling, guarded constraints, boundary semantics, table interpolation, refusal cases and fill plans. A proved generic AST transformation plus source-language semantics is needed. Translating match arms into Lean without an independent source denotation would merely move the mirror. |
| `circuit-prove/src/carrier_pin_twin.rs::insert_tail_claim_pins`; observed calls are its unit test and factory/hatchery deployed-tooth tests | `EffectVmEmitRotationV3.withAfterOctetPins`, `CarrierComposed`, and membership exposure modules already author the corresponding deployed transforms. Native sovereign/membership registry rows no longer use this twin. | Staging/test transform, not demonstrated production debt. Move each remaining tooth to its generated descriptor where identity matches; if arbitrary insertion remains useful, export a generic proved PI-reindexing transform. It currently refuses ProofBind, shifts PiBinding indices and reconstructs the descriptor with `challenges: 0`; do not silently advertise it as a semantics-preserving transform for all IR2 descriptors. |
| `circuit-prove/src/zkoracle_leaf_adapter.rs::zkoracle_to_descriptor2(n_limbs)`; `prove_zkoracle_inner`, then production proving entry points | Existing `SpongeCarrierReduction` supplies collision-extraction/game infrastructure, not this emitted chain. `Crypto/ZkOracle.lean` concerns parser/injection semantics, not the content-commitment descriptor. | Genuine per-length generator: one arity-4 marked length head, then arity-11 absorbs of the previous **eight** lanes plus three body limbs, zero padding, final scalar-head PI. Preserve its admitted 1..=1024-limb range (current byte codec: up to 2040 bytes), length pin and full internal carrier. This commitment is not `hash_bytes`. Prove SAT-to-chain before binding claims; a scalar output requires an explicit collision residual, not unconditional injectivity. |
| `turn/src/umem.rs::umem_proving_inputs_from_v1`; `umem_proving_inputs_v1` and the single/multi-domain cohort adapters | `EffectVmEmitUMemCohort.umemCohortDesc` already emits one guarded operation over base columns 0..5/guard6. `EffectVmEmitUMemCohortMulti.umemCohortDesc2` emits two guards6,7. Their `Satisfied2U` final-state/root theorems and honest witnesses cover the corresponding fixed shapes. | Simplify witness staging first: adapters read domain metadata from the temporary descriptor and discard it, returning rows/boundary for an emitted route. Carry domains explicitly instead. Direct producer tests still consume its arbitrary-domain descriptor, so preserve their API through a genuine generic Lean list generator or migrate them deliberately. The old producer declares no tables; cohort emitters declare main/UMem/boundary tables, so they are not byte-identical drop-ins. |

[READ] The nearby `membership_descriptor_4ary.rs::membership_descriptor_of_depth_4ary` already validates depth and parses `merkle-membership-4ary-wide-general.json`; it does not author its gate block. A function named “descriptor of depth” is therefore not itself proof of remaining authorship.

## Other live composition debt and limits of this map

[READ] `circuit-prove/src/private_book_bfv_terminal/fused.rs::descriptor` starts from emitted slice/terminal descriptors, shifts terminal constraints, then authors a last-row limb-product/reduction weld and PI/domain pins. Its `prove_zk` / `verify_zk` consume the result. This is a **composition constructor**, not a pure adapter: reusing generated ingredients does not make the newly introduced equations generated. The needed reusable transformation is descriptor column/PI relocation plus explicit conjunction/wiring, with separate arithmetic refinement for the product weld. This audit has not established a matching Lean fused descriptor; coordinate with the BFV owner before modifying its active shape. Its file documents one exact coordinate, not the complete 98,304-equation family.

[READ] The wider law1 ledger also retains source/compiler families under `dregg-dsl-differential`, `dregg-dsl-runtime`, `constraint-lowering`, `game-turn-slice`, and SDK proof construction. They are outside this constructor-focused inspection. The ledger's historical reachability labels and theorem citations require source checks; the custom-leaf citation above is a concrete example of why a baseline comment cannot discharge a statement audit.

[INFERRED] Recommended order: finish the owned note-spend consumed cutover; remove UMem's unnecessary descriptor-as-metadata construction where consumers already use emitted cohorts; replace the uniform binary membership block with a generated family and real row/path bridge; then connect the existing finite-logic compiler through a checked source transport. The zkOracle chain is a useful generic wide-carrier generator project; custom-leaf compilation is broader compiler/refinement work. Whole-image fold and retired bilateral AIRs are legitimate remaining cleanup, but cannot substitute for closing live compiler paths.

For every cutover, closure means the actual consumer parses the Lean output, a named theorem refers to that exact generated AST and its intended source relation, honest witnesses inhabit the assumptions, concrete adversarial cases are refused, and axioms are pinned. Differential execution detects drift; it does not prove Rust-to-Lean refinement. No decision requiring Ember's private information was identified by this audit.
