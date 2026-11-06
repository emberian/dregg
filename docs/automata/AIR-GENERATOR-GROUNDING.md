# Lean-first AIR generator: grounding and consumed replacements

2026-11-06, Codex gpt-6-astra. Initiative register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**. [READ] denotes inspected implementation; [MEASURED] a recorded check; [INFERRED] a conclusion from that evidence. This is a partial C9 closure, not a claim that all Rust constraint authorship is gone.

## What exists and what the census actually measures

[READ] `SUBSTRATE-DECISION.md` §2 correctly separates Lean semantics, target refinement, decoder canonicality, and program identity. Its §3 description of `zkoracle-prove/src/zk_leg.rs` as a hand-built descriptor is wrong at this revision: the function parses a JSON literal already emitted by `DfaRoutingGeneralEmit.injectionRoutingDesc`. The census matches its return signature. It needs an artifact route, not another AIR.

[READ] `docs/CIRCUITS-FROM-PROOFS.md` already specifies the useful generator architecture: Lean constructs `EffectVmDescriptor2`; `emitVmJson2` serializes; `EmitByName.lean` routes; Rust parses and interprets. A new code-generation framework would duplicate it. The work here adds reusable proved generators within that architecture and connects their actual consumers.

[MEASURED] The 2026-11-05 census's **111 matches in 51 files are textual occurrences**, including return types, comments, decoders and tests. Before these replacements, `sg -p 'EffectVmDescriptor2 { $$$ }' -l rust --json=compact <the 51 paths>` found **55 actual struct expressions in 26 files**. After the solvency, five tuple, DECO and caveat replacements, the same structural query found **47 expressions in 20 files** (eight production constructors removed). These are bounded observations of that original path set, not a complete census of all constraint dialects.

[READ] Classification of those original 55 expressions:

| Role | Examples and consequence |
|---|---|
| Deserializers | `descriptor_ir2.rs` and `descriptor_ir2_canonical.rs` each have one real decoder construction; parsing authored constraints is interpretation, not new constraint authorship. |
| Tests and benchmark fixtures | Those same files carry 17 and 3 test literals respectively; `refusal.rs` has 2, `effect_vm_descriptors.rs` 1. `joint_turn_recursive.rs` has 4 stand-ins; private preference/graph files have one each; factory/hatchery each retain a stand-in; `carrier_pin_twin` has a test. `perf/src/lib.rs` has 3 benchmark fixtures. Test status is not a proof that the represented statement is faithful. |
| Static production leaves | Solvency, factory, hatchery, sovereign, membership, delegate, DECO and caveat admission are replaced by Lean generators in this step. The zkOracle commitment leaf remains a parameterized producer. |
| Parameterized producers / transformations | General membership, note-spend's duplicated lowering in `circuit` and `circuit-prove`, whole-image fold, custom-leaf lowering, direct-logic lowering, carrier pin insertion, private BFV fused descriptor and turn UMem boundary construction still synthesize constraints. They require generator/refinement work, not blind replacement with one fixed JSON. |
| Other constraint dialects | `impl Air` and assertion-builder closures are separate debt; this struct-expression survey does not establish their elimination. Existing law1 ratchet covers three dialects and remains relevant. |

The reliable closure unit is a production constructor plus its theorem, consumer and emission route. Renaming a file called `air.rs`, deleting a return-type match, or moving the same constraint assembly into a helper does not discharge C9.

## Solvency: replace the constructor and repair its statement

[READ] The old Rust leaf constrained only `(reserve-liability) mod p` to 30 bits. That does **not** prove `reserve ≥ liability`, even when both advertised amounts are 30-bit: with `p=2013265921`, `(R,L)=(0,1073741823)` gives modular difference `939524098 < 2^30`. The broader canonical attack `(0,p-1)` gives difference 1. Both are named kernel-decided falsifiers in `SolvencyLeafEmit.lean`.

[INFERRED] Merely copying the old gates into Lean would preserve the bug. Shrinking the amount domain to 29 bits would avoid one wrap case but silently reduce the interface. The replacement follows the existing two-limb borrow technique in `EffectVmEmitBurn.lean`: six 15-bit limbs cover reserve, liability and difference; one Boolean low-limb borrow; no final borrow. Each limb equation is bounded tightly enough that modular equality implies integer equality. Both advertised 30-bit amounts retain `[0,2^30)`. This is now an enforced operand domain: older callers passing larger amounts merely because their difference was small must supply a different bounded-amount representation.

[READ] `SolvencyLeafEmit.rangeBodies bits value base` is a layout-independent generator, with `rangeBodies_sound` for every fitting bit width and canonical assignment. `arithmetic_sound` composes six instances into exact subtraction. `solvency_emit_sound` extracts those constraints from **the actual `Satisfied2` descriptor**, at the PI-pinned first row. First-boundary constraints also apply at height one; ordinary `.gate` constraints skip the last row and would not suffice there.

[READ] `solvency_commitments_sound` proves the two public inputs equal the fact-hash output heads for the same compared values, assuming the existing `ChipTableSoundN` interpretation and canonical PI decoding. It assumes neither injectivity nor collision resistance. The honest nonzero borrow witness `(32768,1)` inhabits the whole `Satisfied2` premise with a proved sound constant-output chip table (`honest_chip_sound`). This is semantic inhabitation, not an assertion that Poseidon is constant. Scalar fact commitments and their existing security limits remain; these theorems do not prove hiding, hash security or Rust/STARK implementation refinement.

[READ] The old constructor used 51 columns and 36 constraints. The emitted v2 descriptor has **118 columns, 106 constraints: 102 arithmetic boundaries, 2 arity-7 chip lookups, 2 PI pins**. Its public tuple remains `[reserve_commit, liability_commit]`. The new name `solvency-leaf::dregg-reserve-covers-liabilities-v2` deliberately changes descriptor/VK identity. `solvency_leaf_adapter.rs` parses the generated artifact and fills witnesses only. Its input guard refuses out-of-range `u64` values before field reduction can alias an amount. The AIR itself enforces the range against malicious witnesses.

[READ] Structural consumer tracing finds the production constructor call in `prove_solvency_inner`; both recursion entry points go through it. The structured-product fold consumes the same two commitment PIs, so the tuple interface is unchanged while proofs must be regenerated for the new descriptor. Existing full recursion tests remain available; the narrow emitted-expression test checks the actual Rust witness layout against the production interpreter and both old attacks. Such testing is regression evidence, not refinement proof.

## Injection: remove the duplicate serialization hop

[MEASURED] A standalone Lean driver importing the existing `DfaRoutingGeneralEmit` emitted **2901 JSON bytes**, exactly matching the former Rust literal (plus the artifact newline). The stale comment claiming a missing `challenges` key was already false; the literal has `challenges:0`. The consumer now uses `include_str!` on `by-name/dfa-routing-injection.json`, and the same definition is routed by `EmitByName`. No injection descriptor semantics changed.

## Shared generators and the next two consumed leaves

[READ] `BoundedFactEmit` now owns the generic range generator, offset-range theorem and five-slot fact-opening generator. Solvency delegates to it; DECO uses three generated fact sites and the offset range. The DECO amount contract is inclusive at 2^30, matching the former construction; first-boundary constraints remove the former last-row bypass. Its transcript commitment is still an existential witness column, not a public authentication claim.

[READ] `BorrowChainEmit` authors generic modular limb equations and proves exact subtraction for arbitrary limb count. `CaveatAdmissionEmit` connects its actual 194-constraint descriptor to all four public caveat atoms over 5×26-bit operands. Its full honest trace and faithful range-table witness inhabit the statement; its inclusive/strict-chain falsifier isolates the strict-height condition. See `CAVEAT-AIR-REPORT-2026-11-06.md` for the producer and test boundary.

## Remaining work and integration boundary

The tuple generator lane owns factory/hatchery/sovereign/membership/delegate and its generic tuple theorem. This lane coordinates their emission rows with the solvency/injection rows; route-table and weld lanes have additional new route entries. Source/artifact updates require a fresh provenance stamp at the integrated revision, coordinated with the Mina rescue work. An old snapshot's stamp cannot certify new bytes. No whole emitter run was launched on the Mac.

C9 is still open for the parameterized production producers and hand-authored Air/builder dialects above. These eight replacements do not close the full initiative bar. The scalable next step is to move shared transformations (range blocks, tuple pins, copy constraints, hash openings, note-spend limb lowering) into Lean generators with a semantic preservation theorem, then consume the generated instances or extracted parameterized generator. A census reduction is a progress measure, not a substitute for those theorem and consumer connections.
