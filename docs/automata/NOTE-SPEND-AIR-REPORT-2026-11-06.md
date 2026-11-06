# Note-spend consumed AIR consolidation

2026-11-06, Codex gpt-6-astra. Initiative register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**. Root owns commits; this lane performs no git mutations.

## Result and statement boundary

[READ] Two zero-argument Rust constructors duplicated note-spend constraint lowering. Both now consume the existing Lean `NoteSpendingLeafEmit.noteSpendLeafDescFixed`; the recursion adapter also delegates validated witness construction to the core adapter. The actual generated artifact has149columns,7public inputs,33constraints. Six last-row boundaries repair the old27constraint shape's transition-gate gap. The public tuple and descriptor name remain unchanged; canonical descriptor bytes and derived verification-key identity change, so old proofs must be regenerated.

[MEASURED] `NoteSpendingLeafServed.lean` compiles with **eight kernel-clean keystones and eight exact axiom pins**, no `native_decide`. `fixed_implies_base` projects actual `Satisfied2` of the repaired descriptor to the existing base semantics; `served_spend_spec` and `served_committed_note_member` compose the existing row and path theorems. `served_member_inhabited` inhabits **all premises together** on the existing two-row witness, and `served_member_witness` applies the member theorem to that package. `repair_separates_same_trace` proves the identical old forge accepted by the old AST and refused by the consumed AST.

The semantic boundary is explicit: the membership theorem needs interior-row path shape, canonical values and a faithful wide chip table. The positive inhabitant has a zero-depth path and an abstract constant permutation. The old forged trace uses an abstract table, so its acceptance is not evidence of a real Poseidon2 proof forgery. This scalar fact-hash tree is not the deployed Faithful8 note tree. No test or serializer equality is presented as Rust/STARK refinement.

## Files and checks

- `metatheory/Dregg2/Circuit/Emit/NoteSpendingLeafServed.lean`: composed bridges, full premise witness, old/new separation and exact pins.
- `metatheory/EmitByName.lean`: existing note-spend route selects `noteSpendLeafDescFixed`; row count remains144. Corrects the old “fixed is a decoy” comment.
- `circuit/descriptors/by-name/note-spend-leaf.json`: actual fresh Lean emission,19,270bytes including newline.
- `circuit/src/note_spend_witness.rs`: parse artifact; retain witness builder. Tests pin actual repaired shape/dispatch and evaluate each of six malformed last-row cases using production `eval_lean_expr`.
- `circuit-prove/src/note_spend_leaf_adapter.rs`: share core descriptor/public tuple/witness functions; retain public APIs and recursion wrappers. Existing witness validation now applies before recursion proving.
- `circuit-prove/tests/note_spending_emit_gate.rs`: consumer wiring plus existing honest/hostile real prover regressions; removes false “independent lowering equality proves refinement” wording.
- `circuit-prove/tests/law1_enforcement_gate.rs`: remove both41site allowance rows. Remaining enum references inspect patterns. Correct the custom-lowering Lean-mirror claim and legacy DSL drift-detection claim.
- `scripts/check-note-spend-emitter.sh`: one narrow warm-Lean check for all eight theorem pins, exact emitted bytes,33constraint/sixboundary shape and correct routing.
- `docs/automata/AIR-GENERATOR-GROUNDING.md`, `AIR-GENERATOR-REPORT-2026-11-06.md`, `AIR-REMAINING-DEBT.md`, and this report record scope and remaining work.

[MEASURED] `scripts/check-note-spend-emitter.sh` PASS, exit0 (`/tmp/astra-note-gate.log`). Rustfmt succeeds on all three edited Rust implementation/integration files. Static routing parser finds144unique rows. `sg` finds zero `EffectVmDescriptor2` struct expressions in both removed lowerers. Across the original51 census paths it finds45expressions in18files, down from55/26before this campaign: **ten production constructors removed**. These are bounded structural measurements, not a complete C9 census.

[PENDING] Native tests are queued in the shared build-integration lane, with real Lean FFI. No native green is claimed here:

```sh
cargo nextest run --release -p dregg-circuit --lib --ignore-default-filter -E 'test(note_spend_witness::)'
cargo nextest run --release -p dregg-circuit-prove --lib --ignore-default-filter -E 'test(note_spend_descriptor_lowers) | test(fact_arity7_chip_absorb_matches_hash_fact)'
cargo nextest run --release -p dregg-circuit-prove --test note_spending_emit_gate --test note_spending_emit_audit_extra --ignore-default-filter -E 'test(note_spend) | test(forged_) | test(tampered_)'
cargo nextest run --release -p dregg-circuit-prove --test law1_enforcement_gate -E 'test(law1_no_new_rust_authored_constraints) | test(law1_no_new_rust_authored_air_accepts)'
```

[PENDING] Whole Lean tree and integrated-revision provenance re-stamp belong to the root/build lane. No remote job, foreign clone mutation, whole Mac build or stamp fabrication was done here. `AIR-REMAINING-DEBT.md` identifies the next actual compiler/generator gaps; no Ember-only decision was identified.
