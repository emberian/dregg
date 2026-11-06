# UMem cohort witness staging without temporary AIR

2026-11-06, Codex gpt-6-astra. Initiative register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**. Root owns commits; this lane performs no git mutations.

## What changed

[READ] Both `umem_cohort_proving_inputs_from` and `umem_cohort_multidomain_proving_inputs_from` formerly called the arbitrary-domain descriptor producer, read its width/UMemOp constraints to rediscover domains, and discarded that descriptor. The common validation and witness derivation now return private `UmemWitnessInputsV1 { domains, rows, boundary }`. The cohort adapters consume those fields directly. Sorted domain order continues to determine guard column `6 + i`, independently of operation execution order.

The public `umem_proving_inputs_from_v1` and `umem_proving_inputs_v1` APIs remain compatible: they still produce the arbitrary-domain descriptor, with its unchanged name, width, tables, write-form UMemOps and row/boundary layout. That compatibility wrapper is the sole remaining descriptor constructor in `turn/src/umem.rs`. The new helper preserves empty-input refusal, address collision admission, value alias admission at both op endpoints and touched pre-state cells, power-of-two padding and boundary sorting. Cohort public return types remain unchanged; downstream callers in `sdk/src/full_turn_proof.rs` and `turn-prover/src/rotation_witness.rs` still receive domain(s), rows and boundary.

[INFERRED, structural cost] For D touched domains, each cohort call avoids constructing D temporary UMemOp constraints, their7D expression leaves, the descriptor name and constraint vector. The multi-domain path also avoids reconstructing a second domain vector by scanning those constraints. No wall-clock speedup is claimed. The repository still contains the compatibility constructor, so this step does **not** increase the ten-removed-constructor census count.

## Existing Lean connection and remaining scope

[READ] `EffectVmEmitUMemCohort.umemCohortDesc` and `EffectVmEmitUMemCohortMulti.umemCohortDesc2` already describe the fixed single/two-domain shapes and their memory semantics. This change is witness staging: it does not alter those ASTs, emit new artifacts, change a VK or introduce a new theorem. Native regressions are not presented as Rust-to-Lean refinement.

[READ] Important boundary: not every downstream path simply parses a fully emitted cohort descriptor. `effect_vm_descriptors.rs::weld_umem_into_descriptor_with_suffix` and the multidomain weld still construct Rust UMemOp constraints around generated descriptors/splice metadata. Those are separate composition debt. The arbitrary-domain compatibility producer also remains Rust-authored. This task removes the discarded AIR from the actual cohort staging path; it does not claim all generic or welded UMem authorship is closed. The scalar v1 codec's host-side alias admission remains an honesty gate, not a verifier-side faithful encoding; the existing v2 wire/epoch work is unchanged.

## Files and validation

- `turn/src/umem.rs`: private checked witness metadata; direct single/multi cohort adapters; preserved public arbitrary-domain producer.
- `turn/tests/umem_cohort_metadata.rs`: five focused regressions covering real boundary data and compatibility, three-domain sorted guards versus reversed execution order, wrong-cohort/empty refusal, address alias refusal, and op/pre-state value alias refusal through both adapters.
- This report.

[MEASURED] Rustfmt parses both files successfully. `git diff --check` passes. Structural `sg` call queries show the sole internal call to `umem_proving_inputs_from_v1` is the preserved witness convenience wrapper; the two cohort adapters and compatibility producer call the private witness helper. No new constraint construction was added to the cohort adapters. Existing arbitrary-domain compatibility is exercised with three domains, so the two-domain emitted family is not silently imposed as an API limit.

[PENDING] Native tests are queued with the build-integration lane; no local Cargo build, remote job or native green is claimed:

```sh
cargo nextest run --release -p dregg-turn --test umem_cohort_metadata -E 'test(umem_metadata_)'
cargo nextest run --release -p dregg-turn --test umem_v1_value_alias_old_admits_new_rejects -E 'test(new_rejects_the_variant_erasure_and_names_the_value_gate) | test(the_retired_reconstruction_agrees_with_the_live_producer_on_an_honest_trace)'
```

No Ember-only decision is needed. Next C9 work must target the actual remaining generic/weld constructors with a consumed Lean transformation and an appropriate semantic theorem; this staging simplification is not a substitute for that work.
