# DECO fact-opening generator

Initiative register: **#1 — Parser/language excellence (policy language, demos,
perf, Lean-first AIR generator, build)**.

[READ] `circuit-prove/src/deco_leaf_adapter.rs` authored three arity-seven fact
lookups, five public-input pins, and a 30-bit decomposition of `amount - 1` in
Rust. It now interprets `deco-commitment-leaf.json`, emitted from
`Dregg2.Circuit.Emit.DecoLeafEmit.decoDescriptor`. `BoundedFactEmit` owns the shared
bit-range and fact-opening generators, also consumed by the solvency emitter.

The public statement is exactly:

- `1 ≤ amount ≤ 2^30` (inclusive, preserving the previous arithmetic domain);
- the public payment identity is
  `hash_fact(hash_fact(amount, [currency, recipient]), [paymentIntentId])`;
- a **private** transcript-commitment column is the fact hash of that identity and
  a private salt.

The last point does **not** authenticate any externally supplied transcript.
There is no public transcript commitment to compare. Server signatures, TLS MACs,
parsing, PKI, and authorization are separate obligations, not consequences of this
leaf. The identity theorem assumes `ChipTableSoundN` for the actual permutation;
it assumes no injectivity and makes no collision-resistance claim for a scalar.

[READ] `DecoBindingFromFold.DecoLeafFriFloor` is an abstract premise saying a leaf
verifier yields a verifying attestation of its chosen engine. Its specialization
to full `DecoRelation` is not supplied by this commitment-only circuit. The header
claim there that its premises hold for the deployed aggregate is stronger than
this emitter establishes. Do not use the new generator theorem to discharge that
premise for an authenticated-payment engine.

## Correctness change

[MEASURED] The former range constraints used `VmConstraint.gate`, which skips the
final row. A height-one trace therefore had no amount-range constraint. The new
emitter uses first-row boundary gates. `amount_range` consumes full `Satisfied2`
and only requires a nonempty trace; `honest_satisfies` supplies a complete
height-one witness. `old_final_row_range_vacuous` exhibits the old selector gap,
and `zero_amount_arithmetic_refused` demonstrates the corrected arithmetic's
negative pole. `upper_endpoint_arithmetic` pins the existing inclusive endpoint.

This changes the AIR and verification key. The descriptor name advances from
`deco-commitment-leaf::dregg-deco-stripe-v1` to
`deco-commitment-leaf::dregg-deco-stripe-v2`; old proofs must be re-proved against
the new descriptor. The public-input layout remains five felts. No compatibility
with proofs generated under the old AIR is asserted.

[MEASURED] Shape: **59 columns, five public inputs, 39 constraints**: three chip
lookups (three permutations per main row), five PI pins, thirty boolean gates,
one recomposition gate. Boolean constraints have degree two; the recomposition
and pins have degree one. No public or private transcript data is checked in.

## Validation

On a warm Lean cache:

```sh
cd metatheory
lake env lean Dregg2/Circuit/Emit/BoundedFactEmit.lean
lake env lean Dregg2/Circuit/Emit/DecoLeafEmit.lean
```

`payment_identity`, `amount_range`, and `transcript_opening` are about the actual
emitted IR denotation. Exact `#guard_msgs` pins cover every named theorem. The
shared helper has no `native_decide`. A complete witness inhabits the chip-table,
canonicality, and full `Satisfied2` premises together.

The isolated semantic mutation gate is `scripts/check-deco-emitter.sh`. It
restores the old last-row bypass and substitutes private salt for public intent
in separate temporary copies, requiring the amount and identity theorem gates
to reject them. It never edits the shared source.

Filtered Rust integration checks:

```sh
cargo nextest run -p dregg-circuit-prove -E 'test(deco_leaf_adapter)'
cargo nextest run -p dregg-circuit-prove --run-ignored ignored -E 'test(honest_deco_proves_as_foldable_leaf_and_exposes_claim) | test(forged_payment_hash_does_not_fold)'
```

The new `deco_amount_range_endpoints` checks real inner proofs at both inclusive
endpoints and refuses both adjacent out-of-range amounts. It skips recursive
wrapping because range enforcement is an inner-AIR property. Root integration
records Rust results and the coordinated provenance re-stamp separately; source
proofs alone do not certify the checked-in artifact stamp.

[MEASURED] `scripts/check-deco-emitter.sh` passed the two clean module checks and
refused both isolated mutations at the expected semantic theorem and exact axiom
pin. `rustfmt --check` passed for the adapter. The actual Lean emission is 11,176
bytes; filtered Rust execution and coordinated source stamping remain pending
root integration.
