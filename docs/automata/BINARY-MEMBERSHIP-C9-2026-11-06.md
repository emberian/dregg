# Generated binary membership with an actual-path refinement

Register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR
generator, build)**. Codex gpt-6-astra, 2026-11-06.

[READ] `circuit/src/membership_descriptor_general.rs` authored a depth-uniform binary path block:
13 columns, 2 public inputs, 10 constraints. Its live consumer is the binary prefix branch in
`descriptor_by_name`; generic descriptor-dispatch verification consumes that result. This is
not the fixed four-ary descriptor and the old four-ary functional-fold theorem does not prove
this binary block's row semantics.

## What changes

`BinaryMembershipEmit.membershipDesc` now authors the exact existing block in Lean. The generated
`circuit/descriptors/by-name/merkle-membership-binary-general.json` is its depth-2 template;
Rust caches the parsed artifact and changes **only the historical depth-qualified name**.
All constructor depth values retain their previous behavior. Witness admission still requires
a power-of-two path length of at least two.

[MEASURED] Generated artifact SHA-256:
`9a18890aa8d4516cb3f32f1422c573e4c8dfb920d0083aee143d3e47966b6c49`.
It contains 13 columns, 2 PIs, 10 constraints, no declared tables, no inline hash sites or ranges.
One arity-2 chip lookup supplies the parent digest per row. **Count delta: zero columns, PIs,
constraints or permutations.** The transition-only direction/ordering gates and all three matching
last-row boundaries are preserved. AST inspection of the new Rust producer finds no descriptor
struct construction or authored gate-expression construction; parsing and name metadata remain.

[MEASURED] All three new Lean modules passed warm single-file checks with exact axiom pins:

- `BinaryMembershipEmit.lean`: generated AST and depth-uniform shape.
- `BinaryMembershipRefine.lean`: `membership_sat_refines` derives the full binary authentication
  fold from `Satisfied2` of that generated AST, sound chip rows, canonical cells/PIs and nonempty
  trace. It extracts ordered children on **every** row, including the last; threads every parent
  to the next current value; pins the public leaf/root; proves all directions binary.
- `BinaryMembershipWitness.lean`: one complete mixed-direction satisfying witness jointly meets
  all premises and invokes the main theorem. Under the nonconstant reference hash, leaf 3 with
  right sibling 5 yields 13, then left sibling 7 yields public root 33.

No hash-injectivity hypothesis is used. Keystone axiom sets contain only `propext`,
`Classical.choice`, and `Quot.sound`; no `native_decide` is used. The new theorem composes the
existing genuine **binary** row-ordering arithmetic lemma from `AdjacencyMembershipRefine`,
then proves this generated descriptor's whole arbitrary-height fold. It does not borrow a
four-ary result as a substitute for the missing bridge.

## Falsifiers and precise limits

`last_row_separation` keeps the same attack trace while proving all of: genuine chip rows,
canonical cells, acceptance by a deliberately weakened seven-constraint control, a false binary
path claim, and rejection by the full ten-constraint descriptor. The attack reverses the final
ordered children and recomputes their genuine chip output/public root to 27. Thus continuity,
chip correctness and endpoint pins alone cannot explain the rejection: the final ordering
boundary bites. **The Rust descriptor being migrated already had that boundary.** This is a
semantic falsifier of the refinement, not a claim to have found a new deployed missing-gate bug.

`depth_label_does_not_bind_height` proves that the same honest two-row witness satisfies the
descriptor named depth 8. That naming policy already existed and is preserved. The theorem
covers the actual trace height; a caller requiring a particular physical depth must check it
separately. A depth in a string is not a constraint, and the pre-existing truncated-path test
changed the claimed root, so it did not establish height admission.

The public leaf/root and parent spine remain **one felt**. Seven auxiliary permutation output
lanes do not make this an eight-lane commitment. The theorem proves a binary authentication
fold; it does not claim unique leaves or collision resistance at this width. Chip-table
soundness and the ordinary descriptor-model-to-STARK boundary remain explicit assumptions.

## Consumer validation and continuation

The Rust tests now check parse-and-name-only equality against the emitted template, retain
honest depth-2/4/8 prove/verify coverage, reject the final-child-order attack on the unchecked
producer rail, and accept the two-row/depth-8-label control. The unchecked negative runs through
prove **and** verify and recognizes only documented unsatisfiability or an error, not arbitrary
panics.

At this report's creation, native filtered execution is assigned to the shared integration lane,
not yet claimed green. Its narrow `nextest` filter is:

```
test(membership_descriptor_general::tests::descriptor_shape) |
test(membership_descriptor_general::tests::honest_membership_proves_and_verifies_depths_2_4_8) |
test(membership_descriptor_general::tests::last_row_child_order_refuses_on_unchecked_rail) |
test(membership_descriptor_general::tests::depth_label_is_not_a_height_constraint)
```

Root owns the `EmitByName` row, registry explanatory updates, source-provenance restamp,
statement-gate entry, and law-C9 ratchet update. The existing binary prefix continues to route
through the same public constructor. No new remote jobs, local Cargo builds, package updates or
git mutations were performed by this lane. No choice here requires ember's private information.
