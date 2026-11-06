# Lean-authored public tuple carriers

Initiative register: **#1 — Parser/language excellence (policy language, demos,
perf, Lean-first AIR generator, build)**. This closes five concrete production
constructors under C9; it does not claim the repository-wide census is closed.

[READ] `factory_leaf_adapter`, `hatchery_leaf_adapter`,
`sovereign_leaf_adapter`, and `membership_leaf_adapter` each constructed the same
IR-v2 recipe in Rust: first-row public-input pins followed by constant-column
transition windows. `delegate_descriptor` constructed only the first-row pins.
The delegate distinction is intentional and preserved.

`metatheory/Dregg2/Circuit/Emit/TupleBindingEmit.lean` now owns one generator,
`tupleDesc name width constantRows`, and five instantiations. `EmitByName.lean`
serializes them. Rust reads the emitted JSON with `parse_vm_descriptor2`; no
production constructor in these five files authors a constraint.

| Artifact in `circuit/descriptors/by-name/` | Width / public inputs | First-row pins | Transition windows | Total |
|---|---:|---:|---:|---:|
| `factory-backing-leaf.json` | 24 | 24 | 24 | 48 |
| `hatchery-attestation-leaf.json` | 16 | 16 | 16 | 32 |
| `sovereign-authority-leaf.json` | 21 | 21 | 21 | 42 |
| `membership-leaf.json` | 2 | 2 | 2 | 4 |
| `delegate-binding-v2.json` | 24 | 24 | 0 | 24 |

[MEASURED] Total: **150 degree-one constraints**, 87 public-input columns across
the five descriptors, zero lookups, hash sites, ranges, or challenges. The
`constraint_count` theorem proves the generic count `w + (if constantRows then
w else 0)`; these counts are taken from the emitted JSON. No wall-clock performance
claim is made. Widths, names, constraint order, and selector behavior are preserved.

`tuple_semantics` characterizes the **actual** `VmConstraint2.holdsAt` evaluation
of every generated constraint. First-row pins force `loc[c] ≡ pub[c]`; the
constant-row variant additionally forces `nxt[c] ≡ loc[c]` on every nonfinal row.
`all_rows_bound` consumes the full `Satisfied2` denotation and proves every
in-range row agrees with the public tuple. Equalities are modulo BabyBear's
prime, exactly the AIR contract; no equality of arbitrary integer representatives
is asserted.

`honest_satisfies` supplies a full two-row `Satisfied2` witness for **every** tuple,
width, and mode, including empty memory and map tables. `changed_public_refused`
and `changed_next_refused` reject a disagreeing limb for every valid column;
`zero_ne_one_mod` inhabits the disagreement premise. The intentionally weaker
mode is checked by `first_only_allows_distinct_next`. Every theorem has an exact
`#guard_msgs` axiom pin; none uses `native_decide`.

The semantic boundary remains the same: these leaves bind claimed tuples.
Factory derivation, hatchery attestation, sovereign authorization, and membership
validation are not re-proved by a tuple carrier. Delegate scope binding does not
prove the cap-graph effect of delegation. Existing test-only weaker descriptors
in factory/hatchery are deliberate recursion comparators, not production authors.

## Reproduction and validation

On a warm Mac Lean cache, from `metatheory/`:

```sh
lake env lean Dregg2/Circuit/Emit/TupleBindingEmit.lean
```

The normal `scripts/emit_descriptors.py` pipeline routes all five artifacts through
`EmitByName.lean`. Run provenance re-stamping through the coordinated emitter
chain; isolated checks do not certify the whole emission source stamp.

The complete narrow Lean gate, including isolated public-pin and copy-window
mutations, is `scripts/check-tuple-binding-emitter.sh`. The script creates and
removes only its own temporary files; it never disarms the shared emitter.

Filtered Rust checks (the root's bb2 integration batch; no unfiltered suite):

```sh
cargo nextest run -p dregg-circuit -E 'test(delegate_descriptor)'
cargo nextest run -p dregg-circuit-prove -E 'test(factory_leaf_adapter) | test(hatchery_leaf_adapter) | test(sovereign_leaf_adapter) | test(membership_leaf_adapter)'
```

[MEASURED] The Lean module compiles with its exact axiom pins. The artifacts were
produced by Lean's `emitVmJson2`, not reconstructed in Python or Rust. Rust
execution and the coordinated provenance refresh remain integration gates until
the root records their results.

[MEASURED] An isolated copy with every public pin redirected to PI 0 and every
copy window changed to the tautology `loc - loc = 0` failed in `tuple_semantics`
and `copy_semantics`; the exact axiom pins additionally rejected the resulting
`sorryAx`. The production source was never mutated. The checked-in narrow gate
passed its clean check and rejected both mutations independently.
