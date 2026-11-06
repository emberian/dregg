# Caveat AIR generator — 2026-11-06

Initiative register row **#1 — Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**. Codex gpt-6-astra; root owns commits. This closes one more static Rust constraint producer, with a reusable modular borrow-chain generator.

## Grounding and statement

[READ] `Circuit/CaveatBignumCompare.lean` proves the integer `borrowSub_iff` model. Its header additionally names `borrowSubGates` and `gates_hold_iff_BSValid`, but those declarations do not exist in that file. Its actual equation theorem `bsLimbEqn_is_gate` is over integer `Constraint.holds`, not the emitted BabyBear descriptor. The live Rust constructor in `caveat_admission_leaf_adapter.rs` was therefore still the constraint author.

[READ] New `Emit/BorrowChainEmit.lean` authors a parameterized limb-equation list. `modular_limb_sound` lifts a congruence to exact integer subtraction when both operand/difference limbs are bounded by radix B, borrows are Boolean, and `2*B < 2013265921`. `chain_identity` telescopes any number of limbs with zero final borrow; `bodies_sound` connects the generated expressions to integer comparison. All-zero limbs inhabit every width. The named top-borrow falsifier shows why a nonzero final borrow must be refused.

[READ] New `Emit/CaveatAdmissionEmit.lean` uses that generator for the existing three five-limb comparisons. `caveat_emit_sound` derives time≤expiry, height<ceiling, value≤budget, and asset equality from **the actual Satisfied2 descriptor**. `public_limbs_bound` identifies the canonical public limbs with that row; `caveat_public_sound` states all four atoms directly over the public tuple. Canonical decoding and faithful range-table interpretation remain explicit hypotheses. Satisfied2 alone does not assert public range-table semantics.

[MEASURED] Shape: **67 columns, 40 public inputs, 194 constraints** = 40 first-row PI pins + 15 subtraction equations + 12 Boolean borrows + 5 asset equalities + 67 transition copies + 55 range lookups. The 26-bit range is implemented by the existing byte-decomposition backend; it does not allocate a 2^26-row physical table. Five 26-bit limbs retain the full u128 domain; the AIR's admitted integer domain is 130 bits, as before. The descriptor name remains `caveat-admission-leaf::bignum_decidable_atoms_v1`; constraint order and expression trees follow the prior constructor.

[MEASURED] Nine concrete emitter keystones and six generic borrow-chain keystones pass kernel checking, with exact axiom pins. The full honest Satisfied2 witness uses height 0 < ceiling 1 and proves canonicality; its range table is definitionally the faithful table. A named emitted-chain falsifier shows equal heights pass the weaker inclusive chain and fail the strict chain. No native_decide is used.

## Consumption and verification

The Rust cutover replaces only the descriptor constructor/helpers with `include_str!` + `parse_vm_descriptor2`; existing witness generation, public tuple, recursion consumers and range lowering stay connected. New narrow tests exercise the production expression evaluator on honest small/large/u128::MAX witnesses and every false atom, plus a real inner-STARK roundtrip with changed-public-asset refusal. They are regression tests, not a proof of Rust/STARK refinement.

The emitted artifact is `circuit/descriptors/by-name/caveat-admission-leaf.json` (22,100 bytes including newline), routed from `CaveatAdmissionEmit.descriptor` in `EmitByName.lean`. The constructor, actual generated artifact and emission row were installed together after checking the original source had no concurrent edits. EmitByName now has 144 routes, including the DECO and table/weld siblings' additions; the static parser confirms its count and all routed files exist.

The standing gate `scripts/check-caveat-emitter.sh` compiles the two new Lean files and mutates only private temporary copies: replacing first-boundary constraints with last-row-skippable gates, and permitting a final borrow. [MEASURED] The gate passed: both mutants were refused by the semantic `comparison_sound` gate (run log `/tmp/astra-caveat-gate2.log`, exit 0). The shared source was never disarmed.

Rust command for the build-integration lane (queued for bb2 headroom):

```sh
cargo nextest run --release -p dregg-circuit-prove --lib --ignore-default-filter -E 'test(caveat_admission_descriptor_is_wellformed) | test(caveat_emitted_)'
```

Actual Rust and full fresh-provenance results are pending; no green is claimed for them. The descriptor is generated directly from Lean, not manually stamped. Remaining parameterized production generators and other Air/builder dialects remain C9 debt, enumerated in AIR-GENERATOR-GROUNDING.md.
