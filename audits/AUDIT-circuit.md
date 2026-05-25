# AUDIT-circuit

Scope: `circuit/` crate (93 files, ~85 kLoC).
Methodology: adversarial read-only audit focusing on witness/constraint confusion, public-input binding, lookup integrity, field truncation, IVC recursion, the Effect VM, and the Kimchi backend (extra scrutiny per prior burn).

## Verdict

**CRITICAL.** At least one direct soundness break exists in the Effect VM AIR (the most load-bearing circuit), and the entire `kimchi_native` backend appears to have no copy constraints connecting Poseidon/Merkle gadget outputs to the equality gates that "enforce" them. Both of these classes of bug allow a malicious prover to forge proofs that the verifier accepts.

If only one of the two is real, the system has a single confirmed P0. If both are real (high confidence), the trustless story is broken at multiple layers.

## Summary

The Effect VM AIR (`circuit/src/effect_vm.rs`, 5746 LOC, one giant `eval_constraints` function) is the most security-critical circuit. It enforces per-effect transitions, a row-continuity hash chain, and a Poseidon2-based state commitment tree that is correctly bound at first/last rows via boundary constraints. The state-commitment part is well done — `state_commit == hash_4_to_1(hash_4_to_1(bal_lo, bal_hi, nonce, f0), hash_4_to_1(f1..f4), hash_4_to_1(f5..f7, cap_root), 0)` is fully enforced as an algebraic equation on every row, and `hash_2_to_1` is now called directly in `eval_constraints` (not trusted from prover aux) for `GrantCap`, `SlashObligation`, `ValidateHandoff`, etc. This is the kind of fix the user has previously seen done well.

However, the `net_delta` public input — which the executor uses for the cross-cell **conservation check** — is not bound by any algebraic constraint to the actual `initial_balance - final_balance` deducible from the trace. The PI is pinned to `aux[2]/aux[3]` at row 0 via a boundary constraint, but `aux[2]/aux[3]` themselves have no relationship to per-row balance deltas in the AIR equation. A malicious prover producing an honest trace can write any value into `aux[2]` and into the PI; verification will still succeed. The executor (`turn/src/executor.rs:8082`) then sums these prover-controlled "proven deltas" and gates atomic turn commitment on `sum == 0`. This permits value-balance forgery across cells.

The Kimchi native backend (`circuit/src/backends/kimchi_native/`) is the second major worry. Every gate is constructed with `Wire::for_row(r)` — the wire-routing API that points each wire back to its own row's column. No `Wire::new(target_row, target_col)` calls appear. In Kimchi/Plonk, equalities between different gate cells are enforced via the wires (copy constraints / permutation argument), not the gate coefficients. With every wire self-looped, every gate's witness is free except for the local coefficient equation; the chain of Poseidon gadget rows + a final `w[0] - w[1] = 0` "binding gate" does not actually verify that w[0] in the binding gate equals any Poseidon output. The prover can put any value in the binding gate's w[0]/w[1] (as long as they match each other on that row), and similarly fake Merkle/equality chains. Aspirational soundness tests in `kimchi_native/tests.rs` succeed because they call `prove()` which has Rust-side preconditions (`if ta != tb { return Err(...) }`) — those checks live in the prover, not the circuit, so they catch buggy inputs but do NOT prove the verifier rejects the same. A malicious prover who bypasses `prove()` (or writes their own kimchi witness) is not constrained.

The legacy `MerkleStarkAir` in `circuit/src/stark.rs` is intentionally unsound (linear hash binding) and the docstring admits it; it is `#[deprecated]` but still used by `presentation.rs:1406`, `bridge/src/mina.rs:1172`, `demo/src/stark_proof.rs:51`, and `wire/src/bin/demo.rs:358`.

## Findings by severity

### P0 — soundness breaks

**P0-1. EffectVM net_delta PI is not algebraically bound to trace balance deltas.**
`circuit/src/effect_vm.rs:2286-2291` (sign booleanity only), `2324-2335` (boundary pinning aux[2]/aux[3] to PI), `2287` (`delta_sign * (delta_sign - 1) == 0` is the *only* per-row constraint touching aux[3], and *nothing* touches aux[2] in `eval_constraints` other than the boundary). The state commitment chain correctly binds first/last `balance_lo, balance_hi`, but there is no constraint of the form `aux[2]@row0 - sign_factor * (initial_bal_lo - final_bal_lo) == 0`. A malicious prover producing an honest trace (real delta = −500) can declare PI net_delta = −100; the boundary constraint passes because `aux[2]@row0 = 100` is what they wrote.
**Impact**: executor.rs:8082 sums PI-derived deltas to gate atomic-turn conservation. Adversarial cells can claim arbitrary deltas, breaking conservation across cells.
**Fix**: add a constraint that ties aux[2] to `last_bal_lo − first_bal_lo` (encoded with the sign). Easiest: pin first-row `state_before.balance_lo` and last-row `state_after.balance_lo` via boundary constraints, and add a transition or direct algebraic check `aux[2]*(1-2*aux[3]) == last_bal_lo - first_bal_lo` (gated by sign). The same applies to balance_hi if it ever changes.

**P0-2. Kimchi native circuits have no copy constraints connecting gadget outputs to binding gates.**
`circuit/src/backends/kimchi_native/derivation.rs:280-528`, `predicates.rs:36-101`, etc.: every gate uses `Wire::for_row(r)`. Comments at `derivation.rs:421-424` explicitly call this out ("Full soundness of one-hot enforcement requires copy constraints linking these selectors to the binding computation in Gate 3") but the wires are never connected. A binding gate `c[0]*w[0] + c[1]*w[1] == 0 ⇒ w[0] == w[1]` enforces equality only between the two wires of that row; with self-loop wires, the prover can fill those wires with any matching value and the gate accepts, regardless of what the Poseidon gadget computed three rows earlier. A real adversarial test would generate a witness independently of `prove()`; the existing "adversarial" tests in `kimchi_native/tests.rs` only modify the input struct and then call `prove()`, which does its own Rust-side checks (e.g., `derivation.rs:1115-1117`: `if ta != tb { return Err(...) }`). Those Rust checks block the *honest* prover from creating a bad witness but are not part of the *circuit*; they catch nothing if the prover constructs the witness manually.
**Impact**: every kimchi backend proof — derivation, fold, non-membership, predicates, presentation, IVC — may be forgeable.
**Fix**: thread wires through the `Wire::new(row, col)` API so that the Poseidon output cell wires into the binding gate cell. The Kimchi wires array on each gate must be set up so that equality between (gadget_output_row, output_col) and (binding_row, w0) is enforced via the permutation argument.

**P0-3. Kimchi backend embeds prover-supplied circuit gates in proof.**
`circuit/src/backends/kimchi_native/mod.rs:198-223, 343-368`: `verify_derivation`/`verify_fold` deserialize `circuit_gates_bytes` from the proof itself when present and use those gates to build the verifier index. A malicious prover can therefore embed an empty/permissive circuit and have it verify. The fallback path (when `circuit_gates_bytes` is empty) rebuilds a "template" circuit, but the prover controls which path the verifier takes.
**Fix**: the verifier must build the circuit independently from a known descriptor (the public-input rule_hash or a verifier-key digest), not from prover bytes. If the gate-bytes path must exist for variable-shape circuits, hash the canonical gate serialization and bind that hash to a public input + a registered verification key.

**P0-4. `MerkleStarkAir` is provably unsound and still used by non-test code.**
`circuit/src/stark.rs:740-755` constraint is `parent - (current + sib0 + sib1 + sib2 + position) == 0` — a linear sum that is trivially invertible. The `#[deprecated]` attribute documents this. Live callers:
- `circuit/src/presentation.rs:1406, 2036`
- `bridge/src/mina.rs:1172`
- `demo/src/stark_proof.rs:51`, `wire/src/bin/demo.rs:358`
- benches (acceptable but propagate the API as fine)
- `circuit/src/poseidon_stark_verifier_circuit.rs:1098+` (test, OK)

If `presentation.rs` is in the production proof path (the docstring at lib.rs:71-77 advertises it as such), an attacker can forge Merkle membership proofs with a chosen leaf in O(1).
**Fix**: replace remaining call sites with `crate::dsl::descriptors::merkle_poseidon2_circuit()` (which is what the deprecation note already directs to).

### P1 — high-impact correctness, not direct breaks

**P1-1. 32→4 byte commitment truncation across the executor/circuit boundary.**
`turn/src/executor.rs:1225-1228, 1266-1273` truncates stored 32-byte commitments to a single BabyBear field element by taking only the first 4 little-endian bytes (`u32::from_le_bytes([b[0..4]])`). The Effect VM circuit's state commitment is a single BabyBear, so the truncation discards 28 bytes of binding from the stored commitment. Any two commitments sharing the first 4 bytes (≈ 1 collision per 2^32) are indistinguishable at the boundary. A grinding adversary in any setting where they can choose the new commitment can collide the stored value with a chosen target.
**Impact**: amplifies P0-1 — even if you fixed the algebraic delta binding, the limited entropy of the bound commitment makes second-preimage attacks feasible with modest compute.
**Fix**: either widen the in-circuit state commitment to use multiple BabyBear limbs (4×31 bits ≈ 124 bits) and serialize that wider commitment to/from `[u8; 32]`, or move the boundary to a Poseidon2 hash over Fp (Vesta) so the stored 32 bytes are fully bound.

**P1-2. `MakeSovereign` mode flag encoded as +256 in `reserved` slot with no booleanity / monotonicity constraint.**
`effect_vm.rs:1517-1521`: `c_sov_mode = s_makesov * (new_reserved - old_reserved - 256)`. The "reserved" column is otherwise treated as opaque (only required to be unchanged by other effects). There is no constraint that `old_reserved` started at 0, no constraint that the +256 increment doesn't wrap, and no constraint preventing a `Seal` from spuriously bumping mode bits (`sealed_field_mask` is also in `reserved` per the witness gen?). The witness gen writes `new_state.mode_flag = 1` and `new_state.sealed_field_mask |= ...` but I did not see how these fold into the single `reserved` BabyBear column — that needs review. If they share the column, the constraints don't separate them.
**Fix**: dedicate one column per scalar quantity, or constrain via bit-decomposition that the `mode` bit and `sealed_mask` bits are disjoint and that mode is monotonically 0→1.

**P1-3. Custom effect security advertised but unverified inside the AIR.**
`effect_vm.rs:1386-1421`: Custom effects enforce only state continuity. The PI commits `program_vk_hash` and `proof_commitment` per custom effect, and the docstring tells verifiers they "MUST independently verify the external proof". This is *contract-by-comment* — the executor in `turn/src/executor.rs:8043-8049` does call `program.verify_transition(&pi, &entry.proof)`, but only when a custom program is registered for `cell.vk_hash`. If a cell has no registered vk and the turn has Custom effects, the constraint is vacuous. The current flow forces the absence-of-vk path to use the default `EffectVmAir`, which won't even be aware of the Custom commitment binding (it just propagates the hash through PI).
**Fix**: at minimum, refuse to verify proofs containing Custom effects unless a matching registered program is found.

**P1-4. Atomic transactions allow the prover to declare `net_deposit`.**
`effect_vm.rs:2002-2058` (`AtomicQueueTx`): the AIR uses `param[ATOMIC_TX_NET_DEPOSIT]` as a free witness column constraining only `new_bal_lo = old_bal_lo - net_deposit`. There's no constraint that `net_deposit` is the sum of sub-operations' deposits/refunds — the comment at 2007-2008 hand-waves it. Combined with P0-1, this means an atomic queue tx can claim any (small) balance debit independent of the actual operations.
**Fix**: at trace-generation time, enforce `net_deposit == hash(combined_old, combined_new, op_count, tx_hash) ?` — but really this needs sub-step proofs.

**P1-5. `PipelineStep` "pipeline authorization" comment is empty.**
`effect_vm.rs:2099-2106` says "Pipeline ID binding: pipeline_id must be non-zero (proves authorization)" but the actual constraint is just `aux_sink == sink_new` — there's no constraint that `pipeline_id` is non-zero, nor any membership/registration check. A prover can claim any `pipeline_id`.
**Fix**: add a non-zero constraint `pipeline_id * inv_pipeline_id == 1` (like `DropRef` does for refcount), and bind `pipeline_id` to a registered set via lookup or hash.

**P1-6. EnqueueMessage program_vk_inv aux trick is asymmetric.**
`effect_vm.rs:1864-1879`: constraint 2 is `s_enqueue * (1 - program_vk * program_vk_inv) * validation_hash == 0`. When `program_vk != 0`, the prover must set `program_vk_inv = 1/program_vk` to satisfy *some other* constraint (which one?). Actually constraint 1 already enforces `validation_hash == expected` when `program_vk != 0`. Constraint 2 only forces `validation_hash == 0` if `program_vk_inv` is the actual inverse. A malicious prover with `program_vk != 0` could set `program_vk_inv = 0` and `validation_hash = anything` — then constraint 1 fires (`vk * (validation - expected) == 0` ⇒ validation = expected, OK) but constraint 2 reduces to `vk * (1 - 0) * validation == vk * validation == 0`, which fires only when vk*validation == 0. If validation = expected != 0, this fails — so actually the conjunction works because of constraint 1.

But the converse: when `program_vk = 0`, constraint 1 vanishes, and constraint 2 becomes `(1 - 0) * validation_hash = validation_hash == 0`, OK. So a prover with `program_vk = 0` cannot set a non-zero `validation_hash`. Looks correct on second read. (Flagging as P1 only to recommend a unit test that adversarially tries to set `validation_hash != 0` with `program_vk == 0`.)

### P2 — code-quality / footguns

**P2-1. The Effect VM has a 5746-LOC single function**. Auditing it line by line is hard. `eval_constraints` and `generate_effect_vm_trace` should be split per effect type to make per-effect audits tractable.

**P2-2. No range checks on `balance_lo` (30 bits) / `balance_hi` (34 bits)**.
Documented at `effect_vm.rs:1045-1063`; the AIR comment promises range checks are "TODO(range-checks)". Without these, a prover can use field-valid but out-of-range limbs on interior rows. Mitigated by executor recomputation but not in-circuit.

**P2-3. `compute_effects_hash`** binds effects hash to PI — confirm it is collision-resistant and includes every effect-type-discriminating byte. (Not read in full.)

**P2-4. Lookup arguments**: I did not find any `LookupTable` or `LogUp` implementation in the circuit crate during scan. The catalog (`plans/proof-statements-catalog.md:418`) references lookups loosely. If the design depends on lookups (e.g., for range checks), they are not yet implemented.

**P2-5. Soundness tests are mostly *prover-side* tampering tests**.
`circuit/src/soundness_tests.rs` modifies the trace AFTER `prove()` is called, then checks `verify` rejects. This catches PI substitution, not adversarial witness construction. The genuine adversarial test (custom witness that bypasses `prove()`'s Rust checks) is largely absent across kimchi/STARK.

### P3 — minor / informational

**P3-1.** `circuit/src/stark.rs:2949` test `verifier_rejects_zero_trace_len` exists; verifier minimum size enforcement is OK.
**P3-2.** `compute_action_binding` and friends in `binding.rs` not audited but appear straightforward.
**P3-3.** The IVC `ValidatedIvcProof` story (3121 LOC in `ivc.rs`) was not read in detail. It introduces a parallel "Validated" tier that should be examined for whether its `verify` actually re-verifies the inner step proofs vs. just trusting precomputed booleans.

## Coverage

**Read in full** (≥ 50% line coverage with attention to constraints):
- `circuit/src/lib.rs`
- `circuit/src/effect_vm.rs` (5746 LOC; eval_constraints lines 1010–2293 read carefully; witness gen + tests skimmed)
- `circuit/src/proof_tier.rs` (skim)
- `circuit/src/backends/kimchi_native/mod.rs` (read), `derivation.rs` (read core circuit + prove), `predicates.rs` (read gate constructors)
- `circuit/src/stark.rs` lines 685–800 + verify scaffolding
- `turn/src/executor.rs` 920–1300, 7970–8290 (consumer of the PI)
- `plans/proof-statements-catalog.md` (grep + headline read)

**Skimmed** (grep + targeted reads):
- `circuit/src/backends/kimchi_native/{fold.rs, non_membership.rs, presentation.rs, ivc.rs, from_dsl.rs, dsl_backend.rs, tests.rs}`
- `circuit/src/backends/{plonky3.rs, sp1.rs, binius.rs, mod.rs}` — sp1 has confessed TODO stubs
- `circuit/src/dsl/{circuit.rs, derivation.rs, descriptors.rs}` — scanned for conservation / delta references
- `circuit/src/soundness_tests.rs` (structure of tests)
- `circuit/src/ivc.rs` (function inventory only)
- `circuit/src/presentation.rs` (caller list of `MerkleStarkAir`)
- `circuit/src/stark.rs` rest of file (top-level prove/verify structure)
- `circuit/src/binding.rs` (re-export list)

**Skipped or only spot-checked**:
- `circuit/src/backends/mina/*` (Pickles wrap+step verifier, 5800+ LOC). Not touched. Worth a dedicated audit pass.
- `circuit/src/poseidon_stark*.rs`, `circuit/src/poseidon2*.rs` (Poseidon constants and reference impl). Crypto primitives — should be checked against a vetted Poseidon2 spec.
- `circuit/src/{accumulator_air, body_membership, chunked_derivation, committed_threshold, compound_predicate_air, cross_state_derivation, fold_air, garbled, garbled_air, multi_step_air, native_signature, native_signature_air, non_membership, note_spending_air, quantified_absence, schnorr_*, xmss}.rs` — large surface; each could repeat the kimchi-style coefficient/witness confusion.
- `circuit/src/plonky3_*.rs` (when feature flag enabled).
- `circuit/src/effect_interp.rs` (1683 LOC) — interpreter, not constraint code; lower priority.

## Cross-cutting patterns

1. **Witness-vs-constraint confusion is real and active.** The kimchi backend's missing copy constraints (P0-2) are the cleanest instance: the gate coefficients look correct in isolation, but the surrounding plumbing that would make them load-bearing is absent.
2. **PI binding without algebraic backing** (P0-1, P1-4, P1-5): the same anti-pattern of "set value V in the prover's PI; the boundary constraint says aux[i] == PI[V]; but aux[i] is otherwise unconstrained" appears multiple times in `effect_vm.rs`.
3. **Truncation across crate boundaries** (P1-1): stored 32-byte commitments become 4 bytes of binding. The cclerk audit already flagged this on its side; the circuit side confirms the same truncation in `executor.rs::commitment_to_babybear`.
4. **Aspirational comments / aspirational names**: `ProofTier::Production` is returned for `kimchi_native_tier()` despite the soundness gaps. The `MerkleStarkAir` deprecation message is correct but call sites haven't moved. Comments like "SOUNDNESS FIX" (good) sit next to comments admitting "Full soundness of one-hot enforcement requires copy constraints" with no follow-through.
5. **Custom effects**: documented as security-by-verifier-cooperation, which is honest but fragile.

## Catalog discrepancies (`plans/proof-statements-catalog.md`)

- Catalog L19: "The net balance delta equals (PI[NET_DELTA_MAG], PI[NET_DELTA_SIGN])." — **Not enforced in code** (P0-1).
- Catalog L427: `effect_vm.net_delta == conservation.expected_net_delta` — same.
- Catalog appears to assume lookups exist for range checks; no implementation present in `circuit/src/`.
- Catalog L1317 names "MatchProofDescriptor" — present in `circuit/src/dsl/circuit.rs` but not audited here.

## Open questions for the user

1. Is `presentation.rs::prove_authorization` (via `MerkleStarkAir`) on the production proof path, or only used by demos/wire? If production, P0-4 escalates from "leftover deprecated code" to "live soundness break".
2. Is the kimchi backend currently used by any production verifier (e.g., Midnight observation bridge), or only as scaffolding for the Mina-bridge work? `proof_tier.rs:139` labels it `Production`, which suggests yes.
3. For the Effect VM net_delta gap (P0-1): is there a *separate* per-cell ledger check that recomputes the actual balance change from the new commitment by reversing the Poseidon2 hash chain? I did not find one; if it exists, it would mitigate the issue, but the design as I read it does not have it.
4. The atomic-turn conservation check sums proven_deltas across cells. If a cell's "real" delta is bound by its old/new state_commitment (which it is, via the AIR), is the PI net_delta even needed? Removing it would close P0-1 by construction.
