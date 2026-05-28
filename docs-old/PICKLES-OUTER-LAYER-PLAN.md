# Pickles outer layer plan — STARK-in-Pickles bridge to production

**Status:** design + inventory. Written 2026-05-24, branch `main`. Lane parallel to
the Plonky3 recursion lane (`circuit/src/plonky3_recursion_impl.rs`); this lane
treats Kimchi/Pickles as the *outer* recursive layer that consumes dregg's
per-cell BabyBear STARKs.

Companion to `KIMCHI-SURVEY.md` (the read-only inventory + verdict),
`STAGE-7-GAMMA-2-PI-DESIGN.md` §8 (the Phase 2 aggregation sketch),
`STAGE-7-GAMMA-AGGREGATION-DESIGN.md` (the target topology), and
`AUDIT-circuit.md` (the P0-2 soundness gap on `kimchi_native`).

The animating proposition: Pickles is **already operational at the wrapper
level**. `stark_in_pickles::wrap_stark_in_pickles` runs end-to-end on
`MerkleStarkAir` today. The work between "PoC test passes" and "production
γ.2 Phase 2 substrate" is concrete, bounded, and largely orthogonal to the
Plonky3 recursion lane. This document inventories what exists, names the
specific gaps, and proposes a 1-2 week starter lane that demonstrates
"Pickles verifies a Plonky3 STARK end-to-end" *as a deliverable*, not as
an aspiration.

---

## 1. Current state inventory (verified against source 2026-05-24)

All file paths absolute under `/Users/ember/dev/breadstuffs/`. Line
counts are from `wc -l` on the checked-in tree.

### 1.1 `circuit/src/backends/mina/` — five distinct surfaces

| file              | LOC  | status                                                    |
|-------------------|-----:|-----------------------------------------------------------|
| `mod.rs`          |  628 | shared types, Pasta sponges, Poseidon-Merkle utilities    |
| `pickles.rs`      |  875 | **assisted recursion: OPERATIONAL, sound at state-transition layer** |
| `ipa_verifier.rs` | 1144 | partial in-circuit IPA verifier (Vesta-in-Vesta — fails by design, see §1.3) |
| `standalone.rs`   | 1092 | dual-curve standalone path: **structurally complete, marked `deprecated` pending dual-curve migration** |
| `step_verifier.rs`|  729 | Step circuit (Vesta side) — defers EC ops, **complete** |
| `wrap_verifier.rs`| 1151 | Wrap circuit (Pallas side) — performs EC ops natively, **complete** |
| `glv.rs`          |  653 | GLV signed-digit encoding for EndoMul, complete           |
| `membership.rs`   |   11 | trivial stub (just re-exports)                            |
| `tests.rs`        | 1450 | tests for all of the above                                |

What's actually operational today (verified by reading the code):

- **`pickles::prove_recursive_step` / `verify_recursive_proof`** — uses
  `kimchi::ProverProof::create_recursive`, threads `RecursionChallenge`
  forward, real `kimchi::verifier::verify` runs at the end. Pre/post
  state-transition circuit binds `(pre_hash, post_hash, step_count,
  prev_accumulated_hash)` via Poseidon. Tested and passes.
  - Caveat: line 120, `extract_recursion_challenge` uses a "placeholder
    commitment reconstruction" for the public-input absorbtion. The
    comment is honest: it affects intermediate sponge state, not the
    final accumulator check. This is the kind of shortcut that survives
    audit only because the verifier's `verify_recursive_proof` calls
    full `kimchi::verifier::verify`, which re-derives the transcript.
    But it means an *intermediate* chain step that depends on this
    sponge state being correct is currently unsound — there are none
    today (the recursion is linear), but Phase 2 aggregation would expose it.
- **`pickles::recursive_fold`** — line 786-860, explicitly documented as
  a placeholder: *"For now, we produce a placeholder that demonstrates
  the structure."* The body serializes a hash chain, not a real
  recursive proof. **Do not ship this; it's a scaffold.**
- **`standalone::prove_standalone_recursive_step`** + the dual-curve
  pair `prove_standalone_dual_curve_wrap` /
  `verify_standalone_dual_curve_wrap` — these *do* run real
  Kimchi-verifier transcript replay (lines 555-605 call into
  `step_kimchi.oracles()` and `opening.challenges()` from the upstream
  crate, then map the challenges Fp→Fq for the Pallas-side circuit).
  This is the Mina-equivalent path. Why is it marked
  `#[allow(deprecated)]`? The standalone single-curve path (lines
  41-258) is what's deprecated; the dual-curve path (lines 486+)
  replaces it. The `deprecated` label is a migration marker, not a
  defect signal — but it does mean callers of `prove_standalone_recursive_step`
  see a noisy clippy warning. **Improvement: remove the
  `deprecated` annotation; it implies degradation we shouldn't preserve.**
- **`step_verifier.rs` / `wrap_verifier.rs`** — dual-curve gates.
  Reading `step_verifier.rs::StepVerifierLayout` (line 71-85) confirms
  the public-input layout `(pre_hash, post_hash, accumulated_hash,
  step_count, prev_accumulated_hash, commitment_x, commitment_y,
  evaluation_at_zeta, challenge_digest, b_at_zeta)`. Reading
  `wrap_verifier.rs::WrapVerifierWitness` (line 9-54) confirms the Fq
  witness shape (Vesta points with Fq coords for native Pallas
  arithmetic). The module-level docstring states they are
  **structurally complete (correct gate layout, correct curve)**. The
  testing path (`prove_dual_curve_step` /
  `prove_standalone_dual_curve_wrap`) is exercised. **Status: works.**

### 1.2 `circuit/src/backends/stark_in_pickles.rs` — the bridge — 728 LOC

The piece that makes Pickles a viable outer layer for dregg's STARKs.
Reading top-to-bottom:

- Type definitions (lines 76-178): `PicklesWrappedStark`,
  `WrapConfig`, `WrapError`. Public surface: `wrap_stark_in_pickles`,
  `verify_pickles_wrapped_stark`, `compose_wrapped_starks`,
  `wrap_trace_in_pickles`, `estimate_wrap_rows`.
- `wrap_stark_in_pickles` (line 216-307): native pre-verify
  (`verify_poseidon`), build the Kimchi verifier circuit, prove it,
  self-verify, wrap in Pickles state-transition. The state hash binds
  `(air_name, public_inputs, trace_commitment)` → `(kimchi_proof_bytes,
  constraint_commitment, "verified")`. **Works for `MerkleStarkAir`.**
- `verify_pickles_wrapped_stark` (line 322-366): recompute expected
  pre-state hash from the claimed PIs, verify the Pickles proof via
  `verify_recursive_proof`. **Works.**
- `compose_wrapped_starks` (line 384-441): take two wrapped STARKs,
  produce one Pickles proof attesting to both. Uses
  `prove_recursive_step(Some(&proof_a.pickles_proof), &transition)`
  to extend the chain. **Works.**
- Tests (line 509-727): `test_wrap_stark_in_pickles_minimal`,
  `test_verify_pickles_wrapped_stark`, `test_compose_wrapped_starks`,
  `test_wrong_air_rejected`, `test_tampered_proof_rejected`,
  `test_estimate_wrap_rows`. **All pass.**

### 1.3 `circuit/src/poseidon_stark_verifier_circuit.rs` — the in-circuit verifier — 1407 LOC

The Kimchi circuit that re-runs the STARK verifier inside a Kimchi
proof. Verified gate count target: ~225 rows at 1 query depth 4, ~18,500
rows at 80 queries — fits domain 2^15.

**The PoC shortcuts:** (verified verbatim against source, lines
identified)

- **Alpha challenge derivation (line 440-446):**
  ```rust
  let alpha = {
      let tc_bigint = trace_root.into_bigint();
      let limbs = tc_bigint.as_ref();
      ((limbs[0] % BABYBEAR_MOD_FP) as u32).max(1)
  };
  ```
  A single Fp limb of the trace commitment is used as the constraint
  random-linear-combination coefficient. The comment is honest:
  *"In a full implementation this comes from Fiat-Shamir transcript
  replay."* **Impact:** the prover controls one degree of freedom that
  it shouldn't. Cost to fix: thread a Poseidon sponge through the
  circuit (~200 rows) and absorb the same trace/constraint commitments
  the native verifier absorbs.
- **`z_t` (vanishing polynomial eval) computation (line 506-514):**
  ```rust
  // z_t = constraint_eval / quotient (when quotient != 0)
  let z_t = if quotient != 0 {
      let q_inv = BabyBear::new(quotient).inverse().unwrap_or(BabyBear::ONE).0;
      ((constraint_eval as u64 * q_inv as u64) % BABYBEAR_MOD_FP) as u32
  } else { 0u32 };
  ```
  `z_t` is back-derived from `constraint_eval / quotient` to make the
  consistency check `quotient * z_t == constraint_eval` pass trivially
  for honest proofs. The comment is honest: *"For soundness, we trust
  the proof's constraint_value and verify quotient * z_t ==
  constraint_eval. If the prover cheated, the Merkle path won't match."*
  **Impact:** a malicious prover with a real Merkle path but a wrong
  constraint_value can construct a `z_t` that satisfies the in-circuit
  check. The native pre-verify catches this in the current pipeline,
  but for a sound in-circuit verifier this is the canonical place to
  break. The real fix computes `z_t = (omega_eval^index)^trace_len - 1`
  in BabyBear arithmetic — ~5 BabyBear muls (15 Generic gates) per query.
- **AIR-specific constraint hard-coding (line 416-424):** the trace
  columns are explicitly extracted as
  `col0=current, col1=sib0, col2=sib1, col3=sib2, col4=position,
  col5=parent`. The constraint `c1 = parent - (current + sib0 + sib1 +
  sib2 + position)` is the `MerkleStarkAir` constraint. **Generalising
  to Effect VM (width 105, many more constraints) is its own
  engineering task** — but cleanly bounded: it's a code generator from
  the AIR's constraint vector to a sequence of BabyBear-mul gate
  emissions.
- **Copy constraints between gadget outputs and consumers** (lines
  219-220, 232-233, 244-245): equality checks at sections C, F, I use
  `emit_generic_gate` with `Wire::for_row(row)` self-loops. The
  computed Merkle root needs a copy constraint *into* the equality
  gate's input slot; today it relies on the witness being filled with
  the correct value and the Generic gate's coefficient check. **A
  malicious witness-stuffing attack here:** fill `witness[0][row] =
  trace_root` rather than the actually-computed Merkle root. The gate's
  coefficient is `[1, 0, 0, 0, 0]` (just enforces `w[0] == 0` if the
  coeffs were configured that way, but here it's an unconstrained pass-through
  to the binding row). This is the same pattern that flagged
  `kimchi_native` as Experimental in `AUDIT-circuit.md` P0-2. **Cost to
  fix:** wire `Wire::new(merkle_section_last_row, 0)` from the
  Merkle path's output slot into `Wire::new(eq_row, 0)`. Mechanical;
  ~50 LOC across the three equality sections.

These four are the **documented shortcuts**. Everything else in
`build_circuit` is a real Kimchi gate emission that the verifier
checks.

### 1.4 `circuit/src/poseidon_stark.rs` — 1570 LOC

The Plonky3 STARK proof system, re-instantiated with Poseidon-over-Fp
Merkle commitments instead of BLAKE3. This is the *enabling* design
choice for option (B): Kimchi has a native Poseidon gate, so verifying
Poseidon-Merkle paths in-circuit costs ~12 rows per hash instead of
~6800 rows for BLAKE3 emulation. **Status: works, used by the bridge
PoC. Not a bottleneck.**

### 1.5 What's NOT in the inventory but exists

- `circuit/src/backends/kimchi_native/` (~9700 LOC) — the
  *circuit-author surface*, not the recursive layer. Same upstream
  crates, same audit caveats (P0-2 copy constraints), but it's not the
  outer layer; it's a dregg-DSL-to-Kimchi-gates compiler. Out of scope
  for this plan except as a source of patterns (`link_wires`,
  `verify_canonical_circuit_hash`) that the verifier circuit should
  adopt.
- Upstream `kimchi`, `poly-commitment`, `mina-curves`, `mina-poseidon`,
  `groupmap` — pinned to `o1-labs/proof-systems#36a8b510` in
  `circuit/Cargo.toml:53-58`. We do not touch upstream; it's a hard
  dependency.

---

## 2. The integration story — how Pickles serves as the outer layer

```
                      dregg's per-cell Effect VM trace
                                   │
                                   ▼
                    Plonky3 STARK proof over BabyBear + FRI
                                   │
                                   ├──── (today: BLAKE3-committed)
                                   ▼
              poseidon_stark::prove_poseidon() re-proves with
              Poseidon-over-Fp Merkle commitments  (poseidon_stark.rs)
                                   │
                                   ▼
                       PoseidonStarkProof, ~48 KiB
                                   │
                                   │   wrap_stark_in_pickles()
                                   ▼   (stark_in_pickles.rs)
                                   │
              ┌────────────────────┴────────────────────┐
              │                                         │
              │   Kimchi circuit                        │
              │   (poseidon_stark_verifier_circuit.rs)  │
              │                                         │
              │   - Re-runs STARK verifier in-circuit:  │
              │     trace Merkle, constraint Merkle,    │
              │     next-trace Merkle, FRI folding,     │
              │     constraint evaluation               │
              │                                         │
              │   ~18,500 rows at 80 queries, depth 4   │
              │   Fits Kimchi domain 2^15               │
              └────────────────────┬────────────────────┘
                                   │
                                   ▼
                  Kimchi proof over Vesta (~5-10 KiB)
                                   │
                                   │   prove_recursive_step()
                                   ▼   (mina/pickles.rs)
                                   │
                  Pickles recursive proof (~5 KiB, constant-size)
                                   │
                                   ▼
                       Composable with other Pickles proofs
                       via compose_wrapped_starks()
```

The output `PicklesWrappedStark` is **constant-size regardless of**
the original STARK proof size, the AIR's width, or the number of
inner verifier rows. This is the property that makes Pickles
attractive for γ.2 Phase 2 aggregation and for cross-chain settlement.

The trust chain:

1. **STARK soundness.** Plonky3's BabyBear+FRI is sound at ~120 bits
   with 80 queries.
2. **Native pre-verify.** `wrap_stark_in_pickles` calls
   `verify_poseidon` before building the Kimchi circuit. A bogus STARK
   proof never gets wrapped. This is defense-in-depth, not the
   primary soundness layer.
3. **In-circuit verify.** The Kimchi circuit's gates *re-run* the
   STARK verifier. **This** is the primary soundness layer for the
   wrapper: even if the native pre-verify is bypassed (e.g. an
   attacker hands you a `PicklesWrappedStark` directly without
   running through `wrap_stark_in_pickles`), the in-circuit verifier
   must accept the inner STARK for the Kimchi proof to be valid.
4. **Kimchi+IPA soundness.** Pasta curves, IPA commitment scheme,
   Fiat-Shamir over Poseidon. ~128 bits classical, ~0 bits PQ.
5. **Pickles recursion.** `create_recursive` threads the IPA
   accumulator forward; final verify batch-checks the chain.

Where this differs from option (A) (`plonky3_recursion_impl.rs`):
option (A) replaces steps 3-5 with another BabyBear STARK
(verifier-as-AIR). The trust chain stays PQ end-to-end at the cost of
larger outer proofs (a STARK is ~48 KiB; a Pickles proof is ~5 KiB)
and a tree-vs-chain topology mismatch (see §5).

---

## 3. The bridge gap — `stark_in_pickles.rs` to production

The four documented shortcuts from §1.3, with concrete fix sketches
and LOC estimates. Files to touch:
`/Users/ember/dev/breadstuffs/circuit/src/poseidon_stark_verifier_circuit.rs`
and minimally
`/Users/ember/dev/breadstuffs/circuit/src/backends/stark_in_pickles.rs`.

### 3.1 Fiat-Shamir transcript replay for `alpha` (and any other challenge)

**Current (line 440-446):** single Fp limb of trace commitment.

**Real shape:** absorb `verifier_index_digest`, `trace_commitment`,
`constraint_commitment` into a Poseidon sponge in-circuit, then squeeze
`alpha`. This mirrors what `poseidon_stark::verify_poseidon` does
natively. Kimchi has native Poseidon gates; one absorption = 12 rows,
one squeeze = 12 rows.

**Estimate:** ~150 LOC, ~50 rows added to the circuit. Pattern:

```rust
// New section in build_circuit, before section J:
//   Absorb trace_commitment (Poseidon gadget, 12 rows)
//   Absorb constraint_commitment (Poseidon gadget, 12 rows)
//   Squeeze alpha (Poseidon output, 1 row binding to existing alpha witness)
//
// And in generate_witness, the alpha value is the squeeze output rather
// than the trace_root limb hack.
```

This unblocks soundness of the constraint random-linear-combination,
which is the soundness boundary for multi-constraint STARKs.

### 3.2 Real `z_t` computation

**Current (line 506-514):** back-derived from `constraint_eval / quotient`.

**Real shape:** compute `z_t = (x^trace_len - 1)` where `x = omega_eval^index`
is the query coset point. In BabyBear arithmetic this is:

```text
z_t_step_1 = omega_eval^index        (precomputed; provided as witness)
z_t_step_2 = z_t_step_1^trace_len    (~log2(trace_len) BabyBear muls)
z_t        = z_t_step_2 - 1          (1 BabyBear sub)
```

For `trace_len = 16` (Effect VM minimum) this is 4 BabyBear muls = 12
Generic gates. We constrain `omega_eval^index` against the proof's
declared query index (Merkle path index already in the circuit's
witness — copy-constrain into the `z_t` chain's input).

**Estimate:** ~200 LOC, ~50 rows per query. At 80 queries this adds
~4000 rows — the verifier circuit grows from ~18,500 to ~22,500 rows,
still fits domain 2^15.

This closes the **most consequential** soundness gap: today's circuit
accepts any (constraint_eval, quotient) pair as long as their product
equals what the prover claimed. After the fix, `quotient` must be the
*actual* quotient of the *actual* `constraint_eval` divided by the
*actual* vanishing polynomial at the query point.

### 3.3 Copy constraints for gadget outputs

**Current (lines 219-220, 232-233, 244-245):** equality gates use
`Wire::for_row(row)` self-loops.

**Real shape:** wire the Merkle path output cell into the equality
gate's input cell. This is mechanical; the pattern lives in
`circuit/src/backends/kimchi_native/mod.rs::link_wires`. Apply
to:
- Section C: `trace_merkle_root_row` → eq input
- Section F: `constraint_merkle_root_row` → eq input
- Section I: `next_trace_merkle_root_row` → eq input
- Section J→K: `constraint_eval_row` → consistency check input
- Section J→K: `quotient_witness_row` → consistency check input
- All BabyBear mul outputs → subsequent BabyBear mul inputs (the
  chained Horner-like structure)

**Estimate:** ~100 LOC, 0 rows added (copy constraints don't add gates,
they wire existing ones).

This is the same fix pattern as the `kimchi_native` P0-2 audit. The
existing `link_wires` helper is the right primitive; we don't need to
invent anything.

### 3.4 Generalise to Effect VM AIR

**Current (line 416-424):** hard-coded to `MerkleStarkAir` (width 6,
specific constraint shape).

**Real shape:** a code generator that consumes the AIR's constraint
vector (already canonicalised — see `circuit/src/effect_vm/constraints/`)
and emits one BabyBear-mul gate sequence per constraint. The constraint
vector is a `Vec<Constraint>` where each `Constraint` is a polynomial
expression in trace columns; the generator walks it to emit muls/adds.

**Estimate:** the *biggest* item in this section. ~1500-2500 LOC.

But it's also the most **bounded** task: the AIR's constraints are
already enumerated in dregg's source; we're not inventing a new IR,
we're consuming an existing one. Effect VM's width is 105; constraint
count is well-defined per Stage-7 (see `STAGE-7-PLUS-DESIGN.md`).

**Crucial framing:** this work is shared with option (A). Option (A)
must also emit a circuit (BabyBear AIR) that evaluates the Effect VM
constraints; the work is "walk the Effect VM constraint vector → emit
verifier circuit gates" in either case. The substrate differs (BabyBear
AIR vs. Kimchi gates) but the *constraint-walker* logic is shared.

**LOC totals for §3:**
- 3.1 Fiat-Shamir: ~150 LOC
- 3.2 `z_t`: ~200 LOC
- 3.3 copy constraints: ~100 LOC
- 3.4 generalisation: ~1500-2500 LOC (deferrable to Effect VM AIR
  binding step — can demo with `MerkleStarkAir` first)

Bridge-without-generalisation: **~450 LOC, 1-2 weeks careful work.**
Bridge-with-generalisation: **~2000-3000 LOC, 4-6 weeks.**

---

## 4. The standalone dual-curve completion

The dual-curve path (`standalone.rs::prove_standalone_dual_curve_wrap`,
`step_verifier.rs`, `wrap_verifier.rs`) is what unlocks **tree-shaped
recursion** for Pickles (multiple Step proofs verified in parallel by
one Wrap proof, instead of one-at-a-time linear chaining).

Reading the module docstrings + the actual function bodies:

### 4.1 What's structurally complete

- `build_step_verifier_circuit` (mod docstring in `step_verifier.rs`):
  Vesta-side Fp arithmetic, Poseidon transcript replay, b(zeta) Horner
  chain, state-transition. Public-input layout matches Pickles spec.
- `build_wrap_verifier_circuit` (mod docstring in `wrap_verifier.rs`):
  Pallas-side Fq arithmetic, EndoMul `bullet_reduce`, CompleteAdd for
  the final IPA equation. EndoMul outputs flow into the assertion gate
  (line 174 in `standalone.rs`: `add_ipa_verifier_copy_constraints`).
- `prove_standalone_dual_curve_wrap` (line 486+ in `standalone.rs`):
  Actually deserializes the step proof, calls `step_kimchi.oracles()`
  and `opening.challenges()` from upstream to derive challenges, maps
  Fp→Fq, generates Pallas witness, builds and proves the wrap circuit.
- `verify_standalone_dual_curve_wrap` (line 904+): Verifies the Pallas
  proof; defers only `batch_dlog_accumulator_check` on the sg
  accumulator MSM. **This matches Mina's production verifier exactly.**

### 4.2 What's incomplete or marked

The module docstring on `standalone.rs` lines 50-58 lists the pending
work for the *single-curve* standalone path:
1. GLV signed-digit encoding in `Scalar_challenge.to_field_checked`
2. EndoMul outputs wired into the assertion gates via copy constraints
3. Precomputed LHS/RHS in tests replaced with in-circuit computation

Reading further (line 14-23): *"The standalone in-circuit IPA verifier
achieves Mina-equivalent verification: bullet_reduce EndoMul gate
outputs flow directly into the final equation assertion. GLV encoding
uses prechallenge bits via glv_encode_for_endomul. The assertion checks
gate-computed LHS == RHS (no precomputed rubber-stamp). The sg MSM is
DEFERRED (by design, same as Pickles)."*

So items (1) and (2) are **done** for the dual-curve path. Item (3) is
done for the dual-curve path (`prove_standalone_dual_curve_wrap` runs
real `oracles()`, no precomputation).

The remaining items by inspection:

- **The `#[allow(deprecated)]` annotation** (lines 41, 282, 385).
  Marks the single-curve `prove_standalone_recursive_step` as deprecated
  in favor of the dual-curve path. **Per `feedback-improve-dont-degrade.md`,
  we should not preserve a deprecated annotation as a stand-in for the
  migration. Either delete the single-curve path entirely (replace
  callers with dual-curve), or remove the annotation if both paths are
  intended to ship.**
- **The `recursive_fold` placeholder** in `pickles.rs:786-860`
  acknowledges itself as scaffolding. Either delete or implement; do
  not preserve.
- **`extract_recursion_challenge` placeholder commitment** in
  `pickles.rs:120-130`. Comment: *"This affects the intermediate
  sponge state, not the final accumulator check."* In a *linear chain*
  this is benign — the verifier re-derives. In a *tree* (Phase 2
  aggregation), intermediate sponge states matter for cross-branch
  binding. Either fix or document the tree-mode incompatibility.
- **Integration with `wrap_stark_in_pickles`**: today the bridge uses
  the assisted-recursion path (`pickles::prove_recursive_step`). The
  dual-curve path is not wired into `wrap_stark_in_pickles`. **The
  decision:** which path does the bridge produce?
  - Assisted: simpler bridge, larger external verifier work (full
    `kimchi::verifier::verify`).
  - Dual-curve: more complex bridge, minimal external verifier work
    (`batch_dlog_accumulator_check` only). This is the Mina production
    shape.

**Concrete blockers vs. polish:**

| Item | Type | Estimate |
|------|------|---------:|
| Remove `#[allow(deprecated)]` annotations | polish | <1 hour |
| Delete or implement `recursive_fold` placeholder | polish | 1 day |
| Fix `extract_recursion_challenge` placeholder commitment | soundness | 2 days |
| Wire dual-curve path into `wrap_stark_in_pickles` | feature | 1 week |
| Tree-shape `compose_wrapped_starks` (k-ary instead of chain) | feature | 1 week |
| Audit (~AUDIT-mina-recursion.md, parallel to AUDIT-circuit.md P0-2) | audit | 1 week |

Total: **~2-3 weeks** to bring the dual-curve path from "tests pass"
to "production-ready substrate for γ.2 Phase 2."

---

## 5. Pickles vs. plonky3-recursion comparison

The decision is **not** either-or for dregg long-term. Both have
distinct roles. Below: a comparison of when each wins.

| dimension | Pickles outer | plonky3-recursion outer |
|---|---|---|
| **proof size** | ~5-10 KiB constant | ~48 KiB constant (after one recursion) |
| **outer security** | ~128-bit classical (Pasta IPA / dlog) | ~120-bit PQ-resilient (BabyBear+FRI) |
| **trusted setup** | none (IPA, transparent) | none (FRI, transparent) |
| **topology** | linear chain (assisted), or tree (dual-curve, more work) | tree-native (k-ary fan-in is natural in an AIR) |
| **maturity in our tree** | bridge PoC works end-to-end for MerkleStarkAir; dual-curve structurally complete; needs Effect VM generalisation | recursion works end-to-end for `P3MerklePoseidon2Air`; needs Effect VM generalisation |
| **upstream stability** | o1-labs single-commit pin (~36a8b510); thin Rust docs; we are the Rust port of Pickles wrapping | our own fork `emberian/plonky3-recursion#c14b5fc0`; we control upgrade pace |
| **external consumers** | Mina mainnet (and we can settle proofs on Mina via Pickles) | RISC Zero / SP1 / Stwo (we share the recursion-AIR pattern) |
| **PQ posture** | inner STARK is PQ; outer Pasta is classical; quantum break of Pasta invalidates the outer wrap | PQ end-to-end |
| **engineering cost to Effect VM** | bridge gap (§3): ~450 LOC core + ~1500-2500 LOC constraint-walker | recursion generalisation: ~1500-2500 LOC constraint-walker, no bridge gap |

### When Pickles wins

1. **Cross-chain settlement.** A Pickles proof is what Mina (and curve-based
   L1s in general) can verify. If dregg ever needs to anchor a commit
   on Mina, Cardano, or another curve-based chain, Pickles is the
   substrate. This is the "production-proven, smaller proofs"
   regime — same shape RISC Zero ships with their Groth16-wrap for
   Ethereum settlement.
2. **Constant-size proofs.** ~5 KiB regardless of how many STARKs
   were aggregated. For a `WitnessedReceipt` shipped over a slow
   transport or stored long-term, this is the substantial win.
3. **Composability across heterogeneous AIRs.** Pickles is agnostic
   to what the underlying STARK proves; the wrap circuit is the same.
   Mixing Effect VM proofs with predicate-eval proofs in a single
   aggregation is straightforward.
4. **Bilateral / cross-cell binding (γ.2 Phase 2).** Per
   `STAGE-7-GAMMA-2-PI-DESIGN.md §8`, the aggregation AIR consumes N
   inner PIs and proves bilateral consistency. A Pickles wrap of N
   STARKs has *all N PIs in the wrapping state-transition*; the
   aggregation logic can be lifted into the wrap circuit's state
   transition rather than a separate AIR. **Specifically:**
   `compose_wrapped_starks` already chains state-transition hashes —
   extending this to enforce bilateral PI agreement is a state-hash
   schema change, not a new substrate.

### When plonky3-recursion wins

1. **PQ-resilient capability proofs.** A capability proof issued today
   that must hold up over decades shouldn't depend on Pasta
   classical security. Internal recursion stays STARK-in-STARK.
2. **Tree-native topology.** The call_forest pattern from
   `STAGE-7-GAMMA-AGGREGATION-DESIGN.md §C` is naturally tree-shaped;
   plonky3-recursion gives it for free at the cost of larger
   intermediate proofs.
3. **Custody of the stack.** Our own fork; we own the upgrade pace
   and the bug-fix flow.
4. **Transparency by default.** No curve-based assumption anywhere in
   the trust chain.

### The long-term position

`KIMCHI-SURVEY.md §9` recommends option (A) as primary + option (B) as
**export path** for cross-chain settlement. This is the same
architecture RISC Zero uses (STARK recursion internally, SNARK wrap
externally). The two lanes are not mutually exclusive; they serve
distinct roles:

- **Internal aggregation** (cross-cell turn-level proofs,
  witnessed-receipt-chain folding): plonky3-recursion.
  *Tree-shaped, PQ, transparent end-to-end.*
- **External anchoring** (settle a dregg commit on Mina; export a
  compressed proof of a months-long turn history to a thin verifier):
  Pickles wrap of the final aggregated STARK. *5 KiB constant size,
  cross-chain compatible.*

This plan supports that long-term position. The Pickles lane is the
**export substrate**; the Plonky3 lane is the **internal substrate**.
They share the constraint-walker work and the AIR-shape work; they
differ on the outer substrate.

---

## 6. Migration story — γ.2 Phase 2 + sovereign-witness Phase 2 via Pickles

### 6.1 γ.2 Phase 2 substrate

Per `STAGE-7-GAMMA-2-PI-DESIGN.md §8`, Phase 2 wants:

> An aggregation AIR that takes N inner Effect VM proofs (recursive
> verification), enforces bilateral consistency over their PIs, and
> emits a single proof with reduced PI: `TURN_HASH`,
> `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`, `PREVIOUS_RECEIPT_HASH`,
> `BILATERAL_CONSISTENT`.

**Via Pickles:** the `compose_wrapped_starks` function (which today
chains pre/post hashes) becomes the substrate. Instead of binding only
`(trace_commitment_a, trace_commitment_b, "composed")`, the
composition step binds the *full PI sets* of both children, and the
state transition circuit enforces the bilateral consistency rules from
`STAGE-7-GAMMA-2-PI-DESIGN.md §4` (sum-check, transfer_id match,
direction agreement) in-circuit.

API shape (proposed addition to
`/Users/ember/dev/breadstuffs/circuit/src/backends/stark_in_pickles.rs`):

```rust
/// Compose two wrapped STARKs with bilateral-consistency enforcement.
/// This is γ.2 Phase 2's substrate when both proofs are bilateral
/// halves of the same effect.
pub fn compose_bilateral_pair(
    sender_side: &PicklesWrappedStark,
    receiver_side: &PicklesWrappedStark,
    bilateral_kind: BilateralKind, // Transfer | Grant | Introduce
) -> Result<PicklesWrappedStark, WrapError> {
    // 1. Verify both inner Pickles proofs.
    // 2. Build a state-transition circuit that:
    //    a. Absorbs both sides' γ.2 PIs.
    //    b. Re-derives the canonical bilateral_id from the surface inputs.
    //    c. Asserts both sides emitted matching bilateral_id in PI.
    //    d. Asserts directions agree (1 + 0 = 1 for Transfer; analogous for others).
    //    e. Emits the *reduced* PI set as post_state_hash.
    // 3. Wrap in a Pickles recursive step using `prove_recursive_step`
    //    with both pickles_proofs as previous (this needs k-ary chaining,
    //    or equivalently a sequence of two chain steps).
    ...
}

/// Aggregate N wrapped STARKs from one turn into a single proof.
/// Reduces N inner PIs to a single (TURN_HASH, EFFECTS_HASH_GLOBAL,
/// ACTOR_NONCE, PREVIOUS_RECEIPT_HASH, BILATERAL_CONSISTENT).
pub fn aggregate_turn_bundle(
    per_cell_wraps: &[PicklesWrappedStark],
    schedule: &BilateralSchedule,
) -> Result<TurnAggregateProof, WrapError> {
    // Two-level fold:
    //   inner: compose_bilateral_pair for each (sender, receiver) in the schedule
    //   outer: chain-fold the bilateral-pair results
    ...
}
```

The state-transition circuit is a small Kimchi circuit (Poseidon hashes
+ Generic gates for arithmetic), nothing as heavy as the STARK
verifier. **Estimate: ~800 LOC + an `AUDIT-mina-aggregation.md`
spelling out the bilateral_id derivation.**

### 6.2 Sovereign-witness Phase 2

`SOVEREIGN-WITNESS-AIR-DESIGN.md` is its own AIR. Pickles serves it the
same way: wrap each sovereign-witness STARK, compose across witnesses,
get a single proof.

The compatibility seam: sovereign-witness's PI layout must be wrapped
into the Pickles state-transition the same way Effect VM's is. The
`PicklesWrappedStark::public_inputs: Vec<u32>` field already supports
arbitrary PI; the binding hash in `wrap_stark_in_pickles` line 264-274
already absorbs all PI bytes. No code change needed at the wrapping
layer; the change is in the AIR-side (which is sovereign-witness's
problem, not Pickles's).

### 6.3 What the migration doesn't break

- Inner Effect VM AIR: unchanged. Pickles wraps it as-is.
- Per-cell `WitnessedReceipt`: stays the same. Phase 2 layer *adds*
  an aggregation proof; doesn't replace per-cell proofs.
- Verifier API: `verify_proof_carrying_turn_bundle` gains a new
  branch ("if turn has aggregation proof, verify it instead of N
  per-cell proofs"). Backwards-compatible at the API layer (per
  `feedback-improve-dont-degrade.md`, we don't need backwards-compat,
  but the migration is structurally additive anyway).

---

## 7. Compatibility with VK-as-re-execution-recipe

The parallel design lane producing `VK-AS-RE-EXECUTION-RECIPE.md`
treats the AIR's verification key (VK) as a *canonical
re-execution recipe* — the bytes that fully determine the
verifier's behavior, suitable for content-addressing,
reproducible-build proofs, and trusted-by-construction
verification flows.

The seam between Pickles and VK-as-recipe:

### 7.1 What Pickles compresses

A `PicklesWrappedStark` binds, in its state-transition hash:
- `air_name` — string identifier, today; under VK-as-recipe, replaced
  by `vk_hash` (a Poseidon hash of the canonical AIR bytes).
- `public_inputs` — the statement.
- `trace_commitment`, `constraint_commitment` — the prover's
  commitments.

Today the binding is by `air_name` as a string. **The compatibility
seam:** swap `air_name` → `vk_hash` in:
- `wrap_stark_in_pickles`, lines 264-274 (the pre-state binding hash
  absorbs `air_name.as_bytes()` today; should absorb `vk_hash` 32
  bytes).
- `compose_wrapped_starks`, lines 394-414 (same pattern).
- `PicklesWrappedStark::air_name: String` → `vk_hash: [u8; 32]`.

Effort: ~50 LOC mechanical change once VK-as-recipe lands its canonical
hash.

### 7.2 What VK-as-recipe gains from Pickles

The VK-as-recipe doc (per the parallel lane) wants compression of the
canonical bytes — so a verifier can prove *"I verified this
re-execution"* without shipping the full AIR bytes.

**The compression Pickles provides:** a `PicklesWrappedStark` is ~5
KiB, regardless of the AIR. If a verifier produces such a wrap, the
ship-size is dominated by the wrap, not the AIR. The `vk_hash` is
already in the wrap's state-transition; the AIR bytes themselves don't
need to ship.

The compatibility statement: **a Pickles wrap is the natural
compression of the (AIR, trace, proof) tuple under the
VK-as-recipe model.** The wrap is the proof *that* the recipe was
followed correctly; the recipe is identified by `vk_hash`; the recipe
itself is content-addressed and fetchable separately.

### 7.3 What needs to land first

The VK canonical hash function (a Poseidon hash over the AIR's
constraint vector + column count + lookup tables). Without this,
`vk_hash` is undefined.

This is the VK-as-recipe lane's deliverable, not ours. The Pickles
lane's commitment: **once VK-as-recipe lands the canonical hash,
Pickles substitutes it for `air_name` in <1 day of work.** This is a
named seam, not a hard dependency for the rest of the Pickles work.

---

## 8. Concrete next-step lane — 1-2 week starter

**Goal:** demonstrate `Pickles verifies a Plonky3 STARK end-to-end` with
the four shortcuts in §1.3 closed. Demonstrate is the operative word:
we want a test that breaks if any of the soundness shortcuts return.

### 8.1 Deliverable

A new test in
`/Users/ember/dev/breadstuffs/circuit/src/backends/stark_in_pickles.rs`:

```rust
#[test]
fn test_stark_in_pickles_full_security_adversarial() {
    // 1. Generate a real STARK + wrap it with full-security config (80 queries).
    // 2. Verify the wrap. Assert true.
    // 3. ADVERSARIAL CASE A: tamper with the proof's constraint_value.
    //    Today (PoC): the back-derived z_t compensates, in-circuit check passes.
    //    After fix (§3.2): the in-circuit z_t computation rejects.
    // 4. ADVERSARIAL CASE B: replace the proof's trace_commitment with a different
    //    Fp value (e.g., flip one limb).
    //    Today (PoC): alpha derived from limbs changes; if it lands on the same
    //    constraint outcome by luck, the check passes. (Probability: 1/p ≈ 1/2^31.)
    //    After fix (§3.1): the full Fiat-Shamir replay derives a different alpha,
    //    constraint check fails deterministically.
    // 5. ADVERSARIAL CASE C: replace the witness for the Merkle root output cell
    //    with the public trace_commitment directly (skipping the actual
    //    Merkle computation). Bypass attack.
    //    Today (PoC): without copy constraints, the witness-stuffing succeeds.
    //    After fix (§3.3): the copy constraint forces witness coherence.
}
```

This test **fails today and passes after the §3 fixes land.** The test
is the acceptance criterion; the design doc is the work plan.

### 8.2 Files to touch

Bounded scope; no creep into `effect_vm.rs` or `plonky3_recursion_impl.rs`.

1. `/Users/ember/dev/breadstuffs/circuit/src/poseidon_stark_verifier_circuit.rs`
   - **§3.1 Fiat-Shamir:** ~150 LOC new gate emissions + witness fill
     in `build_circuit` and `generate_witness`.
   - **§3.2 `z_t`:** ~200 LOC new BabyBear-mul chain for
     `(omega_eval^index)^trace_len - 1`.
   - **§3.3 copy constraints:** ~100 LOC `link_wires`-style fixes at
     sections C, F, I, J→K, J→J.
2. `/Users/ember/dev/breadstuffs/circuit/src/backends/stark_in_pickles.rs`
   - Add the adversarial test (above).
   - Add `WrapConfig::production()` that sets `num_queries = 80` and
     uses the now-sound circuit.
3. *(Optional)* `/Users/ember/dev/breadstuffs/circuit/src/backends/mina/pickles.rs`
   - Delete `recursive_fold` placeholder body (line 786-860), replace
     with `unimplemented!("use compose_wrapped_starks for n-ary composition")`
     or wire it through to a real impl.
   - Fix `extract_recursion_challenge` placeholder commitment
     (line 120-130) — replace zero commitment with the actual
     reconstructed public-input commitment.

### 8.3 Expected blockers

1. **Poseidon sponge state threading.** The in-circuit transcript replay
   requires the same Poseidon parameters the native verifier uses.
   `mina_poseidon::poseidon::ArithmeticSponge` is used both natively
   (in `poseidon_stark.rs`) and in the circuit (via the Poseidon gate);
   the parameters are identical (`PlonkSpongeConstantsKimchi`). Should
   work; verify by comparing a native squeeze to an in-circuit squeeze
   in a unit test before integrating.
2. **BabyBear mul cost at 80 queries.** Adding ~50 rows of BabyBear muls
   per query for `z_t` computation adds ~4000 rows total at 80 queries.
   Current ~18,500 rows → ~22,500 rows. Still under 2^15 = 32768.
   Confirm by running `estimate_wrap_rows(4, 6, 4, 80)` after the
   changes and asserting it stays under 32K.
3. **Copy-constraint conflicts with Poseidon gadget internals.** Kimchi's
   Poseidon gadget uses internal wires for its 11 rows. The Zero/output
   row at the gadget end is where copy constraints attach; the existing
   `link_wires` helper handles this. The standalone path already does
   this correctly (`add_ipa_verifier_copy_constraints`); the same
   pattern applies.
4. **Witness-determinism for the adversarial test.** Test case C
   requires forging a witness. The `prove` function regenerates the
   witness from `proof`, so we can't easily inject a forged witness via
   the public API. Either (a) add a `prove_with_witness_override` test
   helper, or (b) tamper with the proof bytes post-serialization in a
   way that produces an inconsistent witness — but that's a different
   attack vector. Recommend (a) for crispness.

### 8.4 Out of scope for this 1-2 week lane

- **Effect VM AIR generalisation (§3.4).** Stays at `MerkleStarkAir`.
  The point of this lane is to close the *soundness* gaps, not the
  *generality* gap.
- **Dual-curve integration into the bridge (§4).** Stays on assisted-recursion
  for now. Dual-curve is its own lane.
- **γ.2 Phase 2 bilateral composition (§6).** Substrate-level work; this
  lane delivers the substrate, not the application.
- **VK-as-recipe canonical hash integration (§7).** Waits on the VK
  lane to land its hash function.

### 8.5 Definition of done

1. `test_stark_in_pickles_full_security_adversarial` passes
   (after the §3 fixes).
2. `test_wrap_stark_in_pickles_minimal` and existing tests still pass.
3. `estimate_wrap_rows(4, 6, 4, 80) < 32768` confirmed.
4. The four `SOUNDNESS NOTE` / *"In a full implementation..."* /
   *"For soundness, we trust..."* comments in
   `poseidon_stark_verifier_circuit.rs` are deleted (the implementation
   no longer needs the caveat).
5. An `AUDIT-mina-stark-in-pickles.md` written documenting the
   completed soundness fixes and remaining work (Effect VM
   generalisation, dual-curve wiring, recursion-fold real impl).

---

## 9. Summary of the plan

| section | task | LOC | timeline | status |
|---|---|---:|---|---|
| §3.1 | In-circuit Fiat-Shamir for `alpha` | ~150 | 3 days | starter lane |
| §3.2 | Real `z_t = (omega^idx)^n - 1` | ~200 | 3 days | starter lane |
| §3.3 | Copy constraints at gadget outputs | ~100 | 2 days | starter lane |
| §3.4 | Effect VM AIR generalisation | ~1500-2500 | 4-6 weeks | deferred |
| §4 | Dual-curve integration into bridge | ~1000 | 2-3 weeks | deferred |
| §4 | Remove `#[allow(deprecated)]` annotations | <50 | <1 day | starter lane (cleanup) |
| §4 | Delete or implement `recursive_fold` placeholder | varies | 1 day | starter lane (cleanup) |
| §6 | γ.2 Phase 2 bilateral composition substrate | ~800 | 2 weeks | post-starter |
| §7 | VK-as-recipe `vk_hash` substitution | ~50 | <1 day | post-VK-lane |

**Starter lane (1-2 weeks): §3.1 + §3.2 + §3.3 + §4 cleanups.**
~500 LOC, soundness-closing, demonstrable by adversarial test.

**Mid-term (1-2 months): §3.4 + §4 dual-curve integration + §6
Phase 2 substrate.** This is the path to "Pickles is the production
outer layer for γ.2 Phase 2 + sovereign-witness Phase 2."

**Long-term position: §7 + cross-chain export.** Once VK-as-recipe
lands the canonical hash, Pickles becomes the *export* substrate while
plonky3-recursion remains the *internal* substrate. Two lanes, one
architecture, distinct roles.

---

## 10. What this plan does not commit to

- **Pickles becoming primary for internal recursion.** Per
  `KIMCHI-SURVEY.md §9`, that role belongs to plonky3-recursion.
  Pickles is the export + bilateral-composition + cross-chain substrate.
- **Throwing away `plonky3_recursion_impl.rs` work.** Orthogonal.
  Both lanes share the constraint-walker work (§3.4) and the AIR-shape
  work; both must touch Effect VM constraints in the same way.
- **A specific cross-chain target.** Mina is the obvious one (Pickles
  is Mina's native verifier), but Cardano-via-Midnight (per
  `project-midnight-strategy.md`) and other curve-based L1s are
  candidates. The bridge produces a `PicklesWrappedStark`; what
  chain consumes it is downstream.
- **A timeline for §3.4 specifically.** Effect VM AIR generalisation
  is shared with the plonky3-recursion lane and depends on the
  constraint-walker work landing in either lane. Coordinated work.

---

## 11. Final note on improve-don't-degrade

The Pickles tree contains several "structurally complete but soundness
caveats" markers (the four shortcuts in §3, the `#[allow(deprecated)]`
annotations in §4, the placeholder bodies in `pickles.rs`). Per
`feedback-improve-dont-degrade.md`, **none of these should be preserved
as workarounds**. The response is to close the gap, not to gate
callers around the gap. This plan's starter lane is precisely that
response: ~500 LOC, soundness-closing, demonstrable.

The deferred items (§3.4, §4 dual-curve integration, §6 Phase 2
substrate) are larger but still bounded; each has a named file, a LOC
estimate, and an acceptance criterion. None of them is research; all
are engineering on shapes we already understand.

Pickles is closer to production-ready than the survey's tone suggests.
The bridge works end-to-end today; the question is at what *security
level*. This plan is the work between "PoC" and "audit-grade."
