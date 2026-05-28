# Kimchi/Pickles vs. Plonky3 verifier-AIR — recursive aggregation survey

Written 2026-05-24, branch `main`. Read-only inventory of the code we already
have and what each of the two options would actually require, as a basis for
choosing the outer recursive layer for dregg's per-cell Effect VM STARKs.

The question framed in `THOUGHTS-AND-DREAMS.md` §Q1 / §3:

> Given N per-cell STARK proofs over BabyBear+FRI, can we produce one proof
> attesting to all N? (A) fix `circuit/src/plonky3_verifier_air.rs` from a
> stub into a real verifier-as-AIR — stays transparent end-to-end. (B) wrap
> with Kimchi/Pickles — production-proven recursion at the cost of a
> non-transparent outer curve substrate.

Both options need the same set of primitives (Poseidon2 emulation, FRI
verification, Merkle paths) but in different substrates. The relevant
question is which substrate's primitives are closer to "ready" in our
codebase today.

---

## 1. What Kimchi code do we already have?

There are **three** distinct Kimchi-flavoured trees under `circuit/src/`,
each at a very different maturity level, gated behind the `mina` feature
(which is in the default feature set):

### 1.1 `circuit/src/backends/kimchi_native/` — ~9 700 LOC

This is the largest of the three. It is the **circuit-author surface**: a
collection of native Kimchi circuits that re-prove dregg's per-statement
predicates using Pasta/Vesta + IPA, mirroring shape-for-shape what the
BabyBear STARK backend proves.

| file                 |  LOC  | purpose                                                        |
|----------------------|------:|----------------------------------------------------------------|
| `mod.rs`             | 1 888 | crate-shared types, `KimchiNativeBackend`, `verify_kimchi_proof`, copy-constraint helper `link_wires` |
| `dsl_backend.rs`     | 2 536 | translates generic DSL constraint descriptors → Kimchi gates (Generic/Poseidon); `prove_dsl_kimchi` / `verify_dsl_kimchi` |
| `derivation.rs`      | 1 740 | Datalog rule-application Kimchi circuit                        |
| `tests.rs`           | 2 202 | tests                                                          |
| `predicates.rs`      | 1 195 | arithmetic / relational / temporal / compound predicate gates  |
| `presentation.rs`    |   915 | full composed authorization proof                              |
| `from_dsl.rs`        |   824 | adapter from the `dregg-dsl` IR                                |
| `fold.rs`            |   686 | fold-step (capability attenuation) circuit                     |
| `non_membership.rs`  |   491 | accumulator-polynomial non-revocation                          |
| `ivc.rs`             |   281 | bounded-depth IVC composition                                  |

It builds on the upstream o1-labs crates (`kimchi`, `poly-commitment`,
`mina-curves`, `mina-poseidon`, `groupmap`, all pinned to
`o1-labs/proof-systems#36a8b510` — see `circuit/Cargo.toml:53-58`). It is the
**consumer** of `dregg-dsl`'s `gen_kimchi` module:

- `dregg-dsl/src/gen_kimchi.rs` (250 LOC) is a code-generator (proc-macro
  helper) that emits a `KimchiCircuitDescriptor` from the IR.
- That descriptor is rebuilt at runtime via the
  `kimchi_native::dsl_backend::prove_dsl_kimchi(desc, trace, public_inputs)`
  path, which converts the abstract descriptor into actual
  `kimchi::CircuitGate` rows and drives `kimchi::ProverProof::create`.

Soundness status: the module-level doc-comment opens with a **`UNSAFE FOR
PRODUCTION`** banner (audit P0-2, 2026-05-23). Most binding gates were
written with `Wire::for_row(r)` self-loops and lack copy constraints between
gadget outputs and downstream consumers — the gate-level equality holds for
that one row, but a Poseidon gadget output computed 30 rows earlier is not
forced into the row that "checks" against it. `link_wires` and
`verify_canonical_circuit_hash` exist as the future fix, but the audit lists
multiple still-vacuous sites. The whole module is downgraded to
`ProofTier::Experimental` (see `circuit/src/proof_tier.rs:154`,
`kimchi_native_tier()`).

What this code **does** right today, independent of the soundness issue:

- Generates and verifies a real Kimchi proof for each dregg predicate over
  Vesta (~5-10 KiB, ~1-2s prove time).
- Round-trips through the same upstream `kimchi::verifier::verify` that
  Mina uses on-chain.

What it does **not** do:

- Recursively verify any other proof. It is a circuit-author surface only.

### 1.2 `circuit/src/backends/mina/` — ~5 800 LOC, *recursive layer*

This is the recursive-aggregation half. Same upstream crates. Layout:

| file               |  LOC  | purpose                                                      |
|--------------------|------:|--------------------------------------------------------------|
| `mod.rs`           |   628 | shared types: Pallas/Vesta sponges, Poseidon-Merkle helpers  |
| `pickles.rs`       |   875 | **assisted-recursion** path — wraps `kimchi::ProverProof::create_recursive`, extracts `RecursionChallenge` per step, threads it forward |
| `ipa_verifier.rs`  | 1 144 | partial in-circuit IPA verifier (EndoMul + CompleteAdd over Vesta — but Vesta-points-in-Vesta-circuit fail, see step_verifier.rs) |
| `step_verifier.rs` |   729 | dual-curve **Step circuit** (Vesta, scalar = Fp) — Fiat-Shamir + b(zeta), defers EC ops |
| `wrap_verifier.rs` | 1 151 | dual-curve **Wrap circuit** (Pallas, scalar = Fq) — performs IPA `bullet_reduce` over Vesta points natively |
| `standalone.rs`    | 1 092 | "Mina-equivalent" path — in-circuit IPA except the sg MSM (deferred to a `batch_dlog_accumulator_check`) |
| `glv.rs`           |   653 | GLV signed-digit encoding for EndoMul                        |
| `tests.rs`         | 1 450 | tests                                                        |

Two distinct recursion strategies are implemented here:

- **Assisted recursion (`pickles.rs`)** — *the production path today.* Each
  step proves a Poseidon-binding of `(pre_state, post_state, step_count,
  prev_accumulated)`, calls `ProverProof::create_recursive` with the
  previous step's `RecursionChallenge`, and extracts a new
  `RecursionChallenge` for the next step. The IPA accumulator is carried
  in the public inputs; the external verifier runs full
  `kimchi::verifier::verify`, which batch-checks all accumulated IPA
  commitments in a single MSM. The state-transition circuit itself is
  *just* a Poseidon hash binding — it does not encode anything about the
  inner proof's constraints.
- **Mina-equivalent recursion (`standalone.rs` + dual-curve
  step/wrap)** — verifies everything in-circuit *except* the sg accumulator
  MSM. The external verifier only does `batch_dlog_accumulator_check`. This
  is what Mina's Pickles actually does. Status, per the module docstring:
  step/wrap are "structurally complete (correct gate layout, correct
  curve)" but the standalone path still needs (1) full GLV signed-digit
  encoding in `Scalar_challenge.to_field_checked`, (2) EndoMul outputs
  wired into the assertion gates via copy constraints, (3) precomputed
  LHS/RHS in tests replaced with in-circuit computation.

### 1.3 `circuit/src/backends/stark_in_pickles.rs` + `circuit/src/poseidon_stark*.rs` — ~3 200 LOC

This is the **piece directly relevant to option (B)**. The architecture
(quoting the module-level docstring at `stark_in_pickles.rs:1-60`):

```text
BabyBear STARK proof (PoseidonStarkProof, Poseidon-committed, ~48 KiB)
    | [Kimchi verifier circuit verifies STARK in-circuit]
Kimchi proof (PoseidonStarkKimchiProof, ~5 KiB, single-step)
    | [Pickles recursive wrapping for constant-size + composability]
Pickles recursive proof (~5 KiB, constant-size, recursively composable)
```

The key design trick: the inner STARK is re-proven with Poseidon-over-Fp
Merkle commitments instead of BLAKE3 (in `poseidon_stark.rs`, 1 540 LOC).
Because Kimchi has native Poseidon gates, the in-circuit verifier needs
only ~12 rows per Merkle hash instead of ~6 800 rows for BLAKE3 emulation.

The verifier circuit itself lives in
`circuit/src/poseidon_stark_verifier_circuit.rs` (1 407 LOC). It already
contains:

- Per-query gadgets for trace, constraint, and next-trace Merkle paths
  (Sections A-I of `build_circuit`, lines 207-245).
- BabyBear modular multiplication via 3 Generic gates (Section J, lines
  247-253; the BabyBear-in-Fp encoding is documented in the file's design
  notes — BabyBear's 31-bit modulus trivially embeds into the ~255-bit
  Pasta scalar field).
- A constraint-consistency check (Section K, lines 255-258).
- Per-layer FRI folding (Section L, lines 260-275: Poseidon Merkle leaf +
  path + 1 BabyBear mul + 1 addition gate).

There is a `WrapConfig` with `num_queries`: default 1 (testing), or 80 for
"full security". The 80-query path is estimated at ~18 500 rows for depth
4 — fits domain 2^15.

**Important caveats about the current implementation:**

- The constraint evaluation is hard-coded to `MerkleStarkAir` shape
  (positions 0-5: `current/sib0/sib1/sib2/position/parent` — see lines
  416-424). Generalising to arbitrary AIRs is its own engineering task.
- The Fiat-Shamir `alpha` challenge is derived from a single limb of the
  trace commitment (lines 442-446) rather than from a full sponge replay.
  The comment is honest: *"In a full implementation this comes from
  Fiat-Shamir transcript replay."*
- `z_t` (the vanishing polynomial evaluation) is computed
  as `constraint_eval / quotient` (lines 506-514) — i.e. picked to make
  the consistency check pass for honest provers. The comment again is
  honest: *"For soundness, we trust the proof's constraint_value and
  verify quotient * z_t == constraint_eval. If the prover cheated, the
  Merkle path won't match."* This is **not** how a sound STARK verifier
  computes `z_t`; the real computation is `(x^trace_len - 1)` evaluated at
  the FRI query coset, which the circuit must itself enforce.
- The witness-generation paths exist for all the gadgets, but the same
  unsound-without-copy-constraints issue from §1.1 applies here too —
  many gates are still self-routed.

So the existing `stark_in_pickles.rs` plumbing is the **skeleton** of
option (B), with the same kind of "structurally complete but soundness
gaps" caveat that the rest of the Kimchi tree carries.

### 1.4 Summary of Kimchi consumption

```
┌──────────────────────────────────────────────────────────────────┐
│ dregg-dsl / gen_kimchi.rs    ── (codegen) ──→ KimchiCircuitDescriptor │
│                                                       │            │
│                                                       ▼            │
│ circuit/src/backends/kimchi_native/                                │
│   dsl_backend.rs (descriptor→gates, prove/verify)                  │
│   derivation/fold/non_membership/predicates/presentation/ivc      │
│   ─ ProofTier::Experimental, P0-2 soundness gap (no copy consts)  │
│                                                                    │
│ circuit/src/backends/mina/                                         │
│   pickles.rs   ─ assisted recursion (production path, OPERATIONAL)│
│   standalone.rs + step_verifier.rs + wrap_verifier.rs              │
│                ─ Mina-equivalent dual-curve path (incomplete)     │
│   ipa_verifier.rs ─ partial in-circuit IPA                         │
│                                                                    │
│ circuit/src/backends/stark_in_pickles.rs +                         │
│ circuit/src/poseidon_stark.rs +                                    │
│ circuit/src/poseidon_stark_verifier_circuit.rs                     │
│   ─ the bridge: Plonky3 STARK → Kimchi verifier circuit → Pickles  │
│   ─ MerkleStarkAir-only, single-AIR proof of concept              │
└──────────────────────────────────────────────────────────────────┘
```

All of this is gated behind `feature = "mina"` (in the default set). All
upstream Kimchi crates are pinned to a single o1-labs commit:
`o1-labs/proof-systems#36a8b510`.

---

## 2. What does our Kimchi backend prove today?

Three distinct surfaces:

### 2.1 Circuit-author surface (works, audit-flagged)

`kimchi_native` proves the same statements the BabyBear STARK proves:

- **Derivation** (`prove_derivation`): a Datalog rule application —
  *"given rule R and body facts F_1..F_n committed under state_root, R
  derives a fact under substitution σ."*
- **Fold step** (`prove_fold`): a capability-attenuation step removing
  a set of fact hashes from an old → new state root.
- **Non-membership** (`prove_non_membership`): an element-not-in-set proof
  against a polynomial-accumulator root.
- **Predicates** (arithmetic / relational / temporal / compound): the four
  caveat predicate families from dregg-dsl.
- **Presentation**: a full composed authorization proof.
- **Generic DSL constraint** (`prove_dsl_kimchi`): anything emitted by
  dregg-dsl as a `CircuitDescriptor` — equality, polynomial degree ≤ 2,
  PI binding, gated, transition, conditional-nonzero, AtLeastOne. Hash
  gates are marked `TODO`.

A real Kimchi proof is generated and a real `kimchi::verifier::verify`
runs. The audit caveat is that copy constraints are missing from many
binding gates; a malicious prover can drop the "gadget output → binding
gate input" wire. The tier is downgraded to Experimental
(`proof_tier.rs:154`); the comment is explicit that this tree is **not
to be used to gate any authorization decision until copy constraints
are wired up and re-audited.**

### 2.2 Recursive aggregation, assisted (works)

`pickles::prove_recursive_step` produces a Kimchi proof of a Poseidon
state-transition binding *together with* the `RecursionChallenge`
extracted from the previous step's IPA opening. `verify_recursive_proof`
runs the full `kimchi::verifier::verify`, which absorbs the carried
challenges into Fiat-Shamir and batch-checks the entire chain in one
MSM. This is the same "assisted recursion" pattern (Halo §3.2) Mina
itself used pre-Pickles.

**Crucial gap for option (B):** the state-transition circuit binds *only*
`pre_hash → post_hash` via Poseidon. It does not encode anything about
the inner Plonky3 STARK proof's contents. The composition is sound only
because each step's pre/post hash is independently verifiable. There is
no "this Pickles proof attests that the inner STARK was valid" — that
requires either (a) running the STARK verifier in-circuit, or
(b) running the STARK verifier natively *before* wrapping (which is
what `stark_in_pickles::wrap_stark_in_pickles` does — but then the
Pickles proof's verifier only attests that the wrapper-circuit was
satisfied, not that the original STARK was sound).

### 2.3 STARK-in-Pickles bridge (proof-of-concept, single AIR)

`wrap_stark_in_pickles(stark_proof, air, public_inputs, config)`
(`stark_in_pickles.rs:216-307`) does the full pipeline:

1. Verifies the STARK natively (defense in depth).
2. Builds the verifier circuit (1 or 80 queries).
3. Generates a Kimchi proof of the verifier circuit.
4. Self-verifies the Kimchi proof.
5. Wraps it in a Pickles recursive step whose pre/post hashes commit to
   `(air_name, public_inputs, trace_commitment)` and
   `(kimchi_proof_bytes, constraint_commitment, "verified")`.

The result is a `PicklesWrappedStark` containing a `PicklesRecursiveProof`
that the verifier checks via `verify_recursive_proof`. **For a single
`MerkleStarkAir` proof, this works in tests** (search for "compose_wrapped_starks" in `stark_in_pickles.rs`).

The honest assessment of its current state:
- It is the right skeleton.
- The constraint-evaluation gadget is `MerkleStarkAir`-specific.
- The Fiat-Shamir replay and vanishing-polynomial computation are
  shortcut versions (see §1.3 caveats) that would fail an adversarial
  prover.
- Copy constraints are not consistently threaded.

---

## 3. What would option (B) require, end to end?

A Kimchi circuit that verifies a Plonky3 STARK over BabyBear+FRI+Poseidon2.
The components, with status:

| Component                                                 | Status in our code                                                                  |
|-----------------------------------------------------------|-------------------------------------------------------------------------------------|
| Pasta-curve / Fp arithmetic                               | provided by upstream Kimchi (Generic + ForeignFieldMul + EndoMul gates)             |
| BabyBear arithmetic in Fp                                 | implemented in `poseidon_stark_verifier_circuit.rs` as 3 Generic gates per mul; trivial because 31-bit modulus fits in one Fp limb |
| Poseidon-Merkle verification                              | implemented (`build_circuit` Sections A-I) — native Kimchi Poseidon gate, 12 rows per hash |
| Plonky3-side switch to Poseidon-committed STARK           | `poseidon_stark.rs` (1 540 LOC) already exists — produces `PoseidonStarkProof` instead of BLAKE3-committed |
| FRI verifier as a circuit                                 | per-layer skeleton exists (`build_circuit` Section L); single-query path tested. Missing: real `z_t` computation, real Fiat-Shamir transcript replay for `alpha` |
| Constraint evaluation                                     | hard-coded to `MerkleStarkAir`; needs generalisation per AIR (or a single "Effect VM AIR is the only thing we wrap" decision) |
| Pickles wrapping                                          | `pickles.rs::prove_recursive_step` operational (assisted recursion path)            |
| Tree-fold over N per-cell proofs                          | naturally falls out of `compose_wrapped_starks` (extends pre/post hash chain across leaves) |

Net engineering for option (B) to reach **production soundness** (not just
"a test passes"):

1. **Generalise the in-circuit STARK verifier to the Effect VM AIR shape.**
   The verifier is currently `MerkleStarkAir`-specific. Effect VM has
   width 105 and many more constraint rows. We need either (a) a
   verifier circuit parameterised over the AIR's constraint vector, or
   (b) one bespoke verifier per AIR variant. Given we only need to wrap
   one AIR — the Effect VM — option (b) is feasible.
   *Estimate: 2-4 weeks, 1500-2500 LOC.*

2. **Replace the shortcut Fiat-Shamir and `z_t` computation with real
   transcript replay.** The Poseidon sponge state needs to be threaded
   through the circuit. `mina-poseidon` provides the same sponge that
   `poseidon_stark.rs` already uses, so this is gate-level but tedious.
   *Estimate: 1-2 weeks, 500 LOC.*

3. **Wire up copy constraints.** Module `kimchi_native` has the same
   problem; the fix pattern (use `link_wires` to thread gadget outputs
   into downstream consumer rows) is the same. This is the P0-2 audit
   work that has to happen anyway.
   *Estimate: 1-2 weeks for the verifier circuit specifically, more for
   the broader audit cleanup.*

4. **Scale from 1-query to 80-query FRI.** The skeleton supports it
   (`num_queries` is just a loop count) but has never been exercised at
   full security. Domain pressure at 2^15 looks fine.
   *Estimate: 1 week, mostly benchmarking and trace-domain tuning.*

5. **Decide what gets bridged to where for cross-Pickles composition.**
   The `compose_wrapped_starks` path already does it via hash-chain pre/post
   binding; if we want cross-cell *arithmetic* (delta sums, etc.) the
   chain has to carry those as PI fields, not just opaque hashes.

Even being generous, this is **6-10 weeks of careful, audit-grade work**
on top of foundations that are present but soundness-flagged.

The matching components for option (A) — re-implementing the same five
pieces (FRI, Merkle, Poseidon2, transcript, constraint eval) inside a
BabyBear AIR — are conceptually parallel but use a different
foundation: `p3-recursion` (already in our workspace via the
`recursion` feature, see `Cargo.toml:55`, fork
`emberian/plonky3-recursion#c14b5fc0`). The fork is used today by
`circuit/src/plonky3_recursion_impl.rs::prove_recursive_layer` for the
*Merkle membership* AIR — i.e. exactly the same kind of "verify a
Plonky3 proof in a Plonky3 AIR" recursion, working end-to-end for one
AIR shape. Generalising it to the Effect VM AIR is the same
"generalise to one specific bespoke AIR" task as option (B).

---

## 4. What does the existing `circuit/src/plonky3_verifier_air.rs` look like?

It is genuinely a 33-line stub. Verbatim (modulo doc-comment formatting):

```rust
//! Plonky3 recursive verifier AIR -- stub module.
//!
//! Real recursive verification is not yet implemented. This module provides
//! the types needed by `ivc::recursive_ivc`.

use crate::field::BabyBear;
use crate::plonky3_prover::DreggProof;

/// Recursion strategy selection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionMode {
    /// Use hash-chain accumulation (existing behavior, fast but weaker).
    HashChain,
    /// Request recursive STARK verification (currently unavailable).
    Recursive,
}

/// An IVC step proof using recursive verification.
pub struct RecursiveIvcStep {
    pub proof: DreggProof,
    pub public_inputs: Vec<BabyBear>,
    pub step_number: u32,
}

/// Build a recursive IVC chain (currently unavailable).
pub fn build_recursive_ivc_chain(
    _fold_proofs: &[(&DreggProof, &[BabyBear])],
) -> Result<RecursiveIvcStep, String> {
    Err(
        "recursive verification is unavailable: RecursiveVerifierAir is a non-functional placeholder"
            .to_string(),
    )
}
```

The session notes characterise this accurately. There is **no** verifier
AIR here — only a type-level signature that `ivc.rs::recursive_ivc` can
import without breaking the build.

The actually-functional code that gets called "verifier AIR" elsewhere in
the codebase is split across two files:

- `circuit/src/plonky3_recursion.rs` (~14 KB) — an `AggregationAir`
  that hash-chains the *public inputs* of N inner proofs into a single
  accumulator via Poseidon2. The module docstring is forthright:
  *"This is NOT full in-circuit recursion (verifying a STARK inside a
  STARK). That requires implementing the Plonky3 verifier as an AIR
  circuit. What we provide is proof aggregation: combining N proofs
  into 1 by proving knowledge of their public inputs in a hash chain.
  The verifier still needs access to the inner proofs for full
  soundness."* This is exactly the unsound-wrap pattern §2 of
  `THOUGHTS-AND-DREAMS.md` calls out.
- `circuit/src/plonky3_recursion_impl.rs` (~17 KB) — the *only* file
  that actually does in-circuit verification, via the upstream
  `p3-recursion` crate from `emberian/plonky3-recursion`. It calls
  `build_and_prove_next_layer` to produce a real recursive proof.
  Verified working in `tests::recursive_merkle_poc` for
  `P3MerklePoseidon2Air`. **This is the file that does what the stub
  promises.**

So the work for option (A) is **not** "write `plonky3_verifier_air.rs`
from scratch." It is "generalise `plonky3_recursion_impl.rs` from
`P3MerklePoseidon2Air` to the Effect VM AIR shape." The infrastructure
(`DreggRecursionConfig`, `create_recursion_backend`,
`prove_recursive_layer`, `verify_recursive_layer`) is wired up to the
fork; the missing piece is making the inner AIR be Effect VM (width
105, all its constraints, Stage-7 PI layout) rather than the toy
Merkle membership AIR.

This re-frames option (A). The accurate description is:

> Option (A) = extend the working `plonky3_recursion_impl.rs` from one
> AIR (Merkle membership) to the production AIR (Effect VM), and prove
> the resulting recursive layer is sound — not "write the verifier AIR
> from scratch."

That changes the cost calculus significantly.

---

## 5. Mina's production code and external Pickles consumers

We do **not** depend on `mina` (the OCaml repo) — we depend on
`o1-labs/proof-systems`, which is the Rust side of Mina's stack. Pinned
to commit `36a8b510` across five crates: `kimchi`, `poly-commitment`,
`mina-curves`, `mina-poseidon`, `groupmap`.

Status of that dependency, as far as a read-only survey can tell:

- **Rust API: stable enough to ship a node, fragile at the edges.** The
  o1-labs `kimchi` crate is what runs Mina's mainnet *prover*. The API
  shape (`CircuitGate`, `ProverProof::create`,
  `ProverProof::create_recursive`, `verifier::verify`) has not changed
  meaningfully in the year-plus this codebase has been using it
  (`kimchi_native` was first added ~2025-05). The fact that one pinned
  commit serves all five crates suggests reasonable cross-crate
  cohesion.
- **Documentation: thin.** The doc surface is OCaml-first (the Pickles
  spec, Wong's Mina book, the o1-labs blog). The Rust crate has decent
  rustdoc on individual types but no end-to-end "how to embed Pickles
  in your stack" guide. Our `circuit/src/backends/mina/mod.rs` and
  `pickles.rs` doc-comments are functionally serving as that guide for
  the codebase.
- **External Pickles consumers: very few.** As of late 2025, Mina is
  the only production blockchain shipping Pickles. The Aleo and
  Lurk-Lab ecosystems sit alongside it but did not pick Pickles. The
  closest external Rust embedder I'm aware of is the
  `proof-systems/turshi` example crate and Mina-internal experimental
  projects (zkapp-cli, snarkyjs). There is no widely-used "Pickles as
  a library" external to o1-labs themselves. This affects both the
  upstream-support model (we are largely on our own) and recruitment
  (relevant expertise is concentrated at o1-labs).

The OCaml-side Pickles (`mina/src/lib/pickles/`) is the gold reference
for the dual-curve step/wrap protocol. Our `step_verifier.rs` and
`wrap_verifier.rs` docstrings explicitly cite that path
(`step_verifier.ml`, `wrap_verifier.ml`, `scalar_challenge.ml`).
There is no Rust port of the Pickles wrapping logic upstream — we
*are* the Rust port, at the layer where the IPA verifier circuit
lives. That is a significant maintenance liability.

---

## 6. Soundness and trust assumptions

### 6.1 Pasta cycle

The Pasta cycle (Pallas + Vesta) is well-studied. Each curve has ~255-bit
scalar field, ~128-bit security, ~10 years of cryptanalytic exposure.
Mina relies on it in production. No known issues. The cycle property
(base field of one = scalar field of the other) is the *enabling* trick
for native EC-in-circuit and is the reason Pickles works at all.

### 6.2 Commitment scheme

Kimchi has two PCS variants:

- **IPA (Bulletproofs-style).** *No trusted setup.* Transparent;
  proof size grows logarithmically (~5-10 KiB at our domain sizes).
  This is what Mina production uses. **This is what our
  `kimchi_native` and Pickles backends use** — see
  `circuit/src/backends/mina/mod.rs:103` (`VestaOpeningProof =
  OpeningProof<Vesta, FULL_ROUNDS>`). The o1-labs `kimchi` crate is
  pulled with `default-features = false, features = ["prover"]`,
  selecting the IPA-only build.
- **KZG variant.** Requires trusted setup. Smaller proofs, faster
  verification. We do not use it.

So option (B) does **not** introduce a trusted setup. It does
introduce a curve-based cryptographic assumption (discrete log over
Pasta) that the transparent-STARK stack avoids. Quantum break of
Pasta would invalidate the recursive layer; the inner STARK layer
would still be sound.

### 6.3 Post-quantum

- Option (A): post-quantum end to end (STARK + STARK).
- Option (B): post-quantum inner (STARK), classical outer (Pasta/IPA).
  Mina is in the same position.

For dregg's threat model — issuing capability proofs that need to
hold up over years — this is the most meaningful asymmetry between
the two options. PQ-safe-by-default is a property worth several
weeks of engineering all by itself.

### 6.4 Soundness of what we already have

Honest accounting from the docs and module headers:

- `kimchi_native` predicates: real Kimchi proofs, **unsound binding
  gates** (P0-2 audit; missing copy constraints). Cost to fix: known,
  bounded; pattern is `link_wires` + canonical-hash binding.
- `pickles.rs` assisted recursion: real `create_recursive` +
  `verifier::verify` — **sound for the state-transition statement
  it actually proves** (Poseidon hash of pre/post). The unsoundness
  appears only when you read "Pickles wrapping" as implying the
  inner STARK was verified, which it wasn't.
- `stark_in_pickles.rs`: takes a real `verify_poseidon` call before
  wrapping, so the *prover* sees a real STARK verifier run. But the
  Kimchi circuit's verifier-of-STARK has the shortcuts noted in §1.3.
  A malicious prover producing a fake STARK would be caught by the
  native pre-wrap verify; a malicious prover *with* a real STARK but
  cheating on FS replay inside the wrap circuit would not be.
- `standalone.rs` / dual-curve wrap: structurally complete,
  functionally incomplete (per the module docstring).

---

## 7. Recursive depth: which topology suits dregg's witnessed-receipt chain?

Per `THOUGHTS-AND-DREAMS.md` §8 (the "golden vision" articulation):

> *"unstructured mesh of interactions, with EffectVM braiding attestable
> causality over it... the full vision is a folded DAG attesting to
> 'this is the causally-coherent history of the whole mesh up to here.'"*

And per `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §C ("Recursive IVC over
the call_forest tree"):

> *"Walk the call_forest bottom-up. Each leaf Action produces a proof
> attesting to its effects against the targeted cell's trace slice...
> Each internal node folds its children's proofs into a parent proof
> using a Nova-style folding scheme (or Plonky3's recursive verifier
> as the IVC step)."*

The shape dregg actually wants:

```
                 root proof  (whole turn or whole DAG cut)
                      │
       ┌──────────────┼──────────────┐
       │              │              │
   subtree[0]    subtree[1]    subtree[2]    ← each is itself a recursive proof
       │              │              │
   ┌───┴───┐      ┌───┴───┐      ┌───┴───┐
  leaf   leaf    leaf   leaf    leaf   leaf  ← per-cell Effect VM proofs
```

What each option naturally supports:

- **Option (A) — recursive verifier AIR, tree-shaped.** Each internal
  node runs a STARK verifier AIR over its k children. Fixed branching
  factor (often k=2), fixed depth per tree. Naturally maps to the
  call_forest tree. Multiple call_forests can be folded across turns
  by another tree on top — same machinery, different leaves.
  Composability is structural.
- **Option (B) — Pickles assisted recursion, linear chain by default.**
  Each step takes one previous proof + one new statement, producing
  one new constant-size proof. This is the *chain* topology, not the
  tree topology. You can simulate trees by chaining a depth-first
  walk through them, but you lose parallelism, and the intermediate
  proofs in the chain are no smaller than the leaves. *Mina-equivalent
  recursion in standalone.rs would allow tree-shaped composition* (a
  Wrap circuit can verify k Step proofs in parallel) but standalone
  isn't production-ready in our tree.

This matters concretely for the witnessed-receipt chain:

- Per-cell receipts: thousands per day. Linear-chain Pickles means
  proving time per step grows with proving overhead per step
  (~1-2s), not with chain length (constant) — but you can't fold
  yesterday's 10 000 receipts and today's 10 000 receipts in
  parallel and merge them; you have to chain through.
- Tree-shaped (option A): the same 20 000 receipts can be folded as
  log₂(20 000) ≈ 15 levels, with all leaf proofs in parallel. This
  is a much better fit for the bursty "settle a turn that touched 50
  cells" pattern.

Verdict on topology alone: option (A) is the natural fit. Option (B)
can be coaxed into tree shape via dual-curve wrapping, which is the
piece that is not yet production-ready in our tree.

---

## 8. Bridge: existing Plonky3-→-Kimchi work in the broader ecosystem

I cannot do live web search in this run, so the following is
read-only-from-codebase plus what's encoded in our doc history.

What I can say from our own code:

- We have already built the bridge — `stark_in_pickles.rs` +
  `poseidon_stark_verifier_circuit.rs`. It is a real implementation,
  with the caveats in §1.3. The design choice that makes it
  tractable — re-prove the STARK with Poseidon-over-Fp Merkle
  commitments instead of BLAKE3 — is documented in
  `stark_in_pickles.rs:1-60`. That choice trades ~6 800 rows per hash
  (BLAKE3 emulation in Kimchi) for ~12 rows (native Poseidon gate). It
  is the difference between "fits in domain 2^15" and "doesn't fit at
  all."
- No other dregg-internal Plonky3→Kimchi bridge exists.

What the ecosystem has done, from prior reading (not freshly verified
this session):

- **SP1 v6 Hypercube, Stwo, RISC Zero** all do *STARK-in-STARK*
  recursion (same as option A), with their own verifier-AIRs. None of
  them go STARK → Kimchi.
- **Lurk-Lab's Nova/SuperNova path** does folding rather than wrapping.
- **Mina's own Pickles** verifies Kimchi-in-Kimchi, not
  STARK-in-Kimchi.
- The closest published precedent for "Plonky3 STARK → o1-labs
  Kimchi → Pickles wrap" is... us. This means we don't have a
  reference implementation to crib from for the parts we haven't
  written.

Open question for future investigation: whether the Aztec / Noir crowd
has done STARK→Plonk bridging, and whether their work translates to
Kimchi specifically. Worth a focused search before committing to (B).

---

## 9. Verdict and recommendation

**Recommendation: option (A), extending `plonky3_recursion_impl.rs`
from `P3MerklePoseidon2Air` to the Effect VM AIR.**

Reasoning in summary:

1. **The framing was off.** Option (A) is *not* "write the verifier
   AIR from scratch." `plonky3_verifier_air.rs` is a 33-line stub,
   but the actually-functional in-circuit recursive verifier lives in
   `plonky3_recursion_impl.rs` and works for one AIR today via the
   `emberian/plonky3-recursion` fork. The work is to **generalise to
   a second AIR**, not to write a verifier from scratch.

2. **Soundness story is simpler.** Option (B) inherits the
   `kimchi_native` P0-2 audit work (missing copy constraints), the
   `standalone.rs` "structurally complete, functionally incomplete"
   dual-curve work, the Fiat-Shamir shortcuts in
   `poseidon_stark_verifier_circuit.rs`, *and* the original "extend
   to the Effect VM AIR" work. Option (A) inherits the first item
   only — making one verifier-AIR work for one bigger AIR.

3. **Topology is right.** Tree-shaped recursion is the natural fit
   for the call_forest / DAG / cross-cell aggregation patterns
   in `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` and the
   "braiding attestable causality" framing in `THOUGHTS-AND-DREAMS.md`.
   Pickles assisted-recursion is linear by default; standalone is
   not production-ready.

4. **PQ stays.** dregg's threat horizon is years; capability proofs
   need to hold up. Option (A) keeps the full stack PQ-safe.

5. **Maintenance posture.** The
   `emberian/plonky3-recursion` fork is *our* fork; we control the
   upgrade pace. The Kimchi stack pins five crates to a single
   o1-labs commit, with no Rust-side Pickles documentation and no
   external embedders to learn from. Both choices have
   custody-of-the-stack issues, but option (A)'s is at least our
   custody.

The case for option (B) doesn't disappear:

- Mina's batch-verification cost is genuinely impressive (~864-byte
  state proofs, ~200ms verification — numbers from
  `THOUGHTS-AND-DREAMS.md` §4 and Mina's own docs).
- ~5 800 LOC of `circuit/src/backends/mina/` exists; throwing it
  away is real cost.
- For *external* settlement (e.g. anchoring a dregg commit on
  Mina or another curve-based L1), a Kimchi/Pickles proof is what
  the receiving chain can verify. Option (A) does not give us
  that.

A reasonable long-term position is **option (A) as the primary
recursive aggregation layer + retain `stark_in_pickles.rs` as the
*export* path for cross-chain settlement.** Inner recursion is
STARK-in-STARK; external bridging is a final STARK → Pickles wrap.
This is the same shape RISC Zero ships (Groth16 wrap for Ethereum
settlement, STARK recursion for the actual compute).

### 9.1 ~2-week starter task to build evidence

**Goal:** prove that
`plonky3_recursion_impl.rs::prove_recursive_layer` can be
generalised from `P3MerklePoseidon2Air` to a *minimal Effect VM AIR
slice* — enough to know whether the generalisation is mechanical or
runs into AIR-shape blockers.

**Concrete deliverable:**

1. Pick the smallest non-trivial Effect VM AIR variant from
   `circuit/src/effect_vm/constraints/` (do not modify those; pick
   one whose constraint set is well-understood).
2. Wire that AIR's prover output into the
   `RecursionInput::UniStark` path
   (`plonky3_recursion_impl.rs:320-325`).
3. Run `prove_recursive_layer` + `verify_recursive_layer` on it
   end-to-end.
4. Measure: domain size needed, prove-time, proof-size, whether the
   recursion library's `RecursiveAir` blanket impl accepts the
   Effect VM AIR's column count and constraint set.
5. Write a 1-2 page report on what (if anything) blocks
   generalisation.

If the starter task succeeds: option (A) is mechanically tractable;
commit to it for Stage 7-γ aggregation.

If the starter task hits a blocker (e.g. `p3-recursion` cannot handle
the Effect VM's width 105 or its lookup argument): we get a
specific, named blocker to either fix in the fork or use as a reason
to pivot to option (B). Either way, two weeks turns the open
question in `THOUGHTS-AND-DREAMS.md` §Q1 into a decision.

### 9.2 What this survey does not resolve

- The DAG-shaped aggregation in
  `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §C is structurally
  compatible with both options; the survey does not measure prover
  cost at realistic call_forest sizes.
- The cross-chain settlement bridge (option B's strongest case) is
  worth its own investigation — specifically, whether Midnight (per
  `project-midnight-strategy.md`) needs Pickles compatibility or
  whether a `dregg-verifier` standalone covers it.
- The fabricated-Mangrove correction in `THOUGHTS-AND-DREAMS.md` §1
  affects neither (A) nor (B); the ζ doc's chunking intuition is
  separate from the choice of outer recursive substrate.

---

## File pointers

Primary code paths referenced in this survey, all under
`/Users/ember/dev/breadstuffs/`:

- `circuit/src/plonky3_verifier_air.rs` — the 33-line stub
- `circuit/src/plonky3_recursion.rs` — `AggregationAir` (hash-chain
  aggregation, not in-circuit recursion)
- `circuit/src/plonky3_recursion_impl.rs` — *the actually-working
  recursive layer*, via `emberian/plonky3-recursion` fork
- `circuit/src/backends/kimchi_native/` — Kimchi circuit-author
  surface (predicates / derivation / fold / DSL), tier
  Experimental
- `circuit/src/backends/mina/pickles.rs` — assisted recursion,
  operational
- `circuit/src/backends/mina/standalone.rs` +
  `step_verifier.rs` + `wrap_verifier.rs` — dual-curve
  Mina-equivalent recursion, structurally complete, functionally
  incomplete
- `circuit/src/backends/stark_in_pickles.rs` +
  `circuit/src/poseidon_stark.rs` +
  `circuit/src/poseidon_stark_verifier_circuit.rs` — the
  STARK→Kimchi→Pickles bridge (`MerkleStarkAir`-only proof of
  concept)
- `circuit/src/proof_tier.rs:154` — `kimchi_native_tier() →
  ProofTier::Experimental`
- `dregg-dsl/src/gen_kimchi.rs` — the codegen feeding the
  Kimchi backend
- `circuit/Cargo.toml:53-58` — o1-labs commit pin
  `36a8b510`
- `Cargo.toml:55` — `emberian/plonky3-recursion` commit pin
  `c14b5fc079af18d7f3ba3f3586f173bd166c7cd4`
- `THOUGHTS-AND-DREAMS.md` §Q1, §1 — the framing this survey
  answers
- `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` §C — the
  recursive-IVC-over-call-forest target topology
- `.docs-history-noclaude/recursion-status.md` — prior
  recursion-state inventory (2025-era; some details now
  out-of-date)
