> **Provenance.** Recovered 2026-05-30 from the prior session's read-only study agent
> (`~/.claude/.../subagents/`), which designed this as the body for this path but could not
> write it (read-only `Plan` mode). Verbatim except for stripped read-only-mode preamble.
> Consolidated alongside `PHASE-SHIFT.md`.

# STUDY: Overhauling the `CryptoKernel` §8 Portal into a Dischargeable Contract

**Doc to be authored:** `/Users/ember/dev/breadstuffs/docs/rebuild/PHASE-CRYPTOKERNEL.md`
(Note: this run is read-only / design-only; the content below is the full draft body for that file plus the report. The directory `/Users/ember/dev/breadstuffs/docs/rebuild/` exists and is the right home — it sits alongside `REORIENT.md`, `03-spine-proof.md`, `ROADMAP.md`.)

---

## 1. What's wrong / thin now — the gap inventory

The current portal (`metatheory/Dregg2/CryptoKernel.lean`) is an **uninterpreted typeclass**. That is the right *shape* for parametric proving, but it does not let any §8 obligation be **discharged** — it can only be **assumed**. Concretely:

### 1.1 The four operations are not pinned to the real ones

| Lean op (`CryptoKernel.lean:40-56`) | Real Rust op | The gap |
|---|---|---|
| `hash : List Nat → Digest` | Poseidon2 sponge (`circuit/src/poseidon2.rs:369 hash_many`, `:357 hash_2_to_1`, `commit/src/hash.rs` `hash_leaf`/`hash_node`) | Lean's `hash` is an opaque `List Nat → Digest`; the real hash is a fixed-arity Poseidon2 permutation over `BabyBear` with a specific round structure. The *only* law is `hash_inj` — an **idealized collision-resistance** that the real Poseidon2 cannot satisfy (it is not injective; it is CR). |
| `verify : Digest → Proof → Bool` | `stark::verify(air, proof, public_inputs)` (`circuit/src/stark.rs:1346`) returning `Result<(),String>`; dispatched per-kind by `WitnessedPredicateRegistry::verify` (`cell/src/predicate.rs:844`) | Lean's `verify` is a **bare oracle with no laws at all**. Its soundness/extractability is declared "NEVER a Lean law" (`CryptoKernel.lean:44-46`). The real `verify` takes *three* arguments (`air`, `proof`, `public_inputs`) — the Lean two-argument shape collapses `(air, public_inputs)` into a single `Digest stmt`, losing the AIR identity that `stark.rs:1383` actually checks (`air_name` binding). |
| `commit : Int → Int → Digest` | Pedersen over Ristretto (`cell/src/value_commitment.rs:1-19`, `commit(v,r)=v·V+r·R`) | Lean's `commit` is on `ℤ` with `commit_hom` as the only law — and the *reference* instance makes it the **degenerate linear form `v+r`** (`CryptoKernel.lean:124`). The real commitment lives in the Ristretto scalar/group, where `commit_hom` holds but **binding** (the load-bearing soundness) is a DLog assumption that never appears. |
| `nullifier : Digest → Digest` | `note::Nullifier` deterministic tag + `cell/src/nullifier_set.rs` spent-set | Lean's `nullifier` is `id` in the reference instance (`CryptoKernel.lean:125`). Only **determinism** (function-ness) is used; **unlinkability** is left as a `§8:` note (`PrivacyKernel.lean:144-146`). |

### 1.2 Which laws are assumed-not-grounded

- `hash_inj` (`CryptoKernel.lean:56`) — assumed injective. The real obligation is collision-resistance, a computational hardness, not injectivity. **Mismatch of kind**, not just of strength.
- `commit_hom` (`CryptoKernel.lean:53`) — this one is *genuinely* grounded: `PrivacyKernel.lean:69-118` derives `commit_zero`, packages `commitHom : (Int×Int) →+ Digest`, and proves `committed_conservation_kernel` via `map_sum`. This is the **template** — the homomorphism is a real algebraic law the Pedersen impl satisfies. But hiding/binding remain `§8:` notes (`PrivacyKernel.lean:105-107`).
- `verify` — **no law whatsoever**. This is the central hole.

### 1.3 Where the Lean↔Rust↔circuit cascade is missing

The cascade *exists in miniature* but does not reach the real AIR:

- `Circuit.lean` builds a **toy** `kernelCircuit` (4 gates: Conservation/Authority/ChainLink/ObsAdvance, `Circuit.lean:153`) over `ℤ`-as-field, and proves `bridge` (`Circuit.lean:229`) + `verify_law_derivable` (`Circuit.lean:292`). This is the proof-of-concept that "verify-law is DERIVABLE from a circuit." **But:**
  - The IR (`Expr`/`Constraint`/`ConstraintSystem`, `Circuit.lean:67-95`) is a private Lean toy. It has **no correspondence** to the real Rust IR `CircuitDescriptor`/`ConstraintExpr` (`circuit/src/dsl/circuit.rs:44-130`), which has 15+ constraint forms (`MerkleHash`, `Hash`, `Gated`, `Lookup`, `ConditionalNonzero`, …) that the Lean IR cannot express.
  - The `chainOk` gate carries the **only `-- PRIMITIVE:` seam** (`Circuit.lean:40, 290`): the binding of the Rust prover's CR-hash digest to the Lean indicator wire is *flagged but not modeled*.
  - `RecordCircuit.lean` independently builds an honest **bit-decomposition range gadget** (`range_iff`, `Circuit.lean`… actually `RecordCircuit.lean:84`) with NO primitive seam — proving `≤`/`<` soundly. This is the *good* pattern (gadget fully proven), but it compiles to a *different* Lean IR than `Circuit.lean`, and neither connects to `circuit/src/dsl/`.
  - **No extraction.** `kernelCircuit` is "pure data that extracts to the Rust prover" (`Circuit.lean:151`) — but there is no actual emitter from `Dregg2.Circuit.ConstraintSystem` to `CircuitDescriptor`. The pipeline is asserted, not built. The `dregg-lean-ffi/` crate exists but only does differential testing (`differential.rs`), not circuit-data export.

- The 8 `WitnessedKind` verifiers (`Authority/Predicate.lean:40-58`) are modeled as a **dispatch registry** with `registry_sound` (`Predicate.lean:106`) and `crypto_kind_routes_to_oracle` (`Predicate.lean:217`). But every crypto kind routes to the **same opaque `CryptoKernel.verify` oracle** — there is no per-kind circuit, no per-kind statement algebra, no per-kind epistemic boundary. The Rust side has all 8 as real AIRs (`circuit/src/dsl/membership.rs`, `non_membership.rs`, `dsl/note_spending.rs`, `bridge_action_air.rs`, `temporal_predicate_air.rs`, …) but the Lean side cannot name them.

- `EpistemicDial.lean` is a beautiful standalone order-theory result (`zk_is_dial_bottom`, `dial_unifies_single_and_multi_party`) but it is **not wired to the CryptoKernel**: `accepts` is pinned to `Discharged pred wit` (`EpistemicDial.lean:172`), i.e. to the abstract `Verifiable` seam, not to a per-kind kernel verifier. The dial floats above the portal.

**Summary of gaps:** (a) `verify` has no law and the wrong arity; (b) `hash_inj` is the wrong *kind* of assumption; (c) the Lean circuit IR is a toy disconnected from `CircuitDescriptor`; (d) no extraction emitter exists; (e) the 8 kinds collapse to one oracle; (f) the dial is unwired.

---

## 2. The overhauled interface

The overhaul keeps the *parametric* virtue (every theorem holds for any lawful kernel) but adds **structure that the Rust circuits can discharge**. Three layered classes instead of one flat one.

### 2.1 Layer A — `CryptoPrimitives` (the real operations, real laws)

Replace the flat `CryptoKernel` with a primitives class that names the real ops with their *actual* algebraic laws (not idealized ones):

class CryptoPrimitives (F : Type) (Digest Proof : Type) [Field F] [AddCommGroup Digest] where
  -- Poseidon2 as an arity-tagged compression, NOT an injective List-hash.
  compress    : Digest → Digest → Digest                 -- hash_2_to_1
  compressN   : List Digest → Digest                     -- hash_many (sponge)
  -- The CR law is a *parametric collision hypothesis*, not injectivity:
  collisionHard : Prop                                   -- "no PPT adversary finds x≠y, compress x = compress y"
  -- Pedersen, with the homomorphism as the REAL grounded law (the template that already works):
  commit      : F → F → Digest
  commit_hom  : ∀ v w r s, commit (v+w) (r+s) = commit v r + commit w s
  -- binding stays a hypothesis carrier (Prop), never a proved Lean law:
  binding     : Prop
  -- nullifier: deterministic (function-ness is the law), unlinkability a Prop carrier:
  nullifier   : Digest → Digest
  unlinkable  : Prop

The key move: **separate the *algebraic* laws (proved, used by the metatheory) from the *computational* obligations (carried as `Prop` parameters, discharged by the crypto layer).** This is exactly what `EpistemicDial.lean:489-503` already does for indistinguishability (it lives "as the hypothesis structure of `Disclosure`") and what `PrivacyKernel.lean` does for `commit_hom` vs hiding. Generalize that discipline to the whole portal: algebraic ⇒ proved; computational ⇒ parameter.

### 2.2 Layer B — `VerifierKernel` (verify as a *dischargeable* contract, not an oracle)

This is the heart of the overhaul. The current `verify : Digest → Proof → Bool` has no law. Replace it with a verifier whose soundness is **derivable from a circuit**, generalizing `verify_law_derivable` (`Circuit.lean:292`) off the toy `kernelCircuit` onto the real AIR shape:

class VerifierKernel (F : Type) [Field F] extends CircuitIR F where
  -- A statement is the PUBLIC-INPUT vector + the AIR identity (matching stark.rs:1383):
  Statement := AirId × List F
  -- verify is DEFINED as "the extracted circuit is satisfied by some witness":
  verify : Statement → Proof → Bool
  -- and its soundness law is a THEOREM, parameterized over a relation R the AIR encodes:
  verify_sound : ∀ air pis proof,
      verify (air, pis) proof = true → ∃ w, satisfies (circuitOf air) (pis, w) ∧ R air pis w

where `CircuitIR` is a Lean IR that **mirrors** `circuit/src/dsl/circuit.rs::ConstraintExpr` (the real one, with `MerkleHash`, `Hash`, `Gated`, `Lookup`, `Binary`, `Transition`, boundary constraints), not the toy `Expr`. The `bridge`/`satisfies` machinery of `Circuit.lean` extends to this richer IR (the per-gate `_iff` lemmas become per-`ConstraintExpr`-constructor lemmas, with the `RecordCircuit.lean` range gadget supplying the `≤`/`<` cases honestly).

The `verify_sound` is the **derived verify law** — the discharge — replacing the assumed oracle. The `extractability` (that `verify=true ⇒ a real witness exists, binding) is the only remaining `-- PRIMITIVE:` and it is exactly the STARK soundness of `stark::verify_full` (FRI proximity + Fiat-Shamir), cited to `deep-fri`, `proximity-gaps-reed-solomon`, `whir`/`stir` (`pdfs/INDEX.md §20`).

### 2.3 Layer C — `PredicateKernel` (the 8 kinds as per-kind circuit obligations + dial)

Lift `Authority/Predicate.lean`'s registry so that each `WitnessedKind` carries (i) its statement algebra, (ii) its circuit, and (iii) its dial position:

structure KindObligation (F) where
  circuit     : CircuitIR F            -- the per-kind AIR (Merkle, Pedersen, …)
  statement   : Type                   -- the public-input algebra for this kind
  relation    : statement → Proof → Prop
  dialFloor   : Dial                   -- the epistemic boundary (EpistemicDial.lean)

def kindObligation : WitnessedKind → KindObligation F
  | .merkleMembership => ⟨merkleCircuit, MerkleRoot × Leaf, …, .acceptanceOnly⟩   -- blinded ⇒ ZK floor
  | .pedersen         => ⟨pedersenCircuit, …, .selective⟩                          -- discloses commitments
  | …

Then `registry_sound` (`Predicate.lean:106`) composes with `verify_sound` (Layer B) to give **per-kind soundness-by-circuit**, and `EpistemicDial.DiscloseAt.accepts_eq` (`EpistemicDial.lean:172`) is instantiated with `dialFloor` so the dial is finally *wired*: each kind's verifier accepts iff `Discharged`, at its own disclosure notch. `blindedSet`/`merkleMembership` (blinded) sit at `acceptanceOnly`; `pedersen` at `selective`; `temporal`/`dfa` at `fullDisclosure` or `selective`.

**This is the clean interface the Rust circuits discharge:** Rust provides, per kind, `(circuitOf air ≡ CircuitDescriptor, R ≡ the AIR's relation, verify ≡ stark::verify)`, and the Lean `verify_sound`/`registry_sound`/dial laws are the obligations that hold *for that provision*.

---

## 3. The cascade — how a §8 obligation flows end-to-end

   LEAN (proved)                    EXTRACTION                 RUST/CIRCUIT (discharges)
   ─────────────                    ──────────                 ────────────────────────
1. bridge: satisfies(circuit, w)    circuit : CircuitIR  ───►  CircuitDescriptor
      ↔ Relation(stmt, w)           emitter (NEW)              (dsl/circuit.rs:44)
      [Circuit.lean:229 pattern,                               + AirDescriptor fingerprint
       extended to real IR]                                    (air_descriptor.rs) binds
                                                               the extracted circuit to the
2. verify_sound: verify=true        verify ≡ stark::verify ──► stark::verify_full
      → ∃w, satisfies ∧ Relation     (Layer B)                 (stark.rs:1375): FRI+FS
      [derived, not assumed]                                   ⇒ extractability/binding
                                                               [the PRIMITIVE seam — STARK
3. registry_sound ∘ verify_sound:   registryVerify  ───────►  WitnessedPredicateRegistry
      accepted ⇒ Discharged ⇒        ≡ registry dispatch       ::verify (predicate.rs:844)
      Relation holds (admissible)                              per-kind AIR
      [Predicate.lean:106]
                                                               ─────────────────────────
END-TO-END SOUNDNESS = (1)∘(2)∘(3): "verify accepts ⇒ admissible" (Lean, proved)
                                     ∘ "verify accepts ⇒ it actually happened" (STARK, crypto)

**The trust boundary** sits at exactly one place: `verify_sound`'s `extractability`/`binding` `Prop` (Layer B) and the `collisionHard`/`binding`/`unlinkable` carriers (Layer A). Everything *above* the boundary (the bridge equivalence, the registry dispatch soundness, the dial confinement, the conservation algebra) is **proved in Lean**. Everything *at* the boundary is the genuine cryptographic assumption (FRI soundness, DLog binding, Poseidon2 CR) — named, parameterized, never `axiom`/`sorry` (the `EpistemicDial.lean:489-503` discipline).

**The extraction of circuit data** is the one piece of *new Rust glue*: a serializer from `Dregg2.Circuit.CircuitIR` (Lean) to `CircuitDescriptor` (Rust, already `Serialize`/`Deserialize`, `dsl/circuit.rs:43`), with a Lean-side `#eval`-printable encoding and a Rust-side decoder, gated by `AirDescriptor::fingerprint` (`air_descriptor.rs`) so the validator confirms *the AIR it runs is the AIR Lean proved the bridge for*. The `dregg-lean-ffi/` crate is the natural host (it already links `libdregg_lean.a`).

---

## 4. The proving-system choices

The repo has **already decided** this, and the overhaul should commit to the decision rather than reopen it (`pdfs/DECISION-recursion-strategy.md`):

- **STARK-native recursion, NOT folding.** The verdict: "a hash-based FRI STARK has **no additively-homomorphic commitment**, and that single constraint kills the entire Nova/HyperNova/ProtoStar folding line outright" (`DECISION-recursion-strategy.md` verdict line). Field is BabyBear (`circuit/src/field.rs`), commitment is Poseidon2-Merkle MMCS + FRI PCS (`plonky3_recursion_impl.rs`), transparent + plausibly-PQ. So the kernel's `verify` is **STARK verify** (`stark.rs:1375`), and recursion is **recursive-verifier-in-circuit** (`poseidon_stark_verifier_circuit.rs:135102 bytes`, `plonky3_verifier_air.rs`), not a witness-fold.
- **Poseidon2 as the arithmetization-friendly hash** (`poseidon2.rs`, `poseidon2_air.rs`) — it is the in-circuit hash for the Merkle/FRI commitment *and* the leaf/node hash (`commit/src/poseidon2_tree.rs`). The Lean `compress`/`compressN` (Layer A) name exactly these. Cite `poseidon2` paper (`INDEX §20`).
- **Pedersen/Ristretto stays for value commitments** (`value_commitment.rs`) — it is the *one* homomorphic primitive, used only for conservation (`commit_hom`), deliberately *outside* the FRI commitment layer (so it does not reintroduce the folding temptation).
- **Recursion/aggregation = recursive STARK verification** (the "hyperedge's witness-fold" is, in this repo, a **proof-carrying tree of STARK verifications**, `bilateral_aggregation_air.rs`, `recursive_witness_bundle.rs`, IVC chain `ivc.rs`). The overhaul commits the kernel to expose an `aggregate : List Proof → Proof` whose law is "the aggregate verifies ⇒ each leaf verifies," derivable from the recursive-verifier AIR. Keep lattice folding (Neo/SuperNeo, `INDEX §18`) on the watch-list only (`DECISION-folding-variants.md`).
- **ZK / the dial** = trace blinding (`stark_zk.rs`, `MerkleTreeHidingMmcs`/`HidingFriPcs`) realizes the `acceptanceOnly` floor of `EpistemicDial`; cite `zk-for-starks-note` (`INDEX §21`).

**What the overhaul commits to:** BabyBear + Poseidon2 + FRI-STARK + recursive-verifier recursion + Pedersen-only-for-conservation. No folding in the kernel.

---

## 5. Scope + sequence — the minimal first discharge

**First obligation to discharge end-to-end: Merkle membership** (`WitnessedKind.merkleMembership`).

Why this one first (not Pedersen conservation, though that is the close runner-up):
- The Rust side is **already real and algebraically sound**: `merkle_poseidon2_circuit()` (`dsl/descriptors.rs:176`) with the `MerkleHash` Poseidon2 constraint, position validity, chain continuity, and PI-binding boundaries (`descriptors.rs:225-260`). The deprecated linear `MerkleStarkAir` (`stark.rs:803`) is explicitly *not* it.
- The Lean side has the **honest gadget pattern** ready: `RecordCircuit.lean`'s `range_iff` shows how to prove a gadget sound+complete with *no* primitive seam; Merkle membership is structurally similar (a recomposition: `parent = hash(current, siblings, position)` up a path).
- It exercises the **whole cascade** (bridge → verify_sound → registry_sound) and the **dial wiring** (blinded membership ⇒ `acceptanceOnly` floor) without needing the group/curve algebra that Pedersen drags in.
- Its statement algebra is small: `Statement = (root : Digest, leaf : Digest)`, `Relation = "leaf is in the tree with root"`.

**Minimal-overhaul steps (the spine):**

1. **Define `CircuitIR` in Lean** mirroring the *subset* of `ConstraintExpr` that Merkle needs: `Equality`, `MerkleHash` (Poseidon2 4-to-1 as an uninterpreted `compress` from Layer A), `Transition`, `PiBinding`/boundary. (Generalize `Circuit.lean`'s `Expr`.)
2. **Build `merkleCircuit : CircuitIR`** and prove `merkle_bridge : satisfies merkleCircuit (root,leaf,path) ↔ MerkleMembers root leaf` — the path-recomposition soundness+completeness, with `compress` left abstract (its CR is a Layer-A `Prop`). This is the `bridge` (`Circuit.lean:229`) lifted to the Merkle gadget.
3. **Derive `verify_sound` for this kind** off `merkle_bridge` (the `verify_law_derivable` move, `Circuit.lean:292`).
4. **Wire the kind**: `kindObligation .merkleMembership = ⟨merkleCircuit, …, .acceptanceOnly⟩`; compose with `registry_sound` (`Predicate.lean:106`) and instantiate `EpistemicDial.DiscloseAt` at the floor.
5. **Build the extraction emitter** (Rust glue in `dregg-lean-ffi/`): Lean prints `merkleCircuit` as a `CircuitDescriptor` encoding; Rust decodes and checks `AirDescriptor::fingerprint` equals `merkle_poseidon2_circuit()`'s. Differential-test (the crate already does differential, `differential.rs`) that the Lean-emitted descriptor and `dsl/descriptors.rs:176` agree.
6. **End-to-end test:** a real Merkle proof from `commit/src/merkle.rs` verifies under `stark::verify`, and the Lean cascade certifies "verify accepts ⇒ membership holds ⇒ admissible."

**Path to the rest** (sequence after Merkle):
- **Pedersen conservation** next — most of the algebra is *already proved* (`PrivacyKernel.lean committed_conservation_kernel`); needs only the Layer-A `commit`/`commit_hom` re-homed onto Ristretto and the range gadget (`RecordCircuit.lean range_iff`) for non-negativity. Dial: `selective`.
- **NonMembership** (`non_membership.rs`, neighbor-bracketing) — reuses the Merkle gadget twice + adjacency.
- **Temporal / Dfa** (`temporal_predicate_air.rs`, lookup-table routing) — needs `Lookup`/`Gated` in `CircuitIR`; dial `fullDisclosure`/`selective`.
- **BlindedSet / Bridge / Custom** — `BlindedSet` reuses Merkle+blinding (dial floor); `Bridge` is the comparison AIR (range gadgets); `Custom` is the open `vk_hash` extension (`Predicate.lean custom_is_open_extension`) routed through `AirDescriptor` fingerprints.
- **Aggregation** last — the recursive-verifier kernel op (`aggregate`), discharged by `bilateral_aggregation_air.rs`/`ivc.rs` once the per-kind discharges are in.

---

## Recommended overhaul shape (the one-paragraph verdict)

Split the flat uninterpreted `CryptoKernel` into **three layered classes**: `CryptoPrimitives` (Poseidon2 `compress`, Pedersen `commit`+`commit_hom`, `nullifier`, with all *computational* hardness as `Prop` carriers, not idealized laws like the current `hash_inj`); `VerifierKernel` (whose `verify` is *defined* as "the extracted circuit is satisfiable," with `verify_sound` a **derived theorem** generalizing `verify_law_derivable` off the toy `kernelCircuit` onto a Lean `CircuitIR` that mirrors the real `ConstraintExpr`); and `PredicateKernel` (the 8 `WitnessedKind`s as per-kind `KindObligation`s, each with its circuit, statement algebra, and `Dial` floor, composing `registry_sound` with `verify_sound` and finally **wiring `EpistemicDial`** to the per-kind verifier). The single trust boundary is the FRI/DLog/Poseidon2-CR `Prop` carriers; everything above is proved. Commit to STARK-native recursion (no folding), per `DECISION-recursion-strategy.md`.

**First §8 obligation to discharge end-to-end: Merkle membership** — Rust AIR already real and algebraically sound (`dsl/descriptors.rs:176`), Lean gadget pattern ready (`RecordCircuit.lean range_iff`), exercises the full bridge→verify_sound→registry_sound→dial cascade, and needs no curve algebra.

---

### Critical Files for Implementation
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/CryptoKernel.lean` — the portal to split into the three layered classes
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit.lean` — the `bridge`/`verify_law_derivable` machinery to generalize off the toy `kernelCircuit` onto the real `CircuitIR`
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Authority/Predicate.lean` — the registry to lift into per-kind `KindObligation`s (statement algebra + circuit + dial)
- `/Users/ember/dev/breadstuffs/circuit/src/dsl/circuit.rs` — the real `CircuitDescriptor`/`ConstraintExpr` the Lean `CircuitIR` must mirror and the extraction emitter must target
- `/Users/ember/dev/breadstuffs/circuit/src/dsl/descriptors.rs` — `merkle_poseidon2_circuit()` (`:176`), the concrete first-discharge AIR; plus `/Users/ember/dev/breadstuffs/metatheory/Metatheory/EpistemicDial.lean` for the dial wiring and `/Users/ember/dev/breadstuffs/dregg-lean-ffi/` as the extraction-glue host.
