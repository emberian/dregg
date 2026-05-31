# PHASE: The Cryptographic TCB — an honest conformance map for the §8 swap

> **Companion to** `PHASE-CRYPTOKERNEL.md` (the three-layer split and the §8
> cascade), `PHASE-BRIDGE.md` (the extraction emitter + fingerprint binding),
> and `Dregg2/Crypto/UCBridge.lean` (the Pedersen UC transport). This document
> answers ONE question: **for the running system, do the real Rust crypto
> implementations actually satisfy the interfaces dregg2's Lean §8 boundary
> ASSUMES?** It does not change any source. It is a swap-readiness audit, and
> the rule is the one the rails always demand: **name every assumption; flag
> every gap; never overclaim.**

---

## 0. The shape of the question

dregg2 never proves crypto soundness in Lean. The eight `WitnessedKind`s
(`Merkle`, `Pedersen`, `NonMembership`, `Temporal`, `Dfa`, `Bridge`,
`BlindedSet`, `Custom`) are each discharged as a **bridge theorem** + a set of
**`Prop` carriers**. The pattern is uniform across all eight
(`Dregg2/Crypto/*.lean`):

1. A **gadget bridge** (`*_bridge`): `Satisfies circuit stmt ↔ Relation stmt`,
   proved **both directions, fully, kernel-clean** (`#assert_axioms` ⊆
   `{propext, Classical.choice, Quot.sound}`). The hash `compress` is left
   ABSTRACT inside the gadget — it is never opened, so the bridge has *no
   primitive seam*.
2. A **derived verify law** (`*_verify_sound`): `verify accepts → Relation`,
   composed from the bridge's soundness half and a single `Prop` hypothesis —
   `extractable` (STARK soundness: FRI proximity + Fiat-Shamir + the digest
   binding). The verify law is **derived**, not assumed.
3. A **dial wiring** + **registry cascade** pinning the verifier to its
   epistemic floor.

So the Lean side **assumes** exactly two families of `Prop`:

- **Layer-A carriers** (`Dregg2/Crypto/Primitives.lean:39-64`):
  `collisionHard` (Poseidon2 collision-resistance — explicitly the CORRECT
  assumption, replacing the wrong idealized `hash_inj`), `binding`
  (Pedersen/DLog), `unlinkable` (anonymity advantage). The **one proved
  algebraic law** is `commit_hom` (Pedersen additive homomorphism,
  `Primitives.lean:55`).
- **Per-kind `extractable`** (one `Prop` field on each `*VerifierKernel`
  class): "the verifier's accept bit witnesses a satisfying trace." This folds
  STARK FRI/Fiat-Shamir soundness + (for hash kinds) `compress` CR.

**The swap needs each of these assumed interfaces to be matched by a sound Rust
impl** — and, ideally, a *check* that the Rust AIR the backend runs is the AIR
Lean proved the bridge for. That check exists, today, for exactly **two** AIRs.

---

## 1. The conformance table

Legend for the columns:
- **Real primitive?** — does the running impl use a real, standard primitive
  (vs. a placeholder / reference `Int` stand-in)?
- **Conformance check?** — is there ANY machine check binding the Rust impl to
  the Lean-assumed interface (fingerprint, golden vector, UC transport,
  differential)? "Fingerprint" = the `dregg-lean-ffi` AIR-shape fingerprint
  binding (`circuit_decode.rs::fingerprint`).
- **Assumption** — standard well-studied (S) vs. bespoke/riskier (B).

| WitnessedKind | Lean-assumed property (carrier / bridge hypothesis) | Rust impl (file:line) | Real primitive? | Conformance check? | Assumption |
|---|---|---|---|---|---|
| **Pedersen** | `commit_hom` PROVED; `binding` (DLog) + `unlinkable` (hiding) carriers; `extractable` for the conservation AIR | `cell/src/value_commitment.rs:68-164` (Ristretto, curve25519-dalek, `commit(v,r)=v·V+r·R`); UC: `uc-crypthol/Dregg2_FCom.thy` | **Yes** — real Ristretto group, hash-to-point generators | **Yes — UC transport** (`Crypto/UCBridge.lean`: CryptHOL `pedersen_bind`/`abstract_perfect_hiding` discharge `binding`/`unlinkable`) | **S** (DLog) — *but see §3 caveats* |
| **Merkle** | `collisionHard` (Poseidon2 CR); `extractable` for `merkle_poseidon2` AIR | hash: `circuit/src/poseidon2.rs:357 hash_2_to_1`; AIR: `circuit/src/dsl/descriptors.rs merkle_poseidon2_descriptor()`; verifier: `turn/src/executor/membership_verifier.rs:79 MerkleMembershipStarkVerifier` | **Yes** — real Poseidon2 permutation, Plonky3-sourced params | **Yes — fingerprint** (`dregg-lean-ffi/src/circuit_decode.rs:855 merkle_air_shape_native` vs Lean `emittedMerkle`; `circuit_differential.rs:236`) | **S** (Poseidon2 CR) |
| **NonMembership** | `collisionHard` (Merkle ×2) + sorted-adjacency combinatorics (PROVED) + `extractable` | adjacency: `circuit/src/membership_adjacency_air.rs`; verifier: `cell/src/predicate.rs:1527 SortedNeighborNonMembershipVerifier` / `turn/.../membership_verifier.rs:222 CircuitNeighborAdjacencyVerifier` | **Yes** — real Poseidon2 + range AIR | **No** — no fingerprint binding for the adjacency AIR | **S** (CR) |
| **Temporal** | NO hash/commitment carrier; `extractable` only (pure range combinatorics, PROVED) | `circuit/src/temporal_predicate_air.rs`, `temporal_predicate_dsl.rs`; verifier: `turn/.../membership_verifier.rs:467 TemporalPredicateStarkVerifier` | **Yes** — real range-gadget STARK AIR | **No** — no fingerprint binding for the temporal AIR | **S** (FRI soundness only) |
| **Dfa** | NO hash carrier; `extractable` only (Lookup-as-δ, structural, PROVED) | `circuit/src/dsl/circuit.rs:1746 dfa_lookup_descriptor`; verifier: `turn/.../membership_verifier.rs:344 DslCircuitDfaVerifier` | **Yes** — real lookup-table STARK AIR | **No** — no fingerprint binding for the DFA AIR | **S** (FRI soundness only) |
| **Bridge** | `collisionHard`/`binding` for the opening (`compress` equation, abstract) + range (PROVED) + `extractable` | `circuit/src/bridge_action_air.rs`; verifier lives in `dregg-bridge` | **Yes** (AIR exists) | **No** — and **fails closed in production** (`turn/.../membership_verifier.rs:621` BridgePredicate not wired) | **S** (CR + FRI) |
| **BlindedSet** | `collisionHard` (Merkle reuse) + `HolderAnonymity.ViewIndistinguishable` carrier + `extractable` | `circuit/src/dsl/membership.rs:152 generate_blinded_merkle_poseidon2_trace`; verifier: `cell/src/predicate.rs:1970 CredentialSetMembershipVerifier` (+ issuer-root binding) | **Yes** — real blinded Merkle + Poseidon2 | **No** — no fingerprint binding for the blinded AIR; anonymity carrier unmeasured | **S** (CR) + **B** (holder-anonymity / ZK simulator advantage) |
| **Custom** | PARAMETRIC: the app supplies `(circuit, relation, bridge)`; `extractable` for its AIR | `cell/src/predicate.rs:300 Custom { vk_hash }` + `cell/src/custom_effect.rs` registry | App-dependent | **vk_hash content-addressing** binds the *registration*, but NOT the app's bridge proof to its Rust AIR | **B** (entirely app-defined; inherits the §8 discipline only if the app meets its bridge obligation) |

**Underlying STARK verifier** (shared by all proof-bearing kinds):
`circuit/src/stark.rs:1346 verify` / `:1384 verify_full`. It performs a **real
FRI verification** with `air_name` domain-separation binding
(`stark.rs:1383-48`), public-input equality (`:1404`), query-count checks
(`:1379`), dynamic blowup from constraint degree, and a Fiat-Shamir transcript.
This is the realization of every `extractable` carrier. Its soundness is the
single largest TCB item (see §4).

---

## 2. Where Pedersen-via-UC sets the bar — and who is furthest from it

**Pedersen is the gold standard of conformance**, and it is worth being precise
about *why*, because that "why" is the yardstick for everything else.

For Pedersen, **three** distinct things are true at once:

1. **The impl is a real, standard primitive.** `commit(v,r)=v·V+r·R` over
   Ristretto (`value_commitment.rs:68`, curve25519-dalek), generators by
   hash-to-point with unknown DLog relation. This is textbook Pedersen.
2. **The Lean-assumed carriers are discharged in a real proof tool, against
   real AFP lemmas.** `Crypto/UCBridge.lean` carries `FComDischarge`, whose
   fields name the CryptHOL theorems (`pedersen.pedersen_bind`,
   `pedersen.abstract_perfect_hiding`) that establish `binding` reduces to DLog
   and hiding is perfect. The dregg2 `commit` was *transported* into
   `uc-crypthol/Dregg2_FCom.thy` and the realization theorem
   (`dregg2_pedersen_realizes_F_com`) proved there.
3. **The one law the metatheory actually leans on is PROVED in Lean**, not
   carried: `commit_hom` (`Primitives.lean:55`) → `commit_sum` → conservation
   (`Pedersen.lean:63-283`).

So Pedersen's TCB is: **DLog hardness** (standard) + **two kernels' soundness +
the transport fidelity** (the honest residual, spelled out in
`UCBridge.lean:29-46`). Nothing about the *commitment math* is taken on faith
in Lean.

**No other kind reaches all three bars.** Ranked by distance from the Pedersen
bar (furthest first):

- **Custom (furthest).** Entirely app-defined; the §8 discipline is *inherited
  only if* the registering app proves its own bridge. No UC, no fingerprint of
  the app's circuit, no standard-assumption guarantee. Riskiest by
  construction — but that risk is explicit and localized to the `vk`.
- **Bridge.** Real AIR exists but is **not wired in production** (fails closed,
  `membership_verifier.rs:621`); no fingerprint binding. Its carriers
  (`compress` CR + FRI) are standard, but conformance is *unmeasured* because
  the production path never exercises it.
- **BlindedSet.** Membership recomposition is fine (reuses Merkle), but the
  **holder-anonymity carrier** (`HolderAnonymity.ViewIndistinguishable`,
  `BlindedSet.lean:137-150`) is a ZK-simulator/advantage obligation with **no
  measurement at all** — no UC transport, no game, no test. This is the bespoke
  (B) risk closest in spirit to what UC closed for Pedersen's hiding, but for
  BlindedSet it remains an unmeasured `Prop`.
- **NonMembership / Temporal / Dfa.** Standard assumptions (CR and/or FRI
  only), real AIRs, real STARK verifiers wired in production — but **no
  fingerprint binding**, so "the AIR the backend runs IS the AIR Lean proved
  the bridge for" is *asserted by name string*, not machine-checked.
- **Merkle (closest, but below Pedersen).** Has the **fingerprint binding**
  (the one machine check beyond Pedersen's UC), real Poseidon2, real STARK
  verifier in production. Still below Pedersen because the carrier
  (`collisionHard`) is *not* discharged in any proof tool — it is a named
  standard assumption only, and the Poseidon2 KAT is a frozen self-snapshot
  (§3).

The shape of the gap is therefore: **Pedersen has a cross-system proof
(UC) AND a near-impl check; Merkle has the impl check (fingerprint) but no
cross-system proof; the middle four have neither; Bridge/BlindedSet/Custom have
neither and additional unmeasured risk on top.**

---

## 3. Conformance gaps found in the real code (the honest specifics)

These are the concrete `file:line` facts a swap must not paper over.

### 3.1 Two registries, and the production one must be wired by the host

`cell/src/predicate.rs` ships **two** built-in registry constructors:

- `with_stubs()` (`:725`) installs `StubVerifier`s. **The stub accepts on any
  non-empty proof bytes** (`predicate.rs:1226` impl; it only rejects empty
  bytes, `:54-58`). This is a TEST registry — using it in production would be a
  total soundness hole.
- `default_builtins()` (`:792`) installs `NotYetWiredVerifier`s
  (`:1285-1350`), which **fail closed** — they reject everything with an
  instruction to wire the real verifier. This is the safe default.

The **real, STARK-backed verifiers** are NOT in `dregg-cell`; they live in
`turn/src/executor/membership_verifier.rs` and must be installed by the host:
`registry_with_real_verifiers()` (`:597`) and
`registry_with_real_verifiers_full(...)` (`:658`). The swap-readiness
implication: **the Lean `verify` oracle's soundness is only realized when the
host wires `registry_with_real_verifiers_full`**, not the bare `dregg-cell`
defaults. This is correct fail-closed design, but it is load-bearing and
unchecked-by-construction (nothing forces the host to wire the real one).

### 3.2 PedersenEquality production path is Bulletproofs, NOT the Lean STARK AIR

The Lean Pedersen kind (`Crypto/Pedersen.lean`) models a **STARK conservation
AIR** (commitment-sum balance + per-note bit-decomposition range gadget). But
the production verifier wired for `PedersenEquality` is
`PedersenBulletproofVerifier` (`membership_verifier.rs:557`), which verifies a
**Bulletproof range proof** (`cell/src/value_commitment.rs::verify_range_bytes`).

These are both sound under DLog, and both enforce non-negativity — but they are
**different proof systems** verifying **different statements** through
**different code**. The Lean bridge's `extractable` carrier is stated for the
STARK conservation AIR; the running verifier is a Bulletproof. The conservation
*algebra* (`commit_hom`) is shared and UC-discharged, so the binding is sound,
but **the `extractable` interface Lean assumes is not the one the production
verifier provides**. A swap must either (a) wire the STARK conservation AIR Lean
models, or (b) re-home the Lean `extractable` carrier onto the Bulletproof
verifier's soundness. Today neither is done; the conformance is *by shared
algebra*, not *by matching verifier*.

### 3.3 Fingerprint binding covers only kernel + Merkle

`dregg-lean-ffi` proves the AIR-shape fingerprint of the Lean-emitted circuit
equals the Rust-native AIR for exactly two AIRs: the kernel step AIR
(`circuit_decode.rs:330 kernel_air_shape_*`) and the Merkle Poseidon2 AIR
(`:855 merkle_air_shape_native`), with tamper checks
(`circuit_differential.rs:132,253`). **There is no emitter or fingerprint for
NonMembership, Temporal, Dfa, Bridge, or BlindedSet.** For those five, the
binding "the AIR the backend runs is the AIR Lean proved the bridge for" rests
on the `air_name` string match inside `stark::verify` (`stark.rs:1383`) — a
real check, but a *name* check, not a *shape* check. An AIR with the same name
but a different constraint set would pass the name check and fail the
fingerprint check; only Merkle/kernel get the latter.

### 3.4 The Poseidon2 KAT is a frozen self-snapshot, not a cross-check

`circuit/src/poseidon2.rs` carries the right structure (width 16, x^7 S-box,
8 external + 13 internal rounds, Plonky3-sourced round constants, `:1-16`) and
two known-answer tests (`:561 poseidon2_known_answer_vector`, `:590
hash_4_to_1_known_answer`). But the expected outputs are **"frozen from
implementation"** (`:570`) — i.e. a regression snapshot of *this* code, **not a
vector cross-checked against the `p3-baby-bear` reference permutation output**.
So the KAT catches *drift* but does NOT independently certify that the
permutation equals Plonky3's. If the round structure had a subtle bug, the KAT
would happily freeze the buggy output. `collisionHard` is assumed of the
*correct* Poseidon2; the test only pins *this* Poseidon2. (The Pedersen
generators, by contrast, are real curve25519-dalek hash-to-point — no such
snapshot concern.)

### 3.5 BlindedSet holder-anonymity is an unmeasured `Prop`

`HolderAnonymity.ViewIndistinguishable` (`BlindedSet.lean:137-150`) is the only
carrier in the eight kinds that is a *privacy / indistinguishability* advantage
bound with **no discharge anywhere** — no UC transport (unlike Pedersen's
hiding), no game, no statistical test. The `Reference` instance discharges it
with `view := const 0` (`BlindedSet.lean:409`), which is honest non-vacuity but
tells us nothing about the real blinded transcript. This is the one bespoke
privacy claim furthest from any measurement.

---

## 4. The definitive crypto-TCB enumeration (running system)

These are the things **assumed sound but not proved** that the running system's
soundness/privacy rests on. Each is tagged **S** (standard, well-studied) or
**B** (bespoke / riskier), with the residual honestly stated.

**Computational hardness assumptions (standard):**

1. **FRI / STARK soundness** (`extractable`, all proof kinds) — FRI proximity +
   Fiat-Shamir non-interactivity over BabyBear. **S.** Cited literature:
   `deep-fri`, `proximity-gaps-reed-solomon`, `whir`/`stir`. *Residual:* the
   *concrete parameter choices* (NUM_QUERIES · log₂ blowup ≥ target bits,
   `stark.rs:537-552`) give a claimed ~128-bit floor; this is a parameter
   audit, not a proof. The verifier code is hand-rolled (not Plonky3's own
   verifier), so its *correctness* is also in the TCB.
2. **Poseidon2 collision-resistance** (`collisionHard`; Merkle, NonMembership,
   Bridge, BlindedSet). **S.** *Residual:* §3.4 — the impl is pinned by a frozen
   self-snapshot KAT, not cross-checked against the Plonky3 reference vector.
3. **Discrete-log hardness on Ristretto** (`binding`; Pedersen). **S, and the
   best-discharged of all** — reduced to DLog in CryptHOL (`UCBridge.lean`),
   modulo the two-kernel + transport-fidelity caveat (`UCBridge.lean:29-46`).
4. **BLAKE3 as a domain-keyed PRF/hash** — used for the AIR fingerprint
   (`circuit_decode.rs:273`) and various commitments. **S.** Not a §8 carrier
   per se, but in the TCB of the conformance *check* itself.

**Privacy / indistinguishability assumptions:**

5. **Pedersen perfect hiding** (`unlinkable`, hiding half). **S** — discharged
   in CryptHOL (`abstract_perfect_hiding`).
6. **BlindedSet holder anonymity** (`ViewIndistinguishable`). **B** — unmeasured
   (§3.5). The riskiest privacy claim.
7. **Nullifier / stealth unlinkability** (`unlinkable`, the anonymity half
   beyond hiding). **B** — carried as a `Prop`, no discharge; the determinism
   half is the only part the metatheory uses, and that is free (function-ness).

**Conformance / wiring assumptions (not crypto hardness, but in the TCB for the
running system to match Lean):**

8. **The host wires the real verifier registry** (`registry_with_real_verifiers_full`),
   not stubs/fail-closed (§3.1). **B** (operational; unchecked by construction).
9. **The five un-fingerprinted AIRs match their Lean bridges** by `air_name`
   only (§3.3). **B** (no shape check).
10. **PedersenEquality's running Bulletproof verifier soundness re-homes the
    Lean STARK `extractable`** (§3.2). **B** (verifier mismatch; sound by shared
    algebra, not by matching interface).
11. **Custom `vk` apps meet their own bridge obligation** (`Custom.lean`). **B**
    (delegated entirely to the app).

**Proved in Lean, NOT in the TCB** (for contrast — the discipline working):
every `*_bridge` (both directions), `commit_hom`/`commit_sum`/conservation,
the range gadget (`RecordCircuit.range_iff`), `sorted_gap_excludes`, the DFA
run combinatorics, the registry-cascade dispatch soundness, the dial
confinement, and the `emit_faithful` / `emit_faithful_merkle` extraction
faithfulness. All `#assert_axioms`-clean.

---

## 5. Recommendations to RAISE conformance — ranked by risk-reduction-per-effort

Ranked so the cheapest, highest-leverage items come first.

1. **(S, cheapest, highest leverage) Cross-check the Poseidon2 KAT against the
   `p3-baby-bear` reference.** Add a test that runs the *Plonky3* permutation
   (already a dependency in the workspace, per `poseidon2.rs:3`) on the same
   input and asserts equality with `Poseidon2State::permute`. Turns §3.4's
   frozen snapshot into an independent certification of `collisionHard`'s
   subject. ~20 lines; closes the single most quietly-dangerous gap (a
   permutation bug would silently invalidate every hash-based kind at once).

2. **(B → checked, cheap) Add a compile-/startup-time assertion that the host
   wired the real registry.** A `debug_assert`/typed-newtype that the executor
   path cannot run witnessed predicates against `with_stubs()`/`default_builtins()`.
   Closes §3.1's "unchecked by construction" without new crypto. The
   `NotYetWiredVerifier` fail-closed default already makes the *unsafe* outcome
   loud; this makes the *safe* wiring mandatory.

3. **(B, moderate) Extend the fingerprint-binding emitter to Temporal, Dfa,
   NonMembership.** These three have real production verifiers and standard-only
   assumptions; the missing piece is the *shape* check (§3.3). The emitter
   machinery already exists (`CircuitEmit.lean` PART III emits all the algebraic
   `ConstraintExpr` forms — `Equality`/`Binary`/`Polynomial`/`Gated`/`Lookup`
   is the only residual). Per-AIR effort is one `emittedX`/`emit_faithful_X` in
   Lean + one `X_air_shape_native` in `circuit_decode.rs`. Highest
   per-AIR value: Temporal/Dfa (pure range/lookup, no hash residual).

4. **(B, moderate) Resolve the PedersenEquality verifier mismatch (§3.2).**
   Either wire the STARK conservation AIR the Lean kind models (preferred — it
   unifies with the rest of the STARK-native cascade) OR add a Lean
   `PedersenBulletproofKernel` whose `extractable` is stated for the Bulletproof
   verifier's soundness. The former is the "improve, don't degrade" choice.

5. **(B, larger) A UC / game-based transport for BlindedSet holder anonymity
   (§3.5)** — the analog of what `UCBridge.lean` did for Pedersen hiding. This
   is the highest-effort item but the only one that turns a *bespoke* (B)
   privacy claim into a discharged one. Lower priority than 1–4 because the
   *soundness* (membership) is already fine via Merkle reuse; this is purely the
   *privacy* advantage bound.

6. **(B, ongoing) Wire and fingerprint-bind the Bridge AIR**, removing its
   production fail-closed status — only once a cross-chain bridge path is
   actually needed; until then fail-closed is the correct posture.

7. **(B, per-app) For Custom kinds, require the app to ship its bridge proof +
   a fingerprint of its registered AIR** as part of `vk` registration, so the
   §8 discipline is *enforced* at registration rather than *assumed*.

---

## 6. Smallest first verifiable increment

**Add the Plonky3 cross-check KAT for Poseidon2** (Recommendation 1).

Rationale for picking this as the smallest increment:
- It is ~20 lines in `circuit/src/poseidon2.rs` tests, no new crate, no Lean.
- It is independently *verifiable* in one `cargo test -p dregg-circuit`.
- It closes the gap with the **widest blast radius**: `collisionHard` is the
  carrier shared by four of the eight kinds (Merkle, NonMembership, Bridge,
  BlindedSet) and by the FRI Merkle-commitment layer itself. A frozen-snapshot
  KAT cannot catch a permutation-correctness bug; a reference cross-check can.
- It moves Merkle measurably *toward* the Pedersen bar: Merkle already has the
  fingerprint (impl ↔ Lean AIR shape); this adds the missing impl ↔ *standard
  reference* check, leaving only "no proof-tool discharge of CR" as the gap
  between Merkle and Pedersen — and that gap is inherent to CR (there is no AFP
  Poseidon2-CR lemma to transport, unlike Pedersen's DLog reduction).

**Acceptance test for the increment:** a new `#[test]` in `poseidon2.rs` that
imports the `p3-baby-bear` Poseidon2 permutation, runs it on input `[0..15]`,
and asserts the 16 output felts equal `Poseidon2State::permute`'s output (the
same input the existing `poseidon2_known_answer_vector` uses), so the frozen
snapshot becomes a *derived* equality rather than a *pinned* one.

---

## 7. One-paragraph verdict

The running system's cryptographic TCB is **mostly standard and mostly
honest**: real Poseidon2 over BabyBear, real Pedersen over Ristretto, real
FRI-STARK verification with `air_name` binding, and real production verifiers
(once the host wires `registry_with_real_verifiers_full`). The Lean §8
boundary's two assumed families — Layer-A carriers (`collisionHard`/`binding`/
`unlinkable`) and per-kind `extractable` — map to genuine impls for all eight
kinds, and **Pedersen is fully conformant**: real curve, UC-discharged carriers,
and the one load-bearing law (`commit_hom`) proved in Lean. The gaps are not
"placeholder crypto" — they are **conformance gaps**: (i) only kernel + Merkle
have the AIR-shape fingerprint check, the other five rest on a name-string
match; (ii) the production PedersenEquality verifier is a Bulletproof, not the
STARK AIR the Lean kind models — sound by shared algebra, not matching
interface; (iii) the Poseidon2 KAT is a frozen self-snapshot, not a Plonky3
cross-check; (iv) BlindedSet holder-anonymity is an unmeasured advantage bound;
(v) the real-verifier wiring is correct-but-unenforced (stubs accept, defaults
fail-closed, real ones live one crate up). None of these is fatal; all are
nameable and fixable, and the smallest, widest-leverage first step is a 20-line
Plonky3 cross-check of the Poseidon2 permutation.
