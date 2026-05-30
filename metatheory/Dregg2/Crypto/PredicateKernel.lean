/-
# Dregg2.Crypto.PredicateKernel — Layer C: per-kind circuit obligations + the DIAL wiring.

**The third layer (`PHASE-CRYPTOKERNEL.md §2.3, §5.4`).** Lifts `Authority/Predicate.lean`'s
registry so each `WitnessedKind` carries (i) its statement algebra, (ii) its circuit, (iii)
its `Dial` floor — and finally WIRES `EpistemicDial` to the per-kind verifier (the dial's
`accepts` no longer floats above the portal; it is pinned to the kind's verify seam).

This module lands the FIRST kind end-to-end — **Merkle membership** — composing the cascade:

    merkle_verify_sound (Layer B)   accept ⇒ MerkleMembers      [derived off the bridge]
      ∘ registry_sound (Predicate)  accept ⇒ Discharged          [the dispatch keystone]
      ∘ DiscloseAt @ acceptanceOnly the dial pinned to verify    [blinded ⇒ ZK floor]

`merkleKindObligation` records `(circuit-relation, statement, dial floor = acceptanceOnly)`:
blinded Merkle membership sits at the zero-knowledge floor (`EpistemicDial.Dial.acceptanceOnly`),
the one-bit disclosure notch — the verifier learns "it is a member" and nothing about WHICH
leaf. `merkle_dial_wired` instantiates `DiscloseAt` so its `accepts` IS the kind's verify seam
at that floor, discharging the design's "the dial floats above the portal" gap.
-/
import Dregg2.Crypto.VerifierKernel
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.PredicateKernel

open Dregg2.Crypto Dregg2.Crypto.Merkle Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-! ## The per-kind obligation record (statement algebra + relation + dial floor).

Universe note: the registry/dial machinery (`Verifiable`, `Registry`, `DiscloseAt`) lives at
`Type` (universe 0), so this Layer-C wiring instantiates `Digest`/`Proof` at `Type`. The
`MerkleVerifierKernel` (universe-polymorphic) restricts cleanly to `Type`. -/

/-- **`KindObligation`** — per-kind discharge data (`PHASE-CRYPTOKERNEL.md §2.3`). For a kind
over `Digest`/`Proof`, records the public-input `Statement` type, the `relation` the AIR
encodes (proved equivalent to circuit-satisfiability by the gadget bridge), and the `dialFloor`
— the epistemic boundary this kind discloses at. The circuit itself lives in the gadget module
(`Crypto/Merkle.lean`); this record names the statement algebra and the dial position. -/
structure KindObligation (Digest Proof : Type) where
  /-- The public-input algebra for this kind (e.g. `Digest × Digest` for Merkle `(root,leaf)`). -/
  Statement : Type
  /-- The relation the AIR encodes (membership, for Merkle), as a predicate on the statement. -/
  relation : Statement → Prop
  /-- The epistemic disclosure floor (`EpistemicDial.Dial`). -/
  dialFloor : Dial

/-! ## The Merkle kind — statement `(root, leaf)`, relation `MerkleMembers`, floor `acceptanceOnly`. -/

variable {Digest Proof : Type}

/-- **The Merkle kind's obligation.** Statement = `(root, leaf)`; relation = `MerkleMembers`
(membership recomposition); **dial floor = `acceptanceOnly`** — blinded Merkle membership
discloses ONE bit (it verifies), hiding which leaf (the ZK floor, `PHASE-CRYPTOKERNEL.md §5.4`:
"blinded ⇒ ZK floor"). -/
def merkleKindObligation [K : MerkleVerifierKernel Digest Proof] :
    KindObligation Digest Proof where
  Statement := Digest × Digest
  relation := fun s => MerkleMembers K.compress s.1 s.2
  dialFloor := Dial.acceptanceOnly

@[simp] theorem merkleKindObligation_floor [MerkleVerifierKernel Digest Proof] :
    (merkleKindObligation (Digest := Digest) (Proof := Proof)).dialFloor = Dial.acceptanceOnly :=
  rfl

/-! ## The cascade — registry dispatch ∘ derived verify-soundness, per kind. -/

/-- The Merkle verifier plugin for the registry: the §8 `verify` oracle wrapped to the
`Verifier (Digest × Digest) Proof` shape (statement = `(root, leaf)`). -/
def merkleVerifier [K : MerkleVerifierKernel Digest Proof] :
    Verifier (Digest × Digest) Proof :=
  fun s proof => K.verify s.1 s.2 proof

/-- **`merkle_registry_cascade` — the FIRST end-to-end §8 discharge (PROVED).** Registering
the Merkle kind with its `verify` oracle, an accepted proof both (a) `Discharged`s the kind's
predicate (the registry-dispatch keystone, `registry_sound`) AND (b) — given the STARK
`extractable` carrier — PROVES `MerkleMembers` (the derived `merkle_verify_sound`). This is the
cascade `registry_sound ∘ merkle_verify_sound`: "verify accepts ⇒ admissible (Lean, proved) ∘
verify accepts ⇒ it actually happened (STARK carrier)". The single trust boundary is
`extractable`; the membership recomposition itself is fully proved. -/
theorem merkle_registry_cascade [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable)
    (base : Registry (Digest × Digest) Proof)
    (root leaf : Digest) (proof : Proof)
    (haccept : K.verify root leaf proof = true) :
    let reg : Registry (Digest × Digest) Proof :=
      fun j => if j = .merkleMembership then some merkleVerifier else base j
    (@Discharged (Digest × Digest) Proof (verifiableOfRegistry reg .merkleMembership)
        (root, leaf) proof)
      ∧ MerkleMembers K.compress root leaf := by
  intro reg
  refine ⟨?_, merkle_verify_sound hext root leaf proof haccept⟩
  apply registry_sound reg .merkleMembership (root, leaf) proof
  show registryVerify reg .merkleMembership (root, leaf) proof = true
  unfold registryVerify
  simp only [reg, if_pos rfl]
  exact haccept

/-- The Merkle-kind registry: the §8 `verify` oracle installed at `merkleMembership`. -/
def merkleReg [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) : Registry (Digest × Digest) Proof :=
  fun j => if j = .merkleMembership then some merkleVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (named `def`, passed explicitly via
`@` so `Discharged`/`DiscloseAt` share ONE instance — `base` is explicit, so this is not an
auto-synthesized `instance`). -/
@[reducible] def merkleSeam [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) : Verifiable (Digest × Digest) Proof :=
  verifiableOfRegistry (merkleReg base) .merkleMembership

/-! ## THE DIAL WIRING — `DiscloseAt` instantiated at the Merkle kind's floor.

The design's gap: `EpistemicDial.accepts` floats above the portal — it is pinned to abstract
`Discharged pred wit`, not to a per-kind kernel verifier. Here we CLOSE it: build a
`DiscloseAt` whose `pred`/`wit` are the Merkle statement/proof and whose `accepts` at every
notch is `Discharged (root,leaf) proof` under the registry-at-`merkleMembership` seam — so the
dial's acceptance bit IS the Merkle verifier's bit, at the `acceptanceOnly` floor. -/

/-- **`merkleDisclose` — the dial pinned to the Merkle verifier.** A `DiscloseAt` over the
trivial information order `Unit` (the leaked-info coarsening is not the point here; the wiring
is), whose `accepts d := Discharged (root,leaf) proof` (position-independent: the verifier
consults the witness, never the dial), `accepts_eq := fun _ => Iff.rfl`. This realizes the
design's "instantiate `DiscloseAt` at the `acceptanceOnly` floor (blinded membership)". -/
def merkleDisclose [MerkleVerifierKernel Digest Proof]
    (base : Registry (Digest × Digest) Proof) (root leaf : Digest) (proof : Proof) :
    @DiscloseAt Unit (Digest × Digest) Proof _ (merkleSeam base) :=
  letI : Verifiable (Digest × Digest) Proof := merkleSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := (root, leaf)
    wit := proof
    accepts := fun _ => Discharged (root, leaf) proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`merkle_dial_wired` — THE DIAL WIRING (PROVED, `PHASE-CRYPTOKERNEL.md §5.4`).** The
Merkle kind's epistemic floor is the ZK `acceptanceOnly` notch, and at that floor the dial's
acceptance bit IS exactly the Merkle verifier's `Discharged` bit (`accepts_bot_iff_discharged`).
Plus: given STARK `extractable`, that accepting bit PROVES `MerkleMembers` — so the dial's
bottom notch, the registry dispatch, and the membership relation are all ONE wired cascade.
This discharges "the dial floats above the portal": `accepts ⊥` is pinned to the per-kind
verifier. -/
theorem merkle_dial_wired [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable)
    (base : Registry (Digest × Digest) Proof) (root leaf : Digest) (proof : Proof) :
    -- (1) the floor is acceptanceOnly:
    (merkleKindObligation (Digest := Digest) (Proof := Proof)).dialFloor = Dial.acceptanceOnly ∧
    -- (2) the dial's bottom notch accepts IFF the Merkle verifier discharges:
    (@DiscloseAt.accepts Unit (Digest × Digest) Proof _ (merkleSeam base)
        (merkleDisclose base root leaf proof) (⊥ : Dial)
      ↔ @Discharged (Digest × Digest) Proof (merkleSeam base) (root, leaf) proof) ∧
    -- (3) and an accepting Merkle proof at the floor PROVES membership (the cascade):
    (K.verify root leaf proof = true → MerkleMembers K.compress root leaf) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Digest × Digest) Proof _ (merkleSeam base)
      (merkleDisclose base root leaf proof)
  · exact fun haccept => merkle_verify_sound hext root leaf proof haccept

/-! ## `Reference` — the whole cascade end-to-end at the toy kernel (non-vacuity witness). -/

namespace Reference

open Dregg2.Crypto.Reference

/-- The empty base registry over the toy `ℤ` statement/proof. -/
def base : Registry (Int × Int) Int := fun _ => none

/-- Non-vacuity: at the reference Merkle verifier kernel, an accepted toy proof drives the
FULL cascade — it `Discharged`s the registry predicate AND proves `MerkleMembers`. This
witnesses `merkle_registry_cascade` is not over an empty world. -/
example (leaf : Int) :
    (@Discharged (Int × Int) Int
        (verifiableOfRegistry (merkleReg base) .merkleMembership)
        (leaf + leaf, leaf) (leaf + leaf))
      ∧ MerkleMembers (Digest := Int) (· + ·) (leaf + leaf) leaf :=
  merkle_registry_cascade (K := instMerkleVerifierKernel) trivial base (leaf + leaf) leaf
    (leaf + leaf) (decide_eq_true ⟨rfl, rfl⟩)

/-- Non-vacuity: the dial wiring holds at the reference kernel — the floor is `acceptanceOnly`,
the dial's bottom notch is the verifier's bit, and an accepting proof proves membership. -/
example (leaf : Int) :
    (merkleKindObligation (Digest := Int) (Proof := Int)).dialFloor = Dial.acceptanceOnly :=
  (merkle_dial_wired (K := instMerkleVerifierKernel) trivial base (leaf + leaf) leaf
    (leaf + leaf)).1

end Reference

-- TRIPWIRES: the cascade + dial wiring are kernel-clean; the ONLY cryptographic content is
-- the `extractable` carrier (passed as a hypothesis), never a hidden `sorry`.
#assert_axioms merkle_registry_cascade
#assert_axioms merkle_dial_wired

end Dregg2.Crypto.PredicateKernel
