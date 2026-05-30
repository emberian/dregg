/-
# Dregg2.Crypto.VerifierKernel — Layer B: `verify` as a DISCHARGEABLE contract.

**The heart of the overhaul (`PHASE-CRYPTOKERNEL.md §2.2`).** The flat `CryptoKernel.verify`
is a bare oracle with NO law. This layer replaces it with a verifier whose soundness is
**derived from a circuit bridge**, generalizing `Circuit.lean`'s `verify_law_derivable` off
the toy `kernelCircuit` onto a real per-kind gadget (here: Merkle, `Crypto/Merkle.lean`).

The shape (mirroring the real `stark::verify(air, proof, public_inputs)`):

  * a `Statement` (the public-input vector — for Merkle, `(root, leaf)`);
  * `verify : Statement → Proof → Bool`, the §8 oracle;
  * `extractable : Prop` — the ONE genuine cryptographic carrier: STARK soundness (FRI
    proximity + Fiat-Shamir) gives "verify accepts ⇒ a satisfying trace EXISTS". A `Prop`,
    never proved in Lean, never `sorry` — the single trust boundary;
  * `verify_sound` — a DERIVED THEOREM: `verify accepts → Relation holds`, obtained by
    composing `extractable` (accept ⇒ a satisfying circuit) with the gadget `bridge` (a
    satisfying circuit ⇔ the relation). The verify LAW is no longer assumed; it is the
    bridge ∘ extractability composition.

For Merkle, `verify_sound` is `merkle_verify_sound`: an accepted Merkle proof proves
`MerkleMembers root leaf`, with the ONLY assumption being `extractable` (STARK soundness) —
the recomposition itself is fully proved (`merkle_bridge`, no primitive seam).
-/
import Dregg2.Crypto.Merkle
import Dregg2.Tactics

namespace Dregg2.Crypto

open Dregg2.Crypto.Merkle

universe u

/-! ## The Merkle verifier kernel — `verify` + `extractable` carrier + DERIVED `verify_sound`. -/

/-- **Layer B — the Merkle `VerifierKernel`.** Bundles the per-kind statement public-inputs
`(root, leaf)`, the §8 `verify` oracle, and the STARK-soundness `extractable` carrier
together with the DERIVED soundness law `verify_sound`.

`extractable` is the genuine cryptographic obligation (FRI + Fiat-Shamir): if `verify`
accepts a Merkle statement+proof, then a circuit satisfying the AIR exists (a real trace was
committed). The `verify_sound` field is then DERIVED off `merkle_bridge` — the metatheory
proves "accept ⇒ membership" *given* `extractable`, never assuming the membership law itself. -/
class MerkleVerifierKernel (Digest : Type u) (Proof : Type u) where
  /-- The abstract Poseidon2 node hash (the Layer-A `compress`; CR is `collisionHard`). -/
  compress : Digest → Digest → Digest
  /-- **The §8 verify oracle** (`stark::verify` for the Merkle AIR): does `proof` discharge
  the statement `(root, leaf)`? An opaque `Bool`; its soundness is the carried `extractable`. -/
  verify : Digest → Digest → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI proximity + Fiat-Shamir): "`verify`
  accepts ⇒ a satisfying trace EXISTS". The single trust boundary; a `Prop`, never proved,
  never `sorry`. Stated as the per-statement implication the crypto layer discharges. -/
  extractable : Prop
  /-- The extractability `Prop` UNPACKED to its operational content: an accepted proof
  witnesses a satisfying circuit. This is the named form the bridge composes with — it IS
  `extractable` made usable, and is precisely the STARK soundness obligation. -/
  extract : extractable →
    ∀ (root leaf : Digest) (proof : Proof), verify root leaf proof = true →
      ∃ circuit : CircuitIR Digest, Satisfies compress circuit root leaf

variable {Digest Proof : Type u}

/-- **`merkle_verify_sound` — the DERIVED verify law (`PHASE-CRYPTOKERNEL.md §5.3`).** Given
the STARK-soundness carrier `extractable`, an accepted Merkle proof PROVES membership:

    verify root leaf proof = true  →  MerkleMembers compress root leaf

The proof composes `extract` (accept ⇒ satisfying trace, the crypto carrier) with
`merkle_bridge` (satisfying trace ⇔ membership, FULLY proved). The verify law is DERIVED, not
assumed — exactly `Circuit.lean`'s `verify_law_derivable` move, now on the real Merkle gadget.
The ONLY hypothesis is `extractable`; everything else is proved. -/
theorem merkle_verify_sound [K : MerkleVerifierKernel Digest Proof]
    (hext : K.extractable) (root leaf : Digest) (proof : Proof)
    (haccept : K.verify root leaf proof = true) :
    MerkleMembers K.compress root leaf :=
  (merkle_bridge K.compress root leaf).mp (K.extract hext root leaf proof haccept)

/-! ## A `Reference` (test) verifier kernel — non-vacuity witness over `ℤ`.

A trivial lawful instance: `compress := (+)`, `verify` accepts iff the proof echoes a trivial
self-hash trace, and `extractable := True` discharged by exhibiting that trace. Witnesses the
interface is inhabitable, so `merkle_verify_sound` is non-vacuous. NOT real crypto. -/
namespace Reference

/-- Reference: `verify root leaf proof` accepts iff `proof = root` AND `root` is the
single-level self-hash of `leaf` (`compress leaf leaf = root`, encoded in the proof as a
flag). For the toy `ℤ` model with `compress := (+)`, `root = leaf + leaf` is the witness. -/
instance instMerkleVerifierKernel : MerkleVerifierKernel Int Int where
  compress a b := a + b
  -- accept iff the proof equals the claimed (single-level) root = leaf + leaf
  verify root leaf proof := decide (proof = root ∧ root = leaf + leaf)
  extractable := True
  extract := by
    intro _ root leaf proof haccept
    simp only [decide_eq_true_eq] at haccept
    obtain ⟨_, hroot⟩ := haccept
    -- a single self-hash level: current = leaf, sib = leaf, parent = leaf + leaf = root
    refine ⟨⟨[{ current := leaf, sib := leaf, position := 0, parent := leaf + leaf }]⟩, ?_⟩
    refine ⟨_, _, rfl, rfl, rfl, hroot.symm, ?_, ?_⟩
    · intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; rfl
    · trivial

/-- Non-vacuity: at the reference kernel `merkle_verify_sound` is inhabited — an accepted
toy proof yields a genuine `MerkleMembers` witness. -/
example (leaf : Int) :
    MerkleMembers (Digest := Int) (· + ·) (leaf + leaf) leaf :=
  merkle_verify_sound (K := instMerkleVerifierKernel) trivial (leaf + leaf) leaf (leaf + leaf)
    (decide_eq_true ⟨rfl, rfl⟩)

end Reference

-- TRIPWIRE: the derived verify law rests ONLY on the `extractable` carrier (passed as a
-- hypothesis), never on a hidden `sorry` — kernel-clean.
#assert_axioms merkle_verify_sound

end Dregg2.Crypto
