/-
# Dregg2.Crypto.Primitives — Layer A of the CryptoKernel split (the real operations,
real algebraic laws; computational hardness as `Prop` CARRIERS).

**The overhaul (`docs/rebuild/PHASE-CRYPTOKERNEL.md §2.1`).** The flat `CryptoKernel`
collapsed *algebraic* laws (proved, used by the metatheory) and *computational* obligations
(carried, discharged by the crypto layer) and — worse — used `hash_inj` (idealized
INJECTIVITY) where the real Poseidon2 is only collision-RESISTANT. That is the wrong KIND of
assumption. This layer fixes the discipline:

  * **algebraic laws ⇒ PROVED fields** the metatheory relies on: `commit_hom` (Pedersen
    additive homomorphism — the one genuinely-grounded law, the template); `nullifier`
    determinism (its function-ness).
  * **computational hardness ⇒ `Prop` CARRIERS** the crypto layer discharges, never proved
    in Lean: `collisionHard` (Poseidon2 CR — replaces the wrong `hash_inj`), `binding`
    (Pedersen/DLog binding), `unlinkable` (stealth/nullifier anonymity).

`compress`/`compressN` name the real Poseidon2 4-to-1 / sponge (`circuit/src/poseidon2.rs`,
the in-circuit Merkle/leaf hash). They are uninterpreted here; their ONLY law is the
carried `collisionHard` — never an equational idealization. This is the
`EpistemicDial.lean:489-503` discipline generalized to the whole primitive portal.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

namespace Dregg2.Crypto

universe u

/-- **Layer A — `CryptoPrimitives`.** The real cryptographic operations with their
*actual* algebraic laws, plus the computational-hardness obligations as `Prop` carriers.

`Digest` is the hash/commitment carrier (`AddCommGroup` because Pedersen commitments
compose). The split is the whole point: `compress`/`compressN`/`commit`/`nullifier` are
operations; `commit_hom` is the one PROVED-grade algebraic law (the metatheory uses it);
`collisionHard`/`binding`/`unlinkable` are `Prop` carriers — the genuine cryptographic
assumptions (Poseidon2 CR, DLog binding, anonymity advantage), NEVER a Lean law, NEVER
`sorry`, discharged by the circuit/crypto layer. -/
class CryptoPrimitives (Digest : Type u) [AddCommGroup Digest] where
  /-- **Poseidon2 4-to-1 compression** (`hash_2_to_1` / the Merkle node hash). Two-input
  form; the real one is the arity-tagged permutation over BabyBear. Uninterpreted — its
  collision-resistance is the carried `collisionHard`, NOT an equational law. -/
  compress : Digest → Digest → Digest
  /-- **Poseidon2 sponge** (`hash_many`): absorb a list of digests, squeeze one. The
  variable-arity hash for the leaf/transcript. Uninterpreted; CR is `collisionHard`. -/
  compressN : List Digest → Digest
  /-- **CARRIER — collision-resistance of Poseidon2** (the CORRECT assumption; replaces
  the wrong idealized `hash_inj`). "No PPT adversary finds `x ≠ y` with `compress`/`compressN`
  colliding." A `Prop` the crypto layer discharges; never proved, never `sorry`. -/
  collisionHard : Prop
  /-- **Pedersen commitment** `commit value blinding` over the curve. -/
  commit : Int → Int → Digest
  /-- **LAW (PROVED-grade, algebraic) — additive homomorphism**: the one genuinely-grounded
  Pedersen law the metatheory relies on (conservation over hidden amounts). -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- **CARRIER — Pedersen/DLog binding**: the load-bearing soundness (you cannot open a
  commitment two ways). A `Prop` carrier; the DLog hardness, never a Lean law. -/
  binding : Prop
  /-- **Deterministic per-note nullifier** (Zcash anti-double-spend tag). Function-ness IS
  the determinism the metatheory uses; that is an algebraic fact, available for free. -/
  nullifier : Digest → Digest
  /-- **CARRIER — nullifier/stealth unlinkability** (the anonymity advantage bound). A
  `Prop` carrier; never a Lean law. -/
  unlinkable : Prop

variable {Digest : Type u} [AddCommGroup Digest]

/-! ## Algebraic consequences PROVED from the homomorphism alone (the metatheory's tier). -/

/-- **`commit 0 0 = 0`, DERIVED from `commit_hom`** (cancellation in the `AddCommGroup`).
The neutral note is a *theorem* about any lawful primitive set, not an added field. -/
theorem commit_zero [CryptoPrimitives Digest] :
    (CryptoPrimitives.commit (0 : Int) (0 : Int) : Digest) = 0 := by
  have h := CryptoPrimitives.commit_hom (Digest := Digest) 0 0 0 0
  simp only [add_zero] at h
  have h2 : CryptoPrimitives.commit (0 : Int) (0 : Int) + (0 : Digest)
      = CryptoPrimitives.commit (0 : Int) (0 : Int)
        + CryptoPrimitives.commit (0 : Int) (0 : Int) := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **Nullifier determinism** — function-ness, the only nullifier fact the anti-double-spend
gate needs (the rest, anonymity, is the `unlinkable` carrier). -/
theorem nullifier_deterministic [CryptoPrimitives Digest] {d d' : Digest} (h : d = d') :
    CryptoPrimitives.nullifier d = CryptoPrimitives.nullifier d' := by rw [h]

/-! ## A `Reference` (test) instance — non-vacuity witness over `ℤ`.

A trivial lawful instance: `compress`/`compressN` linear stand-ins, `commit` the degenerate
`v + r`, the hardness carriers `:= True`. This witnesses the interface is inhabitable (the
algebraic laws are satisfiable, the carriers `True`-discharged in the toy model), so every
parametric theorem over `[CryptoPrimitives]` is non-vacuous. The real instance is the Rust
FFI one (Poseidon2/Pedersen). NOT the real crypto — a test stand-in. -/
namespace Reference

instance instCryptoPrimitives : CryptoPrimitives Int where
  compress a b := a + b
  compressN l := l.sum
  collisionHard := True
  commit v r := v + r
  commit_hom := by intro v w r s; ring
  binding := True
  nullifier d := d
  unlinkable := True

example : (CryptoPrimitives.commit (0 : Int) (0 : Int) : Int) = 0 := commit_zero

end Reference

end Dregg2.Crypto
