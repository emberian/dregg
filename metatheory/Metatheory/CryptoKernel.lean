/-
# Metatheory.CryptoKernel — the PORTAL between Lean semantics and the Rust world.

**The architecture (the new vision).** The dregg2 semantics live in Lean and are
*parametric* over a `CryptoKernel`: an interface of the cryptographic operations dregg2
needs (hash, verify, commit, nullifier), bundled with the algebraic **laws** Lean proofs
rely on. The operation *types* (`Digest`, `Proof`) and *implementations* are
**uninterpreted** in Lean — this is precisely the `dregg2 §8` boundary made into an
interface: crypto-soundness is never *proved* in Lean, it is *assumed* as the interface's
laws (the obligations the Rust impl + the circuits discharge).

Two realizations of the SAME interface — the answer to "FFI or uninterpreted symbols?":
*both*.
  • **PROVING** — an abstract `[CryptoKernel Digest Proof]` (uninterpreted symbols + their
    laws). Every Lean theorem is parametric over it, so it holds for *any* lawful impl.
  • **RUNNING** — Rust supplies the concrete `Digest`/`Proof` types + impls
    (Poseidon/Pedersen/WHIR-verify); the compiled Lean calls into them via FFI
    (`@[extern "dregg_poseidon_hash"] opaque hash …`), which IS a lawful instance.

So either entrypoint works: **Lean-as-host** (restricted — a reference/test CryptoKernel)
or **Rust-as-host** (the compiled Lean calls Rust for the *actual semantics of actual
things*). This module is the portal; everything cryptographic in the metatheory routes
through it. (Network/clock/randomness — the nondeterministic external inputs needed for
consensus — are a sibling `World` oracle, future work; this module is the crypto half.)
-/
import Mathlib.Tactic
import Mathlib.Logic.Encodable.Basic
import Metatheory.Laws
import Metatheory.Authority.Positional

namespace Metatheory.Crypto

open Metatheory.Laws Metatheory.Authority

/-- **The CryptoKernel interface.** `Digest` (hashes / commitments / Merkle roots) and
`Proof` (ZK proofs / witnesses) are uninterpreted; the operations are opaque; the fields
ending in a law are the obligations the Rust impl + circuits must satisfy (assumed, never
proved, in Lean — `dregg2 §8`). `Digest` is an `AddCommGroup` because commitments compose
(Pedersen). -/
class CryptoKernel (Digest : Type) (Proof : Type) [AddCommGroup Digest] where
  /-- Collision-resistant hash (Poseidon/BLAKE3): Merkle roots, turn-ids, chainlinks. -/
  hash : List Nat → Digest
  /-- **The Verify oracle (`dregg2 §8`).** Does `proof` discharge the statement committed
  by `stmt`? An opaque `Bool`; its soundness/extractability is the CIRCUIT obligation,
  NEVER a Lean law — Lean treats it as a decidable oracle (the verify/find seam). -/
  verify : Digest → Proof → Bool
  /-- Pedersen commitment `commit value blinding` (hiding + additively homomorphic). -/
  commit : Int → Int → Digest
  /-- Deterministic per-note nullifier (Zcash): the anti-double-spend tag. -/
  nullifier : Digest → Digest
  /-- **LAW — homomorphic commitment** (value-tier conservation over *hidden* amounts):
  the obligation the Pedersen impl + circuit satisfy. -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- **LAW — idealized collision-resistance**: the hash is injective in the model (the
  no-collision idealization the circuit's binding argument stands in for). -/
  hash_inj : Function.Injective hash

variable {Digest Proof : Type} [AddCommGroup Digest]

/-! ## The portal IS the verify/find seam: a CryptoKernel instantiates `Laws.Verifiable`. -/

/-- **A CryptoKernel induces the abstract verify/find seam** (`Laws.Verifiable`): the
predicate is a statement `Digest`, the witness is a `Proof`, and `Verify` is the kernel's
`verify`. This is how the §8 oracle is *instantiated* — the portal IS the `Verify`. -/
instance verifiableOfCryptoKernel [CryptoKernel Digest Proof] :
    Verifiable Digest Proof where
  Verify stmt proof := CryptoKernel.verify stmt proof

/-- **`Discharged` over a CryptoKernel is exactly `verify = true`** (definitional). -/
theorem discharged_iff_verify [CryptoKernel Digest Proof] (stmt : Digest) (proof : Proof) :
    Discharged stmt proof ↔ CryptoKernel.verify stmt proof = true :=
  Iff.rfl

/-! ## Closing the cross-vat integrity bridge via the portal. -/

/-- **The cross-vat integrity bridge, CLOSED via the portal (PROVED).** A non-owner
(cross-vat) change is admissible per `Authority.Integrity` exactly when the actor presents
a `Proof` that the CryptoKernel `verify`s against the change's admissibility statement
`p ko ko'`. This is the `Integrity.cross` case with the **CryptoKernel proof as the
discharging witness** — resolving the open seam the kernel's cap-layer left (the cap's
authorization across a vat boundary IS a `verify`). -/
theorem cross_vat_via_verify [CryptoKernel Digest Proof]
    (owner : Label) (subjects : List Label) {KO : Type}
    (p : KO → KO → Digest) (ko ko' : KO) (proof : Proof)
    (h : CryptoKernel.verify (p ko ko') proof = true) :
    Integrity Proof owner subjects p ko ko' :=
  Integrity.cross proof h

/-- **Intra-vat owner change** stays admissible with no proof needed (l4v `troa_lrefl`) —
the portal is only consulted across a boundary. -/
theorem intra_vat [CryptoKernel Digest Proof]
    (owner : Label) (subjects : List Label) {KO : Type}
    (p : KO → KO → Digest) (ko ko' : KO) (hown : owner ∈ subjects) :
    Integrity Proof owner subjects p ko ko' :=
  Integrity.intra hown

/-! ## A reference (test) CryptoKernel — the Lean-as-host realization.

A trivial lawful instance over `ℤ` (commit = a linear form, verify = a stub accepting a
matching tag) — enough to `#eval`/test the Lean semantics WITHOUT Rust. The real instance
is the Rust FFI one. This witnesses that the interface is inhabitable (the laws are
satisfiable), so parametric theorems are not vacuous. -/
namespace Reference

/-- Reference digest = ℤ (a stand-in group; the real one is the curve/field). -/
abbrev D := Int
/-- Reference proof = the claimed statement (a trivial "proof" = echo). -/
abbrev P := Int

/-- The reference hash: an injective `Encodable` encoding (a TEST stand-in, not the real
collision-resistant hash). Lifted to a top-level def so its injectivity reduces. -/
def refHash (l : List Nat) : Int := (Encodable.encode l : Int)

theorem refHash_inj : Function.Injective refHash := by
  intro a b h
  apply Encodable.encode_injective
  unfold refHash at h
  exact_mod_cast h

instance : CryptoKernel D P where
  hash := refHash
  verify stmt proof := decide (stmt = proof)        -- accepts iff the proof echoes the statement
  commit v r := v + r                                -- a (degenerate) linear commitment
  nullifier d := d
  commit_hom := by intro v w r s; ring
  hash_inj := refHash_inj

end Reference

end Metatheory.Crypto
