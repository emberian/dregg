/-
# Metatheory.PrivacyKernel — the privacy tiers REALIZED over the CryptoKernel portal.

`Privacy.lean` states the three privacy tiers over *abstract* carriers (a bespoke
`Commitment` structure with its homomorphism as a structure field, an opaque
`nullifierOf`), and honestly leaves the crypto-soundness obligations as `sorry`. This
module does the complementary thing: it realizes the **value** and **nullifier** tiers
*over the `CryptoKernel` portal* (`Metatheory/CryptoKernel.lean`), so the algebraic
properties become genuinely PROVED — not as fields of a structure we cooked up, but as
consequences of the CryptoKernel's *interface laws* (`commit_hom`, the determinism of
`nullifier`). The crypto SOUNDNESS (hiding, unlinkability, extractability) remains an
interface obligation — a `§8:` note — exactly as in `Privacy.lean`; what changes is that
the *algebra* (homomorphism ⇒ conservation, determinism ⇒ anti-double-spend) is now
discharged relative to the portal rather than postulated.

  • **value tier** (`committed_conservation_kernel`): the Pedersen opening of Law 1 over
    HIDDEN amounts. From cleartext conservation (`Σ vᵢ = Σ vₒ`, `Σ rᵢ = Σ rₒ`) the SUM of
    `CryptoKernel.commit`ments balances. PROVED via `commit_hom` (an interface LAW, not a
    stub) packaged as an `AddMonoidHom` `(Int × Int) →+ Digest`, then `map_sum`.

  • **nullifier tier** (`nullifier_no_double_spend`): a spent-set check rejects re-spending
    the same note — same digest ⇒ same `CryptoKernel.nullifier` ⇒ rejected. Pure
    Bool/structural logic; the determinism is the function-ness of `nullifier`.

  • **crypto soundness** (hiding / unlinkability / extractability): stays an INTERFACE
    obligation, see the `§8:` notes. NOT faked here.

Note: `CryptoKernel.commit`/`nullifier` take the `Proof` type as an EXPLICIT first argument
(the class carries `Proof` even though `commit` does not mention it), so all calls below
pass `Proof` positionally.
-/
import Metatheory.CryptoKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi

namespace Metatheory.PrivacyKernel

open Metatheory.Crypto

variable {Digest Proof : Type} [AddCommGroup Digest]

/-! ## Value tier — committed conservation over the CryptoKernel portal.

The CryptoKernel exposes `commit : Int → Int → Digest` with the single interface LAW
`commit_hom : commit (v+w) (r+s) = commit v r + commit w s`. Everything below is proved
from that law alone (plus the `AddCommGroup` structure on `Digest`). -/

/-- **`commit 0 0 = 0`, DERIVED from `commit_hom`.** Setting `v=w=r=s=0` in `commit_hom`
gives `commit 0 0 = commit 0 0 + commit 0 0`; cancellation in the `AddCommGroup` `Digest`
forces `commit 0 0 = 0`. So we do NOT need to add `commit_zero` to the interface — it is a
*theorem* about any lawful kernel, the neutral note. -/
theorem commit_zero [CryptoKernel Digest Proof] :
    (CryptoKernel.commit Proof 0 0 : Digest) = 0 := by
  have h := CryptoKernel.commit_hom (Digest := Digest) (Proof := Proof) 0 0 0 0
  simp only [add_zero] at h
  -- h : commit 0 0 = commit 0 0 + commit 0 0; cancel one copy in the AddCommGroup
  have h2 : CryptoKernel.commit Proof (0 : Int) (0 : Int) + (0 : Digest)
      = CryptoKernel.commit Proof (0 : Int) (0 : Int)
        + CryptoKernel.commit Proof (0 : Int) (0 : Int) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **The CryptoKernel commitment as an additive monoid homomorphism.** `commit_hom` is
precisely `f (x + y) = f x + f y` read on pairs `(value, blinding) : Int × Int`, and
`commit_zero` (derived above) is `f 0 = 0`. So `fun p => commit p.1 p.2` is a genuine
`AddMonoidHom (Int × Int) →+ Digest` — the algebraic content of the value tier expressed
over the portal, with the homomorphism now a PROVED interface consequence rather than a
postulated structure field. -/
def commitHom [CryptoKernel Digest Proof] : (Int × Int) →+ Digest where
  toFun p := CryptoKernel.commit Proof p.1 p.2
  map_zero' := commit_zero
  map_add' := fun x y => CryptoKernel.commit_hom (Digest := Digest) (Proof := Proof) x.1 y.1 x.2 y.2

theorem commitHom_apply [CryptoKernel Digest Proof] (v r : Int) :
    commitHom (Digest := Digest) (Proof := Proof) (v, r) = CryptoKernel.commit Proof v r := rfl

/-- The homomorphism collapses a finite sum of per-note commitments into a single
commitment of the summed value under the summed blinding (`Σ commit vᵢ rᵢ
= commit (Σ vᵢ) (Σ rᵢ)`). PROVED from `commitHom` via `map_sum` — the canonical
resource-world fact `Σ (f xᵢ) = f (Σ xᵢ)`, over the portal. -/
theorem commit_sum_kernel [CryptoKernel Digest Proof]
    {ι : Type} (val : ι → Int) (bl : ι → Int) (s : Finset ι) :
    (s.sum (fun i => CryptoKernel.commit Proof (val i) (bl i)) : Digest)
      = CryptoKernel.commit Proof (s.sum val) (s.sum bl) := by
  classical
  -- Re-express both sides via `commitHom`, then `map_sum` is the homomorphism's `Σ` law.
  show (s.sum (fun i => commitHom (Digest := Digest) (Proof := Proof) (val i, bl i)) : Digest)
      = commitHom (Digest := Digest) (Proof := Proof) (s.sum val, s.sum bl)
  rw [← map_sum (commitHom (Digest := Digest) (Proof := Proof)) (fun i => (val i, bl i)) s]
  congr 1
  rw [Prod.ext_iff]
  constructor
  · simpa using (Prod.fst_sum (s := s) (f := fun i => (val i, bl i)))
  · simpa using (Prod.snd_sum (s := s) (f := fun i => (val i, bl i)))

/-- **Value tier law: committed conservation over the CryptoKernel (PROVED via
`commit_hom`).** Given indexed input/output value+blinding lists with cleartext
conservation (`Σ vᵢ = Σ vₒ`) and matching blinding totals (`Σ rᵢ = Σ rₒ`, prover-chosen),
the **sum of `CryptoKernel.commit`ments of the inputs equals the sum of the outputs**. This
is the Pedersen opening of Law 1 (`Core.conservation_step`) over HIDDEN amounts: a verifier
confirms value was conserved while seeing only commitments, never the amounts. Genuinely
proved because `commit_hom` is an interface LAW (not a stub) — `commit_sum_kernel` collapses
each side and the two cleartext hypotheses equate the results.

§8: the *hiding* of the commitment (that the commitments leak nothing about `vᵢ`/`rᵢ`) is a
cryptographic obligation the Pedersen/Ristretto impl discharges — NOT proved here; only the
algebraic balance is. -/
theorem committed_conservation_kernel [CryptoKernel Digest Proof]
    {ι κ : Type} (insV : ι → Int) (inB : ι → Int) (outV : κ → Int) (outB : κ → Int)
    (sin : Finset ι) (sout : Finset κ)
    -- cleartext conservation (Law 1 on the value monoid): inputs' value sum = outputs'
    (hval : (sin.sum insV) = (sout.sum outV))
    -- blinding totals match (prover-chosen): inputs' blinding sum = outputs'
    (hblind : (sin.sum inB) = (sout.sum outB)) :
    (sin.sum (fun i => CryptoKernel.commit Proof (insV i) (inB i)) : Digest)
      = sout.sum (fun j => CryptoKernel.commit Proof (outV j) (outB j)) := by
  rw [commit_sum_kernel (Proof := Proof) insV inB sin,
      commit_sum_kernel (Proof := Proof) outV outB sout, hval, hblind]

/-! ## Nullifier tier — anti-double-spend over the CryptoKernel portal.

The CryptoKernel exposes `nullifier : Digest → Digest`, a *deterministic* per-note tag.
A spent set is a published predicate over nullifiers; a spend is accepted only if the
note's nullifier is not already recorded. Determinism is exactly the function-ness of
`nullifier` — the *same* note digest yields the *same* tag — so re-spending is detectable
by pure Bool logic. -/

/-- A **spent set**: the published set of consumed nullifier digests (the public contention
gate over the concurrent spent-note set), as a decidable membership `Bool`. -/
abbrev SpentSet (Digest : Type) := Digest → Bool

/-- `accepted spent d` : a spend of the note whose digest is `d` is accepted against the
published `spent` set iff its `CryptoKernel.nullifier` is not already present (fail-closed
on reuse). -/
def accepted [CryptoKernel Digest Proof] (spent : SpentSet Digest) (d : Digest) : Prop :=
  spent (CryptoKernel.nullifier Proof d) = false

/-- **Nullifier tier law: no double-spend (determinism ⇒ uniqueness), PROVED
structurally.** Once a note's nullifier is recorded in the spent set, re-spending the
*same* note (same digest `d`) is rejected: `nullifier` is a function, so the same digest
yields the same tag, and `accepted` (a `false` check) contradicts the recorded `true`.
Pure Bool/structural logic over the portal — no crypto assumption.

§8: that distinct *holders* cannot be linked through their nullifiers (anonymity / the
nullifier ≈ fresh-random advantage bound) is the cryptographic obligation — NOT proved
here; only the deterministic-uniqueness gate is. -/
theorem nullifier_no_double_spend [CryptoKernel Digest Proof]
    (spent : SpentSet Digest) (d : Digest)
    -- the note was already spent: its nullifier is recorded in the spent set
    (hspent : spent (CryptoKernel.nullifier Proof d) = true) :
    ¬ accepted (Proof := Proof) spent d := by
  unfold accepted
  rw [hspent]
  simp

/-- **Determinism corollary made explicit.** Two spends of the same note digest produce the
same nullifier — the function-ness of `CryptoKernel.nullifier` IS the determinism that the
double-spend gate relies on. (Trivial, but it names the load-bearing fact: anti-double-spend
needs *only* determinism, no further crypto.) -/
theorem nullifier_deterministic [CryptoKernel Digest Proof] (d d' : Digest) (h : d = d') :
    CryptoKernel.nullifier Proof d = CryptoKernel.nullifier Proof d' := by
  rw [h]

end Metatheory.PrivacyKernel
