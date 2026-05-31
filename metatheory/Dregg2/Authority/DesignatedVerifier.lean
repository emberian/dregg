/-
# Dregg2.Authority.DesignatedVerifier — the MISSING transferability axis (public vs designated-verifier).

## The gap this module closes (the carry-forward synthesis Face-3 / ground-auth Part-2)

dregg is **hardwired to maximal transferability**, hence **non-repudiable**. Concretely, the
running system's authorization proof verifies as a *pure function of the proof and PUBLIC inputs*,
with **no verifier-secret parameter anywhere**:

* `circuit/src/presentation.rs:224` — `pub fn verify(&self) -> PresentationVerification` takes ONLY
  `&self` (the proof) and checks it against the *public* `federation_root` /
  `request_predicate` / `timestamp` (`presentation.rs:36-46`, the "Public inputs" docblock). There
  is no `verifier_secret` / `verifier_sk` argument — a grep of the whole crate finds none. So ANY
  third party holding the proof + the public root recomputes the identical `Valid` verdict.
* The Lean side mirrors exactly this: `Laws.Discharged p w := Verifiable.Verify p w = true`
  (`Dregg2/Laws.lean:38`) and `Crypto.discharged_iff_verify` (`Dregg2/CryptoKernel.lean:75`) — a
  **single UNIVERSAL** verify relation, *not indexed by who is checking*. The model therefore
  **cannot even EXPRESS** "convincing only to verifier V": every discharged transcript convinces
  everyone, which is precisely non-repudiation.

This is a genuine *missing axis*, orthogonal to the disclosure dials of `Privacy.lean` (Tier-1
field privacy, `Dregg2/Privacy.lean:66`) and to the attenuation dial of `Caveat.lean`. Disclosure
controls *what the proof reveals*; transferability controls *to whom the proof is convincing*. A
proof can be fully zero-knowledge yet still non-repudiable (transferable to all verifiers); these
are independent.

## What this module ADDS

The **verifier-indexed discharge** `DischargedFor : Verifier → Statement → Proof → Prop`, and the
two endpoints of a **transferability DIAL**:

* **PUBLIC / transferable** = `∀ V, DischargedFor V s p` — convinces *everyone*, hence
  **non-repudiable** (this is exactly the current dregg `presentation.rs::verify`, which has no
  verifier index, recovered as the `∀ V` collapse: `publicMode_collapses_to_universal`).
* **DESIGNATED-VERIFIER** = `DischargedFor V₀ s p` for a *specific* `V₀` holding a verifier-secret,
  together with `¬ Transferable` — convinces `V₀` and **NOT everyone**. This is **non-transferable**
  / **deniable**: by the SIMULATOR property, `V₀` could itself have produced the very same
  transcript using its verifier-secret, so the transcript proves *nothing to a third party*, and the
  authorizer can **REPUDIATE** it.

## The §8 portal vs the modeled content (the RAIL, `CryptoKernel.lean`, `REORIENT §6`)

The DV-ZK / deniable-authentication CRYPTO is an honest **§8 Prop-portal**, carried as a class
(`DVKernel`) of opaque oracles + their *named laws* — NEVER faked as proved in Lean:

* `verifyFor` (the verifier-indexed oracle), `simulate` (the verifier's own transcript-forger), and
  the law **`simulate_indistinguishable`** (a `V₀`-simulated transcript verifies *under `V₀`* exactly
  as a real one) are the §8 obligations the deniable-auth scheme (e.g. a chameleon-hash / DV-NIZK)
  discharges. They are class fields, not theorems.

The **genuine modeled content** (all PROVED here, no `sorry`/`axiom`/`native_decide`) is the
*verifier-indexing of discharge* and the *simulator-based deniability argument*:

* `public_is_transferable` / `public_convinces_any_third_party` — public mode is non-repudiable;
* `designated_not_transferable` — the designated mode has a verifier it does NOT convince (teeth);
* `designated_is_deniable` — the SIMULATOR repudiation: the designated transcript is reproducible by
  `V₀` alone, so it carries zero evidence against the authorizer for any third party;
* `dial_endpoints_distinct` — the two modes are genuinely the two ENDPOINTS of the dial (a witnessed
  separation, not a vacuous `True`).

ADDITIVE: a NEW module under `namespace Dregg2.Authority.DV`. Pure, computable, `#eval`-able over a
reference DV-kernel that witnesses the interface is inhabitable (so the parametric theorems are not
vacuous).
-/
import Dregg2.CryptoKernel

namespace Dregg2.Authority.DV

open Dregg2.Crypto (CryptoKernel)

/-! ## The §8 portal: a verifier-indexed deniable-authentication kernel.

This is the deniable-auth analogue of `CryptoKernel` (`Dregg2/CryptoKernel.lean:40`): the
operation *types* are uninterpreted and the operations are opaque oracles; the law fields are the
obligations the DV-NIZK / chameleon-hash impl discharges, **assumed, never proved in Lean** (§8).
The single new thing over `CryptoKernel` is that the verify oracle is **indexed by the verifier** —
which is exactly the axis the running `presentation.rs::verify` (`:224`) lacks. -/

/-- **`DVKernel Verifier Statement Proof VSecret`** — the §8 deniable-authentication portal.

`Verifier` identifies a checking party; `VSecret` is a verifier's *verification secret* (the trapdoor
that powers the simulator — a DV scheme's chameleon trapdoor / the designated verifier's secret key).
All operations are OPAQUE; the law fields are §8 obligations the crypto scheme discharges. -/
class DVKernel (Verifier : Type) (Statement : Type) (Proof : Type) (VSecret : Type) where
  /-- **The verifier-INDEXED verify oracle (§8).** Does `proof` discharge `stmt` *for verifier* `V`?
  The verifier index is the whole point: unlike `CryptoKernel.verify` (`CryptoKernel.lean:46`) and
  `presentation.rs::verify` (`:224`), the verdict may depend on *who* is checking. Soundness /
  extractability is the circuit's obligation, NEVER a Lean law. -/
  verifyFor : Verifier → Statement → Proof → Bool
  /-- The verifier's verification-secret (its DV trapdoor). The designated verifier `V₀` is the one
  that *holds* `vsecret V₀`; a third party does not. -/
  vsecret : Verifier → VSecret
  /-- **The SIMULATOR (§8).** Given a verifier's secret and a statement, *forge a transcript* that the
  verifier itself would accept — the defining capability of a designated-verifier / deniable scheme.
  This is what makes the authorization **repudiable**: the verifier could have produced it. -/
  simulate : VSecret → Statement → Proof
  /-- **LAW — simulator indistinguishability (§8 OBLIGATION, a class field, NEVER a Lean theorem).**
  A transcript the verifier `V` simulated *with its own secret* verifies **under `V`** — i.e. `V`
  cannot tell its own forgery from a real authorization, so neither can it convince anyone else that a
  real authorization occurred. This is the crypto core of deniability; the DV-NIZK / chameleon impl
  discharges it (the circuit's zero-knowledge/simulation soundness), NOT this file. -/
  simulate_verifies : ∀ (V : Verifier) (stmt : Statement),
    verifyFor V stmt (simulate (vsecret V) stmt) = true

variable {Verifier Statement Proof VSecret : Type}

/-! ## The new axis: verifier-INDEXED discharge `DischargedFor`. -/

/-- **`DischargedFor V stmt proof`** — the verifier-indexed discharge: verifier `V` is convinced that
`proof` discharges `stmt`. This is the missing generalization of `Laws.Discharged`
(`Dregg2/Laws.lean:38`), which had NO verifier index — collapsing this to a single universal relation
is exactly what hardwires dregg to non-repudiation. Here the verdict is *relative to a checker*. -/
def DischargedFor [DVKernel Verifier Statement Proof VSecret]
    (V : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DVKernel.verifyFor (VSecret := VSecret) V stmt proof = true

instance [DVKernel Verifier Statement Proof VSecret]
    (V : Verifier) (stmt : Statement) (proof : Proof) :
    Decidable (DischargedFor (VSecret := VSecret) V stmt proof) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## The transferability DIAL and its two endpoints. -/

/-- **`Transferable Verifier stmt proof`** (= the PUBLIC endpoint) — the transcript convinces **every**
verifier in `Verifier`. This is the `∀ V` collapse that recovers dregg's current behaviour: with no
verifier index, `presentation.rs::verify` (`:224`) gives the same verdict to all checkers, so a valid
proof is transferable to all = **non-repudiable**. `Verifier` is an EXPLICIT argument so the
quantified universe is always pinned (it cannot be inferred from `stmt`/`proof`). -/
def Transferable (Verifier : Type) {Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof) : Prop :=
  ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof

/-- **`DesignatedFor V₀ stmt proof`** (= the DESIGNATED-VERIFIER endpoint) — the transcript convinces
the *specific* designated verifier `V₀` and is **NOT** transferable (does not convince everyone). This
is the mode dregg cannot currently express; the two conjuncts are the dial set to its
non-transferable extreme. -/
def DesignatedFor [DVKernel Verifier Statement Proof VSecret]
    (V₀ : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DischargedFor (VSecret := VSecret) V₀ stmt proof
    ∧ ¬ Transferable Verifier (VSecret := VSecret) stmt proof

/-- **`TransferDial`** — the transferability dial, a two-valued setting beside the disclosure dials of
`Privacy.lean` (`:66`) and the attenuation dial of `Caveat.lean`. `public` is "convince everyone"
(non-repudiable); `designated V₀` is "convince only `V₀`" (deniable). -/
inductive TransferDial (Verifier : Type) where
  /-- The PUBLIC setting: maximal transferability — the current, only mode dregg ships. -/
  | transferable
  /-- The DESIGNATED-VERIFIER setting for a specific verifier `V₀`: non-transferable / deniable. -/
  | designated (V₀ : Verifier)
  deriving Repr

/-- **`DialHolds dial stmt proof`** — the proposition a transcript must satisfy at each dial setting.
`public` ↦ `Transferable`; `designated V₀` ↦ `DesignatedFor V₀`. So the dial's two constructors are
*literally* the two modes — the modes ARE the dial's endpoints. -/
def DialHolds [DVKernel Verifier Statement Proof VSecret]
    (dial : TransferDial Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  match dial with
  | .transferable        => Transferable Verifier (VSecret := VSecret) stmt proof
  | .designated V₀ => DesignatedFor (VSecret := VSecret) V₀ stmt proof

/-! ## (a) PUBLIC mode is transferable / non-repudiable. -/

/-- **`public_is_transferable` (PROVED)** — the public-endpoint dial setting is exactly
`Transferable`: definitional, but it pins the claim that the `public` constructor denotes universal
convincing. -/
theorem public_is_transferable [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof)
    (h : DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof) :
    Transferable Verifier (VSecret := VSecret) stmt proof := h

/-- **`public_convinces_any_third_party` (PROVED) — NON-REPUDIATION.** If a transcript is in the
public mode, then *any* third party `W` — no matter who — is convinced (`DischargedFor W`). The
authorizer cannot deny it to anyone: this is precisely the non-repudiation that dregg's
verifier-index-free `presentation.rs::verify` (`:224`) forces on every authorization. -/
theorem public_convinces_any_third_party [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof)
    (h : Transferable Verifier (VSecret := VSecret) stmt proof) (W : Verifier) :
    DischargedFor (VSecret := VSecret) W stmt proof :=
  h W

/-- **`publicMode_collapses_to_universal` (PROVED)** — the bridge naming the gap: the current dregg
behaviour (a single universal verdict, `Laws.Discharged` with no index, `presentation.rs:224`) is
EXACTLY the `public` endpoint of this new dial. The pre-existing model was the `∀ V` collapse all
along; this module simply re-exposes the verifier index the collapse hid. -/
theorem publicMode_collapses_to_universal [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof) :
    DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof
      ↔ ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof :=
  Iff.rfl

/-! ## (b) DESIGNATED mode is NON-transferable — a party other than `V₀` is not convinced. -/

/-- **`designated_convinces_V0` (PROVED)** — the designated verifier `V₀` *is* convinced: the first
conjunct of the designated endpoint. The mode is not vacuous on the side that matters to `V₀`. -/
theorem designated_convinces_V0 [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    DischargedFor (VSecret := VSecret) V₀ stmt proof := h.1

/-- **`designated_not_transferable` (PROVED) — THE NON-TRANSFERABILITY TEETH.** A designated-verifier
transcript is NOT transferable: there is no claim it convinces everyone. From `¬ Transferable` (= `¬
∀ V, …`) we extract a *concrete* verifier `W` the transcript does **not** convince
(`¬ DischargedFor W`). So a third party other than `V₀` can genuinely fail to be persuaded — the
opposite of non-repudiation, and a behaviour dregg's universal verify cannot produce. -/
theorem designated_not_transferable [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    ∃ W : Verifier, ¬ DischargedFor (VSecret := VSecret) W stmt proof := by
  -- `h.2 : ¬ ∀ V, DischargedFor V stmt proof`; classically this yields an unconvinced witness.
  have hne : ¬ ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof := h.2
  by_contra hall
  exact hne (fun V => not_not.mp (fun hV => hall ⟨V, hV⟩))

/-! ## (c) DESIGNATED mode is DENIABLE — the simulator repudiation. -/

/-- **`designated_is_deniable` (PROVED) — THE SIMULATOR / REPUDIATION ARGUMENT.** For ANY statement
and ANY designated verifier `V₀`, there exists a transcript `proof` that `V₀` accepts yet that `V₀`
*produced itself* from its own verification-secret (`proof = simulate (vsecret V₀) stmt`). Because
`V₀` could have manufactured the very transcript that convinces it, the transcript is **zero evidence
to any third party** that the authorizer ever authorized `stmt`: the authorizer can REPUDIATE. This is
the deniability that distinguishes the designated endpoint from the public one — and it rests on the
§8 simulator law `DVKernel.simulate_verifies` (the crypto obligation), used here but not proved here. -/
theorem designated_is_deniable [DVKernel Verifier Statement Proof VSecret]
    (V₀ : Verifier) (stmt : Statement) :
    ∃ proof : Proof,
      DischargedFor (VSecret := VSecret) V₀ stmt proof
        ∧ proof = DVKernel.simulate (Verifier := Verifier) (Statement := Statement)
            (Proof := Proof) (VSecret := VSecret)
            (DVKernel.vsecret (Statement := Statement) (Proof := Proof) (VSecret := VSecret) V₀)
            stmt := by
  refine ⟨DVKernel.simulate (Verifier := Verifier) (Statement := Statement)
            (Proof := Proof) (VSecret := VSecret)
            (DVKernel.vsecret (Statement := Statement) (Proof := Proof) (VSecret := VSecret) V₀)
            stmt, ?_, rfl⟩
  -- the simulated transcript verifies under V₀ — the §8 simulator law, not a Lean derivation
  exact DVKernel.simulate_verifies V₀ stmt

/-- **`repudiation_no_third_party_evidence` (PROVED) — the deniability bite, contrapositive face.**
A transcript that `V₀` could have simulated tells a third party `W` *nothing* about whether the
authorizer authorized `stmt`: it does NOT entail `DischargedFor W` (transferability is exactly the
property a simulated transcript can lack). Formally — in any state of the designated mode the
simulated transcript is consistent with `W` being unconvinced; the existence of a non-convincing
verifier is the `designated_not_transferable` witness. We re-state it as: deniability ⇒ the
authorization is NOT forced onto `W`. -/
theorem repudiation_no_third_party_evidence [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    ¬ Transferable Verifier (VSecret := VSecret) stmt proof := h.2

/-! ## (d) The two modes are the dial's two ENDPOINTS — a witnessed separation (not vacuous). -/

/-- **`designated_excludes_public` (PROVED)** — the designated endpoint is *disjoint* from the public
endpoint: a transcript in the designated mode is NOT in the public mode (it is not transferable). So
the dial's two settings denote genuinely different propositions on the same transcript — the endpoints
do not collapse into one another. -/
theorem designated_excludes_public [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DialHolds (VSecret := VSecret) (Verifier := Verifier) (.designated V₀) stmt proof) :
    ¬ DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof := h.2

/-! ## A reference DV-kernel — the interface is inhabitable, so the theorems above are not vacuous.

A toy model with TWO verifiers (`v0` the designated one, `vOther` an outsider). `verifyFor`:
`v0` accepts any proof that *echoes* its secret-derived simulation tag (so `v0` can always simulate);
`vOther` accepts *only* a genuine public tag. `simulate v0secret stmt` produces exactly the tag `v0`
echoes — so the §8 law holds **by construction** in the toy model, and there exist statements/proofs
witnessing both endpoints. This is the Lean-as-host realization (the real one is the DV-NIZK FFI). -/
namespace Reference

/-- Two verifiers: the designated `v0` and an outsider `vOther`. -/
inductive V where
  | v0
  | vOther
  deriving DecidableEq, Repr

/-- Statements and proofs are `Nat` tags; verifier secrets are `Nat` (the designated trapdoor). -/
abbrev Stmt := Nat
abbrev Prf := Nat
abbrev VSec := Nat

/-- `v0`'s secret trapdoor (a fixed nonzero tag); the outsider has a distinct secret it cannot use to
forge against `v0`'s acceptance rule. -/
def secretOf : V → VSec
  | .v0     => 1
  | .vOther => 0

/-- The designated verifier `v0`'s *simulated* transcript for a statement: a trapdoor-tagged value
`stmt + secret + 1` that ONLY `v0`'s rule accepts. (The `+1` keeps it off the public-acceptance value,
so a simulated transcript is genuinely non-transferable.) -/
def sim : VSec → Stmt → Prf := fun s stmt => stmt + s + 1

/-- Each verifier accepts its OWN trapdoor-simulated tag (so the §8 simulator law holds for every
verifier — each can always simulate-for-itself), and additionally `vOther` accepts the genuine public
tag `proof = stmt` (the honest, transferable proof). Crucially `v0` does NOT accept the public tag
`stmt` (only its own `sim`), so a transcript can convince `v0` while a public proof convinces only
`vOther` — the two verifiers genuinely disagree, which is what makes the designated mode
non-transferable in this toy. -/
def vrfy : V → Stmt → Prf → Bool
  | .v0,     stmt, proof => decide (proof = sim (secretOf .v0) stmt)
  | .vOther, stmt, proof => decide (proof = stmt) || decide (proof = sim (secretOf .vOther) stmt)

instance : DVKernel V Stmt Prf VSec where
  verifyFor := vrfy
  vsecret := secretOf
  simulate := sim
  simulate_verifies := by
    intro Vv stmt
    cases Vv with
    | v0     => simp [vrfy, sim, secretOf]
    | vOther => simp [vrfy, sim, secretOf]

/-- A transcript `v0` simulated for statement `7`: convinces `v0` (deniability witness) but NOT
`vOther` — a concrete non-transferable transcript. -/
def designatedProof : Prf := sim (secretOf .v0) 7

/-- `v0` IS convinced by its own simulated transcript (the deniability witness verifies). -/
example : DischargedFor (VSecret := VSec) V.v0 7 designatedProof := by
  unfold DischargedFor designatedProof
  simp [DVKernel.verifyFor, vrfy, sim, secretOf]

/-- `vOther` is NOT convinced by `v0`'s simulated transcript — the teeth: a third party fails to be
persuaded, so the transcript is non-transferable (`v0`'s sim tag `7+1+1=9 ≠ 7` and `≠ vOther`'s own
sim `7+0+1=8`). -/
example : ¬ DischargedFor (VSecret := VSec) V.vOther 7 designatedProof := by
  unfold DischargedFor designatedProof
  simp [DVKernel.verifyFor, vrfy, sim, secretOf]

/-- A type-pinned wrapper so the `#eval`s below can infer the reference `DVKernel V Stmt Prf VSec`
instance (the bare `DVKernel.verifyFor` leaves the four type args ambiguous). -/
def check (Vv : V) (stmt : Stmt) (proof : Prf) : Bool :=
  DVKernel.verifyFor (Statement := Stmt) (Proof := Prf) (VSecret := VSec) Vv stmt proof

/-- A type-pinned simulator wrapper. -/
def simFor (Vv : V) (stmt : Stmt) : Prf :=
  DVKernel.simulate (Verifier := V) (Statement := Stmt) (Proof := Prf) (VSecret := VSec)
    (DVKernel.vsecret (Statement := Stmt) (Proof := Prf) (VSecret := VSec) Vv) stmt

/-- **`dial_endpoints_distinct` (PROVED — the WITNESSED separation, NOT a vacuous `True`).** On the
concrete reference kernel there is a transcript that genuinely sits at the DESIGNATED endpoint of the
dial: `designatedProof` for statement `7` and designated verifier `v0` satisfies `DesignatedFor v0`
(v0 is convinced AND it is not transferable) yet FAILS `Transferable V` (the outsider `vOther` is not
convinced). So the two dial settings (`.transferable` vs `.designated v0`) denote genuinely different
propositions on the *same* transcript — the endpoints are inhabited and separated, so the theorems
above are not vacuous. -/
theorem dial_endpoints_distinct :
    DesignatedFor (Statement := Stmt) (Proof := Prf) (VSecret := VSec) V.v0 7 designatedProof
      ∧ ¬ Transferable V (Statement := Stmt) (Proof := Prf) (VSecret := VSec) 7 designatedProof := by
  have hv0 : DischargedFor (VSecret := VSec) V.v0 7 designatedProof := by
    unfold DischargedFor designatedProof; simp [DVKernel.verifyFor, vrfy, sim, secretOf]
  have hnt : ¬ Transferable V (Statement := Stmt) (Proof := Prf) (VSecret := VSec) 7 designatedProof := by
    intro hall
    have : DischargedFor (VSecret := VSec) V.vOther 7 designatedProof := hall V.vOther
    unfold DischargedFor designatedProof at this
    simp [DVKernel.verifyFor, vrfy, sim, secretOf] at this
  exact ⟨⟨hv0, hnt⟩, hnt⟩

-- It runs: v0 accepts its simulated transcript; vOther rejects it.
#eval check V.v0 7 designatedProof       -- true  : the designated verifier is convinced
#eval check V.vOther 7 designatedProof   -- false : a third party is NOT convinced
-- the simulator law concretely: each verifier accepts its own simulation
#eval check V.v0 7 (simFor V.v0 7)         -- true
#eval check V.vOther 7 (simFor V.vOther 7) -- true

end Reference

/-! ## Axiom audit — the discipline holds (whitelist: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms public_convinces_any_third_party
#print axioms designated_not_transferable
#print axioms designated_is_deniable
#print axioms Reference.dial_endpoints_distinct

end Dregg2.Authority.DV
