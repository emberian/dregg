/-
Mtls — path-validation and identity-extraction theorems.

Headline results (each is a statement about the total validator `verifyFrom`
and the extractor `authenticate`; the crypto stays behind the named `verifySig`
interface throughout):

  * `verify_iff` (#1) — **path-validation soundness, sharp.**  The validator
    accepts a chain *iff* all four named conditions hold: every certificate is
    inside its validity window, every non-top certificate is signed by its
    successor, every non-leaf (signing) certificate carries the CA constraint,
    and the top is a trusted anchor.  The four projections
    (`verify_needs_allValid`, `verify_needs_linkedSigned`,
    `verify_needs_nonLeafCA`, `verify_needs_topAnchored`) each state that one
    named condition is *necessary* for acceptance.

  * `expired_cert_fails` (#2) — a chain containing an expired certificate is
    rejected: the validity window is enforced at every link, so one closed
    window anywhere in the chain fails the whole path.

  * `authenticate_verified` / `authenticate_unverified` / `authenticate_eq_some`
    / `authenticate_deterministic` (#3) — **identity extraction is
    deterministic and cannot be bypassed.**  A verified chain yields exactly one
    identity, the leaf subject; an unverified or empty chain yields none; and
    the extractor is a function, so the identity is uniquely determined by the
    input.

  * `verify_empty` / `authenticate_empty` / `unverified_rejected` (#4) —
    **verification is total.**  Both functions are defined on every input by
    construction; the empty (malformed) chain is a clean reject that produces no
    identity, and any chain failing the named conditions is rejected outright.
-/

import Mtls.Verify

namespace Mtls

/-! ### #1 — path-validation soundness, stated sharply as an iff -/

/-- **The validator accepts a chain iff all four named path-validation
conditions hold.**  Forward (soundness): acceptance implies each condition is
met — so each condition is necessary.  Backward (completeness): the four
conditions together suffice.  The crypto is entirely behind `verifySig`. -/
theorem verify_iff (env : Env) (now : Time) (chain : Chain) :
    verifyFrom env now chain = true ↔
      (allValid now chain ∧ linkedSigned env chain
        ∧ nonLeafCA chain ∧ topAnchored env chain) := by
  induction chain with
  | nil =>
    constructor
    · intro h; simp [verifyFrom] at h
    · rintro ⟨_, _, _, top, htop, _⟩
      simp [topOf] at htop
  | cons c cs ih =>
    cases cs with
    | nil =>
      constructor
      · intro h
        simp only [verifyFrom, Bool.and_eq_true] at h
        obtain ⟨hv, ham⟩ := h
        refine ⟨?_, trivial, ?_, ?_⟩
        · intro x hx
          rw [List.mem_singleton] at hx; subst hx; exact hv
        · intro x hx; exact absurd hx (List.not_mem_nil x)
        · exact ⟨c, rfl, of_decide_eq_true ham⟩
      · rintro ⟨hAll, _, _, top, htop, hmem⟩
        simp only [topOf] at htop
        have hct : c = top := Option.some.inj htop
        simp only [verifyFrom, Bool.and_eq_true]
        refine ⟨hAll c (List.mem_singleton.mpr rfl), ?_⟩
        rw [decide_eq_true_eq, hct]; exact hmem
    | cons next rest =>
      constructor
      · intro h
        simp only [verifyFrom, Bool.and_eq_true] at h
        obtain ⟨⟨⟨hval, hsig⟩, hca⟩, hrec⟩ := h
        obtain ⟨hAllR, hLinkR, hCAR, hTopR⟩ := ih.mp hrec
        refine ⟨?_, ⟨hsig, hLinkR⟩, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hval
          · exact hAllR x hx'
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hca
          · exact hCAR x hx'
        · obtain ⟨top, htop, hmem⟩ := hTopR
          exact ⟨top, htop, hmem⟩
      · rintro ⟨hAll, hLink, hCA, hTop⟩
        obtain ⟨hsig, hLinkR⟩ := hLink
        have hrec : verifyFrom env now (next :: rest) = true := by
          refine ih.mpr ⟨?_, hLinkR, ?_, ?_⟩
          · intro x hx; exact hAll x (List.mem_cons_of_mem c hx)
          · intro x hx; exact hCA x (List.mem_cons_of_mem next hx)
          · obtain ⟨top, htop, hmem⟩ := hTop
            exact ⟨top, htop, hmem⟩
        simp only [verifyFrom, Bool.and_eq_true]
        exact ⟨⟨⟨hAll c (List.mem_cons_self c _), hsig⟩,
          hCA next (List.mem_cons_self next _)⟩, hrec⟩

/-! ### #1 — each named condition is necessary for acceptance -/

/-- Necessary condition: a verified chain has every certificate inside its
validity window at the check time. -/
theorem verify_needs_allValid {env : Env} {now : Time} {chain : Chain}
    (h : verifyFrom env now chain = true) : allValid now chain :=
  ((verify_iff env now chain).mp h).1

/-- Necessary condition: in a verified chain, every non-top certificate is
signed by its successor (under the named `verifySig`). -/
theorem verify_needs_linkedSigned {env : Env} {now : Time} {chain : Chain}
    (h : verifyFrom env now chain = true) : linkedSigned env chain :=
  ((verify_iff env now chain).mp h).2.1

/-- Necessary condition: in a verified chain, every non-leaf (signing)
certificate carries the CA basic constraint. -/
theorem verify_needs_nonLeafCA {env : Env} {now : Time} {chain : Chain}
    (h : verifyFrom env now chain = true) : nonLeafCA chain :=
  ((verify_iff env now chain).mp h).2.2.1

/-- Necessary condition: a verified chain's top is a trusted anchor. -/
theorem verify_needs_topAnchored {env : Env} {now : Time} {chain : Chain}
    (h : verifyFrom env now chain = true) : topAnchored env chain :=
  ((verify_iff env now chain).mp h).2.2.2

/-! ### #2 — an expired certificate anywhere in the chain fails -/

/-- **A chain containing a certificate that is not valid at the check time is
rejected.**  The validity window is enforced at every link, so a single invalid
window anywhere in the chain fails the whole path. -/
theorem invalid_cert_fails {env : Env} {now : Time} {chain : Chain} {c : Cert}
    (hmem : c ∈ chain) (hbad : c.validAt now = false) :
    verifyFrom env now chain = false := by
  cases hb : verifyFrom env now chain with
  | false => rfl
  | true => exact absurd (verify_needs_allValid hb c hmem) (by rw [hbad]; decide)

/-- **#2 — an expired certificate in the chain fails verification.**  If some
certificate's window has closed by the check time (`notAfter < now`), the chain
does not verify. -/
theorem expired_cert_fails {env : Env} {now : Time} {chain : Chain} {c : Cert}
    (hmem : c ∈ chain) (hexp : c.notAfter < now) :
    verifyFrom env now chain = false :=
  invalid_cert_fails hmem (validAt_false_of_expired hexp)

/-! ### #3 — identity extraction: deterministic, and no auth on failure -/

/-- A verified chain authenticates exactly the leaf (client-certificate)
subject. -/
theorem authenticate_verified {env : Env} {now : Time} {leaf : Cert}
    {rest : Chain} (h : verifyFrom env now (leaf :: rest) = true) :
    authenticate env now (leaf :: rest) = some leaf.subject := by
  simp only [authenticate, h, if_true]

/-- **No-bypass.**  An unverified chain yields no identity — there is no path
from a failed verification to `some`. -/
theorem authenticate_unverified {env : Env} {now : Time} {chain : Chain}
    (h : verifyFrom env now chain = false) : authenticate env now chain = none := by
  cases chain with
  | nil => rfl
  | cons leaf rest =>
    simp [authenticate, h]

/-- **Identity is uniquely determined and comes only from a verified leaf.**
Any identity the extractor produces is the leaf subject of a chain that did
verify — so a verified chain yields *exactly one* identity, the leaf subject. -/
theorem authenticate_eq_some {env : Env} {now : Time} {chain : Chain} {id : Name}
    (h : authenticate env now chain = some id) :
    ∃ leaf rest, chain = leaf :: rest ∧ id = leaf.subject
      ∧ verifyFrom env now chain = true := by
  cases chain with
  | nil => exact absurd h (by simp [authenticate])
  | cons leaf rest =>
    simp only [authenticate] at h
    by_cases hv : verifyFrom env now (leaf :: rest) = true
    · rw [if_pos hv] at h
      exact ⟨leaf, rest, rfl, (Option.some.inj h).symm, hv⟩
    · rw [if_neg hv] at h
      exact Option.noConfusion h

/-- **Determinism.**  `authenticate` is a function of its inputs, so it produces
at most one identity for a given chain and check time. -/
theorem authenticate_deterministic {env : Env} {now : Time} {chain : Chain}
    {r₁ r₂ : Option Name}
    (h₁ : authenticate env now chain = r₁) (h₂ : authenticate env now chain = r₂) :
    r₁ = r₂ := h₁.symm.trans h₂

/-! ### #4 — totality: clean reject of the empty / malformed chain -/

/-- The empty chain is rejected. -/
theorem verify_empty (env : Env) (now : Time) : verifyFrom env now [] = false := rfl

/-- The empty chain yields no identity. -/
theorem authenticate_empty (env : Env) (now : Time) :
    authenticate env now [] = none := rfl

/-- **Any chain failing the named conditions is a clean reject.**  Since the
validator is exactly the conjunction of the four conditions (`verify_iff`), a
chain that violates any of them is rejected outright — no partiality, no crash,
no identity. -/
theorem unverified_rejected {env : Env} {now : Time} {chain : Chain}
    (h : ¬ (allValid now chain ∧ linkedSigned env chain
              ∧ nonLeafCA chain ∧ topAnchored env chain)) :
    verifyFrom env now chain = false := by
  cases hb : verifyFrom env now chain with
  | false => rfl
  | true => exact absurd ((verify_iff env now chain).mp hb) h

/-- Corollary of totality: a chain whose top is not a trusted anchor produces no
identity. -/
theorem no_identity_of_not_anchored {env : Env} {now : Time} {chain : Chain}
    (h : ¬ topAnchored env chain) : authenticate env now chain = none :=
  authenticate_unverified <| unverified_rejected (fun hc => h hc.2.2.2)

end Mtls
