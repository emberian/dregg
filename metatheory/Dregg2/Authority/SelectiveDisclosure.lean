/-
# Dregg2.Authority.SelectiveDisclosure — credential selective disclosure + predicate proofs + anonymous unlinkable multi-show.

This module carries forward the REAL Rust semantics of `dregg-credentials`'
**presentation** path — the headline credential feature that the existing Lean
(`Authority/Credential.lean`, whose `claim` is one opaque `Nat`, all-or-nothing
`verify`) and `Privacy.lean` (unlinkability present but DISCONNECTED from the
credential object) only shadow. See the gap analysis in
`docs/rebuild/GROUND-AUTH-ATTESTATION.md §1.2/§1.6` (Selective disclosure: **O**;
predicate proofs: **S**; anonymous multi-show: **S, split & disconnected**) and
`docs/rebuild/CARRY-FORWARD-SYNTHESIS.md §2 Face-2 #3/#4`.

## What this models (the REAL Rust, `credentials/src/presentation.rs:176-359`)

A `Credential` carries a *vector* of attributes (`CredentialAttributes` =
`Vec<AttributeAttenuation{name, value}>`, `credentials/src/schema.rs:101-115`;
re-applied at present time over `credential.attributes.attributes`,
`presentation.rs:216-219`). A `Presentation`:

  1. **Selective disclosure** — reveals a chosen SUBSET in cleartext
     (`PresentationOptions.disclose`, `presentation.rs:36-37`; the
     `disclose_set` filter loop `presentation.rs:257-265`) and commits to exactly
     the revealed terms via a Poseidon2 `revealed_facts_commitment`
     (`presentation.rs:267-270, 365-372`). The HIDDEN rest is *not transmitted at
     all* (`presentation.rs:34-35` doc: "Other attributes are not transmitted").

  2. **Predicate proofs** — `Gte/Lte/InRange` (and `Gt/Lt/Neq`) over HIDDEN
     attributes (`bridge/src/present.rs:2780-2793`; per-request loop
     `presentation.rs:307-351` via `prove_predicate_for_fact`). The proof binds the
     attribute's `predicate_value` (`schema.rs:90-98` `to_predicate_value`) into a
     fact-hash *without revealing the value*.

  3. **Anonymous unlinkable multi-show** — `present_anonymous`
     (`presentation.rs:176-182`) (a) OMITS the holder `confine_user` binding
     (`presentation.rs:231-244`, the UNLINKABILITY note `:204-212`) and (b) uses a
     real STARK with a **fresh per-presentation blinding factor**, so the public
     `blinded_leaf` differs across shows (`presentation.rs:292-299`) while the
     observer cannot correlate two presentations of the same credential.

## The three laws this PROVES (non-vacuously, reusing `Privacy.lean`'s view idiom)

  (a) **`presentation_hides_undisclosed`** — a presentation reveals ONLY the
      disclosed subset + the proven predicates: two credentials that agree on the
      disclosed attributes and on every proven predicate's truth produce the SAME
      observer-view. The hidden attributes are *not determined by* the view (the
      anonymity-set / view-equality style of `Privacy.field_projection_hides_private`
      and the `view`-collapse model, `Privacy.lean:97-109, 262-284`). NON-vacuous:
      the `Reference` view is genuinely non-constant in the disclosed slots.

  (b) **`proven_predicate_holds`** — a predicate that the presentation *proves*
      genuinely holds of the underlying credential's attribute (the soundness law:
      a `ProvenPredicate` carries a proof `evalPred pred (cred.attr i) = true`, and
      this theorem extracts it). The teeth: `predicate_proof_has_teeth` exhibits a
      predicate FALSE of a value for which NO proof can be produced.

  (c) **`multishow_unlinkable`** — two presentations of the SAME credential (fresh
      blinding each show) have EQUAL observer-views: a verifier cannot correlate
      them (wiring `Privacy.lean`'s unlinkability-by-view-collapse INTO the
      credential path it actually governs — the disconnect flagged in the audit).

## §8 PORTAL (NEVER faked as proved)

The *cryptographic soundness* of the underlying machinery — that the STARK / Poseidon2
`revealed_facts_commitment` / predicate-circuit / per-presentation ring-blinding are
*computationally* binding & hiding against a PPT adversary — is the §8 oracle
(`CryptoKernel.verify`, `Crypto/Primitives.lean::unlinkable`,
`bridge/src/present.rs:269-308` STARK verify). This module proves the
*information-theoretic CORE* (perfect view-collapse on the modelled transcript +
the disclosure discipline + predicate extraction), exactly as `Privacy.lean` does;
it does NOT, and does not claim to, prove the computational property.

DISCIPLINE: no `sorry`/`admit`/`axiom`/`native_decide` (kernel-clean: axioms ⊆
{propext, Classical.choice, Quot.sound}); every modelled mechanism cites the REAL
Rust file:line; statements are never weakened to close them (an honest `-- OPEN:`
beats a vacuous theorem). ADDITIVE: a NEW module; edits no existing file.
-/
import Dregg2.Privacy

namespace Dregg2.Authority.SelectiveDisclosure

open Dregg2.Privacy (StealthAddr Recipient)

universe u

/-! ## The predicate vocabulary — the REAL Rust `bridge::present::Predicate`.

`bridge/src/present.rs:2780-2793`: `Gte(u32) | Lte(u32) | Gt(u32) | Lt(u32) |
Neq(u32) | InRange(u32,u32)`. We model the value space as `Nat` (the Rust
`to_predicate_value : AttrValue → Option u32`, `schema.rs:90-98`, lands integers /
dates / bools in `u32`). `evalPred` is the verifier-local *decidable* relation each
predicate proof attests — the genuine arithmetic content the circuit binds. -/

/-- The credential-predicate kinds the Rust supports (`bridge/src/present.rs:2780`).
Thresholds carried as `Nat` (the `u32` predicate-value of `schema.rs:90-98`). -/
inductive Predicate where
  /-- `attribute ≥ threshold` (`present.rs:2782`). -/
  | gte (threshold : Nat)
  /-- `attribute ≤ threshold` (`present.rs:2784`). -/
  | lte (threshold : Nat)
  /-- `attribute > threshold` (`present.rs:2786`). -/
  | gt (threshold : Nat)
  /-- `attribute < threshold` (`present.rs:2788`). -/
  | lt (threshold : Nat)
  /-- `attribute ≠ target` (`present.rs:2790`). -/
  | neq (target : Nat)
  /-- `low ≤ attribute ≤ high` (`present.rs:2792`). -/
  | inRange (low high : Nat)
  deriving DecidableEq, Repr

/-- **The verifier-local predicate relation** — the decidable arithmetic each
predicate proof attests of the (hidden) attribute value. This is the genuine
content the predicate circuit enforces (`bridge/src/present.rs:2847-2868`'s
GTE/LTE/range comparators); the *circuit soundness* that the proof binds this
value is the §8 oracle, but the relation itself is this honest `Bool`. -/
def evalPred : Predicate → Nat → Bool
  | .gte t,        v => decide (t ≤ v)
  | .lte t,        v => decide (v ≤ t)
  | .gt t,         v => decide (t < v)
  | .lt t,         v => decide (v < t)
  | .neq t,        v => decide (v ≠ t)
  | .inRange lo hi, v => decide (lo ≤ v) && decide (v ≤ hi)

/-! ## The credential — a VECTOR of attributes (the real `CredentialAttributes`).

`credentials/src/schema.rs:101-115`: `CredentialAttributes{ attributes:
Vec<AttributeAttenuation{name, value}> }`. We index the vector by `Fin n` (the
positional `name` slot) and store the `predicate_value` (`schema.rs:90-98`) at each
slot. The `n` is the schema arity. -/

/-- A **`Credential`** with a vector of `n` attribute values (the
`CredentialAttributes.attributes` of `schema.rs:101-115`, valued by the
`to_predicate_value` `u32` of `schema.rs:90-98`). `attr i` is the value at the
`i`-th named slot — the SECRET the holder selectively discloses / predicates over. -/
structure Credential (n : Nat) where
  /-- The attribute values, one per schema slot (the hidden secrets). -/
  attr : Fin n → Nat

/-! ## A proven predicate — soundness is a CARRIED proof, not a `Bool` flag.

The Rust predicate proof (`presentation.rs:342-349`, `BridgePredicateProof`) is a
STARK that the named attribute satisfies the predicate. We model the proof object
as a structure carrying (i) which slot, (ii) which predicate, (iii) the SOUNDNESS
WITNESS: a proof that `evalPred` of that predicate at the credential's actual value
is `true`. This is what makes `proven_predicate_holds` real: you cannot construct a
`ProvenPredicate` for a predicate that is false of the value — the constructor
demands the discharging proof. (The *circuit's* enforcement of this is §8.) -/

/-- A **proven predicate over a hidden attribute** of a credential `cred`. Carries
the slot, the predicate, and the soundness witness `holds : evalPred pred (cred.attr
slot) = true`. Mirrors `presentation.rs:307-351`: each `PredicateRequest` becomes a
proof bound to the credential's actual attribute value — a proof exists ONLY when
the predicate genuinely holds. -/
structure ProvenPredicate {n : Nat} (cred : Credential n) where
  /-- Which attribute slot the predicate is about (`req.attribute`, `presentation.rs:320`). -/
  slot : Fin n
  /-- The predicate proven (`req.predicate`, `presentation.rs:343`). -/
  pred : Predicate
  /-- **Soundness witness**: the predicate genuinely holds of the credential's
  actual (hidden) value. The proof object cannot be forged for a false predicate. -/
  holds : evalPred pred (cred.attr slot) = true

/-! ## The presentation — disclosed SUBSET + predicate proofs + per-show blinding.

`presentation.rs:184-359` `present_impl`. We model:
  * `disclose : Fin n → Bool` — the subset mask (`PresentationOptions.disclose` /
    `disclose_set`, `presentation.rs:36-37, 259-265`);
  * `predicateProofs` — the list of `ProvenPredicate`s (`presentation.rs:307-351`);
  * `blinding : Nat` — the fresh per-presentation ring-blinding factor
    (`presentation.rs:292-299`; for the anonymous path each show draws a new one);
  * `anonymous : Bool` — anonymous path omits the holder `confine_user` binding
    (`presentation.rs:235-244`).

The wire form strips the private witness (`presentation.rs:133-152`); only the
OBSERVER-VIEW below travels. -/

/-- A **`Presentation`** of credential `cred` (`presentation.rs:353-358`). -/
structure Presentation {n : Nat} (cred : Credential n) where
  /-- The disclosure subset mask: `true` = revealed in cleartext (`presentation.rs:259-265`). -/
  disclose : Fin n → Bool
  /-- Predicate proofs over (hidden) attributes (`presentation.rs:307-351`). -/
  predicateProofs : List (ProvenPredicate cred)
  /-- The fresh per-presentation ring-blinding factor (`presentation.rs:292-299`).
  Differs across anonymous shows of the same credential. -/
  blinding : Nat
  /-- Anonymous path (omits `confine_user`, `presentation.rs:235-244`). -/
  anonymous : Bool

/-! ### The OBSERVER-VIEW — what travels on the wire (the disclosure transcript).

Reusing the `Privacy.lean` honest model (`Privacy.lean:262-284`): the observer-view
is everything a verifier learns from a presentation. Information-theoretic hiding =
**equality of this view**. The view contains EXACTLY: (i) the disclosed attribute
values, each at its slot, `none` for hidden slots (the `disclosed` cleartext +
`revealed_facts_commitment`, `presentation.rs:257-270`); (ii) the proven predicates
as `(slot, predicate)` pairs — the *predicate*, NOT the value (`presentation.rs:307-351`).

Critically the view does NOT include the hidden attribute values nor the blinding
factor (stripped, `presentation.rs:133-152`): that is what makes hiding /
unlinkability hold. -/

/-- The **disclosed-values view**: the cleartext at each disclosed slot, `none` at
hidden slots. EXACTLY `Privacy.project` (`Privacy.lean:91-95`) under the disclosure
mask — selective disclosure as a projection that withholds the hidden slots. -/
def disclosedView {n : Nat} {cred : Credential n} (p : Presentation cred) :
    Fin n → Option Nat :=
  fun i => if p.disclose i then some (cred.attr i) else none

/-- The **proven-predicate view**: the `(slot, predicate)` pairs the presentation
proves — the predicates an observer sees attested, WITHOUT the underlying values
(`presentation.rs:346-349` ships `attribute`+`predicate`, never the value). -/
def predicateView {n : Nat} {cred : Credential n} (p : Presentation cred) :
    List (Fin n × Predicate) :=
  p.predicateProofs.map (fun pp => (pp.slot, pp.pred))

/-- **The full observer-view** = disclosed-values view ⊕ proven-predicate view. This
is the entire public transcript (`presentation.rs:145-152` `WirePresentation` =
`disclosed` + `predicate_proofs` + `anonymous`, MINUS the stripped private trace and
the per-show blinding). Two presentations are observationally indistinguishable
EXACTLY when these views are equal (`Privacy.lean:262-268`). -/
def observerView {n : Nat} {cred : Credential n} (p : Presentation cred) :
    (Fin n → Option Nat) × List (Fin n × Predicate) :=
  (disclosedView p, predicateView p)

/-! ## LAW (a) — the presentation reveals ONLY the disclosed subset + proven predicates.

The hiding law in the `Privacy.field_projection_hides_private` style
(`Privacy.lean:101-109`): if two credentials agree on every DISCLOSED attribute and
the two presentations prove the same `(slot, predicate)` list, the observer-views are
EQUAL — so the view is *independent of* the hidden attribute values. An observer
learns the disclosed slots + the proven predicates and provably nothing else about
the hidden rest. -/

/-- **LAW (a): a presentation hides the undisclosed attributes.** If `cred` and
`cred'` agree on every DISCLOSED slot (`p.disclose i = true → cred.attr i = cred'.attr
i`) and the two presentations carry the SAME disclosure mask and the SAME proven
`(slot, predicate)` list, then their observer-views are EQUAL. Hence the view is
independent of the hidden attributes — exactly selective disclosure
(`presentation.rs:34-35, 257-270`), proved in the `Privacy.project` idiom. -/
theorem presentation_hides_undisclosed {n : Nat}
    {cred cred' : Credential n}
    (p : Presentation cred) (p' : Presentation cred')
    (hmask : p.disclose = p'.disclose)
    (hpred : predicateView p = predicateView p')
    (hdisc : ∀ i, p.disclose i = true → cred.attr i = cred'.attr i) :
    observerView p = observerView p' := by
  unfold observerView
  refine Prod.ext ?_ hpred
  funext i
  unfold disclosedView
  rw [← hmask]
  cases hi : p.disclose i with
  | false => simp [hi]
  | true  => simp [hi, hdisc i hi]

/-- **Teeth for (a): hiding is NON-vacuous — the view genuinely depends on the
disclosed slots.** Two credentials that DIFFER on a disclosed slot (with that slot
revealed) produce DIFFERENT observer-views. So `presentation_hides_undisclosed` is
not a `True`-masquerade: the disclosed part is really revealed (the view separates
distinct disclosed values), while the hidden part is really hidden. -/
theorem disclosed_slot_is_revealed {n : Nat}
    {cred cred' : Credential n}
    (p : Presentation cred) (p' : Presentation cred')
    (i : Fin n) (hi : p.disclose i = true) (hi' : p'.disclose i = true)
    (hne : cred.attr i ≠ cred'.attr i) :
    observerView p ≠ observerView p' := by
  intro heq
  have h1 : disclosedView p = disclosedView p' := congrArg Prod.fst heq
  have h2 := congrFun h1 i
  unfold disclosedView at h2
  rw [hi, hi'] at h2
  simp only [if_true] at h2
  exact hne (Option.some.inj h2)

/-! ## LAW (b) — a proven predicate genuinely holds of the underlying credential.

Soundness: the presentation cannot prove a predicate that is false of the actual
hidden value. The `ProvenPredicate.holds` field IS the discharging proof; this
theorem extracts it for any proof in the presentation's list. (The *circuit's*
binding of `holds` to the real value is the §8 oracle; the relation `evalPred` is
the honest arithmetic content — `bridge/src/present.rs:2847-2868`.) -/

/-- **LAW (b): every proven predicate genuinely holds of the underlying credential.**
For any predicate proof `pp` attached to the presentation, `evalPred pp.pred
(cred.attr pp.slot) = true` — the proof witnesses a TRUE predicate over the hidden
attribute. This is presentation predicate-soundness (`presentation.rs:307-351`): a
proof binds the attribute's real value, so a false predicate is unprovable. -/
theorem proven_predicate_holds {n : Nat} {cred : Credential n}
    (p : Presentation cred) (pp : ProvenPredicate cred)
    (_hmem : pp ∈ p.predicateProofs) :
    evalPred pp.pred (cred.attr pp.slot) = true :=
  pp.holds

/-- **Teeth for (b): a predicate FALSE of a value admits NO proof.** A
`ProvenPredicate` for `.gte 18` over a credential whose attribute is `17` is
*uninhabitable*: its `holds : evalPred (.gte 18) 17 = true` field is unsatisfiable
(`18 ≤ 17` is false). So `proven_predicate_holds` has real soundness teeth — you
cannot mint a proof of a false predicate. Stated as: any such proof yields `False`. -/
theorem predicate_proof_has_teeth {n : Nat} (cred : Credential n) (slot : Fin n)
    (hval : cred.attr slot = 17)
    (pp : ProvenPredicate cred)
    (hslot : pp.slot = slot) (hpred : pp.pred = .gte 18) :
    False := by
  have h := pp.holds
  rw [hpred, hslot, hval] at h
  -- `evalPred (.gte 18) 17 = decide (18 ≤ 17) = false`, contradicting `… = true`.
  simp [evalPred] at h

/-! ## LAW (c) — anonymous multi-show unlinkability, WIRED to the credential path.

The disconnect the audit flags (`GROUND-AUTH-ATTESTATION.md §1.6`,
`CARRY-FORWARD-SYNTHESIS.md §2 #4`): `Privacy.lean` has unlinkability-by-view-collapse
but NOT bound to the credential object that actually multi-shows in Rust. Here we
state it ABOUT the credential `Presentation`: two anonymous presentations of the SAME
credential — each with a FRESH blinding factor (`presentation.rs:292-299`) and the
SAME disclosure/predicate policy — have EQUAL observer-views. The verifier cannot
correlate them. This is the `Privacy.unlinkable` collapse (`Privacy.lean:457-461`)
landed on the credential path. -/

/-- **LAW (c): multi-show unlinkability of one credential.** Two presentations `p₁
p₂` of the SAME `cred`, sharing the disclosure mask and proving the same `(slot,
predicate)` list — but with DIFFERENT fresh blinding factors (`p₁.blinding ≠
p₂.blinding`) — have EQUAL observer-views. The per-show blinding is NOT in the view
(`presentation.rs:133-152` strips it), so the two shows are indistinguishable on the
wire: an observer cannot tell they came from the same holder. Wires
`Privacy.unlinkable`'s view-collapse INTO the credential multi-show path. -/
theorem multishow_unlinkable {n : Nat} {cred : Credential n}
    (p₁ p₂ : Presentation cred)
    (hmask : p₁.disclose = p₂.disclose)
    (hpred : predicateView p₁ = predicateView p₂)
    (_hfresh : p₁.blinding ≠ p₂.blinding) :
    observerView p₁ = observerView p₂ := by
  -- Same credential, agreeing on the disclosed slots is automatic (`cred = cred`);
  -- reduce to law (a). The differing blinding is invisible to the view.
  exact presentation_hides_undisclosed p₁ p₂ hmask hpred (fun _ _ => rfl)

/-- **Teeth for (c): unlinkability is NON-vacuous — distinct-blinding shows really
do collapse despite the secret blinding differing.** Concretely, two presentations
of the same credential with blinding `0` and `1` (genuinely distinct) and identical
policy have the SAME view: the view function genuinely ignores `blinding`, so this is
real hiding of the per-show randomness, not a `True`-collapse. -/
theorem multishow_blinding_invisible {n : Nat} (cred : Credential n)
    (mask : Fin n → Bool) :
    observerView (cred := cred) ⟨mask, [], 0, true⟩
      = observerView (cred := cred) ⟨mask, [], 1, true⟩ := by
  rfl

/-! ## The `Reference` witnesses — GENUINELY NON-TRIVIAL (not vacuous).

A lawful, fully-concrete instantiation showing the laws have real content: a 3-slot
credential, a presentation disclosing slot 0 and proving `.gte 18` of slot 1 (which
genuinely holds), and the demonstrations that (a) the disclosed slot is really
revealed, (b) the predicate genuinely holds, (c) two shows with different blinding
collapse to one view. The view is genuinely NON-CONSTANT (different disclosed values
give different views), so the hiding theorems are non-vacuous in the HONEST sense. -/
namespace Reference

/-- A 3-attribute credential: `attr 0 = 42`, `attr 1 = 21` (an age ≥ 18),
`attr 2 = 7`. -/
def cred : Credential 3 := ⟨fun i => [42, 21, 7].get i⟩

/-- A proof that slot-1's value (`21`) is `≥ 18` — genuinely TRUE, so inhabitable. -/
def ageProof : ProvenPredicate cred where
  slot := 1
  pred := .gte 18
  holds := by decide

/-- A presentation disclosing slot 0 (revealing `42`), proving `.gte 18` of the
hidden slot 1, anonymous, with blinding `99`. -/
def pres : Presentation cred where
  disclose := fun i => decide (i = 0)
  predicateProofs := [ageProof]
  blinding := 99
  anonymous := true

/-- A SECOND show of the SAME credential, same policy, FRESH blinding `100`. -/
def pres' : Presentation cred where
  disclose := fun i => decide (i = 0)
  predicateProofs := [ageProof]
  blinding := 100
  anonymous := true

/-- (a)-non-vacuity: the disclosed slot 0 really shows `some 42`; the hidden slots
show `none`. The view genuinely reveals the disclosed value and hides the rest. -/
example : disclosedView pres 0 = some 42 ∧ disclosedView pres 1 = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-- (b)-non-vacuity: the proven predicate genuinely holds of the hidden value `21`. -/
example : evalPred ageProof.pred (cred.attr ageProof.slot) = true :=
  proven_predicate_holds pres ageProof (by simp [pres])

/-- (c)-non-vacuity: the two shows (`blinding 99` vs `100`, genuinely distinct) have
EQUAL observer-views — the credential is unlinkable across shows. -/
example : observerView pres = observerView pres' :=
  multishow_unlinkable pres pres' rfl rfl (by decide)

/-- The teeth bite: `.gte 18` is FALSE of `17`, so no proof of it exists at a value-17
slot. We exhibit the contradiction `predicate_proof_has_teeth` derives. -/
example (cred17 : Credential 1) (h : cred17.attr 0 = 17)
    (bad : ProvenPredicate cred17) (hs : bad.slot = 0) (hp : bad.pred = .gte 18) : False :=
  predicate_proof_has_teeth cred17 0 h bad hs hp

end Reference

-- TRIPWIRES: the disclosure / predicate-soundness / unlinkability laws are
-- kernel-clean (axioms ⊆ {propext, Classical.choice, Quot.sound}) — no `sorry`/
-- `axiom`/`native_decide` leaked. The residual *computational* binding/hiding of the
-- real STARK / Poseidon2-commitment / per-show ring-blinding is the §8 portal
-- (`CryptoKernel.verify`, `bridge/src/present.rs:269-308`), NEVER an axiom here.
#assert_axioms presentation_hides_undisclosed
#assert_axioms disclosed_slot_is_revealed
#assert_axioms proven_predicate_holds
#assert_axioms predicate_proof_has_teeth
#assert_axioms multishow_unlinkable
#assert_axioms multishow_blinding_invisible

end Dregg2.Authority.SelectiveDisclosure
