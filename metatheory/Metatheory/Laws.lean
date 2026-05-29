/-
# Metatheory.Laws — the `Predicate ⊣ Witness` adjunction and the verify/find seam.

The central seam of the whole system: a *predicate* and a *witness* form a Galois
connection (an adjunction between thin categories / a residuated pair on a Heyting
algebra). The **verify** side is decidable and verifier-local (`Verify P w : Bool`);
the **find/search** side is an opaque, possibly-undecidable plugin (the prover /
matcher / solver). The metatheory commits ONLY to the verify side; the search side
is contracted to be *sound by verification* and nothing more (no completeness, no
termination — see `Authority/Positional.lean` and the README §matcher).

"Spec-first": the adjunction laws are `sorry`'d obligations to be discharged against
`Order.GaloisConnection` once the `Predicate`/`Witness` orders are fixed.
-/
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Heyting.Basic

open OrderDual Set

namespace Metatheory.Laws

/- The lattice of predicates over a fixed witness space `W`.
In the real system this is the Heyting algebra of admissibility conditions;
here it is abstract, required only to be a `HeytingAlgebra`. -/
variable {P : Type*} {W : Type*}

/-- The decidable, verifier-local check: does witness `w` satisfy predicate `p`?

This is *simultaneously* the proof target and a runnable function — a Lean
`def … : Bool` is both the spec and the executable golden oracle (backend #8 of
the differential harness). -/
class Verifiable (P : Type*) (W : Type*) where
  Verify : P → W → Bool

/-- `Discharged P w` ≜ the verifier accepts: the proof-relevant statement that a
witness discharges a predicate. This is the cross-vat admissibility object — a
freely copyable, verifier-checkable certificate, no off-island mediator. -/
def Discharged [Verifiable P W] (p : P) (w : W) : Prop :=
  Verifiable.Verify p w = true

instance [Verifiable P W] (p : P) (w : W) : Decidable (Discharged p w) := by
  unfold Discharged; exact inferInstanceAs (Decidable (_ = true))

/-- **The opaque search side (the prover plugin).** Given a predicate, *try* to
produce a discharging witness. Modelled as a partial function (`Option`) because
the search may be undecidable / nonterminating; the metatheory makes NO promise
about when it returns `some`. -/
class Searchable (P : Type*) (W : Type*) where
  find : P → Option W

/-- **Soundness-by-verification contract.** The ONLY guarantee demanded of any
search plugin: whatever it returns must verify. (No completeness; no termination.) -/
theorem search_sound
    [Verifiable P W] [Searchable P W] (p : P) (w : W)
    (h : Searchable.find p = some w) :
    Discharged p w := by
  -- PRIMITIVE: `Searchable.find` is an opaque oracle (the prover/matcher plugin).
  -- Soundness-by-verification is a *contract* on that external plugin; there is no
  -- relation between the typeclass's `find` and `Verify` in-module to derive it from.
  sorry

/-- **The polarity Galois connection induced by an arbitrary relation.**

Every binary relation `R : α → β → Prop` induces an antitone Galois connection
between the powerset lattices `Set α` and `Set β` (a "polarity", aka the Birkhoff
dual / formal-concept adjunction). We realise the antitone pair as a *monotone*
`GaloisConnection` into the order dual `(Set β)ᵒᵈ`:

* `l A = {b | ∀ a ∈ A, R a b}` — the upper polar (all `b` related to every `a ∈ A`);
* `u B = {a | ∀ b ∈ B, R a b}` — the lower polar (all `a` related to every `b ∈ B`).

The adjunction `l A ≤ B ↔ A ≤ u B` holds because both sides unfold to the single
symmetric condition `∀ a ∈ A, ∀ b ∈ B, R a b`. This is the standard, fully-provable
construction; no hypotheses beyond the relation are needed. -/
theorem polarity_galois {α β : Type*} (R : α → β → Prop) :
    GaloisConnection
      (fun A : Set α => toDual {b : β | ∀ a ∈ A, R a b})
      (fun B : (Set β)ᵒᵈ => {a : α | ∀ b ∈ ofDual B, R a b}) := by
  intro A B
  -- `l A ≤ B` in `(Set β)ᵒᵈ` is, by defeq, `ofDual B ⊆ {b | ∀ a ∈ A, R a b}`.
  show (ofDual B) ⊆ {b : β | ∀ a ∈ A, R a b} ↔ A ⊆ {a : α | ∀ b ∈ ofDual B, R a b}
  constructor
  · intro h a ha b hb; exact h hb a ha
  · intro h b hb a ha; exact h ha b hb

/-- **Law: `Predicate ⊣ Witness` is a Galois connection** (the verify/find seam).

The genuine predicate⊣witness content, obtained by instantiating `polarity_galois`
at the verifier relation `Discharged` (= `Verify · · = true`). It pins the two
preorders concretely:

* predicates ordered as sets `Set P` under entailment/⊆;
* witness-sets ordered as `(Set W)ᵒᵈ` (specificity: a smaller witness-set is "more
  specific", hence the order dual).

`l A = {w | every predicate in A is discharged by w}` (the witnesses satisfying all
of `A`) and `u B = {p | every witness in B discharges p}` (the predicates satisfied
by all of `B`) form an (antitone) Galois connection — the classic polarity induced
by the `Discharged`/`Verify` relation. This replaces the earlier placeholder which
quantified over *arbitrary* `l, u` and was false as stated. -/
theorem predicate_witness_galois [Verifiable P W] :
    GaloisConnection
      (fun A : Set P => toDual {w : W | ∀ p ∈ A, Discharged p w})
      (fun B : (Set W)ᵒᵈ => {p : P | ∀ w ∈ ofDual B, Discharged p w}) :=
  polarity_galois (fun (p : P) (w : W) => Discharged p w)

/-- **Law: the predicate algebra is Heyting.** Conjunction/implication of
admissibility conditions behaves intuitionistically (the residual of `⊓` is `⇨`),
which is exactly what justifies *attenuation* (a stricter predicate entails a
laxer one) in the authority module. -/
theorem predicate_heyting
    [HeytingAlgebra P] (a b c : P) :
    (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c) :=
  le_himp_iff.symm

end Metatheory.Laws
