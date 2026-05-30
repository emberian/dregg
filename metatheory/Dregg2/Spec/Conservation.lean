/-
# Dregg2.Spec.Conservation — multi-domain, `LinearityClass`-typed, value-monoid-parametric
conservation.

`Dregg2.Core` states conservation as ONE monoid-valued measure with a global mint/burn
balance. The real dregg2 (grounded in `turn/src/action.rs: LinearityClass` /
`Effect::linearity` and the `turn/src/executor/{execute,finalize,atomic}.rs` +
`cell` committed-conservation discipline) is richer in three orthogonal ways, all of which
this module makes faithful in the factored middle layer:

  1. **A coloring `LinearityClass`** — an effect is not just "ordinary vs mint/burn". It
     carries one of *exactly six* linearity colors that say HOW it is allowed to move a
     conserved quantity. A new effect MUST answer its color (the classifiers are exhaustive
     `match`es with no default arm — adding a variant breaks the build until it is colored).

  2. **A coloring map `linearity : Effect → LinearityClass`** over an ABSTRACT effect
     carrier (we do not port the 50-variant dregg1 enum; three example effects suffice to
     witness the coloring — a transfer is `Conservative`, a mint is `Generative`, a
     set-field is `Neutral`).

  3. **Per-domain conservation, PARAMETRIC over a value monoid `Bal`** (the crucial
     generalization). The conserved quantity in a domain need not be cleartext `ℤ`; the
     SAME law `Σδ = 0` runs over a *commitment group* in the private case. Conservation is
     stated per `Domain` (balance / note-per-asset / gas / cross-cell) and the domains
     conserve INDEPENDENTLY.

## The four key theorems

  * `conservation_over_monoid` — the `ℤ` conservation of `Core` generalized to an arbitrary
    `AddCommMonoid Bal`: if the Conservative deltas sum to `0`, the domain total is
    preserved. PROVED, axiom-clean.

  * `disclosed_non_conservation` — a `Generative`/`Annihilative` effect's domain delta need
    NOT be `0`, but `is_disclosed_non_conservation` forces a *disclosure obligation* bound
    into the receipt (un-strippable data). Stated as the receipt-binding discipline. PROVED
    (the structural facts), with the binding modelled as data.

  * `committed_iff_cleartext` — the privacy payoff. Given a monoid hom `h : Cleartext →+
    Commitment` (Pedersen; reusable as `PrivacyKernel.commitHom`, here taken as an
    `AddMonoidHom` PARAMETER so the law is stated over arbitrary monoids and rests on a
    *hypothesis*, not an axiom), `Σ (cleartext δ) = 0 ↔ Σ (h ∘ δ) = 0` *provided `h` is
    injective on the relevant sum* (the forward direction is the pure homomorphism fact and
    needs no injectivity; the backward — "committed Σ = 0 ⇒ cleartext Σ = 0" — is exactly
    where binding/injectivity is consumed). PROVED via `map_sum`/`map_zero`.

  * `multi_domain_independent` — the domains conserve INDEPENDENTLY: a turn conserves iff
    every domain conserves; no cross-domain leakage. PROVED as the conjunction form.

## §8 obligations (NOT discharged here — they are the circuit's job, not the Lean law)

  * **range-proof anti-inflation rib** — `committed_iff_cleartext` shows committed Σ = 0 is
    equivalent to cleartext Σ = 0, but a *malicious* prover could commit to an out-of-range
    (e.g. astronomically large mod-group-order, "negative") value to hide inflation while
    still satisfying Σ = 0. Ruling that out requires a per-note RANGE proof — see
    `-- OPEN:` below. The Lean law assumes well-formed openings; the range proof is the
    circuit obligation that makes the assumption sound.

Discipline: abstract value types (no `Nat`-for-semantics — `Bal` is an `AddCommMonoid`
param); exhaustive classifiers (no default arm); `#assert_axioms` on the clean keystones;
no `axiom`/`admit`/`native_decide`/sorry-alias. Imports ONLY existing built modules.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Dregg2.Tactics

namespace Dregg2.Spec

open scoped BigOperators

/-! ## 1. `LinearityClass` — the six-color coloring, with two PROVED classifiers.

Mirrors `turn/src/action.rs: LinearityClass`. Exactly six colors; the classifiers are
exhaustive `match`es with NO default arm, so a newly-added effect color cannot compile until
it answers both questions ("must it have a paired sibling?", "is it a *disclosed*
non-conservation?"). -/

/-- The linearity color of an effect — HOW it is permitted to move a conserved quantity.
Exactly six, mirroring `turn/src/action.rs`. -/
inductive LinearityClass where
  /-- Paired conservation: the per-domain deltas must sum to `0` (`Σδ = 0`). A debit must be
  matched by an equal credit (the transfer / move discipline). -/
  | Conservative
  /-- Monotone growth: the quantity may only increase (e.g. an append-only counter, a
  monotone clock). Never decreases; no paired sibling required. -/
  | Monotonic
  /-- One-way / terminal: a state may transition out but never back (e.g. a finalized /
  consumed marker). Irreversible, unpaired. -/
  | Terminal
  /-- Ex-nihilo creation: the quantity is created from nothing (a mint). NOT conserved —
  but the non-conservation is *disclosed* (the minted amount is bound into the receipt). -/
  | Generative
  /-- Destruction: the quantity is destroyed (a burn). NOT conserved — but, like
  `Generative`, the non-conservation is *disclosed* in the receipt. -/
  | Annihilative
  /-- No delta: the effect touches no conserved quantity in any domain (e.g. setting an
  opaque metadata field). The trivial color. -/
  | Neutral
  deriving DecidableEq, Repr

namespace LinearityClass

/-- **`requires_paired_sibling`** — true iff the color is `Conservative`. A `Conservative`
effect's delta is only admissible when matched by an equal-and-opposite sibling delta so the
domain sum stays `0`; every other color stands alone. Exhaustive `match`, no default arm. -/
def requires_paired_sibling : LinearityClass → Bool
  | Conservative => true
  | Monotonic    => false
  | Terminal     => false
  | Generative   => false
  | Annihilative => false
  | Neutral      => false

/-- **`is_disclosed_non_conservation`** — true iff the color is `Generative` or
`Annihilative`. These are the two colors that legitimately break `Σδ = 0`, and precisely
because they do, the broken amount must be DISCLOSED (bound into the receipt, see §6).
Exhaustive `match`, no default arm. -/
def is_disclosed_non_conservation : LinearityClass → Bool
  | Generative   => true
  | Annihilative => true
  | Conservative => false
  | Monotonic    => false
  | Terminal     => false
  | Neutral      => false

/-! ### Classifier facts (PROVED — they pin the prose claims to the `def`s). -/

/-- `requires_paired_sibling` is true *exactly* on `Conservative`. -/
theorem requires_paired_sibling_iff (c : LinearityClass) :
    c.requires_paired_sibling = true ↔ c = Conservative := by
  cases c <;> simp [requires_paired_sibling]

/-- `is_disclosed_non_conservation` is true *exactly* on `Generative` or `Annihilative`. -/
theorem is_disclosed_non_conservation_iff (c : LinearityClass) :
    c.is_disclosed_non_conservation = true ↔ (c = Generative ∨ c = Annihilative) := by
  cases c <;> simp [is_disclosed_non_conservation]

/-- The two classifiers are DISJOINT: nothing both requires a paired sibling and is a
disclosed non-conservation (a conserved color and a disclosed-broken color are mutually
exclusive — the soundness backbone of the coloring). -/
theorem paired_and_disclosed_exclusive (c : LinearityClass) :
    ¬ (c.requires_paired_sibling = true ∧ c.is_disclosed_non_conservation = true) := by
  cases c <;> simp [requires_paired_sibling, is_disclosed_non_conservation]

end LinearityClass

/-! ## 2. The coloring map `linearity : Effect → LinearityClass`.

`Effect` is an ABSTRACT carrier — we do NOT port dregg1's 50-variant enum. A tiny example
type witnesses the coloring: a transfer (Conservative), a mint (Generative), a set-field
(Neutral). The real `Effect::linearity` is exactly such a total map over the real enum. -/

/-- A *tiny* example effect carrier — three constructors are enough to witness that the
coloring map is total and discriminating. (The real system colors a 50-variant enum the
same way; the carrier is abstract precisely so this module does not depend on its shape.) -/
inductive Effect where
  /-- Move `amount` of an asset from one cell to another — paired, conserves. -/
  | transfer (amount : Nat)
  /-- Create `amount` of an asset from nothing — disclosed, generative. -/
  | mint (amount : Nat)
  /-- Set an opaque metadata field — touches no conserved quantity. -/
  | setField
  deriving DecidableEq, Repr

/-- **The coloring map.** `Effect::linearity` — total, exhaustive, no default arm. -/
def linearity : Effect → LinearityClass
  | .transfer _ => .Conservative
  | .mint _     => .Generative
  | .setField   => .Neutral

/-- Witness that the coloring is discriminating: a transfer is paired, a mint is a disclosed
non-conservation, a set-field is neither. -/
theorem linearity_examples :
    (linearity (.transfer 7)).requires_paired_sibling = true ∧
    (linearity (.mint 7)).is_disclosed_non_conservation = true ∧
    (linearity .setField).requires_paired_sibling = false ∧
    (linearity .setField).is_disclosed_non_conservation = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [linearity, LinearityClass.requires_paired_sibling,
          LinearityClass.is_disclosed_non_conservation]

/-! ## 3. Domains, and per-domain conservation PARAMETRIC over a value monoid `Bal`.

The conserved quantity in a domain is valued in an arbitrary commutative monoid `Bal`. In
the public case `Bal = ℤ` (cleartext balances); in the private case `Bal` is a commitment
group (Pedersen digests). The SAME `conservedInDomain` law runs over both — that is the
whole point of factoring the value type out as a parameter. -/

/-- The conservation domains — `balance` / `note`-per-asset / `gas` / `crossCell`. Abstract;
the only structure that matters is that they are DISTINCT and conserve INDEPENDENTLY. -/
inductive Domain where
  /-- Fungible cell balances. -/
  | balance
  /-- Shielded notes, indexed per asset. -/
  | note
  /-- Gas / metering budget. -/
  | gas
  /-- Cross-cell (inter-vat) value in flight. -/
  | crossCell
  deriving DecidableEq, Repr

section PerDomain

/- The value monoid for a domain. `Bal = ℤ` in the public case, a commitment group in the
private case — the law below does not care which. -/
variable {Bal : Type*} [AddCommMonoid Bal]

/-- **Per-domain conservation criterion.** A domain `dom` conserves under a list of the
`Conservative`-effects' per-point deltas iff those deltas sum to `0` in `Bal`. This is the
`Conservative`-color obligation, lifted to an arbitrary value monoid. (The `dom` argument is
carried so the SAME predicate names the four independent domain obligations.) -/
def conservedInDomain (_dom : Domain) (deltas : List Bal) : Prop :=
  deltas.sum = 0

/-- **KEY THEOREM 1 — `conservation_over_monoid`.** The `ℤ` conservation of `Core`
generalized to an arbitrary `AddCommMonoid Bal`: if the `Conservative` deltas sum to `0`,
then adding them to any prior domain total `pre` leaves it unchanged
(`pre + Σδ = pre`). This is the clean `AddCommMonoid` fact underlying every per-domain
conservation proof — the executable kernels' `Finset.sum` debit/credit cancellation is the
`Bal = ℤ` instance of exactly this. PROVED, axiom-clean. -/
theorem conservation_over_monoid (dom : Domain) (pre : Bal) (deltas : List Bal)
    (hcons : conservedInDomain dom deltas) :
    pre + deltas.sum = pre := by
  unfold conservedInDomain at hcons
  rw [hcons, add_zero]

/-- The `Finset.sum` form of `conservation_over_monoid`, matching the shape the executable
kernels use (a balance `bal : ι → Bal` and a delta function `δ : ι → Bal` over a `Finset`).
If the deltas sum to `0`, the post total equals the pre total. PROVED, axiom-clean. -/
theorem conservation_over_monoid_finset {ι : Type*} (acc : Finset ι) (bal δ : ι → Bal)
    (hzero : (∑ i ∈ acc, δ i) = 0) :
    (∑ i ∈ acc, (bal i + δ i)) = ∑ i ∈ acc, bal i := by
  rw [Finset.sum_add_distrib, hzero, add_zero]

end PerDomain

/-! ## 4. The disclosure obligation for non-conservation (receipt-binding discipline).

A `Generative`/`Annihilative` effect's domain delta is NOT required to be `0`. But because
`is_disclosed_non_conservation` is true for exactly those colors, the broken amount must be
DISCLOSED: bound into the receipt as data that cannot be stripped (the verifier checks the
receipt carries the disclosed delta for every disclosed-non-conservation effect). We model
"bound into the receipt" as the disclosed delta being a FIELD of the receipt record, so the
binding is structural, not a side condition. -/

section Disclosure

-- The disclosure discipline is purely structural — it does not touch the value algebra, so
-- `Bal` enters as a bare type (no `AddCommMonoid` needed for receipt well-formedness).
variable {Bal : Type*}

/-- A minimal receipt fragment: the effect's color and, when it is a disclosed
non-conservation, the disclosed domain delta carried AS DATA (un-strippable — it is a field,
so a receipt without it is a different value, not a stripped one). `disclosedDelta = none`
for a conserving/neutral/monotone/terminal color; `some δ` for `Generative`/`Annihilative`. -/
structure Receipt (Bal : Type*) where
  /-- The color of the effect this receipt witnesses. -/
  color : LinearityClass
  /-- The disclosed domain delta, present iff the color is a disclosed non-conservation. -/
  disclosedDelta : Option Bal

/-- A receipt is *well-formed* iff it discloses a delta EXACTLY when its color demands it:
`disclosedDelta.isSome ↔ color.is_disclosed_non_conservation`. This is the binding the
verifier enforces — a `Generative`/`Annihilative` effect cannot produce a receipt that omits
its delta, and a conserving effect cannot smuggle a spurious one. -/
def Receipt.WellFormed (r : Receipt Bal) : Prop :=
  r.disclosedDelta.isSome = r.color.is_disclosed_non_conservation

/-- **KEY THEOREM 2 — `disclosed_non_conservation`.** For a well-formed receipt whose effect
is a disclosed non-conservation (`Generative`/`Annihilative`), the disclosed delta is
PRESENT (the obligation is discharged structurally) — and dually, a non-disclosed color
carries NO delta. The delta itself is NOT constrained to be `0` (that is the whole point:
mint/burn legitimately break conservation), but its disclosure is FORCED. PROVED. -/
theorem disclosed_non_conservation (r : Receipt Bal) (hwf : r.WellFormed) :
    (r.color.is_disclosed_non_conservation = true → r.disclosedDelta.isSome) ∧
    (r.color.is_disclosed_non_conservation = false → r.disclosedDelta = none) := by
  unfold Receipt.WellFormed at hwf
  refine ⟨fun hdisc => ?_, fun hndisc => ?_⟩
  · rw [hwf, hdisc]
  · -- `disclosedDelta.isSome = false`, so it is `none`.
    have : r.disclosedDelta.isSome = false := by rw [hwf, hndisc]
    cases hd : r.disclosedDelta with
    | none => rfl
    | some v => rw [hd] at this; simp at this

/-- Corollary: a `Conservative` effect's receipt discloses NOTHING — its only obligation is
`Σδ = 0` (§3), checked against the deltas, not the receipt. Confirms the two regimes are
disjoint: conserved ⇒ no disclosure, disclosed ⇒ not conserved. PROVED. -/
theorem conservative_discloses_nothing (r : Receipt Bal) (hwf : r.WellFormed)
    (hc : r.color = LinearityClass.Conservative) :
    r.disclosedDelta = none := by
  apply (disclosed_non_conservation r hwf).2
  rw [hc]; rfl

end Disclosure

/-! ## 5. KEY THEOREM 3 — `committed_iff_cleartext` (the privacy payoff).

Conservation over HIDDEN committed values is EQUIVALENT to cleartext conservation. The
federation verifies `Σδ = 0` over commitments WITHOUT opening them. The homomorphism `h`
(Pedersen — reuse `PrivacyKernel.commitHom`, here a PARAMETER `Cleartext →+ Commitment` so
the law is monoid-generic and rests on a *hypothesis*, not an axiom) carries the equivalence:

  * **forward** (cleartext Σ = 0 ⇒ committed Σ = 0): the pure homomorphism fact, `map_sum`
    then `map_zero`. Needs NOTHING about `h` beyond being a hom. This is the direction the
    PROVER uses — it knows the cleartext sum vanishes, and the commitment sum vanishes for
    free, so it can publish "Σ over commitments = 0" as the verifier's check.

  * **backward** (committed Σ = 0 ⇒ cleartext Σ = 0): consumes that `h` is INJECTIVE (the
    binding property of the commitment — distinct openings give distinct commitments, modulo
    the §8 range rib). This is the direction the VERIFIER trusts: seeing the commitment sum
    vanish, it concludes the cleartext sum vanishes WITHOUT learning any opening.

The `↔` form is stated under `Function.Injective h` (binding); the forward half is also
exposed standalone since it needs no injectivity. -/

section Committed

variable {Cleartext Commitment : Type*}
  [AddCommMonoid Cleartext] [AddCommMonoid Commitment]

/-- **Forward half — the homomorphism fact (no injectivity needed).** If the cleartext
deltas sum to `0`, then the COMMITTED deltas (`h` applied pointwise) also sum to `0`. PROVED
via `map_sum`/`map_zero`. This is what lets a prover publish a committed conservation check
the verifier can run blind. -/
theorem committed_of_cleartext (h : Cleartext →+ Commitment)
    {ι : Type*} (s : Finset ι) (δ : ι → Cleartext)
    (hcleartext : (∑ i ∈ s, δ i) = 0) :
    (∑ i ∈ s, h (δ i)) = 0 := by
  rw [← map_sum h δ s, hcleartext, map_zero]

/-- **KEY THEOREM 3 — `committed_iff_cleartext`.** Under the BINDING hypothesis that the
commitment hom `h` is injective, conservation over hidden committed values is EQUIVALENT to
cleartext conservation: `Σ (cleartext δ) = 0 ↔ Σ (h ∘ δ) = 0`. So the federation's blind
check (`Σ commitments = 0`) is sound *and* complete for real cleartext conservation —
"value hidden yet provably conserved". PROVED via `map_sum`/`map_zero` + injectivity; rests
on the hom + injectivity HYPOTHESES (parameters, not axioms — `#assert_axioms`-clean). -/
theorem committed_iff_cleartext (h : Cleartext →+ Commitment) (hinj : Function.Injective h)
    {ι : Type*} (s : Finset ι) (δ : ι → Cleartext) :
    (∑ i ∈ s, δ i) = 0 ↔ (∑ i ∈ s, h (δ i)) = 0 := by
  constructor
  · exact committed_of_cleartext h s δ
  · intro hcommitted
    -- Σ h(δ i) = h (Σ δ i) = 0 = h 0, then injectivity strips the commitment.
    rw [← map_sum h δ s] at hcommitted
    have : h (∑ i ∈ s, δ i) = h 0 := by rw [hcommitted, map_zero]
    exact hinj this

end Committed

/-! ## 6. KEY THEOREM 4 — `multi_domain_independent`.

The four domains (balance ⊥ note ⊥ gas ⊥ crossCell) conserve INDEPENDENTLY: a turn conserves
iff EVERY domain conserves. There is no cross-domain leakage — a surplus in one domain cannot
silently cover a deficit in another (which would be the classic "pay gas with notes" attack).
We package the per-domain deltas as a function `Domain → List Bal` and state the whole-turn
predicate as the conjunction over the four domains. -/

section MultiDomain

variable {Bal : Type*} [AddCommMonoid Bal]

/-- A turn's per-domain `Conservative` deltas, one delta list per domain. -/
abbrev TurnDeltas (Bal : Type*) := Domain → List Bal

/-- **Whole-turn conservation = the conjunction of the four independent domain conservations.**
No cross-domain term — each domain's `Σδ = 0` stands alone. -/
def turnConserves (td : TurnDeltas Bal) : Prop :=
  conservedInDomain Domain.balance   (td Domain.balance) ∧
  conservedInDomain Domain.note      (td Domain.note) ∧
  conservedInDomain Domain.gas       (td Domain.gas) ∧
  conservedInDomain Domain.crossCell (td Domain.crossCell)

/-- **KEY THEOREM 4 — `multi_domain_independent`.** A turn conserves IFF every domain
conserves independently. The `↔` makes the independence precise in both directions:
whole-turn conservation is *nothing more* than the four separate domain checks (forward), and
those four checks SUFFICE (backward) — so no domain can borrow conservation from another.
PROVED, axiom-clean. -/
theorem multi_domain_independent (td : TurnDeltas Bal) :
    turnConserves td ↔
      (∀ dom : Domain, conservedInDomain dom (td dom)) := by
  unfold turnConserves
  constructor
  · rintro ⟨hb, hn, hg, hc⟩ dom
    cases dom <;> assumption
  · intro h
    exact ⟨h Domain.balance, h Domain.note, h Domain.gas, h Domain.crossCell⟩

/-- A turn that conserves in every domain conserves the BALANCE domain in particular — the
projection witnessing that the conjunction really does carry each domain separately (no
domain is vacuous). PROVED. -/
theorem turnConserves_balance (td : TurnDeltas Bal) (h : turnConserves td) :
    (td Domain.balance).sum = 0 :=
  ((multi_domain_independent td).1 h Domain.balance)

end MultiDomain

/-! ## 7. §8 OPEN — the range-proof anti-inflation rib.

`committed_iff_cleartext` proves: committed `Σδ = 0` ⇔ cleartext `Σδ = 0`, ASSUMING the
openings are well-formed cleartext values. A *malicious* prover, though, can satisfy
`Σ commitments = 0` by committing to an out-of-range value (e.g. a "negative" amount that is
really a huge value modulo the group order), hiding inflation while the blind sum still
checks out. The Lean conservation law CANNOT rule this out — it is parametric over `Bal` and
sees only the algebra. Soundness requires a per-note RANGE proof (each committed `δ` lies in
`[0, 2^n)`), which is the CIRCUIT's job, not this module's.

-- OPEN (§8, circuit obligation, NOT proved here): for every committed delta there exists a
--   range proof `0 ≤ value < 2^n` verified against the commitment. With that rib in place,
--   `committed_iff_cleartext` is sound against hidden inflation; without it, the algebraic
--   `Σ = 0` is necessary but not sufficient. We state it as a hypothesis the executable /
--   circuit layer must supply, deliberately leaving the obligation visible rather than
--   silently assuming it.
-/

/-- The shape of the §8 range obligation, as a hypothesis the circuit layer discharges: every
committed delta has a verified range witness. We do NOT prove it here (it is not an algebraic
fact); we name it so downstream proofs can take it as an explicit premise rather than smuggle
it. `InRange v` abstracts "`0 ≤ v < 2^n`, proven against the commitment". -/
def RangeObligation {ι Bal : Type*} (InRange : Bal → Prop) (s : Finset ι) (δ : ι → Bal) :
    Prop :=
  ∀ i ∈ s, InRange (δ i)

/-! ## Axiom-hygiene — pin the clean keystones.

The four key theorems plus their supporting classifier facts are axiom-clean (they rest only
on `propext`/`Classical.choice`/`Quot.sound`). `committed_iff_cleartext` rests additionally
on its hom + injectivity HYPOTHESES — those are parameters, not `axiom`-keyword declarations,
so they correctly do not appear in `collectAxioms` and the guard passes. -/

#assert_axioms LinearityClass.requires_paired_sibling_iff
#assert_axioms LinearityClass.is_disclosed_non_conservation_iff
#assert_axioms LinearityClass.paired_and_disclosed_exclusive
#assert_axioms linearity_examples
#assert_axioms conservation_over_monoid
#assert_axioms conservation_over_monoid_finset
#assert_axioms disclosed_non_conservation
#assert_axioms conservative_discloses_nothing
#assert_axioms committed_of_cleartext
#assert_axioms committed_iff_cleartext
#assert_axioms multi_domain_independent
#assert_axioms turnConserves_balance

end Dregg2.Spec
