/-
# Dregg2.Spec.Guard — the ONE verify/find seam, at four sites.

This is the first piece of the **factored middle layer**: the abstract spec of the
*actual* dregg2 semantics, sitting between the ultra-abstract `Dregg2.Core`/`Laws`/
`Boundary` and the executable `Dregg2.Exec.*`.

## The thesis (grounded in dregg1's real semantics)

dregg1 carried four superficially-distinct gating mechanisms:

  1. **authorization** — `AuthRequired ⊣ Authorization` (who may invoke an object);
  2. **action preconditions** — a transition's guard (`balance ≥ amount`, …);
  3. **program state-constraints** — a circuit/program's admissibility predicate;
  4. **capability / macaroon caveats** — attenuating restrictions on a bearer cap.

The claim of this module: **they are all the same object.** Each is a deterministic
predicate over a *request* (the transition/action/access facts) that is either

  • **first-party** — decidable *now*, with no external evidence (`p req : Bool`); or
  • **witnessed** — discharged by the §8 **verify seam** (`Laws.Verifiable.Verify`)
    against a supplied witness for a `Statement`,

AND-composed (conjunction = the lattice **meet**), with `OneOf` alternation (the ∨ /
coproduct), and negation, **narrow-only** under attenuation.

## The one seam, eight kinds, behind a single oracle

The witnessed branch routes EVERY external check through `Laws.Verifiable.Verify :
Statement → Witness → Bool` — the registry oracle. dregg1's eight verifier kinds
(Dfa, Merkle membership, NonMembership, BlindedSet, temporal/DFA, bridge, Pedersen,
…) are **instances behind that oracle**, NOT variants of `Guard`. Each kind carries
its own *epistemic boundary*: the oracle is decidable and verifier-local, but it is
trusted as a black box — the metatheory commits only to "if `Verify` says `true`,
the certificate checked", never to completeness or to *finding* a witness (that is
`Laws.Searchable`, the opaque prover plugin). The kinds are documented, never
enumerated as constructors: a flat ~30-variant port is exactly the legacy mistake
this layer exists to delete.

## The algebra (read this before `attenuate`)

`Guard.admits · req w : Bool` evaluates a guard. Under a fixed `(req, w)`,
`admits · req w` is a Boolean-algebra homomorphism (`all`↦⊓, `any`↦⊔, `gnot`↦ᶜ) —
the algebra of guards is Boolean-over-decidable-predicates **incidentally**. But
**attenuation is the MEET, not the Heyting residual.** `attenuate g c := all [g, c]`
adds a conjunct; `attenuate_narrows` is precisely the meet-semilattice law `a ⊓ b ≤
a`, NOT `a ≤ b ⇨ c` (the residual `⇨` of `Laws.predicate_heyting`). Attenuation
never *weakens*, never introduces an implication: it only ever shrinks the admitted
set. Keeping this straight is the whole point of the framing — see `attenuate` and
`attenuate_narrows` below.
-/
import Dregg2.Laws
import Dregg2.Tactics

namespace Dregg2.Spec

open Dregg2.Laws

universe u

/-! ## §1 — Abstract carriers.

`Request`, `Statement`, `Witness` are abstract **type parameters**, never `Nat`. A
`Request` is what a guard reads (the transition/action/access facts); a `Statement`
is a verify-seam claim; a `Witness` is its discharging evidence. The verify oracle
is `Laws.Verifiable Statement Witness` — a typeclass parameter, the registry behind
which the eight dregg1 kinds live as instances. -/

variable {Request : Type u} {Statement : Type u} {Witness : Type u}

/-! ## §2 — The Guard primitive.

A SMALL set of orthogonal primitives. The legacy catalog is *generated* from these
(see §6), not transcribed. -/

/-- A **Guard**: a deterministic gate over a `Request`, the single object unifying
authorization, action preconditions, program state-constraints, and caveats.

* `firstParty p` — decidable *now* from the request alone (no external evidence);
* `witnessed s` — discharged through the verify seam (`Verify s (w s)`) for the
  statement `s` (this is the single site where the eight oracle kinds enter);
* `all gs` — conjunction; the lattice **meet** (∧). The neutral guard is `all []`;
* `any gs` — alternation; the **OneOf** coproduct (∨). `any []` is the bottom guard;
* `gnot g` — negation (used narrow-only, e.g. non-membership as `gnot (witnessed …)`).

Note `firstParty` takes `Request → Bool` and `witnessed` takes a bare `Statement`;
the witness supply `w : Statement → Witness` is provided at *evaluation* time
(§3), modelling the demand⊣supply split (§5): the guard is the demand, the
`(req, w)` pair is the supply. -/
inductive Guard (Request Statement : Type u) : Type u where
  | firstParty (p : Request → Bool)
  | witnessed  (s : Statement)
  | all  (gs : List (Guard Request Statement))
  | any  (gs : List (Guard Request Statement))
  | gnot (g : Guard Request Statement)

namespace Guard

/-! ## §3 — Evaluation (`admits`).

The recursion descends through `List Guard`; we use a `mutual` block with explicit
`List`-fold helpers so termination is structural and the conjunction/alternation
characterizations (§4) fall out by `simp`. -/

mutual
  /-- Evaluate guard `g` on request `req` with witness supply `w`. -/
  def admits [Verifiable Statement Witness]
      (g : Guard Request Statement) (req : Request) (w : Statement → Witness) : Bool :=
    match g with
    | firstParty p => p req
    | witnessed s  => Verifiable.Verify s (w s)
    | all gs       => admitsAll gs req w
    | any gs       => admitsAny gs req w
    | gnot g       => !admits g req w

  /-- `all`: every conjunct admits (meet). `admitsAll [] = true`. -/
  def admitsAll [Verifiable Statement Witness]
      (gs : List (Guard Request Statement)) (req : Request) (w : Statement → Witness) : Bool :=
    match gs with
    | []      => true
    | g :: gs => admits g req w && admitsAll gs req w

  /-- `any`: some disjunct admits (join / OneOf). `admitsAny [] = false`. -/
  def admitsAny [Verifiable Statement Witness]
      (gs : List (Guard Request Statement)) (req : Request) (w : Statement → Witness) : Bool :=
    match gs with
    | []      => false
    | g :: gs => admits g req w || admitsAny gs req w
end

variable [Verifiable Statement Witness]

@[simp] theorem admits_firstParty (p : Request → Bool) (req : Request) (w : Statement → Witness) :
    admits (firstParty p) req w = p req := by simp [admits]

@[simp] theorem admits_witnessed (s : Statement) (req : Request) (w : Statement → Witness) :
    admits (witnessed s : Guard Request Statement) req w = Verifiable.Verify s (w s) := by
  simp [admits]

@[simp] theorem admits_all_eq (gs : List (Guard Request Statement))
    (req : Request) (w : Statement → Witness) :
    admits (all gs) req w = admitsAll gs req w := by simp [admits]

@[simp] theorem admits_any_eq (gs : List (Guard Request Statement))
    (req : Request) (w : Statement → Witness) :
    admits (any gs) req w = admitsAny gs req w := by simp [admits]

@[simp] theorem admits_gnot (g : Guard Request Statement) (req : Request) (w : Statement → Witness) :
    admits (gnot g) req w = !admits g req w := by simp [admits]

@[simp] theorem admitsAll_nil (req : Request) (w : Statement → Witness) :
    admitsAll ([] : List (Guard Request Statement)) req w = true := by simp [admitsAll]

@[simp] theorem admitsAll_cons (g : Guard Request Statement) (gs : List (Guard Request Statement))
    (req : Request) (w : Statement → Witness) :
    admitsAll (g :: gs) req w = (admits g req w && admitsAll gs req w) := by simp [admitsAll]

@[simp] theorem admitsAny_nil (req : Request) (w : Statement → Witness) :
    admitsAny ([] : List (Guard Request Statement)) req w = false := by simp [admitsAny]

@[simp] theorem admitsAny_cons (g : Guard Request Statement) (gs : List (Guard Request Statement))
    (req : Request) (w : Statement → Witness) :
    admitsAny (g :: gs) req w = (admits g req w || admitsAny gs req w) := by simp [admitsAny]

/-! ## §4 — `all`/`any` characterizations (the meet / join content). -/

/-- **`all` is the meet**: a conjunction admits iff every conjunct admits. -/
theorem admits_all (gs : List (Guard Request Statement)) (req : Request) (w : Statement → Witness) :
    admits (all gs) req w = true ↔ ∀ g ∈ gs, admits g req w = true := by
  rw [admits_all_eq]
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih]

/-- **`any` is the join (OneOf)**: an alternation admits iff some disjunct admits. -/
theorem admits_any (gs : List (Guard Request Statement)) (req : Request) (w : Statement → Witness) :
    admits (any gs) req w = true ↔ ∃ g ∈ gs, admits g req w = true := by
  rw [admits_any_eq]
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih, Bool.or_eq_true]

/-! ## §5 — Attenuation: the MEET, not the residual.

`attenuate g c` adds the conjunct `c` to `g`. This is the only narrowing operation
the authority/caveat layer needs: a macaroon caveat, an extra precondition, a
tighter program constraint — all are *more* conjuncts, the meet `a ⊓ b`. -/

/-- Attenuate `g` by the additional guard `c`: conjoin `c`. **MEET only** — this
uses `all` (the ∧), *never* the Heyting residual `⇨` of `Laws.predicate_heyting`.
The guard algebra happens to be Boolean-over-decidable-predicates, but attenuation
is the meet-semilattice operation `a ↦ a ⊓ c`, whose defining inequality is `a ⊓ c
≤ a` (`attenuate_narrows`), NOT `a ≤ c ⇨ b`. Attenuation can only ever *shrink* the
admitted set; it can never weaken a guard. -/
def attenuate (g c : Guard Request Statement) : Guard Request Statement := all [g, c]

@[simp] theorem admits_attenuate (g c : Guard Request Statement)
    (req : Request) (w : Statement → Witness) :
    admits (attenuate g c) req w = (admits g req w && admits c req w) := by
  simp [attenuate]

/-- **`attenuate_narrows` — the meet-semilattice narrowing law `a ⊓ b ≤ a`.**
Attenuating then admitting implies the un-attenuated guard already admitted: adding
a conjunct can only *remove* admitted requests. This is the formal content of
"attenuation is monotone-decreasing / narrow-only", and it is the MEET law — not a
Heyting residual statement. -/
theorem attenuate_narrows (g c : Guard Request Statement) (req : Request) (w : Statement → Witness)
    (h : admits (attenuate g c) req w = true) : admits g req w = true := by
  rw [admits_attenuate, Bool.and_eq_true] at h
  exact h.1

/-! ## §6 — The demand ⊣ supply bridge to `Laws`.

The factored-layer payoff: `admits` on a `witnessed` guard **IS** `Laws.Discharged`
at the verify seam. A `Guard` is the *demand* (a predicate awaiting evidence); a
`(req, w)` is the *supply* (the request facts + the witness map); `admits` is
`Verify` evaluated at the seam. So the four gating sites collapse onto the single
`Predicate ⊣ Witness` adjunction of `Laws`. -/

/-- **The seam bridge**: a `witnessed s` guard admits under supply `w` *exactly* when
the verifier discharges `s` with `w s` — i.e. `admits (witnessed s)` is definitionally
`Laws.Discharged s (w s)`. This is the demand⊣supply connection: guard = demand,
`(req, w)` = supply, `admits` = `Verify` at the seam. -/
theorem admits_witnessed_iff_discharged (s : Statement) (req : Request) (w : Statement → Witness) :
    admits (witnessed s : Guard Request Statement) req w = true ↔ Discharged s (w s) := by
  simp [Discharged]

/-- Corollary at the adjunction: if the verify side accepts (`Discharged`), the
witnessed guard admits — and conversely. The `Guard` layer therefore *imports* the
soundness contract of `Laws.search_sound` for free: any witness the opaque prover
(`Laws.Searchable.find`) returns and that this guard accepts is one the verifier has
checked. -/
theorem discharged_admits (s : Statement) (req : Request) (w : Statement → Witness)
    (h : Discharged s (w s)) :
    admits (witnessed s : Guard Request Statement) req w = true :=
  (admits_witnessed_iff_discharged s req w).mpr h

/-! ## §7 — DERIVED legacy reconstructions.

The cleanup payoff: dregg1's gate catalog is *generated* from the primitives, not
enumerated. A few representatives — note each is one line over `firstParty`/
`witnessed`/`any`, and each comes with a characterization lemma proving it really
denotes the legacy predicate. -/

/-- `monotonic f` — "the request's `f`-projection is ≥ a threshold `t`" (a
precondition like `balance ≥ amount`). DERIVED: a `firstParty` over the decidable
order. -/
def monotonic (f : Request → Nat) (t : Nat) : Guard Request Statement :=
  firstParty (fun req => decide (t ≤ f req))

@[simp] theorem admits_monotonic (f : Request → Nat) (t : Nat)
    (req : Request) (w : Statement → Witness) :
    admits (monotonic f t : Guard Request Statement) req w = true ↔ t ≤ f req := by
  simp [monotonic]

/-- `sumEquals fs v` — "the sum of the request projections `fs` equals `v`" (a
conservation/state-constraint, e.g. `Σ inputs = Σ outputs`). DERIVED: `firstParty`
over decidable equality. -/
def sumEquals (fs : List (Request → Nat)) (v : Nat) : Guard Request Statement :=
  firstParty (fun req => decide ((fs.map (fun f => f req)).sum = v))

@[simp] theorem admits_sumEquals (fs : List (Request → Nat)) (v : Nat)
    (req : Request) (w : Statement → Witness) :
    admits (sumEquals fs v : Guard Request Statement) req w = true
      ↔ (fs.map (fun f => f req)).sum = v := by
  simp [sumEquals]

/-- `senderAuthorized s` — "the invoker is authorized", the `AuthRequired ⊣
Authorization` site. DERIVED: a `witnessed` guard over the authorization statement
`s` (the authority oracle is one of the eight `Verifiable` instances behind the
seam). -/
def senderAuthorized (s : Statement) : Guard Request Statement := witnessed s

@[simp] theorem admits_senderAuthorized (s : Statement) (req : Request) (w : Statement → Witness) :
    admits (senderAuthorized s : Guard Request Statement) req w = true ↔ Discharged s (w s) :=
  admits_witnessed_iff_discharged s req w

/-- `oneOf gs` — the `OneOf` alternation (any-of-these caveats / disjunctive
authorization). DERIVED: literally `any`. -/
def oneOf (gs : List (Guard Request Statement)) : Guard Request Statement := any gs

/-- `nonMembership s` — "the statement `s` is NOT discharged" (non-membership /
nullifier-absence, dregg1's `NonMembership` kind). DERIVED: `gnot (witnessed …)` —
demonstrating that negation is a primitive, not a fresh verifier variant. -/
def nonMembership (s : Statement) : Guard Request Statement := gnot (witnessed s)

@[simp] theorem admits_nonMembership (s : Statement) (req : Request) (w : Statement → Witness) :
    admits (nonMembership s : Guard Request Statement) req w = true ↔ ¬ Discharged s (w s) := by
  simp [nonMembership, Discharged]

/-- Characterization of the derived `oneOf` (the legacy `OneOf` semantics): admits
iff some alternative admits. Inherited from the `any` join law. -/
theorem admits_oneOf (gs : List (Guard Request Statement)) (req : Request) (w : Statement → Witness) :
    admits (oneOf gs) req w = true ↔ ∃ g ∈ gs, admits g req w = true :=
  admits_any gs req w

end Guard

/-! ## §8 — Axiom-hygiene tripwires.

Pin the proved keystones: each must depend ONLY on the three standard kernel axioms
(no `sorryAx`). These cover the meet-narrowing law, both lattice characterizations,
the demand⊣supply bridge, and the derived reconstructions. -/

#assert_axioms Guard.admits_all
#assert_axioms Guard.admits_any
#assert_axioms Guard.attenuate_narrows
#assert_axioms Guard.admits_attenuate
#assert_axioms Guard.admits_witnessed_iff_discharged
#assert_axioms Guard.discharged_admits
#assert_axioms Guard.admits_monotonic
#assert_axioms Guard.admits_sumEquals
#assert_axioms Guard.admits_senderAuthorized
#assert_axioms Guard.admits_nonMembership
#assert_axioms Guard.admits_oneOf

end Dregg2.Spec
