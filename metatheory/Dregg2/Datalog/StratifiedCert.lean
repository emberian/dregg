/-
# Dregg2.Datalog.StratifiedCert — stratified-negation Datalog certificates over an MMR-committed EDB,
with an exact Count (lane A of `docs/automata/SUBSTRATE-DECISION.md` §7, 2026-11-06).

Additive over `Dregg2.Datalog.FixpointCert`: its `Term`, `Atom`, `Fact`, `Subst`, `applyAtom`,
`substs`, `substOk`, `addFact`, `Firing`, `Round`, `Trace`, `flatten`, `countQ` are reused unmoved.

## The object

A **statement** is `(program, strata, root, pred, count)`: a program whose rule bodies are literals
(`Lit.pos a` / `Lit.neg a`), a stratification (`Strata := List (List Nat)`, rule indices per
stratum, lowest first), the MMR root of the EDB's injective flattening, a predicate, a claimed count.
The stratification is PART OF THE STATEMENT (the ceiling note §1.2: "decidable, and part of `x`").
A **certificate** is the EDB plus one semi-naive trace per stratum. `verifyS hash st c`:

  1. `stratifiedB`: every rule index lies in some stratum, no index twice; a predicate defined by a
     rule of stratum `k` is defined by no rule of a later stratum (so: in exactly one stratum); a
     positive body atom's predicate is defined in the same or a lower stratum (or only in the EDB);
     a negated body atom's predicate is defined in a STRICTLY lower stratum (or only in the EDB);
  2. the root recompute and EDB `Nodup` (as `FixpointCert.verify`);
  3. per stratum, in order, with `lower` the database the previous strata left: replay (positive
     atoms present in the current database, negated atoms ABSENT FROM `lower`, substitutions over
     the active domain, the firing's rule in this stratum), then `closedS` (for every rule of the
     stratum and every admissible substitution: positives present and negatives absent from
     `lower` ⇒ head present), then move on;
  4. `countQ` of the final database against the claim.

## The semantics, and why this formulation

`DerivesAt P dom S L` is the least fixpoint of stratum `S`'s rules over a LOWER database given as a
predicate `L : Fact → Prop`: a negated literal holds iff its instance is NOT in `L`. The stratified
model is the fold `stratDbFrom` over the strata list, each stratum's fixpoint becoming the next
one's `L`; `DerivesS P strata edb := stratDbFrom P (activeDomainS P edb) strata (· ∈ edb)`.
Parameterizing by the lower database (rather than one inductive indexed by stratum number) makes
each stratum's induction the `FixpointCert.closed_complete` induction verbatim, and the iterated
fixpoint a structural recursion on the strata list; the per-stratum equality of the checker's
database with `DerivesAt` is transported to the next stratum by `funext`/`propext`.

The checker reads negation against `lower`, the snapshot at the stratum's start. For a stratified
program that is the SAME as reading it against the final database, and `verifyS_supported_model`
says so: the accepted database is a fixpoint of the immediate-consequence operator with negation
read against ITSELF (a supported model). That theorem is where `stratifiedB` is load-bearing; the
exactness theorems hold for any strata the statement names.

## What is proved (kernel-clean, §7)

  * `stratified_replay_sound`: every fact of a replayed stratum is in that stratum's fixpoint.
  * `stratified_closed_complete`: a closed stratum database contains the whole stratum fixpoint.
  * `verifyS_sound`: an accepted certificate yields a duplicate-free database that is EXACTLY the
    stratified-semantics database `DerivesS`, whose `pred`-count is the claim, whose EDB flattens to
    the committed root, and whose stratification passed `stratifiedB`.
  * `countS_unique_or_collides`: two accepted certificates for one `(program, strata, root, pred)`
    claim the same count, or the sponge collides at the `mrootFind` pair.
  * `verifyS_strata_exact` (codex round 3, finding 17): one duplicate-free database per stratum,
    the `i`-th EXACTLY the cumulative model `Mᵢ` (`M₋₁ = edb`, one global active domain, negated
    literals read against the frozen, closure-verified `Mᵢ₋₁`); the count is the last one's.
  * `verifyS_intended_or_collides`: for an externally intended EDB `E` with the committed root, the
    accepted count is the exact count over `E`, or the sponge collides at the named pair.
  * `verifyS_supported_model`: the accepted database `db` satisfies
    `f ∈ db ↔ f ∈ edb ∨ ∃ r ∈ P, ∃ s, ruleFiresS r s db db = some f` (negation read against `db`).

## Falsifiers (§7; `#guard`s are compiled evaluation; `active1_derivesS`, `active2_not_derivesS` and
the three (c) propositions `forged_accepted_by_currentDb`, `forged_refused_by_verifyS`,
`honest_count0_verifies` are kernel-checked by `decide`). Each weaker checker's ACCEPTANCE is
exhibited beside `verifyS`'s refusal (codex round 2 §1d):

  (a) `active(X) :- issued(X), ¬revoked(X)` over `issued(1), issued(2), revoked(2)`: the honest
      trace verifies at count 1.
  (b) the forged-absence trace firing `active(2)` makes `replayS` return `none`; the positive
      projection checked by `FixpointCert.verify` (negation dropped) ACCEPTS it at count 2.
  (c) the revocation is DERIVABLE LATER (codex round 3, finding 18): EDB `issued(1), flagged(1)`,
      stratum 0 `revoked(X) :- flagged(X)`, stratum 1 the `active` rule; honest count 0. The
      schedule "fire `active(1)`, then `revoked(1)`" at count 1 is ACCEPTED by
      `verifyCurrentDbNegation` (negation against the current database, no closure barrier between
      strata; end-of-run closure passes because the negative rule is now disabled and closure never
      removes an admitted head) and refused by `verifyS`. The open-lower-stratum trace (stratum 0
      never fires) is ACCEPTED by `verifyNoLowerClosure` (closure at the top stratum only) at count
      1 and refused by `verifyS`.
  (d) `p(X) :- q(X), ¬p(X)` is refused by `stratifiedB`; `verifyNoStratCheck` ACCEPTS a trace for it
      deriving `p(1)`, and that database is not supported (`supportedB = false`): `p(1)`'s only
      support is `¬p(1)`.

## Scope, stated
  * Active-domain semantics, as `FixpointCert`. For safe programs it IS the unrestricted stratified
    model (`SafeCoincidence.derivesS_eq_unrestricted`; `verifyJ_sound_unrestricted` for the exe).
  * Count is exact for the strata NAMED in the statement. Independence of the perfect model from the
    choice of stratification (Apt-Blair-Walker) is NOT proved here; `countS_unique_or_collides`
    therefore needs equal `strata` as well as equal rule lists.
  * No coincidence theorem with a well-founded or stable-model semantics; for stratified programs
    those agree with this one classically, not here.
  * `countQ` counts by predicate symbol, not `(pred, arity)`.

## Prior art (not a first)
Benzaken-Contejean-Dumbrava, ITP 2017 (certified stratified Datalog engine in Coq/SSReflect);
Tantow et al., ITP 2025 (Lean checker for Datalog derivation certificates). What is ours is the
same as `FixpointCert`'s: the per-stratum closure leg as an executable exactness certificate with
the MMR root binding and the named-pair collision residual.

## Costs (counts, not clocks)
Per firing: `|body|` membership tests (positives against the current db, negatives against the
stratum's `lower`) and one `addFact`. Per stratum closure: `Σ_{r ∈ S} |dom|^{varBound r}` body
evaluations. `stratifiedB`: `O(|P| · |body| · |strata|)` membership tests, statement-only.

## Axiom hygiene
`#assert_all_clean` on every theorem. NEW file; `FixpointCert` imported read-only. -/
import Dregg2.Datalog.FixpointCert

namespace Dregg2.Datalog.StratifiedCert

open Dregg2.Datalog.FixpointCert
open Dregg2.Lightclient.MMR (mroot MRootColl mroot_binds_or_collides)

set_option autoImplicit false

/-! ## §1 — Syntax. -/

/-- A body literal: a positive or a negated atom. -/
inductive Lit where
  | pos (a : Atom)
  | neg (a : Atom)
  deriving Repr, DecidableEq

def Lit.atom : Lit → Atom
  | .pos a => a
  | .neg a => a

/-- A rule `head :- l₁, …, lₙ` over literals. -/
structure SRule where
  head : Atom
  body : List Lit
  deriving Repr, DecidableEq

abbrev SProgram := List SRule

/-- A stratification: rule indices per stratum, lowest stratum first. -/
abbrev Strata := List (List Nat)

/-- Forget polarity: the rule over the underlying atoms (for variables and constants). -/
def SRule.toRule (r : SRule) : Rule := { head := r.head, body := r.body.map Lit.atom }

def varBoundS (r : SRule) : Nat := varBound r.toRule

/-- The active domain: the constants of the EDB and of the program (negated atoms included). -/
def activeDomainS (P : SProgram) (edb : List Fact) : List ℤ :=
  activeDomain (P.map SRule.toRule) edb

theorem applyAtom_pred {s : Subst} {a : Atom} {f : Fact} (h : applyAtom s a = some f) :
    f.1 = a.pred := by
  unfold applyAtom at h
  obtain ⟨vs, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-! ## §2 — Literal and body evaluation against `(cur, lower)`. -/

/-- A literal holds: a positive atom against the current database, a negated one against `lower`. -/
def litHolds (s : Subst) (cur lower : List Fact) : Lit → Bool
  | .pos a => atomHolds s cur a
  | .neg a =>
    match applyAtom s a with
    | some f => !decide (f ∈ lower)
    | none => false

theorem litHolds_pos (s : Subst) (cur lower : List Fact) (a : Atom) :
    litHolds s cur lower (.pos a) = true ↔ ∃ f, applyAtom s a = some f ∧ f ∈ cur :=
  atomHolds_iff s cur a

theorem litHolds_neg (s : Subst) (cur lower : List Fact) (a : Atom) :
    litHolds s cur lower (.neg a) = true ↔ ∃ f, applyAtom s a = some f ∧ f ∉ lower := by
  simp only [litHolds]
  cases applyAtom s a <;> simp

def bodyHoldsS (s : Subst) (cur lower : List Fact) (r : SRule) : Bool :=
  r.body.all (litHolds s cur lower)

theorem bodyHoldsS_iff (s : Subst) (cur lower : List Fact) (r : SRule) :
    bodyHoldsS s cur lower r = true ↔
      (∀ a, Lit.pos a ∈ r.body → ∃ f, applyAtom s a = some f ∧ f ∈ cur) ∧
      (∀ a, Lit.neg a ∈ r.body → ∃ f, applyAtom s a = some f ∧ f ∉ lower) := by
  unfold bodyHoldsS
  rw [List.all_eq_true]
  constructor
  · intro h
    exact ⟨fun a ha => (litHolds_pos s cur lower a).mp (h _ ha),
      fun a ha => (litHolds_neg s cur lower a).mp (h _ ha)⟩
  · rintro ⟨hp, hn⟩ l hl
    cases l with
    | pos a => exact (litHolds_pos s cur lower a).mpr (hp a hl)
    | neg a => exact (litHolds_neg s cur lower a).mpr (hn a hl)

def ruleFiresS (r : SRule) (s : Subst) (cur lower : List Fact) : Option Fact :=
  if bodyHoldsS s cur lower r then applyAtom s r.head else none

theorem ruleFiresS_some {r : SRule} {s : Subst} {cur lower : List Fact} {h : Fact}
    (hf : ruleFiresS r s cur lower = some h) :
    bodyHoldsS s cur lower r = true ∧ applyAtom s r.head = some h := by
  unfold ruleFiresS at hf
  by_cases hb : bodyHoldsS s cur lower r = true
  · rw [if_pos hb] at hf; exact ⟨hb, hf⟩
  · rw [if_neg hb] at hf; exact absurd hf (by simp)

theorem ruleFiresS_of {r : SRule} {s : Subst} {cur lower : List Fact} {h : Fact}
    (hb : bodyHoldsS s cur lower r = true) (hh : applyAtom s r.head = some h) :
    ruleFiresS r s cur lower = some h := by
  unfold ruleFiresS; rw [if_pos hb]; exact hh

/-- Transfer a firing between databases: positives that move, negatives whose absence moves. -/
theorem ruleFiresS_transfer {r : SRule} {s : Subst} {cur lower cur' lower' : List Fact} {h : Fact}
    (hp : ∀ a, Lit.pos a ∈ r.body → ∀ f, applyAtom s a = some f → f ∈ cur → f ∈ cur')
    (hn : ∀ a, Lit.neg a ∈ r.body → ∀ f, applyAtom s a = some f → f ∈ lower' → f ∈ lower)
    (hf : ruleFiresS r s cur lower = some h) : ruleFiresS r s cur' lower' = some h := by
  obtain ⟨hb, hh⟩ := ruleFiresS_some hf
  obtain ⟨hP, hN⟩ := (bodyHoldsS_iff _ _ _ _).mp hb
  refine ruleFiresS_of ((bodyHoldsS_iff _ _ _ _).mpr ⟨?_, ?_⟩) hh
  · intro a ha
    obtain ⟨f, hf1, hf2⟩ := hP a ha
    exact ⟨f, hf1, hp a ha f hf1 hf2⟩
  · intro a ha
    obtain ⟨f, hf1, hf2⟩ := hN a ha
    exact ⟨f, hf1, fun hl => hf2 (hn a ha f hf1 hl)⟩

/-! ## §3 — Semantics: per-stratum least fixpoints over the closed lower database. -/

/-- **`DerivesAt P dom S L f`** — `f` is in the least fixpoint of the rules of stratum `S` (indices
into `P`) over the lower database `L`, substitutions over `dom`; a negated literal holds iff its
instance is NOT in `L`. -/
inductive DerivesAt (P : SProgram) (dom : List ℤ) (S : List Nat) (L : Fact → Prop) : Fact → Prop
  | base {f : Fact} : L f → DerivesAt P dom S L f
  | fire {i : Nat} {r : SRule} {s : Subst} {h : Fact} :
      i ∈ S → P[i]? = some r → s ∈ substs dom (varBoundS r) →
      (∀ a, Lit.pos a ∈ r.body → (applyAtom s a).isSome = true) →
      (∀ a, Lit.pos a ∈ r.body → ∀ f, applyAtom s a = some f → DerivesAt P dom S L f) →
      (∀ a, Lit.neg a ∈ r.body → ∃ f, applyAtom s a = some f ∧ ¬ L f) →
      applyAtom s r.head = some h → DerivesAt P dom S L h

/-- The iterated fixpoint: each stratum's fixpoint is the next stratum's lower database. -/
def stratDbFrom (P : SProgram) (dom : List ℤ) : Strata → (Fact → Prop) → Fact → Prop
  | [], L => L
  | S :: rest, L => stratDbFrom P dom rest (DerivesAt P dom S L)

/-- **`DerivesS P strata edb f`** — `f` is in the stratified model of `P` over `edb`. -/
def DerivesS (P : SProgram) (strata : Strata) (edb : List Fact) : Fact → Prop :=
  stratDbFrom P (activeDomainS P edb) strata (· ∈ edb)

/-! ## §4 — Stratification, the executable syntactic check. -/

/-- The predicates the rules of stratum `S` define. -/
def headPreds (P : SProgram) (S : List Nat) : List Nat :=
  S.filterMap fun i => (P[i]?).map (·.head.pred)

theorem mem_headPreds {P : SProgram} {S : List Nat} {i : Nat} {r : SRule}
    (hi : i ∈ S) (hr : P[i]? = some r) : r.head.pred ∈ headPreds P S := by
  unfold headPreds
  exact List.mem_filterMap.mpr ⟨i, hi, by simp [hr]⟩

/-- One literal of a rule in stratum `S`, followed by the strata `rest`, respects stratification. -/
def litOkB (P : SProgram) (S : List Nat) (rest : Strata) : Lit → Bool
  | .pos a => rest.all fun T => !decide (a.pred ∈ headPreds P T)
  | .neg a => !decide (a.pred ∈ headPreds P S) && rest.all fun T => !decide (a.pred ∈ headPreds P T)

/-- Stratum `S` followed by `rest`: every rule exists, its literals are admissible, and its head
predicate is defined by no later stratum. -/
def stratumOkB (P : SProgram) (S : List Nat) (rest : Strata) : Bool :=
  S.all fun i =>
    match P[i]? with
    | none => false
    | some r => r.body.all (litOkB P S rest) &&
        rest.all fun T => !decide (r.head.pred ∈ headPreds P T)

def suffixOkB (P : SProgram) : Strata → Bool
  | [] => true
  | S :: rest => stratumOkB P S rest && suffixOkB P rest

/-- **`stratifiedB`** — the partition covers every rule exactly once and every stratum is admissible. -/
def stratifiedB (P : SProgram) (strata : Strata) : Bool :=
  suffixOkB P strata && decide strata.flatten.Nodup &&
    (List.range P.length).all fun i => strata.any fun T => decide (i ∈ T)

theorem stratumOkB_spec {P : SProgram} {S : List Nat} {rest : Strata}
    (h : stratumOkB P S rest = true) : ∀ i ∈ S, ∃ r, P[i]? = some r ∧
      (∀ a, Lit.pos a ∈ r.body → ∀ T ∈ rest, a.pred ∉ headPreds P T) ∧
      (∀ a, Lit.neg a ∈ r.body → a.pred ∉ headPreds P S ∧ ∀ T ∈ rest, a.pred ∉ headPreds P T) := by
  unfold stratumOkB at h
  rw [List.all_eq_true] at h
  intro i hi
  have hx := h i hi
  cases hr : P[i]? with
  | none => rw [hr] at hx; exact absurd hx (by simp)
  | some r =>
    rw [hr] at hx
    simp only [Bool.and_eq_true, List.all_eq_true] at hx
    obtain ⟨hbody, _⟩ := hx
    refine ⟨r, rfl, ?_, ?_⟩
    · intro a ha T hT
      have := hbody _ ha
      simp only [litOkB, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact this T hT
    · intro a ha
      have := hbody _ ha
      simp only [litOkB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at this
      exact this

theorem stratifiedB_cover {P : SProgram} {strata : Strata} (h : stratifiedB P strata = true)
    {r : SRule} (hr : r ∈ P) : ∃ i, P[i]? = some r ∧ ∃ T ∈ strata, i ∈ T := by
  unfold stratifiedB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨_, hcov⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hlt : i < P.length := by
    obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.mp hi
    exact hl
  exact ⟨i, hi, hcov i hlt⟩

/-! ## §5 — The executable checker. -/

/-- One firing in stratum `S`: its rule must be in `S`, the substitution admissible, the body hold. -/
def applyFiringS (P : SProgram) (dom : List ℤ) (S : List Nat) (lower cur : List Fact)
    (fr : Firing) : Option (List Fact) :=
  if fr.rule ∈ S then
    match P[fr.rule]? with
    | none => none
    | some r =>
      if substOk dom r.toRule fr.subst then (ruleFiresS r fr.subst cur lower).map (addFact cur)
      else none
  else none

theorem applyFiringS_some {P : SProgram} {dom : List ℤ} {S : List Nat} {lower cur db' : List Fact}
    {fr : Firing} (h : applyFiringS P dom S lower cur fr = some db') :
    ∃ r hd, fr.rule ∈ S ∧ P[fr.rule]? = some r ∧ fr.subst ∈ substs dom (varBoundS r) ∧
      ruleFiresS r fr.subst cur lower = some hd ∧ db' = addFact cur hd := by
  unfold applyFiringS at h
  by_cases hS : fr.rule ∈ S
  · rw [if_pos hS] at h
    cases hr : P[fr.rule]? with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some r =>
      rw [hr] at h
      simp only at h
      by_cases hok : substOk dom r.toRule fr.subst = true
      · rw [if_pos hok] at h
        obtain ⟨hd, hf, hdb⟩ := Option.map_eq_some_iff.mp h
        exact ⟨r, hd, hS, rfl, (substOk_iff _ _ _).mp hok, hf, hdb.symm⟩
      · rw [if_neg hok] at h
        exact absurd h (by simp)
  · rw [if_neg hS] at h
    exact absurd h (by simp)

def applyFiringsS (P : SProgram) (dom : List ℤ) (S : List Nat) (lower : List Fact) :
    List Fact → List Firing → Option (List Fact)
  | db, [] => some db
  | db, fr :: rest => (applyFiringS P dom S lower db fr).bind fun db' =>
      applyFiringsS P dom S lower db' rest

/-- Replay a stratum's rounds (a round is its firings in order, as in `FixpointCert.applyRound`). -/
def replayS (P : SProgram) (dom : List ℤ) (S : List Nat) (lower db : List Fact)
    (rds : List Round) : Option (List Fact) :=
  applyFiringsS P dom S lower db rds.flatten

/-- Any invariant one firing preserves, the replay preserves. -/
theorem applyFiringsS_induct {P : SProgram} {dom : List ℤ} {S : List Nat} {lower : List Fact}
    (Q : List Fact → Prop)
    (step : ∀ db db' fr, Q db → applyFiringS P dom S lower db fr = some db' → Q db') :
    ∀ (frs : List Firing) (db db' : List Fact), Q db →
      applyFiringsS P dom S lower db frs = some db' → Q db'
  | [], db, db', hq, h => by
    simp only [applyFiringsS, Option.some.injEq] at h; subst h; exact hq
  | fr :: rest, db, db', hq, h => by
    simp only [applyFiringsS, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact applyFiringsS_induct Q step rest db₁ db' (step db db₁ fr hq h₁) h₂

theorem replayS_superset {P : SProgram} {dom : List ℤ} {S : List Nat} {lower db db' : List Fact}
    {rds : List Round} (h : replayS P dom S lower db rds = some db') : ∀ g ∈ db, g ∈ db' := by
  refine applyFiringsS_induct (fun d => ∀ g ∈ db, g ∈ d) ?_ _ db db' (fun _ hg => hg) h
  intro d d' fr hq hf g hg
  obtain ⟨_, hd, _, _, _, _, rfl⟩ := applyFiringS_some hf
  exact subset_addFact d hd g (hq g hg)

theorem replayS_nodup {P : SProgram} {dom : List ℤ} {S : List Nat} {lower db db' : List Fact}
    {rds : List Round} (hn : db.Nodup) (h : replayS P dom S lower db rds = some db') :
    db'.Nodup := by
  refine applyFiringsS_induct (fun d => d.Nodup) ?_ _ db db' hn h
  intro d d' fr hq hf
  obtain ⟨_, hd, _, _, _, _, rfl⟩ := applyFiringS_some hf
  exact nodup_addFact hq hd

/-- **Per-stratum closure** — for every rule of `S` and every admissible substitution, if the
positives are present in `db` and the negatives absent from `lower`, the head is in `db`. -/
def closedS (P : SProgram) (dom : List ℤ) (S : List Nat) (lower db : List Fact) : Bool :=
  S.all fun i =>
    match P[i]? with
    | none => false
    | some r => (substs dom (varBoundS r)).all fun s =>
        match ruleFiresS r s db lower with
        | some h => decide (h ∈ db)
        | none => true

theorem closedS_iff (P : SProgram) (dom : List ℤ) (S : List Nat) (lower db : List Fact) :
    closedS P dom S lower db = true ↔
      ∀ i ∈ S, ∃ r, P[i]? = some r ∧ ∀ s ∈ substs dom (varBoundS r), ∀ h,
        ruleFiresS r s db lower = some h → h ∈ db := by
  unfold closedS
  rw [List.all_eq_true]
  constructor
  · intro H i hi
    have hx := H i hi
    cases hr : P[i]? with
    | none => rw [hr] at hx; exact absurd hx (by simp)
    | some r =>
      rw [hr] at hx
      simp only [List.all_eq_true] at hx
      refine ⟨r, rfl, fun s hs h hf => ?_⟩
      have := hx s hs
      rw [hf] at this
      simpa using this
  · intro H i hi
    obtain ⟨r, hr, hcl⟩ := H i hi
    rw [hr]
    simp only [List.all_eq_true]
    intro s hs
    cases hf : ruleFiresS r s db lower with
    | none => rfl
    | some h => simpa using hcl s hs h hf

/-- Run the strata in order: replay each against the previous database, then close it. -/
def runStrata (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact → Option (List Fact)
  | [], [], db => some db
  | S :: rest, t :: ts, db =>
    match replayS P dom S db db t.rounds with
    | none => none
    | some db₁ => if closedS P dom S db db₁ then runStrata P dom rest ts db₁ else none
  | _, _, _ => none

theorem runStrata_cons {P : SProgram} {dom : List ℤ} {S : List Nat} {rest : Strata} {t : Trace}
    {ts : List Trace} {db db' : List Fact} (h : runStrata P dom (S :: rest) (t :: ts) db = some db') :
    ∃ db₁, replayS P dom S db db t.rounds = some db₁ ∧ closedS P dom S db db₁ = true ∧
      runStrata P dom rest ts db₁ = some db' := by
  simp only [runStrata] at h
  cases hr : replayS P dom S db db t.rounds with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some db₁ =>
    rw [hr] at h
    simp only at h
    by_cases hc : closedS P dom S db db₁ = true
    · rw [if_pos hc] at h; exact ⟨db₁, rfl, hc, h⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)

/-- The statement: program, stratification, committed EDB root, counted predicate, claimed count. -/
structure SStatement where
  program : SProgram
  strata : Strata
  root : ℤ
  pred : Nat
  count : Nat
  deriving Repr

/-- The certificate: the EDB and one semi-naive trace per stratum. -/
structure SCertificate where
  edb : List Fact
  traces : List Trace
  deriving Repr

/-- **The verifier.** -/
def verifyS (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match runStrata st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

/-! ## §6 — Soundness, completeness, exactness. -/

/-- ⚑ **`stratified_replay_sound`** — every fact of a replayed stratum database is in the stratum's
fixpoint over its lower database. -/
theorem stratified_replay_sound {P : SProgram} {dom : List ℤ} {S : List Nat} {lower db : List Fact}
    {rds : List Round} (h : replayS P dom S lower lower rds = some db) :
    ∀ f ∈ db, DerivesAt P dom S (· ∈ lower) f := by
  refine applyFiringsS_induct (fun d => ∀ f ∈ d, DerivesAt P dom S (· ∈ lower) f) ?_ _ lower db
    (fun _ hf => DerivesAt.base hf) h
  intro d d' fr hq hf
  obtain ⟨r, hd, hi, hr, hs, hfire, rfl⟩ := applyFiringS_some hf
  intro g hg
  rcases mem_addFact hg with hg | rfl
  · exact hq g hg
  · obtain ⟨hb, hh⟩ := ruleFiresS_some hfire
    obtain ⟨hP, hN⟩ := (bodyHoldsS_iff _ _ _ _).mp hb
    refine DerivesAt.fire hi hr hs ?_ ?_ hN hh
    · intro a ha
      obtain ⟨f, hf', _⟩ := hP a ha
      rw [hf']; rfl
    · intro a ha f hf'
      obtain ⟨f', hf'', hin⟩ := hP a ha
      rw [hf'] at hf''
      simp only [Option.some.injEq] at hf''
      subst hf''
      exact hq f hin

/-- ⚑ **`stratified_closed_complete`** — a stratum database that contains its lower database and is
closed (`closedS`) contains every fact of the stratum's fixpoint. -/
theorem stratified_closed_complete {P : SProgram} {dom : List ℤ} {S : List Nat}
    {lower db : List Fact} (hcl : closedS P dom S lower db = true)
    (hsub : ∀ f ∈ lower, f ∈ db) : ∀ f, DerivesAt P dom S (· ∈ lower) f → f ∈ db := by
  intro f hf
  induction hf with
  | base h => exact hsub _ h
  | @fire i r s h hi hr hs hsome _ hneg hhead ih =>
    have hb : bodyHoldsS s db lower r = true := by
      refine (bodyHoldsS_iff _ _ _ _).mpr ⟨?_, hneg⟩
      intro a ha
      obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.mp (hsome a ha)
      exact ⟨f', hf', ih a ha f' hf'⟩
    obtain ⟨r', hr', hcl'⟩ := (closedS_iff _ _ _ _ _).mp hcl i hi
    rw [hr] at hr'
    simp only [Option.some.injEq] at hr'
    subst hr'
    exact hcl' s hs h (ruleFiresS_of hb hhead)

/-- The strata run is exactly the iterated fixpoint, and duplicate-free. -/
theorem runStrata_sound {P : SProgram} {dom : List ℤ} :
    ∀ (strata : Strata) (ts : List Trace) (db db' : List Fact), db.Nodup →
      runStrata P dom strata ts db = some db' →
      db'.Nodup ∧ ∀ f, f ∈ db' ↔ stratDbFrom P dom strata (· ∈ db) f
  | [], [], db, db', hn, h => by
    simp only [runStrata, Option.some.injEq] at h; subst h
    exact ⟨hn, fun f => Iff.rfl⟩
  | [], _ :: _, _, _, _, h => by simp [runStrata] at h
  | _ :: _, [], _, _, _, h => by simp [runStrata] at h
  | S :: rest, t :: ts, db, db', hn, h => by
    obtain ⟨db₁, hr, hc, h'⟩ := runStrata_cons h
    have hex : (fun f => f ∈ db₁) = DerivesAt P dom S (· ∈ db) :=
      funext fun f => propext ⟨fun hf => stratified_replay_sound hr f hf,
        stratified_closed_complete hc (replayS_superset hr) f⟩
    obtain ⟨hn', hm⟩ := runStrata_sound rest ts db₁ db' (replayS_nodup hn hr) h'
    refine ⟨hn', fun f => ?_⟩
    rw [hm f]
    simp only [stratDbFrom]
    rw [hex]

/-- ⚑ **`verifyS_sound`** — an accepted certificate: the stratification passed `stratifiedB`, the
EDB flattens to the committed root, and there is a duplicate-free database that is EXACTLY the
stratified model, whose count at `pred` is the claimed count. -/
theorem verifyS_sound (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyS hash st c = true) :
    stratifiedB st.program st.strata = true ∧ mroot hash (flatten c.edb) = st.root ∧
    ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ DerivesS st.program st.strata c.edb f) ∧
      countQ db st.pred = st.count := by
  unfold verifyS at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hst, hroot⟩, hnd⟩, hrest⟩ := h
  refine ⟨hst, hroot, ?_⟩
  cases hrun : runStrata st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    rw [hrun] at hrest
    simp only [beq_iff_eq] at hrest
    obtain ⟨hn, hm⟩ := runStrata_sound _ _ _ _ hnd hrun
    exact ⟨db, hn, hm, hrest⟩

/-- ⚑ **`countS_unique_or_collides`** — the stratified Count is a FUNCTION of
`(program, strata, root, pred)`, or the sponge collides at the named pair. -/
theorem countS_unique_or_collides (hash : List ℤ → ℤ) (st₁ st₂ : SStatement)
    (c₁ c₂ : SCertificate)
    (hP : st₁.program = st₂.program) (hS : st₁.strata = st₂.strata) (hR : st₁.root = st₂.root)
    (hp : st₁.pred = st₂.pred)
    (h₁ : verifyS hash st₁ c₁ = true) (h₂ : verifyS hash st₂ c₂ = true) :
    st₁.count = st₂.count ∨ MRootColl hash (flatten c₁.edb) (flatten c₂.edb) := by
  obtain ⟨_, r₁, db₁, hn₁, hm₁, hc₁⟩ := verifyS_sound hash st₁ c₁ h₁
  obtain ⟨_, r₂, db₂, hn₂, hm₂, hc₂⟩ := verifyS_sound hash st₂ c₂ h₂
  rcases mroot_binds_or_collides hash (r₁.trans (hR.trans r₂.symm)) with heq | hc
  · refine Or.inl ?_
    have hedb : c₁.edb = c₂.edb := flatten_injective _ _ heq
    have hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂ := by
      intro f
      rw [hm₁, hm₂, hedb, hP, hS]
    rw [← hc₁, ← hc₂, hp]
    exact countQ_eq_of_same_members hn₁ hn₂ hm _
  · exact Or.inr hc

/-- The run's per-stratum databases: the `i`-th is duplicate-free and is EXACTLY the cumulative model
`Mᵢ` of strata `0..i` (`stratDbFrom` over `strata.take (i+1)`), and the last is the final database. -/
theorem runStrata_dbs {P : SProgram} {dom : List ℤ} :
    ∀ (strata : Strata) (ts : List Trace) (db db' : List Fact), db.Nodup →
      runStrata P dom strata ts db = some db' →
      ∃ dbs : List (List Fact), dbs.length = strata.length ∧
        (∀ (i : Nat) (hi : i < dbs.length), dbs[i].Nodup ∧
          ∀ f, f ∈ dbs[i] ↔ stratDbFrom P dom (strata.take (i + 1)) (· ∈ db) f) ∧
        (db :: dbs).getLast (List.cons_ne_nil _ _) = db'
  | [], [], db, db', _, h => by
    simp only [runStrata, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, fun i hi => absurd hi (by simp), rfl⟩
  | [], _ :: _, _, _, _, h => by simp [runStrata] at h
  | _ :: _, [], _, _, _, h => by simp [runStrata] at h
  | S :: rest, t :: ts, db, db', hn, h => by
    obtain ⟨db₁, hr, hc, h'⟩ := runStrata_cons h
    have hex : (fun f => f ∈ db₁) = DerivesAt P dom S (· ∈ db) :=
      funext fun f => propext ⟨fun hf => stratified_replay_sound hr f hf,
        stratified_closed_complete hc (replayS_superset hr) f⟩
    have hn₁ := replayS_nodup hn hr
    obtain ⟨dbs, hlen, hall, hlast⟩ := runStrata_dbs rest ts db₁ db' hn₁ h'
    refine ⟨db₁ :: dbs, by simp [hlen], ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        refine ⟨hn₁, fun f => ?_⟩
        simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero, stratDbFrom]
        rw [← hex]
      | succ k =>
        have hk : k < dbs.length := by simpa using hi
        obtain ⟨hnk, hmk⟩ := hall k hk
        refine ⟨by simpa using hnk, fun f => ?_⟩
        simp only [List.getElem_cons_succ, List.take_succ_cons, stratDbFrom]
        rw [← hex]
        exact hmk f
    · rw [List.getLast_cons (List.cons_ne_nil _ _)]
      exact hlast

/-- ⚑ **`verifyS_strata_exact`** — the per-stratum form (codex round 3, finding 17): an accepted
certificate determines a list of cumulative stratum databases, one per stratum, each EXACTLY `Mᵢ`
(`M₋₁ = edb`; `Mᵢ` = least fixpoint of stratum `i`'s rules over one global active domain, negated
literals read against `Mᵢ₋₁`); the claimed count is the count of the last one. -/
theorem verifyS_strata_exact (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyS hash st c = true) :
    stratifiedB st.program st.strata = true ∧ mroot hash (flatten c.edb) = st.root ∧
    ∃ dbs : List (List Fact), dbs.length = st.strata.length ∧
      (∀ (i : Nat) (hi : i < dbs.length), dbs[i].Nodup ∧ ∀ f, f ∈ dbs[i] ↔
        stratDbFrom st.program (activeDomainS st.program c.edb) (st.strata.take (i + 1))
          (· ∈ c.edb) f) ∧
      st.count = countQ ((c.edb :: dbs).getLast (List.cons_ne_nil _ _)) st.pred := by
  have ⟨hst, hroot, _⟩ := verifyS_sound hash st c h
  unfold verifyS at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, _⟩, hnd⟩, hrest⟩ := h
  cases hrun : runStrata st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    rw [hrun] at hrest
    simp only [beq_iff_eq] at hrest
    obtain ⟨dbs, hlen, hall, hlast⟩ := runStrata_dbs _ _ _ _ hnd hrun
    exact ⟨hst, hroot, dbs, hlen, hall, by rw [hlast, hrest]⟩

/-- ⚑ **`verifyS_intended_or_collides`** — against an externally intended EDB `E` with the committed
root: the accepted count is the exact stratified count over `E`, or the sponge collides at the named
`mrootFind` pair between the certificate's EDB and `E`. -/
theorem verifyS_intended_or_collides (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (E : List Fact) (hE : mroot hash (flatten E) = st.root) (h : verifyS hash st c = true) :
    (∃ db : List Fact, db.Nodup ∧ (∀ f, f ∈ db ↔ DerivesS st.program st.strata E f) ∧
      countQ db st.pred = st.count) ∨ MRootColl hash (flatten c.edb) (flatten E) := by
  obtain ⟨_, hroot, hex⟩ := verifyS_sound hash st c h
  rcases mroot_binds_or_collides hash (hroot.trans hE.symm) with heq | hc
  · left
    rw [← flatten_injective _ _ heq]
    exact hex
  · exact Or.inr hc

/-! ### §6½ — The stratified model is a supported model (where `stratifiedB` carries weight). -/

/-- A replayed stratum only adds facts of the predicates its rules define. -/
theorem replayS_preds {P : SProgram} {dom : List ℤ} {S : List Nat} {lower db db' : List Fact}
    {rds : List Round} (h : replayS P dom S lower db rds = some db') :
    ∀ f ∈ db', f ∈ db ∨ f.1 ∈ headPreds P S := by
  refine applyFiringsS_induct (fun d => ∀ f ∈ d, f ∈ db ∨ f.1 ∈ headPreds P S) ?_ _ db db'
    (fun f hf => Or.inl hf) h
  intro d d' fr hq hf
  obtain ⟨r, hd, hi, hr, _, hfire, rfl⟩ := applyFiringS_some hf
  intro g hg
  rcases mem_addFact hg with hg | rfl
  · exact hq g hg
  · refine Or.inr ?_
    rw [applyAtom_pred (ruleFiresS_some hfire).2]
    exact mem_headPreds hi hr

/-- Every fact a replayed stratum adds has a firing whose body holds in the replayed database. -/
theorem replayS_supported {P : SProgram} {dom : List ℤ} {S : List Nat} {lower db db' : List Fact}
    {rds : List Round} (h : replayS P dom S lower db rds = some db') :
    ∀ f ∈ db', f ∈ db ∨ ∃ i ∈ S, ∃ r, P[i]? = some r ∧ ∃ s ∈ substs dom (varBoundS r),
      ruleFiresS r s db' lower = some f := by
  refine applyFiringsS_induct (fun d => ∀ f ∈ d, f ∈ db ∨ ∃ i ∈ S, ∃ r, P[i]? = some r ∧
      ∃ s ∈ substs dom (varBoundS r), ruleFiresS r s d lower = some f) ?_ _ db db'
    (fun f hf => Or.inl hf) h
  intro d d' fr hq hf
  obtain ⟨r, hd, hi, hr, hs, hfire, rfl⟩ := applyFiringS_some hf
  have mono : ∀ {r' : SRule} {s' : Subst} {g : Fact}, ruleFiresS r' s' d lower = some g →
      ruleFiresS r' s' (addFact d hd) lower = some g :=
    fun hx => ruleFiresS_transfer (fun _ _ f _ hf => subset_addFact d hd f hf)
      (fun _ _ _ _ hl => hl) hx
  intro g hg
  rcases mem_addFact hg with hg | rfl
  · rcases hq g hg with hg' | ⟨i', hi', r', hr', s', hs', hf'⟩
    · exact Or.inl hg'
    · exact Or.inr ⟨i', hi', r', hr', s', hs', mono hf'⟩
  · exact Or.inr ⟨fr.rule, hi, r, hr, fr.subst, hs, mono hfire⟩

theorem runStrata_superset {P : SProgram} {dom : List ℤ} :
    ∀ (strata : Strata) (ts : List Trace) (db db' : List Fact),
      runStrata P dom strata ts db = some db' → ∀ g ∈ db, g ∈ db'
  | [], [], db, db', h => by
    simp only [runStrata, Option.some.injEq] at h; subst h; exact fun _ hg => hg
  | [], _ :: _, _, _, h => by simp [runStrata] at h
  | _ :: _, [], _, _, h => by simp [runStrata] at h
  | S :: rest, t :: ts, db, db', h => by
    obtain ⟨db₁, hr, _, h'⟩ := runStrata_cons h
    exact fun g hg => runStrata_superset rest ts db₁ db' h' g (replayS_superset hr g hg)

/-- The suffix invariant behind `verifyS_supported_model`: for an admissible strata suffix, the run's
final database adds only facts of the suffix's head predicates, is closed under every suffix rule
with negation read against ITSELF, and supports every added fact by such a rule. -/
theorem runStrata_supported_model {P : SProgram} {dom : List ℤ} :
    ∀ (strata : Strata) (ts : List Trace) (db db' : List Fact),
      suffixOkB P strata = true → runStrata P dom strata ts db = some db' →
      (∀ f ∈ db', f ∈ db ∨ ∃ T ∈ strata, f.1 ∈ headPreds P T) ∧
      (∀ T ∈ strata, ∀ i ∈ T, ∀ r, P[i]? = some r → ∀ s ∈ substs dom (varBoundS r), ∀ h,
        ruleFiresS r s db' db' = some h → h ∈ db') ∧
      (∀ f ∈ db', f ∈ db ∨ ∃ T ∈ strata, ∃ i ∈ T, ∃ r, P[i]? = some r ∧
        ∃ s ∈ substs dom (varBoundS r), ruleFiresS r s db' db' = some f)
  | [], [], db, db', _, h => by
    simp only [runStrata, Option.some.injEq] at h; subst h
    refine ⟨fun f hf => Or.inl hf, ?_, fun f hf => Or.inl hf⟩
    intro T hT; simp at hT
  | [], _ :: _, _, _, _, h => by simp [runStrata] at h
  | _ :: _, [], _, _, _, h => by simp [runStrata] at h
  | S :: rest, t :: ts, db, db', hok, h => by
    simp only [suffixOkB, Bool.and_eq_true] at hok
    obtain ⟨hS, hrest⟩ := hok
    obtain ⟨db₁, hrep, hc, h'⟩ := runStrata_cons h
    obtain ⟨I1, I2, I3⟩ := runStrata_supported_model rest ts db₁ db' hrest h'
    have sup01 := replayS_superset hrep
    have sup1' := runStrata_superset rest ts db₁ db' h'
    have A := replayS_preds hrep
    have B := replayS_supported hrep
    have C := (closedS_iff _ _ _ _ _).mp hc
    have D := stratumOkB_spec hS
    -- a fact of `db'` whose predicate no later stratum defines was already in `db₁`
    have back1 : ∀ f ∈ db', (∀ T ∈ rest, f.1 ∉ headPreds P T) → f ∈ db₁ := by
      intro f hf hno
      rcases I1 f hf with h1 | ⟨T, hT, hp⟩
      · exact h1
      · exact absurd hp (hno T hT)
    refine ⟨?_, ?_, ?_⟩
    · intro f hf
      rcases I1 f hf with h1 | ⟨T, hT, hp⟩
      · rcases A f h1 with h0 | hp
        · exact Or.inl h0
        · exact Or.inr ⟨S, List.mem_cons_self, hp⟩
      · exact Or.inr ⟨T, List.mem_cons_of_mem _ hT, hp⟩
    · intro T hT i hi r hr s hs hd hf
      rcases List.mem_cons.mp hT with rfl | hT
      · obtain ⟨r', hr', hpos, _⟩ := D i hi
        rw [hr] at hr'
        simp only [Option.some.injEq] at hr'
        subst hr'
        obtain ⟨r'', hr'', hcl⟩ := C i hi
        rw [hr] at hr''
        simp only [Option.some.injEq] at hr''
        subst hr''
        refine sup1' hd (hcl s hs hd (ruleFiresS_transfer ?_ ?_ hf))
        · intro a ha f haf hfin
          refine back1 f hfin ?_
          rw [applyAtom_pred haf]
          exact hpos a ha
        · intro a _ f _ hfin
          exact sup1' f (sup01 f hfin)
      · exact I2 T hT i hi r hr s hs hd hf
    · intro f hf
      rcases I3 f hf with h1 | ⟨T, hT, i, hi, r, hr, s, hs, hfire⟩
      · rcases B f h1 with h0 | ⟨i, hi, r, hr, s, hs, hfire⟩
        · exact Or.inl h0
        · obtain ⟨r', hr', _, hneg⟩ := D i hi
          rw [hr] at hr'
          simp only [Option.some.injEq] at hr'
          subst hr'
          refine Or.inr ⟨S, List.mem_cons_self, i, hi, r, hr, s, hs,
            ruleFiresS_transfer ?_ ?_ hfire⟩
          · intro _ _ g _ hg; exact sup1' g hg
          · intro a ha g hag hg
            have hpred : g.1 = a.pred := applyAtom_pred hag
            have hg1 : g ∈ db₁ := back1 g hg (by rw [hpred]; exact (hneg a ha).2)
            rcases A g hg1 with h0 | hp
            · exact h0
            · rw [hpred] at hp; exact absurd hp (hneg a ha).1
      · exact Or.inr ⟨T, List.mem_cons_of_mem _ hT, i, hi, r, hr, s, hs, hfire⟩

/-- ⚑ **`verifyS_supported_model`** — the accepted database is a fixpoint of the immediate-consequence
operator with negation read against the database ITSELF: every fact is an EDB fact or the head of a
rule whose body holds in `db` (positives present, negatives absent), and every such head is in `db`.
This is where `stratifiedB` carries weight: reading negation against each stratum's snapshot is the
same as reading it against the final database. -/
theorem verifyS_supported_model (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyS hash st c = true) :
    ∃ db : List Fact, (∀ f, f ∈ db ↔ DerivesS st.program st.strata c.edb f) ∧
      ∀ f, f ∈ db ↔ (f ∈ c.edb ∨ ∃ r ∈ st.program,
        ∃ s ∈ substs (activeDomainS st.program c.edb) (varBoundS r), ruleFiresS r s db db = some f) := by
  have hst := (verifyS_sound hash st c h).1
  unfold verifyS at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, _⟩, hnd⟩, hrest⟩ := h
  cases hrun : runStrata st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    obtain ⟨_, hm⟩ := runStrata_sound _ _ _ _ hnd hrun
    have hsuf : suffixOkB st.program st.strata = true := by
      unfold stratifiedB at hst
      simp only [Bool.and_eq_true] at hst
      exact hst.1.1
    obtain ⟨_, I2, I3⟩ := runStrata_supported_model _ _ _ _ hsuf hrun
    refine ⟨db, hm, fun f => ⟨?_, ?_⟩⟩
    · intro hf
      rcases I3 f hf with h0 | ⟨_, _, i, _, r, hr, s, hs, hfire⟩
      · exact Or.inl h0
      · exact Or.inr ⟨r, List.mem_of_getElem? hr, s, hs, hfire⟩
    · rintro (h0 | ⟨r, hr, s, hs, hfire⟩)
      · exact runStrata_superset _ _ _ _ hrun f h0
      · obtain ⟨i, hi, T, hT, hiT⟩ := stratifiedB_cover hst hr
        exact I2 T hT i hiT r hi s hs f hfire

/-! ## §7 — Non-vacuity and falsifiers: revocation. -/

namespace Reference

open Dregg2.Datalog.FixpointCert.Reference (hash0)

def ISSUED : Nat := 0
def REVOKED : Nat := 1
def ACTIVE : Nat := 2
def EVENT : Nat := 3

/-- `active(X) :- issued(X), ¬revoked(X)`. -/
def rActive : SRule :=
  { head := ⟨ACTIVE, [.var 0]⟩, body := [.pos ⟨ISSUED, [.var 0]⟩, .neg ⟨REVOKED, [.var 0]⟩] }

def revProg : SProgram := [rActive]
def revStrata : Strata := [[0]]
def revEdb : List Fact := [(ISSUED, [1]), (ISSUED, [2]), (REVOKED, [2])]

def revStmt (n : Nat) : SStatement :=
  { program := revProg, strata := revStrata, root := mroot hash0 (flatten revEdb), pred := ACTIVE,
    count := n }

def revHonest : List Trace := [{ rounds := [[⟨0, [1]⟩]] }]

-- ⚑ (a) THE HONEST CERTIFICATE VERIFIES at count 1 (active(1); active(2) is revoked).
#guard stratifiedB revProg revStrata = true
#guard verifyS hash0 (revStmt 1) ⟨revEdb, revHonest⟩ = true
#guard verifyS hash0 (revStmt 0) ⟨revEdb, revHonest⟩ = false
#guard verifyS hash0 (revStmt 2) ⟨revEdb, revHonest⟩ = false

-- ⚑ (b) FORGED ABSENCE: firing `active(2)` although `revoked(2)` is present.
def revForged : List Trace := [{ rounds := [[⟨0, [1]⟩, ⟨0, [2]⟩]] }]
#guard replayS revProg (activeDomainS revProg revEdb) [0] revEdb revEdb [[⟨0, [1]⟩, ⟨0, [2]⟩]] = none
#guard verifyS hash0 (revStmt 2) ⟨revEdb, revForged⟩ = false
-- The WEAKER checker: `FixpointCert.verify` on the positive projection (negation dropped) ACCEPTS it.
def posProj (P : SProgram) : Program :=
  P.map fun r => { head := r.head, body := r.body.filterMap fun l =>
    match l with
    | .pos a => some a
    | .neg _ => none }
def revPosStmt : Statement :=
  { program := posProj revProg, root := mroot hash0 (flatten revEdb), pred := ACTIVE, count := 2 }
#guard verify hash0 revPosStmt ⟨revEdb, { rounds := [[⟨0, [1]⟩, ⟨0, [2]⟩]] }⟩ = true

-- ⚑ (c) REVOCATION DERIVABLE LATER (codex round 3, finding 18). EDB `issued(1), flagged(1)`;
-- stratum 0: `revoked(X) :- flagged(X)`; stratum 1: `active(X) :- issued(X), ¬revoked(X)`.
-- The model has `revoked(1)` and NO `active`: the honest count is 0 (the Count = 0 shape).
def FLAGGED : Nat := 3
/-- `revoked(X) :- flagged(X)`. -/
def rRevoked : SRule := { head := ⟨REVOKED, [.var 0]⟩, body := [.pos ⟨FLAGGED, [.var 0]⟩] }
def evProg : SProgram := [rRevoked, rActive]
def evStrata : Strata := [[0], [1]]
def evEdb : List Fact := [(ISSUED, [1]), (FLAGGED, [1])]
def evStmt (n : Nat) : SStatement :=
  { program := evProg, strata := evStrata, root := mroot hash0 (flatten evEdb), pred := ACTIVE,
    count := n }
def evHonest : List Trace := [{ rounds := [[⟨0, [1]⟩]] }, { rounds := [] }]
/-- The forged schedule: fire `active(1)` FIRST, then `revoked(1)`. -/
def evForged : List Trace := [{ rounds := [[⟨1, [1]⟩], [⟨0, [1]⟩]] }, { rounds := [] }]
/-- The open lower stratum: stratum 0 never fires `revoked(1)`; stratum 1 fires `active(1)`. -/
def evOpen : List Trace := [{ rounds := [] }, { rounds := [[⟨1, [1]⟩]] }]

#guard stratifiedB evProg evStrata = true

/-- WEAKER CHECKER 1: negation read against the CURRENT database, no closure barrier between strata:
all traces' firings in one schedule (any rule), closure once at the end over every rule. -/
def applyFiringsCur (P : SProgram) (dom : List ℤ) : List Fact → List Firing → Option (List Fact)
  | db, [] => some db
  | db, fr :: rest =>
    match P[fr.rule]? with
    | none => none
    | some r =>
      if substOk dom r.toRule fr.subst then
        match ruleFiresS r fr.subst db db with
        | none => none
        | some hd => applyFiringsCur P dom (addFact db hd) rest
      else none

def verifyCurrentDbNegation (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  let dom := activeDomainS st.program c.edb
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match applyFiringsCur st.program dom c.edb (c.traces.flatMap fun t => t.rounds.flatten) with
  | none => false
  | some db => closedS st.program dom (List.range st.program.length) db db &&
      (countQ db st.pred == st.count)

/-- WEAKER CHECKER 2: the strata run, closure checked at the TOP stratum only. -/
def runTopClosure (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact →
    Option (List Fact)
  | [], [], db => some db
  | S :: rest, t :: ts, db =>
    match replayS P dom S db db t.rounds with
    | none => none
    | some db₁ =>
      if rest.isEmpty && !closedS P dom S db db₁ then none else runTopClosure P dom rest ts db₁
  | _, _, _ => none

def verifyNoLowerClosure (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match runTopClosure st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

-- The three codex-demanded rows: same EDB, root, program, stratification.
#guard verifyCurrentDbNegation hash0 (evStmt 1) ⟨evEdb, evForged⟩ = true
#guard verifyS hash0 (evStmt 1) ⟨evEdb, evForged⟩ = false
#guard verifyS hash0 (evStmt 0) ⟨evEdb, evHonest⟩ = true
-- The forged schedule's database really contains `revoked(1)` AND `active(1)` (closure passed).
#guard applyFiringsCur evProg (activeDomainS evProg evEdb) evEdb [⟨1, [1]⟩, ⟨0, [1]⟩]
  = some [(ISSUED, [1]), (FLAGGED, [1]), (ACTIVE, [1]), (REVOKED, [1])]
-- The open lower stratum: accepted by the top-closure-only checker at count 1, refused by `verifyS`.
#guard verifyNoLowerClosure hash0 (evStmt 1) ⟨evEdb, evOpen⟩ = true
#guard verifyS hash0 (evStmt 1) ⟨evEdb, evOpen⟩ = false
#guard verifyS hash0 (evStmt 0) ⟨evEdb, evOpen⟩ = false
-- Both weaker checkers accept the honest certificate (weaker, not different).
#guard verifyCurrentDbNegation hash0 (evStmt 0) ⟨evEdb, evHonest⟩ = true
#guard verifyNoLowerClosure hash0 (evStmt 0) ⟨evEdb, evHonest⟩ = true

-- ⚑ (d) NOT STRATIFIED: `p(X) :- q(X), ¬p(X)`.
def NP : Nat := 4
def NQ : Nat := 5
def nsProg : SProgram :=
  [{ head := ⟨NP, [.var 0]⟩, body := [.pos ⟨NQ, [.var 0]⟩, .neg ⟨NP, [.var 0]⟩] }]
def nsEdb : List Fact := [(NQ, [1])]
def nsStmt : SStatement :=
  { program := nsProg, strata := [[0]], root := mroot hash0 (flatten nsEdb), pred := NP, count := 1 }
def nsTrace : List Trace := [{ rounds := [[⟨0, [1]⟩]] }]

def verifyNoStratCheck (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  (mroot hash (flatten c.edb) == st.root) && decide c.edb.Nodup &&
  match runStrata st.program (activeDomainS st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

/-- Supportedness under the standard reading (negation against the database itself). -/
def supportedB (P : SProgram) (dom : List ℤ) (edb db : List Fact) : Bool :=
  db.all fun f => decide (f ∈ edb) ||
    P.any fun r => (substs dom (varBoundS r)).any fun s => decide (ruleFiresS r s db db = some f)

#guard stratifiedB nsProg [[0]] = false
#guard verifyNoStratCheck hash0 nsStmt ⟨nsEdb, nsTrace⟩ = true
#guard verifyS hash0 nsStmt ⟨nsEdb, nsTrace⟩ = false
-- … and what it accepted is not a supported model: `p(1)`'s only support is `¬p(1)`.
#guard (runStrata nsProg (activeDomainS nsProg nsEdb) [[0]] nsTrace nsEdb)
  = some [(NQ, [1]), (NP, [1])]
#guard supportedB nsProg (activeDomainS nsProg nsEdb) nsEdb [(NQ, [1]), (NP, [1])] = false
-- The honest revocation database IS supported (the `verifyS_supported_model` shape, evaluated).
#guard supportedB revProg (activeDomainS revProg revEdb) revEdb
  ((runStrata revProg (activeDomainS revProg revEdb) revStrata revHonest revEdb).getD []) = true

-- Closure enumeration sizes, for the counts table.
#guard (activeDomainS evProg evEdb).length == 2
#guard (substs (activeDomainS evProg evEdb) (varBoundS rActive)).length == 2

/-- (c), kernel-checked: the current-database-negation checker ACCEPTS the forged schedule. -/
theorem forged_accepted_by_currentDb :
    verifyCurrentDbNegation hash0 (evStmt 1) ⟨evEdb, evForged⟩ = true := by decide
/-- (c), kernel-checked: `verifyS` REFUSES the same certificate. -/
theorem forged_refused_by_verifyS : verifyS hash0 (evStmt 1) ⟨evEdb, evForged⟩ = false := by decide
/-- (c), kernel-checked: the honest certificate verifies at count 0. -/
theorem honest_count0_verifies : verifyS hash0 (evStmt 0) ⟨evEdb, evHonest⟩ = true := by decide

/-- Non-vacuity of the SEMANTICS: `active(1)` is in the stratified model, as a term. -/
theorem active1_derivesS : DerivesS revProg revStrata revEdb (ACTIVE, [1]) := by
  show DerivesAt revProg (activeDomainS revProg revEdb) [0] (· ∈ revEdb) (ACTIVE, [1])
  refine DerivesAt.fire (i := 0) (r := rActive) (s := [1]) (by simp) rfl (by decide) ?_ ?_ ?_
    (by decide)
  · intro a ha
    simp only [rActive, List.mem_cons, Lit.pos.injEq, List.not_mem_nil, or_false,
      reduceCtorEq] at ha
    subst ha; decide
  · intro a ha f hf
    simp only [rActive, List.mem_cons, Lit.pos.injEq, List.not_mem_nil, or_false,
      reduceCtorEq] at ha
    subst ha
    have h' : applyAtom [1] (⟨ISSUED, [.var 0]⟩ : Atom) = some (ISSUED, [1]) := by decide
    rw [h'] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    exact DerivesAt.base (by decide)
  · intro a ha
    simp only [rActive, List.mem_cons, Lit.neg.injEq, List.not_mem_nil, or_false,
      reduceCtorEq, false_or] at ha
    subst ha
    exact ⟨(REVOKED, [1]), by decide, by decide⟩

/-- Non-vacuity of the ABSENCE leg: `active(2)` is NOT in the stratified model, as a term. -/
theorem active2_not_derivesS : ¬ DerivesS revProg revStrata revEdb (ACTIVE, [2]) := by
  intro h
  change DerivesAt revProg (activeDomainS revProg revEdb) [0] (· ∈ revEdb) (ACTIVE, [2]) at h
  cases h with
  | base hb => exact absurd hb (by decide)
  | @fire i r s _ hi hr hs _ _ hneg hhead =>
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [revProg, List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    obtain ⟨hl, _⟩ := (mem_substs_iff _ _ _).mp hs
    match s, hl with
    | [x], _ =>
      have hx : x = 2 := by
        simpa [applyAtom, applyTerm, rActive] using hhead
      subst hx
      obtain ⟨f, hf, hnot⟩ := hneg ⟨REVOKED, [.var 0]⟩ (by simp [rActive])
      have h' : applyAtom [2] (⟨REVOKED, [.var 0]⟩ : Atom) = some (REVOKED, [2]) := by decide
      rw [h'] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      exact hnot (by decide)

end Reference

/-! ## §8 — axiom tripwires. -/

#assert_all_clean [applyAtom_pred, litHolds_pos, litHolds_neg, bodyHoldsS_iff, ruleFiresS_some,
  ruleFiresS_of, ruleFiresS_transfer, mem_headPreds, stratumOkB_spec, stratifiedB_cover,
  applyFiringS_some, applyFiringsS_induct, replayS_superset, replayS_nodup, closedS_iff,
  runStrata_cons, stratified_replay_sound, stratified_closed_complete, runStrata_sound,
  verifyS_sound, countS_unique_or_collides, replayS_preds, replayS_supported, runStrata_superset,
  runStrata_supported_model, verifyS_supported_model, runStrata_dbs, verifyS_strata_exact,
  verifyS_intended_or_collides, Reference.forged_accepted_by_currentDb,
  Reference.forged_refused_by_verifyS, Reference.honest_count0_verifies, Reference.active1_derivesS,
  Reference.active2_not_derivesS]

end Dregg2.Datalog.StratifiedCert
