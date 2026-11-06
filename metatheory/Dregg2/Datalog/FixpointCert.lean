/-
# Dregg2.Datalog.FixpointCert — positive-Datalog least-fixpoint certificates over an MMR-committed EDB,
with an exact Count (Part D of `docs/automata/AUTOMATA-ARITHMETIZATION-PROGRAM.md`, 2026-11-05).

## The object

A **statement** is `(program, root, pred, count)`: a positive Datalog program `P`, the MMR root of
the extensional database (the committed facts), a predicate symbol, and a claimed number of
derivable facts of that predicate. A **certificate** is the EDB itself plus a **semi-naive trace**:
rounds of rule firings `(rule index, substitution)`. The verifier `verify hash st cert`:

  1. recomputes the MMR root of the length-prefixed flattening of the EDB (`flatten`, injective —
     `flatten_injective`), against `st.root`;
  2. replays the trace against the program: each firing must have every instantiated body atom
     already in the database, and its substitution must range over the ACTIVE DOMAIN (the
     constants of the EDB and of the program) with exactly the rule's variable count;
  3. checks the final database is CLOSED: for every rule and every active-domain substitution,
     if the body holds then the head is already present (`closedB`, an executable enumeration);
  4. compares `countQ db st.pred` with `st.count`.

## What is proved (kernel-clean, §6)

  * `replay_sound`: every fact of a replayed database is derivable (`Derives`, the inductive
    least-fixpoint semantics with active-domain substitutions — the finite Herbrand semantics of
    Datalog; for safe programs it coincides with the unrestricted one:
    `SafeCoincidence.derives_iff_unrestricted`).
  * `closed_complete`: a closed replayed database contains EVERY derivable fact.
  * `verify_sound`: an accepted certificate yields a duplicate-free database that is EXACTLY the
    set of derivable facts, whose `pred`-count is the claimed count, and whose EDB flattens to the
    committed root.
  * `edb_bound_or_collides`: two accepted certificates for the same root have the same EDB, or
    the sponge collides at the pair `mrootFind` names (`MMR.mroot_binds_or_collides`, floor-free).
  * `count_unique_or_collides`: two accepted certificates for the same `(program, root, pred)`
    claim the SAME count, or that named collision. This is the exact-Count statement: Count is a
    function of the committed EDB and the program, not of the prover.

## Non-vacuity and falsifiers (§6; `#guard`s are COMPILED evaluation of closed `Bool`s, not kernel
proofs — the `Prop`-level content is §4-§5; `path14_derives` is the one kernel-checked instance)

  * Transitive closure over four nodes: `path(X,Y) :- edge(X,Y)`; `path(X,Z) :- edge(X,Y), path(Y,Z)`;
    EDB `edge(1,2), edge(2,3), edge(3,4)`. The honest trace (three rounds, 3 + 2 + 1 firings)
    verifies with `count path = 6`.
  * The OPEN trace (two rounds) is REFUSED: the database is not closed (`path(1,4)` missing).
  * The same open trace with the matching smaller count `5` is STILL refused: closure, not the
    count, is the gate — so "count the facts you bothered to derive" is not a certificate.
  * A firing whose body does not hold (`path(1,2) :- edge(2,3)` with the wrong substitution) makes
    `replay` return `none`.
  * A firing whose substitution leaves the active domain is refused (`substOk`) — isolated on an
    UNSAFE rule `p(X) :- q()` whose body holds regardless of `X`, so nothing but the domain check
    refuses it (codex round 2 §1d).
  * `verifyNoClosure` (replay + count, closure forgotten) ACCEPTS the open trace at its own count
    5 while `verify` refuses it: the weaker checker's acceptance is exhibited, not only the strong
    checker's refusal (codex round 2 §1d).

## Scope, stated (codex round 2)
  * `Derives` is the ACTIVE-DOMAIN fixpoint. For safe programs it coincides with the standard one
    (`SafeCoincidence.derives_iff_unrestricted`, `verify_sound_unrestricted`); for an unsafe `p(X) :- q()` with EDB `{q()}` the active domain is empty and
    this semantics derives NO `p`-fact where unrestricted semantics derives every `p(z)`. Count is
    exact for THIS semantics.
  * `countQ` counts by predicate symbol, not by `(pred, arity)`; `{p(), p(7)}` counts 2.
  * `count_unique_or_collides` needs identical RULE LISTS (order included); invariance under
    reordering is a separate theorem.
  * `flatten` is injective over `ℤ`; a deployed hash that reduces leaves modulo the field prime
    aliases `e(0)` and `e(p)`. The deployed leaf encoding must be canonical bounded felts (or a
    signed-limb serialization); `Reference.hash0` is a toy with exactly that alias.

## Costs (counts, not clocks) — the L2 rung

Per firing: `|body|` membership tests against the current database and one `addFact`; per round,
`|firings|`; closure: `|P| · |dom|^{vars}` body evaluations once. The arithmetization (L3, not
here) is `DerivationEmit`'s single-firing AIR (386 columns, 393 constraints, 13 PIs [MEASURED])
iterated once per firing under a fold, plus one lookup per body atom into the running fact table;
closure is the expensive leg and is where the alternating/product constructions of the program
doc §3 do not help — it is a universal statement over the active domain, i.e. `|dom|^{vars}`
lookups, and is the honest price of "Count is exact" as opposed to "at least count".

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
read-only. -/
import Dregg2.Lightclient.MMR
import Dregg2.Tactics

namespace Dregg2.Datalog.FixpointCert

open Dregg2.Lightclient.MMR (mroot MRootColl mroot_binds_or_collides)

set_option autoImplicit false

/-! ## §1 — Syntax. -/

/-- A term: a variable (by index) or an integer constant. -/
inductive Term where
  | var (i : Nat)
  | const (c : ℤ)
  deriving Repr, DecidableEq

/-- An atom: a predicate symbol applied to terms. -/
structure Atom where
  pred : Nat
  args : List Term
  deriving Repr, DecidableEq

/-- A rule `head :- body`. -/
structure Rule where
  head : Atom
  body : List Atom
  deriving Repr, DecidableEq

/-- A ground fact. -/
abbrev Fact := Nat × List ℤ
/-- A positive Datalog program. -/
abbrev Program := List Rule
/-- A substitution: variable `i` ↦ `s[i]`. -/
abbrev Subst := List ℤ

def applyTerm (s : Subst) : Term → Option ℤ
  | .var i => s[i]?
  | .const c => some c

/-- Instantiate an atom; `none` if a variable is unbound. -/
def applyAtom (s : Subst) (a : Atom) : Option Fact :=
  (a.args.mapM (applyTerm s)).map fun vs => (a.pred, vs)

/-- The variables of an atom / rule, and the rule's variable count (one past the largest index). -/
def atomVars (a : Atom) : List Nat :=
  a.args.filterMap fun t => match t with | .var i => some i | .const _ => none

def ruleVars (r : Rule) : List Nat := (r.head :: r.body).flatMap atomVars

def varBound (r : Rule) : Nat := (ruleVars r).foldl (fun m i => max m (i + 1)) 0

/-- The constants of a rule. -/
def ruleConsts (r : Rule) : List ℤ :=
  (r.head :: r.body).flatMap fun a =>
    a.args.filterMap fun t => match t with | .const c => some c | .var _ => none

/-- **The active domain**: the constants of the EDB and of the program. -/
def activeDomain (P : Program) (edb : List Fact) : List ℤ :=
  edb.flatMap (·.2) ++ P.flatMap ruleConsts

/-- All substitutions of length `n` over `dom`. -/
def substs (dom : List ℤ) : Nat → List Subst
  | 0 => [[]]
  | n + 1 => dom.flatMap fun c => (substs dom n).map fun s => c :: s

theorem mem_substs_iff (dom : List ℤ) : ∀ (n : Nat) (s : Subst),
    s ∈ substs dom n ↔ s.length = n ∧ ∀ x ∈ s, x ∈ dom := by
  intro n
  induction n with
  | zero =>
    intro s
    simp only [substs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨hl, _⟩; exact List.eq_nil_of_length_eq_zero hl
  | succ k ih =>
    intro s
    simp only [substs, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨c, hc, s', hs', rfl⟩
      obtain ⟨hl, hd⟩ := (ih s').mp hs'
      refine ⟨by simp [hl], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hc
      · exact hd x hx
    · rintro ⟨hl, hd⟩
      cases s with
      | nil => simp at hl
      | cons c s' =>
        refine ⟨c, hd c (List.mem_cons_self), s', ?_, rfl⟩
        exact (ih s').mpr ⟨by simpa using hl, fun x hx => hd x (List.mem_cons_of_mem _ hx)⟩

/-! ## §2 — Semantics: the active-domain least fixpoint, as an inductive. -/

/-- **`Derives P edb f`** — `f` is in the least fixpoint of `P` over `edb`, with rule substitutions
ranging over the active domain (the finite Herbrand semantics). -/
inductive Derives (P : Program) (edb : List Fact) : Fact → Prop
  | edb {f : Fact} : f ∈ edb → Derives P edb f
  | fire {r : Rule} {s : Subst} {h : Fact} :
      r ∈ P → s ∈ substs (activeDomain P edb) (varBound r) →
      (∀ b ∈ r.body, (applyAtom s b).isSome = true) →
      (∀ b ∈ r.body, ∀ f, applyAtom s b = some f → Derives P edb f) →
      applyAtom s r.head = some h → Derives P edb h

/-! ## §3 — The executable checker. -/

/-- One body atom holds under `s` against `db`. -/
def atomHolds (s : Subst) (db : List Fact) (b : Atom) : Bool :=
  match applyAtom s b with
  | some f => decide (f ∈ db)
  | none => false

theorem atomHolds_iff (s : Subst) (db : List Fact) (b : Atom) :
    atomHolds s db b = true ↔ ∃ f, applyAtom s b = some f ∧ f ∈ db := by
  unfold atomHolds
  cases h : applyAtom s b with
  | none => simp
  | some f => simp

/-- The whole body holds. -/
def bodyHolds (s : Subst) (db : List Fact) (r : Rule) : Bool := r.body.all (atomHolds s db)

theorem bodyHolds_iff (s : Subst) (db : List Fact) (r : Rule) :
    bodyHolds s db r = true ↔ ∀ b ∈ r.body, ∃ f, applyAtom s b = some f ∧ f ∈ db := by
  unfold bodyHolds
  rw [List.all_eq_true]
  constructor
  · intro h b hb; exact (atomHolds_iff s db b).mp (h b hb)
  · intro h b hb; exact (atomHolds_iff s db b).mpr (h b hb)

/-- The substitution is admissible for `r` over `dom`. -/
def substOk (dom : List ℤ) (r : Rule) (s : Subst) : Bool :=
  s.length == varBound r && s.all (fun x => decide (x ∈ dom))

theorem substOk_iff (dom : List ℤ) (r : Rule) (s : Subst) :
    substOk dom r s = true ↔ s ∈ substs dom (varBound r) := by
  rw [mem_substs_iff]
  unfold substOk
  simp [List.all_eq_true]

/-- `ruleFires r s db = some h`: the body holds and the head instantiates to `h`. -/
def ruleFires (r : Rule) (s : Subst) (db : List Fact) : Option Fact :=
  if bodyHolds s db r then applyAtom s r.head else none

theorem ruleFires_some {r : Rule} {s : Subst} {db : List Fact} {h : Fact}
    (hf : ruleFires r s db = some h) :
    bodyHolds s db r = true ∧ applyAtom s r.head = some h := by
  unfold ruleFires at hf
  by_cases hb : bodyHolds s db r = true
  · rw [if_pos hb] at hf; exact ⟨hb, hf⟩
  · rw [if_neg hb] at hf; exact absurd hf (by simp)

/-- Add a fact if absent (keeps the database duplicate-free). -/
def addFact (db : List Fact) (f : Fact) : List Fact := if f ∈ db then db else db ++ [f]

theorem mem_addFact {db : List Fact} {f g : Fact} (h : g ∈ addFact db f) : g ∈ db ∨ g = f := by
  unfold addFact at h
  by_cases hf : f ∈ db
  · rw [if_pos hf] at h; exact Or.inl h
  · rw [if_neg hf] at h
    simp only [List.mem_append, List.mem_singleton] at h
    exact h

theorem subset_addFact (db : List Fact) (f : Fact) : ∀ g ∈ db, g ∈ addFact db f := by
  intro g hg
  unfold addFact
  by_cases hf : f ∈ db
  · rw [if_pos hf]; exact hg
  · rw [if_neg hf]; exact List.mem_append_left _ hg

theorem mem_addFact_self (db : List Fact) (f : Fact) : f ∈ addFact db f := by
  unfold addFact
  by_cases hf : f ∈ db
  · rw [if_pos hf]; exact hf
  · rw [if_neg hf]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem nodup_addFact {db : List Fact} (hn : db.Nodup) (f : Fact) : (addFact db f).Nodup := by
  unfold addFact
  by_cases hf : f ∈ db
  · rw [if_pos hf]; exact hn
  · rw [if_neg hf]
    refine List.nodup_append.mpr ⟨hn, List.nodup_singleton f, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    intro h
    exact hf (h ▸ ha)

/-- A firing: which rule, with which substitution. -/
structure Firing where
  rule : Nat
  subst : Subst
  deriving Repr

/-- A semi-naive round: a list of firings. -/
abbrev Round := List Firing

/-- The certificate's trace. -/
structure Trace where
  rounds : List Round
  deriving Repr

/-- Apply one firing: the rule must exist, its substitution must be admissible, and it must fire. -/
def applyFiring (P : Program) (dom : List ℤ) (db : List Fact) (fr : Firing) : Option (List Fact) :=
  match P[fr.rule]? with
  | none => none
  | some r =>
    if substOk dom r fr.subst then (ruleFires r fr.subst db).map (addFact db) else none

/-- What an accepted firing IS: an existing rule, an admissible substitution, a genuine fire. -/
theorem applyFiring_some {P : Program} {dom : List ℤ} {db db' : List Fact} {fr : Firing}
    (h : applyFiring P dom db fr = some db') :
    ∃ r hd, P[fr.rule]? = some r ∧ substOk dom r fr.subst = true
      ∧ ruleFires r fr.subst db = some hd ∧ db' = addFact db hd := by
  unfold applyFiring at h
  cases hr : P[fr.rule]? with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h
    by_cases hok : substOk dom r fr.subst = true
    · rw [if_pos hok] at h
      obtain ⟨hd, hf, hdb⟩ := Option.map_eq_some_iff.mp h
      exact ⟨r, hd, rfl, hok, hf, hdb.symm⟩
    · rw [if_neg hok] at h
      exact absurd h (by simp)

def applyRound (P : Program) (dom : List ℤ) (db : List Fact) : Round → Option (List Fact)
  | [] => some db
  | fr :: rest => (applyFiring P dom db fr).bind fun db' => applyRound P dom db' rest

def replay (P : Program) (dom : List ℤ) (db : List Fact) : List Round → Option (List Fact)
  | [] => some db
  | rd :: rest => (applyRound P dom db rd).bind fun db' => replay P dom db' rest

/-- **Closure**: for every rule and every active-domain substitution, if the body holds then the
head is already present. Executable: enumerates `substs dom (varBound r)`. -/
def closedB (P : Program) (dom : List ℤ) (db : List Fact) : Bool :=
  P.all fun r => (substs dom (varBound r)).all fun s =>
    match ruleFires r s db with
    | some h => decide (h ∈ db)
    | none => true

theorem closedB_iff (P : Program) (dom : List ℤ) (db : List Fact) :
    closedB P dom db = true ↔
      ∀ r ∈ P, ∀ s ∈ substs dom (varBound r), ∀ h, ruleFires r s db = some h → h ∈ db := by
  unfold closedB
  simp only [List.all_eq_true]
  constructor
  · intro H r hr s hs h hf
    have := H r hr s hs
    rw [hf] at this
    simpa using this
  · intro H r hr s hs
    cases hf : ruleFires r s db with
    | none => rfl
    | some h => simpa using H r hr s hs h hf

/-- The Count query: the number of facts of predicate `p`. -/
def countQ (db : List Fact) (p : Nat) : Nat := (db.filter fun f => f.1 == p).length

/-! ## §4 — Soundness and completeness of the checker. -/

/-- Invariant: every fact of `db` is derivable. -/
def AllDerivable (P : Program) (edb db : List Fact) : Prop := ∀ f ∈ db, Derives P edb f

theorem applyFiring_sound {P : Program} {edb db db' : List Fact} {fr : Firing}
    (hinv : AllDerivable P edb db)
    (h : applyFiring P (activeDomain P edb) db fr = some db') : AllDerivable P edb db' := by
  obtain ⟨r, hd, hr, hok, hf, rfl⟩ := applyFiring_some h
  intro g hg
  rcases mem_addFact hg with hg | rfl
  · exact hinv g hg
  · obtain ⟨hb, hh⟩ := ruleFires_some hf
    have hbody := (bodyHolds_iff _ _ _).mp hb
    refine Derives.fire (List.mem_of_getElem? hr) ((substOk_iff _ _ _).mp hok) ?_ ?_ hh
    · intro b hb'
      obtain ⟨f, hf', _⟩ := hbody b hb'
      rw [hf']; rfl
    · intro b hb' f hf'
      obtain ⟨f', hf'', hfdb⟩ := hbody b hb'
      rw [hf'] at hf''
      simp only [Option.some.injEq] at hf''
      subst hf''
      exact hinv f hfdb

theorem applyRound_sound {P : Program} {edb : List Fact} :
    ∀ (rd : Round) (db db' : List Fact), AllDerivable P edb db →
      applyRound P (activeDomain P edb) db rd = some db' → AllDerivable P edb db'
  | [], db, db', hinv, h => by
    simp only [applyRound, Option.some.injEq] at h; subst h; exact hinv
  | fr :: rest, db, db', hinv, h => by
    simp only [applyRound, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact applyRound_sound rest db₁ db' (applyFiring_sound hinv h₁) h₂

theorem replay_sound' {P : Program} {edb : List Fact} :
    ∀ (rds : List Round) (db db' : List Fact), AllDerivable P edb db →
      replay P (activeDomain P edb) db rds = some db' → AllDerivable P edb db'
  | [], db, db', hinv, h => by
    simp only [replay, Option.some.injEq] at h; subst h; exact hinv
  | rd :: rest, db, db', hinv, h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact replay_sound' rest db₁ db' (applyRound_sound rd db db₁ hinv h₁) h₂

/-- ⚑ **`replay_sound`** — every fact of a replayed database is derivable. -/
theorem replay_sound {P : Program} {edb db : List Fact} {rds : List Round}
    (h : replay P (activeDomain P edb) edb rds = some db) : ∀ f ∈ db, Derives P edb f :=
  replay_sound' rds edb db (fun _ hf => Derives.edb hf) h

/-- Replay only grows the database. -/
theorem applyFiring_superset {P : Program} {dom : List ℤ} {db db' : List Fact} {fr : Firing}
    (h : applyFiring P dom db fr = some db') : ∀ g ∈ db, g ∈ db' := by
  obtain ⟨r, hd, _, _, _, rfl⟩ := applyFiring_some h
  exact subset_addFact db hd

theorem applyRound_superset {P : Program} {dom : List ℤ} :
    ∀ (rd : Round) (db db' : List Fact), applyRound P dom db rd = some db' → ∀ g ∈ db, g ∈ db'
  | [], db, db', h => by
    simp only [applyRound, Option.some.injEq] at h; subst h; exact fun _ hg => hg
  | fr :: rest, db, db', h => by
    simp only [applyRound, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact fun g hg => applyRound_superset rest db₁ db' h₂ g (applyFiring_superset h₁ g hg)

theorem replay_superset {P : Program} {dom : List ℤ} :
    ∀ (rds : List Round) (db db' : List Fact), replay P dom db rds = some db' → ∀ g ∈ db, g ∈ db'
  | [], db, db', h => by
    simp only [replay, Option.some.injEq] at h; subst h; exact fun _ hg => hg
  | rd :: rest, db, db', h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact fun g hg => replay_superset rest db₁ db' h₂ g (applyRound_superset rd db db₁ h₁ g hg)

/-- Replay preserves duplicate-freeness. -/
theorem applyFiring_nodup {P : Program} {dom : List ℤ} {db db' : List Fact} {fr : Firing}
    (hn : db.Nodup) (h : applyFiring P dom db fr = some db') : db'.Nodup := by
  obtain ⟨r, hd, _, _, _, rfl⟩ := applyFiring_some h
  exact nodup_addFact hn hd

theorem applyRound_nodup {P : Program} {dom : List ℤ} :
    ∀ (rd : Round) (db db' : List Fact), db.Nodup → applyRound P dom db rd = some db' → db'.Nodup
  | [], db, db', hn, h => by
    simp only [applyRound, Option.some.injEq] at h; subst h; exact hn
  | fr :: rest, db, db', hn, h => by
    simp only [applyRound, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact applyRound_nodup rest db₁ db' (applyFiring_nodup hn h₁) h₂

theorem replay_nodup {P : Program} {dom : List ℤ} :
    ∀ (rds : List Round) (db db' : List Fact), db.Nodup → replay P dom db rds = some db' → db'.Nodup
  | [], db, db', hn, h => by
    simp only [replay, Option.some.injEq] at h; subst h; exact hn
  | rd :: rest, db, db', hn, h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨db₁, h₁, h₂⟩ := h
    exact replay_nodup rest db₁ db' (applyRound_nodup rd db db₁ hn h₁) h₂

/-- ⚑ **`closed_complete`** — a CLOSED database containing the EDB contains every derivable fact. -/
theorem closed_complete {P : Program} {edb db : List Fact}
    (hcl : closedB P (activeDomain P edb) db = true) (hedb : ∀ f ∈ edb, f ∈ db) :
    ∀ f, Derives P edb f → f ∈ db := by
  intro f hf
  induction hf with
  | edb h => exact hedb _ h
  | fire hr hs hsome hbody hhead ih =>
    rename_i r s h
    have hb : bodyHolds s db r = true := by
      rw [bodyHolds_iff]
      intro b hb'
      obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.mp (hsome b hb')
      exact ⟨f', hf', ih b hb' f' hf'⟩
    have hfire : ruleFires r s db = some h := by
      unfold ruleFires; rw [if_pos hb]; exact hhead
    exact (closedB_iff _ _ _).mp hcl r hr s hs h hfire

/-! ## §5 — The committed statement and the verifier. -/

/-- Length-prefixed flattening of the EDB: `pred, arity, args…` per fact. Injective. -/
def flatten (edb : List Fact) : List ℤ :=
  edb.flatMap fun f => ((f.1 : ℤ) :: (f.2.length : ℤ) :: f.2)

theorem flatten_injective : ∀ (e₁ e₂ : List Fact), flatten e₁ = flatten e₂ → e₁ = e₂
  | [], [], _ => rfl
  | [], (f :: _), h => by simp [flatten] at h
  | (f :: _), [], h => by simp [flatten] at h
  | (f₁ :: r₁), (f₂ :: r₂), h => by
    simp only [flatten, List.flatMap_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨hp, hl, hrest⟩ := h
    have hp' : f₁.1 = f₂.1 := by exact_mod_cast hp
    have hl' : f₁.2.length = f₂.2.length := by exact_mod_cast hl
    obtain ⟨ha, hr⟩ := List.append_inj hrest hl'
    have hf : f₁ = f₂ := Prod.ext hp' ha
    have := flatten_injective r₁ r₂ (by simpa [flatten] using hr)
    rw [hf, this]

/-- The statement: program, committed EDB root, the counted predicate, the claimed count. -/
structure Statement where
  program : Program
  root : ℤ
  pred : Nat
  count : Nat
  deriving Repr

/-- The certificate: the EDB and the semi-naive trace. -/
structure Certificate where
  edb : List Fact
  trace : Trace
  deriving Repr

/-- **The verifier.** -/
def verify (hash : List ℤ → ℤ) (st : Statement) (c : Certificate) : Bool :=
  let dom := activeDomain st.program c.edb
  (mroot hash (flatten c.edb) == st.root) && decide c.edb.Nodup &&
  match replay st.program dom c.edb c.trace.rounds with
  | none => false
  | some db => closedB st.program dom db && (countQ db st.pred == st.count)

/-- ⚑ **`verify_sound`** — an accepted certificate yields a duplicate-free database that is EXACTLY
the derivable facts, whose count at `pred` is the claimed count, and whose EDB flattens to the
committed root. -/
theorem verify_sound (hash : List ℤ → ℤ) (st : Statement) (c : Certificate)
    (h : verify hash st c = true) :
    mroot hash (flatten c.edb) = st.root ∧
    ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ Derives st.program c.edb f) ∧
      countQ db st.pred = st.count := by
  unfold verify at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hroot, hnd⟩, hrest⟩ := h
  refine ⟨hroot, ?_⟩
  cases hrep : replay st.program (activeDomain st.program c.edb) c.edb c.trace.rounds with
  | none => rw [hrep] at hrest; exact absurd hrest (by simp)
  | some db =>
    rw [hrep] at hrest
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨hcl, hcount⟩ := hrest
    refine ⟨db, replay_nodup _ _ _ hnd hrep, ?_, hcount⟩
    intro f
    constructor
    · exact fun hf => replay_sound hrep f hf
    · exact closed_complete hcl (replay_superset _ _ _ hrep) f

/-- ⚑ **`edb_bound_or_collides`** — two accepted certificates at one root carry the same EDB, or
the sponge collides at the pair `mrootFind` names. Floor-free (no `Poseidon2SpongeCR`). -/
theorem edb_bound_or_collides (hash : List ℤ → ℤ) (st : Statement) (c₁ c₂ : Certificate)
    (h₁ : verify hash st c₁ = true) (h₂ : verify hash st c₂ = true) :
    c₁.edb = c₂.edb ∨ MRootColl hash (flatten c₁.edb) (flatten c₂.edb) := by
  have r₁ := (verify_sound hash st c₁ h₁).1
  have r₂ := (verify_sound hash st c₂ h₂).1
  rcases mroot_binds_or_collides hash (r₁.trans r₂.symm) with heq | hc
  · exact Or.inl (flatten_injective _ _ heq)
  · exact Or.inr hc

/-- Two duplicate-free lists with the same members have the same count at every predicate. -/
theorem countQ_eq_of_same_members {db₁ db₂ : List Fact} (h₁ : db₁.Nodup) (h₂ : db₂.Nodup)
    (hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂) (p : Nat) : countQ db₁ p = countQ db₂ p := by
  have hperm : db₁.Perm db₂ := (List.perm_ext_iff_of_nodup h₁ h₂).mpr hm
  unfold countQ
  exact (hperm.filter _).length_eq

/-- ⚑ **`count_unique_or_collides`** — Count is a FUNCTION of `(program, root, pred)`: two accepted
certificates for statements that agree on those three claim the same count, or the sponge
collides at the named pair. This is "the count is exact", stated without a prover. -/
theorem count_unique_or_collides (hash : List ℤ → ℤ) (st₁ st₂ : Statement) (c₁ c₂ : Certificate)
    (hP : st₁.program = st₂.program) (hR : st₁.root = st₂.root) (hp : st₁.pred = st₂.pred)
    (h₁ : verify hash st₁ c₁ = true) (h₂ : verify hash st₂ c₂ = true) :
    st₁.count = st₂.count ∨ MRootColl hash (flatten c₁.edb) (flatten c₂.edb) := by
  obtain ⟨r₁, db₁, hn₁, hm₁, hc₁⟩ := verify_sound hash st₁ c₁ h₁
  obtain ⟨r₂, db₂, hn₂, hm₂, hc₂⟩ := verify_sound hash st₂ c₂ h₂
  rcases mroot_binds_or_collides hash (r₁.trans (hR.trans r₂.symm)) with heq | hc
  · refine Or.inl ?_
    have hedb : c₁.edb = c₂.edb := flatten_injective _ _ heq
    have hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂ := by
      intro f
      rw [hm₁, hm₂, hedb, hP]
    rw [← hc₁, ← hc₂, hp]
    exact countQ_eq_of_same_members hn₁ hn₂ hm _
  · exact Or.inr hc

/-! ## §6 — Non-vacuity and falsifiers: transitive closure over four nodes. -/

namespace Reference

/-- A concrete hash for the `#guard`s (NOT Poseidon2; the theorems are abstract in `hash`). -/
def hash0 (l : List ℤ) : ℤ := l.foldl (fun a x => (a * 1000003 + x) % 2013265921) 17

def EDGE : Nat := 0
def PATH : Nat := 1

/-- `path(X, Y) :- edge(X, Y)`. -/
def rBase : Rule :=
  { head := ⟨PATH, [.var 0, .var 1]⟩, body := [⟨EDGE, [.var 0, .var 1]⟩] }
/-- `path(X, Z) :- edge(X, Y), path(Y, Z)`. -/
def rStep : Rule :=
  { head := ⟨PATH, [.var 0, .var 2]⟩
  , body := [⟨EDGE, [.var 0, .var 1]⟩, ⟨PATH, [.var 1, .var 2]⟩] }

def tc : Program := [rBase, rStep]

def edb : List Fact := [(EDGE, [1, 2]), (EDGE, [2, 3]), (EDGE, [3, 4])]

/-- The honest semi-naive trace: three rounds. -/
def honest : Trace :=
  { rounds :=
      [ [⟨0, [1, 2]⟩, ⟨0, [2, 3]⟩, ⟨0, [3, 4]⟩]
      , [⟨1, [1, 2, 3]⟩, ⟨1, [2, 3, 4]⟩]
      , [⟨1, [1, 2, 4]⟩] ] }

/-- The OPEN trace: stops one round early (`path(1,4)` never derived). -/
def open2 : Trace := { rounds := honest.rounds.take 2 }

def stmt (n : Nat) : Statement := { program := tc, root := mroot hash0 (flatten edb), pred := PATH, count := n }

-- ⚑ THE HONEST CERTIFICATE VERIFIES, with count 6 = |{(1,2),(2,3),(3,4),(1,3),(2,4),(1,4)}|.
#guard verify hash0 (stmt 6) ⟨edb, honest⟩ = true
-- The replayed database, for the record: 3 edges + 6 paths.
#guard (replay tc (activeDomain tc edb) edb honest.rounds).map List.length = some 9
#guard (replay tc (activeDomain tc edb) edb honest.rounds).map (countQ · PATH) = some 6

-- ⚑ FALSIFIER 1: the OPEN trace is refused at the honest count …
#guard verify hash0 (stmt 6) ⟨edb, open2⟩ = false
-- … AND at the count of what it did derive: closure is the gate, not the count.
#guard (replay tc (activeDomain tc edb) edb open2.rounds).map (countQ · PATH) = some 5
#guard verify hash0 (stmt 5) ⟨edb, open2⟩ = false
#guard closedB tc (activeDomain tc edb) ((replay tc (activeDomain tc edb) edb open2.rounds).getD []) = false

-- ⚑ FALSIFIER 2: a wrong count with the honest trace is refused.
#guard verify hash0 (stmt 5) ⟨edb, honest⟩ = false
#guard verify hash0 (stmt 7) ⟨edb, honest⟩ = false

-- ⚑ FALSIFIER 3: a firing whose body does not hold (`rStep` at `[1, 3, 4]`: no `edge(1,3)`) → `none`.
#guard replay tc (activeDomain tc edb) edb [[⟨1, [1, 3, 4]⟩]] = none

-- ⚑ FALSIFIER 4: a substitution outside the active domain is refused, ISOLATED from body failure:
-- the unsafe rule `p(X) :- q()` fires for every `X` once `q()` holds, so only the domain check can
-- refuse `X := 9` (the active domain of `{q(), d(1)}` is `[1]`).
def unsafeP : Program := [{ head := ⟨2, [.var 0]⟩, body := [⟨3, []⟩] }]
def unsafeEdb : List Fact := [(3, []), (4, [1])]
#guard activeDomain unsafeP unsafeEdb = [1]
#guard replay unsafeP (activeDomain unsafeP unsafeEdb) unsafeEdb [[⟨0, [1]⟩]]
  = some [(3, []), (4, [1]), (2, [1])]
#guard replay unsafeP (activeDomain unsafeP unsafeEdb) unsafeEdb [[⟨0, [9]⟩]] = none

-- ⚑ FALSIFIER 6: the WEAKER checker that forgets closure. It accepts the open trace at the count
-- of what it derived; `verify` refuses the same certificate. Acceptance exhibited, not just refusal.
def verifyNoClosure (hash : List ℤ → ℤ) (st : Statement) (c : Certificate) : Bool :=
  let dom := activeDomain st.program c.edb
  (mroot hash (flatten c.edb) == st.root) && decide c.edb.Nodup &&
  match replay st.program dom c.edb c.trace.rounds with
  | none => false
  | some db => countQ db st.pred == st.count
#guard verifyNoClosure hash0 (stmt 5) ⟨edb, open2⟩ = true
#guard verify hash0 (stmt 5) ⟨edb, open2⟩ = false

/-- The exact-count soundness premise is inhabited by the complete three-round trace. -/
theorem honest_verifies : verify hash0 (stmt 6) ⟨edb, honest⟩ = true := by decide

/-- Removing only closure accepts an incomplete database at its own count. The strong checker
rejects the SAME statement and certificate: checking the claimed count cannot replace closure. -/
theorem open_trace_separation :
    verifyNoClosure hash0 (stmt 5) ⟨edb, open2⟩ = true ∧
    verify hash0 (stmt 5) ⟨edb, open2⟩ = false := by decide

-- ⚑ FALSIFIER 5: a wrong root is refused (the EDB is bound, not just the trace).
#guard verify hash0 { stmt 6 with root := 0 } ⟨edb, honest⟩ = false

-- The active domain and the closure enumeration size, for the counts table.
#guard (activeDomain tc edb).length == 6
#guard (substs (activeDomain tc edb) (varBound rStep)).length == 216

/-- Non-vacuity of the SEMANTICS: `path(1, 4)` is derivable, as a term. -/
theorem path14_derives : Derives tc edb (PATH, [1, 4]) := by
  have hedge12 : Derives tc edb (EDGE, [1, 2]) := Derives.edb (by simp [edb])
  have hedge23 : Derives tc edb (EDGE, [2, 3]) := Derives.edb (by simp [edb])
  have hedge34 : Derives tc edb (EDGE, [3, 4]) := Derives.edb (by simp [edb])
  have hp34 : Derives tc edb (PATH, [3, 4]) :=
    Derives.fire (r := rBase) (s := [3, 4]) (by simp [tc]) (by decide)
      (by intro b hb; simp [rBase] at hb; subst hb; decide)
      (by
        intro b hb f hf
        simp [rBase] at hb; subst hb
        have : f = (EDGE, [3, 4]) := by
          have h' : applyAtom [3, 4] (⟨EDGE, [.var 0, .var 1]⟩ : Atom) = some (EDGE, [3, 4]) := by decide
          rw [h'] at hf; simpa using hf.symm
        subst this; exact hedge34)
      (by decide)
  have hp24 : Derives tc edb (PATH, [2, 4]) :=
    Derives.fire (r := rStep) (s := [2, 3, 4]) (by simp [tc]) (by decide)
      (by
        intro b hb
        simp only [rStep, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> decide)
      (by
        intro b hb f hf
        simp only [rStep, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · have h' : applyAtom [2, 3, 4] (⟨EDGE, [.var 0, .var 1]⟩ : Atom) = some (EDGE, [2, 3]) := by
            decide
          rw [h'] at hf; simp only [Option.some.injEq] at hf; subst hf; exact hedge23
        · have h' : applyAtom [2, 3, 4] (⟨PATH, [.var 1, .var 2]⟩ : Atom) = some (PATH, [3, 4]) := by
            decide
          rw [h'] at hf; simp only [Option.some.injEq] at hf; subst hf; exact hp34)
      (by decide)
  exact Derives.fire (r := rStep) (s := [1, 2, 4]) (by simp [tc]) (by decide)
    (by
      intro b hb
      simp only [rStep, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
    (by
      intro b hb f hf
      simp only [rStep, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · have h' : applyAtom [1, 2, 4] (⟨EDGE, [.var 0, .var 1]⟩ : Atom) = some (EDGE, [1, 2]) := by
          decide
        rw [h'] at hf; simp only [Option.some.injEq] at hf; subst hf; exact hedge12
      · have h' : applyAtom [1, 2, 4] (⟨PATH, [.var 1, .var 2]⟩ : Atom) = some (PATH, [2, 4]) := by
          decide
        rw [h'] at hf; simp only [Option.some.injEq] at hf; subst hf; exact hp24)
    (by decide)

end Reference

/-! ## §7 — axiom tripwires. -/

#assert_all_clean [mem_substs_iff, atomHolds_iff, bodyHolds_iff, substOk_iff, ruleFires_some,
  mem_addFact, subset_addFact, mem_addFact_self, nodup_addFact, closedB_iff, applyFiring_some,
  applyFiring_sound, applyRound_sound, replay_sound', replay_sound,
  applyFiring_superset, applyRound_superset, replay_superset,
  applyFiring_nodup, applyRound_nodup, replay_nodup, closed_complete,
  flatten_injective, verify_sound, edb_bound_or_collides, countQ_eq_of_same_members,
  count_unique_or_collides, Reference.path14_derives, Reference.honest_verifies,
  Reference.open_trace_separation]

end Dregg2.Datalog.FixpointCert
