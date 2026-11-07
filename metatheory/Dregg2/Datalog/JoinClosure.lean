/-
# Dregg2.Datalog.JoinClosure — the closure leg by JOIN, not by enumeration; the checker
`lake exe datalog-check` runs (lane A, 2026-11-06).

## Why this file exists

`StratifiedCert.closedS` checks closure by enumerating `substs dom (varBoundS r)`: `|dom|^{vars}`
candidates per rule. On the demo EDB (`demo/datalog-governance/`) the active domain has thousands of
constants and the governance rules have up to six variables, so that enumeration does not run
(note `13-datalog.md` §3 named it the ceiling). For a SAFE rule (every variable occurs in a positive
body atom) the only substitutions under which the body can hold are those produced by matching the
positive atoms against the database, one atom at a time: a nested-loop join. `closedJoinS`
enumerates exactly those, and `closedJoinS_closedS` proves it implies `closedS` for every domain.

Also: replay consults the domain only through membership, so the checker may use the sorted,
deduplicated domain (`domFast`, `mem_domFast`) instead of the multiset `activeDomainS` (which has
one entry per EDB argument).

`verifyJ` is `verifyS` with these two substitutions, and `verifyJ_verifyS` proves
`verifyJ hash st c = true → verifyS hash st c = true`, so `verifyS_sound`,
`verifyS_strata_exact`, `countS_unique_or_collides`, `verifyS_supported_model` and
`verifyS_intended_or_collides` all hold for what the executable accepts. `verifyBudgetJ` is the same
for `Aggregates.verifyBudget` (`verifyBudgetJ_verifyBudget`).

The converse is not claimed: `verifyJ` additionally REFUSES unsafe rules (`safeB`), which `verifyS`
accepts over the active domain. That is a refusal, never an extra acceptance.

`safeB` means **range-restricted with DENSE variable numbering** (codex round 4, item 15): every
index below `varBoundS r` must occur in a positive atom, so a range-restricted rule that uses only
variable `1` is refused (`#guard` below). Variable ids are not normalized; write rules with
variables `0..n-1`. This too is a refusal, never an acceptance.

## Proved (kernel-clean, §6)
`bindArgs_complete`, `joinAll_complete`, `mem_candidates`, `closedJoinS_closedS`, `mem_domFast`,
`replayS_congr`, `runStrataJ_runStrata`, `verifyJ_verifyS`, `verifyBudgetJ_verifyBudget`.

## Falsifier
`verifyJNoSafe` (the join closure without the safety check) ACCEPTS a certificate for the unsafe
rule `p(X) :- q()` that leaves `p(1)` underived (the join binds no `X`, so it checks nothing), while
`verifyS` and `verifyJ` both refuse it. Every `StratifiedCert`/`Aggregates` reference certificate
gets the same verdict from `verifyJ` as from `verifyS`.

## Axiom hygiene
`#assert_all_clean` on every theorem. NEW file; imports read-only. -/
import Dregg2.Datalog.Aggregates

namespace Dregg2.Datalog.JoinClosure

/- v4.35: core's `Std.LinearOrderPackage` (Int, Fin, UInt*) supplies a choice-built `BEq`; keep
`==`/`!=` on instBEqOfDecidableEq so the choice-free axiom pins hold (see Tree/Value.lean). -/
attribute [local instance high] instBEqOfDecidableEq

open Dregg2.Datalog.FixpointCert
open Dregg2.Datalog.StratifiedCert
open Dregg2.Datalog.Aggregates
open Dregg2.Lightclient.MMR (mroot)

set_option autoImplicit false

/-! ## §1 — Partial substitutions and matching. -/

abbrev PSubst := List (Option ℤ)

/-- Bind one term to one value. -/
def bindTerm (ps : PSubst) : Term → ℤ → Option PSubst
  | .const c, v => if c = v then some ps else none
  | .var i, v =>
    match ps[i]? with
    | none => none
    | some none => some (ps.set i (some v))
    | some (some w) => if w = v then some ps else none

def bindArgs : PSubst → List Term → List ℤ → Option PSubst
  | ps, [], [] => some ps
  | ps, t :: ts, v :: vs => (bindTerm ps t v).bind fun ps' => bindArgs ps' ts vs
  | _, _, _ => none

def matchAtom (ps : PSubst) (a : Atom) (f : Fact) : Option PSubst :=
  if f.1 = a.pred then bindArgs ps a.args f.2 else none

def posAtoms (r : SRule) : List Atom :=
  r.body.filterMap fun l => match l with | .pos a => some a | .neg _ => none

theorem mem_posAtoms {r : SRule} {a : Atom} : a ∈ posAtoms r ↔ Lit.pos a ∈ r.body := by
  unfold posAtoms
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l with
    | pos b => simp only [Option.some.injEq] at he; subst he; exact hl
    | neg b => simp at he
  · intro h; exact ⟨_, h, rfl⟩

/-- The nested-loop join of the positive atoms against `db`. -/
def joinAll (db : List Fact) : List Atom → List PSubst → List PSubst
  | [], pss => pss
  | a :: as, pss =>
    let fs := db.filter fun f => f.1 == a.pred
    joinAll db as (pss.flatMap fun ps => fs.filterMap fun f => matchAtom ps a f)

def candidates (db : List Fact) (r : SRule) : List Subst :=
  (joinAll db (posAtoms r) [List.replicate (varBoundS r) none]).filterMap fun ps => ps.mapM id

/-- Safety: every variable below `varBoundS r` occurs in a positive body atom (range restriction
WITH dense numbering: an unused index below the bound fails it). -/
def safeB (r : SRule) : Bool :=
  (List.range (varBoundS r)).all fun i => decide (i ∈ (posAtoms r).flatMap atomVars)

/-! ## §2 — Completeness of the join. -/

/-- `ps` agrees with the total substitution `s`. -/
def Agrees (ps : PSubst) (s : Subst) : Prop :=
  ps.length = s.length ∧ ∀ (i : Nat) (v : ℤ), ps[i]? = some (some v) → s[i]? = some v

def Bound (ps : PSubst) (i : Nat) : Prop := ∃ v, ps[i]? = some (some v)

theorem bindTerm_complete {ps : PSubst} {s : Subst} (hag : Agrees ps s) (t : Term) (v : ℤ)
    (ht : applyTerm s t = some v) :
    ∃ ps', bindTerm ps t v = some ps' ∧ Agrees ps' s ∧
      (∀ i, Bound ps i → Bound ps' i) ∧
      (∀ i, t = .var i → Bound ps' i) := by
  cases t with
  | const c =>
    simp only [applyTerm, Option.some.injEq] at ht
    subst ht
    refine ⟨ps, by simp [bindTerm], hag, fun _ h => h, fun i h => by cases h⟩
  | var i =>
    simp only [applyTerm] at ht
    have hlt : i < s.length := (List.getElem?_eq_some_iff.mp ht).1
    have hlt' : i < ps.length := hag.1 ▸ hlt
    have hpi : ps[i]? = some ps[i] := List.getElem?_eq_getElem hlt'
    cases hx : ps[i] with
    | none =>
      refine ⟨ps.set i (some v), by simp [bindTerm, hpi, hx], ⟨by simp [hag.1], ?_⟩, ?_, ?_⟩
      · intro j w hj
        by_cases hij : i = j
        · subst hij
          rw [List.getElem?_set_self hlt'] at hj
          simp only [Option.some.injEq] at hj
          rw [← hj]; exact ht
        · rw [List.getElem?_set_ne hij] at hj
          exact hag.2 j w hj
      · intro j hb
        obtain ⟨w, hw⟩ := hb
        by_cases hij : i = j
        · subst hij; exact ⟨v, List.getElem?_set_self hlt'⟩
        · exact ⟨w, by rw [List.getElem?_set_ne hij]; exact hw⟩
      · intro j hj
        cases hj
        exact ⟨v, List.getElem?_set_self hlt'⟩
    | some w =>
      have hw : ps[i]? = some (some w) := by rw [hpi, hx]
      have hsw : s[i]? = some w := hag.2 i w hw
      rw [ht] at hsw
      simp only [Option.some.injEq] at hsw
      subst hsw
      refine ⟨ps, by simp [bindTerm, hpi, hx], hag, fun _ h => h, ?_⟩
      intro j hj
      cases hj
      exact ⟨_, hw⟩

theorem bindArgs_complete : ∀ (ts : List Term) (ps : PSubst) (s : Subst) (vs : List ℤ),
    Agrees ps s → ts.mapM (applyTerm s) = some vs →
    ∃ ps', bindArgs ps ts vs = some ps' ∧ Agrees ps' s ∧
      (∀ i, Bound ps i → Bound ps' i) ∧
      (∀ i, Term.var i ∈ ts → Bound ps' i)
  | [], ps, s, vs, hag, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨ps, rfl, hag, fun _ h => h, fun _ h => by simp at h⟩
  | t :: ts, ps, s, vs, hag, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs', hvs', rfl⟩ := h
    obtain ⟨ps₁, h₁, hag₁, hmono₁, hb₁⟩ := bindTerm_complete hag t v hv
    obtain ⟨ps₂, h₂, hag₂, hmono₂, hb₂⟩ := bindArgs_complete ts ps₁ s vs' hag₁ hvs'
    refine ⟨ps₂, ?_, hag₂, fun i hi => hmono₂ i (hmono₁ i hi), ?_⟩
    · simp only [bindArgs, h₁, Option.bind_some, h₂]
    · intro i hi
      rcases List.mem_cons.mp hi with he | hi
      · exact hmono₂ i (hb₁ i he.symm)
      · exact hb₂ i hi

theorem mem_atomVars {a : Atom} {i : Nat} : i ∈ atomVars a ↔ Term.var i ∈ a.args := by
  unfold atomVars
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, he⟩
    cases t with
    | var j => simp only [Option.some.injEq] at he; subst he; exact ht
    | const c => simp at he
  · intro h; exact ⟨_, h, rfl⟩

theorem matchAtom_complete {ps : PSubst} {s : Subst} {a : Atom} {f : Fact} (hag : Agrees ps s)
    (hf : applyAtom s a = some f) :
    ∃ ps', matchAtom ps a f = some ps' ∧ Agrees ps' s ∧ (∀ i, Bound ps i → Bound ps' i) ∧
      (∀ i ∈ atomVars a, Bound ps' i) := by
  unfold applyAtom at hf
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨ps', h, hag', hmono, hb⟩ := bindArgs_complete a.args ps s vs hag hvs
  refine ⟨ps', by simp [matchAtom, h], hag', hmono, fun i hi => hb i (mem_atomVars.mp hi)⟩

theorem joinAll_complete (db : List Fact) (s : Subst) : ∀ (as : List Atom) (pss : List PSubst)
    (ps : PSubst), ps ∈ pss → Agrees ps s →
    (∀ a ∈ as, ∃ f, applyAtom s a = some f ∧ f ∈ db) →
    ∃ ps' ∈ joinAll db as pss, Agrees ps' s ∧ (∀ i, Bound ps i → Bound ps' i) ∧
      (∀ a ∈ as, ∀ i ∈ atomVars a, Bound ps' i)
  | [], pss, ps, hps, hag, _ => ⟨ps, hps, hag, fun _ h => h, fun _ h => by simp at h⟩
  | a :: as, pss, ps, hps, hag, hall => by
    obtain ⟨f, hf, hfdb⟩ := hall a List.mem_cons_self
    obtain ⟨ps₁, hm, hag₁, hmono₁, hb₁⟩ := matchAtom_complete hag hf
    have hpred : f.1 = a.pred := applyAtom_pred hf
    have hmem : ps₁ ∈ pss.flatMap fun ps =>
        (db.filter fun f => f.1 == a.pred).filterMap fun f => matchAtom ps a f := by
      refine List.mem_flatMap.mpr ⟨ps, hps, List.mem_filterMap.mpr ⟨f, ?_, hm⟩⟩
      exact List.mem_filter.mpr ⟨hfdb, by simp [hpred]⟩
    obtain ⟨ps₂, h₂, hag₂, hmono₂, hb₂⟩ :=
      joinAll_complete db s as _ ps₁ hmem hag₁ (fun b hb => hall b (List.mem_cons_of_mem _ hb))
    refine ⟨ps₂, h₂, hag₂, fun i hi => hmono₂ i (hmono₁ i hi), ?_⟩
    intro b hb i hi
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hmono₂ i (hb₁ i hi)
    · exact hb₂ b hb i hi

theorem mapM_id_of_total {ps : PSubst} {s : Subst} (hag : Agrees ps s)
    (htot : ∀ i, i < s.length → Bound ps i) : ps.mapM id = some s := by
  have hps : ps = s.map some := by
    apply List.ext_getElem? 
    intro i
    by_cases hi : i < s.length
    · obtain ⟨v, hv⟩ := htot i hi
      rw [hv, List.getElem?_map, hag.2 i v hv]
      rfl
    · have h1 : ps[i]? = none := List.getElem?_eq_none (by have := hag.1; omega)
      have h2 : (s.map some)[i]? = none := List.getElem?_eq_none (by simp; omega)
      rw [h1, h2]
  subst hps
  clear hag htot
  induction s with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- ⚑ **`mem_candidates`** — for a safe rule, every substitution of the right length under which all
positive atoms hold in `db` is a join candidate. -/
theorem mem_candidates {db : List Fact} {r : SRule} {s : Subst} (hsafe : safeB r = true)
    (hlen : s.length = varBoundS r)
    (hpos : ∀ a, Lit.pos a ∈ r.body → ∃ f, applyAtom s a = some f ∧ f ∈ db) :
    s ∈ candidates db r := by
  have hag0 : Agrees (List.replicate (varBoundS r) none) s := by
    refine ⟨by simp [hlen], fun i v h => ?_⟩
    simp [List.getElem?_replicate] at h
  obtain ⟨ps', hmem, hag', _, hb⟩ := joinAll_complete db s (posAtoms r) _ _
    (List.mem_singleton_self _) hag0 (fun a ha => hpos a (mem_posAtoms.mp ha))
  refine List.mem_filterMap.mpr ⟨ps', hmem, mapM_id_of_total hag' ?_⟩
  intro i hi
  unfold safeB at hsafe
  rw [List.all_eq_true] at hsafe
  have := hsafe i (List.mem_range.mpr (hlen ▸ hi))
  simp only [decide_eq_true_eq, List.mem_flatMap] at this
  obtain ⟨a, ha, hia⟩ := this
  exact hb a ha i hia

/-! ## §3 — The join closure check implies the enumeration closure check. -/

def closedJoinS (P : SProgram) (S : List Nat) (lower db : List Fact) : Bool :=
  S.all fun i =>
    match P[i]? with
    | none => false
    | some r => safeB r && (candidates db r).all fun s =>
        match ruleFiresS r s db lower with
        | some h => decide (h ∈ db)
        | none => true

/-- ⚑ **`closedJoinS_closedS`** — the join closure check implies the enumeration one, at EVERY
domain. -/
theorem closedJoinS_closedS {P : SProgram} {S : List Nat} {lower db : List Fact}
    (h : closedJoinS P S lower db = true) (dom : List ℤ) : closedS P dom S lower db = true := by
  rw [closedS_iff]
  unfold closedJoinS at h
  rw [List.all_eq_true] at h
  intro i hi
  have hx := h i hi
  cases hr : P[i]? with
  | none => rw [hr] at hx; exact absurd hx (by simp)
  | some r =>
    rw [hr] at hx
    simp only [Bool.and_eq_true, List.all_eq_true] at hx
    obtain ⟨hsafe, hall⟩ := hx
    refine ⟨r, rfl, fun s hs hd hf => ?_⟩
    obtain ⟨hb, _⟩ := ruleFiresS_some hf
    have hpos := ((bodyHoldsS_iff _ _ _ _).mp hb).1
    have hlen : s.length = varBoundS r := ((mem_substs_iff _ _ _).mp hs).1
    have := hall s (mem_candidates hsafe hlen hpos)
    rw [hf] at this
    simpa using this

/-! ## §4 — The fast domain. -/

def dedupSorted : List ℤ → List ℤ
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedupSorted (y :: rest) else x :: dedupSorted (y :: rest)

theorem mem_dedupSorted : ∀ (l : List ℤ) (x : ℤ), x ∈ dedupSorted l ↔ x ∈ l
  | [], x => Iff.rfl
  | [y], x => Iff.rfl
  | y :: z :: rest, x => by
    simp only [dedupSorted]
    by_cases h : y = z
    · rw [if_pos h, mem_dedupSorted (z :: rest) x]
      subst h; simp
    · rw [if_neg h, List.mem_cons, mem_dedupSorted (z :: rest) x]
      exact List.mem_cons.symm

/-- The sorted, duplicate-free active domain. -/
def domFast (P : SProgram) (edb : List Fact) : List ℤ :=
  dedupSorted ((activeDomainS P edb).mergeSort fun a b => decide (a ≤ b))

theorem mem_domFast (P : SProgram) (edb : List Fact) (x : ℤ) :
    x ∈ domFast P edb ↔ x ∈ activeDomainS P edb := by
  unfold domFast
  rw [mem_dedupSorted]
  exact (List.mergeSort_perm _ _).mem_iff

theorem substOk_congr {d₁ d₂ : List ℤ} (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) (r : Rule) (s : Subst) :
    substOk d₁ r s = substOk d₂ r s := by
  unfold substOk
  simp only [hd]

theorem applyFiringS_congr {d₁ d₂ : List ℤ} (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) (P : SProgram)
    (S : List Nat) (lower cur : List Fact) (fr : Firing) :
    applyFiringS P d₁ S lower cur fr = applyFiringS P d₂ S lower cur fr := by
  unfold applyFiringS
  split <;> try rfl
  split <;> try rfl
  rename_i r _
  rw [substOk_congr hd]

theorem applyFiringsS_congr {d₁ d₂ : List ℤ} (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) (P : SProgram)
    (S : List Nat) (lower : List Fact) :
    ∀ (db : List Fact) (frs : List Firing),
      applyFiringsS P d₁ S lower db frs = applyFiringsS P d₂ S lower db frs
  | db, [] => rfl
  | db, fr :: rest => by
    simp only [applyFiringsS]
    rw [applyFiringS_congr hd]
    congr 1
    funext db'
    exact applyFiringsS_congr hd P S lower db' rest

theorem replayS_congr {d₁ d₂ : List ℤ} (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) (P : SProgram)
    (S : List Nat) (lower db : List Fact) (rds : List Round) :
    replayS P d₁ S lower db rds = replayS P d₂ S lower db rds :=
  applyFiringsS_congr hd P S lower db _

/-! ## §5 — The executable verifier and its transfer to `verifyS`. -/

def runStrataJ (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact →
    Option (List Fact)
  | [], [], db => some db
  | S :: rest, t :: ts, db =>
    match replayS P dom S db db t.rounds with
    | none => none
    | some db₁ => if closedJoinS P S db db₁ then runStrataJ P dom rest ts db₁ else none
  | _, _, _ => none

theorem runStrataJ_runStrata {P : SProgram} {d₁ d₂ : List ℤ} (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) :
    ∀ (strata : Strata) (ts : List Trace) (db db' : List Fact),
      runStrataJ P d₁ strata ts db = some db' → runStrata P d₂ strata ts db = some db'
  | [], [], db, db', h => h
  | [], _ :: _, _, _, h => by simp [runStrataJ] at h
  | _ :: _, [], _, _, h => by simp [runStrataJ] at h
  | S :: rest, t :: ts, db, db', h => by
    simp only [runStrataJ] at h
    rw [replayS_congr hd] at h
    simp only [runStrata]
    cases hr : replayS P d₂ S db db t.rounds with
    | none => rw [hr] at h; exact absurd h (by simp)
    | some db₁ =>
      rw [hr] at h
      simp only at h ⊢
      by_cases hc : closedJoinS P S db db₁ = true
      · rw [if_pos hc] at h
        rw [if_pos (closedJoinS_closedS hc d₂)]
        exact runStrataJ_runStrata hd rest ts db₁ db' h
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **The executable verifier**: `verifyS` with the join closure and the fast domain. -/
def verifyJ (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match runStrataJ st.program (domFast st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

/-- ⚑ **`verifyJ_verifyS`** — what the executable accepts, `verifyS` accepts: every `StratifiedCert`
theorem holds for the extracted checker. -/
theorem verifyJ_verifyS (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate)
    (h : verifyJ hash st c = true) : verifyS hash st c = true := by
  unfold verifyJ at h
  unfold verifyS
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨hpre, hrest⟩ := h
  refine ⟨hpre, ?_⟩
  cases hrun : runStrataJ st.program (domFast st.program c.edb) st.strata c.traces c.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    rw [hrun] at hrest
    rw [runStrataJ_runStrata (mem_domFast st.program c.edb) _ _ _ _ hrun]
    exact hrest

def verifyBudgetJ (hash : List ℤ → ℤ) (st : BudgetStatement) (c : BudgetCertificate) : Bool :=
  verifyJ hash (st.toS c.count) c.cert &&
  match runStrataJ st.program (domFast st.program c.cert.edb) st.strata c.cert.traces
      c.cert.edb with
  | none => false
  | some db => accValid (vals db st.pred st.arg) c.acc &&
      match c.acc.getLast? with
      | some v => decide (v ≤ st.limit)
      | none => false

/-- ⚑ **`verifyBudgetJ_verifyBudget`** — the executable budget check implies `verifyBudget`. -/
theorem verifyBudgetJ_verifyBudget (hash : List ℤ → ℤ) (st : BudgetStatement)
    (c : BudgetCertificate) (h : verifyBudgetJ hash st c = true) :
    verifyBudget hash st c = true := by
  unfold verifyBudgetJ at h
  unfold verifyBudget
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hv, hrest⟩ := h
  refine ⟨verifyJ_verifyS hash _ _ hv, ?_⟩
  cases hrun : runStrataJ st.program (domFast st.program c.cert.edb) st.strata c.cert.traces
      c.cert.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    rw [hrun] at hrest
    rw [runStrataJ_runStrata (mem_domFast st.program c.cert.edb) _ _ _ _ hrun]
    exact hrest

/-! ## §6 — Agreement on the reference certificates, and the safety falsifier. -/

namespace Reference

open Dregg2.Datalog.FixpointCert.Reference (hash0)
open Dregg2.Datalog.StratifiedCert.Reference
open Dregg2.Datalog.Aggregates.Reference

#guard verifyJ hash0 (revStmt 1) ⟨revEdb, revHonest⟩ = true
#guard verifyJ hash0 (revStmt 2) ⟨revEdb, revForged⟩ = false
#guard verifyJ hash0 (evStmt 0) ⟨evEdb, evHonest⟩ = true
#guard verifyJ hash0 (evStmt 1) ⟨evEdb, evForged⟩ = false
#guard verifyJ hash0 (evStmt 1) ⟨evEdb, evOpen⟩ = false
#guard verifyJ hash0 (evStmt 0) ⟨evEdb, evOpen⟩ = false
#guard verifyJ hash0 nsStmt ⟨nsEdb, nsTrace⟩ = false
#guard verifyBudgetJ hash0 (billStmt 10) honestB = true
#guard verifyBudgetJ hash0 (billStmt 8) honestB = false
#guard verifyBudgetJ hash0 (billStmt 8) tamperedB = false

-- ⚑ SAFETY FALSIFIER: `p(X) :- q()` over `{q(), d(1)}`; the trace derives nothing.
def unsafeRule : SRule := { head := ⟨2, [.var 0]⟩, body := [.pos ⟨3, []⟩] }
def unsafeProg : SProgram := [unsafeRule]
def unsafeEdb : List Fact := [(3, []), (4, [1])]
def unsafeStmt : SStatement :=
  { program := unsafeProg, strata := [[0]], root := mroot hash0 (flatten unsafeEdb), pred := 2,
    count := 0 }
def unsafeCert : SCertificate := ⟨unsafeEdb, [{ rounds := [] }]⟩

/-- The WEAKER checker: the join closure without `safeB`. -/
def closedJoinNoSafe (P : SProgram) (S : List Nat) (lower db : List Fact) : Bool :=
  S.all fun i =>
    match P[i]? with
    | none => false
    | some r => (candidates db r).all fun s =>
        match ruleFiresS r s db lower with
        | some h => decide (h ∈ db)
        | none => true

def runNoSafe (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact → Option (List Fact)
  | [], [], db => some db
  | S :: rest, t :: ts, db =>
    match replayS P dom S db db t.rounds with
    | none => none
    | some db₁ => if closedJoinNoSafe P S db db₁ then runNoSafe P dom rest ts db₁ else none
  | _, _, _ => none

def verifyJNoSafe (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match runNoSafe st.program (domFast st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

#guard safeB unsafeRule = false
#guard candidates unsafeEdb unsafeRule = []
#guard verifyJNoSafe hash0 unsafeStmt unsafeCert = true
#guard verifyS hash0 unsafeStmt unsafeCert = false
#guard verifyJ hash0 unsafeStmt unsafeCert = false
#guard domFast revProg revEdb = [1, 2]
-- Dense numbering: `p(X₁) :- q(X₁)` is range-restricted but uses only index 1, so `safeB` refuses it.
#guard safeB { head := ⟨2, [.var 1]⟩, body := [.pos ⟨3, [.var 1]⟩] } = false
#guard safeB { head := ⟨2, [.var 0]⟩, body := [.pos ⟨3, [.var 0]⟩] } = true

/-- `p(1)` IS in the (active-domain) stratified model of the unsafe program: the count 0 the weak
checker accepted is false. -/
theorem unsafe_p1_derivesS : DerivesS unsafeProg [[0]] unsafeEdb (2, [1]) := by
  show DerivesAt unsafeProg (activeDomainS unsafeProg unsafeEdb) [0] (· ∈ unsafeEdb) (2, [1])
  refine DerivesAt.fire (i := 0) (r := unsafeRule) (s := [1]) (by simp) rfl (by decide) ?_ ?_ ?_
    (by decide)
  · intro a ha
    simp only [unsafeRule, List.mem_singleton, Lit.pos.injEq] at ha
    subst ha; decide
  · intro a ha f hf
    simp only [unsafeRule, List.mem_singleton, Lit.pos.injEq] at ha
    subst ha
    have h' : applyAtom [1] (⟨3, []⟩ : Atom) = some (3, []) := by decide
    rw [h'] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    exact DerivesAt.base (by decide)
  · intro a ha
    simp [unsafeRule] at ha

/-- ⚑ JOIN SAFETY SEPARATION (codex round 4, item 8): the join closure without `safeB` accepts the
open certificate at count 0; `verifyS` and `verifyJ` refuse it; and `p(1)` is in the model, so the
accepted count is false. -/
theorem join_safety_separation :
    verifyJNoSafe hash0 unsafeStmt unsafeCert = true ∧
    verifyS hash0 unsafeStmt unsafeCert = false ∧
    verifyJ hash0 unsafeStmt unsafeCert = false ∧
    DerivesS unsafeProg [[0]] unsafeEdb (2, [1]) := by
  have hS : verifyS hash0 unsafeStmt unsafeCert = false := by decide
  refine ⟨by decide, hS, ?_, unsafe_p1_derivesS⟩
  cases hJ : verifyJ hash0 unsafeStmt unsafeCert with
  | false => rfl
  | true => rw [verifyJ_verifyS _ _ _ hJ] at hS; exact absurd hS (by simp)

end Reference

#assert_all_clean [mem_posAtoms, bindTerm_complete, bindArgs_complete, mem_atomVars,
  matchAtom_complete, joinAll_complete, mapM_id_of_total, mem_candidates, closedJoinS_closedS,
  mem_dedupSorted, mem_domFast, substOk_congr, applyFiringS_congr, applyFiringsS_congr,
  replayS_congr, runStrataJ_runStrata, verifyJ_verifyS, verifyBudgetJ_verifyBudget,
  Reference.unsafe_p1_derivesS, Reference.join_safety_separation]

end Dregg2.Datalog.JoinClosure
