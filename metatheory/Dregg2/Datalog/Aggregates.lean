/-
# Dregg2.Datalog.Aggregates — Sum / Min / Max over an exactly-certified Datalog database, and the
budget statement (lane A of `docs/automata/SUBSTRATE-DECISION.md` §7, 2026-11-06).

## The object

Over the closed database a `StratifiedCert.verifyS` certificate determines (EXACTLY the stratified
model, `verifyS_sound`), the aggregates of argument `i` of predicate `p` are folds over the facts of
`p` in database order: `sumAt`, `minAt`, `maxAt`. Because the database is duplicate-free and its
member set is determined by `(program, strata, root)` (`countS_unique_or_collides`' argument), every
aggregate here is invariant under reordering (`sumAt_eq_of_same_members`, `minAt_eq_of_same_members`,
`maxAt_eq_of_same_members`), so it is a function of the committed EDB and the program.

A certificate for a SUM carries the row-by-row accumulator column (the weighted-automaton shape of
note `08-weighted.md` §5): row 0 is `0` and row `k+1` is row `k` plus the `k`-th value. The checker
verifies every row (`accValid`, a degree-1 gate per row); `seq_acc_is_fold` is the statement that
the column IS the prefix fold, and `accValid_iff` that the row gates pin the column uniquely.

The **budget statement** `BudgetStatement := (program, strata, root, pred, arg, limit)`;
`verifyBudget` = `verifyS` (with the certificate's exact count) + the accumulator rows over the
facts of `pred` in the verified database + `final row ≤ limit`. `verifyBudget_sound`: the sum of
argument `arg` over EXACTLY the derivable `pred`-facts is `≤ limit`, the count is exact, the EDB is
bound to the root. `budget_final_unique_or_collides`: the final accumulator row is a function of the
statement, or the sponge collides at the named pair.

## What `audit::BudgetProof` claims today, and what this restates

[READ `audit/src/proofs.rs:253-305`] `BudgetProof::verify` checks `uses_consumed ≤ budget_limit`,
`remaining = budget_limit - uses_consumed`, `count_proof.count = uses_consumed`, the token ids
agree, and `count_proof.verify()`. [READ `audit/src/budget.rs:168-195`] `prove_budget_status`
fills `uses_consumed` from the enforcer's own state and attaches `self.log.prove_count(&token_id)`;
the comment at `budget.rs:181-182` says the count proof covers ALL of the token's events, also for a
windowed budget, while `uses_consumed` is the in-window count [INFERRED: a windowed proof with an
out-of-window event fails `proofs.rs:294`'s equality]. The arithmetic is therefore only as strong as
`CountProof`, which [READ `SUBSTRATE-DECISION.md` §1] never ties `global_index` to the inclusion
path, leaves `log_size` unbound, and verifies `count = 0` for any token and root. So today's
`BudgetProof` proves arithmetic about a number it does not bind.

The restatement: uses are facts `use(token, seq, cost)` in a committed EDB; `uses_consumed` is the
EXACT `countQ` of `verifyS` (no omission: closure is the gate), and the spend is `sumAt … cost` with
its accumulator column checked row by row; `remaining = limit - sum` is then arithmetic over a bound
number. Unit-cost budgets are `cost = 1` (sum = count). The time window is NOT restated: it waits on
a timestamp-to-leaf binding (SUBSTRATE-DECISION §3, row `audit`). Nothing here edits `audit`.

## What is proved (kernel-clean, §5)
  * `seq_acc_is_fold`: row `k` of `accCol xs` is the fold of the first `k` values.
  * `accValid_iff`: the row gates hold iff the column is `accCol xs`.
  * `sumAt_eq_of_same_members`, `minAt_spec`, `maxAt_spec`, `minAt_eq_of_same_members`,
    `maxAt_eq_of_same_members`.
  * `verifyBudget_sound`, `budget_final_unique_or_collides`.

## Falsifier (§4; `#guard`s and the kernel-decided pair `tampered_accepted_by_trustFinal`,
`tampered_refused_by_verifyBudget`): `billable(S, C) :- charge(S, C), ¬refunded(S)` over
`charge(1,5), charge(2,7), charge(3,4), refunded(2)`: the billable sum is 9. At `limit = 10` the
honest column `[0, 5, 9]` verifies; at `limit = 8` it is refused (over budget). The TAMPERED column
`[0, 5, 5]` (row 2 disagrees with the fold) hides the overrun: `verifyTrustFinal` (rows not checked,
final row trusted) ACCEPTS it at `limit = 8`; `verifyBudget` refuses it.

## Scope
  * `argAt` reads a missing argument as `0`: a `pred`-fact of smaller arity contributes `0`. The
    deployed schema fixes the arity; a per-predicate arity check is not part of `verifyS`.
  * Aggregates are over the SET of facts: two identical events collapse to one fact unless the
    event carries its occurrence id (sequence number); the schema must carry it.
  * Values are `ℤ`; no overflow model. A field-element accumulator needs a range argument.

## Axiom hygiene
`#assert_all_clean` on every theorem. NEW file; `FixpointCert` and `StratifiedCert` read-only. -/
import Dregg2.Datalog.StratifiedCert

namespace Dregg2.Datalog.Aggregates

/- v4.35: core's `Std.LinearOrderPackage` (Int, Fin, UInt*) supplies a choice-built `BEq`; keep
`==`/`!=` on instBEqOfDecidableEq so the choice-free axiom pins hold (see Tree/Value.lean). -/
attribute [local instance high] instBEqOfDecidableEq

open Dregg2.Datalog.FixpointCert
open Dregg2.Datalog.StratifiedCert
open Dregg2.Lightclient.MMR (mroot MRootColl mroot_binds_or_collides)

set_option autoImplicit false

/-! ## §1 — Aggregates as folds. -/

/-- Argument `i` of a fact (`0` when absent). -/
def argAt (i : Nat) (f : Fact) : ℤ := f.2.getD i 0

/-- The values of argument `i` over the `p`-facts of `db`, in database order. -/
def vals (db : List Fact) (p i : Nat) : List ℤ :=
  (db.filter fun f => f.1 == p).map (argAt i)

def sumAt (db : List Fact) (p i : Nat) : ℤ := (vals db p i).foldl (· + ·) 0

def minStep (a : Option ℤ) (x : ℤ) : Option ℤ :=
  some (match a with | none => x | some m => min m x)
def maxStep (a : Option ℤ) (x : ℤ) : Option ℤ :=
  some (match a with | none => x | some m => max m x)

def minAt (db : List Fact) (p i : Nat) : Option ℤ := (vals db p i).foldl minStep none
def maxAt (db : List Fact) (p i : Nat) : Option ℤ := (vals db p i).foldl maxStep none

theorem foldl_add_eq (l : List ℤ) : ∀ a : ℤ, l.foldl (· + ·) a = a + l.sum := by
  induction l with
  | nil => intro a; simp
  | cons x xs ih => intro a; simp only [List.foldl_cons, List.sum_cons]; rw [ih]; ring

theorem vals_perm {db₁ db₂ : List Fact} (h : db₁.Perm db₂) (p i : Nat) :
    (vals db₁ p i).Perm (vals db₂ p i) := (h.filter _).map _

/-- The sum is a function of the member set of a duplicate-free database. -/
theorem sumAt_eq_of_same_members {db₁ db₂ : List Fact} (h₁ : db₁.Nodup) (h₂ : db₂.Nodup)
    (hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂) (p i : Nat) : sumAt db₁ p i = sumAt db₂ p i := by
  have hperm : db₁.Perm db₂ := (List.perm_ext_iff_of_nodup h₁ h₂).mpr hm
  unfold sumAt
  rw [foldl_add_eq, foldl_add_eq, (vals_perm hperm p i).sum_eq]

/-- The fold of `minStep` from `some a`: the result is `a` or a member, and below `a` and all. -/
theorem foldl_minStep_some (l : List ℤ) : ∀ a m : ℤ, l.foldl minStep (some a) = some m →
    (m = a ∨ m ∈ l) ∧ m ≤ a ∧ ∀ x ∈ l, m ≤ x := by
  induction l with
  | nil => intro a m h; simp only [List.foldl_nil, Option.some.injEq] at h; subst h; simp
  | cons x xs ih =>
    intro a m h
    simp only [List.foldl_cons, minStep] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h
    refine ⟨?_, le_trans h2 (min_le_left _ _), ?_⟩
    · rcases h1 with h1 | h1
      · rcases min_choice a x with hc | hc
        · exact Or.inl (h1.trans hc)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (h1.trans hc)))
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_trans h2 (min_le_right _ _)
      · exact h3 y hy

theorem foldl_maxStep_some (l : List ℤ) : ∀ a m : ℤ, l.foldl maxStep (some a) = some m →
    (m = a ∨ m ∈ l) ∧ a ≤ m ∧ ∀ x ∈ l, x ≤ m := by
  induction l with
  | nil => intro a m h; simp only [List.foldl_nil, Option.some.injEq] at h; subst h; simp
  | cons x xs ih =>
    intro a m h
    simp only [List.foldl_cons, maxStep] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h
    refine ⟨?_, le_trans (le_max_left _ _) h2, ?_⟩
    · rcases h1 with h1 | h1
      · rcases max_choice a x with hc | hc
        · exact Or.inl (h1.trans hc)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (h1.trans hc)))
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_trans (le_max_right _ _) h2
      · exact h3 y hy

theorem foldl_step_none_iff (step : Option ℤ → ℤ → Option ℤ) (hs : ∀ a x, (step a x).isSome)
    (l : List ℤ) : l.foldl step none = none ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons x xs =>
      exfalso
      simp only [List.foldl_cons] at h
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs none x)
      rw [hb] at h
      have key : ∀ (l' : List ℤ) (b' : ℤ), l'.foldl step (some b') ≠ none := by
        intro l'
        induction l' with
        | nil => intro b' h'; simp at h'
        | cons y ys ih' =>
          intro b' h'
          simp only [List.foldl_cons] at h'
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hs (some b') y)
          rw [hc] at h'
          exact ih' c h'
      exact key xs b h
  · rintro rfl; rfl

/-- ⚑ `minAt` is the minimum: `none` iff there is no `p`-fact; otherwise a member below all. -/
theorem minAt_spec (db : List Fact) (p i : Nat) :
    (minAt db p i = none ↔ vals db p i = []) ∧
    ∀ m, minAt db p i = some m → m ∈ vals db p i ∧ ∀ x ∈ vals db p i, m ≤ x := by
  refine ⟨foldl_step_none_iff minStep (fun _ _ => rfl) _, ?_⟩
  intro m h
  unfold minAt at h
  cases hv : vals db p i with
  | nil => rw [hv] at h; simp at h
  | cons x xs =>
    rw [hv] at h
    simp only [List.foldl_cons, minStep] at h
    obtain ⟨h1, h2, h3⟩ := foldl_minStep_some xs x m h
    refine ⟨?_, ?_⟩
    · rcases h1 with rfl | h1
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h2
      · exact h3 y hy

/-- ⚑ `maxAt` is the maximum. -/
theorem maxAt_spec (db : List Fact) (p i : Nat) :
    (maxAt db p i = none ↔ vals db p i = []) ∧
    ∀ m, maxAt db p i = some m → m ∈ vals db p i ∧ ∀ x ∈ vals db p i, x ≤ m := by
  refine ⟨foldl_step_none_iff maxStep (fun _ _ => rfl) _, ?_⟩
  intro m h
  unfold maxAt at h
  cases hv : vals db p i with
  | nil => rw [hv] at h; simp at h
  | cons x xs =>
    rw [hv] at h
    simp only [List.foldl_cons, maxStep] at h
    obtain ⟨h1, h2, h3⟩ := foldl_maxStep_some xs x m h
    refine ⟨?_, ?_⟩
    · rcases h1 with rfl | h1
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ h1
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h2
      · exact h3 y hy

theorem vals_mem_iff {db₁ db₂ : List Fact} (hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂) (p i : Nat) (x : ℤ) :
    x ∈ vals db₁ p i ↔ x ∈ vals db₂ p i := by
  unfold vals
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨f, ⟨hf, hp⟩, rfl⟩; exact ⟨f, ⟨(hm f).mp hf, hp⟩, rfl⟩
  · rintro ⟨f, ⟨hf, hp⟩, rfl⟩; exact ⟨f, ⟨(hm f).mpr hf, hp⟩, rfl⟩

/-- The minimum is a function of the member set. -/
theorem minAt_eq_of_same_members {db₁ db₂ : List Fact} (hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂)
    (p i : Nat) : minAt db₁ p i = minAt db₂ p i := by
  obtain ⟨n₁, s₁⟩ := minAt_spec db₁ p i
  obtain ⟨n₂, s₂⟩ := minAt_spec db₂ p i
  have hv := vals_mem_iff hm p i
  cases h₁ : minAt db₁ p i with
  | none =>
    have e₁ := n₁.mp h₁
    symm; apply n₂.mpr
    cases hv2 : vals db₂ p i with
    | nil => rfl
    | cons x _ => exfalso; have := (hv x).mpr (by rw [hv2]; exact List.mem_cons_self); simp [e₁] at this
  | some m₁ =>
    cases h₂ : minAt db₂ p i with
    | none =>
      exfalso
      have e₂ := n₂.mp h₂
      have := (hv m₁).mp (s₁ m₁ h₁).1
      simp [e₂] at this
    | some m₂ =>
      obtain ⟨a₁, b₁⟩ := s₁ m₁ h₁
      obtain ⟨a₂, b₂⟩ := s₂ m₂ h₂
      have : m₁ = m₂ := le_antisymm (b₁ m₂ ((hv m₂).mpr a₂)) (b₂ m₁ ((hv m₁).mp a₁))
      rw [this]

/-- The maximum is a function of the member set. -/
theorem maxAt_eq_of_same_members {db₁ db₂ : List Fact} (hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂)
    (p i : Nat) : maxAt db₁ p i = maxAt db₂ p i := by
  obtain ⟨n₁, s₁⟩ := maxAt_spec db₁ p i
  obtain ⟨n₂, s₂⟩ := maxAt_spec db₂ p i
  have hv := vals_mem_iff hm p i
  cases h₁ : maxAt db₁ p i with
  | none =>
    have e₁ := n₁.mp h₁
    symm; apply n₂.mpr
    cases hv2 : vals db₂ p i with
    | nil => rfl
    | cons x _ => exfalso; have := (hv x).mpr (by rw [hv2]; exact List.mem_cons_self); simp [e₁] at this
  | some m₁ =>
    cases h₂ : maxAt db₂ p i with
    | none =>
      exfalso
      have e₂ := n₂.mp h₂
      have := (hv m₁).mp (s₁ m₁ h₁).1
      simp [e₂] at this
    | some m₂ =>
      obtain ⟨a₁, b₁⟩ := s₁ m₁ h₁
      obtain ⟨a₂, b₂⟩ := s₂ m₂ h₂
      have : m₁ = m₂ := le_antisymm (b₂ m₁ ((hv m₁).mp a₁)) (b₁ m₂ ((hv m₂).mpr a₂))
      rw [this]

/-! ## §2 — The accumulator column. -/

/-- The prefix folds from `a`: `[a, a+x₀, a+x₀+x₁, …]`. -/
def accFrom : ℤ → List ℤ → List ℤ
  | a, [] => [a]
  | a, x :: xs => a :: accFrom (a + x) xs

/-- The accumulator column a certificate should carry. -/
def accCol (xs : List ℤ) : List ℤ := accFrom 0 xs

theorem accFrom_getElem? : ∀ (xs : List ℤ) (a : ℤ) (i : Nat), i ≤ xs.length →
    (accFrom a xs)[i]? = some ((xs.take i).foldl (· + ·) a)
  | [], a, i, hi => by
    have : i = 0 := by simpa using hi
    subst this; rfl
  | x :: xs, a, 0, _ => rfl
  | x :: xs, a, i + 1, hi => by
    simp only [accFrom, List.getElem?_cons_succ, List.take_succ_cons, List.foldl_cons]
    exact accFrom_getElem? xs (a + x) i (by simpa using hi)

/-- ⚑ **`seq_acc_is_fold`** — row `i` of the accumulator column is the fold of the first `i`
values (note `08-weighted.md` §5, specialised to the additive monoid of `ℤ`). -/
theorem seq_acc_is_fold (xs : List ℤ) (i : Nat) (hi : i ≤ xs.length) :
    (accCol xs)[i]? = some ((xs.take i).foldl (· + ·) 0) :=
  accFrom_getElem? xs 0 i hi

theorem accFrom_getLast? : ∀ (xs : List ℤ) (a : ℤ),
    (accFrom a xs).getLast? = some (xs.foldl (· + ·) a)
  | [], a => rfl
  | x :: xs, a => by
    simp only [accFrom, List.foldl_cons]
    rw [List.getLast?_cons, accFrom_getLast? xs (a + x)]
    rfl

/-- The final row of the column is the sum. -/
theorem accCol_last (db : List Fact) (p i : Nat) :
    (accCol (vals db p i)).getLast? = some (sumAt db p i) :=
  accFrom_getLast? _ 0

/-- The row gates: `ACC[k+1] = ACC[k] + x[k]` on every row, and one more row than values. -/
def rowsOk : List ℤ → List ℤ → Bool
  | [], [_] => true
  | x :: xs, y :: z :: rest => z == y + x && rowsOk xs (z :: rest)
  | _, _ => false

/-- The row gates plus the initial pin `ACC[0] = 0`. -/
def accValid (xs acc : List ℤ) : Bool := acc.head? == some 0 && rowsOk xs acc

theorem rowsOk_iff : ∀ (xs : List ℤ) (y : ℤ) (rest : List ℤ),
    rowsOk xs (y :: rest) = true ↔ y :: rest = accFrom y xs
  | [], y, [] => by simp [rowsOk, accFrom]
  | [], y, _ :: _ => by simp [rowsOk, accFrom]
  | x :: xs, y, [] => by
    simp only [rowsOk, accFrom, List.cons.injEq, true_and, Bool.false_eq_true, false_iff]
    cases xs <;> simp [accFrom]
  | x :: xs, y, z :: rest => by
    simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, accFrom, List.cons.injEq, true_and]
    rw [rowsOk_iff xs z rest]
    constructor
    · rintro ⟨rfl, h⟩; rw [h]
    · intro h
      have hz : z = y + x := by
        have := congrArg List.head? h
        cases xs <;> simpa [accFrom] using this
      subst hz
      exact ⟨rfl, h⟩

/-- ⚑ **`accValid_iff`** — the row gates hold iff the column IS the accumulator column. -/
theorem accValid_iff (xs acc : List ℤ) : accValid xs acc = true ↔ acc = accCol xs := by
  unfold accValid accCol
  cases acc with
  | nil => cases xs <;> simp [accFrom]
  | cons y rest =>
    simp only [List.head?_cons, beq_iff_eq, Option.some.injEq, Bool.and_eq_true]
    constructor
    · rintro ⟨rfl, h⟩; exact (rowsOk_iff xs 0 rest).mp h
    · intro h
      have hy : y = 0 := by cases xs <;> simp [accFrom] at h <;> exact h.1
      subst hy
      exact ⟨rfl, (rowsOk_iff xs 0 rest).mpr h⟩

/-! ## §3 — The budget statement. -/

structure BudgetStatement where
  program : SProgram
  strata : Strata
  root : ℤ
  pred : Nat
  arg : Nat
  limit : ℤ
  deriving Repr

/-- The stratified certificate, the exact count it claims for `pred`, and the accumulator column
over the `pred`-facts of the verified database, in database order. -/
structure BudgetCertificate where
  cert : SCertificate
  count : Nat
  acc : List ℤ
  deriving Repr

def BudgetStatement.toS (st : BudgetStatement) (n : Nat) : SStatement :=
  { program := st.program, strata := st.strata, root := st.root, pred := st.pred, count := n }

/-- **The budget verifier.** `verifyS` (exact count), then the accumulator rows over the verified
database, then the final row against the limit. (The strata run is recomputed for the rows; the
extracted checker runs it once — `DatalogCheck.lean`.) -/
def verifyBudget (hash : List ℤ → ℤ) (st : BudgetStatement) (c : BudgetCertificate) : Bool :=
  verifyS hash (st.toS c.count) c.cert &&
  match runStrata st.program (activeDomainS st.program c.cert.edb) st.strata c.cert.traces
      c.cert.edb with
  | none => false
  | some db => accValid (vals db st.pred st.arg) c.acc &&
      match c.acc.getLast? with
      | some v => decide (v ≤ st.limit)
      | none => false

/-- ⚑ **`verifyBudget_sound`** — an accepted budget certificate: the EDB is bound to the root, and
there is a duplicate-free database that is EXACTLY the stratified model, whose `pred`-count is the
claimed count, whose accumulator column is the prefix-fold column of its `pred`-facts, and whose
SUM of argument `arg` over those facts is at most the limit. -/
theorem verifyBudget_sound (hash : List ℤ → ℤ) (st : BudgetStatement) (c : BudgetCertificate)
    (h : verifyBudget hash st c = true) :
    mroot hash (flatten c.cert.edb) = st.root ∧
    ∃ db : List Fact, db.Nodup ∧
      (∀ f, f ∈ db ↔ DerivesS st.program st.strata c.cert.edb f) ∧
      countQ db st.pred = c.count ∧ c.acc = accCol (vals db st.pred st.arg) ∧
      sumAt db st.pred st.arg ≤ st.limit := by
  unfold verifyBudget at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hS, hrest⟩ := h
  have hS' := hS
  unfold verifyS at hS'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hS'
  obtain ⟨⟨⟨_, hroot⟩, hnd⟩, hcnt⟩ := hS'
  refine ⟨hroot, ?_⟩
  cases hrun : runStrata st.program (activeDomainS st.program c.cert.edb) st.strata c.cert.traces
      c.cert.edb with
  | none => rw [hrun] at hrest; exact absurd hrest (by simp)
  | some db =>
    simp only [BudgetStatement.toS] at hcnt
    rw [hrun] at hrest hcnt
    simp only [beq_iff_eq] at hcnt
    rw [Bool.and_eq_true] at hrest
    obtain ⟨hacc, hlim⟩ := hrest
    have hacc' := (accValid_iff _ _).mp hacc
    obtain ⟨hn, hm⟩ := runStrata_sound _ _ _ _ hnd hrun
    refine ⟨db, hn, hm, hcnt, hacc', ?_⟩
    rw [hacc', accCol_last] at hlim
    simpa using hlim

/-- ⚑ **`budget_final_unique_or_collides`** — the sum is a FUNCTION of
`(program, strata, root, pred, arg)`: two accepted budget certificates have the same final
accumulator row, or the sponge collides at the named pair. -/
theorem budget_final_unique_or_collides (hash : List ℤ → ℤ) (st₁ st₂ : BudgetStatement)
    (c₁ c₂ : BudgetCertificate)
    (hP : st₁.program = st₂.program) (hS : st₁.strata = st₂.strata) (hR : st₁.root = st₂.root)
    (hp : st₁.pred = st₂.pred) (ha : st₁.arg = st₂.arg)
    (h₁ : verifyBudget hash st₁ c₁ = true) (h₂ : verifyBudget hash st₂ c₂ = true) :
    c₁.acc.getLast? = c₂.acc.getLast? ∨
      MRootColl hash (flatten c₁.cert.edb) (flatten c₂.cert.edb) := by
  obtain ⟨r₁, db₁, hn₁, hm₁, _, ha₁, _⟩ := verifyBudget_sound hash st₁ c₁ h₁
  obtain ⟨r₂, db₂, hn₂, hm₂, _, ha₂, _⟩ := verifyBudget_sound hash st₂ c₂ h₂
  rcases mroot_binds_or_collides hash (r₁.trans (hR.trans r₂.symm)) with heq | hc
  · refine Or.inl ?_
    have hedb : c₁.cert.edb = c₂.cert.edb := flatten_injective _ _ heq
    have hm : ∀ f, f ∈ db₁ ↔ f ∈ db₂ := by
      intro f; rw [hm₁, hm₂, hedb, hP, hS]
    rw [ha₁, ha₂, accCol_last, accCol_last, hp, ha,
      sumAt_eq_of_same_members hn₁ hn₂ hm]
  · exact Or.inr hc

/-! ## §4 — Falsifier: the tampered row. -/

namespace Reference

open Dregg2.Datalog.FixpointCert.Reference (hash0)

def CHARGE : Nat := 0
def REFUNDED : Nat := 1
def BILLABLE : Nat := 2

/-- `billable(S, C) :- charge(S, C), ¬refunded(S)`. -/
def rBill : SRule :=
  { head := ⟨BILLABLE, [.var 0, .var 1]⟩
  , body := [.pos ⟨CHARGE, [.var 0, .var 1]⟩, .neg ⟨REFUNDED, [.var 0]⟩] }
def billProg : SProgram := [rBill]
def billEdb : List Fact := [(CHARGE, [1, 5]), (CHARGE, [2, 7]), (CHARGE, [3, 4]), (REFUNDED, [2])]
def billCert : SCertificate := ⟨billEdb, [{ rounds := [[⟨0, [1, 5]⟩, ⟨0, [3, 4]⟩]] }]⟩
def billStmt (limit : ℤ) : BudgetStatement :=
  { program := billProg, strata := [[0]], root := mroot hash0 (flatten billEdb), pred := BILLABLE,
    arg := 1, limit := limit }

def honestB : BudgetCertificate := ⟨billCert, 2, [0, 5, 9]⟩
def tamperedB : BudgetCertificate := ⟨billCert, 2, [0, 5, 5]⟩

/-- The WEAKER checker: `verifyS`, the column's length and initial pin, and the final row trusted. -/
def verifyTrustFinal (hash : List ℤ → ℤ) (st : BudgetStatement) (c : BudgetCertificate) : Bool :=
  verifyS hash (st.toS c.count) c.cert && c.acc.head? == some 0 &&
  match runStrata st.program (activeDomainS st.program c.cert.edb) st.strata c.cert.traces
      c.cert.edb with
  | none => false
  | some db => c.acc.length == (vals db st.pred st.arg).length + 1 &&
      match c.acc.getLast? with
      | some v => decide (v ≤ st.limit)
      | none => false

-- The verified database's billable values, and the aggregates over them.
#guard (runStrata billProg (activeDomainS billProg billEdb) [[0]] billCert.traces billEdb).map
  (vals · BILLABLE 1) = some [5, 4]
#guard (runStrata billProg (activeDomainS billProg billEdb) [[0]] billCert.traces billEdb).map
  (fun db => (sumAt db BILLABLE 1, minAt db BILLABLE 1, maxAt db BILLABLE 1)) = some (9, some 4, some 5)
#guard accCol [5, 4] = [0, 5, 9]

-- ⚑ The honest column verifies within budget 10, and is refused at 8 (the sum 9 is over budget).
#guard verifyBudget hash0 (billStmt 10) honestB = true
#guard verifyBudget hash0 (billStmt 8) honestB = false
-- ⚑ THE TAMPERED ROW: row 2 claims 5 where the fold is 9.
#guard accValid [5, 4] [0, 5, 5] = false
#guard verifyBudget hash0 (billStmt 8) tamperedB = false
#guard verifyTrustFinal hash0 (billStmt 8) tamperedB = true
-- The weaker checker agrees on the honest certificate.
#guard verifyTrustFinal hash0 (billStmt 10) honestB = true
-- A wrong count is refused even with the honest column (the count leg is `verifyS`'s).
#guard verifyBudget hash0 (billStmt 10) ⟨billCert, 3, [0, 5, 9]⟩ = false

/-- Kernel-checked: the final-row-trusting checker ACCEPTS the tampered column at limit 8. -/
theorem tampered_accepted_by_trustFinal : verifyTrustFinal hash0 (billStmt 8) tamperedB = true := by
  decide
/-- Kernel-checked: `verifyBudget` REFUSES it. -/
theorem tampered_refused_by_verifyBudget : verifyBudget hash0 (billStmt 8) tamperedB = false := by
  decide

end Reference

/-! ## §5 — axiom tripwires. -/

#assert_all_clean [foldl_add_eq, vals_perm, sumAt_eq_of_same_members, foldl_minStep_some,
  foldl_maxStep_some, foldl_step_none_iff, minAt_spec, maxAt_spec, vals_mem_iff,
  minAt_eq_of_same_members, maxAt_eq_of_same_members, accFrom_getElem?, seq_acc_is_fold,
  accFrom_getLast?, accCol_last, rowsOk_iff, accValid_iff, verifyBudget_sound,
  budget_final_unique_or_collides, Reference.tampered_accepted_by_trustFinal,
  Reference.tampered_refused_by_verifyBudget]

end Dregg2.Datalog.Aggregates
