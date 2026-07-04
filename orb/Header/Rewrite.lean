/-
Header — the rewrite algebra: identities and a program interpreter.

Everything here is a corollary of the two locality lemmas in `Header/Basic.lean`
(`get_remove`, `get_set`), plus a few structural facts about `filter`/`++`.

Headline results, keyed to the task:

  (1) `set_idem`        — `set n v ; set n v = set n v`;
      `get_set_eq`      — `get n (set n v h) = some v`.
  (2) `get_remove_eq`   — `get n (remove n h) = none`;
      `remove_idem`     — `remove n ; remove n = remove n`.
  (3) `remove_set`      — `set n v ; remove n = remove n` (remove dominates a
                          prior set of the same name).
  (4) distinct-name commutation:
      `remove_comm`      — `remove` on any two names commutes (unconditional);
      `set_set_comm`, `set_remove_comm`, `add_add_comm` — on *distinct* names,
      the two orders are observationally equal (agree on every `get`).
  (6) `run` is total and deterministic: `run_total`, `run_deterministic`,
      `run_functional`, plus the sequencing identities `run_nil/cons/append`.

The commutation results for `set`/`add` are stated observationally (agree on
every lookup) rather than as list equality on purpose: `set`/`add` append, so
two independent writes land in list order, and only their *observable* effect —
what `get` returns — is order-independent.  For `remove` the stronger list
equality holds and is proved directly.
-/

import Header.Basic

namespace Header

/-! ### Structural `remove` facts -/

theorem remove_append (n : Name) (a b : Headers) :
    remove n (a ++ b) = remove n a ++ remove n b := by
  simp only [remove, List.filter_append]

theorem remove_singleton_self (n : Name) (v : Value) : remove n [⟨n, v⟩] = [] := by
  simp [remove, nameEqb_refl]

/-- **(2) `remove` is idempotent.** -/
theorem remove_idem (n : Name) (h : Headers) : remove n (remove n h) = remove n h := by
  simp only [remove, List.filter_filter, Bool.and_self]

/-- **(3)**  A `set n` followed by `remove n` equals `remove n` alone: the
remove erases the value the set had installed. -/
theorem remove_set (n : Name) (v : Value) (h : Headers) :
    remove n (set n v h) = remove n h := by
  unfold set
  rw [remove_append, remove_idem, remove_singleton_self, List.append_nil]

/-! ### (1) `set` idempotence and set-then-get -/

/-- **(1) set-then-get.**  Reading the name just set returns the set value. -/
theorem get_set_eq (n : Name) (v : Value) (h : Headers) : get n (set n v h) = some v := by
  rw [get_set]; simp

/-- **(1) `set` is idempotent.** -/
theorem set_idem (n : Name) (v : Value) (h : Headers) :
    set n v (set n v h) = set n v h := by
  show remove n (set n v h) ++ [⟨n, v⟩] = remove n h ++ [⟨n, v⟩]
  rw [remove_set]

/-! ### (2) remove-then-get -/

/-- **(2) remove-then-get.**  Reading a removed name returns absent. -/
theorem get_remove_eq (n : Name) (h : Headers) : get n (remove n h) = none := by
  rw [get_remove]; simp

/-! ### (4) commutation on distinct names -/

/-- **(4) `remove` commutes** — unconditionally, on any two names. -/
theorem remove_comm (n1 n2 : Name) (h : Headers) :
    remove n1 (remove n2 h) = remove n2 (remove n1 h) := by
  simp only [remove, List.filter_filter]
  congr 1
  funext f
  exact Bool.and_comm _ _

/-- **(4) two `set`s on distinct names commute** (observationally). -/
theorem set_set_comm (n1 : Name) (v1 : Value) (n2 : Name) (v2 : Value) (h : Headers)
    (hne : nameEqb n1 n2 = false) (m : Name) :
    get m (set n2 v2 (set n1 v1 h)) = get m (set n1 v1 (set n2 v2 h)) := by
  simp only [get_set]
  by_cases h1 : nameEqb n1 m = true
  · by_cases h2 : nameEqb n2 m = true
    · exact absurd (nameEqb_trans h1 (nameEqb_symm h2)) (name_neq hne)
    · simp [h1, eq_false_of_ne_true h2]
  · by_cases h2 : nameEqb n2 m = true
    · simp [eq_false_of_ne_true h1, h2]
    · simp [eq_false_of_ne_true h1, eq_false_of_ne_true h2]

/-- **(4) a `set` and a `remove` on distinct names commute** (observationally). -/
theorem set_remove_comm (n1 : Name) (v1 : Value) (n2 : Name) (h : Headers)
    (hne : nameEqb n1 n2 = false) (m : Name) :
    get m (remove n2 (set n1 v1 h)) = get m (set n1 v1 (remove n2 h)) := by
  simp only [get_remove, get_set]
  by_cases h1 : nameEqb n1 m = true
  · by_cases h2 : nameEqb n2 m = true
    · exact absurd (nameEqb_trans h1 (nameEqb_symm h2)) (name_neq hne)
    · simp [h1, eq_false_of_ne_true h2]
  · by_cases h2 : nameEqb n2 m = true
    · simp [eq_false_of_ne_true h1, h2]
    · simp [eq_false_of_ne_true h1, eq_false_of_ne_true h2]

/-- **(4) two `add`s on distinct names commute** (observationally). -/
theorem add_add_comm (n1 : Name) (v1 : Value) (n2 : Name) (v2 : Value) (h : Headers)
    (hne : nameEqb n1 n2 = false) (m : Name) :
    get m (add n2 v2 (add n1 v1 h)) = get m (add n1 v1 (add n2 v2 h)) := by
  simp only [add, get_append, get_singleton]
  by_cases h1 : nameEqb n1 m = true
  · by_cases h2 : nameEqb n2 m = true
    · exact absurd (nameEqb_trans h1 (nameEqb_symm h2)) (name_neq hne)
    · cases hgh : get m h <;> simp [h1, eq_false_of_ne_true h2]
  · by_cases h2 : nameEqb n2 m = true
    · cases hgh : get m h <;> simp [eq_false_of_ne_true h1, h2]
    · cases hgh : get m h <;> simp [eq_false_of_ne_true h1, eq_false_of_ne_true h2]

/-! ### (6) a rewrite program: total and deterministic -/

/-- One rewrite operation. -/
inductive Op where
  | set (n : Name) (v : Value)
  | remove (n : Name)
  | add (n : Name) (v : Value)
  | hop (names : List Name)
deriving Repr

/-- Interpret one operation. -/
def applyOp : Op → Headers → Headers
  | .set n v, h => set n v h
  | .remove n, h => remove n h
  | .add n v, h => add n v h
  | .hop names, h => strip names h

/-- A rewrite program is an ordered list of operations, applied left-to-right. -/
def run (prog : List Op) (h : Headers) : Headers :=
  prog.foldl (fun acc o => applyOp o acc) h

@[simp] theorem run_nil (h : Headers) : run [] h = h := rfl

/-- Sequencing: running `o :: rest` is `o` first, then `rest`. -/
theorem run_cons (o : Op) (p : List Op) (h : Headers) :
    run (o :: p) h = run p (applyOp o h) := by
  simp [run, List.foldl_cons]

/-- Programs compose by concatenation: run `p`, then run `q`. -/
theorem run_append (p q : List Op) (h : Headers) :
    run (p ++ q) h = run q (run p h) := by
  simp [run, List.foldl_append]

/-- **(6) totality.**  Every operation returns a header list on every input. -/
theorem applyOp_total (o : Op) (h : Headers) : ∃ r, applyOp o h = r := ⟨_, rfl⟩

/-- **(6) totality.**  Every program returns a header list on every input —
no `partial`, no fuel, no failure mode. -/
theorem run_total (p : List Op) (h : Headers) : ∃ r, run p h = r := ⟨_, rfl⟩

/-- **(6) determinism.**  A program maps each input to a single output. -/
theorem run_deterministic {p : List Op} {h : Headers} {r1 r2 : Headers}
    (h1 : run p h = r1) (h2 : run p h = r2) : r1 = r2 := by
  rw [← h1, ← h2]

/-- **(6) total + deterministic in one statement:** the output is the unique
value the program yields on the input. -/
theorem run_functional (p : List Op) (h : Headers) :
    ∃ r, run p h = r ∧ ∀ r', run p h = r' → r = r' :=
  ⟨run p h, rfl, fun _ hr => hr⟩

end Header
