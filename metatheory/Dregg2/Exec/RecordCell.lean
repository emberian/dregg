/-
# Dregg2.Exec.RecordCell — the RecordProgram as the *executable* structure-map arrow.

`dregg2 §1.5` / `cand-A`: **the CellProgram IS the coalgebra structure-map** — the
`AdmissibleTurn ⇒ Cell` arrow of the final coalgebra `νF, F X = Obs × (AdmissibleTurn ⇒ X)`.
The previous build (`Exec/Program.lean`) realized `RecordProgram.admits` as a *flat* Boolean
admissibility checker — the *domain predicate* of the arrow — but left it dead: nothing on the
other side, no actual transition it gates. This module makes it the genuine **DOMAIN FILTER of a
real executable record-cell transition**: a small record-update operation produces a *candidate*
next state, and the `RecordProgram` decides — fail-closed — whether that candidate commits.

The shape is exactly the structure-map arrow `step : old → Obs × (op ⇒ new?)`, projected to the
single transition: `recExec prog old op : Option Value`. The `Option` IS the partiality of the
arrow — `none` is "the structure-map rejects this turn" (default-deny / a constraint failed), and
`some new` is a committed point in the codomain. The **keystone** (`recExec_admitted`) is the
executable `denote`-only-tightens fact: *nothing commits that the structure-map rejects* — every
committed transition was genuinely admitted by the program. This is the record-cell shadow of
`Exec/StepComplete.lean`'s `cexec_attests`: the program **genuinely gates the arrow**.

We then prove the structure-map's constraint *genuinely holds post-commit* for a concrete program
(`monotonic "count"`): a committed transition really does satisfy `new.count ≥ old.count`. The
op-application is total and computable; admissibility is the only gate. Pure, `#eval`-able;
imports only `Exec.Program` (which pulls `Exec.Value`), so it type-checks fast.
-/
import Dregg2.Exec.Program

namespace Dregg2.Exec.RecordCell

open Dregg2.Exec

/-! ## `RecOp` — a small, total record-update operation (the raw turn payload). -/

/-- **A record-update operation** — the un-gated content of a turn. Either set a named scalar
field to a value, or add a signed delta to a named scalar field. Deliberately tiny: the point is
not a rich op language but that *any* candidate next-state must still pass the program's filter to
commit. (A richer op set is a later extension; the gating discipline is identical.) -/
inductive RecOp where
  /-- `new[field] := value` (overwrite a scalar field). -/
  | setScalar (field : FieldName) (value : Int)
  /-- `new[field] := old[field] + delta` (increment/decrement a scalar field; absent ⇒ delta). -/
  | addScalar (field : FieldName) (delta : Int)
  deriving Repr

/-! ## `setField` / `applyOp` — total, computable state transition (no gating yet). -/

/-- Set the named field of a record's field-list to `v`, overwriting in place if present,
appending otherwise. Total and order-preserving on existing keys. -/
def setFieldList : List (FieldName × Value) → FieldName → Value → List (FieldName × Value)
  | [],                f, v => [(f, v)]
  | (k, x) :: rest,    f, v => if k == f then (k, v) :: rest
                              else (k, x) :: setFieldList rest f v

/-- **`setField rec f v`** — return `rec` with field `f` set to `v` (record case only; a
non-record value is replaced by a singleton record, keeping the function total). -/
def setField : Value → FieldName → Value → Value
  | .record fs, f, v => .record (setFieldList fs f v)
  | _,          f, v => .record [(f, v)]

/-- **`applyOp old op`** — the candidate next state from applying `op` to `old`. Total and
computable; this is the *raw* arrow, before the program filters it. A `setScalar` overwrites; an
`addScalar` reads the old scalar (defaulting an absent/ill-typed field to `0`) and writes the
sum. -/
def applyOp (old : Value) : RecOp → Value
  | .setScalar f val => setField old f (.int val)
  | .addScalar f d   => setField old f (.int ((old.scalar f).getD 0 + d))

/-! ### `setField` reads back: the field we set holds exactly what we set (the witness lemma). -/

/-- After `setFieldList`, looking up the set field returns exactly the set value. -/
theorem setFieldList_find_self (fs : List (FieldName × Value)) (f : FieldName) (v : Value) :
    (setFieldList fs f v).find? (fun p => p.1 == f) = some (f, v) := by
  induction fs with
  | nil => simp [setFieldList]
  | cons hd tl ih =>
      obtain ⟨k, x⟩ := hd
      simp only [setFieldList]
      by_cases hk : (k == f) = true
      · rw [if_pos hk]
        rw [List.find?_cons_of_pos (by simpa using hk)]
        simp only [beq_iff_eq] at hk; rw [hk]
      · have hkf : (k == f) = false := by simpa using hk
        rw [if_neg hk, List.find?_cons_of_neg (by simpa using hkf)]
        exact ih

/-- **`setField_scalar_self` (PROVED)** — reading the scalar we just set returns exactly it. The
record-cell write/read law: `applyOp` puts the intended value on the intended field. -/
theorem setField_scalar_self (old : Value) (f : FieldName) (val : Int) :
    (setField old f (.int val)).scalar f = some val := by
  cases old with
  | record fs =>
      simp only [setField, Value.scalar, Value.field, setFieldList_find_self fs f (.int val),
        Option.map_some]
  | int _  => simp [setField, Value.scalar, Value.field]
  | dig _  => simp [setField, Value.scalar, Value.field]
  | sym _  => simp [setField, Value.scalar, Value.field]

/-! ## `recExec` — the GATED arrow: apply, then commit ONLY if the program admits. -/

/-- **`recExec prog method old op` (the executable structure-map arrow).** Compute the candidate
`new = applyOp old op`, and **commit it (`some new`) iff `prog.admits method old new`**; otherwise
**`none`** (fail-closed). The `RecordProgram` is the admissibility filter = the *domain* of the
structure-map arrow; this is the arrow itself, projected to one turn. `none` = the structure-map
rejects the turn (a constraint failed, or default-deny). -/
def recExec (prog : RecordProgram) (method : Nat) (old : Value) (op : RecOp) : Option Value :=
  let new := applyOp old op
  if prog.admits method old new = true then some new else none

/-! ## THE KEYSTONE — the program genuinely gates the arrow. -/

/-- **`recExec_admitted` (THE KEYSTONE — PROVED).** A committed transition was *admitted* by the
program: if `recExec prog method old op = some new`, then `prog.admits method old new = true`.
Nothing commits that the structure-map rejects — the program genuinely gates the arrow. This is
the executable `denote`-only-tightens fact for the record cell (the `cexec_attests` shadow at the
single-transition tier): the domain filter is *load-bearing*, never bypassed. -/
theorem recExec_admitted
    {prog : RecordProgram} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    (h : recExec prog method old op = some new) :
    prog.admits method old new = true := by
  unfold recExec at h
  by_cases ha : prog.admits method old (applyOp old op) = true
  · rw [if_pos ha, Option.some.injEq] at h
    rw [← h]; exact ha
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-- **`recExec_commits_applyOp` (PROVED)** — a committed transition commits exactly the candidate
the op produced (no silent rewriting between apply and commit). Together with `recExec_admitted`
this fully characterizes a commit: `new = applyOp old op` *and* `admits old new`. -/
theorem recExec_commits_applyOp
    {prog : RecordProgram} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    (h : recExec prog method old op = some new) :
    new = applyOp old op := by
  unfold recExec at h
  by_cases ha : prog.admits method old (applyOp old op) = true
  · rw [if_pos ha, Option.some.injEq] at h; exact h.symm
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-- **`recExec_some_iff_admits` (PROVED)** — the arrow commits *iff* the candidate is admitted:
`recExec` succeeds exactly on the admitted candidate. (`recExec_admitted` is the ⟸-soundness; this
is the full ⇔ characterization of the domain.) -/
theorem recExec_some_iff_admits
    (prog : RecordProgram) (method : Nat) (old : Value) (op : RecOp) :
    (∃ new, recExec prog method old op = some new)
      ↔ prog.admits method old (applyOp old op) = true := by
  unfold recExec
  constructor
  · rintro ⟨new, h⟩
    by_cases ha : prog.admits method old (applyOp old op) = true
    · exact ha
    · rw [if_neg ha] at h; exact absurd h (by simp)
  · intro ha
    exact ⟨applyOp old op, by rw [if_pos ha]⟩

/-! ## The constraint genuinely holds post-commit — a concrete program (`monotonic "count"`). -/

/-- A monotonic-counter program: `count` only ever increases (`new.count ≥ old.count`). The
canonical living-cell example — the same `counterProgram` shape as `Exec/Program.lean`, here the
body of a *gated arrow*. -/
def monoCountProgram : RecordProgram := .predicate [.simple (.monotonic "count")]

/-- **`recExec_mono_holds` (PROVED)** — for the `monotonic "count"` program, a *committed*
transition genuinely satisfies the constraint: the new `count` is ≥ the old `count`, and both are
present scalars. This is the structure-map's declared constraint *holding on the committed codomain
point* — the filter is not merely consulted, its predicate is true of every state that gets
through. (We reason from `admits = true` back through `evalConstraint`/`evalSimple` to recover the
honest `Int` inequality `a ≤ b`.) -/
theorem recExec_mono_holds
    {method : Nat} {old : Value} {op : RecOp} {new : Value}
    (h : recExec monoCountProgram method old op = some new) :
    ∃ a b, old.scalar "count" = some a ∧ new.scalar "count" = some b ∧ a ≤ b := by
  have hadm : monoCountProgram.admits method old new = true := recExec_admitted h
  -- `admits (.predicate [monotonic "count"]) = (monotonic-"count" check on old/new)`.
  simp only [monoCountProgram, RecordProgram.admits, List.all_cons, List.all_nil, Bool.and_true,
    evalConstraint, evalSimple] at hadm
  -- `hadm` is now the `match old.scalar, new.scalar with | some a, some b => decide (a ≤ b) | _ => false`.
  cases hoa : old.scalar "count" with
  | none => rw [hoa] at hadm; simp at hadm
  | some a =>
      cases hnb : new.scalar "count" with
      | none => rw [hoa, hnb] at hadm; simp at hadm
      | some b =>
          rw [hoa, hnb] at hadm
          exact ⟨a, b, rfl, rfl, of_decide_eq_true hadm⟩

/-! ## `#eval` demos — a counter cell: increment commits, decrement is rejected (fail-closed). -/

/-- A counter record sitting at `count = 5`. -/
def counterCell : Value := .record [("count", .int 5)]

-- Incrementing by 1 ⇒ candidate `count = 6 ≥ 5` ⇒ admitted ⇒ commits.
#eval recExec monoCountProgram 0 counterCell (.addScalar "count" 1)    -- some (record [("count", int 6)])
-- Decrementing by 2 ⇒ candidate `count = 3 ≥ 5`? no ⇒ rejected ⇒ none (fail-closed).
#eval recExec monoCountProgram 0 counterCell (.addScalar "count" (-2)) -- none
-- `setScalar` to a higher value commits; to a lower value is rejected.
#eval recExec monoCountProgram 0 counterCell (.setScalar "count" 9)    -- some (record [("count", int 9)])
#eval recExec monoCountProgram 0 counterCell (.setScalar "count" 2)    -- none
-- The terminal program `.none` admits every candidate — the op always commits.
#eval recExec .none 0 counterCell (.addScalar "count" (-100))          -- some (record [("count", int -95)])
-- A `circuit` program admits nothing in the pure evaluator (needs its proof) ⇒ always none.
#eval recExec (.circuit 7) 0 counterCell (.addScalar "count" 1)        -- none

end Dregg2.Exec.RecordCell
