/-
# Dregg2.Automata.TableRunSpec: `dfa-run` computes the house DFA object

`TableRun.runFrom` (the fold `lake exe dfa-run` executes, via `runArray_eq_runFrom`) is
`Deriv.PredRE.TableDfa.runState` on the table read as a `TableDfa Nat UInt8`, and `acceptsBytes`
is `TableDfa.accepts` on the document's bytes. For a non-empty document the verdict is also the
`Dfa.lean` relational `DfaAccepts` over the table's deterministic δ (`tableRun_dfaAccepts`).

What this does NOT say: anything about which language the table denotes. Whether the table is the
absence automaton of the policy (the padded complement of `.* P .*`) is the compiler's obligation:
`tableDfa_faithful`'s agreement premise for a Lean-compiled table, and unproved for the interim
Rust-compiled table the demo ships.
-/
import Dregg2.Automata.TableRun
import Dregg2.Crypto.Deriv.TableDfa

namespace Dregg2.Automata.TableRun

open Dregg2.Crypto.Deriv.PredRE (TableDfa)
open Dregg2.Crypto.Dfa (DfaAccepts)

/-- The flat table as the house object: total `step`, `start`, `accept := membership`. -/
def FlatTable.toTableDfa (t : FlatTable) : TableDfa Nat UInt8 :=
  { step := t.step, start := t.start, accept := fun s => t.isAccepting s = true }

theorem runFrom_eq_runState (t : FlatTable) (q : Nat) (w : List UInt8) :
    runFrom t q w = t.toTableDfa.runState q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a as ih => exact ih (t.step q a)

/-- The executable verdict is `TableDfa.accepts` on the document's bytes. -/
theorem accepts_iff (t : FlatTable) (bs : ByteArray) :
    acceptsBytes t bs = true ↔ t.toTableDfa.accepts bs.data.toList := by
  rw [acceptsBytes_eq, runFrom_eq_runState]
  rfl

/-- For a non-empty document the verdict is a `Dfa.lean` accepting run over the table's δ. -/
theorem accepts_iff_dfaAccepts (t : FlatTable) (bs : ByteArray) (a : UInt8) (as : List UInt8)
    (h : bs.data.toList = a :: as) :
    acceptsBytes t bs = true ↔
      DfaAccepts t.toTableDfa.δ t.toTableDfa.start t.toTableDfa.accept
        (t.toTableDfa.runTrace t.toTableDfa.start (a :: as)) := by
  rw [accepts_iff, h]
  exact (TableDfa.tableRun_dfaAccepts _ a as).symm

/-- Counting: the number of documents the table rejects, the receipt's `count`. -/
def rejectCount (t : FlatTable) (docs : List ByteArray) : Nat :=
  (docs.filter fun d => !acceptsBytes t d).length

theorem rejectCount_eq_zero_iff (t : FlatTable) (docs : List ByteArray) :
    rejectCount t docs = 0 ↔ ∀ d ∈ docs, t.toTableDfa.accepts d.data.toList := by
  simp only [rejectCount, List.length_eq_zero_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
    Bool.not_eq_false]
  constructor
  · intro h d hd
    exact (accepts_iff t d).mp (by simpa using h d hd)
  · intro h d hd
    simpa using (accepts_iff t d).mpr (h d hd)

#guard rejectCount noA ["ok".toUTF8, "fine".toUTF8] = 0
#guard rejectCount noA ["ok".toUTF8, "An A".toUTF8] = 1

#assert_all_clean [runFrom_eq_runState, accepts_iff, accepts_iff_dfaAccepts, rejectCount_eq_zero_iff,
  runArray_eq_runFrom, acceptsBytes_eq]

end Dregg2.Automata.TableRun
