/-
# Dregg2.Automata.TableRun: the executable flat-table DFA runner

The runner behind `lake exe dfa-run` (root `DfaRun.lean`, the absence-receipt demo
`demo/absence-receipt/`). It reads a flat transition table in the `dfa` crate's serde shape
(`num_states`, `transitions[state * 256 + byte]`, `start`, `accepting`) and folds it over a
document's bytes.

This module imports Lean core only, so the executable links without compiling Mathlib to native
code. The statement that this fold IS the house DFA object lives in `TableRunSpec.lean`
(`runFrom_eq_runState`, `accepts_iff`), which imports the derivative tower and is checked by
`lake env lean`; the executable runs exactly the constants that file is about.

Out-of-range indices step to state 0 (the `dfa` crate's dead state). The Rust runtime's early exit
on the dead state agrees with this fold exactly when state 0 is a non-accepting sink, which
`FlatTable.deadIsSink` checks and `dfa-run` prints.
-/
import Lean.Data.Json

namespace Dregg2.Automata.TableRun

/-- `compiler.rs::Dfa` on the wire. -/
structure FlatTable where
  numStates : Nat
  transitions : Array Nat
  start : Nat
  accepting : List Nat
  deriving Repr

namespace FlatTable

/-- One transition: `transitions[s * 256 + b]`, state 0 when out of range. -/
def step (t : FlatTable) (s : Nat) (b : UInt8) : Nat :=
  t.transitions.getD (s * 256 + b.toNat) 0

/-- `accepting.contains`. -/
def isAccepting (t : FlatTable) (s : Nat) : Bool := t.accepting.contains s

/-- The table is total over its states: exactly `numStates * 256` entries, each `< numStates`. -/
def wellFormed (t : FlatTable) : Bool :=
  t.transitions.size == t.numStates * 256 && t.transitions.all (· < t.numStates)
    && t.start < t.numStates

/-- State 0 loops to itself on every byte and does not accept. -/
def deadIsSink (t : FlatTable) : Bool :=
  (List.range 256).all (fun b => t.step 0 (UInt8.ofNat b) == 0) && !t.isAccepting 0

end FlatTable

/-- The specification fold over a list of bytes. -/
def runFrom (t : FlatTable) (q : Nat) (w : List UInt8) : Nat := w.foldl t.step q

/-- The executable fold over an array of bytes (the hot loop of `dfa-run`). -/
def runArray (t : FlatTable) (q : Nat) (a : Array UInt8) : Nat := a.foldl t.step q

theorem runArray_eq_runFrom (t : FlatTable) (q : Nat) (a : Array UInt8) :
    runArray t q a = runFrom t q a.toList := by
  simp only [runArray, runFrom, Array.foldl_toList]

/-- The verdict on one document: does the run from `start` end in an accepting state. -/
def acceptsBytes (t : FlatTable) (bs : ByteArray) : Bool :=
  t.isAccepting (runArray t t.start bs.data)

theorem acceptsBytes_eq (t : FlatTable) (bs : ByteArray) :
    acceptsBytes t bs = t.isAccepting (runFrom t t.start bs.data.toList) := by
  simp only [acceptsBytes, runArray_eq_runFrom]

/-! ## Reading the table -/

open Lean (Json)

private def natField (j : Json) (k : String) : Except String Nat := do
  let v ← j.getObjVal? k
  v.getNat?

private def natArray (j : Json) (k : String) : Except String (Array Nat) := do
  let v ← j.getObjVal? k
  let arr ← v.getArr?
  arr.mapM (·.getNat?)

/-- Parse the `dfa` crate's serde JSON for `Dfa`. -/
def FlatTable.ofJson (j : Json) : Except String FlatTable := do
  return { numStates := (← natField j "num_states")
           transitions := (← natArray j "transitions")
           start := (← natField j "start")
           accepting := (← natArray j "accepting").toList }

/-! ## Non-vacuity: a two-state table that rejects exactly the words containing byte 0x41. -/

/-- States: 0 dead, 1 clean (accepting), 2 seen 'A' (rejecting sink). -/
def noA : FlatTable :=
  { numStates := 3
    transitions := (Array.replicate 256 0)
      ++ (Array.ofFn (n := 256) fun b => if b.val = 0x41 then 2 else 1)
      ++ Array.replicate 256 2
    start := 1
    accepting := [1] }

#guard noA.wellFormed
#guard noA.deadIsSink
#guard acceptsBytes noA "hello".toUTF8
#guard !acceptsBytes noA "xxAxx".toUTF8
#guard acceptsBytes noA ByteArray.empty
#guard runArray noA 1 "BA".toUTF8.data = 2

end Dregg2.Automata.TableRun
