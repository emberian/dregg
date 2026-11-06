/-
# `lake exe dfa-run`: the flat-table DFA runner (absence-receipt demo)

    dfa-run <table.json> <document>                    -- prints ACCEPT or REJECT, exit 0
    dfa-run <table.json> --corpus <root> <manifest>    -- one relative path per manifest line

Corpus mode prints one JSON object: the table's well-formedness and dead-sink checks, the number
of documents and bytes read, the number the table ACCEPTS, the number it REJECTS (`count`), and
the indices of the rejected documents. Exit 0 when the table is well formed, 1 otherwise, 2 on bad
input. The verdict per document is `Dregg2.Automata.TableRun.acceptsBytes`, which
`TableRunSpec.accepts_iff` proves equal to `Deriv.PredRE.TableDfa.accepts` on the document's bytes.
-/
import Dregg2.Automata.TableRun

open Dregg2.Automata.TableRun
open Lean (Json)

def loadTable (path : String) : IO FlatTable := do
  let s ← IO.FS.readFile path
  match Json.parse s >>= FlatTable.ofJson with
  | .ok t => pure t
  | .error e => throw (IO.userError s!"dfa-run: cannot read table {path}: {e}")

def runCorpus (t : FlatTable) (root manifest : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile manifest).splitOn "\n" |>.filter (· ≠ "")
  let mut n : Nat := 0
  let mut bytes : Nat := 0
  let mut accepted : Nat := 0
  let mut rejected : Array Nat := #[]
  for rel in lines do
    let doc ← IO.FS.readBinFile (root ++ "/" ++ rel)
    bytes := bytes + doc.size
    if acceptsBytes t doc then accepted := accepted + 1 else rejected := rejected.push n
    n := n + 1
  let out := Json.mkObj
    [ ("table_well_formed", Json.bool t.wellFormed)
    , ("dead_state_is_sink", Json.bool t.deadIsSink)
    , ("num_states", Lean.toJson t.numStates)
    , ("documents", Lean.toJson n)
    , ("bytes", Lean.toJson bytes)
    , ("accepted", Lean.toJson accepted)
    , ("count", Lean.toJson rejected.size)
    , ("rejected_indices", Lean.toJson rejected) ]
  IO.println out.compress
  return if t.wellFormed then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [table, "--corpus", root, manifest] => runCorpus (← loadTable table) root manifest
  | [table, doc] =>
      let t ← loadTable table
      let bs ← IO.FS.readBinFile doc
      IO.println (if acceptsBytes t bs then "ACCEPT" else "REJECT")
      return 0
  | _ =>
      IO.eprintln "usage: dfa-run <table.json> <document> | dfa-run <table.json> --corpus <root> <manifest>"
      return 2
