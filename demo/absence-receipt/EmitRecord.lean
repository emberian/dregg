/-
EmitRecord.lean: emit ONE document's run as a descriptor of the served table-routing family.

    cd metatheory
    lake env lean --run ../demo/absence-receipt/EmitRecord.lean <table.json> <document> <out.json>

The descriptor is `DfaRoutingTableEmit.tableRoutingDesc name rows` with `rows` the document's run
`[state, byte, next]` under the table (the same `FlatTable.step` the `dfa-run` verdict folds), so
the run is public in the descriptor itself: this is the served shape's evidence on one record,
not a private-word proof. The by-name object `dregg-dfa-routing-table::exact-public-v1` is this
family at the one-row demo table; the record's object differs only in its rows and name.
Prints: rows, final state, whether it accepts, and the descriptor's width/constraints/tables.
-/
import Dregg2.Automata.TableRun
import Dregg2.Circuit.Emit.DfaRoutingTableEmit

open Dregg2.Automata.TableRun
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Lean (Json)

def runRows (t : FlatTable) (q : Nat) : List UInt8 → List (List Nat)
  | [] => []
  | b :: bs => [q, b.toNat, t.step q b] :: runRows t (t.step q b) bs

def main (args : List String) : IO UInt32 := do
  match args with
  | [tablePath, docPath, outPath] =>
    let t ← match Json.parse (← IO.FS.readFile tablePath) >>= FlatTable.ofJson with
      | .ok t => pure t
      | .error e => throw (IO.userError e)
    let doc ← IO.FS.readBinFile docPath
    let rows := runRows t t.start doc.data.toList
    let final := runFrom t t.start doc.data.toList
    let d := tableRoutingDesc "dregg-dfa-routing-table::absence-record-v1" rows
    IO.FS.writeFile outPath (emitVmJson2 d)
    IO.println (Json.mkObj
      [ ("rows", Lean.toJson rows.length), ("start", Lean.toJson t.start)
      , ("final", Lean.toJson final), ("accepts", Json.bool (acceptsBytes t doc))
      , ("trace_width", Lean.toJson d.traceWidth), ("pi_count", Lean.toJson d.piCount)
      , ("constraints", Lean.toJson d.constraints.length)
      , ("tables", Lean.toJson d.tables.length) ]).compress
    return 0
  | _ => IO.eprintln "usage: EmitRecord <table.json> <document> <out.json>"; return 2
