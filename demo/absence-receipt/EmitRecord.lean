/-
EmitRecord.lean: emit ONE document's run as a descriptor of the served table-routing family.

    cd metatheory
    lake env lean --run ../demo/absence-receipt/EmitRecord.lean <table.json> <document> <out.json>

The descriptor is `DfaRoutingTableRoute8.tableRoutingBoundDesc name rows` with `rows` the document's run
`[state, byte, next]` under the table (the same `FlatTable.step` the `dfa-run` verdict folds), so
the declared transition multiset is public in the descriptor. The eight-lane route and public
length bind traversal order; the Rust proof test constructs these extra witness columns with the
shared route-chain helper. This is one record's evidence, not a corpus proof. The by-name object
`dregg-dfa-routing-table::route8-bound-v1` is the same family with a small demo table.
Prints: rows, final state, whether it accepts, and the descriptor's width/constraints/tables.
-/
import Dregg2.Automata.TableRun
import Dregg2.Circuit.Emit.DfaRoutingTableRoute8

open Dregg2.Automata.TableRun
open Dregg2.Circuit.Emit.DfaRoutingTableRoute8
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
    let d := tableRoutingBoundDesc "dregg-dfa-routing-table::absence-record-route8-v1" rows
    IO.FS.writeFile outPath (emitVmJson2 d)
    IO.println (Json.mkObj
      [ ("rows", Lean.toJson rows.length), ("start", Lean.toJson t.start)
      , ("final", Lean.toJson final), ("accepts", Json.bool (acceptsBytes t doc))
      , ("trace_width", Lean.toJson d.traceWidth), ("pi_count", Lean.toJson d.piCount)
      , ("constraints", Lean.toJson d.constraints.length)
      , ("tables", Lean.toJson d.tables.length) ]).compress
    return 0
  | _ => IO.eprintln "usage: EmitRecord <table.json> <document> <out.json>"; return 2
