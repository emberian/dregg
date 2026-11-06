/-
# `lake exe tree-check`: the extracted tree-certificate checker (initiative 12)

    tree-check verify <cert.json>        check a schema / field / corpus certificate; exit 0 accept,
                                         1 refuse, 2 malformed input
    tree-check project <record.json>     the Lean projection of one JSON text: canonical CBOR hex,
                                         tree root, flat digest (the Rust producer's conformance target)
    tree-check flat <value.json>         the flat digest of a JSON value (schemas, tables)

The verdicts are `Dregg2.Tree.schemaCheck` / `fieldCheck` / `corpusCheck`, instantiated with
`Merkle.shakeH`, `Instance.flatF` and `Instance.mmrHash`. Their soundness theorems are
`schema_sound`, `path_pattern_sound`, `corpus_count_sound` (Cert.lean) and `corpus_absence`
(Spec.lean). Every value inside a certificate is canonical CBOR read by the proved
`ofCanonicalBytes`; the JSON envelope around it is read by `Lean.Json` (unverified, outside the
theorems; a malformed envelope is exit 2, never an accept).
-/
import Dregg2.Tree.Instance
import Dregg2.Tree.Json

open Lean (Json)
open Dregg2.Tree
open Dregg2.Tree.Instance

def H : List UInt8 → Digest := shakeH
def F : List UInt8 → Digest := flatF

def pathStr (p : Path) : String :=
  "/" ++ "/".intercalate (p.map fun
    | .key k => (String.fromUTF8? (ByteArray.mk k.toArray)).getD (toHex k)
    | .idx i => toString i)

/-- What the checker did, in substrate-neutral units. -/
structure Tally where
  frames : Nat := 0
  frameBytes : Nat := 0
  keccakF : Nat := 0
  dfaBytes : Nat := 0
  nodesDisclosed : Nat := 0

def Tally.frame (t : Tally) (n : Nat) : Tally :=
  { t with frames := t.frames + 1, frameBytes := t.frameBytes + n,
           keccakF := t.keccakF + keccakFOf (nodePrefixLen + n) }

def tallyOpening : Tally → Opening → Tally
  | t, .here v =>
    let c := counts H v
    { t with frames := t.frames + c.nodes, frameBytes := t.frameBytes + c.frameBytes,
             keccakF := t.keccakF + c.keccakF, nodesDisclosed := t.nodesDisclosed + c.nodes }
  | t, .arr ds rest => tallyOpening (t.frame (Frame.arr ds).bytes.length) rest
  | t, .obj es rest => tallyOpening (t.frame (Frame.obj es).bytes.length) rest
  | t, .absentArr ds => t.frame (Frame.arr ds).bytes.length
  | t, .absentObj es => t.frame (Frame.obj es).bytes.length

def tallyJson (t : Tally) : Json := Json.mkObj
  [ ("frames_hashed", Lean.toJson t.frames), ("frame_bytes", Lean.toJson t.frameBytes)
  , ("keccak_f", Lean.toJson t.keccakF), ("nodes_disclosed", Lean.toJson t.nodesDisclosed) ]

def verify (j : Json) : Except String (Bool × Json) := do
  let sj ← j.getObjVal? "statement"
  let rc ← j.getObjVal? "receipt"
  match ← getStr sj "kind" with
  | "schema" =>
    let tr ← getHex sj "tree_root"
    let sd ← getHex sj "schema_digest"
    let vd ← (← sj.getObjVal? "verdict").getBool?
    let stmt : SchemaStmt := ⟨tr, sd, vd⟩
    let tree ← valueOfHex (← getStr rc "tree")
    let sch ← valueOfHex (← getStr rc "schema")
    let run ← runOfJson (← rc.getObjVal? "run")
    let r : SchemaReceipt := ⟨tree, sch, run⟩
    let ok := schemaCheck H F stmt r
    let c := counts H r.tree
    pure (ok, Json.mkObj [("kind", "schema"), ("tree_root", toHex stmt.treeRoot),
      ("schema_digest", toHex stmt.schemaDigest), ("verdict", Json.bool stmt.verdict),
      ("accepted", Json.bool ok), ("nodes", Lean.toJson c.nodes), ("edges", Lean.toJson c.edges),
      ("leaves", Lean.toJson c.leaves), ("string_bytes", Lean.toJson c.strBytes),
      ("frame_bytes", Lean.toJson c.frameBytes), ("keccak_f", Lean.toJson c.keccakF)])
  | "field" =>
    let tr ← getHex sj "tree_root"
    let p ← pathOfJson (← sj.getObjVal? "path")
    let td ← getHex sj "table_digest"
    let vd ← verdictOfStr (← getStr sj "verdict")
    let stmt : FieldStmt := ⟨tr, p, td, vd⟩
    let op ← openingOfJson (← rc.getObjVal? "opening")
    let tab ← valueOfHex (← getStr rc "table")
    let r : FieldReceipt := ⟨op, tab⟩
    let ok := fieldCheck H F stmt r
    pure (ok, Json.mkObj [("kind", "field"), ("tree_root", toHex stmt.treeRoot),
      ("path", pathStr stmt.path), ("table_digest", toHex stmt.tableDigest),
      ("verdict", verdictStr stmt.verdict), ("accepted", Json.bool ok),
      ("work", tallyJson (tallyOpening {} r.opening))])
  | "corpus" =>
    let q ← (← getArr sj "query").toList.mapM fun c => do
      let p ← pathOfJson (← c.getObjVal? "path")
      let td ← getHex c "table_digest"
      pure (⟨p, td⟩ : Conjunct)
    let rootBytes ← getHex sj "mmr_root"
    let n ← getNat sj "n"
    let cnt ← getNat sj "count"
    let stmt : CorpusStmt := ⟨(Cbor.ofBE rootBytes : Int), n, q, cnt⟩
    let tables ← (← getArr rc "tables").toList.mapM fun t => do valueOfHex (← t.getStr?)
    let recs ← (← getArr rc "records").toList.mapM evidenceOfJson
    let r : CorpusReceipt := ⟨tables, recs⟩
    let ok := corpusCheck H F mmrHash stmt r
    let work := recs.foldl (fun t ev => match ev with
      | .refute _ _ op => tallyOpening t op
      | .full _ ops => ops.foldl tallyOpening t) {}
    let refuted := recs.filter fun | .refute .. => true | _ => false
    pure (ok, Json.mkObj [("kind", "corpus"), ("mmr_root", toHex rootBytes), ("n", Lean.toJson stmt.n),
      ("query", Json.arr (q.map fun c => Json.mkObj [("path", pathStr c.path),
        ("table_digest", toHex c.tableDigest)]).toArray),
      ("count", Lean.toJson stmt.count), ("accepted", Json.bool ok),
      ("records_refuted", Lean.toJson refuted.length),
      ("records_matching_disclosed", Lean.toJson (recs.length - refuted.length)),
      ("mmr_hashes", Lean.toJson (2 * recs.length)), ("work", tallyJson work)])
  | k => throw s!"statement kind {k}"

def readJsonText (path : String) : IO (List UInt8) := do
  pure (← IO.FS.readBinFile path).data.toList

def main (args : List String) : IO UInt32 := do
  match args with
  | ["verify", path] =>
    match Json.parse (← IO.FS.readFile path) with
    | .error e => IO.eprintln s!"tree-check: {e}"; return 2
    | .ok j => match verify j with
      | .error e => IO.eprintln s!"tree-check: malformed certificate: {e}"; return 2
      | .ok (ok, out) =>
        IO.println out.pretty
        IO.println (if ok then "ACCEPT" else "REFUSE")
        return if ok then 0 else 1
  | ["project", path] =>
    match Dregg2.Tree.Json.parse (← readJsonText path) with
    | none => IO.eprintln "tree-check: not JSON in the model (strict RFC 8259, no duplicate keys)"; return 2
    | some v =>
      IO.println (Json.mkObj [("cbor", toHex (encode v)), ("tree_root", toHex (digest H v)),
        ("flat_digest", toHex (flatDigest F v))]).compress
      return 0
  | ["flat", path] =>
    match Dregg2.Tree.Json.parse (← readJsonText path) with
    | none => IO.eprintln "tree-check: not JSON in the model"; return 2
    | some v => IO.println (toHex (flatDigest F v)); return 0
  | _ =>
    IO.eprintln "usage: tree-check verify <cert.json> | project <record.json> | flat <value.json>"
    return 2
