/-
Arena — the runnable model harness (`arena-check`).

Reads one JSON document on stdin:

    {"input": [72, 84, 84, ...]}      -- the raw request bytes, 0..255

and writes the parsed arena view (or a typed non-result) as one JSON document
on stdout:

    {"status": "complete", "consumed": N,
     "request_line": {"method": "...", "target": "...", "version": "..."},
     "headers": [{"name": "...", "value": "...",
                  "name_range": {"off": N, "len": N},
                  "value_range": {"off": N, "len": N}}, ...],
     "arena": {"main_len": N, "sidecar_len": N,
               "entries": [{"tag": "...", "off": N, "len": N,
                            "sidecar": bool}, ...]}}

    {"status": "incomplete"}
    {"status": "error", "class": "...", "detail": "..."}

Every string in the output is produced by running the PROVEN-total
`Store.resolve` on the store the parser built, then decoding UTF-8 (which the
parser already checked per range). Header names are canonical (lowercase);
offsets ≥ 0x8000_0000 address the sidecar arena. Exit code 0 covers all three
statuses (they are all valid model outputs); exit code 1 means the harness
input itself was unusable.
-/
import Lean.Data.Json
import Arena.Basic
import Arena.Theorems
import Arena.Parse

open Lean (Json)

namespace Arena
namespace Check

/-- Resolve an entry through the model's total resolve and decode UTF-8. -/
def resolveString (s : Store) (e : Entry) : Option String :=
  (s.resolve e).bind fun b => String.fromUTF8? (ByteArray.mk b)

def spanJson (off len : Nat) : Json :=
  Json.mkObj [("off", Json.num off), ("len", Json.num len)]

def entryRangeJson (e : Entry) : Json :=
  spanJson e.off.toNat e.len.toNat

def tagString : NameTag → String
  | .method => "method"
  | .target => "target"
  | .version => "version"
  | .headerName => "header-name"
  | .headerValue => "header-value"

def entryJson (e : Entry) : Json :=
  Json.mkObj
    [ ("tag", Json.str (tagString e.tag))
    , ("off", Json.num e.off.toNat)
    , ("len", Json.num e.len.toNat)
    , ("sidecar", Json.bool e.inSidecar) ]

def headerJson (s : Store) (h : Parse.ParsedHeader) : Option Json := do
  let name ← resolveString s h.name
  let value ← resolveString s h.value
  return Json.mkObj
    [ ("name", Json.str name)
    , ("value", Json.str value)
    , ("name_range", entryRangeJson h.name)
    , ("value_range", entryRangeJson h.value) ]

def errorJson (cls detail : String) : Json :=
  Json.mkObj
    [ ("status", Json.str "error")
    , ("class", Json.str cls)
    , ("detail", Json.str detail) ]

def outcomeJson : Parse.Outcome → Json
  | .incomplete => Json.mkObj [("status", Json.str "incomplete")]
  | .error e detail => errorJson e.tag detail
  | .complete req =>
    let s := req.store
    let strings? := do
      let method ← resolveString s req.method
      let target ← resolveString s req.target
      let version ← resolveString s req.version
      let headers ← req.headers.mapM (headerJson s)
      pure (method, target, version, headers)
    match strings? with
    | none =>
      -- unreachable: a complete store is well-formed by THEOREM (`parse_wf`),
      -- so `resolve` succeeds (`resolve_total`), and the parser checked UTF-8
      -- per range, so `fromUTF8?` succeeds. Kept only because `Outcome` does
      -- not carry the proofs; the tag is the harness's defensive fallback.
      errorJson "internal-wf-violation" "resolve failed on a complete store"
    | some (method, target, version, headers) =>
      Json.mkObj
        [ ("status", Json.str "complete")
        , ("consumed", Json.num req.consumed)
        , ("request_line", Json.mkObj
            [ ("method", Json.str method)
            , ("target", Json.str target)
            , ("version", Json.str version) ])
        , ("headers", Json.arr headers.toArray)
        , ("arena", Json.mkObj
            [ ("main_len", Json.num s.main.size)
            , ("sidecar_len", Json.num s.sidecar.size)
            , ("entries", Json.arr (s.entries.map entryJson).toArray.reverse) ]) ]

/-- Decode the `{"input": [bytes...]}` harness input. -/
def decodeInput (doc : String) : Except String Parse.Bytes := do
  let j ← Json.parse doc
  let arr ← j.getObjVal? "input" |>.bind Json.getArr?
  arr.toList.mapM fun v => do
    let n ← v.getNat?
    if n ≤ 255 then pure (UInt8.ofNat n)
    else throw s!"byte out of range: {n}"

def run (doc : String) : (Json × UInt32) :=
  match decodeInput doc with
  | .error e => (errorJson "bad-harness-input" e, 1)
  | .ok bytes => (outcomeJson (Parse.parse bytes), 0)

/-- Drain a stream to a string (the IO shell; the model itself is total). -/
partial def readAll (s : IO.FS.Stream) : IO String := do
  let rec loop (acc : String) : IO String := do
    let line ← s.getLine
    if line.isEmpty then pure acc else loop (acc ++ line)
  loop ""

end Check
end Arena

def main : IO UInt32 := do
  let doc ← Arena.Check.readAll (← IO.getStdin)
  let (json, code) := Arena.Check.run doc
  IO.println json.compress
  return code
