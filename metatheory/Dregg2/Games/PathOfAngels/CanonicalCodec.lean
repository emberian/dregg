/-
# CanonicalCodec — a `Canonical` deriving handler for the PoA wire tower.

## What this replaces

`Wire`/`Runtime` across Path-of-Angels is ~9,880 lines, most of it canonical codec
plumbing written by hand once per type: an encoder that concatenates JSON text in a fixed
key order, a strict `Except String T` parser that re-lists the same keys, and one roundtrip
theorem. Measured 2026-08-05: **33 `_reencodes` theorems across 8 modules, and 8 separate
copies of the same generic `canonicalDecode_reencodes` lemma** — one per module, each proved
again. (`NightWatchLoopWire`, deleted 2026-08-07 with the unreachable `NightWatchLoop` cone,
was 124 defs against 15 theorems in 1,638 lines — one module's share of that hand-work.)

Coverage is uneven by ACCIDENT, because each module's author chose which facts to name.

## What is DETERMINED and what is CHOSEN

Metaprogram what is determined; hand-write what is chosen.

* **Determined** (derived here): the key spelling from the field name, the encoder's byte
  layout, the strict reader, the well-formedness predicate the reader enforces, and the
  roundtrip theorem tying them together.
* **Chosen** (still hand-written, deliberately): which fields exist, the wire bound on each
  field type, whether a record carries a `"format"` tag, every semantic admission gate, and
  every refusal that is about the GAME rather than about the bytes. This handler cannot and
  must not touch those.

## The law is a FIELD, not a test

`FieldCodec` carries `read_toJson` as a structure field. A codec whose reader disagrees
with its writer therefore fails to TYPECHECK; it is not a red test that someone can delete.
The record-level roundtrip is assembled from those field laws, so a derived roundtrip
theorem cannot be weaker than its parts. `Dregg2/Games/PathOfAngels/CanonicalCodecFalsifier.lean`
calibrates that this rejection actually fires, in both polarities.

## ⚑ THE TWO HONEST BOUNDARIES — read before citing anything derived here

**(a) The derived roundtrip lives at the ROW layer, not the byte layer.**
`readRow_toRow` says: for every well-formed value, the strict reader accepts the writer's
canonical row and returns that same value. It does NOT say `decodeBytes (render v) = some v`.
Reaching the byte layer requires `Lean.Json.parse (render v) = .ok (rowToJson (toRow v))` —
adequacy of Lean's own JSON *parser* against this renderer, over an arbitrary value. That is
a real theorem about `Lean.Json.parse`, it is not proved anywhere in this repository, and it
is not proved here. It is named once, as `RowAdapterFaithful` / `ParserAdequate`, so it stops
being invisible; the only evidence in tree for it remains per-fixture `native_decide`.

**(b) The row layer is a `List`, deliberately, and that is load-bearing.**
`Json.obj` is backed by `Std.TreeMap.Raw`, whose `ofList`/`get?` do not reduce under `rfl`
in a form a per-type proof can rely on. `List.lookup`-shaped literal-row matching does. So
the derived reader reads a `Row = List (String × Json)` and a thin, TYPE-INDEPENDENT adapter
(`jsonToRow`) crosses to `Json`. Crossing once, in one place, is why the adapter obligation
above is a single named fact rather than one per derived type.

Neither boundary is new debt: no PoA module proves the byte-layer direction for a general
value today either. The difference is that here it is named.
-/
import Lean
import Lean.Data.Json
import Dregg2.Tactics

namespace Dregg2.Canonical

open Lean

set_option autoImplicit false

/-! ## The canonical row -/

/-- The canonical object SPINE: an ordered key/value list. Both the derived writer and the
derived strict reader talk to this, so a per-type roundtrip proof never has to reduce a
`Std.TreeMap.Raw`. Order is significant — it is the byte order the renderer emits. -/
abbrev Row := List (String × Lean.Json)

/-- The wire integer ceiling PoA uses everywhere (`WIRE_U64_MAX` in
`NightWatchCampaignAdmission`, `WIRE_U64_LIMIT` in `ActivatedContentRuntime`). Restated here so the derived `Nat` codec
carries the SAME refusal the hand-written `objectNat` carries, not a laxer one. -/
abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1

/-! ## Field codecs — the law is a field -/

/-- A canonical field codec: a JSON writer, a canonical TEXT renderer, a strict reader, the
well-formedness the reader enforces, and — as a FIELD, not a test — the law tying them.

`read_toJson` is why a wrong codec cannot be packaged: there is no inhabitant to supply.
`ok` is what makes a bounded field honest — the law is conditional on exactly the bound the
reader checks, so a codec cannot advertise a bound it does not enforce (or enforce one it
does not advertise; the falsifier pins both directions). -/
structure FieldCodec (α : Type) where
  /-- The values the reader will accept back. -/
  ok : α → Bool
  /-- Structured canonical JSON for one field value. -/
  toJson : α → Lean.Json
  /-- Canonical TEXT for one field value — the exact bytes the encoder emits. -/
  render : α → String
  /-- Strict reader. Must refuse anything outside `ok`. -/
  read : Lean.Json → Except String α
  /-- THE LAW. Not a test: an uninhabited field is a type error at construction. -/
  read_toJson : ∀ a, ok a = true → read (toJson a) = Except.ok a

/-- The codec registry. A field type with no instance CANNOT be derived — that is the
refusal, and it is the mechanism by which coverage stays uneven-BY-DESIGN rather than
uneven-by-accident. Adding an instance means proving `read_toJson`, so the registry
cannot grow without the proof growing with it. -/
class HasFieldCodec (α : Type) where
  codec : FieldCodec α

/-! ### `Nat` -/

/-- Canonical JSON for a `Nat`: an integral number with zero exponent. Written against the
constructors rather than `Lean.Json`'s coercion patterns so the reader's match reduces. -/
def natToJson (n : Nat) : Lean.Json := .num ⟨Int.ofNat n, 0⟩

/-- Strict `Nat` reader: refuses non-numbers, negatives, any exponent, and anything over
the wire bound. The exponent-zero requirement is canonicality, not pedantry — `1e1` and `10`
are the same number and only one of them is the canonical spelling. -/
def natRead (limit : Nat) (j : Lean.Json) : Except String Nat :=
  match j with
  | .num ⟨.ofNat n, 0⟩ => if n ≤ limit then Except.ok n else Except.error "integer exceeds the wire bound"
  | _ => Except.error "expected a canonical non-negative integer"

theorem natRead_natToJson (limit n : Nat) (bounded : decide (n ≤ limit) = true) :
    natRead limit (natToJson n) = Except.ok n := by
  have hle : n ≤ limit := of_decide_eq_true bounded
  simp only [natRead, natToJson]
  simp [hle]

/-- The bounded `Nat` codec. `render` is `toString`, which is byte-for-byte what every
hand-written PoA encoder already emits for a numeric field. -/
def natField (limit : Nat) : FieldCodec Nat where
  ok n := decide (n ≤ limit)
  toJson := natToJson
  render := toString
  read := natRead limit
  read_toJson := natRead_natToJson limit

instance : HasFieldCodec Nat := ⟨natField WIRE_U64_MAX⟩

/-! ### `Bool` -/

def boolRead (j : Lean.Json) : Except String Bool :=
  match j with
  | .bool b => Except.ok b
  | _ => Except.error "expected a boolean"

theorem boolRead_boolToJson (b : Bool) (_h : true = true) :
    boolRead (Lean.Json.bool b) = Except.ok b := by
  cases b <;> rfl

/-- `render` matches the hand-written `boolJson` (`if value then "true" else "false"`). -/
def boolField : FieldCodec Bool where
  ok _ := true
  toJson := Lean.Json.bool
  render b := if b then "true" else "false"
  read := boolRead
  read_toJson := boolRead_boolToJson

instance : HasFieldCodec Bool := ⟨boolField⟩

/-! ### `String` -/

def strRead (limit : Nat) (j : Lean.Json) : Except String String :=
  match j with
  | .str s => if s.utf8ByteSize ≤ limit then Except.ok s else Except.error "string exceeds the wire bound"
  | _ => Except.error "expected a string"

theorem strRead_strToJson (limit : Nat) (s : String) (bounded : decide (s.utf8ByteSize ≤ limit) = true) :
    strRead limit (Lean.Json.str s) = Except.ok s := by
  have hle : s.utf8ByteSize ≤ limit := of_decide_eq_true bounded
  simp [strRead, hle]

/-- `render` is `String.quote`, byte-identical to the hand-written `jsonString`. -/
def strField (limit : Nat) : FieldCodec String where
  ok s := decide (s.utf8ByteSize ≤ limit)
  toJson := Lean.Json.str
  render := String.quote
  read := strRead limit
  read_toJson := strRead_strToJson limit

/-! ### ⚑ DELIBERATELY ABSENT: `Digest32`

There is NO `HasFieldCodec Digest32`, and there must not be one until this is a theorem:

    Emit.parseBytes32Hex? (Emit.bytes32Hex d) = some d

Measured 2026-08-05, that lemma does not exist anywhere in this tree. `Emit.lean` proves two
`native_decide` POINT vectors (`parseBytes32Hex_test_federation_vector`,
`parseBytes32Hex_refuses_display_label`) and nothing general. Until it exists, a digest-bearing
record REFUSES to derive — see `CanonicalCodecFalsifier.SealBearingWire`. That refusal is the
feature: the alternative is a derived theorem that quietly omits the digest fields, which is
exactly the uniform-looking vacuity this handler exists to prevent.

This single missing lemma is what blocks `WorldWire`, `OfficerWire`, `VisitKeyWire`,
`ServingWire` and every envelope type from a derived roundtrip. It is the highest-value
next unit of work in this area, and it is NOT done here. -/

/-! ## Field helpers the generated code names

The handler emits calls to these rather than to `HasFieldCodec.codec` directly, so the type
argument is fixed by an ordinary unification against a value or an existing projection, and
the generated syntax never has to render a type. -/

def fieldOk {α : Type} [HasFieldCodec α] (a : α) : Bool := (HasFieldCodec.codec).ok a
def fieldJson {α : Type} [HasFieldCodec α] (a : α) : Lean.Json := (HasFieldCodec.codec).toJson a
def fieldRender {α : Type} [HasFieldCodec α] (a : α) : String := (HasFieldCodec.codec).render a

/-- Read a field whose TYPE is pinned by an existing projection. The projection is erased;
it exists only so the elaborator knows which codec to resolve. -/
def fieldReadFor {S α : Type} [HasFieldCodec α] (_proj : S → α) (j : Lean.Json) :
    Except String α := (HasFieldCodec.codec).read j

theorem fieldReadFor_fieldJson {S α : Type} [HasFieldCodec α] (proj : S → α) (a : α)
    (wellFormed : fieldOk a = true) : fieldReadFor proj (fieldJson a) = Except.ok a :=
  (HasFieldCodec.codec).read_toJson a wellFormed

/-! ## The derived interface -/

/-- What deriving `Canonical` produces. `readRow_toRow` is the non-vacuous half — the half
no PoA module proves today for a general value. -/
class Canonical (α : Type) where
  keys : List String
  toRow : α → Row
  readRow : Row → Except String α
  wf : α → Bool
  render : α → String
  readRow_toRow : ∀ a, wf a = true → readRow (toRow a) = Except.ok a

/-! ## The `Json` adapter — crossed ONCE, for every derived type -/

def rowToJson (row : Row) : Lean.Json := Lean.Json.mkObj row

/-- Field count of a JSON object, via the same fold `Lean.Json`'s own `beq'` uses. -/
def objFieldCount (kvs : Std.TreeMap.Raw String Lean.Json compare) : Nat :=
  kvs.foldl (init := 0) (fun n _ _ => n + 1)

/-- Project a JSON object onto the canonical row for `keys`. Refuses a non-object, a missing
key, and — via the count — any UNKNOWN key, which is what makes the crossing as strict as the
hand-written `exactKeys`. Key ORDER is then re-imposed downstream by the literal-row match in
the derived reader, which `exactKeys` does not do. -/
def jsonToRow (keys : List String) (j : Lean.Json) : Except String Row :=
  match j with
  | .obj kvs =>
      if objFieldCount kvs = keys.length then
        keys.mapM fun k =>
          match kvs.get? k with
          | some v => Except.ok (k, v)
          | none => Except.error ("missing field " ++ k)
      else Except.error "object carries unknown or duplicated fields"
  | _ => Except.error "expected an object"

/-- ⚑ **UNDISCHARGED, NAMED.** The adapter leg: reading back the object built from a
canonical row recovers that row. Not proved — `Std.TreeMap.Raw.ofList`/`get?` would have to
be reasoned through, and this repo has no such development. Every derived codec depends on
it to reach the byte layer, so it is stated once here rather than assumed silently in each. -/
def RowAdapterFaithful (keys : List String) (row : Row) : Prop :=
  jsonToRow keys (rowToJson row) = Except.ok row

/-- ⚑ **UNDISCHARGED, NAMED.** The parser leg: Lean's own JSON parser recovers exactly the
object this renderer wrote. Not proved for a general value anywhere in this repository; the
only evidence in tree is per-fixture `native_decide`. Naming it stops "the canonical wire
roundtrips" from reading as a theorem about all values. -/
def ParserAdequate (render : String) (j : Lean.Json) : Prop :=
  Lean.Json.parse render = Except.ok j

/-! ## The byte layer — ONE copy, replacing eight

`canonicalDecode`/`canonicalDecode_reencodes` is written out separately in
`BazaarGameRuntime`, `CrewFieldMissionRuntime`, `DarkBazaarJudgeWire`, `EventBatchRuntime`,
`GalleyMaintenanceDailyRuntime`, `NetworkGenesisWire`, `NetworkJudgeWire` and (until its
cone was deleted on 2026-08-07) `NightWatchLoopWire` — eight proofs of one fact, seven now.
This is that fact, once. -/

def canonicalDecode {T : Type} (keys : List String) (readRow : Row → Except String T)
    (render : T → String) (byteLimit : Nat) (bytes : String) : Option T :=
  if bytes.utf8ByteSize > byteLimit then none
  else match Lean.Json.parse bytes with
    | .error _ => none
    | .ok json => match jsonToRow keys json with
      | .error _ => none
      | .ok row => match readRow row with
        | .error _ => none
        | .ok value => if render value = bytes then some value else none

/-- Canonicality: an accepted byte string is the unique canonical spelling of the value it
decodes to. This is the `_reencodes` shape, and it is TRUE — but see the falsifier: on its
own it is satisfied by a decoder that accepts nothing. It is the derived `readRow_toRow`
that supplies the missing half. -/
theorem canonicalDecode_reencodes {T : Type} (keys : List String)
    (readRow : Row → Except String T) (render : T → String) (byteLimit : Nat) (bytes : String)
    (value : T) (accepted : canonicalDecode keys readRow render byteLimit bytes = some value) :
    render value = bytes := by
  unfold canonicalDecode at accepted
  split at accepted <;> try contradiction
  next _ =>
    split at accepted <;> try contradiction
    next json _ =>
      split at accepted <;> try contradiction
      next row _ =>
        split at accepted <;> try contradiction
        next decoded _ =>
          split at accepted
          next agreed =>
            have same : decoded = value := Option.some.inj accepted
            simpa [same] using agreed
          next _ => contradiction

#assert_axioms canonicalDecode_reencodes

/-! ## The generated roundtrip proof — ONE tactic, named once

Every derived theorem is closed by this macro, so if the reduction ever needs a different
move there is exactly one place to change it and every derived type follows.

⚑ There is deliberately **no `first` combinator here.** A `first` whose earlier branch can
succeed without closing the goal commits to that branch and lets Lean fill the remainder with
`sorryAx` — that exact shape shipped a `sorry` past an authoring lane and its adversarial
reviewer in this repo. Each tactic below either closes its goal or fails loudly. -/
macro "canonical_roundtrip" wf:ident row:ident rd:ident : tactic =>
  `(tactic|
    (intro v wellFormed
     cases v
     simp only [$wf:ident, Bool.and_eq_true] at wellFormed
     simp_all [$row:ident, $rd:ident, Dregg2.Canonical.fieldOk,
       Dregg2.Canonical.fieldReadFor_fieldJson]))

/-! ## The deriving handler -/

/-- `contentEpoch` ↦ `content_epoch`. The wire spelling is DETERMINED by the field name; a
handler that let the author choose it per field would just be the hand-written codec again
with more ceremony. A field name that would produce a leading underscore is refused. -/
def camelToSnake (s : String) : String :=
  s.toList.foldl
    (fun acc c => if c.isUpper then acc ++ "_" ++ c.toLower.toString else acc ++ c.toString) ""

open Lean Elab Command in
/-- Emit every declaration for a `Canonical` codec over `structName`. Shared by the
`deriving` handler and by `#assert_derive_refuses`, so the falsifier exercises exactly the
path a real derivation takes — not a reimplementation of it. -/
def deriveCanonicalFor (structName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env structName do
    throwError "Canonical: {structName} is not a structure. The handler derives a canonical \
      record codec; a sum type's wire tag is a CHOSEN thing and stays hand-written."
  unless (getStructureParentInfo env structName).isEmpty do
    throwError "Canonical: {structName} extends a parent structure. The derived reader builds \
      the value with an anonymous constructor, which does not see a flattened parent. Flatten \
      the record or hand-write this codec."
  let fields := getStructureFields env structName
  if fields.isEmpty then
    throwError "Canonical: {structName} has no fields — an empty canonical object is not a \
      wire type, and the roundtrip theorem over it would be content-free."
  let keys : Array String := fields.map fun f => camelToSnake f.getString!
  for k in keys do
    if k.startsWith "_" then
      throwError "Canonical: {structName} has a field whose wire key would be {k}. A leading \
        underscore means the field name started uppercase; rename the field."
  if keys.toList.eraseDups.length != keys.size then
    throwError "Canonical: {structName} has two fields with the same wire key — the reader \
      could not tell them apart and the roundtrip would be false."
  -- Declarations land beside the structure, whatever namespace the derivation runs in.
  let currNs ← getCurrNamespace
  let rel : Name → Ident := fun suffix =>
    mkIdent (Name.replacePrefix (structName ++ suffix) currNs Name.anonymous)
  let tyId : Ident := mkIdent (Name.replacePrefix structName currNs Name.anonymous)
  let keysId := rel `canonKeys
  let rowId := rel `toRow
  let wfId := rel `canonWf
  let renderId := rel `renderCanon
  let readId := rel `readRow
  let thmId := rel `readRow_toRow
  let projId : Nat → Ident := fun i =>
    mkIdent (Name.replacePrefix (structName ++ fields[i]!) currNs Name.anonymous)
  let n := fields.size
  let idxs := (List.range n)
  -- `.raw`-wrapped rather than coerced: a string literal has to sit in both TERM and PATTERN
  -- positions below, and the explicit `TSyntax` construction works in both.
  let keyLit : Nat → Term := fun i => ⟨(Syntax.mkStrLit keys[i]!).raw⟩
  -- ⚑ `mkIdent`, NOT a quotation-local `v`. The binder is emitted in one quotation and the body
  -- in another; a `v` written inside each would carry DIFFERENT macro scopes and simply not bind.
  -- An `mkIdent` name has no scopes, so ordinary lexical scoping joins the two.
  let vId : Ident := mkIdent (Name.mkSimple "v")
  -- keys
  let keyLits : Array Term := (idxs.map keyLit).toArray
  elabCommand (← `(command| def $keysId : List String := [$keyLits,*]))
  -- toRow
  let entries : Array Term ← idxs.toArray.mapM fun i =>
    `(term| ($(keyLit i), Dregg2.Canonical.fieldJson ($(projId i) $vId)))
  elabCommand (← `(command| def $rowId ($vId : $tyId) : Dregg2.Canonical.Row := [$entries,*]))
  -- canonWf : right-nested `&&` over the per-field `ok`
  let mut wfTerm : Term ← `(term| Dregg2.Canonical.fieldOk ($(projId (n - 1)) $vId))
  for i in (List.range (n - 1)).reverse do
    wfTerm ← `(term| Dregg2.Canonical.fieldOk ($(projId i) $vId) && $wfTerm)
  elabCommand (← `(command| def $wfId ($vId : $tyId) : Bool := $wfTerm))
  -- renderCanon : LEFT-nested `++`, because `++` IS `infixl:65` in Lean 4 and every
  -- hand-written PoA encoder therefore associates LEFT.
  -- ⚠ FIXED 2026-08-05.  This was built right-nested under a comment asserting the
  -- opposite, and `CanonicalCodecHealthWire.renderCanon_eq_healthViewJson` — the whole point of the
  -- handler, the theorem that makes the encoder swap a no-op on the BYTES — could not be
  -- closed by `rfl`.  `String.append` is not definitionally associative over VARIABLE
  -- fields, so the nesting has to MATCH the shipped encoder; agreeing with it up to
  -- `String.append_assoc` is exactly what does not reduce.
  let sepLit : Nat → Term := fun i =>
    ⟨(Syntax.mkStrLit ((if i == 0 then "{\"" else ",\"") ++ keys[i]! ++ "\":")).raw⟩
  let mut renderTerm : Term ←
    `(term| $(sepLit 0) ++ Dregg2.Canonical.fieldRender ($(projId 0) $vId))
  for i in idxs.drop 1 do
    renderTerm ←
      `(term| $renderTerm ++ $(sepLit i) ++ Dregg2.Canonical.fieldRender ($(projId i) $vId))
  renderTerm ← `(term| $renderTerm ++ "}")
  elabCommand (← `(command| def $renderId ($vId : $tyId) : String := $renderTerm))
  -- readRow : ONE literal-row pattern pins key spelling, key ORDER and arity at once — which is
  -- strictly more than the hand-written `exactKeys`, a SET check that leaves order to the
  -- re-encode comparison downstream. Nested `match` rather than `>>=` so the derived proof
  -- reduces by plain iota after the field laws rewrite, with no monad-instance unfolding.
  let jId : Nat → Ident := fun i => mkIdent (Name.mkSimple s!"j{i}")
  let aId : Nat → Ident := fun i => mkIdent (Name.mkSimple s!"a{i}")
  let errId : Ident := mkIdent (Name.mkSimple "err")
  let pats : Array Term ← idxs.toArray.mapM fun i => `(term| ($(keyLit i), $(jId i)))
  let aIds : Array Term := (idxs.map fun i => (aId i : Term)).toArray
  let rowId' : Ident := mkIdent (Name.mkSimple "row")
  let mut readBody : Term ← `(term| Except.ok ⟨$aIds,*⟩)
  for i in idxs.reverse do
    readBody ← `(term|
      match Dregg2.Canonical.fieldReadFor $(projId i) $(jId i) with
      | Except.error $errId => Except.error $errId
      | Except.ok $(aId i) => $readBody)
  elabCommand (← `(command|
    def $readId ($rowId' : Dregg2.Canonical.Row) : Except String $tyId :=
      match $rowId':ident with
      | [$pats,*] => $readBody
      | _ => Except.error "canonical row: key spelling, key order, or arity mismatch"))
  -- the roundtrip theorem
  elabCommand (← `(command|
    theorem $thmId : ∀ ($vId : $tyId), $wfId $vId = true →
        $readId ($rowId $vId) = Except.ok $vId := by
      canonical_roundtrip $wfId $rowId $readId))
  -- the instance (braced, not `where`: a `where` block inside a quotation is layout-sensitive)
  elabCommand (← `(command|
    instance : Dregg2.Canonical.Canonical $tyId :=
      { keys := $keysId, toRow := $rowId, readRow := $readId, wf := $wfId,
        render := $renderId, readRow_toRow := $thmId }))

open Lean Elab Command in
initialize
  Lean.Elab.registerDerivingHandler ``Canonical fun typeNames => do
    for n in typeNames do
      deriveCanonicalFor n
    return true

/-! ## The rejectors

Four commands. Each has a red path in BOTH directions — a checker that can only pass is not a
checker, the same discipline `Dregg2/Tactics.lean` applies to `#assert_compiled`:

| command | rejects | its positive control (what makes blindness a RED) |
|---|---|---|
| `#assert_derive_refuses` | a derivable type | the real `deriving instance` in `CanonicalCodecHealthWire`, which runs this same `deriveCanonicalFor` |
| `#assert_term_refused` | a term that elaborates | `#assert_term_elaborates`, sharing `runProbe` |
| `#assert_term_elaborates` | a term that does not | `#assert_term_refused`, sharing `runProbe` |
| `#assert_codec_nonvacuous` | the `_reencodes` shape, a missing witness, a non-clean pin | the derived `HealthViewWire` codec, which must PASS it |
-/

open Lean Elab Command in
/-- Run `act` with the command state fully restored afterwards — environment AND message log,
so a probe leaves no trace and a LOGGED error (Lean's recovery path) still counts as failure.
Returns `true` only if the action neither threw nor logged an error. -/
def runProbe (act : CommandElabM Unit) : CommandElabM Bool := do
  let saved ← get
  let mut succeeded := true
  try
    act
    if (← get).messages.hasErrors then succeeded := false
  catch _ =>
    succeeded := false
  set saved
  return succeeded

open Lean Elab Command in
/-- `#assert_derive_refuses Foo` — ERROR if `Foo` CAN be derived. Runs the real
`deriveCanonicalFor`, not a stand-in, inside a fully restored probe. Its calibrated use is a
record carrying a field type with no proved codec law: the refusal is what keeps a missing
proof from turning into a quietly narrower derived theorem. -/
elab "#assert_derive_refuses" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  if ← runProbe (deriveCanonicalFor name) then
    throwError "REFUSAL EXPECTED: `Canonical` DERIVED for {name}, and this command asserts it \
      must not. Either a `HasFieldCodec` instance was added for a field type whose roundtrip \
      law is not proved — in which case the law is the work, not the instance — or the \
      handler's guards have gone toothless. Do NOT delete this assertion to get green."
  logInfo m!"#assert_derive_refuses {name}: derivation refused, as required"

open Lean Elab Command in
/-- `#assert_term_refused (e)` — ERROR if `e` elaborates. Treats a term that elaborated but
left `sorryAx` in it, or that logged an error, as REFUSED: Lean recovers from a failed `by`
block by inserting `sorryAx`, and without that check this command would pass on exactly the
wrong evidence. The falsifier's positive control (an honest codec, which must elaborate)
covers the other direction. -/
elab "#assert_term_refused" "(" e:term ")" : command => do
  let elaborated ← runProbe do
    liftTermElabM do
      let expr ← Lean.Elab.Term.elabTerm e none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← instantiateMVars expr
      if expr.hasSorry then
        throwError "term elaborated only via sorry"
  if elaborated then
    throwError "REFUSAL EXPECTED: the term elaborated. A codec whose reader disagrees with \
      its writer must be a TYPE ERROR, because the roundtrip law is a field of `FieldCodec`. \
      If this passes, the law field has gone vacuous."
  logInfo m!"#assert_term_refused: term refused, as required"

open Lean Elab Command in
/-- `#assert_term_elaborates (e)` — the POSITIVE CONTROL, exact dual of `#assert_term_refused`
and sharing the same `runProbe`, so the two go blind together or not at all.

A pure rejector cannot detect its own blindness: a `#assert_term_refused` that refused
EVERYTHING — because `runProbe` mis-restored state, because `hasSorry` started firing on
every term, because `liftTermElabM` began throwing for an unrelated reason — would report
every fixture in the file as correctly refused. Pinning that an HONEST codec still elaborates
turns that failure into a red instead of a green. This is the same discipline
`Dregg2/Tactics.lean` applies with `#assert_depends_on` against `#assert_not_depends_on`;
an ordinary `example` does not serve, because it does not go through `runProbe`. -/
elab "#assert_term_elaborates" "(" e:term ")" : command => do
  let elaborated ← runProbe do
    liftTermElabM do
      let expr ← Lean.Elab.Term.elabTerm e none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← instantiateMVars expr
      if expr.hasSorry then
        throwError "term elaborated only via sorry"
  unless elaborated do
    throwError "POSITIVE CONTROL FAIL: an honest term did NOT elaborate through the same probe \
      `#assert_term_refused` uses. Either this codec really broke — then re-pin the control on \
      a live one — or the probe has gone BLIND, in which case every `#assert_term_refused` in \
      the tree is now passing VACUOUSLY. Do not delete this control to get green."
  logInfo m!"#assert_term_elaborates: term elaborated (the probe is not blind)"

/-- Strip `∀`/`→` binders, returning the binder types and the conclusion (bound variables in
both stay loose — only head constants are inspected, which is safe under loose bvars). -/
partial def stripBinders (e : Expr) (acc : Array Expr := #[]) : Array Expr × Expr :=
  match e with
  | .forallE _ t b _ => stripBinders b (acc.push t)
  | _ => (acc, e)

open Lean Elab Command in
/-- `#assert_codec_nonvacuous Foo` — the anti-vacuity gate on a DERIVED roundtrip. A derived
theorem that looks like uniform coverage and proves nothing is worse than fourteen honest
hand-written ones, so this refuses on every way it could be hollow:

* `Foo.readRow_toRow` must EXIST and be a theorem;
* its conclusion must be an equation whose right side is headed by `Except.ok` — this is what
  rejects the `decode b = some v → encode v = b` shape, which the falsifier proves is
  satisfied by a decoder that accepts nothing;
* its left side must be headed by `Foo.readRow`, so it is about the derived reader;
* it must quantify over a binder of type `Foo`, so it is not a statement about one point;
* `Foo.canonWf_witness` must exist — a conditional roundtrip whose condition is unsatisfiable
  is vacuous in a second, quieter way, and the author supplies the witness because the
  handler cannot invent an inhabitant;
* both must be kernel-clean, via the SAME `Dregg2.assertNameClean` every other pin uses. -/
elab "#assert_codec_nonvacuous" id:ident : command => do
  let ty ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let thmName := ty ++ `readRow_toRow
  let some info := env.find? thmName
    | throwError "#assert_codec_nonvacuous {ty}: {thmName} does not exist — nothing was derived, \
        so there is no roundtrip to call non-vacuous."
  unless info.isThm do
    throwError "#assert_codec_nonvacuous {ty}: {thmName} is not a theorem."
  let readerName := ty ++ `readRow
  let (binders, concl) := stripBinders info.type
  let (eqHead, eqArgs) := concl.getAppFnArgs
  unless eqHead == ``Eq && eqArgs.size == 3 do
    throwError "#assert_codec_nonvacuous {ty}: the conclusion of {thmName} is not an equation."
  let lhs := eqArgs[1]!
  let rhs := eqArgs[2]!
  unless rhs.getAppFn.isConstOf ``Except.ok do
    throwError "VACUITY REFUSED: {thmName} does not conclude `Except.ok _`. The shape \
      `decode b = some v → encode v = b` is REJECTED here on purpose: it constrains the \
      decoder only where the decoder already accepts, and \
      `CanonicalCodecFalsifier.blindDecode_reencodes` proves it holds of a decoder that \
      accepts NOTHING. A derived roundtrip must state acceptance."
  unless lhs.getAppFn.isConstOf readerName do
    throwError "#assert_codec_nonvacuous {ty}: {thmName} is not about {readerName} — it could \
      be a true equation about some other function entirely."
  unless binders.any (fun b => b.getAppFn.isConstOf ty) do
    throwError "#assert_codec_nonvacuous {ty}: {thmName} does not quantify over a {ty} — a \
      roundtrip proved at one point is a fixture, not coverage."
  Dregg2.assertNameClean thmName
  let witnessName := ty ++ `canonWf_witness
  let some wInfo := env.find? witnessName
    | throwError "#assert_codec_nonvacuous {ty}: {witnessName} does not exist. {thmName} is \
        CONDITIONAL on `canonWf v = true`; without a witness that some value satisfies it, the \
        theorem could be vacuous in its hypothesis. Supply \
        `theorem {witnessName} : {ty}.canonWf <a concrete value> = true := by decide`."
  unless wInfo.isThm do
    throwError "#assert_codec_nonvacuous {ty}: {witnessName} is not a theorem."
  Dregg2.assertNameClean witnessName
  logInfo m!"#assert_codec_nonvacuous {ty}: acceptance stated over all values, hypothesis \
    witnessed by {witnessName}, both kernel-clean"

end Dregg2.Canonical
