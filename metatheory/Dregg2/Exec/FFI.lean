/-
# Dregg2.Exec.FFI — the C-ABI boundary onto the PROVED executable kernel.

A thin, scalar-only (`UInt64`/`UInt8`) shell over `Dregg2.Exec` (`Kernel.lean`):
the SAME `exec` whose conservation (`exec_conserves`) and integrity (`exec_authorized`)
are proved in Lean is the one a C/Rust host calls here. No new logic — we only marshal
`UInt64` ⇄ `ℤ` at the boundary and `@[export]` two entry points. This is the cascade
seam for dregg2 §8 (the Rust boundary hosts the verified kernel).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.FFI

open Dregg2.Exec
open Dregg2.Authority

/-- **C entry point — run one transfer, return the conserved total.**

Builds a 2-account state (`{0,1}`, `bal 0 ↦ balA`, `bal 1 ↦ balB`, no caps), a turn
moving `amt` from cell 0 to cell 1 under actor 0's own authority, runs the proved
`Exec.exec`, and returns the live total: on success the (conserved) total of the new
state, on a fail-closed `none` the unchanged total of the input. By `exec_conserves`
both equal `balA + balB`. -/
@[export dregg_kernel_transfer_total]
def transferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : KernelState :=
    { accounts := {0, 1}
      bal := fun c => if c = 0 then Int.ofNat balA.toNat
                      else if c = 1 then Int.ofNat balB.toNat else 0
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : KernelState := (Exec.exec k turn).getD k
  (Exec.total result).toNat.toUInt64

/-- **C entry point — the authority check, in isolation.**

Returns `1` iff `actor` is authorized over `src = 0` for a unit transfer under the
empty cap table (i.e. iff `actor = 0`, ownership). Demonstrates `Exec.authorizedB`
— the integrity predicate from `exec` — callable directly from C. -/
@[export dregg_kernel_authorized]
def authorized (actor : UInt64) : UInt8 :=
  if Exec.authorizedB (fun _ => []) { actor := actor.toNat, src := 0, dst := 1, amt := 1 }
  then 1 else 0

/-- **C entry point — run one transfer on the CONTENT-ADDRESSED record cell, return the conserved
total `balance` field.**

The record-cell analog of `transferTotal`: the cell-state is now a `Value` record (carrying a
`balance` field plus, here, a `nonce` field that the transfer must leave intact), NOT two scalars.
We marshal the `balance` FIELD as the scalar at the boundary — the FFI signature stays
`UInt64 → UInt64 → UInt64 → UInt64`, byte-stable with `transferTotal`, so the Rust host and the
10k/10k differential oracle need no signature change — while the PROVED function underneath is now
`RecordKernel.recKExec` over the real record cell. By `recKExec_conserves` the returned total equals
`balA + balB` (conserved over the `balance` field). This turns the scalar PoC into the actual
record-cell migration ratchet, with the marshalling honestly limited to the `balance` field. -/
@[export dregg_record_kernel_transfer_total]
def recordTransferTotal (balA balB amt : UInt64) : UInt64 :=
  let k : RecordKernelState :=
    { accounts := {0, 1}
      cell := fun c => if c = 0 then .record [("balance", .int (Int.ofNat balA.toNat)),
                                              ("nonce", .int 0)]
                       else if c = 1 then .record [("balance", .int (Int.ofNat balB.toNat))]
                       else .record [("balance", .int 0)]
      caps := fun _ => [] }
  let turn : Turn := { actor := 0, src := 0, dst := 1, amt := Int.ofNat amt.toNat }
  let result : RecordKernelState := (Exec.recKExec k turn).getD k
  (Exec.recTotal result).toNat.toUInt64

/-! ## The `Value`/`RecordKernelState` WIRE CODEC — marshalling real record cell-state.

The scalar exports above marshal only a single `balance` field as a `UInt64`. To make the
FFI a real SWAP-enabler — the node calling `recKExec` over the **content-addressed record
cell** rather than a scalar — we need to marshal a whole `RecordKernelState` (the per-cell
`Value` records + the turn) across the C ABI, run the PROVED `recKExec`, and marshal the
output state back.

We reuse the `CircuitEmit.lean` discipline: a deterministic Lean `→ String` encoder + its
parser, both sides agreeing on a minimal JSON grammar, differential-checked against a Rust
reference (cross-validation, NOT certification — the codec is TCB, not proved). The wire
grammar (no whitespace, exactly as emitted):

    state  := {"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}        (input)
    out    := {"cells":CELLS,"ok":B}                                  (output; B ∈ {0,1})
    CELLS  := [] | [CELL(,CELL)*]
    CELL   := [N,VALUE]                                               (cell-id, its record)
    VALUE  := {"int":N} | {"dig":N} | {"sym":N} | {"rec":FIELDS}
    FIELDS := [] | [FIELD(,FIELD)*]
    FIELD  := ["NAME",VALUE]
    N      := a signed decimal integer;  NAME := a JSON string (plain chars).

`amt` and `int` payloads are signed (`Int`); ids/digests/symbols are non-negative.
The MARSHALLING BOUNDARY is exactly this grammar: it is the only thing the Lean and Rust
sides must agree on, and the differential is what certifies the agreement empirically.
Nested records are handled (the grammar/codec recurse), so this covers the full `Value`
leaf set (int/dig/sym/record), not only the flat `balance` record.
-/

/-! ### Encoder: `Value`/state → canonical JSON `String`. -/

/-- JSON-escape the plain field-name characters the codec uses (`"` and `\`). Field names
in this kernel are simple identifiers, but we escape defensively so the grammar stays exact. -/
def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else String.singleton c)) ""

mutual
/-- Encode a `Value` to its canonical wire JSON. -/
def encodeValue : Value → String
  | .int i    => "{\"int\":" ++ toString i ++ "}"
  | .dig d    => "{\"dig\":" ++ toString d ++ "}"
  | .sym s    => "{\"sym\":" ++ toString s ++ "}"
  | .record fs => "{\"rec\":" ++ encodeFields fs ++ "}"
/-- Encode a record's named fields as a JSON array of `["name",value]` pairs. -/
def encodeFields : List (FieldName × Value) → String
  | []          => "[]"
  | (n, v) :: fs =>
      let head := "[\"" ++ jsonEscape n ++ "\"," ++ encodeValue v ++ "]"
      "[" ++ head ++ encodeFieldsTail fs ++ "]"
/-- The comma-prefixed tail of a fields array. -/
def encodeFieldsTail : List (FieldName × Value) → String
  | []          => ""
  | (n, v) :: fs => ",[\"" ++ jsonEscape n ++ "\"," ++ encodeValue v ++ "]" ++ encodeFieldsTail fs
end

/-- Encode a list of `(cellId, Value)` entries as the `CELLS` array. -/
def encodeCells : List (CellId × Value) → String
  | []      => "[]"
  | c :: cs =>
      let one := fun (p : CellId × Value) =>
        "[" ++ toString p.1 ++ "," ++ encodeValue p.2 ++ "]"
      "[" ++ one c ++ (cs.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-- Encode an output state: the post-state cells + the commit bit. -/
def encodeOut (cells : List (CellId × Value)) (ok : Bool) : String :=
  "{\"cells\":" ++ encodeCells cells ++ ",\"ok\":" ++ (if ok then "1" else "0") ++ "}"

/-! ### Decoder: a tiny recursive-descent parser over the fixed grammar.

A hand-rolled, zero-dependency parser (Lean-core `String`/`List Char`). It is intentionally
strict: any deviation from the emitted grammar returns `none` (fail-closed), so a malformed
wire can never silently produce a wrong state. The parser state is `(remaining chars)`; it
returns `(value, rest)` on success. -/

/-- Parse position: the remaining character list. -/
abbrev PState := List Char

/-- Match an explicit char list as a prefix; `none` on mismatch. -/
def litGo : List Char → PState → Option PState
  | [],      rest    => some rest
  | l :: ls, r :: rs => if l == r then litGo ls rs else none
  | _ :: _,  []      => none

/-- Consume an exact literal prefix; `none` on mismatch. -/
def lit (s : String) (cs : PState) : Option PState := litGo s.toList cs

/-- Greedily collect leading decimal digits, returning them and the rest. -/
def digitsGo : PState → List Char → (List Char × PState)
  | c :: rest, acc => if c.isDigit then digitsGo rest (acc ++ [c]) else (acc, c :: rest)
  | [],        acc => (acc, [])

/-- Parse a signed decimal integer; returns the `Int` and the rest. -/
def parseInt (cs : PState) : Option (Int × PState) :=
    let (neg, cs) := match cs with | '-' :: rest => (true, rest) | _ => (false, cs)
    let (ds, rest) := digitsGo cs []
    if ds.isEmpty then none
    else
      let n : Nat := ds.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
      some ((if neg then -(Int.ofNat n) else Int.ofNat n), rest)

/-- Parse a non-negative `Nat` (an id / digest / symbol payload). -/
def parseNat (cs : PState) : Option (Nat × PState) :=
  match parseInt cs with
  | some (i, rest) => if i ≥ 0 then some (i.toNat, rest) else none
  | none           => none

/-- Accumulate a JSON string body until the closing quote (escapes: `\"`, `\\`). -/
def parseStrGo : PState → List Char → Option (String × PState)
  | '"' :: rest,         acc => some (String.ofList acc, rest)
  | '\\' :: '"' :: rest, acc => parseStrGo rest (acc ++ ['"'])
  | '\\' :: '\\' :: rest, acc => parseStrGo rest (acc ++ ['\\'])
  | c :: rest,           acc => parseStrGo rest (acc ++ [c])
  | [],                  _   => none

/-- Parse a JSON string literal (handles the `\"` and `\\` escapes the encoder emits). -/
def parseStr : PState → Option (String × PState)
  | '"' :: cs => parseStrGo cs []
  | _ => none

/- Parse a `Value` and its sub-records. Fuel-bounded on a `Nat` so termination is structural;
the caller seeds the fuel with the wire length (an upper bound on parse depth). -/
mutual
/-- Parse a `Value` from the wire (int/dig/sym/record). -/
def parseValue (fuel : Nat) (cs : PState) : Option (Value × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "{\"int\":" cs with
    | some rest => match parseInt rest with
                   | some (i, r) => (lit "}" r).map (fun r' => (Value.int i, r'))
                   | none => none
    | none =>
    match lit "{\"dig\":" cs with
    | some rest => match parseNat rest with
                   | some (d, r) => (lit "}" r).map (fun r' => (Value.dig d, r'))
                   | none => none
    | none =>
    match lit "{\"sym\":" cs with
    | some rest => match parseNat rest with
                   | some (s, r) => (lit "}" r).map (fun r' => (Value.sym s, r'))
                   | none => none
    | none =>
    match lit "{\"rec\":" cs with
    | some rest => match parseFields fuel rest with
                   | some (fs, r) => (lit "}" r).map (fun r' => (Value.record fs, r'))
                   | none => none
    | none => none

/-- Parse a `FIELDS` array `[["name",value],...]` (or `[]`). -/
def parseFields (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some rest => parseFieldsLoop fuel rest

/-- Parse the non-empty body of a `FIELDS` array, having consumed the opening `[`. -/
def parseFieldsLoop (fuel : Nat) (cs : PState) : Option (List (FieldName × Value) × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match lit "[" cs with
    | none => none
    | some r0 =>
    match parseStr r0 with
    | none => none
    | some (name, r1) =>
      match lit "," r1 with
      | none => none
      | some r2 =>
        match parseValue fuel r2 with
        | none => none
        | some (v, r3) =>
          match lit "]" r3 with
          | none => none
          | some r4 =>
            match lit "," r4 with
            | some r5 => match parseFieldsLoop fuel r5 with
                         | some (rest, r6) => some ((name, v) :: rest, r6)
                         | none => none
            | none => match lit "]" r4 with
                      | some r6 => some ([(name, v)], r6)
                      | none => none
end

/-- Parse one `CELL` `[id,value]`. -/
def parseCell (fuel : Nat) (cs : PState) : Option ((CellId × Value) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (id, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseValue fuel r3 with
        | none => none
        | some (v, r4) => (lit "]" r4).map (fun r5 => ((id, v), r5))

/-- Parse a `CELLS` array `[[id,value],...]` (or `[]`). Fuel-bounded on the number of cells. -/
def parseCellsLoop (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match parseCell fuel cs with
    | none => none
    | some (cell, r1) =>
      match lit "," r1 with
      | some r2 => match parseCellsLoop fuel r2 with
                   | some (rest, r3) => some (cell :: rest, r3)
                   | none => none
      | none => match lit "]" r1 with
                | some r3 => some ([cell], r3)
                | none => none

/-- Parse the `CELLS` array (the empty/non-empty split). -/
def parseCells (fuel : Nat) (cs : PState) : Option (List (CellId × Value) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some rest => parseCellsLoop fuel rest

/-- The decoded input: the cell entries + the turn fields. -/
structure WireInput where
  cells : List (CellId × Value)
  actor : CellId
  src   : CellId
  dst   : CellId
  amt   : Int

/-- Parse a full input state `{"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}`. Strict:
the whole string must be consumed (no trailing bytes). -/
def parseInput (s : String) : Option WireInput :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"actor\":" r1 with
      | none => none
      | some r2 => match parseNat r2 with
        | none => none
        | some (actor, r3) =>
          match lit ",\"src\":" r3 with
          | none => none
          | some r4 => match parseNat r4 with
            | none => none
            | some (src, r5) =>
              match lit ",\"dst\":" r5 with
              | none => none
              | some r6 => match parseNat r6 with
                | none => none
                | some (dst, r7) =>
                  match lit ",\"amt\":" r7 with
                  | none => none
                  | some r8 => match parseInt r8 with
                    | none => none
                    | some (amt, r9) =>
                      match lit "}" r9 with
                      | some [] => some { cells := cells, actor := actor, src := src,
                                          dst := dst, amt := amt }
                      | _ => none

/-! ### The state-marshalling step export. -/

/-- Build a `RecordKernelState` from decoded cell entries: the `accounts` set is exactly the
listed cell-ids, the `cell` function looks each id up in the entry list (absent ⇒ an empty
`balance:0` record, matching `recKExec`'s fail-soft measure), and the cap table is empty
(authority is by ownership — the differential's regime, identical to the scalar exports). -/
def stateOfCells (cells : List (CellId × Value)) : RecordKernelState :=
  { accounts := (cells.map Prod.fst).toFinset
    cell := fun c => match cells.find? (fun p => p.1 == c) with
                     | some p => p.2
                     | none   => .record [(Exec.balanceField, .int 0)]
    caps := fun _ => [] }

/-- Read the post-state cells back out, in the SAME id order as the input list (so the wire is
deterministic and the Rust side can compare positionally). -/
def cellsOfState (ids : List CellId) (k : RecordKernelState) : List (CellId × Value) :=
  ids.map (fun c => (c, k.cell c))

/-- **C entry point — marshal a full record-cell STATE, run the PROVED `recKExec`, marshal back.**

This is the real swap-enabler: the input is a canonical JSON encoding of a `RecordKernelState`
(per-cell `Value` records, not a scalar) plus the turn; we decode it, run the SAME
`Exec.recKExec` whose conservation/authority/fail-closed laws are proved in `RecordKernel.lean`,
and re-encode the output state. On a malformed wire (decode failure) we fail-closed to
`{"cells":[],"ok":0}`. On a rejected turn (`recKExec = none`) we echo the unchanged input cells
with `ok:0`; on commit we emit the new cells with `ok:1`. By `recKExec_conserves` the total
`balance` over the live accounts is preserved across a commit — now end-to-end over the wire. -/
@[export dregg_record_kernel_step]
def recordKernelStep (input : String) : String :=
  match parseInput input with
  | none => encodeOut [] false
  | some wi =>
    let k := stateOfCells wi.cells
    let ids := wi.cells.map Prod.fst
    let turn : Turn := { actor := wi.actor, src := wi.src, dst := wi.dst, amt := wi.amt }
    match Exec.recKExec k turn with
    | some k' => encodeOut (cellsOfState ids k') true
    | none    => encodeOut (cellsOfState ids k) false

/-! ## The CAPS-bearing wire codec — marshalling the HELD-CAP authority table.

`recordKernelStep` above marshals the record `cell`-state but hard-codes `caps := fun _ => []`,
so authority there is by OWNERSHIP only (`actor = src`). For the cascade swap the node's
turn-decision must exercise the FULL `authorizedB` gate — including the cross-vat case where an
`actor ≠ owner` is authorized because it HOLDS a discharging cap on `src` (a `node src` cap, or
an `endpoint src` cap carrying `Auth.write`; see `Kernel.authorizedB`). So we extend the wire to
also carry the `Caps` table (`Label → List Cap`) and feed it into the SAME proved `recKExec`.

The cap wire grammar (appended to the input object, before `actor`; output is UNCHANGED):

    state_caps := {"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}
    CAPS    := [] | [CAPENTRY(,CAPENTRY)*]
    CAPENTRY:= [N,CAPLIST]                        (holder-label, that holder's cap list)
    CAPLIST := [] | [CAP(,CAP)*]
    CAP     := {"null":0} | {"node":N} | {"ep":[N,AUTHS]}   (null / node target / endpoint)
    AUTHS   := [] | [A(,A)*]                       (A := an Auth tag, 0..6)
    A       := 0=read 1=write 2=grant 3=call 4=reply 5=reset 6=control  (the `Auth` ctor order)

A `Caps` value is a TOTAL function `Label → List Cap`; we marshal it as the finite list of
holders with a non-empty slot, and reconstruct the total function as "listed slot, else `[]`"
(matching the differential's regime: only the listed holders carry caps). The caps codec is
likewise TCB — cross-validated by the caps differential, not certified. -/

/-! ### Auth tag ⇄ `Auth` (the 7-constructor enumeration). -/

/-- Encode an `Auth` to its wire tag (`0..6`), in `Auth`'s constructor order. -/
def authTag : Auth → Nat
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6

/-- Decode a wire tag back to an `Auth`; out-of-range ⇒ `none` (fail-closed). -/
def authOfTag : Nat → Option Auth
  | 0 => some .read | 1 => some .write | 2 => some .grant | 3 => some .call
  | 4 => some .reply | 5 => some .reset | 6 => some .control | _ => none

/-! ### Caps encoder. -/

/-- Encode an `Auth` list as the `AUTHS` array. -/
def encodeAuths : List Auth → String
  | []      => "[]"
  | a :: as =>
      "[" ++ toString (authTag a) ++ (as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) "") ++ "]"

/-- Encode one `Cap` to its wire form. -/
def encodeCap : Cap → String
  | .null         => "{\"null\":0}"
  | .node t       => "{\"node\":" ++ toString t ++ "}"
  | .endpoint t r => "{\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}"

/-- Encode a holder's cap list as the `CAPLIST` array. -/
def encodeCapList : List Cap → String
  | []      => "[]"
  | c :: cs =>
      "[" ++ encodeCap c ++ (cs.foldl (fun acc x => acc ++ "," ++ encodeCap x) "") ++ "]"

/-- Encode the `CAPS` array from a list of `(holder, capList)` entries. -/
def encodeCapsEntries : List (CellId × List Cap) → String
  | []      => "[]"
  | e :: es =>
      let one := fun (p : CellId × List Cap) =>
        "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]"
      "[" ++ one e ++ (es.foldl (fun acc p => acc ++ "," ++ one p) "") ++ "]"

/-! ### Caps decoder (reuses the `lit`/`parseNat`/`parseInt` primitives above). -/

/-- Parse an `AUTHS` array `[A,...]` (or `[]`), validating each tag fail-closed. -/
def parseAuths (cs : PState) : Option (List Auth × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List Auth × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseNat cs with
          | none => none
          | some (tag, r1) =>
            match authOfTag tag with
            | none => none
            | some a =>
              match lit "," r1 with
              | some r2 => match loop fuel r2 with
                           | some (rest, r3) => some (a :: rest, r3)
                           | none => none
              | none => match lit "]" r1 with
                        | some r3 => some ([a], r3)
                        | none => none
      loop (cs.length + 1) r0

/-- Parse one `CAP` (`null`/`node`/`ep`). -/
def parseCap (cs : PState) : Option (Cap × PState) :=
  match lit "{\"null\":0}" cs with
  | some rest => some (Cap.null, rest)
  | none =>
  match lit "{\"node\":" cs with
  | some rest => match parseNat rest with
                 | some (t, r) => (lit "}" r).map (fun r' => (Cap.node t, r'))
                 | none => none
  | none =>
  match lit "{\"ep\":[" cs with
  | some rest =>
    match parseNat rest with
    | none => none
    | some (t, r1) =>
      match lit "," r1 with
      | none => none
      | some r2 =>
        match parseAuths r2 with
        | none => none
        | some (auths, r3) =>
          match lit "]" r3 with
          | none => none
          | some r4 => (lit "}" r4).map (fun r5 => (Cap.endpoint t auths, r5))
  | none => none

/-- Parse a `CAPLIST` array `[CAP,...]` (or `[]`). -/
def parseCapList (cs : PState) : Option (List Cap × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List Cap × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCap cs with
          | none => none
          | some (c, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (c :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([c], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- Parse one `CAPENTRY` `[holder,CAPLIST]`. -/
def parseCapEntry (cs : PState) : Option ((CellId × List Cap) × PState) :=
  match lit "[" cs with
  | none => none
  | some r1 =>
    match parseNat r1 with
    | none => none
    | some (holder, r2) =>
      match lit "," r2 with
      | none => none
      | some r3 =>
        match parseCapList r3 with
        | none => none
        | some (cl, r4) => (lit "]" r4).map (fun r5 => ((holder, cl), r5))

/-- Parse the `CAPS` array `[CAPENTRY,...]` (or `[]`). -/
def parseCapsEntries (cs : PState) : Option (List (CellId × List Cap) × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List (CellId × List Cap) × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseCapEntry cs with
          | none => none
          | some (e, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (e :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([e], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- The decoded caps-bearing input: cell entries, the caps entries, and the turn fields. -/
structure WireInputCaps where
  cells : List (CellId × Value)
  caps  : List (CellId × List Cap)
  actor : CellId
  src   : CellId
  dst   : CellId
  amt   : Int

/-- Parse a full caps-bearing input state
`{"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}`. Strict: the whole string
must be consumed (fail-closed on any deviation). -/
def parseInputCaps (s : String) : Option WireInputCaps :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"caps\":" r1 with
      | none => none
      | some rc0 => match parseCapsEntries rc0 with
        | none => none
        | some (caps, rc1) =>
          match lit ",\"actor\":" rc1 with
          | none => none
          | some r2 => match parseNat r2 with
            | none => none
            | some (actor, r3) =>
              match lit ",\"src\":" r3 with
              | none => none
              | some r4 => match parseNat r4 with
                | none => none
                | some (src, r5) =>
                  match lit ",\"dst\":" r5 with
                  | none => none
                  | some r6 => match parseNat r6 with
                    | none => none
                    | some (dst, r7) =>
                      match lit ",\"amt\":" r7 with
                      | none => none
                      | some r8 => match parseInt r8 with
                        | none => none
                        | some (amt, r9) =>
                          match lit "}" r9 with
                          | some [] => some { cells := cells, caps := caps, actor := actor,
                                              src := src, dst := dst, amt := amt }
                          | _ => none

/-- Reconstruct the total `Caps` function from the decoded entries: a listed holder gets its
listed cap list, every other holder gets `[]` (matching the differential's regime — only
listed holders carry caps). -/
def capsOfEntries (entries : List (CellId × List Cap)) : Caps :=
  fun l => match entries.find? (fun p => p.1 == l) with
           | some p => p.2
           | none   => []

/-- Build a `RecordKernelState` from decoded cell entries AND the decoded caps table. Identical
to `stateOfCells` except the cap table is the marshalled one rather than empty — so the
cross-vat / held-cap branch of `authorizedB` is now exercised across the FFI. -/
def stateOfCellsCaps (cells : List (CellId × Value)) (caps : List (CellId × List Cap)) :
    RecordKernelState :=
  { accounts := (cells.map Prod.fst).toFinset
    cell := fun c => match cells.find? (fun p => p.1 == c) with
                     | some p => p.2
                     | none   => .record [(Exec.balanceField, .int 0)]
    caps := capsOfEntries caps }

/-- **C entry point — marshal record cell-state PLUS the held-cap table, run the PROVED
`recKExec`, marshal back.**

The caps-bearing analog of `recordKernelStep`: the input now also carries the `Caps` table, so
the authority gate (`Kernel.authorizedB`, reused unchanged by `recKExec`) can fire on a HELD cap
(`actor ≠ src` but the actor holds a `node src` cap or an `endpoint src` cap with `Auth.write`),
not just on ownership. The output wire is IDENTICAL to `recordKernelStep`'s
(`{"cells":CELLS,"ok":B}`) so the Rust decoder is shared. Fail-closed on a malformed wire
(`{"cells":[],"ok":0}`). The conservation/authority/fail-closed laws proved in `RecordKernel.lean`
hold of EVERY commit here — now including held-cap-authorized cross-vat turns. -/
@[export dregg_record_kernel_step_caps]
def recordKernelStepCaps (input : String) : String :=
  match parseInputCaps input with
  | none => encodeOut [] false
  | some wi =>
    let k := stateOfCellsCaps wi.cells wi.caps
    let ids := wi.cells.map Prod.fst
    let turn : Turn := { actor := wi.actor, src := wi.src, dst := wi.dst, amt := wi.amt }
    match Exec.recKExec k turn with
    | some k' => encodeOut (cellsOfState ids k') true
    | none    => encodeOut (cellsOfState ids k) false

/-! ### Codec round-trip sanity (`#eval`) — the Lean side of the differential. -/

/-- A two-cell input: cell 0 = `{balance:100, nonce:7}`, cell 1 = `{balance:5}`,
turn = actor 0 moves 30 from 0→1. -/
def wireDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}],[\"nonce\",{\"int\":7}]]}]," ++
  "[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"actor\":0,\"src\":0,\"dst\":1,\"amt\":30}"

#eval recordKernelStep wireDemo
-- Expect: {"cells":[[0,{"rec":[["balance",{"int":70}],["nonce",{"int":7}]]}],
--                   [1,{"rec":[["balance",{"int":35}]]}]],"ok":1}
#eval (parseInput wireDemo).isSome                                   -- true
-- Unauthorized actor 2 ⇒ fail-closed, cells unchanged, ok:0:
#eval recordKernelStep
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"actor\":2,\"src\":0,\"dst\":1,\"amt\":30}"
-- Malformed wire ⇒ fail-closed empty:
#eval recordKernelStep "garbage"                                      -- {"cells":[],"ok":0}

/-! ### Caps-bearing codec sanity (`#eval`) — the held-cap authorization round-trip. -/

/-- A held-cap-authorized case: cell 0 = `{balance:100}`, cell 1 = `{balance:5}`; the cap table
gives holder 9 (NOT the owner of src 0) an `endpoint 0 [write]` cap; actor 9 moves 30 from 0→1.
The cross-vat held-cap branch of `authorizedB` fires, so this COMMITS. -/
def wireCapsDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
  "\"caps\":[[9,[{\"ep\":[0,[1]]}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"

#eval recordKernelStepCaps wireCapsDemo
-- Expect ok:1 (held-cap authorized): {"cells":[[0,{"rec":[["balance",{"int":70}]]}],
--                                              [1,{"rec":[["balance",{"int":35}]]}]],"ok":1}
#eval (parseInputCaps wireCapsDemo).isSome                            -- true

-- A `node 0` cap (control ⇒ everything) held by actor 9 also authorizes the cross-vat move.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[[9,[{\"node\":0}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:1.

-- Unauthorized: actor 9 holds only a READ-only endpoint on src 0 (no `write`), and is not the
-- owner ⇒ `authorizedB` is false ⇒ fail-closed, cells unchanged, ok:0.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[[9,[{\"ep\":[0,[0]]}]]],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:0 (read-only cap does not confer write authority).

-- No cap at all for actor 9 ⇒ fail-closed, ok:0.
#eval recordKernelStepCaps
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]],\"caps\":[],\"actor\":9,\"src\":0,\"dst\":1,\"amt\":30}"
-- Expect ok:0.

-- Malformed caps wire ⇒ fail-closed empty:
#eval recordKernelStepCaps "garbage"                                  -- {"cells":[],"ok":0}

/-! ## §FULL — the FULL-TURN export: `execFullTurn` over a `List FullAction`.

`recordKernelStep[Caps]` above run ONE `recKExec` step (single transfer) ± caps. The node's real
turn-decision is `TurnExecutorFull.execFullTurn` — an ALL-OR-NOTHING transaction over a
`List FullAction` (balance/delegate/revoke/mint/burn). This section marshals a whole
`(RecChainedState, List FullAction)` across the wire, runs the PROVED `execFullTurn`, and re-encodes
the resulting `Option` state — INCLUDING the rollback case (any failing action aborts the whole turn,
leaving state unchanged; on the wire this is `ok:0` echoing the unchanged input).

The full-turn wire grammar (additive; reuses CELLS/CAPS/VALUE codecs above):

    turn   := {"cells":CELLS,"caps":CAPS,"actions":ACTIONS}
    out    := {"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}     (B ∈ {0,1})
    ACTIONS:= [] | [ACTION(,ACTION)*]
    ACTION := {"bal":[M,E,actor,src,dst,amt]}     (M = method Nat, E = effect-kind tag Nat)
            | {"del":[delegator,recipient,t]}
            | {"rev":[holder,t]}
            | {"mint":[actor,cell,amt]}
            | {"burn":[actor,cell,amt]}

The OUTPUT carries the post-state caps too, because `delegate`/`revoke` MUTATE the cap table — they
are observable across the seam only if echoed back. We emit caps at the OBSERVABLE label set: every
label appearing in the input caps OR in any action (actor/src/dst/holder/delegator/recipient/target),
in a deterministic sorted order, so the Rust reference can compare positionally.

Like the rest of the codec this is TCB (cross-validated by the differential, NOT proved). The
PROVED function underneath is `execFullTurn`, carrying `execFullTurn_ledger`/`_conserves`/
`_each_attests` (`TurnExecutorFull.lean §10`): every committed turn attests the four StepInv
conjuncts per action by construction. -/

open Dregg2.Exec.TurnExecutorFull (FullAction execFull execFullTurn)
open Dregg2.Exec.TurnExecutor (Action)
open Dregg2.CatalogInstances (EffectKind)

/-! ### Effect-kind tag ⇄ `EffectKind` (a minimal enumeration — only the conservation-relevant
balance kinds are reachable through the balance branch of `execFull`, which RUNS `recCexec s a.move`
and is INDIFFERENT to the `effect`/`method` tag; we round-trip the tag faithfully nonetheless). -/

/-- Encode an `EffectKind` to a wire tag. Only `transfer` (the canonical balance op) is given a
distinguished tag `1`; every other kind maps to `0` (`setField`, the inert default) — sufficient
because the balance branch of `execFull` does not read the effect. -/
def effectTag : EffectKind → Nat
  | .transfer => 1
  | _         => 0

/-- Decode a wire tag to an `EffectKind` (fail-OPEN to `setField`/`transfer`; the executor is
indifferent, so any tag yields a valid balance action). -/
def effectOfTag : Nat → EffectKind
  | 1 => .transfer
  | _ => .setField

/-! ### Action encoder. -/

/-- Encode one `FullAction` to its wire form. -/
def encodeAction : FullAction → String
  | .balance a =>
      "{\"bal\":[" ++ toString a.method ++ "," ++ toString (effectTag a.effect) ++ ","
        ++ toString a.move.actor ++ "," ++ toString a.move.src ++ ","
        ++ toString a.move.dst ++ "," ++ toString a.move.amt ++ "]}"
  | .delegate del rec t =>
      "{\"del\":[" ++ toString del ++ "," ++ toString rec ++ "," ++ toString t ++ "]}"
  | .revoke holder t =>
      "{\"rev\":[" ++ toString holder ++ "," ++ toString t ++ "]}"
  | .mint actor cell amt =>
      "{\"mint\":[" ++ toString actor ++ "," ++ toString cell ++ "," ++ toString amt ++ "]}"
  | .burn actor cell amt =>
      "{\"burn\":[" ++ toString actor ++ "," ++ toString cell ++ "," ++ toString amt ++ "]}"

/-- Encode an `ACTIONS` array. -/
def encodeActions : List FullAction → String
  | []      => "[]"
  | a :: as =>
      "[" ++ encodeAction a ++ (as.foldl (fun acc x => acc ++ "," ++ encodeAction x) "") ++ "]"

/-- Encode the full-turn output: post-state cells + post-state caps (at the observable labels) +
the receipt-log length + the commit bit. -/
def encodeFullOut (cells : List (CellId × Value)) (caps : List (CellId × List Cap))
    (loglen : Nat) (ok : Bool) : String :=
  "{\"cells\":" ++ encodeCells cells
    ++ ",\"caps\":" ++ encodeCapsEntries caps
    ++ ",\"loglen\":" ++ toString loglen
    ++ ",\"ok\":" ++ (if ok then "1" else "0") ++ "}"

/-! ### Action decoder. -/

/-- Parse a fixed-length comma-separated tuple of signed integers of the given arity, having
consumed the opening `[`. Returns the ints and the rest (after the closing `]`). -/
def parseIntTuple : Nat → PState → Option (List Int × PState)
  | 0,      _  => none
  | 1,      cs =>
      match parseInt cs with
      | none => none
      | some (i, r) => (lit "]" r).map (fun r' => ([i], r'))
  | n + 1,  cs =>
      match parseInt cs with
      | none => none
      | some (i, r) =>
        match lit "," r with
        | none => none
        | some r' => (parseIntTuple n r').map (fun (xs, r'') => (i :: xs, r''))

/-- Parse one `ACTION`. -/
def parseAction (cs : PState) : Option (FullAction × PState) :=
  match lit "{\"bal\":[" cs with
  | some rest =>
    match parseIntTuple 6 rest with
    | some ([m, e, actor, src, dst, amt], r) =>
        (lit "}" r).map (fun r' =>
          (FullAction.balance
            { method := m.toNat, effect := effectOfTag e.toNat,
              move := { actor := actor.toNat, src := src.toNat, dst := dst.toNat, amt := amt } }, r'))
    | _ => none
  | none =>
  match lit "{\"del\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([del, rec, t], r) =>
        (lit "}" r).map (fun r' => (FullAction.delegate del.toNat rec.toNat t.toNat, r'))
    | _ => none
  | none =>
  match lit "{\"rev\":[" cs with
  | some rest =>
    match parseIntTuple 2 rest with
    | some ([holder, t], r) =>
        (lit "}" r).map (fun r' => (FullAction.revoke holder.toNat t.toNat, r'))
    | _ => none
  | none =>
  match lit "{\"mint\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([actor, cell, amt], r) =>
        (lit "}" r).map (fun r' => (FullAction.mint actor.toNat cell.toNat amt, r'))
    | _ => none
  | none =>
  match lit "{\"burn\":[" cs with
  | some rest =>
    match parseIntTuple 3 rest with
    | some ([actor, cell, amt], r) =>
        (lit "}" r).map (fun r' => (FullAction.burn actor.toNat cell.toNat amt, r'))
    | _ => none
  | none => none

/-- Parse an `ACTIONS` array `[ACTION,...]` (or `[]`). Fuel-bounded on the count. -/
def parseActions (cs : PState) : Option (List FullAction × PState) :=
  match lit "[]" cs with
  | some rest => some ([], rest)
  | none =>
    match lit "[" cs with
    | none => none
    | some r0 =>
      let rec loop (fuel : Nat) (cs : PState) : Option (List FullAction × PState) :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match parseAction cs with
          | none => none
          | some (a, r1) =>
            match lit "," r1 with
            | some r2 => match loop fuel r2 with
                         | some (rest, r3) => some (a :: rest, r3)
                         | none => none
            | none => match lit "]" r1 with
                      | some r3 => some ([a], r3)
                      | none => none
      loop (cs.length + 1) r0

/-- The decoded full-turn input: cell entries, the caps entries, and the action list. -/
structure WireFullTurn where
  cells   : List (CellId × Value)
  caps    : List (CellId × List Cap)
  actions : List FullAction

/-- Parse a full-turn input `{"cells":CELLS,"caps":CAPS,"actions":ACTIONS}`. Strict: the whole
string must be consumed (fail-closed on any deviation). -/
def parseFullTurn (s : String) : Option WireFullTurn :=
  let cs := s.toList
  let fuel := cs.length + 1
  match lit "{\"cells\":" cs with
  | none => none
  | some r0 =>
    match parseCells fuel r0 with
    | none => none
    | some (cells, r1) =>
      match lit ",\"caps\":" r1 with
      | none => none
      | some rc0 => match parseCapsEntries rc0 with
        | none => none
        | some (caps, rc1) =>
          match lit ",\"actions\":" rc1 with
          | none => none
          | some ra0 => match parseActions ra0 with
            | none => none
            | some (actions, ra1) =>
              match lit "}" ra1 with
              | some [] => some { cells := cells, caps := caps, actions := actions }
              | _ => none

/-- Every cell-label and action-label observed in the input (for the deterministic caps readout):
the union of input cap holders, input cell ids, and every label mentioned by any action. Sorted
ascending and de-duplicated so the Rust side compares positionally. -/
def observedLabels (wi : WireFullTurn) : List CellId :=
  let fromCaps := wi.caps.map Prod.fst
  let fromCells := wi.cells.map Prod.fst
  let fromActions := wi.actions.flatMap (fun
    | .balance a          => [a.move.actor, a.move.src, a.move.dst]
    | .delegate del rec t => [del, rec, t]
    | .revoke holder t    => [holder, t]
    | .mint actor cell _  => [actor, cell]
    | .burn actor cell _  => [actor, cell])
  ((fromCaps ++ fromCells ++ fromActions).foldl
      (fun acc l => if acc.contains l then acc else l :: acc) []).mergeSort (· ≤ ·)

/-- Read the post-state caps at the observed labels, in the SAME sorted order, dropping empty
slots' presence by still listing the label with `[]` (so the wire is positionally deterministic). -/
def capsOfState (labels : List CellId) (k : RecordKernelState) : List (CellId × List Cap) :=
  labels.map (fun l => (l, k.caps l))

/-- **C entry point — marshal a full `(RecChainedState, List FullAction)`, run the PROVED
`execFullTurn`, marshal back.**

This is THE swap-enabler: the whole turn decision-maker. The input is a canonical JSON encoding of a
`RecChainedState` (cells + caps + an EMPTY initial log) plus the `List FullAction`; we decode it, run
the SAME `TurnExecutorFull.execFullTurn` whose ledger/conservation/step-completeness laws are proved
(`TurnExecutorFull.lean §10`), and re-encode the result.

ALL-OR-NOTHING: on a committed turn we emit the post-state cells + post-state caps + the receipt-log
length (which equals the number of committed actions) with `ok:1`. On a turn that fails mid-way
(`execFullTurn = none`) we ECHO the UNCHANGED input cells + input caps with `loglen:0` and `ok:0` —
the rollback is observable: state is exactly the pre-state. On a malformed wire we fail-closed to
`{"cells":[],"caps":[],"loglen":0,"ok":0}`. -/
@[export dregg_exec_full_turn]
def execFullTurnStep (input : String) : String :=
  match parseFullTurn input with
  | none => encodeFullOut [] [] 0 false
  | some wi =>
    let k0 := stateOfCellsCaps wi.cells wi.caps
    let s0 : RecChainedState := { kernel := k0, log := [] }
    let ids := wi.cells.map Prod.fst
    let labels := observedLabels wi
    match execFullTurn s0 wi.actions with
    | some s' =>
        encodeFullOut (cellsOfState ids s'.kernel) (capsOfState labels s'.kernel) s'.log.length true
    | none =>
        -- All-or-nothing ROLLBACK: echo the unchanged pre-state, ok:0, empty log.
        encodeFullOut (cellsOfState ids s0.kernel) (capsOfState labels s0.kernel) 0 false

/-! ### Full-turn codec sanity (`#eval`) — the Lean side of the multi-action differential. -/

/-- A mixed full-turn over two cells: actor 9 (holds `node 0`) mints +50 to cell 0, then owner 0
transfers 30 → cell 1, then burns -50 from cell 0. Nets to 0; all commit; log grows by 3. -/
def wireFullDemo : String :=
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
  "\"caps\":[[9,[{\"node\":0}]]]," ++
  "\"actions\":[{\"mint\":[9,0,50]},{\"bal\":[0,1,0,0,1,30]},{\"burn\":[9,0,50]}]}"

#eval execFullTurnStep wireFullDemo
-- Expect ok:1, loglen:3, cell0.balance = 100+50-30-50 = 70, cell1.balance = 5+30 = 35.
#eval (parseFullTurn wireFullDemo).isSome                              -- true

-- ROLLBACK: a turn whose 2nd action is unauthorized (actor 0 cannot mint) ⇒ whole turn none ⇒
-- echo unchanged pre-state, ok:0, loglen:0.
#eval execFullTurnStep
  ("{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
   "\"caps\":[[9,[{\"node\":0}]]]," ++
   "\"actions\":[{\"mint\":[9,0,50]},{\"mint\":[0,0,50]}]}")
-- Expect ok:0, loglen:0, cells = {100, 5} (UNCHANGED — rollback).

-- A DELEGATE then REVOKE turn (caps mutate, balances fixed):
#eval execFullTurnStep
  ("{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}],[1,{\"rec\":[[\"balance\",{\"int\":5}]]}]]," ++
   "\"caps\":[[0,[{\"node\":7}]]]," ++
   "\"actions\":[{\"del\":[0,1,7]},{\"rev\":[0,7]}]}")
-- Expect ok:1, loglen:2; recipient 1 gains a `node 7` cap; holder 0 loses its `node 7` edge.

-- Empty turn ⇒ commits trivially, loglen:0, state unchanged.
#eval execFullTurnStep
  "{\"cells\":[[0,{\"rec\":[[\"balance\",{\"int\":100}]]}]],\"caps\":[],\"actions\":[]}"
-- Expect ok:1, loglen:0.

-- Malformed wire ⇒ fail-closed empty.
#eval execFullTurnStep "garbage"   -- {"cells":[],"caps":[],"loglen":0,"ok":0}

