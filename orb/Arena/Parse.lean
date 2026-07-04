/-
Arena — an executable HTTP/1.1 request-head parser written AS the model.

This is the runnable face of the arena theory: it parses a request line +
header fields into the two-arena `Store` representation (main arena = the wire
bytes; sidecar arena = synthesized canonical header names) and registers every
view range as an `Entry`. Of the two hypotheses the theory carries:

* `Store.Wf` holds *statically*: `parse_wf` (Arena/ParseTheorems.lean) proves
  every store a `complete` outcome carries is well-formed — including the
  sidecar entries the canonicalization path synthesizes — so the parser runs
  no well-formedness check (the old runtime `wfCheck` gate and its
  `internal-wf-violation` error class were provably dead and are gone);
* `Store.WfUtf8` is *dynamically discharged* via `String.validateUTF8` per
  resolved range — content validity is the one hypothesis that genuinely
  enters at runtime.

Total by construction (structural recursion only), written for clarity over
speed. Canonicalization: header names are lowercased; a name that is already
lowercase points into the main arena, otherwise the lowered bytes are appended
to the sidecar and the entry's offset carries the sidecar discriminant
(`sidecarBase + sidecarOffset`).
-/
import Arena.Basic
import Arena.Theorems

namespace Arena
namespace Parse

/-- Wire bytes as a list (clarity over speed). -/
abbrev Bytes := List UInt8

def CR : UInt8 := 13
def LF : UInt8 := 10
def SP : UInt8 := 32
def HTAB : UInt8 := 9
def COLON : UInt8 := 58

/-- A `(offset, length)` span, in `Nat`, relative to the start of the input. -/
structure Span where
  off : Nat
  len : Nat
  deriving Repr, DecidableEq

/-- The bytes a span denotes. -/
def sliceSpan (bs : Bytes) (s : Span) : Bytes :=
  (bs.drop s.off).take s.len

/-- Offset of the first `CRLFCRLF`, if any. -/
def findDoubleCrlf : Bytes → Option Nat
  | a :: rest@(b :: c :: d :: _) =>
    if a == CR && b == LF && c == CR && d == LF then some 0
    else (findDoubleCrlf rest).map (· + 1)
  | _ => none

/-- Offsets of every `CRLF` within `bs`. -/
def crlfPositions (bs : Bytes) : List Nat :=
  (List.range bs.length).filter fun i =>
    bs.getD i 0 == CR && bs.getD (i + 1) 0 == LF

/-- Cut `[start, headLen)` into the segments between the given `CRLF`
positions (each position `p` consumes bytes `p` and `p+1`). -/
def segments (start headLen : Nat) : List Nat → List Span
  | [] => [⟨start, headLen - start⟩]
  | p :: ps => ⟨start, p - start⟩ :: segments (p + 2) headLen ps

def findByteIdx (t : UInt8) (l : Bytes) : Option Nat :=
  l.findIdx? (· == t)

def isOws (b : UInt8) : Bool := b == SP || b == HTAB

/-- The DEL byte (`0x7F`). -/
def DEL : UInt8 := 127

/-- RFC 7230 field-value discipline for a single header-value byte: a value
byte must be SP, HTAB, a visible ASCII char (`0x21`–`0x7E`), or obs-text
(`0x80`–`0xFF`). The bytes this predicate flags are exactly the ones a value
may not contain: the C0 control bytes other than HTAB (so `NUL`, `CR`, `LF`,
… below `0x20`) and the DEL byte. -/
def isCtlValueByte (b : UInt8) : Bool := (b < SP && b != HTAB) || b == DEL

/-- `"HTTP/"` prefix check for the version field. -/
def startsWithHttpSlash : Bytes → Bool
  | h :: t₁ :: t₂ :: p :: sl :: _ =>
    h == 72 && t₁ == 84 && t₂ == 84 && p == 80 && sl == 47
  | _ => false

structure ReqLineSpans where
  method : Span
  target : Span
  version : Span
  deriving Repr

/-- Parse a request line at absolute offset `off`: exactly three
space-separated parts, non-empty method, version starting `HTTP/`. -/
def parseRequestLine (off : Nat) (line : Bytes) : Option ReqLineSpans := do
  let i₁ ← findByteIdx SP line
  let rest₁ := line.drop (i₁ + 1)
  let i₂ ← findByteIdx SP rest₁
  let rest₂ := rest₁.drop (i₂ + 1)
  if (findByteIdx SP rest₂).isSome then none
  else if i₁ == 0 then none
  else if !startsWithHttpSlash rest₂ then none
  else
    some
      { method := ⟨off, i₁⟩
        target := ⟨off + i₁ + 1, i₂⟩
        version := ⟨off + i₁ + 1 + i₂ + 1, rest₂.length⟩ }

structure RawHeaderSpans where
  name : Span
  value : Span
  deriving Repr

/-- Parse one header line at absolute offset `off`: a non-empty,
whitespace-free name before the first `:`, then the value with leading and
trailing optional whitespace (SP / HTAB) trimmed. The value must satisfy the
RFC 7230 field-value discipline (`isCtlValueByte`): a control byte other than
HTAB (in particular `NUL`) — or DEL — anywhere in the value rejects the line.
The OWS trim only strips SP / HTAB, neither of which `isCtlValueByte` flags, so
checking the raw value is equivalent to checking the trimmed value. -/
def parseHeaderLine (off : Nat) (line : Bytes) : Option RawHeaderSpans := do
  let ci ← findByteIdx COLON line
  if ci == 0 then none
  else
    let name := line.take ci
    if name.any (fun b => isOws b || b == CR || b == LF) then none
    else
      let rawVal := line.drop (ci + 1)
      if rawVal.any isCtlValueByte then none
      else
        let lead := (rawVal.takeWhile isOws).length
        let trimmedFront := rawVal.drop lead
        let trail := (trimmedFront.reverse.takeWhile isOws).length
        some
          { name := ⟨off, ci⟩
            value := ⟨off + ci + 1 + lead, trimmedFront.length - trail⟩ }

/-! ## Canonicalization into the sidecar -/

def isUpperAscii (b : UInt8) : Bool := decide (65 ≤ b ∧ b ≤ 90)

def lowerByte (b : UInt8) : UInt8 := if isUpperAscii b then b + 32 else b

def hasUpper (l : Bytes) : Bool := l.any isUpperAscii

def mkEntry (tag : NameTag) (off len : Nat) : Entry :=
  { tag, off := UInt32.ofNat off, len := UInt32.ofNat len }

/-- The canonical (lowercase) name entry for a raw name span. Already-lowercase
names point into the main arena; otherwise the lowered bytes are appended to
the sidecar and the entry addresses them through the sidecar discriminant. -/
def canonNameEntry (input sidecar : Bytes) (sp : Span) : Bytes × Entry :=
  let raw := sliceSpan input sp
  if hasUpper raw then
    (sidecar ++ raw.map lowerByte,
     mkEntry .headerName (sidecarBaseNat + sidecar.length) sp.len)
  else
    (sidecar, mkEntry .headerName sp.off sp.len)

/-! ## The parse outcome -/

/-- Typed error classes of the head parse. -/
inductive ErrClass where
  /-- The request line is not `method SP target SP HTTP/…`. -/
  | malformedRequestLine
  /-- A header line is not `name ":" OWS value OWS` with a clean name and a
  control-free value, or the head carries more than `maxHeaders` header lines. -/
  | malformedHeader
  /-- A referenced range failed the explicit UTF-8 hypothesis. -/
  | nonUtf8
  /-- Input exceeds the 31-bit addressable range of the main arena. -/
  | tooLarge
  deriving Repr, DecidableEq

def ErrClass.tag : ErrClass → String
  | .malformedRequestLine => "malformed-request-line"
  | .malformedHeader => "malformed-header"
  | .nonUtf8 => "non-utf8"
  | .tooLarge => "too-large"

structure ParsedHeader where
  name : Entry
  value : Entry
  deriving Repr

/-- A parsed request head: the store plus the tagged view entries. -/
structure Request where
  store : Store
  method : Entry
  target : Entry
  version : Entry
  headers : List ParsedHeader
  consumed : Nat
  deriving Repr

inductive Outcome where
  /-- The head parsed; the store is well-formed by `parse_wf` (a theorem, not
  a runtime check) and every range passed the UTF-8 check. -/
  | complete (req : Request)
  /-- No `CRLFCRLF` yet — need more bytes. No consumed count exists. -/
  | incomplete
  | error (e : ErrClass) (detail : String)

/-- Parse all header lines, accumulating the sidecar and parsed headers. -/
def parseHeaders (input : Bytes) (spans : List Span) (sidecar : Bytes) :
    Option (Bytes × List ParsedHeader) :=
  match spans with
  | [] => some (sidecar, [])
  | sp :: rest =>
    if sp.len == 0 then
      -- an empty segment inside the head (bare CRLF) is malformed
      none
    else do
      let raw ← parseHeaderLine sp.off (sliceSpan input sp)
      let (sidecar', nameEntry) := canonNameEntry input sidecar raw.name
      let valueEntry := mkEntry .headerValue raw.value.off raw.value.len
      let (sidecar'', parsed) ← parseHeaders input rest sidecar'
      some (sidecar'', { name := nameEntry, value := valueEntry } :: parsed)

/-- Default header-count bound: the number of header lines a head may carry
before the parser refuses it. `64` matches the slot cap the hand-written
differential baselines enforce; it caps the unbounded-allocation surface an
attacker reaches for with a header flood. -/
def defaultMaxHeaders : Nat := 64

/-- The head parser: bytes → arena view. Total; every referenced range is
registered in the store. The store of every `complete` outcome is well-formed
*by theorem* (`parse_wf`, Arena/ParseTheorems.lean); the explicit UTF-8
hypothesis is the one check discharged dynamically before a `complete` is
produced. `maxHeaders` is the configurable header-count bound (default
`defaultMaxHeaders`): a head with more than `maxHeaders` header lines is
refused as `malformedHeader`, so the parser never registers an unbounded
number of entries. -/
def parse (input : Bytes) (maxHeaders : Nat := defaultMaxHeaders) : Outcome :=
  if sidecarBaseNat ≤ input.length then
    .error .tooLarge "input exceeds the 2^31-1 addressable range"
  else
    match findDoubleCrlf input with
    | none => .incomplete
    | some headEnd =>
      let consumed := headEnd + 4
      let head := input.take headEnd
      match segments 0 headEnd (crlfPositions head) with
      | [] => .error .malformedRequestLine "empty head"
      | reqSpan :: headerSpans =>
        match parseRequestLine reqSpan.off (sliceSpan input reqSpan) with
        | none => .error .malformedRequestLine "want: method SP target SP HTTP/…"
        | some rl =>
          match parseHeaders input headerSpans [] with
          | none => .error .malformedHeader "want: name \":\" OWS value OWS"
          | some (sidecar, headers) =>
            -- Header-count bound: refuse a head that carries more than
            -- `maxHeaders` header lines before any entry is registered.
            if maxHeaders < headers.length then
              .error .malformedHeader "header count exceeds the configured bound"
            else
              let methodE := mkEntry .method rl.method.off rl.method.len
              let targetE := mkEntry .target rl.target.off rl.target.len
              let versionE := mkEntry .version rl.version.off rl.version.len
              let allEntries :=
                methodE :: targetE :: versionE ::
                  headers.flatMap fun h => [h.name, h.value]
              -- `entries := allEntries.reverse` keeps the registration order the
              -- old `foldl Store.pushEntry` produced (each push consed).
              let store : Store :=
                { main := input.toArray, sidecar := sidecar.toArray,
                  entries := allEntries.reverse }
              -- `store.Wf` needs no runtime gate: `parse_wf` proves every store
              -- built here is well-formed (so the `none` arm below is provably
              -- dead too — `Store.resolve_total` — but `resolve` is total-as-
              -- Option, so the match must still spell it).
              -- Dynamic discharge of the explicit UTF-8 hypothesis, per range:
              if allEntries.any (fun e =>
                  match store.resolve e with
                  | some b => !(decide (Utf8Valid b))
                  | none => true) then
                .error .nonUtf8 "a referenced range is not valid UTF-8"
              else
                .complete
                  { store, method := methodE, target := targetE,
                    version := versionE, headers, consumed }

end Parse
end Arena
