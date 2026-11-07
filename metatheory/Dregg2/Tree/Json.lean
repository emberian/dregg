/-
# Dregg2.Tree.Json: the projection from JSON text bytes to the model

`parse` reads RFC 8259 JSON over bytes and returns the value in the model of `Dregg2.Tree.Value`,
canonicalized as GROUNDING §3 decides:

* **Numbers are exact.** The grammar `-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?` is read into
  an exact `(m, e)` with value `m·10^e` and normalized by `mkNum`: integers (`-0`, `1.0`, `10e-1`,
  `1e400`) are `int`, everything else is a `dec` with `10 ∤ m`. No `Float` is involved. The written
  exponent is capped at `4096` in magnitude and a number beyond it is refused: `1e4096` is a
  13.6-kbit integer, while the earlier cap of `10^6` admitted `1e1000000`, a 3.3-Mbit integer on
  which `Value.natBytes` (quadratic in its length) did not finish in two minutes. A projection of
  untrusted records also caps the input length.
* **Escapes are decoded, Unicode is not normalized.** `\uXXXX`, surrogate pairs and the short
  escapes become their UTF-8 bytes; a lone surrogate is refused; raw control bytes are refused; the
  decoded string must be valid UTF-8. NFC and NFD spellings stay two leaves.
* **Duplicate keys are refused** (compared after escape decoding); entries are then sorted by
  `keyLt`, the RFC 8949 §4.2.1 order.
* Nesting is fuelled by the input length. Every call in the recursion is charged to a distinct
  input byte (a value's first byte, or the `[`, `{` or `,` before an element), so fuel
  `b.length + 1` never runs out on input the grammar accepts.

The last step keeps a result only if `WF` holds, so `parse_wf` is immediate; the pins below show
that check is not what does the work.

Lean core only: this links into the `tree-check` executable.
-/
import Dregg2.Tree.Value

namespace Dregg2.Tree.Json

/- v4.35: keep `==` on `UInt8` on instBEqOfDecidableEq rather than core's choice-built
`Std.LinearOrderPackage` BEq (see Tree/Value.lean). -/
attribute [local instance high] instBEqOfDecidableEq

/-! ## Numbers -/

/-- Strip trailing decimal zeros of `m` while the exponent is negative (`k` bounds the steps). -/
def stripZeros : Nat → Int → Int → Int × Int
  | 0, m, e => (m, e)
  | k + 1, m, e => if m % 10 = 0 ∧ m ≠ 0 then stripZeros k (m / 10) (e + 1) else (m, e)

/-- The canonical number for the value `m · 10^e`. -/
def mkNum (m : Int) (e : Int) : JVal :=
  if m = 0 then .int 0
  else
    let r := stripZeros (-e).toNat m e
    if 0 ≤ r.2 then .int (r.1 * 10 ^ r.2.toNat) else .dec r.1 r.2

theorem stripZeros_spec : ∀ (k : Nat) (m e : Int), k = (-e).toNat → m ≠ 0 →
    0 ≤ (stripZeros k m e).2 ∨ (stripZeros k m e).1 % 10 ≠ 0
  | 0, m, e, hk, _ => by simp [stripZeros]; omega
  | k + 1, m, e, hk, hm => by
    unfold stripZeros
    by_cases h : m % 10 = 0 ∧ m ≠ 0
    · rw [if_pos h]
      exact stripZeros_spec k (m / 10) (e + 1) (by omega) (by omega)
    · rw [if_neg h]; right; omega

/-- A `dec` out of `mkNum` is canonical. -/
theorem mkNum_wf_dec {m e m' e' : Int} (h : mkNum m e = .dec m' e') : decCanon m' e' = true := by
  unfold mkNum at h
  by_cases hm : m = 0
  · rw [if_pos hm] at h; cases h
  · rw [if_neg hm] at h
    simp only at h
    by_cases he : 0 ≤ (stripZeros (-e).toNat m e).2
    · rw [if_pos he] at h; cases h
    · rw [if_neg he] at h
      cases h
      have := stripZeros_spec (-e).toNat m e rfl hm
      simp [decCanon]; omega

/-! ## Lexical helpers -/

def isWs (c : UInt8) : Bool := c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D

def skipWs : List UInt8 → List UInt8
  | c :: r => if isWs c then skipWs r else c :: r
  | [] => []

def isDigit (c : UInt8) : Bool := 0x30 ≤ c && c ≤ 0x39

/-- The longest digit prefix and the rest. -/
def spanDigits : List UInt8 → List UInt8 × List UInt8
  | c :: r =>
    if isDigit c then let p := spanDigits r; (c :: p.1, p.2) else ([], c :: r)
  | [] => ([], [])

def digitsVal (ds : List UInt8) : Nat := ds.foldl (fun a d => a * 10 + (d.toNat - 0x30)) 0

/-- The written exponent's magnitude cap. -/
def expCap : Nat := 4096

/-- Optional exponent part: `(exponent, rest)`, or `none` on a malformed or over-cap exponent. -/
def pExp : List UInt8 → Option (Int × List UInt8)
  | c :: r =>
    if c == 0x65 || c == 0x45 then
      let (neg, r) := match r with
        | 0x2B :: r => (false, r)
        | 0x2D :: r => (true, r)
        | r => (false, r)
      let (es, r) := spanDigits r
      let v := digitsVal es
      if es.isEmpty || expCap < v then none
      else some (if neg then -(v : Int) else v, r)
    else some (0, c :: r)
  | [] => some (0, [])

/-- A number token, exact. -/
def pNum (b : List UInt8) : Option (JVal × List UInt8) :=
  let (neg, b) := match b with
    | 0x2D :: r => (true, r)
    | r => (false, r)
  let (ids, b) := spanDigits b
  match ids with
  | [] => none
  | d :: ds =>
    if d == 0x30 && !ds.isEmpty then none   -- leading zero
    else
      let frac : Option (List UInt8 × List UInt8) := match b with
        | 0x2E :: r => let (fs, r) := spanDigits r; if fs.isEmpty then none else some (fs, r)
        | r => some ([], r)
      match frac with
      | none => none
      | some (fs, b) =>
        match pExp b with
        | none => none
        | some (x, b) =>
          let mag : Int := digitsVal (ids ++ fs)
          some (mkNum (if neg then -mag else mag) (x - fs.length), b)

/-! ## Strings -/

def hexVal (c : UInt8) : Option Nat :=
  if 0x30 ≤ c && c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x61 ≤ c && c ≤ 0x66 then some (c.toNat - 0x61 + 10)
  else if 0x41 ≤ c && c ≤ 0x46 then some (c.toNat - 0x41 + 10)
  else none

def hex4 (a b c d : UInt8) : Option Nat :=
  match hexVal a, hexVal b, hexVal c, hexVal d with
  | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d)
  | _, _, _, _ => none

/-- UTF-8 bytes of a scalar value (callers pass no surrogates and nothing above U+10FFFF). -/
def cpUtf8 (u : Nat) : List UInt8 :=
  if u < 0x80 then [UInt8.ofNat u]
  else if u < 0x800 then [UInt8.ofNat (0xC0 + u / 0x40), UInt8.ofNat (0x80 + u % 0x40)]
  else if u < 0x10000 then
    [UInt8.ofNat (0xE0 + u / 0x1000), UInt8.ofNat (0x80 + u / 0x40 % 0x40),
     UInt8.ofNat (0x80 + u % 0x40)]
  else
    [UInt8.ofNat (0xF0 + u / 0x40000), UInt8.ofNat (0x80 + u / 0x1000 % 0x40),
     UInt8.ofNat (0x80 + u / 0x40 % 0x40), UInt8.ofNat (0x80 + u % 0x40)]

/-- The short escapes `\" \\ \/ \b \f \n \r \t`. -/
def shortEsc (c : UInt8) : Option UInt8 :=
  if c == 0x22 then some 0x22 else if c == 0x5C then some 0x5C
  else if c == 0x2F then some 0x2F else if c == 0x62 then some 0x08
  else if c == 0x66 then some 0x0C else if c == 0x6E then some 0x0A
  else if c == 0x72 then some 0x0D else if c == 0x74 then some 0x09
  else none

/-- String body after the opening quote; `acc` holds the decoded bytes reversed. -/
def pStrBody : List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | [], _ => none
  | 0x22 :: r, acc => some (acc.reverse, r)
  | 0x5C :: 0x75 :: a :: b :: c :: d :: r, acc =>
    match hex4 a b c d with
    | none => none
    | some u =>
      if 0xD800 ≤ u ∧ u < 0xDC00 then
        match r with
        | 0x5C :: 0x75 :: a' :: b' :: c' :: d' :: r' =>
          match hex4 a' b' c' d' with
          | some l =>
            if 0xDC00 ≤ l ∧ l < 0xE000 then
              pStrBody r' ((cpUtf8 (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00))).reverse ++ acc)
            else none
          | none => none
        | _ => none
      else if 0xDC00 ≤ u ∧ u < 0xE000 then none
      else pStrBody r ((cpUtf8 u).reverse ++ acc)
  | 0x5C :: c :: r, acc =>
    match shortEsc c with
    | some x => pStrBody r (x :: acc)
    | none => none
  | c :: r, acc => if c < 0x20 then none else pStrBody r (c :: acc)

/-- A string after its opening quote. The decoded bytes must be valid UTF-8; since every escape
contributes a complete UTF-8 sequence that starts with a non-continuation byte, this holds exactly
when every raw (unescaped) run is valid UTF-8. -/
def pStr (b : List UInt8) : Option (List UInt8 × List UInt8) :=
  match pStrBody b [] with
  | some (s, r) => if utf8Valid s then some (s, r) else none
  | none => none

/-! ## Objects -/

/-- Insert into a list sorted by `keyLt` (ties go after, so a duplicate ends up adjacent). -/
def insertKV (x : List UInt8 × JVal) : List (List UInt8 × JVal) → List (List UInt8 × JVal)
  | [] => [x]
  | y :: ys => if keyLt x.1 y.1 then x :: y :: ys else y :: insertKV x ys

def sortKVs (kvs : List (List UInt8 × JVal)) : List (List UInt8 × JVal) :=
  kvs.foldl (fun s x => insertKV x s) []

/-- Sorted entries, or `none` on a duplicate key (a sorted list that is not strictly increasing). -/
def mkObj (kvs : List (List UInt8 × JVal)) : Option JVal :=
  let s := sortKVs kvs
  if keysSorted s then some (.obj s) else none

/-! ## Values -/

mutual
/-- One value (leading whitespace skipped; trailing whitespace left). -/
def pValue : Nat → List UInt8 → Option (JVal × List UInt8)
  | 0, _ => none
  | fuel + 1, b =>
    match skipWs b with
    | 0x6E :: 0x75 :: 0x6C :: 0x6C :: r => some (.null, r)
    | 0x74 :: 0x72 :: 0x75 :: 0x65 :: r => some (.bool true, r)
    | 0x66 :: 0x61 :: 0x6C :: 0x73 :: 0x65 :: r => some (.bool false, r)
    | 0x22 :: r => (pStr r).map fun (s, r) => (.str s, r)
    | 0x5B :: r =>
      match skipWs r with
      | 0x5D :: r => some (.arr [], r)
      | _ => pItems fuel r []
    | 0x7B :: r =>
      match skipWs r with
      | 0x7D :: r => some (.obj [], r)
      | _ => pMembers fuel r []
    | r => pNum r
/-- Array elements after `[` or `,`; `acc` reversed. -/
def pItems : Nat → List UInt8 → List JVal → Option (JVal × List UInt8)
  | 0, _, _ => none
  | fuel + 1, b, acc =>
    match pValue fuel b with
    | none => none
    | some (v, r) =>
      match skipWs r with
      | 0x2C :: r => pItems fuel r (v :: acc)
      | 0x5D :: r => some (.arr (v :: acc).reverse, r)
      | _ => none
/-- Object members after `{` or `,`; `acc` reversed. -/
def pMembers : Nat → List UInt8 → List (List UInt8 × JVal) → Option (JVal × List UInt8)
  | 0, _, _ => none
  | fuel + 1, b, acc =>
    match skipWs b with
    | 0x22 :: r =>
      match pStr r with
      | none => none
      | some (k, r) =>
        match skipWs r with
        | 0x3A :: r =>
          match pValue fuel r with
          | none => none
          | some (v, r) =>
            match skipWs r with
            | 0x2C :: r => pMembers fuel r ((k, v) :: acc)
            | 0x7D :: r => (mkObj ((k, v) :: acc).reverse).map fun o => (o, r)
            | _ => none
        | _ => none
    | _ => none
end

/-- **The projection.** One JSON value, optional whitespace around it, nothing after; kept only
if it is canonical and admitted. -/
def parse (b : List UInt8) : Option JVal :=
  match pValue (b.length + 1) b with
  | some (v, r) => if skipWs r = [] ∧ WF v then some v else none
  | none => none

/-- What the projection returns is in the canonical form the checkers accept. -/
theorem parse_wf {b : List UInt8} {v : JVal} (h : parse b = some v) : WF v := by
  unfold parse at h
  split at h
  · split at h
    · cases h; rename_i hc; exact hc.2
    · cases h
  · cases h

def parseString (s : String) : Option JVal := parse s.toUTF8.toList

/-! ## Pins -/

private def u (s : String) : List UInt8 := s.toUTF8.toList

-- numbers: -0 is 0, 1.50 is 15·10⁻¹, 1e2 is the integer 100, keys sorted a before b
#guard parseString "{\"b\":1,\"a\":[true,null,-0,1.50,1e2,-2.5e-3]}" ==
  some (.obj [(u "a", .arr [.bool true, .null, .int 0, .dec 15 (-1), .int 100, .dec (-25) (-4)]),
              (u "b", .int 1)])
#guard parseString "0.000" == some (.int 0) && parseString "10e-1" == some (.int 1)
#guard parseString "1e400" == some (.int (10 ^ 400))
#guard parseString "1e-4096" == some (.dec 1 (-4096))
#guard parseString "1e4097" == none && parseString "1e-4097" == none
#guard parseString "1e1000001" == none   -- over the exponent cap
#guard parseString " \t\n\r 7 \r\n" == some (.int 7)

-- escapes are decoded: one leaf
#guard parseString "\"\\u0070kill\\u0020-f\"" == parseString "\"pkill -f\"" &&
  parseString "\"pkill -f\"" == some (.str (u "pkill -f"))
#guard parseString "\"\\ud83d\\ude00\"" == some (.str [0xF0, 0x9F, 0x98, 0x80])
#guard parseString "\"\\ud800\"" == none && parseString "\"\\udc00\"" == none &&
  parseString "\"\\ud800\\u0041\"" == none
#guard parseString "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"" ==
  some (.str [0x22, 0x5C, 0x2F, 0x08, 0x0C, 0x0A, 0x0D, 0x09])
-- NFC é escaped and raw are one leaf; NFD é (e + U+0301) is a different leaf
#guard parseString "\"\\u00e9\"" == parse ([0x22, 0xC3, 0xA9, 0x22]) &&
  parse [0x22, 0xC3, 0xA9, 0x22] == some (.str [0xC3, 0xA9])
#guard parseString "\"e\\u0301\"" == some (.str [0x65, 0xCC, 0x81]) &&
  parseString "\"e\\u0301\"" != parseString "\"\\u00e9\""

-- duplicate keys refused, including when one is spelled with an escape
#guard parseString "{\"a\":1,\"a\":2}" == none
#guard parseString "{\"a\":1,\"\\u0061\":2}" == none
#guard parseString "{\"a\":1,\"b\":{\"a\":2}}" |>.isSome

-- [] and {} are different values with different bytes
#guard parseString "[]" == some (.arr []) && parseString "{ }" == some (.obj []) &&
  (parseString "[]").map encode != (parseString "{}").map encode

-- refusals
#guard parseString "1 2" == none && parseString "{} x" == none
#guard parseString "01" == none && parseString "-01" == none
#guard parseString ".5" == none && parseString "1." == none && parseString "+1" == none
#guard parseString "-" == none && parseString "1e" == none && parseString "1e+" == none
#guard parseString "{a:1}" == none
#guard parseString "[1,]" == none && parseString "{\"a\":1,}" == none && parseString "[,1]" == none
#guard parse [0x22, 0x0A, 0x22] == none                 -- raw LF in a string
#guard parse [0x22, 0xC0, 0xAF, 0x22] == none           -- overlong '/'
#guard parse [0x22, 0xED, 0xA0, 0x80, 0x22] == none     -- a raw surrogate's bytes
#guard parseString "" == none && parseString "tru" == none && parseString "nul" == none
#guard parseString "\"abc" == none && parseString "[1" == none && parseString "\"\\x\"" == none

-- nesting: the fuel bound is enough at depth
#guard parseString ("".pushn '[' 200 ++ "".pushn ']' 200) |>.isSome
#guard parseString "[[[]],{\"k\":[{}]}]" |>.isSome

/- **The JCS falsifier.** RFC 8785 canonicalizes the I-JSON double model: Lean's `Float` is an
IEEE double, and 2^53 + 1 has no double, so a double-based canonicalization prints these two
numbers identically. JCS is injective on the I-JSON double model, not on JSON values as written;
this projection keeps them apart. -/
#guard (9007199254740993 : Float) == (9007199254740992 : Float)
#guard parseString "9007199254740993" != parseString "9007199254740992"

/-- Does `pat` occur as a contiguous run in `s`? -/
def containsBytes (s pat : List UInt8) : Bool :=
  match s with
  | [] => pat.isEmpty
  | _ :: r => pat.isPrefixOf s || containsBytes r pat

/- **The flat-scan falsifier.** A byte search of the raw JSON text for `pkill -f` finds nothing;
the parsed `command` leaf contains it. -/
#guard !containsBytes (u "{\"command\":\"\\u0070kill -f x\"}") (u "pkill -f") &&
  (match parseString "{\"command\":\"\\u0070kill -f x\"}" with
   | some (.obj [(k, .str s)]) => k == u "command" && containsBytes s (u "pkill -f")
   | _ => false)

/-- info: 'Dregg2.Tree.Json.parse_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parse_wf

end Dregg2.Tree.Json
