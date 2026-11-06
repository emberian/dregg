/-
# DatalogCheck — `lake exe datalog-check`: the extracted stratified-Datalog checker (lane A, 2026-11-06).

Reads `{"statement": …, "certificate": …}` and runs `JoinClosure.verifyJ` (and `verifyBudgetJ` when
the statement carries a `budget`). `verifyJ_verifyS` and `verifyBudgetJ_verifyBudget` transfer
`StratifiedCert.verifyS_sound` / `verifyS_strata_exact` / `countS_unique_or_collides` and
`Aggregates.verifyBudget_sound` to what this executable accepts. Prints the statement it checked,
the verdict, and the counts; exit code 0 (accept) / 1 (refuse) / 2 (malformed input).

    datalog-check <file.json>            verify
    datalog-check --digest <file.json>   print the program digest and the EDB root, no verification
    datalog-check --weaker-no-lower-closure <file.json>
                                         the WEAKER checker (falsifier exhibit; never a verdict)

## The hash, and the second injectivity obligation (codex round 3, finding 2)

`mroot` is abstract in `hash : List ℤ → ℤ`. This executable instantiates it with
`leafHash l = int_be(SHAKE256("dregg.datalog.mmr.v1" ‖ 0x00 ‖ enc l, 32))`, using the tree's
executable `Dregg2.Crypto.Keccak.shake256` (KAT-pinned in that module and `KeccakCavp`). `enc` is a
canonical framed encoding of a `List ℤ`: an 8-byte big-endian element count, then per element a sign
byte (`0x00` for `x ≥ 0`, `0x01` for `x < 0`), a 4-byte big-endian magnitude length and the minimal
big-endian magnitude (zero has length 0). No reduction modulo a field prime happens anywhere, so
`e(0)` and `e(p)` do not alias. `FixpointCert.flatten_injective` proves injectivity of the fact
flattening over `List ℤ`; injectivity of `enc` from `List ℤ` to bytes is a SECOND obligation, and
here it is discharged only by evaluation: `decodeEnc (enc l) = some l` on a set of
colliding-looking pairs (`#guard`s below), not by a theorem. The DEPLOYED instantiation is the
leaf's cSHAKE256 Merkle root (SUBSTRATE-DECISION §2); SHAKE256 with a domain prefix stands in for it
here, and the statement does not change when the hash does.

The program digest is `SHAKE256("dregg.datalog.program.v1" ‖ 0x00 ‖ enc (programEnc P strata), 32)`.
-/
import Dregg2.Datalog.JoinClosure
import Dregg2.Crypto.Keccak

open Lean (Json)
open Dregg2.Datalog.FixpointCert
open Dregg2.Datalog.StratifiedCert
open Dregg2.Datalog.Aggregates
open Dregg2.Datalog.JoinClosure
open Dregg2.Lightclient.MMR (mroot)

namespace DatalogCheck

/-! ## The byte codec and the hash. -/

def natBytesBE (n : Nat) : List UInt8 :=
  if n = 0 then [] else natBytesBE (n / 256) ++ [(n % 256).toUInt8]
termination_by n
decreasing_by omega

def fixedBE (width n : Nat) : List UInt8 :=
  (List.range width).reverse.map fun k => ((n / 256 ^ k) % 256).toUInt8

def encInt (x : ℤ) : List UInt8 :=
  let mag := natBytesBE x.natAbs
  (if x < 0 then (1 : UInt8) else 0) :: fixedBE 4 mag.length ++ mag

def enc (l : List ℤ) : List UInt8 := fixedBE 8 l.length ++ l.flatMap encInt

def bytesToNat (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- The decoder, for the round-trip guards. -/
def decodeInts : Nat → List UInt8 → Option (List ℤ)
  | 0, [] => some []
  | 0, _ :: _ => none
  | k + 1, sgn :: rest =>
    let len := bytesToNat (rest.take 4)
    if rest.length < 4 + len then none else
    let mag := bytesToNat ((rest.drop 4).take len)
    let canonical := len == 0 || ((rest.drop 4).head? != some 0)
    if !canonical || sgn > 1 || (sgn == 1 && mag == 0) then none else
    let x : ℤ := if sgn == 1 then -(mag : ℤ) else mag
    (decodeInts k ((rest.drop 4).drop len)).map (x :: ·)
  | _ + 1, [] => none

def decodeEnc (bs : List UInt8) : Option (List ℤ) :=
  if bs.length < 8 then none else decodeInts (bytesToNat (bs.take 8)) (bs.drop 8)

def tagBytes (s : String) : List UInt8 := s.toUTF8.toList ++ [0]

def leafHash (l : List ℤ) : ℤ :=
  (bytesToNat (Dregg2.Crypto.Keccak.shake256 (tagBytes "dregg.datalog.mmr.v1" ++ enc l) 32) : ℤ)

def encTerm : Term → List ℤ
  | .var i => [0, i]
  | .const c => [1, c]

def encAtom (a : Atom) : List ℤ := (a.pred : ℤ) :: (a.args.length : ℤ) :: a.args.flatMap encTerm

def encLit : Lit → List ℤ
  | .pos a => 0 :: encAtom a
  | .neg a => 1 :: encAtom a

def encRule (r : SRule) : List ℤ :=
  encAtom r.head ++ (r.body.length : ℤ) :: r.body.flatMap encLit

def programEnc (P : SProgram) (strata : Strata) : List ℤ :=
  (P.length : ℤ) :: P.flatMap encRule ++
    (strata.length : ℤ) :: strata.flatMap fun S => (S.length : ℤ) :: S.map (fun i => (i : ℤ))

def programDigest (P : SProgram) (strata : Strata) : Nat :=
  bytesToNat (Dregg2.Crypto.Keccak.shake256
    (tagBytes "dregg.datalog.program.v1" ++ enc (programEnc P strata)) 32)

def hexNat (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  "0x" ++ String.ofList (List.replicate (64 - ds.length) '0' ++ ds)

-- Round-trip guards on colliding-looking pairs (the second injectivity obligation, by evaluation).
#guard decodeEnc (enc [0]) = some [0]
#guard decodeEnc (enc [2013265921]) = some [2013265921]
#guard enc [0] ≠ enc [2013265921]
#guard decodeEnc (enc [1, 2]) = some [1, 2]
#guard decodeEnc (enc [12]) = some [12]
#guard enc [1, 2] ≠ enc [12]
#guard enc [] ≠ enc [0]
#guard decodeEnc (enc []) = some []
#guard decodeEnc (enc [-1, 1, -256, 256, 65536]) = some [-1, 1, -256, 256, 65536]
#guard enc [-1] ≠ enc [1]
#guard enc [256] ≠ enc [1, 0]
#guard decodeEnc (enc [256]) = some [256]
#guard decodeEnc (enc [1, 0]) = some [1, 0]
-- Pinned hash value; `extract_edb.py` (Python `hashlib.shake_256`) reproduces it, and `run.sh`
-- cross-checks the demo's EDB root between the two implementations.
#guard hexNat (Int.toNat (leafHash [1, -2, 300])) =
  "0xf504a3168b5844d89c04d2dd14dcd12301f318b7704c3c766a81f6651ca673e6"

/-! ## JSON. -/

abbrev P := Except String

def getK (j : Json) (k : String) : P Json := j.getObjVal? k
def arr (j : Json) : P (List Json) := (·.toList) <$> j.getArr?
def nat (j : Json) : P Nat := j.getNat?
def int (j : Json) : P ℤ := j.getInt?

/-- A big integer: a JSON integer, or a string `0x…` / decimal. -/
def bigInt (j : Json) : P ℤ :=
  match j.getStr? with
  | .ok s =>
    if s.startsWith "0x" then
      let ds := s.toList.drop 2
      ds.foldlM (fun (a : ℤ) c =>
        if c.isDigit then pure (a * 16 + (c.toNat - '0'.toNat))
        else if 'a' ≤ c ∧ c ≤ 'f' then pure (a * 16 + (c.toNat - 'a'.toNat + 10))
        else throw s!"bad hex digit {c}") 0
    else match s.toInt? with
      | some x => pure x
      | none => throw s!"bad integer {s}"
  | .error _ => j.getInt?

def term (j : Json) : P Term :=
  match getK j "var" with
  | .ok v => Term.var <$> nat v
  | .error _ => Term.const <$> (getK j "const" >>= bigInt)

def atom (j : Json) : P Atom := do
  let p ← getK j "pred" >>= nat
  let as ← getK j "args" >>= arr
  return ⟨p, ← as.mapM term⟩

def lit (j : Json) : P Lit :=
  match getK j "pos" with
  | .ok a => Lit.pos <$> atom a
  | .error _ => Lit.neg <$> (getK j "neg" >>= atom)

def rule (j : Json) : P SRule := do
  let h ← getK j "head" >>= atom
  let b ← getK j "body" >>= arr
  return ⟨h, ← b.mapM lit⟩

def fact (j : Json) : P Fact := do
  match ← arr j with
  | [p, as] => return (← nat p, ← (← arr as).mapM bigInt)
  | _ => throw "a fact is [pred, [args]]"

def firing (j : Json) : P Firing := do
  match ← arr j with
  | [r, s] => return ⟨← nat r, ← (← arr s).mapM bigInt⟩
  | _ => throw "a firing is [rule, [subst]]"

def trace (j : Json) : P Trace := do
  let rds ← arr j
  return ⟨← rds.mapM fun rd => do (← arr rd).mapM firing⟩

structure Input where
  st : SStatement
  cert : SCertificate
  budget : Option (Nat × ℤ)
  acc : List ℤ

def input (j : Json) : P Input := do
  let s ← getK j "statement"
  let c ← getK j "certificate"
  let prog ← (← getK s "program" >>= arr).mapM rule
  let strata ← (← getK s "strata" >>= arr).mapM fun S => do (← arr S).mapM nat
  let root ← getK s "root" >>= bigInt
  let pred ← getK s "pred" >>= nat
  let count ← getK s "count" >>= nat
  let edb ← (← getK c "edb" >>= arr).mapM fact
  let traces ← (← getK c "traces" >>= arr).mapM trace
  let budget ← match getK s "budget" with
    | .ok b => do pure (some (← getK b "arg" >>= nat, ← getK b "limit" >>= bigInt))
    | .error _ => pure none
  let acc ← match getK c "acc" with
    | .ok a => do (← arr a).mapM bigInt
    | .error _ => pure []
  return ⟨⟨prog, strata, root, pred, count⟩, ⟨edb, traces⟩, budget, acc⟩

/-! ## Diagnostics and counts (run after the verdict; they never decide it). -/

def stratumStats (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact →
    List (Nat × Nat × List (Nat × Nat)) → Option (List Fact) × List (Nat × Nat × List (Nat × Nat)) × String
  | [], [], db, acc => (some db, acc.reverse, "")
  | S :: rest, t :: ts, db, acc =>
    match replayS P dom S db db t.rounds with
    | none => (none, acc.reverse, s!"stratum {acc.length}: replay refused a firing")
    | some db₁ =>
      let cands := S.map fun i => (i, match P[i]? with
        | some r => (candidates db₁ r).length
        | none => 0)
      let row := (t.rounds.flatten.length, db₁.length - db.length, cands)
      if closedJoinS P S db db₁ then stratumStats P dom rest ts db₁ (row :: acc)
      else (none, (row :: acc).reverse, s!"stratum {acc.length}: NOT CLOSED")
  | _, _, _, acc => (none, acc.reverse, "trace count differs from stratum count")

/-- The WEAKER checker (the `StratifiedCert.verifyNoLowerClosure` shape, join closure): closure at
the TOP stratum only. It exists to exhibit, on real data, the acceptance `verifyJ` refuses. -/
def runTopClosureJ (P : SProgram) (dom : List ℤ) : Strata → List Trace → List Fact →
    Option (List Fact)
  | [], [], db => some db
  | S :: rest, t :: ts, db =>
    match replayS P dom S db db t.rounds with
    | none => none
    | some db₁ =>
      if rest.isEmpty && !closedJoinS P S db db₁ then none else runTopClosureJ P dom rest ts db₁
  | _, _, _ => none

def verifyNoLowerClosureJ (hash : List ℤ → ℤ) (st : SStatement) (c : SCertificate) : Bool :=
  stratifiedB st.program st.strata && (mroot hash (flatten c.edb) == st.root) &&
    decide c.edb.Nodup &&
  match runTopClosureJ st.program (domFast st.program c.edb) st.strata c.traces c.edb with
  | none => false
  | some db => countQ db st.pred == st.count

def run (path : String) (digestOnly : Bool) (weaker : Bool := false) : IO UInt32 := do
  let txt ← IO.FS.readFile path
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"datalog-check: JSON parse error: {e}"; return 2
  let inp ← match input j with
    | .ok i => pure i
    | .error e => do IO.eprintln s!"datalog-check: malformed input: {e}"; return 2
  let st := inp.st
  let c := inp.cert
  let rootNow := mroot leafHash (flatten c.edb)
  let pd := programDigest st.program st.strata
  IO.println s!"program digest : {hexNat pd}"
  IO.println s!"EDB root       : {hexNat rootNow.toNat}   (over {(flatten c.edb).length} flattened integers)"
  if digestOnly then return 0
  if weaker then
    let ok := verifyNoLowerClosureJ leafHash st c
    IO.println s!"WEAKER checker (closure at the top stratum only, NOT the statement's checker): {if ok then "ACCEPT" else "REFUSE"}"
    return (if ok then 0 else 1)
  IO.println "statement"
  IO.println s!"  rules        : {st.program.length}"
  IO.println s!"  strata       : {st.strata}"
  IO.println s!"  root         : {hexNat st.root.toNat}"
  IO.println s!"  pred         : {st.pred}"
  IO.println s!"  claimed count: {st.count}"
  match inp.budget with
  | some (a, l) => IO.println s!"  budget       : sum of argument {a} of pred {st.pred} ≤ {l}"
  | none => pure ()
  let t2 ← IO.monoMsNow
  let ok := verifyJ leafHash st c
  let okB := match inp.budget with
    | some (a, l) => verifyBudgetJ leafHash ⟨st.program, st.strata, st.root, st.pred, a, l⟩
        ⟨c, st.count, inp.acc⟩
    | none => true
  let t3 ← IO.monoMsNow
  -- counts
  let dom := domFast st.program c.edb
  let (dbo, rows, why) := stratumStats st.program dom st.strata c.traces c.edb []
  IO.println "counts"
  IO.println s!"  EDB facts    : {c.edb.length}"
  IO.println s!"  active domain: {dom.length} distinct constants"
  let mut k := 0
  for (fires, added, cands) in rows do
    IO.println s!"  stratum {k}    : {fires} firings, {added} facts added, join candidates per rule {cands}"
    k := k + 1
  match dbo with
  | some db =>
    IO.println s!"  final db     : {db.length} facts; count at pred {st.pred} = {countQ db st.pred}"
    match inp.budget with
    | some (a, _) => IO.println s!"  sum at arg {a} : {sumAt db st.pred a}"
    | none => pure ()
  | none => IO.println s!"  run stopped  : {why}"
  IO.println s!"verify time    : {t3 - t2} ms (verifyJ{if inp.budget.isSome then " + verifyBudgetJ" else ""}, native)"
  if ok && okB then
    IO.println "verdict        : ACCEPT"
    return 0
  else
    let reasons := [
      (!stratifiedB st.program st.strata, "stratifiedB refused the stratification"),
      (rootNow != st.root, "EDB root differs from the statement's root"),
      (!decide c.edb.Nodup, "EDB has duplicate facts"),
      (!why.isEmpty, why),
      (dbo.isSome && dbo.map (countQ · st.pred) != some st.count, "count differs"),
      (ok && !okB, "budget leg refused (accumulator rows or limit)")]
    IO.println s!"verdict        : REFUSE ({", ".intercalate ((reasons.filter (·.1)).map (·.2))})"
    return 1

end DatalogCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--digest", p] => DatalogCheck.run p true
  | ["--weaker-no-lower-closure", p] => DatalogCheck.run p false true
  | [p] => DatalogCheck.run p false
  | _ =>
    IO.eprintln "usage: datalog-check <file.json> | datalog-check --digest <file.json>"
    return 2
