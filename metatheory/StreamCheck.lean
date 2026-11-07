/-
# `lake exe stream-check`: the streaming-receipt follower (initiative 11)

    stream-check produce <dir>            compute the next window's receipt (honest producer)
    stream-check verify  <dir> [--anchor R]  check every receipt in <dir> once, from genesis: exit 0
                                          only for a completed run (DONE names the window count, no
                                          gaps), 3 for an accepted prefix, 1 refused, 2 bad input; with
                                          --anchor, also require the final root to be R, the root
                                          published for the source log (`anchored_is_genuine`)
    stream-check root    <file>           the MMR root of a log file (what a publisher publishes)
    stream-check follow  <dir> [idle_s]   follow <dir> as it grows; exit when the producer's DONE marker is
                                          present and checked through, or after idle_s seconds idle
    stream-check digest  <file>           print each line's entry value and symbol (debug)

`<dir>` holds `windows/w000001.jsonl, ...` (window k's raw transcript lines) and
`receipts/r000001.json, ...` (receipt k). The acceptance decision is `Dregg2.Stream.Policy.checkWindow` at
`Claude.policyOver streamHash entryVal sym`, the object `Stream.Window.window_sound` /
`windows_compose` and `Stream.Claude.policy_windows_compose` are about; nothing else accepts.

The hash instantiates `Lightclient.MMR`'s abstract `hash : List ℤ → ℤ` with
`int_be(blake3("dregg-stream-v1:mmr:n" ‖ arity byte ‖ be32(x₁) ‖ … ))` (pure-Lean BLAKE3,
`Crypto.Blake3Compute`, KAT-pinned). Arity separates empty / leaf / node-and-bag exactly as the model
does. Values are always blake3 outputs, so `be32` (the low 256 bits) is injective on them. An entry's
committed value is `int_be(blake3("dregg-stream-v1:entry" ‖ line bytes))`; its symbol is
`Claude.classify` of the same bytes. The Rust producer (`dregg-query`'s `stream-monitor`) computes the
same root with its `ArityBlake3` hasher; agreement is a differential check, not an acceptance.

Per window the follower prints the count of hash evaluations it spent (entry digests, leaf hashes,
carries, bagging) and the bytes hashed: the O(w + log n) bill, counted, beside the clock.
-/
import Dregg2.Stream.ClaudeCore
import Dregg2.Crypto.Blake3Compute
import Dregg2.Stream.Hash

open Lean (Json)
open Dregg2.Stream
open Dregg2.Stream.Claude
open Dregg2.Stream.Hash

namespace StreamCheck

def entrySym (line : ByteArray) : Ev :=
  match String.fromUTF8? line with
  | some s => classify s
  | none => .other

abbrev P : Policy ByteArray (Bool × Bool) Ev := policyOver streamHash entryVal entrySym

/-! ## Wire format -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def toHex (x : Int) : String :=
  let b := be32 x
  String.ofList <| b.toList.flatMap fun c => [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]

def ofHex (s : String) : Option Int := do
  let cs := s.toList
  if cs.length != 64 then none
  let v ← cs.foldlM (fun a c =>
    if '0' ≤ c && c ≤ '9' then some (a * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10)) else none) 0
  pure (Int.ofNat v)

def stateJson (q : Bool × Bool) : Json := Json.mkObj [("tripped", q.1), ("waiting", q.2)]

def verdictStr : Verdict → String
  | .sat => "sat" | .viol => "viol" | .unknown => "unknown"

def certJson (k : Nat) (c : WindowCert (Bool × Bool)) : Json :=
  Json.mkObj [
    ("k", k), ("n0", c.n0), ("n1", c.n1),
    ("root_in", toHex c.rootIn), ("root_out", toHex c.rootOut),
    ("state_in", stateJson c.stateIn), ("state_out", stateJson c.stateOut),
    ("count_in", c.countIn), ("count_out", c.countOut), ("last_mark_out", c.lastMarkOut),
    ("front_out", Json.arr <| c.frontOut.toArray.map fun p => Json.arr #[p.1, toHex p.2]),
    ("verdict", verdictStr c.verdict)]

def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k
def getHex (j : Json) (k : String) : Except String Int := do
  match ofHex (← j.getObjValAs? String k) with
  | some v => pure v
  | none => throw s!"{k}: not 64 lowercase hex digits"
def getState (j : Json) (k : String) : Except String (Bool × Bool) := do
  let s ← j.getObjVal? k
  pure (← s.getObjValAs? Bool "tripped", ← s.getObjValAs? Bool "waiting")

def certOfJson (j : Json) : Except String (Nat × WindowCert (Bool × Bool)) := do
  let front ← (← j.getObjValAs? (Array Json) "front_out").toList.mapM fun p => do
    let a ← p.getArr?
    if a.size != 2 then throw "front_out: pair expected"
    let h ← a[0]!.getNat?
    match ofHex (← a[1]!.getStr?) with
    | some v => pure (h, v)
    | none => throw "front_out: bad hex"
  let v ← match (← j.getObjValAs? String "verdict") with
    | "sat" => pure Verdict.sat | "viol" => pure Verdict.viol | "unknown" => pure Verdict.unknown
    | s => throw s!"verdict: {s}"
  pure (← getNat j "k",
    { n0 := ← getNat j "n0", n1 := ← getNat j "n1"
      rootIn := ← getHex j "root_in", rootOut := ← getHex j "root_out"
      stateIn := ← getState j "state_in", stateOut := ← getState j "state_out"
      countIn := ← getNat j "count_in", countOut := ← getNat j "count_out"
      lastMarkOut := ← getNat j "last_mark_out", frontOut := front, verdict := v })

/-- The follower state a producer resumes from: receipt k's outputs. -/
def accOfCert (c : WindowCert (Bool × Bool)) : Acc (Bool × Bool) :=
  ⟨⟨c.stateOut, c.n1, c.countOut, c.lastMarkOut⟩, c.frontOut, c.rootOut⟩

/-! ## Files -/

def windowPath (dir : String) (k : Nat) : String :=
  let s := toString k
  s!"{dir}/windows/w{String.ofList (List.replicate (6 - s.length) '0')}{s}.jsonl"

/-- Split a byte file into its newline-TERMINATED lines (each one entry) and the byte length of any
unterminated tail. The tail is never an entry: the Rust producer commits only complete lines, and the
follower refuses a window file that has one (the producer always terminates every line). -/
def splitTerminated (b : ByteArray) : List ByteArray × Nat := Id.run do
  let mut out : Array ByteArray := #[]
  let mut start := 0
  for i in [0:b.size] do
    if b.get! i == 10 then
      out := out.push (b.extract start i)
      start := i + 1
  return (out.toList, b.size - start)

def splitLines (b : ByteArray) : List ByteArray := (splitTerminated b).1

def pad6 (k : Nat) : String :=
  let s := toString k
  String.ofList (List.replicate (6 - s.length) '0') ++ s

/-- Receipt k is its own file, written to a temporary name and renamed into place, so a follower
never reads a half-written receipt and never rereads earlier ones: per-window I/O is O(1) files. -/
def receiptPath (dir : String) (k : Nat) : String := s!"{dir}/receipts/r{pad6 k}.json"

/-- The number of receipts present: the largest k with `r1 … rk` all present (found by doubling
then bisection, O(log k) existence checks, only used by `produce`). -/
partial def countReceipts (dir : String) : IO Nat := do
  let has (k : Nat) : IO Bool := if k = 0 then pure true else System.FilePath.pathExists (receiptPath dir k)
  let mut hi := 1
  while ← has hi do hi := hi * 2
  let mut lo := hi / 2
  -- invariant: has lo, ¬ has hi
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← has mid then lo := mid else hi := mid
  return lo

def popcount (n : Nat) : Nat := if n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n
decreasing_by omega

/-- The hash bill of one window `[n0, n1)` with `bytes` entry bytes: entry digests, leaf hashes,
carry merges, and the bagging (one per peak plus the empty bag). -/
def hashBill (n0 n1 : Nat) : Nat :=
  let w := n1 - n0
  w + w + (popcount n0 + w - popcount n1) + (popcount n1 + 1)

/-! ## Modes -/

def produce (dir : String) : IO UInt32 := do
  let n ← countReceipts dir
  let acc ← if n = 0 then pure P.genesis else
    match Json.parse (← IO.FS.readFile (receiptPath dir n)) >>= certOfJson with
    | .ok (_, c) => pure (accOfCert c)
    | .error e => throw (IO.userError s!"stream-check: receipt {n} unreadable: {e}")
  let k := n + 1
  let ws := splitLines (← IO.FS.readBinFile (windowPath dir k))
  let c := P.produce acc ws
  IO.FS.createDirAll s!"{dir}/receipts"
  let tmp := s!"{receiptPath dir k}.tmp"
  IO.FS.writeFile tmp ((certJson k c).compress ++ "\n")
  IO.FS.rename tmp (receiptPath dir k)
  IO.println s!"{k} {c.n0} {c.n1} {toHex c.rootOut} {verdictStr c.verdict}"
  return 0

/-- Check receipt k against the follower state; print one line. -/
def checkOne (dir : String) (acc : Acc (Bool × Bool)) (k : Nat) (line : String) :
    IO (Option (Acc (Bool × Bool))) := do
  let t0 ← IO.monoNanosNow
  let raw ← IO.FS.readBinFile (windowPath dir k)
  let (ws, tail) ← IO.lazyPure fun _ => splitTerminated raw
  let t1 ← IO.monoNanosNow
  if tail != 0 then
    IO.println s!"REFUSE k={k}: window file ends in {tail} unterminated bytes (not an entry)"; return none
  match Json.parse line.trimAscii.toString >>= certOfJson with
  | .error e =>
    IO.println s!"REFUSE k={k}: unreadable receipt: {e}"; return none
  | .ok (k', c) =>
    if k' != k then
      IO.println s!"REFUSE k={k}: receipt claims k={k'}"; return none
    -- THE acceptance decision: `Policy.checkWindow`, nothing else.
    let ok ← IO.lazyPure fun _ => P.checkWindow acc ws c
    let t2 ← IO.monoNanosNow
    if !ok then
      IO.println s!"REFUSE k={k} [{c.n0},{c.n1}): receipt is not the policy's run over the window"
      return none
    let us := (t2 - t1) / 1000
    IO.println <| (Json.mkObj [("k", k), ("n0", c.n0), ("n1", c.n1), ("verdict", verdictStr c.verdict),
      ("tripped", c.stateOut.1), ("waiting", c.stateOut.2), ("marks", c.countOut),
      ("last_mark", c.lastMarkOut), ("peaks", c.frontOut.length), ("hashes", hashBill c.n0 c.n1),
      ("bytes", raw.size), ("check_us", us), ("read_us", ((t1 - t0) / 1000 : Nat)),
      ("root", toHex c.rootOut)]).compress
    (← IO.getStdout).flush
    return some (P.advance acc ws)

/-- Follow (or, with `idle? = none`, verify) a receipt directory from genesis.
Exit 0 only for a COMPLETED run: the producer's `DONE` marker is present, it names exactly the number
of windows checked, and no receipt or window exists past that number. A run without `DONE` is reported
as an accepted PREFIX (exit 3), never as ACCEPT. Missing directory: exit 2. -/
def follow (dir : String) (idle? : Option Nat) (anchor? : Option String := none) : IO UInt32 := do
  unless ← System.FilePath.isDir dir do
    IO.println s!"REFUSE: {dir} is not a directory"; return 2
  let mut acc := P.genesis
  let mut k := 1
  let mut idleMs := 0
  repeat
    if (← System.FilePath.pathExists (receiptPath dir k)) && (← System.FilePath.pathExists (windowPath dir k)) then
      match ← checkOne dir acc k (← IO.FS.readFile (receiptPath dir k)) with
      | some acc' => acc := acc'; k := k + 1; idleMs := 0
      | none => return 1
    else if ← System.FilePath.pathExists s!"{dir}/DONE" then
      break
    else
      match idle? with
      | none => break
      | some s =>
        if idleMs ≥ s * 1000 then break
        IO.sleep 200
        idleMs := idleMs + 200
  let checked := k - 1
  -- The directories must hold EXACTLY the checked pairs: no file past a gap, no stale generation,
  -- no stray name. Enumerated, not probed.
  for (sub, mk) in [("windows", windowPath dir), ("receipts", receiptPath dir)] do
    let expected := (List.range checked).map fun i => mk (i + 1)
    let present ← if ← System.FilePath.isDir s!"{dir}/{sub}" then
        (← System.FilePath.readDir s!"{dir}/{sub}").toList.mapM fun e => pure e.path.toString
      else pure []
    for f in present do
      unless expected.contains f do
        IO.println s!"REFUSE: {f} is not one of the {checked} checked {sub} (a gap, a stale generation, or a stray file)"
        return 1
  -- `anchored_is_genuine`: the chain is about THE published log only if the final root is its root.
  if let some a := anchor? then
    if a != toHex acc.root then
      IO.println s!"REFUSE anchor: final root {toHex acc.root} != published root {a} (the windows are not the published log)"
      return 1
  let summary := s!"{checked} windows, {acc.st.pos} entries, root {toHex acc.root}, verdict {verdictStr (verdictOf policyVC acc.st.q)}{if anchor?.isSome then " (anchored)" else ""}"
  let donePath := s!"{dir}/DONE"
  if ← System.FilePath.pathExists donePath then
    let declared := (← IO.FS.readFile donePath).trimAscii.toString.toNat?
    if declared != some checked then
      IO.println s!"REFUSE: DONE declares {declared} windows, {checked} were present and checked"
      return 1
    IO.println s!"ACCEPT {summary}"
    return 0
  IO.println s!"PREFIX {summary} (no DONE marker: an accepted prefix, not a completed run)"
  return 3

def digest (file : String) : IO UInt32 := do
  for l in splitLines (← IO.FS.readBinFile file) do
    IO.println s!"{toHex (entryVal l)} {repr (entrySym l)}"
  return 0

end StreamCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | ["produce", dir] => StreamCheck.produce dir
  | ["verify", dir] => StreamCheck.follow dir none
  | ["verify", dir, "--anchor", a] => StreamCheck.follow dir none (some a)
  | ["follow", dir] => StreamCheck.follow dir (some 30)
  | ["follow", dir, s] => StreamCheck.follow dir (some s.toNat!)
  | ["digest", f] => StreamCheck.digest f
  | ["root", f] =>
    let (ws, tail) := StreamCheck.splitTerminated (← IO.FS.readBinFile f)
    let acc := StreamCheck.P.advance StreamCheck.P.genesis ws
    IO.println s!"{ws.length} {StreamCheck.toHex acc.root}{if tail != 0 then s!" (ignored {tail} unterminated bytes)" else ""}"
    return 0
  | _ =>
    IO.eprintln "usage: stream-check produce <dir> | verify <dir> [--anchor R] | follow <dir> [idle_s] | digest <file> | root <file>"
    return 2
