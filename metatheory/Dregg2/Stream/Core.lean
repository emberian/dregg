/-
# Dregg2.Stream.Core: the executable half of the streaming receipts (Lean core only)

Everything `lake exe stream-check` runs is defined here, and `Dregg2.Stream.Omega` / `Window` prove their theorems
about these very definitions (no second copy of any of them exists anywhere, in Lean or Rust).
This module imports nothing beyond Lean core, so the executable links without compiling Mathlib.

* `DOmega`: a deterministic ω-automaton (transition, start, marked set). Its acceptance condition is a
  `Cond` (`buchi`: the run visits a marked state infinitely often; `coBuchi`: only finitely often). The
  ω-semantics is stated in `Omega`; here is only what runs on finite prefixes.
* `MState` / `scanStep`: the monitor's running state over a finite prefix: automaton state, positions
  consumed, the number of positions in `(0, n]` at which the run was in a marked state, and the last
  such position.
* `VCert` / `verdictOf`: the three-valued verdict from a checked pair of state sets (`dead`, `good`).
* `HPeak` / `hpush` / `hbag`: the MMR frontier as (height, hash) pairs, the carry of
  `Lightclient.MMR.push` with every tree replaced by its hash. `Window.hfront_append` proves the two agree.
* `Acc`, `WindowCert`, `produce`, `checkWindow`, `checkChain`: the receipt chain.

The hash is a parameter `List Int → Int`, as in `Lightclient.MMR`; `StreamCheck` instantiates it with
blake3 (`Crypto.Blake3Compute`) over an arity-framed encoding.
-/

namespace Dregg2.Stream

/-- A deterministic ω-automaton over `Sym`: transition, start state, and the marked set `F`
(Büchi: accepting states; co-Büchi: rejecting states). -/
structure DOmega (Q Sym : Type) where
  step : Q → Sym → Q
  start : Q
  mark : Q → Bool

/-- The acceptance condition over infinite runs: `buchi` = `F` visited infinitely often;
`coBuchi` = `F` visited only finitely often. -/
inductive Cond
  | buchi
  | coBuchi
  deriving DecidableEq, Repr

/-- The monitor's running state after a finite prefix of length `pos`: automaton state `q`, the number
`count` of positions `i ∈ (0, pos]` at which the run is in a marked state, and `lastMark`, the last such
position (0 if none). -/
structure MState (Q : Type) where
  q : Q
  pos : Nat
  count : Nat
  lastMark : Nat
  deriving DecidableEq, Repr

namespace DOmega

variable {Q Sym : Type}

/-- The finite run's last state. -/
def exec (A : DOmega Q Sym) (q : Q) (w : List Sym) : Q := w.foldl A.step q

/-- One monitor step. -/
def scanStep (A : DOmega Q Sym) (s : MState Q) (a : Sym) : MState Q :=
  let q' := A.step s.q a
  { q := q'
    pos := s.pos + 1
    count := s.count + (if A.mark q' then 1 else 0)
    lastMark := if A.mark q' then s.pos + 1 else s.lastMark }

/-- The monitor over a finite word. -/
def scan (A : DOmega Q Sym) (s : MState Q) (w : List Sym) : MState Q := w.foldl A.scanStep s

/-- The monitor before any symbol. -/
def init (A : DOmega Q Sym) : MState Q := ⟨A.start, 0, 0, 0⟩

end DOmega

/-- The three-valued verdict on a finite prefix (LTL3's ⊤ / ⊥ / ?). -/
inductive Verdict
  | sat
  | viol
  | unknown
  deriving DecidableEq, Repr

/-- A verdict certificate: a set of states from which every continuation is rejected (`dead`) and one
from which every continuation is accepted (`good`). `Omega.VCert.Valid` is what makes them sound. -/
structure VCert (Q : Type) where
  dead : Q → Bool
  good : Q → Bool

def verdictOf {Q : Type} (c : VCert Q) (q : Q) : Verdict :=
  if c.dead q then .viol else if c.good q then .sat else .unknown

/-! ## Safety ∩ liveness, as a product automaton -/

/-- A safety monitor: a DFA with a bad set. -/
structure SafetyMon (S Sym : Type) where
  step : S → Sym → S
  start : S
  bad : S → Bool

/-- The product of a safety monitor with an ω-automaton; marked iff not bad and `L`-marked. -/
def prodSafety {S L Sym : Type} (M : SafetyMon S Sym) (A : DOmega L Sym) : DOmega (S × L) Sym where
  step p a := (M.step p.1 a, A.step p.2 a)
  start := (M.start, A.start)
  mark p := !M.bad p.1 && A.mark p.2

/-- Its dead set: the tripped states. Its good set: empty (a safety part that can still trip forbids
any `sat`). -/
def prodVCert {S L Sym : Type} (M : SafetyMon S Sym) : VCert (S × L) where
  dead p := M.bad p.1
  good _ := false

/-! ## The MMR frontier as (height, hash) pairs -/

/-- A frontier peak: its height and its hash. Youngest first, as `Lightclient.MMR.Forest`. -/
abbrev HPeak := Nat × Int

/-- The carry over hashes: `Lightclient.MMR.push` with each tree replaced by `(height, hashOf)`. -/
def hpush (hash : List Int → Int) : List HPeak → HPeak → List HPeak
  | [], t => [t]
  | s :: rest, t => if t.1 = s.1 then hpush hash rest (s.1 + 1, hash [s.2, t.2]) else t :: s :: rest

/-- Append one log value: push a height-0 peak `hash [v]`. -/
def happend (hash : List Int → Int) (f : List HPeak) (v : Int) : List HPeak := hpush hash f (0, hash [v])

/-- Bag the frontier into the root: `Lightclient.MMR.bag` over hashes. -/
def hbag (hash : List Int → Int) : List HPeak → Int
  | [] => hash []
  | t :: rest => hash [t.2, hbag hash rest]

/-! ## The receipt chain -/

/-- What a follower holds after accepting a prefix: the monitor state, the frontier, the root. -/
structure Acc (Q : Type) where
  st : MState Q
  front : List HPeak
  root : Int
  deriving DecidableEq, Repr

/-- The window receipt for positions `[n0, n1)`: the root before and after, the monitor state and the
counters before and after, the frontier after (what the next window is checked against), and the
verdict after. -/
structure WindowCert (Q : Type) where
  n0 : Nat
  n1 : Nat
  rootIn : Int
  rootOut : Int
  stateIn : Q
  stateOut : Q
  countIn : Nat
  countOut : Nat
  lastMarkOut : Nat
  frontOut : List HPeak
  verdict : Verdict
  deriving DecidableEq, Repr

/-- The parameters a receipt chain is about: automaton, verdict certificate, hash, and how an entry
`E` yields its committed value and its symbol. -/
structure Policy (E Q Sym : Type) where
  A : DOmega Q Sym
  vc : VCert Q
  hash : List Int → Int
  val : E → Int
  sym : E → Sym

namespace Policy

variable {E Q Sym : Type}

/-- The empty prefix. -/
def genesis (P : Policy E Q Sym) : Acc Q := ⟨P.A.init, [], P.hash []⟩

/-- Advance the follower's state by one window of entries. -/
def advance (P : Policy E Q Sym) (acc : Acc Q) (ws : List E) : Acc Q :=
  let front := (ws.map P.val).foldl (happend P.hash) acc.front
  ⟨P.A.scan acc.st (ws.map P.sym), front, hbag P.hash front⟩

/-- The honest receipt for the window `ws` after `acc`. -/
def produce (P : Policy E Q Sym) (acc : Acc Q) (ws : List E) : WindowCert Q :=
  let acc' := P.advance acc ws
  { n0 := acc.st.pos, n1 := acc'.st.pos
    rootIn := acc.root, rootOut := acc'.root
    stateIn := acc.st.q, stateOut := acc'.st.q
    countIn := acc.st.count, countOut := acc'.st.count
    lastMarkOut := acc'.st.lastMark
    frontOut := acc'.front
    verdict := verdictOf P.vc acc'.st.q }

/-- **The window check.** Accept `c` for the window `ws` after `acc` iff it is exactly the receipt the
policy computes: O(|ws| + |acc.front|) hash evaluations, and nothing about the prefix before `acc`. -/
def checkWindow [DecidableEq Q] (P : Policy E Q Sym) (acc : Acc Q) (ws : List E) (c : WindowCert Q) :
    Bool :=
  decide (c = P.produce acc ws)

/-- Check a chain of windows from `acc`; `some` the final follower state iff every window checks. -/
def checkChain [DecidableEq Q] (P : Policy E Q Sym) : Acc Q → List (List E × WindowCert Q) → Option (Acc Q)
  | acc, [] => some acc
  | acc, (ws, c) :: rest => if P.checkWindow acc ws c then P.checkChain (P.advance acc ws) rest else none

end Policy

end Dregg2.Stream
