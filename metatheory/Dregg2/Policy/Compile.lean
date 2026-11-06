/-
# Dregg2.Policy.Compile — a pattern, determinized into a 256-column byte table, executably.

The derivative determinizer IS executable: `SymbolicFixpoint.reachFixAux` saturates the `≅`-class
frontier over the regex's minterm cover (`SymbolicMinterms.coverOfSymbolic`), and
`GuardToAutomatonCircuit.GuardAut.ofFix` packages a saturated run as a table DFA whose correctness
is `GuardAut.guardDfa_decides`. This file runs that pipeline on an elaborated pattern and reads
the cover-indexed table off at the 256 byte frames:

    step s b := G.step s (enc C (byteFrame b))          accept s := null (G.stateAt s)

`compiled_decides` is the correctness of exactly these two functions: for EVERY byte word, the
byte-table run accepts iff the derivative matcher accepts the word (hence, with
`Elab.elabRe_derives`, iff the surface semantics `ReSem` holds). `policyc compile` prints these
functions' values; the JSON printing itself is not a theorem.

What can fail, and is reported rather than hidden: a pattern whose leaves are not
pin-representable (cannot happen for elaborated patterns, whose leaves are `symEq`/`symMemberOf`/
`tt` under `not`), a non-rigid regex (likewise), and fuel exhaustion of the worklist.
-/
import Dregg2.Crypto.GuardToAutomatonCircuit
import Dregg2.Policy.Elab

namespace Dregg2.Policy

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.GuardToAutomatonCircuit (GuardAut)
open Dregg2.Crypto.GuardToAutomatonCircuit.GuardAut (enc)
open Dregg2.Crypto.DfaAcceptanceAir (classifyFrom)

set_option autoImplicit false

/-- A determinized pattern `R`: a cover, a saturated guard automaton for `R`. -/
structure Compiled (R : PredRE) where
  L : List Pred
  C : MintermCover L
  G : GuardAut C
  hroot : G.root = R

namespace Compiled

variable {R : PredRE}

def size (c : Compiled R) : Nat := c.G.size

/-- The byte transition function. -/
def step (c : Compiled R) (s b : Nat) : Nat := c.G.step s (enc c.C (byteFrame b))

def start (c : Compiled R) : Nat := c.G.start

def accepting (c : Compiled R) (s : Nat) : Bool := null (c.G.stateAt s)

def run (c : Compiled R) (s : Nat) (w : List Nat) : Nat := w.foldl c.step s

theorem run_eq (c : Compiled R) : ∀ (w : List Nat) (s : Nat),
    c.run s w = classifyFrom c.G.guardDfa s ((w.map byteFrame).map (enc c.C)) := by
  intro w
  induction w with
  | nil => intro s; rfl
  | cons b w ih => intro s; exact ih _

/-- ⚑ **`compiled_decides`** — the byte table decides the pattern, on every byte word. -/
theorem compiled_decides (c : Compiled R) (w : List Nat) :
    c.accepting (c.run c.start w) = true ↔ derives (w.map byteFrame) R = true := by
  have h := c.G.guardDfa_decides (w.map byteFrame)
  rw [c.hroot] at h
  rw [run_eq]
  exact h

/-- …and therefore the surface semantics. -/
theorem compiled_decides_surface (r : Re) (c : Compiled (elabRe r)) (w : List Nat) :
    c.accepting (c.run c.start w) = true ↔ ReSem r w := by
  rw [compiled_decides, elabRe_derives]

/-- …and the absence semantics. -/
theorem compiled_decides_absence (r : Re) (c : Compiled (absenceOf (elabRe r))) (w : List Nat) :
    c.accepting (c.run c.start w) = true ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ ReSem r y := by
  rw [compiled_decides, correctness, absenceOf_semantics]

end Compiled

/-! ## The cover, deduplicated by leaf signature.

`coverOfSymbolic` enumerates one candidate frame per pin, so `\w` alone contributes 63 frames that
all carry the same signature. The determinizer only needs one frame per signature
(`der_factors_over`), so we keep the first of each. -/

def sigRepsAux (L : List Pred) : List Value → List Value → List Value
  | acc, [] => acc
  | acc, c :: cs =>
    sigRepsAux L (if acc.any (fun d => leafSig L d == leafSig L c) then acc else acc ++ [c]) cs

theorem sigRepsAux_sub (L : List Pred) : ∀ (l acc : List Value), ∀ x ∈ acc, x ∈ sigRepsAux L acc l := by
  intro l
  induction l with
  | nil => intro acc x hx; exact hx
  | cons c cs ih =>
    intro acc x hx
    apply ih
    split
    · exact hx
    · exact List.mem_append_left _ hx

theorem sigRepsAux_covers (L : List Pred) : ∀ (l acc : List Value), ∀ x ∈ acc ++ l,
    ∃ d ∈ sigRepsAux L acc l, leafSig L d = leafSig L x := by
  intro l
  induction l with
  | nil => intro acc x hx; exact ⟨x, by simpa using hx, rfl⟩
  | cons c cs ih =>
    intro acc x hx
    simp only [sigRepsAux]
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, sigRepsAux_sub L cs _ x (by split <;> simp_all), rfl⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · split
        · rename_i h
          obtain ⟨d, hd, he⟩ := List.any_eq_true.mp h
          exact ⟨d, sigRepsAux_sub L cs _ d hd, eq_of_beq he⟩
        · exact ⟨x, sigRepsAux_sub L cs _ x (by simp), rfl⟩
      · exact ih _ x (List.mem_append_right _ hx)

/-- The deduplicated cover (same `L`, one frame per signature). -/
def dedupCover {L : List Pred} (C : MintermCover L) : MintermCover L where
  cands := sigRepsAux L [] C.cands
  covers a := by
    obtain ⟨c, hc, hs⟩ := C.covers a
    obtain ⟨d, hd, hd'⟩ := sigRepsAux_covers L C.cands [] c (by simpa using hc)
    exact ⟨d, hd, hd'.trans hs⟩

/-- **`compile R`** — run the determinizer on the deduplicated cover. `fuel` bounds worklist pops. -/
def compile (R : PredRE) (fuel : Nat := 1000000) : Except String (Compiled R) :=
  match hA : atomsOfLeaves? (leavesOf R) with
  | none => .error "pattern leaves are not pin-representable (no minterm cover)"
  | some _ =>
    let C := dedupCover (coverOfSymbolic hA)
    if hr : rigidRE R = true then
      match hf : reachFixAux C.cands fuel [] [R] with
      | none => .error s!"determinizer fuel {fuel} exhausted"
      | some seen =>
        .ok ⟨_, C, GuardAut.ofFix C R fuel seen (symbolicOver_leavesOf R) hr hf, rfl⟩
    else .error "pattern is not rigid"

/-! ## Tables, simulations, minimization.

A `Table` is a byte DFA given by functions. A runtime-checked simulation `cls : t → t'`
(`simCheck`) transfers the verdict (`simCheck_run`), so the minimized and relabelled table that
`policyc` prints decides the same byte words as the compiled one. -/

structure Table where
  n : Nat
  step : Nat → Nat → Nat
  acc : Nat → Bool
  start : Nat

def Table.run (t : Table) (s : Nat) (w : List Nat) : Nat := w.foldl t.step s

/-- The transition table at the cover symbols, computed once (each `G.step` runs `simDecide`
against every state, so the byte table must not recompute it per byte). -/
def Compiled.memo {R : PredRE} (c : Compiled R) : Array (Array Nat) :=
  (Array.range c.size).map fun s => (Array.range c.C.cands.length).map fun y => c.G.step s y

def Compiled.encs {R : PredRE} (c : Compiled R) : Array Nat :=
  (Array.range 256).map fun b => enc c.C (byteFrame b)

def Compiled.accs {R : PredRE} (c : Compiled R) : Array Bool :=
  (Array.range c.size).map c.accepting

/-- The memoized step, with the arrays passed in (so a closure computes them once). -/
def Compiled.fstepWith {R : PredRE} (c : Compiled R) (m : Array (Array Nat)) (e : Array Nat)
    (s b : Nat) : Nat :=
  if s < c.size ∧ b < 256 then (m.getD s #[]).getD (e.getD b 0) 0 else c.step s b

def Compiled.faccWith {R : PredRE} (c : Compiled R) (a : Array Bool) (s : Nat) : Bool :=
  if s < c.size then a.getD s false else c.accepting s

def Compiled.fstep {R : PredRE} (c : Compiled R) : Nat → Nat → Nat := c.fstepWith c.memo c.encs

def Compiled.facc {R : PredRE} (c : Compiled R) : Nat → Bool := c.faccWith c.accs

theorem Compiled.fstep_eq {R : PredRE} (c : Compiled R) (s b : Nat) : c.fstep s b = c.step s b := by
  unfold Compiled.fstep Compiled.fstepWith
  split
  · rename_i h
    have he : c.encs.getD b 0 = enc c.C (byteFrame b) := by
      simp [Compiled.encs, Array.getD, h.2]
    have hlt := GuardAut.enc_lt c.C (byteFrame b)
    rw [he]
    simp [Compiled.memo, Array.getD, h.1, hlt, Compiled.step]
  · rfl

theorem Compiled.facc_eq {R : PredRE} (c : Compiled R) (s : Nat) : c.facc s = c.accepting s := by
  unfold Compiled.facc Compiled.faccWith
  split
  · rename_i h; simp [Compiled.accs, Array.getD, h]
  · rfl

def Compiled.table {R : PredRE} (c : Compiled R) : Table :=
  let m := c.memo
  let e := c.encs
  let a := c.accs
  ⟨c.size, fun s b => c.fstepWith m e s b, fun s => c.faccWith a s, c.start⟩

/-- `cls` maps `t`'s states into `t'`, commuting with steps on bytes and preserving acceptance;
`t` is closed. All checked by enumeration. -/
def simCheck (t t' : Table) (cls : Nat → Nat) : Bool :=
  decide (t.start < t.n) && t'.start == cls t.start &&
  (List.range t.n).all (fun s => t'.acc (cls s) == t.acc s &&
    (List.range 256).all (fun b => decide (t.step s b < t.n) && cls (t.step s b) == t'.step (cls s) b))

theorem simCheck_run {t t' : Table} {cls : Nat → Nat} (h : simCheck t t' cls = true) :
    ∀ (w : List Nat), w.all (· < 256) = true → ∀ s, s < t.n →
      cls (t.run s w) = t'.run (cls s) w ∧ t.run s w < t.n ∧ t'.acc (cls (t.run s w)) = t.acc (t.run s w) := by
  simp only [simCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨_, _⟩, hall⟩ := h
  intro w
  induction w with
  | nil => intro _ s hs; exact ⟨rfl, hs, (hall s hs).1⟩
  | cons b w ih =>
    intro hw s hs
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨h1, h2⟩ := (hall s hs).2 b hw.1
    obtain ⟨i1, i2, i3⟩ := ih hw.2 _ h1
    refine ⟨?_, i2, i3⟩
    simp only [Table.run, List.foldl_cons] at i1 i2 i3 ⊢
    rw [i1, h2]

theorem simCheck_verdict {t t' : Table} {cls : Nat → Nat} (h : simCheck t t' cls = true)
    (w : List Nat) (hw : w.all (· < 256) = true) :
    t'.acc (t'.run t'.start w) = t.acc (t.run t.start w) := by
  have h' := h
  simp only [simCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨⟨hs, hst⟩, -⟩ := h'
  obtain ⟨e1, -, e3⟩ := simCheck_run h w hw t.start hs
  rw [hst, ← e1, e3]

/-- Moore partition refinement: class id = least state with the same signature. -/
def refineStep (t : Table) (cls : Array Nat) : Array Nat := Id.run do
  let mut seen : Std.HashMap (Nat × List Nat) Nat := {}
  let mut out : Array Nat := #[]
  for s in [0:t.n] do
    let key := (cls.getD s 0, (List.range 256).map (fun b => cls.getD (t.step s b) 0))
    match seen.get? key with
    | some k => out := out.push k
    | none => seen := seen.insert key s; out := out.push s
  return out

def classesOf (t : Table) : Array Nat := Id.run do
  let mut cls : Array Nat := (Array.range t.n).map (fun s => if t.acc s then 1 else 0)
  -- canonicalize the initial partition to least representatives
  let firstAcc := (List.range t.n).find? t.acc
  let firstRej := (List.range t.n).find? (fun s => !t.acc s)
  cls := cls.map (fun k => if k = 1 then firstAcc.getD 0 else firstRej.getD 0)
  for _ in [0:t.n + 1] do
    let cls' := refineStep t cls
    if cls' == cls then break
    cls := cls'
  return cls

/-- The quotient table, with dense class numbers, and the class map. -/
def minimize (t : Table) : Table × (Nat → Nat) :=
  let cls := classesOf t
  let reps := (List.range t.n).filter (fun s => cls.getD s 0 == s)
  let repsA := reps.toArray
  let dense := fun (s : Nat) => reps.idxOf (cls.getD s 0)
  let rows : Array (Array Nat) := repsA.map (fun r => (Array.range 256).map (fun b => dense (t.step r b)))
  (⟨reps.length, fun k b => (rows.getD k #[]).getD b 0, fun k => t.acc (repsA.getD k 0), dense t.start⟩,
   dense)

def swap0 (d s : Nat) : Nat := if s = d then 0 else if s = 0 then d else s

/-- Relabel a non-accepting sink (if any) to state 0, the `dfa` crate's dead state. -/
def relabelDead (t : Table) : Table × (Nat → Nat) :=
  match (List.range t.n).find? (fun s => !t.acc s && (List.range 256).all (fun b => t.step s b == s)) with
  | none => (t, id)
  | some d => (⟨t.n, fun s b => swap0 d (t.step (swap0 d s) b), fun s => t.acc (swap0 d s), swap0 d t.start⟩,
               swap0 d)

/-- A byte table certified to decide `R` on byte words. -/
structure Certified (R : PredRE) where
  t : Table
  hdec : ∀ w : List Nat, w.all (· < 256) = true →
    (t.acc (t.run t.start w) = true ↔ derives (w.map byteFrame) R = true)

/-- The compiled table itself is certified (`compiled_decides`). -/
def Compiled.certified {R : PredRE} (c : Compiled R) : Certified R :=
  ⟨c.table, fun w _ => by
    have hs : c.fstep = c.step := funext fun s => funext fun b => c.fstep_eq s b
    have ha : c.facc = c.accepting := funext c.facc_eq
    show c.facc (List.foldl c.fstep c.start w) = true ↔ _
    rw [hs, ha]; exact c.compiled_decides w⟩

/-- Transport a certificate along a checked simulation. -/
def Certified.along {R : PredRE} (c : Certified R) (t' : Table) (cls : Nat → Nat)
    (h : simCheck c.t t' cls = true) : Certified R :=
  ⟨t', fun w hw => by rw [simCheck_verdict h w hw]; exact c.hdec w hw⟩

/-- **`certify R`** — compile, minimize, relabel the dead state to 0; each step is kept only
when its simulation check passes (otherwise the previous table is kept and the step is named). -/
def certify (R : PredRE) : Except String (Certified R × List String) := do
  let c ← compile R
  let c0 := c.certified
  let (t1, m1) := minimize c0.t
  let (c1, notes) := if h : simCheck c0.t t1 m1 = true then (c0.along t1 m1 h, [])
    else (c0, ["minimization check failed; unminimized table emitted"])
  let (t2, m2) := relabelDead c1.t
  if h : simCheck c1.t t2 m2 = true then pure (c1.along t2 m2 h, notes)
  else pure (c1, notes ++ ["dead-state relabelling check failed; not relabelled"])

def Certified.rows {R : PredRE} (c : Certified R) : List (List Nat) :=
  (List.range c.t.n).map fun s => (List.range 256).map fun b => c.t.step s b

def Certified.accepting {R : PredRE} (c : Certified R) : List Nat :=
  (List.range c.t.n).filter c.t.acc

/-! ## Measured (compiled evaluation): the small absence automaton. Larger tables are measured by
`policyc` (the interpreter is minutes-slow on `\w{20,64}`); see the note. -/

#assert_all_clean [Compiled.run_eq, Compiled.compiled_decides, Compiled.compiled_decides_surface,
  Compiled.compiled_decides_absence, sigRepsAux_covers, simCheck_run, simCheck_verdict, Compiled.fstep_eq, Compiled.facc_eq]

end Dregg2.Policy
