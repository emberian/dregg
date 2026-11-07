/-
# `Dregg2.Circuit.Emit.MinaWrapCommitStages` — the COMMITMENT-COMBINATION stages of Kimchi's
`verify`, as emitted dregg AIRs over a REAL Mina devnet block.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every stage below is a `List Instr` over
`MinaWrapCommitMachine`'s Lean-authored machine, lowered by `EffectLower.lowerAir`. There is no
hand-written `VmConstraint2` and no Rust-authored gadget anywhere in this cone. Rust parses the
emitted descriptor, fills cells, and runs the deployed prover. House Law #1.

## THE FOUR STAGES, AND WHERE THEIR NUMBERS COME FROM

`kimchi/src/verifier.rs` on a Wrap verifier index (no lookup index, no optional gate commitments):

  * **`public_comm`** (`verifier.rs:834-857`) — `PolyComm::multi_scalar_mul(lagrange_bases,
    −public_input)`, then `mask_custom` with all-ones blinders, i.e. one further `+ H`.
    **41 nominal, 31 meaningful**: ten of the block's forty public inputs are ZERO, and a zero
    scalar makes the term the point at infinity, which an affine term list cannot carry (§6b).
  * **`f_comm`** (`verifier.rs:904-953`) — `sigma_comm[PERMUTS−1]` at `perm_scalars`, plus one term
    per `linearization.index_terms`; that list is **empty** on the wrap side, so **1 term**.
  * **`ft_comm`** (`verifier.rs:958-964`) — `chunk(f_comm, ζ^srs_len) − chunk(t_comm, ζ^srs_len) ·
    (ζ^n − 1)`. **9 nominal, 7 meaningful.**
  * **the ξ-aggregate** (`poly-commitment/src/commitment.rs:724-744`, `combine_commitments`) —
    `Σᵢ polyscale^i · Cᵢ` over 2 recursion + `public_comm` + `ft_comm` + `Z` + 6 index + 15 witness
    + 15 coefficient + 6 sigma = **47 terms** at `COLUMNS = 15`, `PERMUTS = 7`.

⚑ **THE DATA IS REAL.** Every base point, every challenge and every golden output below comes from
`MinaWrapGroupGate` / `MinaWrapAggregationGate` / `MinaWrapPublicCommGate`, which carry Mina devnet
block **539508** and are `by decide`-checked against o1-labs' own `PolyComm::multi_scalar_mul`
output. This file adds no new constants; it CHECKS those constants with an AIR.

## ⚑ THE HONEST SPLIT — read this before reading any green

A commitment combination is `Σ sᵢ · Bᵢ`. Three separable obligations, and this file emits a
descriptor for each rather than one descriptor that quietly does two of them:

  1. **THE SCALARS.** `s_i` must be what the transcript says, not what the prover likes.
     `xiChainProg` computes all 47 powers of the block's REAL `ξ` in-circuit, from `ξ` as a public
     input, in 46 Pasta multiplies. **Full fidelity, no reduction.**
  2. **THE GROUP ACCUMULATION AND THE SCALAR↔BASE PAIRING.** `sumProg` folds the stage's term list
     with the affine chord law, one ROM-pinned base per instruction, at the stage's FULL term count
     (40 / 1 / 9 / 47) — against the block's own golden aggregate.
  3. **THE SCALAR MULTIPLICATION `sᵢ · Bᵢ` ITSELF.** `msmProg` is the double-and-add ladder with an
     in-circuit bit decomposition and a closing `SC = s` assertion. It is emitted at a REDUCED plane
     count (§7) because the full 255 planes are `9 456` instructions per term and the trace does not
     fit a checked-in fixture — `full_width_ladder_price` is that as a theorem, not an excuse.

⚠ So: obligation (2) is emitted at full term count over PRE-SCALED points, which means the emitted
`sumProg` instances take `sᵢ·Bᵢ` as given. That is exactly what obligation (3) supplies and exactly
what is NOT closed at full width **on this machine**. Nothing in THIS FILE should be read as "the
ξ-aggregate is verified in-AIR". What is true here is: *the scalar vector is computed in-AIR at full
fidelity; the 47-term group fold is computed in-AIR at full term count; the 255-plane scalar
multiplication that joins them is demonstrated at 8 planes and priced at 255.*

⚑ **AND THE ξ-AGGREGATE'S OBLIGATION (3) IS NOW CLOSED ELSEWHERE, AT FULL WIDTH.**
`Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm` emits the same 47-term aggregate on
`PastaMsmBucketed`'s fused running-sum layout: the scalars enter as NUMBERS, the generators enter
UNSCALED, and `T_COVER`'s permutation makes `sᵢ·Bᵢ` the trace's own work at `nbits = 255`, in 8 192
rows. That descriptor — not this one — is what may be cited for "the ξ-aggregate scales in-circuit".
⚠ It buys that at a real price, named in its header and not to be absorbed: its rows are denominated
in the **unsound `fpMulCore`**, where every descriptor in THIS file is `PastaFieldSound`.

## ⚑ INCOMPLETE ADDITION, NAMED

`addAffine` is the chord law with a WITNESSED slope pinned by `s·(x₁−x₂) = y₁−y₂` — Kimchi's own
`CompleteAdd` gate minus the `same_x` branch, i.e. Pickles' `add_fast` in its non-exceptional case.
At `x₁ = x₂` no slope satisfies the pin, so **no witness exists and the prover cannot produce a
trace**: this is a COMPLETENESS gap (a trace that ought to exist does not), never a soundness gap
(a trace that ought not to exist is accepted). `dblAffine` carries the tangent branch. The ladder
uses a fixed non-identity OFFSET so the accumulator never reaches the point at infinity, which the
affine coordinates cannot represent — `offset_is_a_real_pallas_point`.

## Axiom hygiene

General theorems (the machine, the traces, the tie verdict, the lowering) are kernel-proved and
`#assert_axioms`-clean. Facts about block 539508's concrete data (field values, curve points, the
folds against o1-labs' goldens, the ξ chain) are checked by compiled evaluation, `native_decide`,
and pinned `#assert_compiled` (they rest on `Lean.ofReduceBool`). Until 2026-11-06 they were
kernel `decide`s, which recomputed the same scalar multiplications per theorem and put this module
at 15.7 GB; see `metatheory/docs/MINA-PICKLES-RESCUE.md`. No `sorry`/`admit`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.MinaWrapCommitMachine
import Dregg2.Circuit.Emit.MinaWrapAggregationData
-- ⚑ the DATA module, not the GATE (2026-08-09). This file reads `LAGRANGE`, `NEG_PUBLIC`,
-- `PUBLIC_COMM_GOLD` and `SRS_H` — all literals — and mentions `tamper_blinder_dropped` only in a
-- DOCBLOCK, so it cited no term from the gate. The gate is a 14.5 GB kernel `decide`, and this
-- import is what put it behind `MinaWrapXiEndoLift` and therefore behind `KimchiStepMainPins19d`.
import Dregg2.Circuit.Emit.MinaWrapPublicCommData
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.MinaWrapCommitStages

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.Emit.MinaWrapCommitMachine

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! ## §1 — AFFINE PASTA ARITHMETIC, and the inverse the machine cannot do.

⚑ The machine has three opcodes and none of them is a division. A slope therefore enters as a
WITNESS through the free operand code and is pinned by a multiply and an assert. This section is
the reference that COMPUTES the witness from the gadget's actual inputs — never from what the
answer was supposed to be. -/

abbrev Fp := Nat

def fmul (x y : Fp) : Fp := PastaField.Ref.fpMul x y
def fadd (x y : Fp) : Fp := PastaField.Ref.fpAdd x y
def fsub (x y : Fp) : Fp := PastaField.Ref.fpSub x y

/-- Modular exponentiation by squaring, structurally recursive on FUEL so the kernel reduces it. -/
def powAux : Nat → Fp → Nat → Fp → Fp
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powAux fuel (fmul b b) (e / 2) (if e % 2 = 1 then fmul acc b else acc)

/-- `x⁻¹` in the Pasta base field, by Fermat. `pN` is 255 bits, so 256 doublings of fuel suffice. -/
def finv (x : Fp) : Fp := powAux 260 x (pN - 2) 1

/-- ⚑ **THE INVERSE IS AN INVERSE**, on the block's own field elements — checked, not assumed,
because every witnessed slope in this file is a quotient and a wrong `finv` would make every honest
trace refuse for a reason no refusal message would explain. -/
theorem finv_is_an_inverse :
    fmul (MinaWrapAggregationGate.XI) (finv MinaWrapAggregationGate.XI) = 1
      ∧ fmul 7 (finv 7) = 1 := by native_decide

/-! ⚑ **THE SCALARS LIVE IN THE SCALAR FIELD `q`, THE COORDINATES IN THE BASE FIELD `p`.** Reading
one for the other is the classic Pasta error; these three are `q`-arithmetic and nothing else in
this file is. -/

def qmul (x y : Nat) : Nat := (x * y) % PastaField.qN
def qpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => qmul (qpow x n) x
def qneg (x : Nat) : Nat := (PastaField.qN - x % PastaField.qN) % PastaField.qN

/-- An affine Pasta point. -/
abbrev Aff := Fp × Fp

/-- The chord slope of two distinct-abscissa points: `(y₁ − y₂)/(x₁ − x₂)`. -/
def slopeAdd (Pt1 Pt2 : Aff) : Fp :=
  fmul (fsub Pt1.2 Pt2.2) (finv (fsub Pt1.1 Pt2.1))

/-- The tangent slope: `3x² / 2y`. -/
def slopeDbl (Pt1 : Aff) : Fp :=
  let x2 := fmul Pt1.1 Pt1.1
  fmul (fadd (fadd x2 x2) x2) (finv (fadd Pt1.2 Pt1.2))

/-- `x₃ = s² − x₁ − x₂`, `y₃ = s(x₁ − x₃) − y₁` — the chord-and-tangent law, written once and used
by both gadgets. -/
def chordOut (s : Fp) (Pt1 : Aff) (x2 : Fp) : Aff :=
  let x3 := fsub (fsub (fmul s s) Pt1.1) x2
  (x3, fsub (fmul s (fsub Pt1.1 x3)) Pt1.2)

def addAffine (Pt1 Pt2 : Aff) : Aff := chordOut (slopeAdd Pt1 Pt2) Pt1 Pt2.1
def dblAffine (Pt1 : Aff) : Aff := chordOut (slopeDbl Pt1) Pt1 Pt1.1

/-- ⚑ **THE REFERENCE SATISFIES THE PIN THE AIR ASSERTS.** The descriptor demands
`s·(x₁ − x₂) = y₁ − y₂` and nothing else about `s`; this says the value the witness generator
supplies is one that satisfies it, on real block data. If it did not, the honest trace would
refuse — which is the failure mode the mandate's rule 1 exists to prevent, and it is checked here
rather than discovered at prove time. -/
def affOf (p : Nat × Nat × Nat) : Aff := (p.1, p.2.1)

def PT_A : Aff := affOf (MinaWrapAggregationGate.COMBINE_POINTS.getD 0 (0, 0, 1))
def PT_B : Aff := affOf (MinaWrapAggregationGate.COMBINE_POINTS.getD 1 (0, 0, 1))

theorem slope_pin_holds_on_real_block_points :
    fmul (slopeAdd PT_A PT_B) (fsub PT_A.1 PT_B.1) = fsub PT_A.2 PT_B.2 := by native_decide

theorem tangent_pin_holds_on_a_real_block_point :
    fadd (fmul (slopeDbl PT_A) PT_A.2) (fmul (slopeDbl PT_A) PT_A.2)
      = fadd (fadd (fmul PT_A.1 PT_A.1) (fmul PT_A.1 PT_A.1)) (fmul PT_A.1 PT_A.1) := by native_decide

/-- The Pallas curve equation `y² = x³ + 5`, affine. -/
def onPallas (Pt1 : Aff) : Bool :=
  decide (fmul Pt1.2 Pt1.2 = fadd (fmul (fmul Pt1.1 Pt1.1) Pt1.1) 5)

/-- ⚑ **AND THE CHORD LAW LANDS BACK ON THE CURVE**, on the block's own points — the property that
makes an accumulator a group element rather than a pair of field values. -/
theorem chord_law_stays_on_pallas :
    onPallas PT_A = true ∧ onPallas PT_B = true
      ∧ onPallas (addAffine PT_A PT_B) = true
      ∧ onPallas (dblAffine PT_A) = true := by native_decide

/-! ## §2 — THE REGISTER ALLOCATION.

Twelve registers, and every one of them is live in the ladder's inner loop — which is what
`MinaWrapCommitMachine.the_one_hot_word_fits_the_raised_cap_and_the_index_word_still_wins`
prices — ⚠ and whose refusal half is now HISTORICAL: the cap was raised `64 → 97` on 2026-08-06. -/

def ZERO : Nat := 0   -- the constant 0, forced by instruction 0
def TX : Nat := 1     -- running total, x
def TY : Nat := 2     -- running total, y
def AX : Nat := 3     -- ladder accumulator, x
def AY : Nat := 4     -- ladder accumulator, y
def BIT : Nat := 5    -- the plane's digit
def SL : Nat := 6     -- the witnessed slope
def T0 : Nat := 7
def T1 : Nat := 8
def X3 : Nat := 9
def Y3 : Nat := 10
def SC : Nat := 11    -- the scalar accumulator

/-- The `y` operand code for the immediate. -/
def IMMC : Nat := NREG
/-- The `y` operand code for the FREE witness block. -/
def FREEC : Nat := NREG + 1
/-- The `wr` code for "write nothing". -/
def NOWR : Nat := NREG

theorem allocation_fits_the_register_file :
    ZERO < NREG ∧ SC < NREG ∧ IMMC = 12 ∧ FREEC = 13 ∧ NOWR = 12 := by decide +kernel

/-! ## §3 — THE INSTRUCTION CONSTRUCTORS. -/

def mulR (x y w : Nat) : Instr := ⟨1, x, y, w, 0, 0⟩
def addR (x y w : Nat) : Instr := ⟨2, x, y, w, 0, 0⟩
def subR (x y w : Nat) : Instr := ⟨3, x, y, w, 0, 0⟩
def addI (x i w : Nat) : Instr := ⟨2, x, IMMC, w, 0, i⟩
def subI (x i w : Nat) : Instr := ⟨3, x, IMMC, w, 0, i⟩
/-- ⚑ `SUB x, y → ∅` with the assert bit: the descriptor DEMANDS `x ≡ y (mod p)`. -/
def eqR (x y : Nat) : Instr := ⟨3, x, y, NOWR, 1, 0⟩
def eqI (x i : Nat) : Instr := ⟨3, x, IMMC, NOWR, 1, i⟩
/-- ⚑ The witness load: `w := 0 + FREE`. The ROM names it, so the descriptor decides where a
witness may enter. -/
def wit (w : Nat) : Instr := ⟨2, ZERO, FREEC, w, 0, 0⟩

/-- A program is a list of (instruction, witness) pairs: the witness is only read by the free-code
instructions, and `MinaWrapCommitMachine.routed_instruction_ignores_the_witness` is that as a
theorem. -/
abbrev Step := Instr × Nat

def instrs (p : List Step) : List Instr := p.map Prod.fst
def witsOf (p : List Step) : Nat → Nat := fun pc => (p.getD pc (PAD, 0)).2

/-! ## §4 — THE GADGETS.

Each takes the ENTRY point values and computes its own witnesses from them. Nothing below reads a
value it did not derive from the gadget's inputs. -/

/-- `(TX, TY) := (TX, TY) + (bx, by)` with `(bx, by)` a ROM immediate. **12 instructions**, one
witnessed slope, one assert. -/
def emitAddImmT (cur : Aff) (bx by_ : Fp) : List Step :=
  let s := slopeAdd cur (bx, by_)
  [ (subI TX bx T0, 0)
  , (subI TY by_ T1, 0)
  , (wit SL, s)
  , (mulR SL T0 T0, 0)
  , (eqR T0 T1, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 TX T0, 0)
  , (subI T0 bx X3, 0)
  , (subR TX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 TY TY, 0)
  , (addR X3 ZERO TX, 0) ]

/-- `(AX, AY) := 2·(AX, AY)`. **15 instructions**, one witnessed slope, one assert. -/
def emitDblA (cur : Aff) : List Step :=
  let s := slopeDbl cur
  [ (mulR AX AX T0, 0)
  , (wit SL, s)
  , (mulR SL AY T1, 0)
  , (addR T1 T1 T1, 0)
  , (subR T1 T0 T1, 0)
  , (subR T1 T0 T1, 0)
  , (eqR T1 T0, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 AX T0, 0)
  , (subR T0 AX X3, 0)
  , (subR AX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 AY Y3, 0)
  , (addR X3 ZERO AX, 0)
  , (addR Y3 ZERO AY, 0) ]

/-- `(X3, Y3) := (AX, AY) + (bx, by)` — the ladder's CANDIDATE, left unselected. **11
instructions**. -/
def emitAddImmA (cur : Aff) (bx by_ : Fp) : List Step :=
  let s := slopeAdd cur (bx, by_)
  [ (subI AX bx T0, 0)
  , (subI AY by_ T1, 0)
  , (wit SL, s)
  , (mulR SL T0 T0, 0)
  , (eqR T0 T1, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 AX T0, 0)
  , (subI T0 bx X3, 0)
  , (subR AX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 AY Y3, 0) ]

/-- `(AX, AY) := BIT ? (X3, Y3) : (AX, AY)`. **6 instructions**, degree 2 in the trace. -/
def emitSelect : List Step :=
  [ (subR X3 AX T0, 0)
  , (mulR T0 BIT T0, 0)
  , (addR AX T0 AX, 0)
  , (subR Y3 AY T1, 0)
  , (mulR T1 BIT T1, 0)
  , (addR AY T1 AY, 0) ]

/-- Load the plane's digit and pin it to a bit; then fold it into the scalar accumulator.
**5 instructions**. ⚑ The scalar fold is what makes the digits the digits OF something: without it
the bit vector is 255 free choices and the ladder computes `Σ bⱼ 2ʲ · B` for a scalar nobody
named. -/
def emitBit (b : Nat) : List Step :=
  [ (wit BIT, b)
  , (mulR BIT BIT T0, 0)
  , (eqR T0 BIT, 0)
  , (addR SC SC SC, 0)
  , (addR SC BIT SC, 0) ]

/-- One ladder plane over base `(bx, by)`: double, digit, candidate, select. **37 instructions**. -/
def emitPlane (accIn : Aff) (bx by_ : Fp) (b : Nat) : List Step :=
  let d := dblAffine accIn
  emitDblA accIn ++ emitBit b ++ emitAddImmA d bx by_ ++ emitSelect

/-- The accumulator after one plane, by the reference. -/
def planeOut (accIn : Aff) (bx by_ : Fp) (b : Nat) : Aff :=
  if b = 1 then addAffine (dblAffine accIn) (bx, by_) else dblAffine accIn

/-- ⚑ **A PLANE IS `A ↦ 2A + b·B`.** Stated so the ladder's meaning is a named fact and not a
comment; `sc ↦ 2sc + b` is the scalar the same plane accumulates, which is why the closing
assertion binds them. -/
theorem plane_is_double_and_conditional_add (accIn : Aff) (bx by_ : Fp) :
    planeOut accIn bx by_ 1 = addAffine (dblAffine accIn) (bx, by_)
      ∧ planeOut accIn bx by_ 0 = dblAffine accIn := by
  constructor <;> rfl

/-! ## §5 — THE STAGE PROGRAMS. -/

/-- The ladder OFFSET. ⚑ Affine coordinates have no point at infinity, so a ladder that started at
the identity would be unrepresentable at its first step. The offset is the first commitment of the
block's own aggregate list, and the closing subtraction of `2^planes · Ω` removes it. -/
def OMEGA : Aff := PT_A

theorem offset_is_a_real_pallas_point : onPallas OMEGA = true := by native_decide

/-- `−P`. -/
def negA (Pt1 : Aff) : Aff := (Pt1.1, fsub 0 Pt1.2)

/-- `2^k · P`, by repeated doubling. -/
def dblPow : Nat → Aff → Aff
  | 0, Pt1 => Pt1
  | k + 1, Pt1 => dblAffine (dblPow k Pt1)

/-- The bit of `v` at plane `j` counting from the TOP of a `k`-plane window (MSB first). -/
def planeBit (v k j : Nat) : Nat := (v / 2 ^ (k - 1 - j)) % 2

/-- ⚑ **THE OPENING INSTRUCTION FORCES THE ZERO REGISTER.** `SUB R0, R0 → R0` reads the first row's
`R0` — whatever the prover put there — and writes `0`. Every immediate-load and every witness-load
below rides on it. -/
def emitInit : List Step := [(subR ZERO ZERO ZERO, 0)]

/-- Load the running total with the first pre-scaled term. -/
def emitLoadT (bx by_ : Fp) : List Step := [(addI ZERO bx TX, 0), (addI ZERO by_ TY, 0)]

/-- The pure ACCUMULATION program: fold a term list with the affine chord law. This is obligation
(2) — the group fold and the scalar↔base pairing at the stage's full term count. -/
def sumSteps : Aff → List Aff → List Step
  | _, [] => []
  | cur, B :: rest => emitAddImmT cur B.1 B.2 ++ sumSteps (addAffine cur B) rest

def sumProg (terms : List Aff) : List Step :=
  match terms with
  | [] => emitInit
  | B0 :: rest => emitInit ++ emitLoadT B0.1 B0.2 ++ sumSteps B0 rest

/-- The reference fold, so the emitted trace's claimed output is COMPUTED and not asserted. -/
def sumRef : Aff → List Aff → Aff
  | cur, [] => cur
  | cur, B :: rest => sumRef (addAffine cur B) rest

def sumOut (terms : List Aff) : Aff :=
  match terms with
  | [] => (0, 0)
  | B0 :: rest => sumRef B0 rest

/-- The LADDER program for one term: `A := Ω`, `k` planes, assert the scalar, remove the offset,
fold into the running total. This is obligation (3). -/
def ladderSteps (acc : Aff) (bx by_ : Fp) (s k : Nat) : Nat → List Step
  | 0 => []
  | j + 1 =>
      let idx := k - (j + 1)
      let b := planeBit s k idx
      emitPlane acc bx by_ b ++ ladderSteps (planeOut acc bx by_ b) bx by_ s k j

def ladderOut (acc : Aff) (bx by_ : Fp) (s k : Nat) : Nat → Aff
  | 0 => acc
  | j + 1 => ladderOut (planeOut acc bx by_ (planeBit s k (k - (j + 1)))) bx by_ s k j

/-- One scaled term `s·B`, in full: the ladder, the scalar assertion, the offset removal, and the
fold into the running total. -/
def emitTerm (cur : Aff) (bx by_ : Fp) (s k : Nat) : List Step :=
  let acc := ladderOut OMEGA bx by_ s k k
  let off := negA (dblPow k OMEGA)
  let scaled := addAffine acc off
  [(subR ZERO ZERO SC, 0), (addI ZERO OMEGA.1 AX, 0), (addI ZERO OMEGA.2 AY, 0)]
  ++ ladderSteps OMEGA bx by_ s k k
  ++ [(eqI SC s, 0)]
  -- remove the offset: (X3,Y3) := A + (−2^k Ω), then A := (X3,Y3)
  ++ emitAddImmA acc off.1 off.2
  ++ [(addR X3 ZERO AX, 0), (addR Y3 ZERO AY, 0)]
  -- fold into the running total
  ++ (let s2 := slopeAdd cur scaled
      [ (subR TX AX T0, 0)
      , (subR TY AY T1, 0)
      , (wit SL, s2)
      , (mulR SL T0 T0, 0)
      , (eqR T0 T1, 0)
      , (mulR SL SL T0, 0)
      , (subR T0 TX T0, 0)
      , (subR T0 AX X3, 0)
      , (subR TX X3 T0, 0)
      , (mulR SL T0 T0, 0)
      , (subR T0 TY TY, 0)
      , (addR X3 ZERO TX, 0) ])

def termOut (cur : Aff) (bx by_ : Fp) (s k : Nat) : Aff :=
  addAffine cur (addAffine (ladderOut OMEGA bx by_ s k k) (negA (dblPow k OMEGA)))

/-- ⚑ **THE LADDER'S OUTPUT IS `s·B` PLUS THE OFFSET IT STARTED FROM**, which is why the closing
subtraction is `2^k·Ω` and not something else. Stated at `k = 1` and `k = 2` on real block data,
where `decide` can reach — the general statement is the standard double-and-add invariant and the
instances are what pin the implementation to it. -/
theorem ladder_carries_the_offset (bx by_ : Fp) (s : Nat) :
    ladderOut OMEGA bx by_ s 1 1
      = (if s % 2 = 1 then addAffine (dblAffine OMEGA) (bx, by_) else dblAffine OMEGA) := by
  show planeOut OMEGA bx by_ (planeBit s 1 0) = _
  unfold planeOut planeBit
  norm_num

/-! ## §6 — THE EMITTED STAGES, over Mina devnet block 539508. -/

/-- The block's polyscale challenge. -/
def XI : Nat := MinaWrapAggregationGate.XI

/-- The 47 commitments `combine_commitments` feeds the terminal MSM, as affine points. Every one is
`z = 1` in the source list, so the affine reading is exact. -/
def COMBINE_AFF : List Aff :=
  MinaWrapAggregationGate.COMBINE_POINTS.map (fun p => (p.1, p.2.1))

theorem combine_aff_is_47_long : COMBINE_AFF.length = 47 := by decide +kernel

theorem every_combine_base_is_on_pallas :
    COMBINE_AFF.all onPallas = true := by native_decide

/-! ### §6a — OBLIGATION (1): THE ξ SCALAR VECTOR, at full fidelity.

⚑ 46 multiplies. `ξ` is a public input on the first row; `ξ⁴⁶` is a public input on the last. Every
intermediate power is a register the ROM's own instruction wrote, so the whole scalar vector of the
47-term aggregate is forced by 46 Pasta multiplies and the register file's hold half. -/

/-! #### ⚑⚑ THE SQUARING BASIS, TAPPED OUT OF THE SAME WALK — 2026-08-05.

The 46-multiply walk already passes through `ξ¹, ξ², ξ⁴, ξ⁸, ξ¹⁶, ξ³²`; it just never kept them.
`MinaWrapXiScalarWeld.the_squaring_basis_generates_the_orbit` is the reason to: at
`c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` the tensor product `∏_j c_j^{bit_j(i)}` **is** `ξ^i` for every
`i < 64`, so those six values are all the ξ-aggregate's 47 scalars need — **six wire values, not
forty-seven.** Six `addR` copies keep them alive to the last row, where the widened pin publishes
them.

⚠ **The registers are the LADDER's, and they are idle here.** `xiChainProg` writes only `ZERO`,
`TX` and `TY`; `AX … T1` are live in `ladderProg`'s inner loop and in no instruction of this one.
Reusing them is what keeps the basis inside `NREG = 12` with no machine change. -/

def XB1  : Nat := AX    -- ξ¹
def XB2  : Nat := AY    -- ξ²
def XB4  : Nat := BIT   -- ξ⁴
def XB8  : Nat := SL    -- ξ⁸
def XB16 : Nat := T0    -- ξ¹⁶
def XB32 : Nat := T1    -- ξ³²

/-- ⚑ **HIGH POWER FIRST** — `PastaMsmScalarDerive`'s own convention, where challenge `j` pairs
with binary digit `nb−1−j` of the generator index. Getting this backwards would publish a basis
whose tensor is `ξ^(bit-reversed i)`, which agrees with `ξ^i` at `i ∈ {0, 63}` and nowhere else. -/
def XI_BASIS_REGS : List Nat := [XB32, XB16, XB8, XB4, XB2, XB1]

/-- The basis width: six challenges. -/
def NBASIS : Nat := 6

/-- ⚑ **AND THE SIX ARE SIX DISTINCT REGISTERS, NONE OF THEM THE CHAIN'S OWN.** A tap that aliased
`TY` would publish `ξ⁴⁶` six times and every downstream `decide` would still be green about it. -/
theorem the_basis_registers_are_distinct_and_idle :
    XI_BASIS_REGS.length = NBASIS
      ∧ XI_BASIS_REGS.eraseDups.length = NBASIS
      ∧ XI_BASIS_REGS.all (fun r => decide (r < NREG)) = true
      ∧ XI_BASIS_REGS.all (fun r => decide (r ≠ ZERO ∧ r ≠ TX ∧ r ≠ TY)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The copy that keeps `ξ^k` after the `k`-th multiply, for the six `k` the basis names. `addR x y
w` is `w := x + y`, so `addR TY ZERO XBk` is a register move and nothing else. -/
def xiBasisTap : Nat → List Step
  | 1  => [(addR TY ZERO XB1,  0)]
  | 2  => [(addR TY ZERO XB2,  0)]
  | 4  => [(addR TY ZERO XB4,  0)]
  | 8  => [(addR TY ZERO XB8,  0)]
  | 16 => [(addR TY ZERO XB16, 0)]
  | 32 => [(addR TY ZERO XB32, 0)]
  | _  => []

/-- `R1 := ξ` is the FIRST-ROW public-input pin; `R2 := 1` is the zeroth scalar; then `R2 := R2 · R1`
forty-six times walks the whole vector `(ξ⁰, …, ξ⁴⁶)` through the register file — tapping the six
squaring powers into their holds on the way. -/
def xiChainSteps (n : Nat) : List Step :=
  (List.range n).flatMap (fun j => (mulR TY TX TY, 0) :: xiBasisTap (j + 1))

def xiChainProg : List Step :=
  emitInit ++ [(addI ZERO 1 TY, 0)] ++ xiChainSteps 46

/-- ⚑ **THE TAPS COST SIX INSTRUCTIONS AND THE CHAIN STILL FITS ITS 64-ROW TRACE.** `1 + 1 + 46`
multiplies plus `6` copies is `54`; the emitted height is unchanged, so the basis is bought out of
padding and not out of a re-shaped artifact. -/
theorem the_chain_is_fifty_four_instructions :
    xiChainProg.length = 54 ∧ (xiChainSteps 46).length = 52
      ∧ ((List.range 47).filter (fun k => !(xiBasisTap k).isEmpty)) = [1, 2, 4, 8, 16, 32] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- ⚑ **THE CHAIN'S ENDPOINT IS `ξ⁴⁶`**, the last scalar `combine_commitments` assigns — computed
by `qpow`, which is **`q`-arithmetic**: `ξ` is a SCALAR-field element and reducing its powers mod
the BASE field would be the classic Pasta error. The chain's AIR is emitted at `qLimb` for the same
reason (`xiDesc`), and `MinaWrapCommitMachine.the_reference_ops_are_the_pasta_ones` is the weld
between the machine's own interpreter and `PastaField.Ref.fq*`. -/
def XI_46 : Nat := qpow XI 46

theorem xi_chain_starts_at_one_and_walks_by_xi :
    qpow XI 0 = 1 ∧ qpow XI 1 = XI ∧ qpow XI 47 = qmul XI_46 XI := by
  refine ⟨rfl, ?_, rfl⟩
  show qmul 1 XI = XI
  native_decide

/-- ⚑ **AND THE TWO REDUCTIONS REALLY DO DISAGREE**, on the block's own challenge — so the choice
above is a decision the data can refute, not a convention. Reading `ξ²` in the base field gives a
different scalar, and the aggregate it produces is not the block's. -/
theorem the_base_field_reduction_of_xi_squared_is_a_different_scalar :
    qmul XI XI ≠ fmul XI XI := by native_decide

/-! ### §6b — OBLIGATION (2): THE GROUP FOLD AT FULL TERM COUNT.

The term list is `ξⁱ · Cᵢ`, computed HERE by the reference scalar multiplication, so the fold's
output is the block's own aggregate. -/

/-- Projective `smul`/`padd` are `MinaWrapGroupGate`'s, already `decide`-checked against o1-labs'
`multi_scalar_mul`; the affine reading normalises by `finv`. -/
def toAff (p : MinaWrapGroupGate.Pt) : Aff :=
  let zi := finv p.2.2
  (fmul p.1 zi, fmul p.2.1 zi)


/-- The 47 PRE-SCALED terms `ξⁱ · Cᵢ`, by `MinaWrapGroupGate`'s own projective ladder. -/
def XI_TERMS : List Aff :=
  (List.range 47).map (fun i =>
    toAff (MinaWrapGroupGate.smul (qpow XI i)
      (MinaWrapAggregationGate.COMBINE_POINTS.getD i (0, 0, 1))))

/-- ⚑ The 41 NOMINAL terms of `public_comm`: the forty Lagrange bases at the block's own NEGATED
public inputs, then the SRS blinder `H` that `mask_custom` adds (`verifier.rs:849-855`). The blinder
is a TERM, not a decoration — `MinaWrapPublicCommGate.tamper_blinder_dropped` is the refutation that
dropping it changes the answer. -/
def PUBLIC_TERMS_NOMINAL : List Aff :=
  ((List.range 40).map (fun i =>
      toAff (MinaWrapGroupGate.smul (MinaWrapPublicCommGate.NEG_PUBLIC.getD i 0)
        (MinaWrapPublicCommGate.LAGRANGE.getD i (0, 0, 1)))))
  ++ [toAff MinaWrapPublicCommGate.SRS_H]

/-! ### ⚑ THE IDENTITY CANNOT RIDE IN AN AFFINE TERM LIST — found 2026-08-05, on the wire.

TEN of the block's forty public inputs are **zero**. `smul 0 P` is the point at infinity, and
`toAff` reads it as `(0, 0)` — because `finv 0 = 0`, not because `(0,0)` means anything. `(0,0)` is
**not on Pallas**, and folding it with `addAffine` takes the running total OFF THE CURVE.

⚑ **The 41-term fold reached o1-labs' `public_comm` ANYWAY, and only because ten is EVEN.** Adding
`(0,0)` twice is the identity map, so the ten pseudo-points cancel in pairs and the accumulator
returns to the curve. With an odd count the answer is simply WRONG. That is a correct result
standing on a parity coincidence in one block's public inputs, and the theorems below are what
replace the coincidence: the identity terms are DROPPED, and the fold is over the 31 that carry a
non-zero scalar.

This is the same "nominal vs meaningful" split `FT_TERMS` already carries (9 nominal / 7 meaningful),
now forced by the data rather than by the shape of `verifier.rs`. -/

/-- The affine reading of the point at infinity. Not a point — a sentinel `toAff` produces. -/
def AFF_IDENTITY : Aff := (0, 0)

/-- ⚑ **AND IT IS NOT ON THE CURVE**, which is the whole reason it cannot be a fold term. -/
theorem the_affine_identity_is_not_on_pallas : onPallas AFF_IDENTITY = false := by native_decide

/-- ⚑ **ONE OF THEM TAKES THE FOLD OFF PALLAS; TWO OF THEM CANCEL.** The mechanism, on the block's
own point — this is the coincidence the filter removes, stated so it cannot be rediscovered. -/
theorem the_identity_term_leaves_the_curve_and_pairs_cancel :
    onPallas (addAffine PT_A AFF_IDENTITY) = false
      ∧ addAffine (addAffine PT_A AFF_IDENTITY) AFF_IDENTITY = PT_A := by native_decide

/-- ⚑ **THE MEANINGFUL TERMS — 31 of 41.** -/
def PUBLIC_TERMS : List Aff :=
  PUBLIC_TERMS_NOMINAL.filter (fun p => !(decide (p.1 = 0) && decide (p.2 = 0)))

/-- ⚑ **THE CENSUS: 41 nominal, 31 meaningful, 10 dropped.** -/
theorem the_public_term_census :
    PUBLIC_TERMS_NOMINAL.length = 41 ∧ PUBLIC_TERMS.length = 31 := by
  native_decide

/-- ⚑ **AND EVERYTHING DROPPED WAS THE IDENTITY** — nothing with a real scalar left the fold. -/
theorem only_identity_terms_were_dropped :
    ((PUBLIC_TERMS_NOMINAL.filter (fun p => decide (p.1 = 0) && decide (p.2 = 0))).all
      (fun p => decide (p = AFF_IDENTITY))) = true := by
  native_decide

/-- ⚑ **AND EVERY SURVIVING TERM IS A REAL PALLAS POINT.** -/
theorem every_meaningful_public_term_is_on_pallas :
    PUBLIC_TERMS.all onPallas = true := by
  native_decide

/-- ⚑ The 8 terms of `ft_comm`: `chunk(f_comm, ζ^srs)` — one chunk on the wrap side, so `f_comm`
itself — minus each of the seven `t_comm` chunks at `ζ^(srs·j) · (ζⁿ − 1)`. **9 nominal, 7
meaningful**: the nominal count counts `f_comm` and the Maller factor as terms of their own; the
group fold sees `1 + 7 = 8` points, and the seven that carry a non-trivial scalar are the
meaningful ones. -/
def FT_TERMS : List Aff :=
  toAff MinaWrapGroupGate.fComm
  :: (List.range 7).map (fun j =>
       toAff (MinaWrapGroupGate.smul
         (qneg (qmul (qpow MinaWrapGroupGate.ZETA_SRS j) MinaWrapGroupGate.ZETA_DOM_M1))
         (MinaWrapGroupGate.TCHUNKS.getD j (0, 0, 1))))

/-! ### §6c — ⚑ THE WELD TO o1-LABS, AS NAMED THEOREMS.

Until now these four folds matched o1-labs' own values by **two adjacent `IO.println`s** in
`EmitCommitStages.lean` — a human reading two lines of stdout and agreeing they were the same
digits. A sibling lane deleted exactly that shape after finding all 174 of its constants correctly
copied, and its reason is the reason these exist: *"one wrong digit would have given a
self-consistent tree — Lean proving the program computes ITS constants, the harness pinning ITS
digest, every gate green."*

Each theorem below says the AFFINE fold this file emits a descriptor for lands on the value the
gate cone already carries from Mina devnet block 539508 — and each of those goldens is separately
`by decide`-checked against o1-labs' `PolyComm::multi_scalar_mul`. The `golds` printlns are
deleted; a reader wanting the comparison reads these.

⚠ What these do NOT say is that the SCALING is in-circuit — it is not, in this file. These are
folds of PRE-SCALED points, and `MinaWrapXiAggregateMsm` is where the ξ-aggregate's scalar
multiplication actually happens inside a descriptor. -/

/-- ⚑ **THE ξ-AGGREGATE FOLD REACHES o1-LABS' AGGREGATE.** -/
theorem the_xi_fold_is_o1_labs_aggregate :
    sumOut XI_TERMS = toAff MinaWrapAggregationGate.COMBINED_GOLD := by native_decide

/-- ⚑ **THE `public_comm` FOLD REACHES o1-LABS' `public_comm`** — the 31 Lagrange terms with a
non-zero public input, plus the `mask_custom` blinder, which is a TERM and not a decoration. -/
theorem the_public_fold_is_o1_labs_public_comm :
    sumOut PUBLIC_TERMS = toAff MinaWrapPublicCommGate.PUBLIC_COMM_GOLD := by
  native_decide

/-- ⚑ **AND THE 41-TERM FOLD REACHED IT TOO — BY PARITY, NOT BY CONSTRUCTION.** Kept as the record
of what was actually shipped before 2026-08-05: the nominal fold agrees. -/
theorem the_nominal_fold_also_agreed :
    sumOut PUBLIC_TERMS_NOMINAL = toAff MinaWrapPublicCommGate.PUBLIC_COMM_GOLD := by
  native_decide

/-- ⚑ **…AND ONE MORE IDENTITY BREAKS IT.** This is the refutation that makes the theorem above a
COINCIDENCE rather than a result: append a single further point at infinity — the shape a block with
an odd number of zero public inputs would produce — and the fold misses o1-labs' value. The filtered
`PUBLIC_TERMS` is insensitive to this by construction; the nominal list was not. -/
theorem an_odd_identity_count_misses_the_golden :
    sumOut (PUBLIC_TERMS_NOMINAL ++ [AFF_IDENTITY])
      ≠ toAff MinaWrapPublicCommGate.PUBLIC_COMM_GOLD := by
  native_decide

/-- ⚑ …and the filtered fold IS insensitive: the same appended identity is dropped, so the answer
does not move. -/
theorem the_filtered_fold_is_insensitive_to_an_appended_identity :
    sumOut ((PUBLIC_TERMS_NOMINAL ++ [AFF_IDENTITY]).filter
      (fun p => !(decide (p.1 = 0) && decide (p.2 = 0))))
      = toAff MinaWrapPublicCommGate.PUBLIC_COMM_GOLD := by
  native_decide

/-- ⚑ **THE `ft_comm` FOLD REACHES o1-LABS' `ft_comm`.** -/
theorem the_ft_fold_is_o1_labs_ft_comm :
    sumOut FT_TERMS = toAff MinaWrapGroupGate.FT_COMM_GOLD := by native_decide

/-- ⚑ **THE `f_comm` FOLD REACHES o1-LABS' `f_comm`** — one term, because
`linearization.index_terms` is empty on the wrap side. -/
theorem the_f_fold_is_o1_labs_f_comm :
    sumOut [toAff MinaWrapGroupGate.fComm] = toAff MinaWrapGroupGate.F_COMM_GOLD := by native_decide

/-- ⚑ **AND THE FOUR GOLDENS ARE FOUR DIFFERENT POINTS.** Without this, four theorems of the form
`sumOut X = toAff G` would all be satisfied by a cone in which every `G` had collapsed to the same
value — which is exactly what a wrong shared constant looks like. -/
theorem the_four_goldens_are_distinct :
    toAff MinaWrapAggregationGate.COMBINED_GOLD ≠ toAff MinaWrapPublicCommGate.PUBLIC_COMM_GOLD
      ∧ toAff MinaWrapGroupGate.FT_COMM_GOLD ≠ toAff MinaWrapGroupGate.F_COMM_GOLD
      ∧ toAff MinaWrapAggregationGate.COMBINED_GOLD ≠ toAff MinaWrapGroupGate.FT_COMM_GOLD := by
  native_decide

/-! ## §7 — THE CENSUS: what a full-width stage costs on this machine. -/

/-- Instructions per ladder plane. -/
def PLANE_COST : Nat := 37
/-- Fixed cost of one scaled term besides its planes. -/
def TERM_FIXED : Nat := 3 + 1 + 11 + 2 + 12
/-- Instructions for one term at `k` planes. -/
def termCost (k : Nat) : Nat := TERM_FIXED + PLANE_COST * k
/-- Instructions for an `n`-term stage at `k` planes. -/
def stageCost (n k : Nat) : Nat := 1 + n * termCost k

theorem plane_and_term_costs : PLANE_COST = 37 ∧ TERM_FIXED = 29 ∧ termCost 255 = 9464 := by decide +kernel

/-- ⚑ **THE FULL-WIDTH PRICE, PER STAGE.** 255 planes is the Pasta scalar width. -/
def COST_PUBLIC_COMM : Nat := stageCost 40 255
def COST_F_COMM : Nat := stageCost 1 255
def COST_FT_COMM : Nat := stageCost 9 255
def COST_XI : Nat := stageCost 47 255

theorem full_width_ladder_price :
    COST_PUBLIC_COMM = 378561 ∧ COST_F_COMM = 9465 ∧ COST_FT_COMM = 85177
      ∧ COST_XI = 444809 := by decide +kernel

/-- ⚑ **EVERY STAGE FITS ONE ROM AT FULL WIDTH, AND THEIR SUM DOES NOT** — the same shape
`MinaWrapVerifierProgram` found at a coarser price, now at this machine's 40-cell instruction word,
which holds `838 860` instructions. The ξ-aggregate is the largest at **53.0%**. -/
theorem every_stage_fits_one_rom_at_full_width :
    COST_PUBLIC_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_F_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_FT_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_XI ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MAX_ROM_CELLS / ROM_ARITY
        < COST_PUBLIC_COMM + COST_F_COMM + COST_FT_COMM + COST_XI := by decide +kernel

/-- ⚑ **THE SCALAR VECTOR IS 1/9464 OF ITS OWN STAGE.** 47 instructions against the ξ-aggregate's
444 809 — which is the whole reason obligation (1) is emitted at FULL fidelity and obligation (3)
is not: they are not the same size of problem, and a report that presented them as one stage would
be hiding a factor of nine thousand. ⚠ The first draft of this theorem asserted `10000 · 47` and
`decide` REFUTED it; the true ratio is `9464 = termCost 255`, not a round number someone liked. -/
theorem the_scalar_vector_is_a_rounding_error_against_its_own_stage :
    9464 * 47 < COST_XI ∧ 9465 * 47 > COST_XI := by decide +kernel

/-! ## §8 — THE EMITTED OBJECTS.

Each stage is a program padded to a power-of-two height with `add R0, #0 → ∅` — a real ALU
operation, because `selSumExpr` is inherited and there is no nop. The ROM manifest has one row per
instruction and `PublicLookupBalanced` is a PERMUTATION, so the manifest length IS the trace
length: a prover cannot run the program twice, stop early, or pad. -/

/-- Pad a program to `n` instructions. -/
def padTo (n : Nat) (p : List Step) : List Step :=
  p ++ List.replicate (n - p.length) (PAD, 0)

/-- ONE 32-limb boundary block: register `r`'s limb columns on `row`, at public-input base `base`.
Every pin in this file is one of these, so a block that landed at the wrong PI base would move a
whole 32-felt slice rather than one felt — which is what makes the widened surface below readable
as eight blocks and not as 256 indices. -/
def pinBlock (row : VmRow) (r base : Nat) : List AirLeg :=
  (List.range SK).map (fun i => AirLeg.pin ⟨row, regCol r + i, base + i⟩)

/-- The 64 boundary pins: `R_in`'s 32 limbs on the FIRST row, `R_out`'s on the LAST. -/
def pinPair (rIn rOut : Nat) : List AirLeg :=
  pinBlock VmRow.first rIn 0 ++ pinBlock VmRow.last rOut SK

/-- ⚑ **THE FOLD PINS BOTH COORDINATES OF THE RESULT** — 64 public inputs, `TX` and `TY` on the
last row. A stage that pinned only the abscissa would accept `−Σ sᵢBᵢ` as readily as the sum. -/
def pinOutPoint : List AirLeg :=
  ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol TX + i, i⟩))
  ++ ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol TY + i, SK + i⟩))

def PI64 : Nat := 2 * SK

/-- Public inputs from a field element pair. -/
def piPair (u v : Fp) : List ℤ :=
  (List.range SK).map (limbAt u) ++ (List.range SK).map (limbAt v)

/-- ONE published field element, as the `SK` eight-bit limbs every boundary in this cone uses. -/
def piBlock (v : Fp) : List ℤ := (List.range SK).map (limbAt v)

theorem piPair_is_two_blocks (u v : Fp) : piPair u v = piBlock u ++ piBlock v := rfl

/-! ### ⚑⚑ THE ξ CHAIN'S WIDENED BOUNDARY — the squaring basis ON THE WIRE.

`MinaWrapXiScalarWeld` §3 measured the obstruction and the fix in the same breath: the ξ-aggregate
had **no PI slot** for a computed scalar, and the derivation that closes it needs a **six**-element
challenge vector rather than a 47-element one. This is the publishing half. Eight blocks, `8 · 32 =
256` public inputs:

| block | row | register | what it carries |
|---|---|---|---|
| 0 | first | `TX` | `ξ` — consumed from `MinaWrapXiEndoLift`'s output |
| 1 | last | `TY` | `ξ⁴⁶`, the orbit's endpoint |
| 2–7 | last | `XB32 … XB1` | ⚑ **the squaring basis, high power first** |

⚠ **FLAG DAY.** `piCount` moves `64 → 256` and the descriptor is `::v2`; `mina-commit-xi.json` and
`mina-commit-xi-pis.txt` re-emit, and a `::v1` artifact no longer resolves under this name. Nothing
migrates. -/

/-- The widened public-input count: input ξ, output ξ⁴⁶, and the six basis powers. -/
def PI_XI : Nat := (2 + NBASIS) * SK

/-- ⚑ **THE EIGHT PINNED BLOCKS.** -/
def pinXiChain : List AirLeg :=
  pinPair TX TY
  ++ pinBlock VmRow.last XB32 (2 * SK) ++ pinBlock VmRow.last XB16 (3 * SK)
  ++ pinBlock VmRow.last XB8  (4 * SK) ++ pinBlock VmRow.last XB4  (5 * SK)
  ++ pinBlock VmRow.last XB2  (6 * SK) ++ pinBlock VmRow.last XB1  (7 * SK)

/-- ⚑ **AND THE EIGHT BLOCKS TILE THE PI SURFACE EXACTLY.** 256 pins, every declared slot addressed
once, none twice and none past the count — so a block written at a stale base would leave a hole
here rather than silently overlap a neighbour. -/
theorem the_pinned_blocks_tile_the_public_inputs :
    pinXiChain.length = PI_XI ∧ PI_XI = 256
      ∧ ((List.range PI_XI).all (fun k =>
            decide ((pinXiChain.filter
                      (fun l => match l with | .pin p => p.idx == k | _ => false)).length = 1)))
          = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The initial register file of every stage: all zero except the pinned inputs. -/
def initRegs (r : Nat) (v : Nat) : RegFile := fun k => if k = r then v else 0

/-! ### §8-pre — ⚑ THE STRICT REGISTER FILE IS THIS FILE'S INITIAL STATE, not a copy of it.

Every trace below runs on `runRowsVecAt`, whose state is a strict `NREG`-entry `List Nat`. These
two theorems are the only thing standing between that and the closures the stages were written
against, and they are what makes the swap a REWRITE: `regsOf` of the strict initial file IS
`initRegs`, so `runRowsVecAt_is_runRowsAt` applies and **no emitted byte can move.** -/

/-- ⚑ **THE STRICT ZERO FILE IS `initRegs ZERO 0`.** -/
theorem regsOf_zeroVec : regsOf zeroVec = initRegs ZERO 0 := by
  funext k
  unfold regsOf readVec zeroVec initRegs ZERO
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k NREG with h | h
  · rw [List.getElem?_replicate_of_lt h]; simp
  · rw [List.getElem?_eq_none (by simpa using h)]; simp

/-- ⚑ **AND THE STRICT PINNED FILE IS `initRegs r v`**, for any register the file actually has. -/
theorem regsOf_pinVec (r v : Nat) (hr : r < NREG) : regsOf (pinVec r v) = initRegs r v := by
  funext k
  unfold regsOf pinVec initRegs
  rcases Nat.lt_or_ge k NREG with h | h
  · rw [readVec_map _ k h]
  · rw [readVec_map_ge _ k (by omega)]
    have : ¬ (k = r) := by omega
    rw [if_neg this]

/-! ### §8a — STAGE (S): the ξ scalar vector, FULL fidelity. -/

def XI_HEIGHT : Nat := 64
def xiProg : List Step := padTo XI_HEIGHT xiChainProg

theorem xiProg_length : xiProg.length = 64 := by decide +kernel

/-- ⚑ **THE SCALAR CHAIN'S AIR IS AT `qLimb`**, the Pallas SCALAR prime — the same `commitAir`, the
same gates, a different limb vector. Emitting it at `pLimb` would be an AIR for the wrong field. -/
def xiAir : EffectAir :=
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs xiProg) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs xiProg)).legs
              ++ pinXiChain }

theorem xiAir_mainRailOk : xiAir.mainRailOk = true := by
  unfold xiAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinXiChain, pinPair, pinBlock, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩,
    fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩

/-- ⚑ **`::v2` — THE PI SURFACE WIDENED, SO THE NAME MOVED.** `PastaMsmBucketed`'s own §4b: a name
is a KEY, and two AIRs that differ in their published surface must not share one. -/
def xiDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-xi-scalar-vector::v2" CM_WIDTH PI_XI [] xiAir

/-- ⚑ **THE LIMB VECTOR IS MEMOISED, AND THAT IS NOT COSMETIC.** `qLimb j` is a 255-bit shift, and
`mulAsg` queries it thousands of times per emitted column. On the `pN` path `pLimb` is a CONSTANT
the compiler can cache; passed as a parameter to `runRowsAt` it is an indirect call with no caching,
and the `qN` trace stopped finishing. The table is an ARGUMENT to `limbTable` for the same reason
`materialize` takes one. -/
def limbTable (l : List ℤ) : Nat → ℤ := fun j => l.getD j 0

def qLimbFast : Nat → ℤ :=
  limbTable ((List.range 80).map Dregg2.Circuit.Emit.PastaFieldSound.qLimb)

/-- ⚑ **AND IT IS THE SAME VECTOR.** Below 80 by evaluation; at and above 80 both are `0`, because
`qN < 2^255 < 2^(8·80)`. A memoisation that quietly changed a gate constant would make the emitted
trace refuse against its own descriptor, so this is checked rather than trusted. -/
theorem qLimbFast_agrees_below_80 :
    ((List.range 80).all
      fun j => decide (qLimbFast j = Dregg2.Circuit.Emit.PastaFieldSound.qLimb j)) = true := by
  native_decide

/-- ⚑ **THE ξ TRACE, on the STRICT register file.** `runRowsVecAt` threads an `NREG`-entry
`List Nat` where `runRowsAt` threaded a closure; the closure generator is `Theta(d^2)` in the
program depth, which is why this trace was emitted as a ZERO-BYTE file and withdrawn. -/
def xiTrace : List (List ℤ) :=
  runRowsVecAt PastaField.qN qLimbFast (pinVec TX XI) (witsOf xiProg) 0 (instrs xiProg)

/-- ⚑ **AND NOT ONE BYTE MOVED.** The strict generator emits the closure generator's list, by
`runRowsVecAt_is_runRowsAt` at `regsOf (pinVec TX XI) = initRegs TX XI` — so the fixture check is a
confirmation of this theorem and not the reason to believe it. -/
theorem xiTrace_is_the_closure_trace :
    xiTrace = runRowsAt PastaField.qN qLimbFast (initRegs TX XI) (witsOf xiProg) 0 (instrs xiProg) := by
  unfold xiTrace
  rw [runRowsVecAt_is_runRowsAt _ _ _ _ _ _ (pinVec_length TX XI), regsOf_pinVec TX XI (by decide)]

/-- ⚑ **THE SIX BASIS VALUES, HIGH POWER FIRST.** `PastaMsmScalarDerive.sAt`'s convention pairs
challenge `j` with binary digit `nb−1−j`, so `c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` and its tensor
`∏_j c_j^{bit_j(i)}` is `ξ^i`. -/
def XI_BASIS : List Nat :=
  [qpow XI 32, qpow XI 16, qpow XI 8, qpow XI 4, qpow XI 2, XI]

/-- ⚑ **AND THE BASIS IS SIX SQUARINGS OF ONE VALUE**, not six numbers a file chose: each entry is
the square of its successor, ending on `ξ` itself. `the_chain_computes_the_basis` in
`MinaWrapXiBasisWeld` is the same fact about the emitted MACHINE. -/
theorem the_basis_is_the_squaring_orbit :
    XI_BASIS.length = NBASIS
      ∧ ((List.range (NBASIS - 1)).all
          (fun j => decide (XI_BASIS.getD j 0
                      = qmul (XI_BASIS.getD (j + 1) 0) (XI_BASIS.getD (j + 1) 0)))) = true
      ∧ XI_BASIS.getD (NBASIS - 1) 0 = XI := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **THE WIDENED PI VECTOR — 256 FELTS IN EIGHT BLOCKS.** `ξ`, `ξ⁴⁶`, then the squaring basis. -/
def xiPIs : List ℤ := piPair XI XI_46 ++ XI_BASIS.flatMap piBlock

theorem the_chain_publishes_two_hundred_and_fifty_six_felts :
    xiPIs.length = PI_XI ∧ xiDesc.piCount = PI_XI := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE BASIS BLOCK IS SIX DISTINCT FIELD ELEMENTS.** Without this the elementwise weld
downstream would be equally green over a basis that had collapsed to six copies of one value — the
exact shape a tap that aliased its register would produce, and one no length check sees. -/
theorem the_published_basis_is_six_distinct_values :
    XI_BASIS.eraseDups.length = NBASIS
      ∧ (xiPIs.drop (2 * SK)).length = NBASIS * SK
      ∧ XI_BASIS.all (fun v => decide (2 ^ 240 < v ∧ v < PastaField.qN)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ### §8b — STAGE (G2): the group folds, at FULL term count. -/

/-- The fold descriptor for a term list. -/
def foldAir (terms : List Aff) : EffectAir :=
  let prog := padTo (Nat.max 8 (Nat.nextPowerOfTwo (sumProg terms).length)) (sumProg terms)
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs prog) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs prog)).legs
              ++ pinOutPoint }

def foldProg (terms : List Aff) : List Step :=
  padTo (Nat.max 8 (Nat.nextPowerOfTwo (sumProg terms).length)) (sumProg terms)

theorem foldAir_mainRailOk (terms : List Aff) : (foldAir terms).mainRailOk = true := by
  unfold foldAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinOutPoint, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

def foldDesc (name : String) (terms : List Aff) : EffectVmDescriptor2 :=
  lowerAir name CM_WIDTH PI64 [] (foldAir terms)

/-- ⚠ `p` is bound ONCE. `witsOf (foldProg terms)` closes over a recomputation of `foldProg`, and
`foldProg` runs the whole reference fold — 41 modular inverses for `public_comm` — so a witness
lookup per row made trace generation quadratic in the fold's own cost. Measured: the 1 024-row
aggregate did not finish in four minutes. -/
def foldTrace (terms : List Aff) : List (List ℤ) :=
  let p := foldProg terms
  runRowsVecAt pN Dregg2.Circuit.Emit.PastaFieldSound.pLimb zeroVec (witsOf p) 0 (instrs p)

/-- ⚑ **AND NOT ONE BYTE MOVED**, for EVERY term list — this is a theorem about the generator, not
about the two committed fixtures, so the stages that never fit a fixture are covered by it too. -/
theorem foldTrace_is_the_closure_trace (terms : List Aff) :
    foldTrace terms
      = (let p := foldProg terms; runRows (initRegs ZERO 0) (witsOf p) 0 (instrs p)) := by
  unfold foldTrace
  rw [runRowsVecAt_is_runRowsAt _ _ _ _ _ _ zeroVec_length, regsOf_zeroVec,
    runRowsAt_is_the_base_field_one]

def foldPIs (terms : List Aff) : List ℤ := piPair (sumOut terms).1 (sumOut terms).2

/-- ⚑ **THE FOUR STAGES.** `public_comm` at 41 terms (40 Lagrange + the `mask_custom` blinder),
`f_comm` at 1, `ft_comm` at 8 points (9 nominal / 7 meaningful), the ξ-aggregate at 47. -/
def publicCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-public-comm-fold::v1" PUBLIC_TERMS
def fCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-f-comm-fold::v1" [toAff MinaWrapGroupGate.fComm]
def ftCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-ft-comm-fold::v1" FT_TERMS
def xiAggDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-xi-aggregate-fold::v1" XI_TERMS

/-! ### §8c — STAGE (G): the ladder, so obligation (3) has a wire. -/

/-- The demo ladder's plane count. ⚠ **8, not 255.** `full_width_ladder_price` is the number this
is a reduction of, and the reduction is in the PLANE count only: the base is the block's real
`sigma_comm[6]`, the assertion `SC = s` is the real one, and every gate is the full-width gate. -/
def DEMO_PLANES : Nat := 8
/-- The demo scalar: the low 8 bits of the block's own `perm_scalars` output, so the digits are
real digits of a real transcript value rather than a number someone picked. -/
def DEMO_SCALAR : Nat := MinaWrapGroupGate.PERM_SCALAR % 2 ^ DEMO_PLANES

def SIGMA6_AFF : Aff := toAff MinaWrapGroupGate.SIGMA6

def ladderSteps' : List Step :=
  emitInit ++ emitLoadT SIGMA6_AFF.1 SIGMA6_AFF.2
  ++ emitTerm SIGMA6_AFF SIGMA6_AFF.1 SIGMA6_AFF.2 DEMO_SCALAR DEMO_PLANES

def ladderProg : List Step :=
  padTo (Nat.max 8 (Nat.nextPowerOfTwo ladderSteps'.length)) ladderSteps'

def ladderAir : EffectAir :=
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs ladderProg) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs ladderProg)).legs
              ++ pinOutPoint }

theorem ladderAir_mainRailOk : ladderAir.mainRailOk = true := by
  unfold ladderAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinOutPoint, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- ⚑ **NO PIN IS DECORATIVE** — every published column is DERIVED by another leg: the 64 pins
publish `TX`/`TY`'s limb columns, which the routing gates and the register window legs read.

⚑ Named so `ladderTiedAir` is HANDED both verdicts. Its fields are `autoParam`s defaulting to
`by decide`; a blank field re-derives, inside the elaborator's `whnf`, a fact this file already
carries — and for `ok` that fact is `commitAir_mainRailOk` APPLIED, not a `decide` over the
assembled ladder at all. -/
theorem ladderAir_pinsTied : ladderAir.pinsTied = true := by
  unfold ladderAir
  apply EffectAir.pinsTied_append
  · refine EffectAir.pinsTied_of_no_pins _ fun p hp => ?_
    simp [commitAir, selBoolLegs, regWindowLegs] at hp
  · intro p hp
    simp only [pinOutPoint, List.mem_append, List.mem_map, List.mem_range, AirLeg.pin.injEq] at hp
    unfold EffectAir.readsCol
    have key : ∀ r, r < NREG → ∀ i, i < Dregg2.Circuit.Emit.PastaFieldSound.SK →
        ((commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs ladderProg)).legs.any
          fun m => decide (regCol r + i ∈ m.readCols)) = true := by
      intro r hr i hi
      refine List.any_eq_true.mpr ⟨AirLeg.window ⟨.transition, regWindowExpr r i⟩, ?_, ?_⟩
      · simp [commitAir, regWindowLegs]
        exact Or.inr (Or.inl ⟨r, hr, i, hi, rfl⟩)
      · simp [AirLeg.readCols, regWindowExpr, Dregg2.Circuit.GateExpr.render,
          Dregg2.Circuit.GateExpr.gEsub, Dregg2.Circuit.GateExpr.gMux,
          Dregg2.Circuit.GateExpr.toWindow, Dregg2.Circuit.EffectAirIR.windowCols,
          Dregg2.Circuit.GateExpr.WLeaf.expr]
    rcases hp with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact key TX (by decide) i hi
    · exact key TY (by decide) i hi

/-- ⚑ **THE TIED SOURCE** — `ladderAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def ladderTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := ladderAir
  ok   := ladderAir_mainRailOk
  tied := ladderAir_pinsTied

def ladderDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-scalar-mul-ladder::v1" CM_WIDTH PI64 [] ladderTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem ladderDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines ladderDesc [] ladderAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-scalar-mul-ladder::v1" CM_WIDTH PI64 [] ladderTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs that reason through `lowerAir`. -/
theorem ladderDesc_eq_lowerAir :
    ladderDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-scalar-mul-ladder::v1" CM_WIDTH PI64 [] ladderAir := rfl

def ladderTrace : List (List ℤ) :=
  let p := ladderProg
  runRowsVecAt pN Dregg2.Circuit.Emit.PastaFieldSound.pLimb zeroVec (witsOf p) 0 (instrs p)

/-- ⚑ **AND NOT ONE BYTE MOVED** for the ladder either. -/
theorem ladderTrace_is_the_closure_trace :
    ladderTrace = (let p := ladderProg; runRows (initRegs ZERO 0) (witsOf p) 0 (instrs p)) := by
  unfold ladderTrace
  rw [runRowsVecAt_is_runRowsAt _ _ _ _ _ _ zeroVec_length, regsOf_zeroVec,
    runRowsAt_is_the_base_field_one]

def ladderRef : Aff := termOut SIGMA6_AFF SIGMA6_AFF.1 SIGMA6_AFF.2 DEMO_SCALAR DEMO_PLANES
def ladderPIs : List ℤ := piPair ladderRef.1 ladderRef.2

#assert_compiled finv_is_an_inverse
#assert_compiled slope_pin_holds_on_real_block_points
#assert_compiled tangent_pin_holds_on_a_real_block_point
#assert_compiled chord_law_stays_on_pallas
#assert_axioms allocation_fits_the_register_file
#assert_axioms plane_is_double_and_conditional_add
#assert_compiled offset_is_a_real_pallas_point
#assert_axioms ladder_carries_the_offset
#assert_axioms combine_aff_is_47_long
#assert_compiled every_combine_base_is_on_pallas
#assert_compiled xi_chain_starts_at_one_and_walks_by_xi
#assert_compiled the_base_field_reduction_of_xi_squared_is_a_different_scalar
#assert_axioms plane_and_term_costs
#assert_axioms full_width_ladder_price
#assert_axioms every_stage_fits_one_rom_at_full_width
#assert_axioms the_scalar_vector_is_a_rounding_error_against_its_own_stage
#assert_axioms xiProg_length
#assert_axioms xiAir_mainRailOk
#assert_axioms foldAir_mainRailOk
#assert_axioms ladderAir_mainRailOk
#assert_compiled qLimbFast_agrees_below_80
#assert_axioms regsOf_zeroVec
#assert_axioms regsOf_pinVec
#assert_axioms xiTrace_is_the_closure_trace
#assert_axioms foldTrace_is_the_closure_trace
#assert_axioms ladderTrace_is_the_closure_trace
#assert_compiled the_xi_fold_is_o1_labs_aggregate
#assert_compiled the_public_fold_is_o1_labs_public_comm
#assert_compiled the_ft_fold_is_o1_labs_ft_comm
#assert_compiled the_f_fold_is_o1_labs_f_comm
#assert_compiled the_four_goldens_are_distinct
#assert_compiled the_affine_identity_is_not_on_pallas
#assert_compiled the_identity_term_leaves_the_curve_and_pairs_cancel
#assert_compiled the_public_term_census
#assert_compiled only_identity_terms_were_dropped
#assert_compiled every_meaningful_public_term_is_on_pallas
#assert_compiled the_nominal_fold_also_agreed
#assert_compiled an_odd_identity_count_misses_the_golden
#assert_compiled the_filtered_fold_is_insensitive_to_an_appended_identity

#assert_compiled the_basis_is_the_squaring_orbit
#assert_compiled the_published_basis_is_six_distinct_values
#assert_compiled the_chain_publishes_two_hundred_and_fifty_six_felts
#assert_compiled the_pinned_blocks_tile_the_public_inputs
#assert_axioms ladderAir_pinsTied
end Dregg2.Circuit.Emit.MinaWrapCommitStages
