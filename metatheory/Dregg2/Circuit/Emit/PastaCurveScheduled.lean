/-
# `Dregg2.Circuit.Emit.PastaCurveScheduled` — the sound RCB complete addition ON THE ALLOCATED
LAYOUT: one op per row, 11 value slots, **481 declared columns instead of 3 048 — and
1 499 COMMITTED instead of 10 756, which is the width the cost law is linear in.**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index in this file is COMPUTED BY THE ALLOCATOR
(`AirColumnAlloc.allocate`), not written by hand and not written in Rust. The layout is
`slotOf`/`valueCol`, both derived from `allocate rcbScheduledRanges`; there is no hand-written
`VmConstraint2` anywhere here. House Law #1.

## ⚑ WHAT MOVED, AND IT IS NOT THE ARITHMETIC

`PastaCurveSound.swCompleteAddSoundLegs` asserts all 33 op blocks **on one row**, so
`AirColumnAlloc.rcb_single_row_interference_is_complete` says every live range is the whole row and
`all_interfering_forces_distinct_slots` says the allocation must therefore be injective: **3 048
columns is OPTIMAL for that schedule.** The reuse is created by the SCHEDULE, and this file is the
schedule.

* The 33 ops move to 33 rows (`rcbOpsScheduled`, a proved permutation of the gadget's order that
  respects the DAG — `rcbOpsScheduled_is_a_permutation`, `rcbOpsScheduled_topological`).
* Which op fires on which row is pinned by a **one-hot phase shift register**: 33 phase columns
  plus an idle state, `s₀ = 1` on the first row, `nxt(sᵢ₊₁) = loc(sᵢ)` on the transition. A witness
  selector with booleanity and a sum-to-one is not something the prover can turn off.
* Every op's gates are multiplied by their phase selector. Degree goes 2 → 3, which is FREE here:
  `circuit/src/descriptor_ir2.rs:8244` freezes the main-rail budget at 3 and `IR2_FRI_LOG_BLOWUP`
  (`:6939`) is the constant 6 — the blowup is not a function of degree, and
  `log2_ceil(3−1) = 1` leaves the quotient at 2 chunks exactly as before.
* The 39 value blocks land in **11** column-slots (`rcb_scheduled_alloc_width_is_eleven`), which is
  the peak-live floor, so no allocator can do better on this schedule.

## ⚑ THE RANGE POOLS ARE A SOUNDNESS CONSTRAINT, NOT TIDINESS

`Ir2Air::Main` hardcodes lookup multiplicity to `AB::Expr::ONE`
(`circuit/src/descriptor_ir2.rs:3738`, and `LookupSpec` at `:636` has no multiplicity field at
all), so **a declared range lookup fires on every row**. A physical column shared between an 8-bit
limb and a 16-bit carry would be queried against both tables at every row and would refuse the
honest witness. So the witness columns are pooled by range class — `w1`, `w8`, `w16` — and the
per-op `limbs` legs are replaced by **one pool leg per class, asserted on every row**.

⚑ That is STRICTLY STRONGER than what the one-row block asserted, not weaker: the one-row block
range-checked each op's witness once; this range-checks the whole pool on all 64 rows. The
hypotheses `felt_gates_force_congruence` / `addsub_gates_force_congruence` /
`smul_gates_force_congruence` take (`hx hy hz hq hc`, the byte-ranges that make `|body| < P`) are
therefore available at every op's own row. **No soundness is relaxed to reach the width.**

## ⚑ WHAT IS PROVED HERE, AND WHAT IS NOT — read this before quoting a number

* `pallasScheduledAir_mainRailOk` — the compiler accepts the block. Not a formality: a `limbs` leg
  at width ≥ 30 or an `.all` window reading `nxt` would emit `refuseConstraints` instead.
* `pallasScheduledDesc_certified` — `CertifiedRefines`, produced by `lowerTiedAir`. **Every leg of
  this source is forced by the emitted descriptor**, per-leg, in the source's own `AirLeg.forces`
  vocabulary. This is `EffectLowerCertified`'s existing machinery and it applies unchanged, which
  is the point of §1b of `AirColumnAlloc` (`renameAir_mainRailOk`).
* `pallasScheduledDesc_width` — the width, on the emitted object, and
  `scheduled_columns_fit` — every column the constraints address is inside it.
* `rcbSchedule_is_the_scheduled_dag` — the row order IS `rcbOpsScheduled`, which is itself a
  proved permutation of the gadget's order. A transcription slip here would be a different circuit
  that still emitted and still proved.

⚑⚑ **THE CROSS-ROW ASSIGNMENT RECONSTRUCTION IS PROVED — in `Emit.AirCrossRow`, not here.**
`PastaCurveSound.RcbSat.apply` chains the 33 op blocks over ONE assignment `a`, and on this layout
they live on 33 different rows. `AirCrossRow.rcbSat_of_rows` is the missing theorem: the carried
trace induces a single assignment (`gather`) on which the unscheduled block is satisfied, built
from the carry legs of §3d exactly as this paragraph predicted.
`AirCrossRow.scheduledRows_force_the_rcb_formula` composes it with
`PastaCurveSound.pallasCompleteAddSound_forces`, so **this layout forces the RCB formula at the
real Pallas-base prime**, and `vestaScheduledRows_force_the_rcb_formula` does the Vesta half.

⚠ **Two premises remain, and both are selector plumbing rather than row-crossing.**
`AirCrossRow.PhaseIndicator` (the phase register reads as the one-hot row indicator — §3c's legs
are what force it, and the step that needs an argument is booleanity + sum-to-one over a PRIME
field) and `AirCrossRow.RowsSat` (each row satisfies its own op's core gates — §3a's `gateBy`
legs, needing the `filter isGate` bookkeeping per kind). So this descriptor's status is: **shape,
per-leg refinement, AND end-to-end forcing, the last conditional on the selector reading
honestly.** It is still not emitted by name and no VK is rotated for it.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.AirColumnAlloc
import Dregg2.Circuit.Emit.PastaCurveSound

namespace Dregg2.Circuit.Emit.PastaCurveScheduled

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef WindowExpr mainTableDef)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB CB NG limbCols carryCols rangeTidW pLimb qLimb)
open Dregg2.Circuit.Emit.PastaAddSubSound (NA ACB CBITS acarryCols)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3)
open Dregg2.Circuit.Emit.PastaCurveSound (SoundCore mulCore addSubCore smulCore)
open Dregg2.Circuit.Emit.AirColumnAlloc

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §1 — ⚑ THE LAYOUT, COMPUTED BY THE ALLOCATOR.

Nothing below is a chosen constant except the pool ORDER, and that is chosen so each core's
`wB`/`wB+1`/`wB+SK` stride lands inside the right range class. -/

/-- The physical slot the allocator gave value `v`. -/
def slotOf (v : Nat) : Nat :=
  (((allocate rcbScheduledRanges).find? (fun p => p.1.val == v)).map Prod.snd).getD 0

/-- The 34 phase columns: `0 .. 32` are the ops, `33` is the idle state the power-of-two row count
needs (`prove_vm_descriptor2` REFUSES a non-power-of-two trace height —
`circuit/src/descriptor_ir2.rs:6987`). -/
def SEL (i : Nat) : Nat := i
/-- The idle phase. -/
def SEL_IDLE : Nat := 33
/-- Where the 11 value slots start. -/
def VAL_BASE : Nat := 34
/-- The column holding value `v`'s least-significant limb. -/
def valueCol (v : Nat) : Nat := VAL_BASE + SK * slotOf v

/-- The one-bit pool: an add/sub's carry/borrow bit. -/
def W1_COL : Nat := VAL_BASE + SK * 11
/-- The 8-bit witness pool: 32 columns, the widest single-op 8-bit witness (a multiply's quotient). -/
def W8_BASE : Nat := W1_COL + 1
/-- The 16-bit witness pool: 62 columns, the widest single-op 16-bit witness (a multiply's carries). -/
def W16_BASE : Nat := W8_BASE + 32

/-- ⚑ **THE SCHEDULED ROW'S WIDTH.** -/
def SCHED_W : Nat := W16_BASE + (NG - 1)

theorem sched_w_eq : SCHED_W = 481 := by decide +kernel

/-- Agreement with the width `AirColumnAlloc` derives from the pool sizes alone — two independent
routes to the same number, which is what makes it a pin rather than a restatement. -/
theorem sched_w_agrees_with_the_pool_arithmetic : SCHED_W = SCHED_WIDTH := by decide +kernel

/-! ### The three witness bases, one per op kind, each landing in its own range class.

* a MULTIPLY writes 32 quotient limbs at `wB` and 62 carries at `wB + SK`, so `wB = W8_BASE` and
  `W8_BASE + 32 = W16_BASE` — the pools are adjacent ON PURPOSE.
* an ADD/SUB writes its carry BIT at `wB` and 31 eight-bit carries at `wB + 1`, so `wB = W1_COL`.
* a CONSTANT MULTIPLY writes one byte quotient at `wB` and 31 SIXTEEN-bit carries at `wB + 1`, so
  `wB` is the LAST column of the 8-bit pool. -/
def MUL_WIT : Nat := W8_BASE
def ADDSUB_WIT : Nat := W1_COL
def SMUL_WIT : Nat := W8_BASE + 31

theorem witness_bases_land_in_their_pools :
    MUL_WIT = W8_BASE ∧ MUL_WIT + SK = W16_BASE ∧ ADDSUB_WIT + 1 = W8_BASE
      ∧ SMUL_WIT + 1 = W16_BASE := by
  refine ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §2 — ⚑ THE SCHEDULE, as data. Kind, destination, two operands. -/

/-- The four op kinds of RCB Algorithm 7. -/
inductive OpKind where
  | mul | add | sub | smul
  deriving Repr, DecidableEq

/-- ⚑ **THE 33 OPS IN ROW ORDER** — `rcbOpsScheduled`'s order, with the kind each `++` line of
`PastaCurveSound.swCompleteAddSoundLegs` used. -/
def rcbSchedule : List (OpKind × Nat × Nat × Nat) :=
  [ (.add,  V 3,  0,     1)
  , (.add,  V 4,  3,     4)
  , (.mul,  V 5,  V 3,   V 4)
  , (.mul,  V 0,  0,     3)
  , (.mul,  V 1,  1,     4)
  , (.add,  V 6,  V 0,   V 1)
  , (.sub,  V 7,  V 5,   V 6)
  , (.mul,  V 2,  2,     5)
  , (.add,  V 8,  1,     2)
  , (.add,  V 9,  4,     5)
  , (.mul,  V 10, V 8,   V 9)
  , (.add,  V 11, V 1,   V 2)
  , (.sub,  V 12, V 10,  V 11)
  , (.add,  V 13, 0,     2)
  , (.add,  V 14, 3,     5)
  , (.mul,  V 15, V 13,  V 14)
  , (.add,  V 16, V 0,   V 2)
  , (.sub,  V 17, V 15,  V 16)
  , (.add,  V 18, V 0,   V 0)
  , (.add,  V 19, V 18,  V 0)
  , (.smul, V 20, V 2,   V 2)
  , (.add,  V 21, V 1,   V 20)
  , (.sub,  V 22, V 1,   V 20)
  , (.smul, V 23, V 17,  V 17)
  , (.mul,  V 24, V 12,  V 23)
  , (.mul,  V 25, V 7,   V 22)
  , (.sub,  V 26, V 25,  V 24)
  , (.mul,  V 27, V 23,  V 19)
  , (.mul,  V 28, V 22,  V 21)
  , (.add,  V 29, V 28,  V 27)
  , (.mul,  V 30, V 19,  V 7)
  , (.mul,  V 31, V 21,  V 12)
  , (.add,  V 32, V 31,  V 30) ]

theorem rcbSchedule_length : rcbSchedule.length = 33 := by decide +kernel

/-- ⚑ **THE SCHEDULE IS THE DAG.** Kind-erasing `rcbSchedule` gives back `rcbOpsScheduled` exactly
— same destinations, same operands, same order. A transcription slip here would be a DIFFERENT
CIRCUIT that still emitted and still proved, so it is pinned rather than trusted. -/
theorem rcbSchedule_is_the_scheduled_dag :
    rcbSchedule.map (fun t => (⟨t.2.1, [t.2.2.1, t.2.2.2]⟩ : SsaOp))
      = rcbOpsScheduled.map (fun o => (⟨o.dst, [o.srcs.headD 0, o.srcs.getD 1 0]⟩ : SsaOp)) := by
  decide +kernel

/-- The op-kind census: 12 multiplies, 14 adds, 5 subtractions, 2 constant multiplies — the
gadget's own `12 mul + 2 smul + 14 add + 5 sub`. -/
theorem rcbSchedule_kind_census :
    (rcbSchedule.filter (fun t => t.1 == OpKind.mul)).length = 12
    ∧ (rcbSchedule.filter (fun t => t.1 == OpKind.add)).length = 14
    ∧ (rcbSchedule.filter (fun t => t.1 == OpKind.sub)).length = 5
    ∧ (rcbSchedule.filter (fun t => t.1 == OpKind.smul)).length = 2 := by decide +kernel

/-! ## §3 — ⚑ THE LEGS. -/

/-- Multiply a row-local gate body by its phase selector. Everything else passes through — after
§3a's filter there is nothing else, but the total function is what makes the census below
meaningful. -/
def gateBy (sel : Nat) : AirLeg → AirLeg
  | .gate c => .gate ⟨.mul (.var sel) c.lhs, c.rhs⟩
  | l       => l

/-- Is this leg an algebraic gate? (`§3a`: the cores' `limbs` legs are replaced by pool legs.) -/
def isGate : AirLeg → Bool
  | .gate _ => true
  | _       => false

/-- The core for an op kind, at the given modulus limb function. -/
def coreOf (pl : Nat → ℤ) : OpKind → SoundCore
  | .mul  => mulCore pl
  | .add  => addSubCore pl 1 (-1)
  | .sub  => addSubCore pl (-1) 1
  | .smul => smulCore pl (curveB3 : ℤ)

/-- Where the op kind's private witness lives. -/
def witOf : OpKind → Nat
  | .mul  => MUL_WIT
  | .add  => ADDSUB_WIT
  | .sub  => ADDSUB_WIT
  | .smul => SMUL_WIT

/-- ⚑ **ONE OP'S LEGS, ON ITS OWN ROW.** The core's algebraic gates, relocated to the allocated
columns and gated by the phase selector. The core's `limbs` legs are dropped here and reappear in
§3b as pool legs asserted on EVERY row — strictly more range checking, not less. -/
def opLegs (pl : Nat → ℤ) (i : Nat) (t : OpKind × Nat × Nat × Nat) : List AirLeg :=
  (((coreOf pl t.1).legs (valueCol t.2.2.1) (valueCol t.2.2.2) (valueCol t.2.1)
      (witOf t.1)).filter isGate).map (gateBy (SEL i))

/-- All 33 ops' legs. -/
def scheduleLegs (pl : Nat → ℤ) : List AirLeg :=
  (List.range rcbSchedule.length).flatMap
    (fun i => match rcbSchedule[i]? with | some t => opLegs pl i t | none => [])

/-! ### §3b — the range pools, asserted on every row. -/

/-- One `limbs` leg per value slot: 32 byte limbs, the `w8` table. Every value the row ever holds
is a 32-limb byte decomposition, so this is exactly the `Ranged` hypothesis the forcing lemmas
take, available at every row rather than at one. -/
def valuePoolLegs : List AirLeg :=
  (List.range 11).map (fun k => AirLeg.limbs ⟨limbCols (VAL_BASE + SK * k), SB, rangeTidW SB⟩)

/-- The three witness pools. -/
def witnessPoolLegs : List AirLeg :=
  [ AirLeg.limbs ⟨[W1_COL], CBITS, rangeTidW CBITS⟩
  , AirLeg.limbs ⟨(List.range 32).map (W8_BASE + ·), SB, rangeTidW SB⟩
  , AirLeg.limbs ⟨(List.range (NG - 1)).map (W16_BASE + ·), CB, rangeTidW CB⟩ ]

/-! ### §3c — ⚑ THE PHASE SHIFT REGISTER.

33 one-hot phase columns plus an idle state. `.window` and not `.gate` throughout, because
`AirLeg.forces` on a `gate` is `isLast = false → …`: the schedule discipline has to bind on the
LAST row too, or a prover picks that row's phase freely. -/

/-- Sum of a column list, as a window body. -/
def sumLoc : List Nat → WindowExpr
  | []      => .const 0
  | c :: cs => .add (.loc c) (sumLoc cs)

/-- `s(s−1) = 0` on every row, for each of the 34 phase columns. -/
def selBooleanLegs : List AirLeg :=
  (List.range 34).map (fun i =>
    AirLeg.window ⟨.all, .mul (.loc (SEL i)) (.add (.loc (SEL i)) (.const (-1)))⟩)

/-- ⚑ **EXACTLY ONE PHASE IS LIVE ON EVERY ROW.** With booleanity this is one-hot, and it is what
stops a prover turning every gate off by zeroing the selectors. -/
def selOneHotLeg : AirLeg :=
  AirLeg.window ⟨.all, .add (sumLoc (List.range 34)) (.const (-1))⟩

/-- The register: phase 0 on the first row; `nxt(sᵢ₊₁) = loc(sᵢ)`; phase 0 never returns; and the
idle state absorbs everything after phase 32. -/
def selShiftLegs : List AirLeg :=
  AirLeg.window ⟨.first, .add (.loc (SEL 0)) (.const (-1))⟩
  :: AirLeg.window ⟨.transition, .nxt (SEL 0)⟩
  :: AirLeg.window ⟨.transition,
        .add (.nxt SEL_IDLE) (.mul (.const (-1)) (.add (.loc (SEL 32)) (.loc SEL_IDLE)))⟩
  :: (List.range 32).map (fun i =>
        AirLeg.window ⟨.transition, .add (.nxt (SEL (i + 1))) (.mul (.const (-1)) (.loc (SEL i)))⟩)

/-! ### §3d — ⚑ THE CARRY LEGS: what makes a live range mean anything.

A value allocated to slot `k` must survive from its definition row to its last-use row, so the
column carries whenever some value in that slot spans the transition. The mask is the SUM of the
phase selectors of the spanning rows — degree 1, so the carry gate is degree 2.

⚑ **This is where the disjointness invariant is cashed.** Because `alloc_disjoint` guarantees two
values in one slot never overlap, the phase sets of the values sharing slot `k` are disjoint, and
the mask is a sum of distinct one-hot columns — it is never `2`. A mask that could reach `2` would
be a slot carrying two different values across the same transition, which is exactly the bug the
invariant rules out. -/

/-- The transitions across which slot `k` must hold its value: `lo ≤ t < hi` for some range the
allocator put there. -/
def carryPhases (k : Nat) : List Nat :=
  (List.range 33).filter (fun t =>
    (allocate rcbScheduledRanges).any (fun p => p.2 == k && p.1.lo ≤ t && t < p.1.hi))

/-- Slot `k`'s carry mask. -/
def carryMask (k : Nat) : WindowExpr := sumLoc ((carryPhases k).map SEL)

/-- ⚑ The 352 carry legs: `mask · (nxt c − loc c) = 0` on the transition, one per value column. -/
def carryLegs : List AirLeg :=
  (List.range 11).flatMap (fun k =>
    (List.range SK).map (fun j =>
      AirLeg.window ⟨.transition,
        .mul (carryMask k)
          (.add (.nxt (VAL_BASE + SK * k + j))
                (.mul (.const (-1)) (.loc (VAL_BASE + SK * k + j))))⟩))

/-! ## §4 — the AIRs and the emitted descriptors. -/

/-- The three range tables — the SAME union `PastaCurveSound.rcbTables` declares, at the new width.
No fourth width was invented to make the layout fit. -/
def schedTables : List TableDef :=
  [ mainTableDef SCHED_W
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- ⚑ **THE SCHEDULED SOUND PALLAS COMPLETE ADDITION.** -/
def pallasScheduledAir : EffectAir :=
  { tables := schedTables
  , legs := selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs ++ valuePoolLegs
              ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs pLimb }

/-- …and the Vesta twin, because the accumulator leg is Step/Tick on Vesta. -/
def vestaScheduledAir : EffectAir :=
  { tables := schedTables
  , legs := selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs ++ valuePoolLegs
              ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs qLimb }

/-- ⚑ **THE COMPILER ACCEPTS THE ALLOCATED BLOCK.** Every leg has a deployed main-rail image —
which for the `limbs` legs is the `0 < bits ≤ 29` verdict, and for the `.all` windows is that they
do not read `nxt`. A selector gate scoped `.all` that read the next row would emit
`refuseConstraints` and this would be false. -/
theorem pallasScheduledAir_mainRailOk : pallasScheduledAir.mainRailOk = true := by decide +kernel

theorem vestaScheduledAir_mainRailOk : vestaScheduledAir.mainRailOk = true := by decide +kernel

/-- ⚑ **THE TIE VERDICT, NAMED RATHER THAN RE-DERIVED.** This block publishes no PI at all, so
every leg lands in the non-`pin` arm of `EffectAir.pinsTied`. The `TiedAir` fields below are
`autoParam`s defaulting to `by decide`; a blank field decides the same block a second time inside
the elaborator's `whnf`, which is what these two theorems exist to stop. -/
theorem pallasScheduledAir_pinsTied : pallasScheduledAir.pinsTied = true := by decide +kernel

theorem vestaScheduledAir_pinsTied : vestaScheduledAir.pinsTied = true := by decide +kernel

/-- ⚑ **THE TIED SOURCE.** Same `TiedAir` discipline as the one-row block: a decorative pin is
unrepresentable. (This block publishes no PI at all, so `pinsTied` is vacuously true — recorded
here rather than left implicit.) -/
def pallasScheduledTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := pallasScheduledAir
  ok   := pallasScheduledAir_mainRailOk
  tied := pallasScheduledAir_pinsTied

def pallasScheduledDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-scheduled::v1" SCHED_W 0 [] pallasScheduledTiedAir).val

/-- ⚑ **THE CERTIFICATE, PRODUCED BY THE EMIT** — and it needed no new lowering. `renameAir` moved
the columns; `AirColumnAlloc.renameAir_mainRailOk` says the compiler's verdict did not move; so
`lowerTiedAir` hands back `CertifiedRefines` for this block by the same machinery it hands it back
for the 3 048-column one. Every leg of this source is FORCED by the emitted constraints. -/
theorem pallasScheduledDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines pallasScheduledDesc [] pallasScheduledAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-pallas-complete-add-scheduled::v1" SCHED_W 0 [] pallasScheduledTiedAir).property

def vestaScheduledTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := vestaScheduledAir
  ok   := vestaScheduledAir_mainRailOk
  tied := vestaScheduledAir_pinsTied

def vestaScheduledDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-scheduled::v1" SCHED_W 0 [] vestaScheduledTiedAir).val

theorem vestaScheduledDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines vestaScheduledDesc [] vestaScheduledAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-vesta-complete-add-scheduled::v1" SCHED_W 0 [] vestaScheduledTiedAir).property

/-! ## §5 — ⚑ THE MEASUREMENT, ON THE EMITTED OBJECTS. -/

/-- ⚑⚑ **481 COLUMNS**, against `PastaCurveSound.pallasCompleteAddSoundDesc_width`'s **3 048**. -/
theorem pallasScheduledDesc_width : pallasScheduledDesc.traceWidth = 481 := rfl
theorem vestaScheduledDesc_width : vestaScheduledDesc.traceWidth = 481 := rfl

/-! One kernel check per leg family, and the 33 scheduled ops in slices of three, so no single declaration walks
all 1 864 legs: the single `decide` over the whole list was 7.7 GB of this module's 11.7 GB peak. -/
theorem scheduled_columns_fit_sel_boolean :
    (selBooleanLegs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_sel_one_hot :
    ([selOneHotLeg].all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_sel_shift :
    (selShiftLegs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_value_pool :
    (valuePoolLegs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_witness_pool :
    (witnessPoolLegs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_carry :
    (carryLegs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_0 :
    (((List.range' 0 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_3 :
    (((List.range' 3 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_6 :
    (((List.range' 6 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_9 :
    (((List.range' 9 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_12 :
    (((List.range' 12 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_15 :
    (((List.range' 15 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_18 :
    (((List.range' 18 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_21 :
    (((List.range' 21 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_24 :
    (((List.range' 24 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_27 :
    (((List.range' 27 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_ops_30 :
    (((List.range' 30 3).flatMap
      (fun i => match rcbSchedule[i]? with | some t => opLegs pLimb i t | none => [])).all
      (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by decide +kernel
theorem scheduled_columns_fit_schedule :
    ((scheduleLegs pLimb).all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by
  have hr : List.range rcbSchedule.length
      = List.range' 0 3 ++ List.range' 3 3 ++ List.range' 6 3 ++ List.range' 9 3
        ++ List.range' 12 3 ++ List.range' 15 3 ++ List.range' 18 3 ++ List.range' 21 3
        ++ List.range' 24 3 ++ List.range' 27 3 ++ List.range' 30 3 := by
    decide +kernel
  unfold scheduleLegs
  rw [hr]
  simp only [List.flatMap_append, List.all_append,
    scheduled_columns_fit_ops_0, scheduled_columns_fit_ops_3, scheduled_columns_fit_ops_6,
    scheduled_columns_fit_ops_9, scheduled_columns_fit_ops_12, scheduled_columns_fit_ops_15,
    scheduled_columns_fit_ops_18, scheduled_columns_fit_ops_21, scheduled_columns_fit_ops_24,
    scheduled_columns_fit_ops_27, scheduled_columns_fit_ops_30,
    Bool.and_self]

/-- Every column the emitted constraints address is inside the declared width — the check
`circuit/src/descriptor_ir2.rs:2171` performs, done on the source side so a layout slip is a Lean
error and not a prover refusal. -/
theorem scheduled_columns_fit :
    (pallasScheduledAir.legs.all (fun l => l.readCols.all (fun c => c < SCHED_W))) = true := by
  show (selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs ++ valuePoolLegs ++ witnessPoolLegs
      ++ carryLegs ++ scheduleLegs pLimb).all (fun l => l.readCols.all (fun c => c < SCHED_W)) = true
  simp only [List.all_append, scheduled_columns_fit_sel_boolean, scheduled_columns_fit_sel_one_hot,
    scheduled_columns_fit_sel_shift, scheduled_columns_fit_value_pool,
    scheduled_columns_fit_witness_pool, scheduled_columns_fit_carry, scheduled_columns_fit_schedule,
    Bool.and_self]

/-- ⚑⚑ **2 297 CONSTRAINTS**, against `PastaCurveSound.pallasCompleteAddSoundDesc_constraint_count`'s
**4 476** — and the reason it went DOWN rather than up is that one op per row means the per-op range
lookups become per-POOL range lookups: 3 048 lookups collapse to 447. -/
theorem pallasScheduledDesc_constraint_count : pallasScheduledDesc.constraints.length = 2297 := by decide +kernel
theorem vestaScheduledDesc_constraint_count : vestaScheduledDesc.constraints.length = 2297 := by decide +kernel

/-- The census, so a dropped block moves a number: 34 booleanity + 1 one-hot + 35 shift-register
+ 352 value-pool lookups + 95 witness-pool lookups + 352 carry gates + 1 428 op gates. -/
theorem scheduled_constraint_census :
    34 + 1 + 35 + 352 + 95 + 352 + 1428 = pallasScheduledDesc.constraints.length := by decide +kernel

/-- ⚑ **THE 1 428 ALGEBRAIC GATES ARE THE SAME ONES.** 12 multiplies at 63 coefficient gates,
14 adds and 5 subtractions at 32, 2 constant multiplies at 32 — the identical algebra
`PastaCurveSound` emits, moved to rows and multiplied by a selector. The arithmetic did not change;
only where it is asserted did. -/
theorem scheduled_gate_count_is_the_sound_algebra :
    12 * 63 + 14 * 32 + 5 * 32 + 2 * 32 = 1428 := by decide +kernel

/-- ⚑ **THE RANGE-LOOKUP COUNT**, which is where the constraint saving is: the one-row block
declares one `limbs` leg per op per operand block (3 048 lookups); this declares one per POOL,
fired on every row (447). Strictly more coverage per column, far fewer declarations. -/
theorem pallasScheduledAir_range_lookups : pallasScheduledAir.totalRangeLookups = 447 := by decide +kernel

/-- The leg count, for the same reason a constraint count is pinned. -/
theorem pallasScheduledAir_leg_count : pallasScheduledAir.legs.length = 1864 := by decide +kernel

/-! ### §5a — the comparison, stated rather than described. -/

/-- ⚑⚑ **THE HEADLINE: 3 048 → 481 COLUMNS (6.34×), 4 476 → 2 297 CONSTRAINTS (1.95×).**
The column factor is stated as `× 6` because that is the largest integer it clears; the constraint
factor is stated as a bare `<` because `× 2` is FALSE (`2 297 · 2 = 4 594 > 4 476`) and rounding it
up to the flattering figure is how a 1.95 becomes a "2×". -/
theorem the_scheduled_row_is_narrower_and_shorter :
    pallasScheduledDesc.traceWidth * 6 < Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundDesc.traceWidth
    ∧ pallasScheduledDesc.constraints.length
        < Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundDesc.constraints.length := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The two widths, side by side, on the two EMITTED objects. -/
theorem the_two_widths :
    Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundDesc.traceWidth = 3048
    ∧ pallasScheduledDesc.traceWidth = 481 := ⟨rfl, rfl⟩

/-! ### §5b — ⚑⚑ THE WIDTH THE PROVER COMMITS, WHICH IS THE ONE THE COST LAW IS LINEAR IN.

`traceWidth` is not what `Ir2Air::Main` is `width()`d at: `MainLayout::build`
(`circuit/src/descriptor_ir2.rs:1919`) adds a nibble aux block per declared range lookup. Measured
by `circuit-prove/tests/mina_accumulator_leaf_anatomy.rs::the_wrap_cost_tracks_committed_width_not_declared_width`,
`ops/committed` spreads 1.12× across two shapes where `ops/declared` spreads 1.78× — **so the cost
is linear in committed width and a declared-width ratio over-promises.** -/

/-- ⚑⚑ **THE DEPLOYED ROW COMMITS 10 756 COLUMNS, NOT 3 048** — and this is the cross-check that
makes the model a pin rather than a restatement: `AirColumnAlloc.decompCols` is transcribed from
`descriptor_ir2.rs:1876-1883` and applied to the LEAN source, while the sibling's
`committed_width` reads the EMITTED descriptor's tables in Rust. **Two independent routes, same
number.** (The naive `⌈bits/4⌉` model gives 10 737: the 19-column gap is the partial-top term
making each one-bit add/sub carry cost 2 aux columns, not 1.) -/
theorem the_sound_row_commits_10756 :
    committedWidth Dregg2.Circuit.Emit.PastaCurveSound.RCB_WIDTH
      Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir = 10756 := by decide +kernel

/-- ⚑⚑ **AND THE SCHEDULED ROW COMMITS 1 499.** -/
theorem the_scheduled_row_commits_1499 :
    committedWidth SCHED_W pallasScheduledAir = 1499 := by decide +kernel

/-- ⚑ **7.17× IN THE WIDTH THAT COSTS** — better than the declared-width ratio of 6.34×, because
one op per row is what lets the 3 048 per-op range lookups become 447 per-pool ones, and the aux
block scales with lookups. **The range-decomposition block, not the SSA scratch, is the bigger
half of this win**: 7 708 → 1 018 aux columns, against 2 567 declared columns recovered. -/
theorem the_committed_width_ratio_clears_seven :
    committedWidth SCHED_W pallasScheduledAir * 7
      < committedWidth Dregg2.Circuit.Emit.PastaCurveSound.RCB_WIDTH
          Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir := by decide +kernel

/-- The two aux blocks, so the claim above is checkable rather than asserted. -/
theorem the_two_aux_blocks :
    airAuxCols Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir = 7708
    ∧ airAuxCols pallasScheduledAir = 1018 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- ⚠ **AND THE RANGE BLOCK IS STILL THE MAJORITY OF WHAT IS COMMITTED** — 67.9% here against
71.7% there. Register allocation does not touch it; `LIMB_BITS` does. Recorded so this cone's win
is not credited for a radix change it did not make. -/
theorem the_aux_block_is_still_the_majority :
    2 * airAuxCols pallasScheduledAir > committedWidth SCHED_W pallasScheduledAir := by decide +kernel

#assert_axioms the_sound_row_commits_10756
#assert_axioms the_scheduled_row_commits_1499
#assert_axioms the_committed_width_ratio_clears_seven
#assert_axioms the_two_aux_blocks
#assert_axioms pallasScheduledAir_mainRailOk
#assert_axioms vestaScheduledAir_mainRailOk
#assert_axioms pallasScheduledDesc_certified
#assert_axioms vestaScheduledDesc_certified
#assert_axioms pallasScheduledDesc_width
#assert_axioms pallasScheduledDesc_constraint_count
#assert_axioms scheduled_columns_fit
#assert_axioms rcbSchedule_is_the_scheduled_dag
#assert_axioms rcbSchedule_kind_census
#assert_axioms the_two_widths
#assert_axioms the_scheduled_row_is_narrower_and_shorter

end Dregg2.Circuit.Emit.PastaCurveScheduled
