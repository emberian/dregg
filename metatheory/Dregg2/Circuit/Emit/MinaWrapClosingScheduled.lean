/-
# `Dregg2.Circuit.Emit.MinaWrapClosingScheduled` — ⚑⚑ THE IPA CLOSING CHECK ON THE SCHEDULED ROW:
**10 799 → 1 500 COMMITTED COLUMNS.**

## ⚑ SAY THE SUBSTRATE OUT LOUD (HOUSE LAW #1, at constraint #1)

**This is Lean-authored AIR.** Every value column here is COMPUTED BY THE ALLOCATOR
(`AirColumnAlloc.allocate` through `PastaCurveScheduled.valueCol`), not written by hand and not
written in Rust. The only hand-chosen index in the file is `GO`, one column past the scheduled
block, and it is `SCHED_W` rather than a literal.

## ⚑ WHAT WAS BLOCKING THIS, IN ITS AUTHOR'S OWN WORDS

`MinaWrapClosingAir` rides `PastaCurveSound`'s 3 048-column row, one complete-add per row. Putting
it on `PastaCurveScheduled`'s 481-column row was named as blocked precisely:

> the scheduled layout is one op per row behind a **33-phase shift register**, so a chain needs a
> **phase-gated carry** plus a re-run of `AirCrossRow`'s composition.

Both are here. §2 is the phase-gated carry; §5 composes `AirSelectorForcing`'s per-block forcing.

## ⚑⚑ THE THREE THINGS THE REGISTER HAD TO LEARN, AND WHY EACH IS FORCED

`PastaCurveScheduled.selShiftLegs` is a **one-shot** register: `nxt(s₀) = 0` on every transition, so
phase 0 never returns and the block runs exactly once. A chain needs it to cycle. Three changes,
and only three:

1. **`nxt(s₀) = loc(s₃₂)·loc(GO)`** — phase 0 returns after phase 32 exactly when the chain
   continues. `GO` is one boolean column. ⚑ Degree 2, so the main-rail budget of 3 is untouched:
   the op gates are already the degree-3 term and nothing here reaches past them.
2. **`nxt(s₃₃) = loc(s₃₃) + loc(s₃₂)·(1 − loc(GO))`** — the idle phase absorbs when the chain
   stops. ⚑ **The idle state is absorbing on its own**, with no monotonicity leg on `GO`: at an idle
   row `loc(s₃₂) = 0`, so `nxt(s₀) = 0` and `nxt(s₃₃) = loc(s₃₃)` whatever `GO` does. A `GO` that
   came back up could not restart the register, so no leg is spent forbidding it.
3. ⚑⚑ **`.last`: `s₃₃ = 1` — THE LAST ROW IS IDLE.** This is not tidiness and it is the seam the
   one-row file names: *"an off-by-one silently drops the final addend."* Without it a prover picks
   a height whose last row is phase 32, the block's OUTPUT has not been threaded into the
   accumulator yet, and the discharge reads the accumulator ENTERING the last block — so the last
   addend is silently dropped and every count still passes. With it, `GO` must have fallen at a
   phase-32 row, a whole number of blocks ran, and the final block's output IS in the accumulator.

⚠ `prove_vm_descriptor2` refuses a non-power-of-two trace height (`descriptor_ir2.rs:7102`, read at
source), and no power of two is a multiple of 33 (`33 = 3·11`, coprime to 2). So an idle tail is
not optional and a purely cyclic 33-register could never close. That is *why* `GO` exists.

## ⚑⚑ THE CARRY LEGS DID NOT HAVE TO CHANGE, AND THAT IS THE MEASUREMENT

`PastaCurveScheduled.carryLegs` masks each slot by `Σ_{t ∈ carryPhases k} SEL t`. Under the cyclic
register `SEL t` reads `1` at every row `≡ t (mod 33)`, so **the same 352 legs hold every slot
across exactly the transitions inside every block's live ranges** — one authored block, N blocks of
force. And `no_slot_carries_across_the_block_boundary` is the fact that makes the handover legal:
**32 is in no slot's `carryPhases`** (the maximum is 31), so at the phase-32 transition no value
column is held and the thread is free to write. A single slot that carried across `t = 32` would
fight the thread and refuse the honest witness.

## ⚑⚑ WHERE THE ACCUMULATOR LIVES — the choice that costs zero columns

The accumulator is threaded into **the input slots the allocator already gave value ids 0/1/2**, not
into a fresh register. `the_scheduled_roles_are_the_allocators_columns` reads them off `valueCol`.
So the chain state costs **no new columns at all**, and the idle tail holds those three blocks
(`idleHoldLegs`) while everything else goes quiet.

⚠ **`OUT_X` AND THE ADDEND'S `X` SHARE A SLOT** — `valueCol (V 26) = valueCol 3 = 290`, because the
allocator reused slot 8 after the addend's last use at row 14. That is legal *inside* a block and it
is exactly the kind of coincidence that would be a silent aliasing bug across the boundary, so it is
pinned rather than trusted: the thread READS 290 at phase 32 (where slot 8 holds `V 26`) and the
next block's addend WRITES it at phases 0-14, and no carry leg spans the gap.

## ⚑ WHAT THIS COSTS — measured on the EMITTED descriptors, in §4

| | declared | committed | constraints |
|---|---|---|---|
| `pallasCompleteAddSoundAir` — the row all three closing descriptors ride | 3 048 | **10 756** | 4 476 |
| `dregg-mina-wrap-closing-final::v1` | 3 048 | 10 756 | 4 828 |
| `dregg-mina-wrap-closing-fs::v1` | 3 091 | 10 799 | 4 961 |
| `dregg-mina-wrap-closing-scheduled-final::v1` | **482** | **1 500** | **2 747** |

⚑ **THE THEOREMS COMPARE AGAINST THE ROW, NOT AGAINST THE CHAIN WRAPPER, AND THAT IS THE RIGHT
OBJECT.** `closingSegAir`/`closingFinalAir`/`closingFsAirOn` add threads, pins, a discharge and a
transcript weld — **none of which declares a range lookup**, so all three commit
`pallasCompleteAddSoundAir`'s 7 708 aux columns and differ only in DECLARED width (+0, +0, +43). A
width claim keyed to the wrapper would move when a pin moved; keyed to the row it does not. The two
wrapper rows above are measured, not theorems of this file.

⚠ **AND THE TRADE, BOTH HALVES, BECAUSE ONE HALF IS A LIE.** A complete addition costs **1 row**
on the deployed row and **33 rows** here. So per addition:

* **committed CELLS go UP** — `1 × 10 756 = 10 756` against `33 × 1 500 = 49 500`, a factor of
  **4.60× MORE** work for the LEAF prover (`the_leaf_prover_pays_more_per_addition`);
* **the WRAP's per-query column work goes DOWN 7.17×**, because an in-circuit FRI verifier opens
  `Q · W` committed cells per round and `W` is the committed WIDTH;
* **the Merkle path grows by `log₂ 33 = 6` bits per block**, so the wrap pays `Q · 6` extra
  compressions per commitment round.

Quoting only the 7.17× is the flattering half of a pair. The honest sentence is: **this moves work
from the wrap into the leaf**, and it is worth it only because the wrap is the expensive one — the
verification circuit is ~10³ times larger than the descriptor it verifies.

⚠ **RE-DERIVE THE LDE, DO NOT INHERIT IT.** Since the FRI split
(`recursion-verify/src/config.rs:571`, `recursion_layer_over`) a layer VERIFIES at its child's mint
knobs and MINTS at `RECURSION_FRI_LOG_BLOWUP = 3`. The child descriptor proof is still minted at
`IR2_INNER_LOG_BLOWUP = 6`, so `log₂|D⁰|` of the object the wrap OPENS is `log₂(height) + 6` —
6 → 12 for a single block, and `log₂(64N) + 6` for a chain of `N` blocks against `log₂(N) + 6` on
the deployed row. The wrap's OWN LDE is at blowup 3, not 6. ⚠ Any figure computed from a named
config constant instead of `recursion_layer_over(child)` is measuring a config the tower no longer
runs.

## ⚠ WHAT IS PROVED HERE AND WHAT IS NOT — read this before quoting a number

* `closingSchedFinalAir_mainRailOk` / `_pinsTied` — the compiler accepts the block and no pin is
  decorative. Not a formality: a `.all` window reading `nxt`, or a `limbs` leg at width ≥ 30, emits
  `refuseConstraints` instead.
* `closingSchedFinalDesc_certified` — `CertifiedRefines`, per-leg, in the source's own
  `AirLeg.forces` vocabulary.
* `closingSchedFinalDesc_width` / `_committed` / `_constraint_count` and the censuses — on the
  EMITTED objects.
* `no_slot_carries_across_the_block_boundary`, `chain_phase_zero_returns` against
  `the_one_shot_register_kills_phase_zero`, and `chain_last_row_is_idle` — the three facts the
  design turns on, stated as what the legs FORCE rather than as syntactic pins.
* `oneBlockRows_force_the_rcb_formula` — **one block's** rows force the RCB formula, composed from
  `AirSelectorForcing`. ⚠ It is stated for the FIRST block (rows 0-32), where the phase register's
  reading is `AirCrossRow.PhaseIndicator` unchanged.

⚠⚠ **WHAT IS NOT PROVED, NAMED AS UNDONE WORK RATHER THAN WORN AS A CAVEAT.** The CHAIN-level
forcing — `closing_discharge_forced`'s analogue, "`N` blocks plus the discharge force the `N`-fold
RCB chain to be the point at infinity" — is **not here.** It needs `PhaseIndicator` generalised from
`[i = t]` to `[i = t mod 33]` under `GO`, which is the same induction as
`AirSelectorForcing.phaseIndicator_of_selectorLegs` with a second case at the boundary, and then
`AirCrossRow`'s `gather` re-based per block. That is ordinary work of a known shape; it is not a
theorem of the model and it is not small. **Until it lands, this file is a WIDTH and SHAPE result
plus per-block forcing — quote it that way and do not say the scheduled closing check is forced.**

⚠ **P10, the opening-soundness floor, is untouched**, as in the one-row file: that a prover which
passes the closing check must KNOW an opening is the IPA/dlog extraction argument, undischarged here
and everywhere in this stack.

⚠ **Which object.** Everything is about the HAND schedule `AirColumnAlloc.rcbOpsScheduled` through
`PastaCurveScheduled.rcbSchedule` — the emitted one. **NOT** `AirSchedule.rcbOpsOptimal`, whose
1 307 committed columns are a width result no forcing theorem mentions; re-pointing at it moves
`carryPhases`, `loOf`/`hiOf` and every `by decide` in this file.

## Axiom hygiene

General theorems `#assert_axioms`-clean; facts about concrete data `native_decide`, pinned
`#assert_compiled` (since 2026-11-06); no `sorry`/`admit`; zero `#guard`s. NEW file, imports
read-only; NOT imported by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapClosingScheduled`
-/
import Dregg2.Circuit.Emit.AirSelectorForcing
import Dregg2.Circuit.Emit.MinaAccumulatorAir

namespace Dregg2.Circuit.Emit.MinaWrapClosingScheduled

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TraceFamily WindowExpr mainTableDef)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB CB rangeTidW pLimb qLimb)
open Dregg2.Circuit.Emit.PastaAddSubSound (CBITS)
open Dregg2.Circuit.Emit.AirColumnAlloc (V committedWidth airAuxCols)
open Dregg2.Circuit.Emit.PastaCurveScheduled
  (SEL SEL_IDLE SCHED_W valueCol carryPhases selBooleanLegs selOneHotLeg sumLoc
   valuePoolLegs witnessPoolLegs carryLegs scheduleLegs)
open Dregg2.Circuit.Emit.MinaAccumulatorAir (ACC_IN_PI ACC_OUT_PI ACC_PI_COUNT)
open Dregg2.Circuit.Emit.AirCrossRow
  (RowTrace rowEnv PhaseIndicator PoolsRanged SlotsCarry gather sumLoc_eval
   slotsCarry_of_carryLegs scheduledRows_force_the_rcb_formula)
open Dregg2.Circuit.Emit.AirSelectorForcing
  (LegsHold phaseIndicator_of_phaseFacts rowsSat_of_scheduleLegs)
open Dregg2.Circuit.Emit.PastaFieldSound (sVal)
open Dregg2.Circuit.Emit.PastaCurveSound (IN_BASE vBase)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbTraceZ)
open Dregg2.Circuit.Emit.PastaCurve (CZp)

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §1 — ⚑ THE COLUMN ROLES, READ OFF THE ALLOCATOR.

Nothing below is a chosen index except `GO`, and that is `SCHED_W` — the first column past the
scheduled block — rather than a literal. -/

/-- ⚑ **THE CHAIN FLAG**: `1` on a phase-32 row means another block follows. One column. -/
def GO : Nat := SCHED_W

/-- ⚑ **THE CHAINED SCHEDULED ROW'S WIDTH** — the block, plus one bit. -/
def CHAIN_W : Nat := SCHED_W + 1

theorem chain_w_eq : CHAIN_W = 482 ∧ GO = 481 := by refine ⟨by native_decide, by native_decide⟩

/-- The accumulator's X block — value id `0`, at whatever column the allocator gave it. -/
def ACC_XS : Nat := valueCol 0
/-- …Y — value id `1`. -/
def ACC_YS : Nat := valueCol 1
/-- …Z — value id `2`. -/
def ACC_ZS : Nat := valueCol 2

/-- `X3` — the SSA intermediate `V 26`, at its allocated column. -/
def OUT_XS : Nat := valueCol (V 26)
/-- `Y3` — `V 29`. -/
def OUT_YS : Nat := valueCol (V 29)
/-- `Z3` — `V 32`. -/
def OUT_ZS : Nat := valueCol (V 32)

/-- ⚑ **THE ROLES ARE THE ALLOCATOR'S COLUMNS, AND THEY ARE NOT CONTIGUOUS.** On the one-row layout
the six input blocks sit at `0, SK, …, 5·SK` by construction; here they sit wherever register
allocation put them, and reading a role off an assumed stride would address a different value. ⚠ The
last conjunct is the one to look at: **`OUT_XS` and the ADDEND's X block are the SAME column**,
because slot 8 was reused after the addend's last use at row 14. -/
theorem the_scheduled_roles_are_the_allocators_columns :
    ACC_XS = 258 ∧ ACC_YS = 194 ∧ ACC_ZS = 322
    ∧ OUT_XS = 290 ∧ OUT_YS = 130 ∧ OUT_ZS = 98
    ∧ OUT_XS = valueCol 3 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- ⚑⚑ **NO SLOT CARRIES ACROSS THE BLOCK BOUNDARY** — `32` is in no slot's `carryPhases`, because
every live range ends at or before row 32 and the mask fires on `lo ≤ t < hi`. This is what makes
the phase-gated thread legal: at the phase-32 transition every value column is FREE, so the thread's
write is the only claim on it. A single slot that spanned `t = 32` would fight the thread and refuse
the honest witness — silently, since both legs would still emit. -/
theorem no_slot_carries_across_the_block_boundary :
    ∀ k, k < 11 → (carryPhases k).contains 32 = false := by native_decide

/-! ## §2 — ⚑⚑ THE CYCLIC REGISTER AND THE PHASE-GATED CARRY. -/

/-- Booleanity of the chain flag. ⚑ `.all`, so there is no row on which it sleeps. -/
def goBooleanLeg : AirLeg :=
  .window ⟨.all, .mul (.loc GO) (.add (.loc GO) (.const (-1)))⟩

/-- ⚑⚑ **THE REGISTER, CYCLIC.** Four legs differ from `PastaCurveScheduled.selShiftLegs`: phase 0
returns through `GO`, the idle phase absorbs through `1 − GO`, and the LAST row is pinned idle. The
32 plain shift legs are unchanged. -/
def chainShiftLegs : List AirLeg :=
  .window ⟨.first, .add (.loc (SEL 0)) (.const (-1))⟩
  :: .window ⟨.transition,
        .add (.nxt (SEL 0)) (.mul (.const (-1)) (.mul (.loc (SEL 32)) (.loc GO)))⟩
  :: .window ⟨.transition,
        .add (.nxt SEL_IDLE)
          (.mul (.const (-1))
            (.add (.loc SEL_IDLE)
              (.add (.loc (SEL 32))
                (.mul (.const (-1)) (.mul (.loc (SEL 32)) (.loc GO))))))⟩
  :: .window ⟨.last, .add (.loc SEL_IDLE) (.const (-1))⟩
  :: (List.range 32).map (fun i =>
        .window ⟨.transition, .add (.nxt (SEL (i + 1))) (.mul (.const (-1)) (.loc (SEL i)))⟩)

/-- ⚑ **THE CHAIN'S SELECTOR BLOCK** — booleanity, the one-hot sum, the chain flag's booleanity,
and the CYCLIC register. Named so §5's extraction is list membership and the AIRs below quote ONE
object rather than three. -/
def chainSelectorLegs : List AirLeg :=
  selBooleanLegs ++ [selOneHotLeg, goBooleanLeg] ++ chainShiftLegs

/-- ⛑⛑ **THE REGISTER IS CYCLIC** — stated as what the leg FORCES rather than as a syntactic pin,
which is both stronger and the form §5 consumes: at a phase-32 row with `GO` live, phase 0 RETURNS
on the next row. -/
theorem chain_phase_zero_returns {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 33) :
    tr (t + 1) (SEL 0) + -1 * (tr t (SEL 32) * tr t GO) ≡ 0 [ZMOD P] :=
  h t ht _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl

/-- ⛑⛑ **…AND `PastaCurveScheduled`'s IS ONE-SHOT** — the same slot forces `nxt(s₀) ≡ 0`, full stop.
The pair is what makes "cyclic, not one-shot" a theorem instead of a sentence: a block whose register
carried that leg could never run twice, whatever its height. -/
theorem the_one_shot_register_kills_phase_zero (tr : RowTrace) (tf : TraceFamily)
    (pub chal : Assignment) {t : Nat} {isFirst : Bool}
    (h : ∀ l ∈ Dregg2.Circuit.Emit.PastaCurveScheduled.selShiftLegs,
           l.forces tf (rowEnv tr pub chal t) isFirst false) :
    tr (t + 1) (SEL 0) ≡ 0 [ZMOD P] :=
  h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl

/-- The idle phase absorbs when the chain stops. -/
theorem chain_idle_leg {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 33) :
    tr (t + 1) SEL_IDLE
        + -1 * (tr t SEL_IDLE + (tr t (SEL 32) + -1 * (tr t (SEL 32) * tr t GO)))
      ≡ 0 [ZMOD P] :=
  h t ht _ (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl

/-- ⛑⛑ **THE LAST ROW IS IDLE** — the leg that closes the dropped-final-addend seam, as what it
forces. Without it a prover picks a height whose last row is phase 32, the block's output has not
been threaded into the accumulator, and the discharge reads the accumulator ENTERING the last
block — every count still passing. ⚠ Its hypothesis is at `isLast = true`, which is a DIFFERENT row
window from `LegsHold`'s: that is the point of the leg. -/
theorem chain_last_row_is_idle (tr : RowTrace) (tf : TraceFamily) (pub chal : Assignment)
    {t : Nat} {isFirst : Bool}
    (h : ∀ l ∈ chainShiftLegs, l.forces tf (rowEnv tr pub chal t) isFirst true) :
    tr t SEL_IDLE + -1 ≡ 0 [ZMOD P] :=
  h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))) rfl

/-- One phase-gated thread leg: at the block boundary the accumulator's `i`-th limb on the NEXT row
is the block output's `i`-th limb on THIS row. ⚑ `.transition` is the only selector under which
`nxt` is the genuine successor; the `SEL 32` factor is what makes it fire once per BLOCK rather than
once per row. -/
def chainThreadLeg (dst src i : Nat) : AirLeg :=
  .window ⟨.transition,
    .mul (.loc (SEL 32)) (.add (.nxt (dst + i)) (.mul (.const (-1)) (.loc (src + i))))⟩

/-- ⚑⚑ **THE 96 PHASE-GATED THREADS** — three coordinates × 32 limbs, once per 33 rows. -/
def chainThreadLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [chainThreadLeg ACC_XS OUT_XS i, chainThreadLeg ACC_YS OUT_YS i, chainThreadLeg ACC_ZS OUT_ZS i])

/-- One idle-tail hold: while the register is parked, the accumulator does not move. Without these
the terminal accumulator would be unconstrained on the padding rows and the `.last` discharge would
read a free witness. -/
def idleHoldLeg (c i : Nat) : AirLeg :=
  .window ⟨.transition,
    .mul (.loc SEL_IDLE) (.add (.nxt (c + i)) (.mul (.const (-1)) (.loc (c + i))))⟩

/-- ⚑ **THE 96 IDLE HOLDS.** -/
def idleHoldLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [idleHoldLeg ACC_XS i, idleHoldLeg ACC_YS i, idleHoldLeg ACC_ZS i])

theorem the_thread_and_the_hold_are_ninety_six_each :
    chainThreadLegs.length = 96 ∧ idleHoldLegs.length = 96 := by
  refine ⟨by native_decide, by native_decide⟩

/-! ## §3 — THE ENDPOINTS AND THE DISCHARGE, AT THE ALLOCATED ACCUMULATOR. -/

/-- The FIRST row's accumulator, published at `PI[0..95]`. -/
def schedInPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.first, ACC_XS + i, ACC_IN_PI i⟩
    , AirLeg.pin ⟨.first, ACC_YS + i, ACC_IN_PI (SK + i)⟩
    , AirLeg.pin ⟨.first, ACC_ZS + i, ACC_IN_PI (2 * SK + i)⟩ ])

/-- The LAST row's accumulator, published at `PI[96..191]`. ⚑ Same PI layout as the one-row block,
so a fold node's `cb.connect` of a left child's outgoing limbs to a right child's incoming ones is
the SAME adapter — the narrowing does not move the interface. -/
def schedOutPinLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.pin ⟨.last, ACC_XS + i, ACC_OUT_PI i⟩
    , AirLeg.pin ⟨.last, ACC_YS + i, ACC_OUT_PI (SK + i)⟩
    , AirLeg.pin ⟨.last, ACC_ZS + i, ACC_OUT_PI (2 * SK + i)⟩ ])

/-- ⚑ **THE 64 DISCHARGE GATES** — every LIMB of the terminal `X` and `Z` is zero on the last row.
Limbs and not the value: `sVal` over 32 byte-ranged limbs ranges past the prime, so "the value is
`≡ 0`" would also admit the limbs of `q` and `2q`. -/
def schedDischargeLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [ AirLeg.window ⟨RowSel.last, .loc (ACC_XS + i)⟩
    , AirLeg.window ⟨RowSel.last, .loc (ACC_ZS + i)⟩ ])

theorem the_endpoint_and_discharge_counts :
    schedInPinLegs.length = 96 ∧ schedOutPinLegs.length = 96
    ∧ schedDischargeLegs.length = 64 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-! ## §4 — THE AIRS, THE DESCRIPTORS AND THE MEASUREMENT. -/

/-- The three range tables the scheduled block declares, at the chained width. **No fourth width was
invented**: same `w8`/`w16`/`w1` union `PastaCurveSound.rcbTables` declares. -/
def chainTables : List TableDef :=
  [ mainTableDef CHAIN_W
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

/-- ⚑ **A SEGMENT of the scheduled closing chain.** -/
def closingSchedSegAir : EffectAir :=
  { tables := chainTables
  , legs := chainSelectorLegs
              ++ valuePoolLegs ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs pLimb
              ++ chainThreadLegs ++ idleHoldLegs ++ schedInPinLegs ++ schedOutPinLegs }

/-- ⚑⚑ **THE FINAL SEGMENT** — the same block plus the 64 `.last` discharge gates. This is the
closing check. -/
def closingSchedFinalAir : EffectAir :=
  { tables := chainTables
  , legs := chainSelectorLegs
              ++ valuePoolLegs ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs pLimb
              ++ chainThreadLegs ++ idleHoldLegs ++ schedInPinLegs ++ schedOutPinLegs
              ++ schedDischargeLegs }

/-- …and the Vesta twin, because the accumulator leg is Step/Tick on Vesta and a Pallas-only
narrowing would leave half the recursion boundary on the wide row. -/
def closingSchedFinalAirQ : EffectAir :=
  { tables := chainTables
  , legs := chainSelectorLegs
              ++ valuePoolLegs ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs qLimb
              ++ chainThreadLegs ++ idleHoldLegs ++ schedInPinLegs ++ schedOutPinLegs
              ++ schedDischargeLegs }

/-- ⚑ **THE SEGMENT'S LEGS ARE A PREFIX OF THE FINAL'S** — the discharge APPENDS, it does not
re-author, so every statement about the segment applies to the final block unchanged. -/
theorem closingSchedFinalAir_extends_seg :
    closingSchedSegAir.legs <+: closingSchedFinalAir.legs :=
  ⟨schedDischargeLegs, by
    simp [closingSchedSegAir, closingSchedFinalAir, List.append_assoc]⟩

set_option maxHeartbeats 8000000 in
/-- ⚑ **THE COMPILER ACCEPTS THE BLOCK.** The `.all` selector legs read no `nxt`, the threads and
holds are `.transition` (the only selector under which `nxt` is the successor), the discharge and
the idle pin are `.last`. A selector confusion in any of the three families lowers to
`refuseConstraints` and this goes red. -/
theorem closingSchedSegAir_mainRailOk : closingSchedSegAir.mainRailOk = true := by decide

set_option maxHeartbeats 8000000 in
theorem closingSchedFinalAir_mainRailOk : closingSchedFinalAir.mainRailOk = true := by decide

set_option maxHeartbeats 8000000 in
theorem closingSchedFinalAirQ_mainRailOk : closingSchedFinalAirQ.mainRailOk = true := by native_decide

set_option maxHeartbeats 40000000 in
/-- ⚑ **NO PIN IS DECORATIVE** — every published column is DERIVED by another leg. The accumulator
columns are read by the carry legs, the op gates and the thread; a pin on a column nothing
constrains would make this false.

⚑ The `TiedAir`s below are HANDED this and its segment twin. Their fields are `autoParam`s
defaulting to `by decide`: a field left blank decides the same 40-million-heartbeat verdict a
second time, inside the elaborator's `whnf`. -/
theorem closingSchedFinalAir_pinsTied : closingSchedFinalAir.pinsTied = true := by decide

set_option maxHeartbeats 40000000 in
/-- The segment block's tie verdict — the same claim about the block WITHOUT the discharge legs,
which `closingSchedFinalAir_extends_seg` makes a strictly smaller leg list. -/
theorem closingSchedSegAir_pinsTied : closingSchedSegAir.pinsTied = true := by decide

set_option maxHeartbeats 40000000 in
/-- ⚑ **EVERY COLUMN THE CONSTRAINTS ADDRESS IS INSIDE THE DECLARED WIDTH** — the check
`descriptor_ir2.rs:2171` performs, done on the source side so a layout slip is a Lean error rather
than a prover refusal. `GO` is the widest, at `CHAIN_W − 1`. -/
theorem closingSchedFinal_columns_fit :
    (closingSchedFinalAir.legs.all (fun l => l.readCols.all (fun c => c < CHAIN_W))) = true := by
  native_decide

set_option maxHeartbeats 8000000 in
/-- ⚑ **THE SELECTOR CENSUS.** A `.transition → .all` re-scope on a thread accepts strictly more and
a `.last → .all` on the discharge refuses every intermediate accumulator; neither moves a constraint
COUNT, so the counts are what keep a re-scope visible. -/
theorem the_scheduled_closing_selector_census :
    closingSchedFinalAir.windowCountSel RowSel.transition = 578
    ∧ closingSchedFinalAir.windowCountSel RowSel.last = 65
    ∧ closingSchedFinalAir.windowCountSel RowSel.first = 1
    ∧ closingSchedFinalAir.windowCountSel RowSel.all = 36 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

def closingSchedSegTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := closingSchedSegAir
  ok   := closingSchedSegAir_mainRailOk
  tied := closingSchedSegAir_pinsTied

def closingSchedFinalTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := closingSchedFinalAir
  ok   := closingSchedFinalAir_mainRailOk
  tied := closingSchedFinalAir_pinsTied

def closingSchedSegDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-closing-scheduled-seg::v1" CHAIN_W ACC_PI_COUNT [] closingSchedSegTiedAir).val

def closingSchedFinalDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-closing-scheduled-final::v1" CHAIN_W ACC_PI_COUNT []
    closingSchedFinalTiedAir).val

/-- ⚑ **THE CERTIFICATE, PRODUCED BY THE EMIT** — every leg of this source is FORCED by the emitted
constraints, per-leg, in the source's own `AirLeg.forces` vocabulary. Not re-derived: it is
`EffectLowerCertified`'s machinery applied unchanged. -/
theorem closingSchedFinalDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines closingSchedFinalDesc [] closingSchedFinalAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-closing-scheduled-final::v1" CHAIN_W ACC_PI_COUNT []
    closingSchedFinalTiedAir).property

theorem closingSchedSegDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines closingSchedSegDesc [] closingSchedSegAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-wrap-closing-scheduled-seg::v1" CHAIN_W ACC_PI_COUNT [] closingSchedSegTiedAir).property

/-- ⚑ **A NAME IS A KEY.** This cone now has EIGHT descriptors over one algebra shape, and a lookup
that resolved a scheduled closing block to a one-row one would verify at a different width with
every other number still plausible. -/
theorem the_scheduled_closing_names_are_new :
    closingSchedSegDesc.name ≠ closingSchedFinalDesc.name
    ∧ closingSchedFinalDesc.name ≠ Dregg2.Circuit.Emit.MinaAccumulatorAir.accFinalDesc.name
    ∧ closingSchedFinalDesc.name ≠ Dregg2.Circuit.Emit.MinaAccumulatorAir.accSegDesc.name := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-! ### §4a — ⚑⚑ THE MEASUREMENT, ON THE EMITTED OBJECTS. -/

theorem closingSchedFinalDesc_width : closingSchedFinalDesc.traceWidth = 482 := rfl
theorem closingSchedFinalDesc_piCount : closingSchedFinalDesc.piCount = 192 := rfl

/-- ⚑⚑ **THE COMMITTED WIDTH — 1 500**, against the deployed closing row's 10 756. `traceWidth` is
not what `Ir2Air::Main` is `width()`d at: `MainLayout::build` (`descriptor_ir2.rs:1919`) adds a
nibble aux block per declared range lookup, and the cost law is linear in THAT. -/
theorem closingSchedFinalDesc_committed :
    committedWidth CHAIN_W closingSchedFinalAir = 1500 := by native_decide

/-- ⚑ The aux block is unchanged from the standalone scheduled row: the thread, the holds, the pins
and the discharge declare no range lookup at all. **A booleanity assertion is a degree-2 window
gate, not a bus query** — which is why the register and the chain flag are free in the width that
costs. -/
theorem the_chain_legs_cost_no_aux_columns :
    airAuxCols closingSchedFinalAir = 1018
    ∧ airAuxCols Dregg2.Circuit.Emit.PastaCurveScheduled.pallasScheduledAir = 1018 := by
  refine ⟨by native_decide, by native_decide⟩

/-- ⚑⚑⚑ **THE HEADLINE, ON THE TWO EMITTED OBJECTS: 10 756 → 1 500 COMMITTED COLUMNS.** Stated as
`× 7` because that is the largest integer it clears — 7.17×, and rounding it up to 8 is how a 7.17
becomes an "8×". -/
theorem the_scheduled_closing_row_commits_seven_times_less :
    committedWidth CHAIN_W closingSchedFinalAir * 7
      < committedWidth Dregg2.Circuit.Emit.PastaCurveSound.RCB_WIDTH
          Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir := by native_decide

/-- The three committed widths side by side, so the ratio above is checkable rather than asserted.
⚑ The `-fs` figure is the object the brief names at `3 091` declared — its transcript weld costs 43
declared columns and NOT ONE aux column. -/
theorem the_two_committed_widths :
    committedWidth Dregg2.Circuit.Emit.PastaCurveSound.RCB_WIDTH
        Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir = 10756
    ∧ committedWidth CHAIN_W closingSchedFinalAir = 1500 := by
  refine ⟨by native_decide, by native_decide⟩

/-- The constraint count, and the census so a dropped family moves a number: 34 booleanity + 1
one-hot + 1 `GO` booleanity + 36 register + 352 value-pool + 95 witness-pool + 352 carry + 1 428 op
gates + 96 threads + 96 idle holds + 192 endpoint pins + 64 discharge. -/
theorem closingSchedFinalDesc_constraint_count :
    closingSchedFinalDesc.constraints.length = 2747 := by native_decide

theorem the_scheduled_closing_census :
    34 + 1 + 1 + 36 + 352 + 95 + 352 + 1428 + 96 + 96 + 192 + 64
      = closingSchedFinalDesc.constraints.length := by native_decide

/-- ⚑ **THE RANGE-LOOKUP COUNT IS THE SCHEDULED ROW'S, UNCHANGED** — 447 per-pool lookups against
the deployed closing row's 3 048 per-op ones. This is where the aux block goes, and therefore where
the committed width goes. -/
theorem the_scheduled_closing_range_lookups :
    closingSchedFinalAir.totalRangeLookups = 447
    ∧ Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir.totalRangeLookups
        = 3048 := by
  refine ⟨by native_decide, by native_decide⟩

/-! ### §4b — ⚠⚑ THE HALF OF THE TRADE THAT IS NOT A WIN.

A width ratio quoted alone is the flattering member of a pair. One complete addition is **1 row** on
the deployed layout and **33 rows** here, so the LEAF prover's committed CELLS go the other way, and
the honest claim is that this moves work from the wrap into the leaf. -/

/-- ⚑⚑ **THE LEAF PROVER PAYS 4.6× MORE PER ADDITION.** `33 · 1 500 = 49 500` committed cells
against `1 · 10 756`. Stated as `> 4 ·` because that is the largest integer it clears; the ratio is
4.60. ⚠ Do not quote the 7.17× without this. -/
theorem the_leaf_prover_pays_more_per_addition :
    33 * committedWidth CHAIN_W closingSchedFinalAir
      > 4 * committedWidth Dregg2.Circuit.Emit.PastaCurveSound.RCB_WIDTH
            Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSoundAir := by native_decide

/-- ⚑ **AND THE MERKLE PATH GROWS BY `log₂ 33 = 6` BITS PER BLOCK.** `2⁵ < 33 ≤ 2⁶`, so a block that
was one row is six rounds of a Merkle path deeper — the depth an in-circuit FRI verifier pays `Q`
compressions for, per commitment round. Stated on the row count rather than on a config constant,
because the blowup that multiplies it is `recursion_layer_over`'s business and not this file's. -/
theorem the_block_costs_six_bits_of_merkle_depth :
    2 ^ 5 < 33 ∧ 33 ≤ 2 ^ 6 := by refine ⟨by native_decide, by native_decide⟩

/-! ## §5 — ⚑⚑ ONE BLOCK'S ROWS FORCE THE RCB FORMULA — the re-run of `AirCrossRow`'s composition.

The blocker named *"a re-run of `AirCrossRow`'s composition"* and this is it. The cyclic register is
NOT the one `AirSelectorForcing.phaseIndicator_of_selectorLegs` was proved against, so the induction
is reused through `phaseIndicator_of_phaseFacts` — which takes the six FACTS rather than one leg
list, and hands the `nxt(s₀)` and idle facts `tr t 32 ≡ 0`. That hypothesis is exactly what collapses
`nxt(s₀) ≡ loc(s₃₂)·loc(GO)` to `nxt(s₀) ≡ 0` over the first block, and it is why one induction
serves both registers instead of two copies drifting apart.

⚠ **FIRST BLOCK ONLY.** See the header: the chain-level statement is undone work, not a caveat. -/

section Forcing

variable {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}

theorem chain_boolean (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 33)
    {i : Nat} (hi : i < 34) : tr t i * (tr t i + (-1)) ≡ 0 [ZMOD P] :=
  h t ht _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))

theorem chain_onehot (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 33) :
    ((List.range 34).map (tr t)).sum ≡ 1 [ZMOD P] := by
  have hb : (WindowExpr.add (sumLoc (List.range 34)) (.const (-1))).eval (rowEnv tr pub chal t)
      ≡ 0 [ZMOD P] :=
    h t ht _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)))
  simp only [WindowExpr.eval, sumLoc_eval, rowEnv] at hb
  have h1 := hb.add_right 1
  have e1 : ((List.range 34).map (tr t)).sum + -1 + 1 = ((List.range 34).map (tr t)).sum := by ring
  have e2 : (0 : ℤ) + 1 = 1 := by ring
  rwa [e1, e2] at h1

theorem chain_first (h : LegsHold tr tf pub chal chainSelectorLegs) : tr 0 0 ≡ 1 [ZMOD P] := by
  have hb : (WindowExpr.add (.loc (SEL 0)) (.const (-1))).eval (rowEnv tr pub chal 0)
      ≡ 0 [ZMOD P] :=
    h 0 (by omega) _ (List.mem_append_right _ (List.mem_cons_self ..)) rfl
  simp only [WindowExpr.eval, rowEnv, SEL] at hb
  have h1 := hb.add_right 1
  have e1 : tr 0 0 + -1 + 1 = tr 0 0 := by ring
  have e2 : (0 : ℤ) + 1 = 1 := by ring
  rwa [e1, e2] at h1

theorem chain_shift (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 33)
    {i : Nat} (hi : i < 32) : tr (t + 1) (i + 1) + -1 * tr t i ≡ 0 [ZMOD P] :=
  h t ht _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))) rfl

/-- ⚑ **THE CYCLIC LEG COLLAPSES TO THE ONE-SHOT ONE INSIDE A BLOCK.** With phase 32 dead at row
`t`, `nxt(s₀) ≡ loc(s₃₂)·loc(GO)` says `nxt(s₀) ≡ 0` — whatever `GO` is. -/
theorem chain_no_return (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 32)
    (h32 : tr t 32 ≡ 0 [ZMOD P]) : tr (t + 1) 0 ≡ 0 [ZMOD P] := by
  have hb := chain_phase_zero_returns h (by omega : t < 33)
  have hz : tr t 32 * tr t GO ≡ 0 * tr t GO [ZMOD P] := h32.mul_right _
  have hc : tr (t + 1) 0 + -1 * (tr t 32 * tr t GO)
      ≡ tr (t + 1) 0 + -1 * (0 * tr t GO) [ZMOD P] :=
    (Int.ModEq.refl _).add ((Int.ModEq.refl (-1 : ℤ)).mul hz)
  have := hc.symm.trans hb
  simpa using this

theorem chain_idle (h : LegsHold tr tf pub chal chainSelectorLegs) {t : Nat} (ht : t < 32)
    (h32 : tr t 32 ≡ 0 [ZMOD P]) (h33 : tr t 33 ≡ 0 [ZMOD P]) :
    tr (t + 1) 33 ≡ 0 [ZMOD P] := by
  have hb := chain_idle_leg h (by omega : t < 33)
  have hs : tr t 33 + (tr t 32 + -1 * (tr t 32 * tr t GO))
      ≡ 0 + (0 + -1 * (0 * tr t GO)) [ZMOD P] :=
    h33.add (h32.add ((Int.ModEq.refl (-1 : ℤ)).mul (h32.mul_right _)))
  have hc : tr (t + 1) 33 + -1 * (tr t 33 + (tr t 32 + -1 * (tr t 32 * tr t GO)))
      ≡ tr (t + 1) 33 + -1 * (0 + (0 + -1 * (0 * tr t GO))) [ZMOD P] :=
    (Int.ModEq.refl _).add ((Int.ModEq.refl (-1 : ℤ)).mul hs)
  have := hc.symm.trans hb
  simpa using this

/-- ⚑⚑ **`PhaseIndicator` FOR THE CYCLIC REGISTER, OVER THE FIRST BLOCK.** -/
theorem chain_phaseIndicator (h : LegsHold tr tf pub chal chainSelectorLegs) : PhaseIndicator tr :=
  phaseIndicator_of_phaseFacts
    (fun t ht i hi => chain_boolean h ht hi) (fun t ht => chain_onehot h ht) (chain_first h)
    (fun t ht h32 => chain_no_return h ht h32) (fun t ht h32 h33 => chain_idle h ht h32 h33)
    (fun t ht i hi => chain_shift h ht hi)

theorem chainSelectorLegs_sub : ∀ l ∈ chainSelectorLegs, l ∈ closingSchedFinalAir.legs := by
  intro l hl
  simp only [closingSchedFinalAir, chainSelectorLegs, List.mem_append] at hl ⊢
  tauto

theorem carryLegs_sub : ∀ l ∈ carryLegs, l ∈ closingSchedFinalAir.legs := by
  intro l hl
  simp only [closingSchedFinalAir, List.mem_append] at hl ⊢
  tauto

theorem scheduleLegs_sub : ∀ l ∈ scheduleLegs pLimb, l ∈ closingSchedFinalAir.legs := by
  intro l hl
  simp only [closingSchedFinalAir, List.mem_append] at hl ⊢
  tauto

end Forcing

/-- ⚑⚑⚑ **THE FIRST BLOCK'S 33 ROWS FORCE `(X3, Y3, Z3) ≡ rcbTraceZ 15 (P, Q)` MOD THE PALLAS-BASE
PRIME**, from the CHAINED block's own legs — the cyclic register, the carry legs and the op gates.

⚠ **Which object:** `closingSchedFinalAir`, the block emitted as
`dregg-mina-wrap-closing-scheduled-final::v1` at 482 declared / 1 500 committed columns, on the hand
schedule `rcbOpsScheduled`. ⚠ **First block only** — rows 0-32. The chain-level statement is the
undone work named in the header, and this theorem is not it. -/
theorem oneBlockRows_force_the_rcb_formula (tr : RowTrace) (tf : TraceFamily)
    (pub chal : Assignment) (h : LegsHold tr tf pub chal closingSchedFinalAir.legs)
    (hr : PoolsRanged tr) :
    CZp (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c := by
  have hp : PhaseIndicator tr := chain_phaseIndicator (h.mono chainSelectorLegs_sub)
  have hc : SlotsCarry tr :=
    slotsCarry_of_carryLegs tr tf pub chal hp
      (fun t ht l hl => h t ht l (carryLegs_sub l hl))
  exact scheduledRows_force_the_rcb_formula tr hc hr
    (rowsSat_of_scheduleLegs hp (h.mono scheduleLegs_sub))

#assert_compiled the_scheduled_roles_are_the_allocators_columns
#assert_compiled no_slot_carries_across_the_block_boundary
#assert_axioms chain_phase_zero_returns
#assert_axioms the_one_shot_register_kills_phase_zero
#assert_axioms chain_last_row_is_idle
#assert_compiled the_thread_and_the_hold_are_ninety_six_each
#assert_compiled the_endpoint_and_discharge_counts
#assert_axioms closingSchedSegAir_mainRailOk
#assert_axioms closingSchedFinalAir_mainRailOk
#assert_compiled closingSchedFinalAirQ_mainRailOk
#assert_axioms closingSchedFinalAir_pinsTied
#assert_compiled closingSchedFinal_columns_fit
#assert_compiled the_scheduled_closing_selector_census
#assert_axioms closingSchedFinalDesc_certified
#assert_axioms closingSchedSegDesc_certified
#assert_axioms closingSchedFinalDesc_width
#assert_compiled closingSchedFinalDesc_committed
#assert_compiled the_chain_legs_cost_no_aux_columns
#assert_compiled the_scheduled_closing_row_commits_seven_times_less
#assert_compiled the_two_committed_widths
#assert_compiled closingSchedFinalDesc_constraint_count
#assert_compiled the_scheduled_closing_census
#assert_compiled the_scheduled_closing_range_lookups
#assert_compiled the_leaf_prover_pays_more_per_addition
#assert_compiled the_scheduled_closing_names_are_new
#assert_axioms chain_phaseIndicator
#assert_axioms oneBlockRows_force_the_rcb_formula

#assert_compiled the_block_costs_six_bits_of_merkle_depth
#assert_compiled chain_w_eq
end Dregg2.Circuit.Emit.MinaWrapClosingScheduled
