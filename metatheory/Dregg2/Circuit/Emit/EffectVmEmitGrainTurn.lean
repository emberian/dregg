/-
# Dregg2.Circuit.Emit.EffectVmEmitGrainTurn — ONE executor grain turn as ONE EffectVM row.

A grain turn (`grain-turn/src/lib.rs` `ToolGatewayMinter::mint_turn`) is one executor turn on the
grain worker cell `w` (the turn's agent): PHASE 1 debits `turn.fee` and ticks `w`'s nonce ONCE
(`turn/src/executor/execute.rs`, modelled by `Admission.commitPrologue`), then the body writes the
five grain slots 4 (`calls_made`), 3 (`history_root`), 5 (`consumed`), 6 (`heap_root`), 7
(`action`). The per-slot `setFieldVmDescriptor2-{slot}R24` members model one nonce tick PER
WRITE, so a grain turn folded through them lands at `nonce = pre + 5` with the pre-fee balance.

`grainTurnVmDescriptor` is the faithful face: ONE active row carries the whole turn.
  * the five grain slots take their lane-0 values from `param0..param4` (slot `j` ↔ `param (j-3)`);
  * slots 0..2, `bal_hi`, `cap_root`, `reserved` are frozen;
  * `bal_lo` is debited by the fee at `param5`;
  * the nonce ticks by the selector `s_g` itself (`after − before − s_g`), so it ticks on the
    active row and on no other row;
  * the first-row pin makes row 0 the active row, and the IR-v2 window gate
    (`grainNoSecondActiveRow`) makes every later row inactive. Together they force exactly one
    tick per leg (`grainTurn_trace_ticks_once`).

The executor link is `grainTurn_row_agrees_executor`: on an executor-committed grain turn, the
row's post-block equals the worker cell's post-turn projection (balance, nonce and all eight slot
fields) after admission, prologue, body and fee distribution.

STATUS: a design-branch module (`i10-single-tick-grain-descriptor`, ember-gated). It is NOT in any
registry; nothing emits or deploys it. See `grain-session/SINGLE-TICK-DESCRIPTOR.md`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Exec.Admission

namespace Dregg2.Circuit.Emit.EffectVmEmitGrainTurn

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub ePrm gBalHi gCapPass gResPass gFieldPass transferHashSites transitionAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitSetField (slotName slotName_ne_balance)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec (balOf balanceField)
open Dregg2.Exec.EffectTransfer (nonceOf nonceField setNonce setNonce_nonceOf setNonce_balOf)
open Dregg2.Exec.EffectsState (fieldOf setField setField_fieldOf setField_balOf)
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullA execFullTurnA)
open Dregg2.Exec.Admission
  (AdmCtx TurnHdr admissible commitPrologue prologueCell distributeFee distributeFee_frame runTurn)
open Dregg2.Circuit.Spec.CellStateField (setFieldCellMap execFullA_setFieldA_iff_spec)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — columns. -/

/-- The grain-turn selector column. `6` is the first entry of the Rust
`columns::sel::RETIRED_SELECTORS` (a factory-dissolved index no constraint reads, measured by
`unforced_pi_pin_census.rs::retired_selector_columns_are_referenced_by_nothing`); repurposing it
follows the `sel::MINT = 14` precedent. The choice of index is ember's decision (design note D1). -/
def SEL_GRAIN_TURN : Nat := 6

/-- A grain slot: written by every grain turn (3 `history_root`, 4 `calls_made`, 5 `consumed`,
6 `heap_root`, 7 `action`). Slots 0..2 are never written by the minter. -/
def IsGrainSlot (j : Fin 8) : Bool := decide (3 ≤ j.val)

/-- The param column carrying slot `j`'s written lane-0 value: `param (j − 3)`, so `param0..param4`
carry slots 3..7. -/
def grainParam (j : Fin 8) : Nat := j.val - 3

/-- The param column carrying `turn.fee` (the Phase-1 debit). -/
def FEE_PARAM : Nat := 5

/-- The fee range width: the wide graduation's 15-bit table. A grain turn's fee (`5_000`) fits; a
larger fee is refused (fail-closed completeness bound, not a soundness gap). -/
def FEE_BITS : Nat := 15

/-- The selector as an expression. -/
def eSelG : EmittedExpr := .var SEL_GRAIN_TURN

/-! ## §1 — the per-row gates. -/

/-- Grain-slot write gate, two-sided: `after − before − s_g·(param − before)`. On the active row
(`s_g = 1`) it is `after = param`; on any other row (`s_g = 0`) it FREEZES the slot. -/
def gGrainWrite (j : Fin 8) : EmittedExpr :=
  eSub (eSub (eSA (state.FIELD_BASE + j.val)) (eSB (state.FIELD_BASE + j.val)))
    (.mul eSelG (eSub (ePrm (grainParam j)) (eSB (state.FIELD_BASE + j.val))))

/-- Balance-lo fee gate: `after − before + s_g·fee`. Active row: `after = before − fee`; else frozen. -/
def gBalLoFeeG : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul eSelG (ePrm FEE_PARAM))

/-- The ONE-tick nonce gate: `after − before − s_g`. The tick is the selector itself, so a row that
is not the active grain row (pad, or any other selector) cannot move the nonce. -/
def gNonceG : EmittedExpr :=
  eSub (eSub (eSA state.NONCE) (eSB state.NONCE)) eSelG

/-- Selector booleanity: `s_g·(s_g − 1)`. -/
def gSelBool : EmittedExpr := .mul eSelG (eSub eSelG (.const 1))

/-- The per-slot gate: a grain slot gets the two-sided write gate, a non-grain slot the freeze. -/
def grainSlotGate (j : Fin 8) : VmConstraint :=
  if IsGrainSlot j then .gate (gGrainWrite j) else .gate (gFieldPass j.val)

/-- The per-row gates of the grain-turn face. -/
def grainTurnRowGates : List VmConstraint :=
  [ .gate gBalLoFeeG, .gate gBalHi, .gate gNonceG, .gate gCapPass, .gate gResPass, .gate gSelBool ]
  ++ (List.finRange 8).map grainSlotGate

/-- First-row pin: row 0 IS the active grain row (`s_g − 1 = 0` on the first row). -/
def grainFirstRowPin : VmConstraint := .boundary .first (eSub eSelG (.const 1))

def grainTurnVmAirName : String := "dregg-effectvm-grainturn-v1"

/-- **`grainTurnVmDescriptor`** — the v1 face: the row gates, the first-row pin, whole-block
continuity (`transitionAll`, the transfer face's; the per-slot setField face carries none), the
transfer GROUP-4 hash sites (all eight field columns are among the absorbed state-block columns), the two
balance-limb range teeth, and a `FEE_BITS`-bit (15) range on the fee param. Together the after-`bal_lo`
tooth and the fee tooth refuse the mod-p wrap forgery (docs/FINDING-modp-wrap-forgery-audit.md): an
underflowing debit (`fee > bal_lo_before`) lands at `bal_lo_before − fee + p ≥ p − 2^15 > 2^30` and fails
the 30-bit after-`bal_lo` range. A 30-bit fee range would NOT suffice (`p − 2^30 < 2^30`, so a fee in
`(p − 2^30, 2^30)` against a zero balance would read as a credit); the 15-bit width rides the wide
graduation's 15-bit table (`graduateV1Wide`, the borrow-weld precedent). -/
def grainTurnVmDescriptor : EffectVmDescriptor :=
  { name := grainTurnVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := grainTurnRowGates ++ [grainFirstRowPin] ++ transitionAll
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩, ⟨prmCol FEE_PARAM, FEE_BITS⟩ ] }

#guard grainTurnRowGates.length == 14
#guard grainTurnVmDescriptor.constraints.length == 14 + 1 + 14

/-- The trace theorem's continuity hypothesis is one of the face's own constraints. -/
theorem nonce_transition_mem :
    VmConstraint.transition state.NONCE state.NONCE ∈ grainTurnVmDescriptor.constraints := by
  simp [grainTurnVmDescriptor, transitionAll, state.NONCE, STATE_SIZE]

/-- The first-row pin is one of the face's own constraints. -/
theorem firstRowPin_mem : grainFirstRowPin ∈ grainTurnVmDescriptor.constraints := by
  simp [grainTurnVmDescriptor]
#guard ((List.finRange 8).filter (fun j => IsGrainSlot j)).map (·.val) == [3, 4, 5, 6, 7]
#guard ((List.finRange 8).filter (fun j => IsGrainSlot j)).map grainParam == [0, 1, 2, 3, 4]

/-! ## §2 — row intent + faithfulness. -/

/-- The active row is the grain row. -/
def IsGrainTurnRow (env : VmRowEnv) : Prop := env.loc SEL_GRAIN_TURN = 1

/-- **`GrainTurnRowIntent env`** — the executor's whole grain turn on the worker cell's block: the
fee debited from `bal_lo`, the nonce ticked ONCE, the five grain slots set to their params, every
other column frozen. -/
def GrainTurnRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol FEE_PARAM)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ j : Fin 8, IsGrainSlot j = true →
      env.loc (saCol (state.FIELD_BASE + j.val)) = env.loc (prmCol (grainParam j)))
  ∧ (∀ j : Fin 8, IsGrainSlot j = false →
      env.loc (saCol (state.FIELD_BASE + j.val)) = env.loc (sbCol (state.FIELD_BASE + j.val)))

/-- The explicit canonicality envelope (the deployed field-representative / range invariant as
named hypotheses): both state windows canonical, the six params canonical, the nonce tick in-field,
and the fee covered by `bal_lo` (the executor's fee-coverage gate; in-circuit the 30-bit range on the
after `bal_lo` refuses the wrapped debit). -/
def GrainRowCanon (env : VmRowEnv) : Prop :=
  (∀ off, off < STATE_SIZE →
      (0 ≤ env.loc (sbCol off) ∧ env.loc (sbCol off) < 2013265921)
      ∧ (0 ≤ env.loc (saCol off) ∧ env.loc (saCol off) < 2013265921))
  ∧ (∀ k, k ≤ FEE_PARAM → 0 ≤ env.loc (prmCol k) ∧ env.loc (prmCol k) < 2013265921)
  ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921
  ∧ env.loc (prmCol FEE_PARAM) ≤ env.loc (sbCol state.BALANCE_LO)

theorem mem_grainTurnRowGates_slot (j : Fin 8) : grainSlotGate j ∈ grainTurnRowGates := by
  unfold grainTurnRowGates
  exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

/-- **FAITHFULNESS** — on the active grain row, the emitted gates hold iff the row intent does. -/
theorem grainTurnVm_faithful (env : VmRowEnv) (hrow : IsGrainTurnRow env)
    (hcanon : GrainRowCanon env) :
    (∀ c ∈ grainTurnRowGates, c.holdsVm env false false) ↔ GrainTurnRowIntent env := by
  obtain ⟨hcells, hprm, hovf, hcover⟩ := hcanon
  have hbLo := hcells state.BALANCE_LO (by norm_num [state.BALANCE_LO, STATE_SIZE])
  have hbHi := hcells state.BALANCE_HI (by norm_num [state.BALANCE_HI, STATE_SIZE])
  have hbN := hcells state.NONCE (by norm_num [state.NONCE, STATE_SIZE])
  have hbCap := hcells state.CAP_ROOT (by norm_num [state.CAP_ROOT, STATE_SIZE])
  have hbRes := hcells state.RESERVED (by norm_num [state.RESERVED, STATE_SIZE])
  have hfee := hprm FEE_PARAM le_rfl
  have hF : ∀ j : Fin 8, _ := fun j => hcells (state.FIELD_BASE + j.val)
    (by have := j.isLt; simp only [state.FIELD_BASE, STATE_SIZE]; omega)
  have hP : ∀ j : Fin 8, IsGrainSlot j = true → _ := fun j _ =>
    hprm (grainParam j) (by have := j.isLt; simp only [grainParam, FEE_PARAM]; omega)
  constructor
  · intro h
    have hLo  := h (.gate gBalLoFeeG) (by simp [grainTurnRowGates])
    have hHi  := h (.gate gBalHi) (by simp [grainTurnRowGates])
    have hNon := h (.gate gNonceG) (by simp [grainTurnRowGates])
    have hCap := h (.gate gCapPass) (by simp [grainTurnRowGates])
    have hRes := h (.gate gResPass) (by simp [grainTurnRowGates])
    simp only [VmConstraint.holdsVm, gBalLoFeeG, gBalHi, gNonceG, gCapPass, gResPass, eSelG,
      eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hrow] at hLo hNon
    rw [Int.modEq_zero_iff_dvd] at hLo hHi hNon hCap hRes
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · intro j hj
      have hW := h _ (mem_grainTurnRowGates_slot j)
      simp only [grainSlotGate, hj, ite_true, VmConstraint.holdsVm, gGrainWrite, eSelG, eSA, eSB,
        ePrm, eSub, EmittedExpr.eval] at hW
      rw [hrow, Int.modEq_zero_iff_dvd] at hW
      have := hF j; have := hP j hj
      omega
    · intro j hj
      have hW := h _ (mem_grainTurnRowGates_slot j)
      simp only [grainSlotGate, hj, Bool.false_eq_true, ite_false, VmConstraint.holdsVm,
        gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hW
      rw [Int.modEq_zero_iff_dvd] at hW
      have := hF j
      omega
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hW, hP0⟩ c hc
    simp only [grainTurnRowGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_finRange, true_and] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFeeG, eSelG, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd, hrow]; omega
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gNonceG, eSelG, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd, hrow]; omega
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gSelBool, eSelG, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd, hrow]; omega
    · cases hj : IsGrainSlot j
      · have := hP0 j hj
        simp only [grainSlotGate, hj, Bool.false_eq_true, ite_false, VmConstraint.holdsVm,
          gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
        rw [Int.modEq_zero_iff_dvd]; omega
      · have := hW j hj
        simp only [grainSlotGate, hj, ite_true, VmConstraint.holdsVm, gGrainWrite, eSelG, eSA,
          eSB, ePrm, eSub, EmittedExpr.eval]
        rw [Int.modEq_zero_iff_dvd, hrow]; omega

/-- **A row that is not the active grain row moves NOTHING** — not the nonce, not the balance, not
any slot. This is what makes "one active row" mean "one tick": the tick lives on the selector. -/
theorem grainTurn_inactive_row_frozen (env : VmRowEnv) (hoff : env.loc SEL_GRAIN_TURN = 0)
    (hcells : ∀ off, off < STATE_SIZE →
      (0 ≤ env.loc (sbCol off) ∧ env.loc (sbCol off) < 2013265921)
      ∧ (0 ≤ env.loc (saCol off) ∧ env.loc (saCol off) < 2013265921))
    (h : ∀ c ∈ grainTurnRowGates, c.holdsVm env false false) :
    env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
    ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
    ∧ ∀ j : Fin 8, env.loc (saCol (state.FIELD_BASE + j.val))
        = env.loc (sbCol (state.FIELD_BASE + j.val)) := by
  have hbLo := hcells state.BALANCE_LO (by norm_num [state.BALANCE_LO, STATE_SIZE])
  have hbN := hcells state.NONCE (by norm_num [state.NONCE, STATE_SIZE])
  have hLo  := h (.gate gBalLoFeeG) (by simp [grainTurnRowGates])
  have hNon := h (.gate gNonceG) (by simp [grainTurnRowGates])
  simp only [VmConstraint.holdsVm, gBalLoFeeG, gNonceG, eSelG, eSA, eSB, ePrm, eSub,
    EmittedExpr.eval] at hLo hNon
  rw [hoff] at hLo hNon
  rw [Int.modEq_zero_iff_dvd] at hLo hNon
  refine ⟨by omega, by omega, ?_⟩
  intro j
  have hFj := hcells (state.FIELD_BASE + j.val)
    (by have := j.isLt; simp only [state.FIELD_BASE, STATE_SIZE]; omega)
  have hW := h _ (mem_grainTurnRowGates_slot j)
  cases hj : IsGrainSlot j
  · simp only [grainSlotGate, hj, Bool.false_eq_true, ite_false, VmConstraint.holdsVm, gFieldPass,
      eSA, eSB, eSub, EmittedExpr.eval] at hW
    rw [Int.modEq_zero_iff_dvd] at hW; omega
  · simp only [grainSlotGate, hj, ite_true, VmConstraint.holdsVm, gGrainWrite, eSelG, eSA, eSB,
      ePrm, eSub, EmittedExpr.eval] at hW
    rw [hoff, Int.modEq_zero_iff_dvd] at hW; omega

/-- **Row-level two-tick refusal.** On the active row, a nonce delta of 2 is UNSAT. -/
theorem grainTurn_rejects_double_tick_row (env : VmRowEnv) (hrow : IsGrainTurnRow env)
    (hcanon : GrainRowCanon env)
    (htwo : env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 2) :
    ¬ (∀ c ∈ grainTurnRowGates, c.holdsVm env false false) := by
  intro h
  have hint := (grainTurnVm_faithful env hrow hcanon).mp h
  have := hint.2.2.1
  omega

/-- Two canonical representatives congruent mod p are equal. -/
theorem canonEq {a b : ℤ} (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  rwa [Int.ModEq, Int.emod_eq_of_lt ha.1 ha.2, Int.emod_eq_of_lt hb.1 hb.2] at h

/-! ## §3 — the trace: exactly one tick per leg.

The IR-v2 window gate below (`nxt s_g = 0` on every transition) plus the first-row pin make row 0
the only active row. With the selector-valued tick and the nonce continuity the rotation wrap
carries (`.transition NONCE NONCE`), every row after row 0 starts at `pre + 1`. -/

/-- The IR-v2 window gate: no row after row 0 is the active grain row. -/
def grainNoSecondActiveRow : DescriptorIR2.WindowConstraint :=
  { body := .nxt SEL_GRAIN_TURN, onTransition := true }

/-- **`grainTurn_trace_ticks_once`** — on a trace of ≥ 2 rows whose non-last rows satisfy the row
gates, the window gate and nonce continuity, and whose first row satisfies the first-row pin, every
row `k ≥ 1` starts at exactly `pre + 1`, where `pre` is row 0's before-nonce. In particular the
before-block of the LAST row (the block the rotated NEW_COMMIT absorbs on a padded trace) carries
ONE tick, whatever the trace length. -/
theorem grainTurn_trace_ticks_once (t : DescriptorIR2.VmTrace)
    (hlen : 2 ≤ t.rows.length)
    (hgates : ∀ i, i + 1 < t.rows.length →
      ∀ c ∈ grainTurnRowGates, c.holdsVm (DescriptorIR2.envAt t i) false false)
    (hfirst : grainFirstRowPin.holdsVm (DescriptorIR2.envAt t 0) true false)
    (hwin : ∀ i, i + 1 < t.rows.length →
      grainNoSecondActiveRow.holdsAt (DescriptorIR2.envAt t i) false)
    (hcont : ∀ i, i + 1 < t.rows.length →
      (VmConstraint.transition state.NONCE state.NONCE).holdsVm (DescriptorIR2.envAt t i) false false)
    (hcanon : ∀ i, i < t.rows.length →
      (0 ≤ (DescriptorIR2.envAt t i).loc SEL_GRAIN_TURN
        ∧ (DescriptorIR2.envAt t i).loc SEL_GRAIN_TURN < 2013265921)
      ∧ (0 ≤ (DescriptorIR2.envAt t i).loc (sbCol state.NONCE)
        ∧ (DescriptorIR2.envAt t i).loc (sbCol state.NONCE) < 2013265921)
      ∧ (0 ≤ (DescriptorIR2.envAt t i).loc (saCol state.NONCE)
        ∧ (DescriptorIR2.envAt t i).loc (saCol state.NONCE) < 2013265921))
    (hovf : (DescriptorIR2.envAt t 0).loc (sbCol state.NONCE) + 1 < 2013265921) :
    ∀ k, 1 ≤ k → k < t.rows.length →
      (DescriptorIR2.envAt t k).loc (sbCol state.NONCE)
        = (DescriptorIR2.envAt t 0).loc (sbCol state.NONCE) + 1 := by
  -- the per-row nonce gate, read at row `i` with selector value `σ`
  have hnon : ∀ i, i + 1 < t.rows.length →
      (DescriptorIR2.envAt t i).loc (saCol state.NONCE)
        - (DescriptorIR2.envAt t i).loc (sbCol state.NONCE)
        - (DescriptorIR2.envAt t i).loc SEL_GRAIN_TURN ≡ 0 [ZMOD 2013265921] := by
    intro i hi
    have h := hgates i hi (.gate gNonceG) (by simp [grainTurnRowGates])
    simp only [VmConstraint.holdsVm, gNonceG, eSelG, eSA, eSB, eSub, EmittedExpr.eval] at h
    have he : ∀ a b c : ℤ, a + -1 * b + -1 * c = a - b - c := by intros; ring
    rwa [he] at h
  -- continuity: row `i+1` starts where row `i` ended
  have hc : ∀ i, i + 1 < t.rows.length →
      (DescriptorIR2.envAt t (i + 1)).loc (sbCol state.NONCE)
        = (DescriptorIR2.envAt t i).loc (saCol state.NONCE) := by
    intro i hi
    have h := hcont i hi
    simp only [VmConstraint.holdsVm] at h
    have h1 := (hcanon (i + 1) hi).2.1
    have h2 := (hcanon i (by omega)).2.2
    exact canonEq h1 h2 h
  intro k hk1 hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- row 0 is active: s_g = 1 by the first-row pin, so it ticks once
      have hs := hfirst
      simp only [grainFirstRowPin, VmConstraint.holdsVm, eSelG, eSub, EmittedExpr.eval,
        forall_const] at hs
      rw [Int.modEq_zero_iff_dvd] at hs
      have hsel := (hcanon 0 (by omega)).1
      have hsel1 : (DescriptorIR2.envAt t 0).loc SEL_GRAIN_TURN = 1 := by omega
      have h0 := hnon 0 hk
      rw [hsel1, Int.modEq_zero_iff_dvd] at h0
      have ha := (hcanon 0 (by omega)).2.2
      have hb0 := (hcanon 0 (by omega)).2.1
      rw [hc 0 hk]
      omega
    · -- row n ≥ 1 is inactive (window gate at row n-1), so it does not tick
      have hprev := ih hn (by omega)
      have hw := hwin (n - 1) (by omega)
      simp only [grainNoSecondActiveRow, DescriptorIR2.WindowConstraint.holdsAt,
        DescriptorIR2.WindowExpr.eval, ite_true, forall_const] at hw
      have hnxt : (DescriptorIR2.envAt t (n - 1)).nxt SEL_GRAIN_TURN
          = (DescriptorIR2.envAt t n).loc SEL_GRAIN_TURN := by
        simp only [DescriptorIR2.envAt]
        rw [Nat.sub_add_cancel hn]
      rw [hnxt, Int.modEq_zero_iff_dvd] at hw
      have hsel := (hcanon n (by omega)).1
      have hsel0 : (DescriptorIR2.envAt t n).loc SEL_GRAIN_TURN = 0 := by omega
      have hn' := hnon n hk
      rw [hsel0, Int.modEq_zero_iff_dvd] at hn'
      have ha := (hcanon n (by omega)).2.2
      have hb := (hcanon n (by omega)).2.1
      rw [hc n hk]
      omega

/-- **THE TWO-TICK FORGERY IS REFUSED (trace level).** No trace satisfying the descriptor's
constraints ends (last row's before-block) at `pre + 2`. -/
theorem grainTurn_refuses_two_ticks (t : DescriptorIR2.VmTrace)
    (hlen : 2 ≤ t.rows.length)
    (hgates : ∀ i, i + 1 < t.rows.length →
      ∀ c ∈ grainTurnRowGates, c.holdsVm (DescriptorIR2.envAt t i) false false)
    (hfirst : grainFirstRowPin.holdsVm (DescriptorIR2.envAt t 0) true false)
    (hwin : ∀ i, i + 1 < t.rows.length →
      grainNoSecondActiveRow.holdsAt (DescriptorIR2.envAt t i) false)
    (hcont : ∀ i, i + 1 < t.rows.length →
      (VmConstraint.transition state.NONCE state.NONCE).holdsVm (DescriptorIR2.envAt t i) false false)
    (hcanon : ∀ i, i < t.rows.length →
      (0 ≤ (DescriptorIR2.envAt t i).loc SEL_GRAIN_TURN
        ∧ (DescriptorIR2.envAt t i).loc SEL_GRAIN_TURN < 2013265921)
      ∧ (0 ≤ (DescriptorIR2.envAt t i).loc (sbCol state.NONCE)
        ∧ (DescriptorIR2.envAt t i).loc (sbCol state.NONCE) < 2013265921)
      ∧ (0 ≤ (DescriptorIR2.envAt t i).loc (saCol state.NONCE)
        ∧ (DescriptorIR2.envAt t i).loc (saCol state.NONCE) < 2013265921))
    (hovf : (DescriptorIR2.envAt t 0).loc (sbCol state.NONCE) + 1 < 2013265921)
    (hforged : (DescriptorIR2.envAt t (t.rows.length - 1)).loc (sbCol state.NONCE)
        = (DescriptorIR2.envAt t 0).loc (sbCol state.NONCE) + 2) :
    False := by
  have := grainTurn_trace_ticks_once t hlen hgates hfirst hwin hcont hcanon hovf
    (t.rows.length - 1) (by omega) (by omega)
  omega

/-! ## §4 — the executor link: the active row IS the executor's per-turn grain transition.

The executor side is the real Lean model of `execute.rs`'s turn: `Admission.runTurn` (admission →
`commitPrologue` = Phase 1 fee debit + ONE nonce tick → rollback-able body) with the body the
per-asset full executor `execFullTurnA` over the five `setFieldA` writes in the minter's commit
order, followed on commit by `distributeFee` (Phase 3). The developer slot `j` is the record field
`slotName j` (the `EffectVmEmitSetField.unify_setField_exec` convention). -/

/-- The grain body in the executor's commit order: `calls_made` (4, gateway-prepended), then
`history_root` (3), `consumed` (5), `heap_root` (6), `action` (7). -/
def grainBody (w : CellId) (v : Fin 8 → Int) : List FullActionA :=
  ([4, 3, 5, 6, 7] : List (Fin 8)).map (fun j => .setFieldA w w (slotName j) (v j))

/-- **The executor's per-turn grain transition**: admission, Phase-1 prologue on the agent (= the
worker cell), the body, and Phase-3 fee distribution on a committing body. -/
def grainTurnExec (ctx : AdmCtx) (h : TurnHdr) (v : Fin 8 → Int) (s : RecChainedState) :
    Option RecChainedState :=
  runTurn ctx h s (fun s₁ =>
    (execFullTurnA s₁ (grainBody h.agent v)).map (fun s₂ => distributeFee ctx s₂ h.fee))

/-- The worker cell's projection onto the EffectVM state block: balance, nonce, the eight slot
fields. (`balHi`/`capRoot`/`reserved`/`commit` carry no record-kernel analogue here, the same
convention as `EffectVmEmitSetField.cellProjF`.) -/
def grainProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := nonceOf (k.cell c)
  fields   := fun j => fieldOf (slotName j) (k.cell c)
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The row's state-block columns encode `(pre, post)`. -/
def RowEncodesGrain (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ j : Fin 8, env.loc (sbCol (state.FIELD_BASE + j.val)) = pre.fields j)
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ j : Fin 8, env.loc (saCol (state.FIELD_BASE + j.val)) = post.fields j)

/-! ### record-level frame lemmas (restated locally; this module edits nothing upstream). -/

theorem fieldOf_setField_ne' (f g : FieldName) (cell : Value) (v : Int) (hfg : g ≠ f) :
    fieldOf g (setField f cell (.int v)) = fieldOf g cell := by
  have hfg' : (f == g) = false := by
    rw [beq_eq_false_iff_ne]; exact fun h => hfg h.symm
  have hlist : ∀ fs : List (FieldName × Value),
      ((setField.setFieldList f fs (.int v)).find? (fun p => p.1 == g))
        = fs.find? (fun p => p.1 == g) := by
    intro fs
    induction fs with
    | nil => simp [setField.setFieldList, List.find?, hfg']
    | cons hd tl ih =>
        obtain ⟨kk, x⟩ := hd
        simp only [setField.setFieldList]
        by_cases hk : (kk == f) = true
        · have hkk : kk = f := by simpa using hk
          rw [if_pos hk]
          simp only [List.find?_cons, hfg', hkk]
        · rw [if_neg hk]
          by_cases hg : (kk == g) = true
          · simp only [List.find?_cons, hg]
          · rw [List.find?_cons_of_neg (by simpa using hg),
                List.find?_cons_of_neg (by simpa using hg)]
            exact ih
  unfold fieldOf Value.scalar Value.field
  cases cell with
  | record fs => simp only [setField]; rw [hlist fs]
  | int n => simp [setField, List.find?, hfg']
  | dig d => simp [setField, List.find?, hfg']
  | sym s => simp [setField, List.find?, hfg']

/-- Read-after-write, both cases. -/
theorem fieldOf_setField_eq (f g : FieldName) (cell : Value) (v : Int) :
    fieldOf g (setField f cell (.int v)) = if g = f then v else fieldOf g cell := by
  by_cases h : g = f
  · subst h; rw [if_pos rfl]; exact setField_fieldOf g cell v
  · rw [if_neg h]; exact fieldOf_setField_ne' f g cell v h

/-- `setNonce` IS the `nonce` field write. -/
theorem setNonce_eq_setField (cell : Value) (n : Int) :
    setNonce cell n = setField nonceField cell (.int n) := by
  have hl : ∀ fs : List (FieldName × Value),
      setNonce.setNonceList fs n = setField.setFieldList nonceField fs (.int n) := by
    intro fs
    induction fs with
    | nil => rfl
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setNonce.setNonceList, setField.setFieldList, ih]
  cases cell with
  | record fs => simp only [setNonce, setField, hl]
  | int _ => rfl
  | dig _ => rfl
  | sym _ => rfl

/-- `setBalance` IS the `balance` field write. -/
theorem setBalance_eq_setField (cell : Value) (n : Int) :
    setBalance cell n = setField balanceField cell (.int n) := by
  have hl : ∀ fs : List (FieldName × Value),
      setBalance.setBalanceList fs n = setField.setFieldList balanceField fs (.int n) := by
    intro fs
    induction fs with
    | nil => rfl
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [setBalance.setBalanceList, setField.setFieldList, ih]
  cases cell with
  | record fs => simp only [setBalance, setField, hl]
  | int _ => rfl
  | dig _ => rfl
  | sym _ => rfl

theorem slotName_inj (a b : Fin 8) : slotName a = slotName b ↔ a = b := by
  constructor
  · intro h; fin_cases a <;> fin_cases b <;> first | rfl | (exact absurd h (by decide))
  · intro h; rw [h]

theorem slotName_ne_nonce (j : Fin 8) : slotName j ≠ nonceField := by
  fin_cases j <;> decide

/-- One committed `setFieldA` on cell `w` writes `w`'s record exactly. -/
theorem execFullA_setFieldA_cell {s s' : RecChainedState} {w : CellId} {f : FieldName} {v : Int}
    (h : execFullA s (.setFieldA w w f v) = some s') :
    s'.kernel.cell w = setField f (s.kernel.cell w) (.int v) := by
  have hspec := (execFullA_setFieldA_iff_spec s w w f v s').mp h
  rw [hspec.2.2.1]
  simp only [setFieldCellMap, if_pos]

theorem execFullTurnA_cons_some {s s' : RecChainedState} {a : FullActionA}
    {rest : List FullActionA} (h : execFullTurnA s (a :: rest) = some s') :
    ∃ s1, execFullA s a = some s1 ∧ execFullTurnA s1 rest = some s' := by
  unfold execFullTurnA at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · exact absurd h (by simp)

/-- The worker cell after a committed grain body, as an explicit record term. -/
theorem grainBody_cell {s₁ s₂ : RecChainedState} {w : CellId} {v : Fin 8 → Int}
    (h : execFullTurnA s₁ (grainBody w v) = some s₂) :
    s₂.kernel.cell w =
      setField (slotName 7) (setField (slotName 6) (setField (slotName 5)
        (setField (slotName 3) (setField (slotName 4) (s₁.kernel.cell w) (.int (v 4)))
          (.int (v 3))) (.int (v 5))) (.int (v 6))) (.int (v 7)) := by
  simp only [grainBody, List.map_cons, List.map_nil] at h
  obtain ⟨a, ha, h⟩ := execFullTurnA_cons_some h
  obtain ⟨b, hb, h⟩ := execFullTurnA_cons_some h
  obtain ⟨c, hc, h⟩ := execFullTurnA_cons_some h
  obtain ⟨d, hd, h⟩ := execFullTurnA_cons_some h
  obtain ⟨e, he, h⟩ := execFullTurnA_cons_some h
  simp only [execFullTurnA, Option.some.injEq] at h
  subst h
  rw [execFullA_setFieldA_cell he, execFullA_setFieldA_cell hd, execFullA_setFieldA_cell hc,
    execFullA_setFieldA_cell hb, execFullA_setFieldA_cell ha]

/-- **`grainTurn_row_agrees_executor` — THE AGREEMENT.** Let the executor commit a grain turn on
worker `w = h.agent` (admission passes, the body commits; the proposer and treasury are other
cells). Let a row satisfy the grain gates on the active row, encode the worker's pre-turn
projection as its before-block, and carry the turn's written values and `turn.fee` in its params.
Then the turn's executor result is `distributeFee … s₂`, and the row's after-block equals the
worker cell's post-turn projection: balance `pre − fee`, nonce `pre + 1` (ONE tick), and all eight
slot fields. -/
theorem grainTurn_row_agrees_executor
    (ctx : AdmCtx) (h : TurnHdr) (v : Fin 8 → Int) (s s₂ : RecChainedState) (p t : CellId)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hwp : h.agent ≠ p) (hwt : h.agent ≠ t)
    (hadm : admissible ctx h s = true)
    (hbody : execFullTurnA (commitPrologue s h.agent h.fee) (grainBody h.agent v) = some s₂)
    (env : VmRowEnv) (post : CellState)
    (hrow : IsGrainTurnRow env) (hcanon : GrainRowCanon env)
    (henc : RowEncodesGrain env (grainProj s.kernel h.agent) post)
    (hval : ∀ j : Fin 8, IsGrainSlot j = true → env.loc (prmCol (grainParam j)) = v j)
    (hfee : env.loc (prmCol FEE_PARAM) = h.fee)
    (hsat : ∀ c ∈ grainTurnRowGates, c.holdsVm env false false) :
    grainTurnExec ctx h v s = some (distributeFee ctx s₂ h.fee)
    ∧ post.balLo = balOf ((distributeFee ctx s₂ h.fee).kernel.cell h.agent)
    ∧ post.nonce = nonceOf ((distributeFee ctx s₂ h.fee).kernel.cell h.agent)
    ∧ ∀ j : Fin 8,
        post.fields j = fieldOf (slotName j) ((distributeFee ctx s₂ h.fee).kernel.cell h.agent) := by
  obtain ⟨hLo, _, hNon, _, _, hW, hP⟩ := (grainTurnVm_faithful env hrow hcanon).mp hsat
  obtain ⟨ebLo, ebN, ebF, eaLo, eaN, eaF⟩ := henc
  -- the executor's post cell
  have hcell : (distributeFee ctx s₂ h.fee).kernel.cell h.agent = s₂.kernel.cell h.agent :=
    distributeFee_frame ctx s₂ h.fee p t h.agent hp ht hwp hwt
  have hpro : (commitPrologue s h.agent h.fee).kernel.cell h.agent
      = setField nonceField
          (setField balanceField (s.kernel.cell h.agent)
            (.int (balOf (s.kernel.cell h.agent) - h.fee)))
          (.int (nonceOf (s.kernel.cell h.agent) + 1)) := by
    simp only [commitPrologue, prologueCell, if_pos, setNonce_eq_setField, setBalance_eq_setField]
  rw [hcell, grainBody_cell hbody, hpro]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [grainTurnExec, runTurn, if_pos hadm, hbody, Option.map_some]
  · -- balance: pre − fee
    rw [← eaLo, hLo, ebLo, hfee]
    show _ = fieldOf balanceField _
    simp only [fieldOf_setField_eq]
    simp only [show balanceField ≠ nonceField by decide, ite_false, ite_true]
    rfl
  · -- nonce: pre + 1, one tick
    rw [← eaN, hNon, ebN]
    show _ = fieldOf nonceField _
    simp only [fieldOf_setField_eq, ite_true]
    rfl
  · intro j
    rw [← eaF j]
    have hb : slotName j ≠ balanceField := slotName_ne_balance j
    have hn : slotName j ≠ nonceField := slotName_ne_nonce j
    simp only [fieldOf_setField_eq, slotName_inj, hb, hn, ite_false]
    cases hj : IsGrainSlot j
    · rw [hP j hj, ebF j]
      have hlt : j.val < 3 := by simpa [IsGrainSlot] using hj
      have h7 : j ≠ 7 := fun e => by subst e; simp at hlt
      have h6 : j ≠ 6 := fun e => by subst e; simp at hlt
      have h5 : j ≠ 5 := fun e => by subst e; simp at hlt
      have h4 : j ≠ 4 := fun e => by subst e; simp at hlt
      have h3 : j ≠ 3 := fun e => by subst e; simp at hlt
      simp only [h7, h6, h5, h4, h3, ite_false]
      rfl
    · rw [hW j hj, hval j hj]
      have hge : 3 ≤ j.val := by simpa [IsGrainSlot] using hj
      fin_cases j <;> first | (exact absurd hge (by decide)) | simp

#assert_axioms grainTurnVm_faithful
#assert_axioms grainTurn_inactive_row_frozen
#assert_axioms grainTurn_rejects_double_tick_row
#assert_axioms grainTurn_trace_ticks_once
#assert_axioms grainTurn_refuses_two_ticks
#assert_axioms grainTurn_row_agrees_executor

end Dregg2.Circuit.Emit.EffectVmEmitGrainTurn
