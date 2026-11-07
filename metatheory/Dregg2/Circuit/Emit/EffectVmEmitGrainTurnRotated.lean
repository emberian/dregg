/-
# Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated — the R=24 rotated member for the grain turn.

`grainTurnVmDescriptor2R24` is assembled exactly as the deployed `setFieldVmDescriptor2-{slot}R24`
members are (`EffectVmEmitRotationV3.v3RegistryBare`), generalised from one written slot to the five
grain slots, plus the published fee:
  * `rotateV3` + the authority continuity weld (`frozenAuthorityColEqs`), with the fields completion
    freezes kept ONLY for the unwritten slots 0..2 (24 freezes; the per-slot member keeps 56);
  * the FEE PIN: `param5` (`turn.fee`) pinned on the first row to the first PI slot past the four
    rotated commit pins (`ROT_PI_COUNT`, the `transferFeeV3` / `ROT_FEE_PI` precedent), so the
    verifier reads the fee the proof debited;
  * `graduateV1Wide` (the 15-bit fee range rides the wide graduation's 15-bit table);
  * `withSelectorGate SEL_GRAIN_TURN` (a row is a NoOp pad or the grain row);
  * the IR-v2 window gate `grainNoSecondActiveRow` (no active row after row 0);
  * `withSetFieldCompletionPins j` for each grain slot `j` (8 lanes × 5 slots = 40 tail PIs
    publishing the high lanes of the five written 32-byte values);
  * `withDfaRcPins` outermost (`grainTurnHost`), as every v3Registry member;
  * `wideAppend` at the face base (`grainTurnWide`), as `v3RegistryWide`.

`grainTurnHost` is emitted by `metatheory/EmitRotationV3.lean` and `grainTurnWide` by
`metatheory/EmitWideRegistryProbe.lean` (a TAIL member after `supplyMint`, through the same
`emitCompact` chain), keyed `grainTurnVmDescriptor2R24`.

§O1 closes the rotated lift: any `Satisfied2` witness of the host OR the wide member yields every
hypothesis `grainTurn_trace_ticks_once` consumes, by constraint membership (`graduateV1Wide` keeps each
face constraint as `.base c`, every wrapper only appends, and `wideAppend` drops only the two legacy
1-felt commit pins, which the face does not carry). §O2 closes the wrap row on the emitted
(last-row-hardened) form: the AFTER nonce of the last row, the one the NEW_COMMIT anchor absorbs, is
the genesis nonce plus one (`hardened_head_ticks_once`).
-/
import Dregg2.Circuit.Emit.EffectVmEmitGrainTurn
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide
import Dregg2.Circuit.Emit.LastRowFrameHardening

namespace Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend isLegacyCommitPin1)
open Dregg2.Circuit.Emit.EffectVmEmitGrainTurn

set_option autoImplicit false

/-- The five grain slots. -/
def grainSlots : List (Fin 8) := [3, 4, 5, 6, 7]

#guard grainSlots == (List.finRange 8).filter (fun j => IsGrainSlot j)

/-- The fields completion freezes for the UNWRITTEN slots only (0..2): every completion lane not
owned by a grain slot stays frozen BEFORE↔AFTER. -/
def fieldsCompletionFreezesExceptGrain (w : Nat) : List VmConstraint :=
  (fieldsCompletionOffs.filter
      (fun off => !(grainSlots.any (fun j => (fieldsSlotLanes j).contains off)))).map
    (fun off => colEq (w + off) (w + AFTER_BLOCK_OFF + off))

#guard (fieldsCompletionFreezesExceptGrain 186).length == 24

/-- `rotateV3` + the authority continuity weld + the unwritten-slot completion freezes + the fee pin
(first row, PI slot `(rotateV3 d).piCount`). -/
def rotateV3FrozenAuthorityGrain (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount := r.piCount + 1
    constraints :=
      r.constraints
        ++ (frozenAuthorityColEqs d.traceWidth ++ fieldsCompletionFreezesExceptGrain d.traceWidth
          ++ [.piBinding .first (prmCol FEE_PARAM) r.piCount]) }

/-- The fee PI slot: the first slot past the four rotated commit pins. -/
def GRAIN_FEE_PI : Nat := (rotateV3 grainTurnVmDescriptor).piCount

#guard GRAIN_FEE_PI == pi.V1_PI_COUNT + 4
#guard GRAIN_FEE_PI == ROT_FEE_PI

/-- The graduated rotated core. -/
def grainTurnV3Core : EffectVmDescriptor2 :=
  graduateV1Wide (rotateV3FrozenAuthorityGrain grainTurnVmDescriptor)

/-- Append the single-active-row window gate. -/
def withGrainWindow (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with constraints := g.constraints ++ [.windowGate grainNoSecondActiveRow] }

/-- Publish the completion lanes of all five written slots. -/
def withGrainCompletionPins (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  grainSlots.foldl (fun acc j => withSetFieldCompletionPins j acc) g

/-- **`grainTurnVmDescriptor2R24`** — the single-tick multi-field grain member (bare, pre-rc). -/
def grainTurnVmDescriptor2R24 : EffectVmDescriptor2 :=
  withGrainCompletionPins (withGrainWindow (withSelectorGate SEL_GRAIN_TURN grainTurnV3Core))

/-- The narrow registry form (the `v3Registry` outermost rc wrap). -/
def grainTurnHost : EffectVmDescriptor2 := withDfaRcPins grainTurnVmDescriptor2R24

/-- The BEFORE limbs sit at the face width (the same `bb` every setField member uses). -/
def grainTurnBB : Nat := grainTurnVmDescriptor.traceWidth

/-- The wide registry form (`v3RegistryWide`'s `wideAppend host bb (bb + B_SPAN)`). -/
def grainTurnWide : EffectVmDescriptor2 := wideAppend grainTurnHost grainTurnBB (grainTurnBB + B_SPAN)

#guard grainTurnV3Core.piCount == GRAIN_FEE_PI + 1
#guard grainTurnVmDescriptor2R24.piCount == GRAIN_FEE_PI + 1 + 40
#guard grainTurnHost.piCount == GRAIN_FEE_PI + 1 + 40 + 4
#guard grainTurnWide.piCount == GRAIN_FEE_PI + 1 + 40 + 4 + 16
#guard grainTurnV3Core.traceWidth == (setFieldV3 3).traceWidth
#guard grainTurnBB == (setFieldTickFace 3).traceWidth
#guard grainTurnVmDescriptor2R24.constraints.length
  == grainTurnV3Core.constraints.length + 1 + 1 + 40

/-! ## §O1 — the rotated lift, by constraint membership. -/

/-- Every face constraint is a gate, a first-row boundary or a transition: none is a PI binding. -/
def notPiBinding : VmConstraint → Bool
  | .piBinding _ _ _ => false
  | _ => true

theorem face_no_piBinding_all : grainTurnVmDescriptor.constraints.all notPiBinding = true := by
  decide

theorem face_no_piBinding : ∀ c ∈ grainTurnVmDescriptor.constraints, notPiBinding c = true :=
  List.all_eq_true.mp face_no_piBinding_all

/-- Every face constraint survives into the graduated core as `.base c`. -/
theorem face_mem_core (c : VmConstraint) (hc : c ∈ grainTurnVmDescriptor.constraints) :
    VmConstraint2.base c ∈ grainTurnV3Core.constraints := by
  unfold grainTurnV3Core graduateV1Wide
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨c, ?_, rfl⟩
  show c ∈ (rotateV3 grainTurnVmDescriptor).constraints ++ _
  apply List.mem_append_left
  show c ∈ grainTurnVmDescriptor.constraints ++ _
  exact List.mem_append_left _ hc

theorem mem_withGrainCompletionPins {x : VmConstraint2} :
    ∀ (l : List (Fin 8)) (g : EffectVmDescriptor2), x ∈ g.constraints →
      x ∈ (l.foldl (fun acc j => withSetFieldCompletionPins j acc) g).constraints
  | [], _, h => h
  | j :: l, g, h => by
      simp only [List.foldl_cons]
      apply mem_withGrainCompletionPins l
      rw [withSetFieldCompletionPins_constraints]
      exact List.mem_append_left _ h

/-- The bare member keeps every face constraint and the window gate. -/
theorem r24_mem (x : VmConstraint2)
    (hx : x ∈ grainTurnV3Core.constraints ∨ x = .windowGate grainNoSecondActiveRow) :
    x ∈ grainTurnVmDescriptor2R24.constraints := by
  unfold grainTurnVmDescriptor2R24 withGrainCompletionPins
  apply mem_withGrainCompletionPins
  show x ∈ (withSelectorGate SEL_GRAIN_TURN grainTurnV3Core).constraints ++ _
  rcases hx with hx | rfl
  · apply List.mem_append_left
    show x ∈ grainTurnV3Core.constraints ++ _
    exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

theorem host_mem (x : VmConstraint2) (hx : x ∈ grainTurnVmDescriptor2R24.constraints) :
    x ∈ grainTurnHost.constraints := by
  unfold grainTurnHost withDfaRcPins
  exact List.mem_append_left _ hx

theorem wide_mem (x : VmConstraint2) (hx : x ∈ grainTurnHost.constraints)
    (hnot : isLegacyCommitPin1 grainTurnBB (grainTurnBB + B_SPAN) x = false) :
    x ∈ grainTurnWide.constraints := by
  unfold grainTurnWide wideAppend
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_filter.mpr ⟨hx, by simp [hnot]⟩

/-- The descriptor-membership premises of the lift, for an arbitrary emitted member `D`. -/
structure CarriesGrainFace (D : EffectVmDescriptor2) : Prop where
  face : ∀ c ∈ grainTurnVmDescriptor.constraints, VmConstraint2.base c ∈ D.constraints
  window : VmConstraint2.windowGate grainNoSecondActiveRow ∈ D.constraints

theorem host_carries : CarriesGrainFace grainTurnHost where
  face c hc := host_mem _ (r24_mem _ (Or.inl (face_mem_core c hc)))
  window := host_mem _ (r24_mem _ (Or.inr rfl))

theorem wide_carries : CarriesGrainFace grainTurnWide where
  face c hc := wide_mem _ (host_carries.face c hc) (by
    have h := face_no_piBinding c hc
    cases c <;> simp_all [notPiBinding, isLegacyCommitPin1])
  window := wide_mem _ host_carries.window (by simp [isLegacyCommitPin1])

theorem gate_holds_any_first {env : VmRowEnv} {c : VmConstraint} (hc : c ∈ grainTurnRowGates)
    (b : Bool) (h : c.holdsVm env b false) : c.holdsVm env false false := by
  simp only [grainTurnRowGates, List.mem_append, List.mem_cons, List.mem_map, List.mem_finRange,
    List.not_mem_nil, or_false, true_and] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, rfl⟩
  all_goals first
    | exact h
    | (cases hj : IsGrainSlot j <;>
        simp only [grainSlotGate, hj, Bool.false_eq_true, ite_true, ite_false] at h ⊢ <;> exact h)

/-- **O1 — THE ROTATED LIFT.** A `Satisfied2` witness of ANY descriptor that carries the grain face
and the window gate (the host and the wide member both do: `host_carries`, `wide_carries`) forces
the single tick: every row `k ≥ 1` starts at the row-0 before-nonce plus one. -/
theorem carries_ticks_once (D : EffectVmDescriptor2) (hD : CarriesGrainFace D)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash D minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : ∀ i, i < t.rows.length →
      (0 ≤ (envAt t i).loc SEL_GRAIN_TURN ∧ (envAt t i).loc SEL_GRAIN_TURN < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (sbCol state.NONCE)
        ∧ (envAt t i).loc (sbCol state.NONCE) < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (saCol state.NONCE)
        ∧ (envAt t i).loc (saCol state.NONCE) < 2013265921))
    (hovf : (envAt t 0).loc (sbCol state.NONCE) + 1 < 2013265921) :
    ∀ k, 1 ≤ k → k < t.rows.length →
      (envAt t k).loc (sbCol state.NONCE) = (envAt t 0).loc (sbCol state.NONCE) + 1 := by
  have hrow : ∀ i, i + 1 < t.rows.length → ∀ c ∈ grainTurnVmDescriptor.constraints,
      c.holdsVm (envAt t i) (i == 0) false := by
    intro i hi c hc
    have h := hsat.rowConstraints i (by omega) _ (hD.face c hc)
    have hl : (i + 1 == t.rows.length) = false := by simp; omega
    simpa [VmConstraint2.holdsAt, hl] using h
  refine grainTurn_trace_ticks_once t hlen ?_ ?_ ?_ ?_ hcanon hovf
  · intro i hi c hc
    exact gate_holds_any_first hc _ (hrow i hi c (by
      unfold grainTurnVmDescriptor; exact List.mem_append_left _ (List.mem_append_left _ hc)))
  · have h := hrow 0 (by omega) grainFirstRowPin firstRowPin_mem
    simpa using h
  · intro i hi
    have h := hsat.rowConstraints i (by omega) _ hD.window
    have hl : (i + 1 == t.rows.length) = false := by simp; omega
    simpa [VmConstraint2.holdsAt, hl] using h
  · intro i hi
    have h := hrow i hi _ nonce_transition_mem
    simpa [VmConstraint.holdsVm] using h

/-- The two-tick forgery is refused on the WIDE member itself. -/
theorem wide_refuses_two_ticks (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash grainTurnWide minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : ∀ i, i < t.rows.length →
      (0 ≤ (envAt t i).loc SEL_GRAIN_TURN ∧ (envAt t i).loc SEL_GRAIN_TURN < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (sbCol state.NONCE)
        ∧ (envAt t i).loc (sbCol state.NONCE) < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (saCol state.NONCE)
        ∧ (envAt t i).loc (saCol state.NONCE) < 2013265921))
    (hovf : (envAt t 0).loc (sbCol state.NONCE) + 1 < 2013265921)
    (hforged : (envAt t (t.rows.length - 1)).loc (sbCol state.NONCE)
        = (envAt t 0).loc (sbCol state.NONCE) + 2) :
    False := by
  have := carries_ticks_once grainTurnWide wide_carries hash minit mfin maddrs t hsat hlen hcanon
    hovf (t.rows.length - 1) (by omega) (by omega)
  omega

/-! ## §O2 — the wrap row, closed by the deployed last-row hardening.

Every emitted member goes through `LastRowFrameHardening.hardenLastRow` (EmitRotationV3.lean,
EmitWideRegistryProbe.lean `emitCompact`): each `.base (.gate b)` is lifted onto the WHOLE domain,
so on the LAST row the grain gates bind too. There the selector is 0 (the window gate at the row
before), so the nonce gate freezes it, and the last row's AFTER nonce — the block the rotated
NEW_COMMIT anchor absorbs — is the row-0 before-nonce plus ONE. -/
theorem hardened_head_ticks_once (D : EffectVmDescriptor2) (hD : CarriesGrainFace D)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (Dregg2.Circuit.Emit.LastRowFrameHardening.hardenLastRow D)
      minit mfin maddrs t)
    (hlen : 2 ≤ t.rows.length)
    (hcanon : ∀ i, i < t.rows.length →
      (0 ≤ (envAt t i).loc SEL_GRAIN_TURN ∧ (envAt t i).loc SEL_GRAIN_TURN < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (sbCol state.NONCE)
        ∧ (envAt t i).loc (sbCol state.NONCE) < 2013265921)
      ∧ (0 ≤ (envAt t i).loc (saCol state.NONCE)
        ∧ (envAt t i).loc (saCol state.NONCE) < 2013265921))
    (hovf : (envAt t 0).loc (sbCol state.NONCE) + 1 < 2013265921) :
    (envAt t (t.rows.length - 1)).loc (saCol state.NONCE)
      = (envAt t 0).loc (sbCol state.NONCE) + 1 := by
  have hbase := Dregg2.Circuit.Emit.LastRowFrameHardening.satisfied2_of_hardened hsat
  have hbefore := carries_ticks_once D hD hash minit mfin maddrs t hbase hlen hcanon hovf
    (t.rows.length - 1) (by omega) (by omega)
  -- the selector is 0 on the last row: the window gate at the row before it
  have hw := hbase.rowConstraints (t.rows.length - 2) (by omega) _ hD.window
  have hl : (t.rows.length - 2 + 1 == t.rows.length) = false := by simp; omega
  simp only [VmConstraint2.holdsAt, grainNoSecondActiveRow, WindowConstraint.holdsAt,
    WindowExpr.eval, ite_true, hl, forall_const] at hw
  have hnxt : (envAt t (t.rows.length - 2)).nxt SEL_GRAIN_TURN
      = (envAt t (t.rows.length - 1)).loc SEL_GRAIN_TURN := by
    simp only [envAt]
    rw [show t.rows.length - 2 + 1 = t.rows.length - 1 by omega]
  rw [hnxt, Int.modEq_zero_iff_dvd] at hw
  have hsel := (hcanon (t.rows.length - 1) (by omega)).1
  have hsel0 : (envAt t (t.rows.length - 1)).loc SEL_GRAIN_TURN = 0 := by omega
  -- the hardened nonce gate binds on the last row
  have hg := Dregg2.Circuit.Emit.LastRowFrameHardening.hardened_gate_binds_on_last_row hsat
    (by omega) (hD.face _ (by
      unfold grainTurnVmDescriptor
      exact List.mem_append_left _ (List.mem_append_left _ (by simp [grainTurnRowGates]))))
      (body := gNonceG)
  simp only [gNonceG, eSelG, Dregg2.Circuit.Emit.EffectVmEmitTransfer.eSub,
    Dregg2.Circuit.Emit.EffectVmEmitTransfer.eSA, Dregg2.Circuit.Emit.EffectVmEmitTransfer.eSB,
    Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at hg
  rw [hsel0, Int.modEq_zero_iff_dvd] at hg
  have ha := (hcanon (t.rows.length - 1) (by omega)).2.2
  have hb := (hcanon (t.rows.length - 1) (by omega)).2.1
  omega

#assert_axioms hardened_head_ticks_once
#assert_axioms face_no_piBinding
#assert_axioms wide_carries
#assert_axioms carries_ticks_once
#assert_axioms wide_refuses_two_ticks

end Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated
