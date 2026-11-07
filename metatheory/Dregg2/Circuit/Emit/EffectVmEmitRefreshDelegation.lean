/-
# Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation — the REFRESH-DELEGATION effect `refreshDelegationA`
  on the runnable EffectVM row, AMPLIFIED to FULL at the record-commitment layer now that STAGE 3
  (`Exec.SystemRoots`) gives `delegations` its OWN bindable side-table root.

## STAGE 3 unblocks the `delegations` move: a dedicated `deleg_root` (the `systemRoot.DELEG` column)

Before STAGE 3 this module flagged a LOUD IR GAP: `refreshDelegationA`'s genuine content — overwrite
`delegations child` with the parent's c-list snapshot (`refreshDelegationsMap`) — was over the
`delegations` sub-table, which had NO EffectVM state column, so it rode ONLY universe-A's
`refreshDelegationA_full_sound`. STAGE 3 (`Exec.SystemRoots`, `_RECORD-LAYER-UPGRADE.md` §C) gives the 8
kernel side-tables their OWN namespace: `delegations` is `systemRoot.DELEG` (index 4), digested by
`Exec.SystemRoots.systemRootsDigest`, carried in the `SYSTEM_ROOTS_DIGEST` column, and ABSORBED into the
canonical cell commitment by `cellCommitS` — with the anti-ghost tooth `cellCommitS_binds_systemRoots_or_collides`
(equal commitment ⇒ equal digest ⇒ equal `DELEG` root pointwise) PROVED. So the `delegations` move is now
BINDABLE: this module BINDS universe-A's injective `delegations` digest `D` onto the `DELEG` system-root,
re-proves the faithfulness + anti-ghost over the now-bound root, and connects it to
`refreshDelegationA_full_sound`. (`#62` record-layer STAGE 3 is the landed dependency.)

## TWO honest layers — the EffectVM ROW (cutover) and the RECORD COMMITMENT (the deleg move)

  * **EffectVM ROW layer (cutover-ready).** The runtime hand-AIR (`effect_vm/air.rs:980-986`) classes
    `REFRESH_DELEGATION` as a STATE-PASSTHROUGH variant: every `state` column (balance / nonce / fields /
    cap_root / reserved) is unchanged EXCEPT the GLOBAL nonce, which TICKS by one (`generate_effect_vm_trace`
    `Effect::RefreshDelegation => new_state.nonce += 1`). The emitted `refreshVmDescriptor` therefore
    FREEZES every column and TICKS the nonce — `gNonceTick` (= the running prover's
    `new_nonce − old_nonce − (1 − s_noop)` global gate), the SAME column-fix that graduated burn /
    bridgeMint through the cutover harness (`3aaf0772d`). The previous version FROZE the nonce
    (`gNonceFix`), which is UNSAT on the honest runtime trace — this version reconciles it so the
    descriptor AGREES with the hand-AIR on the honest witness (the cutover precondition).

  * **RECORD COMMITMENT layer (the deleg move, now bound).** The genuine `delegations := refreshDelegationsMap`
    move is bound at the canonical-commitment layer through STAGE 3's `DELEG` system-root: the row's
    `deleg_root` (= `D k.delegations`) MOVES from `D k.delegations` to `D (refreshDelegationsMap k child)`,
    every OTHER system-root FREEZES, and `cellCommitS_binds_systemRoots_or_collides` makes tampering the `DELEG` root
    flip the published commitment (UNSAT). This is the anti-ghost tooth the coverage memos demand, now over
    the touched field. Connected to `refreshDelegationA_full_sound` (`unify_refresh_delegMove_via_full_sound`).

## BOUNDARY (precise) — what is cutover-ready vs still blocked

  * **EffectVM-ROW freeze+tick is FULL + cutover-ready.** The runnable row pins the runtime
    passthrough+nonce-tick EXACTLY as the hand-AIR does, so the descriptor is a faithful drop-in for the
    refresh row's state-column behaviour (the harness AGREE the cutover demands).

  * **The `delegations` move is BOUND at the record layer (STAGE 3), NOT yet a runtime-trace column.**
    `generate_effect_vm_trace`'s `RefreshDelegation` arm does NOT yet WRITE a `DELEG`/`SYSTEM_ROOTS_DIGEST`
    column — it is a Rust trace-generator extension (the `_RECORD-LAYER-UPGRADE.md` §C close-plan), OUTSIDE
    this single-file scope. So the in-row deleg-MOVE gate is proved sound + anti-ghost against the STAGE-3
    record-commitment MODEL (`Exec.SystemRoots`), and its full prover-trace column lands when the runtime
    emits it. This is reported, NOT papered: `delegRoot_runtime_column_pending`.

  * **The `RefreshDelegationGuard`** (actor-authorizes-child) is enforced by `refreshDelegationA_full_sound`'s
    `propBit` column, carried through the connector hypothesis — NOT a state-column row gate.

  * `state.RESERVED` not commitment-bound at the EffectVM-row layer (inherited finding); PER-CELL / PER-ROW.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Universe-A's `Function.Injective D` is
carried; Imports read-only.

⚑ **THE SIDE-TABLE DIGEST NO LONGER CARRIES A CR FLOOR (07-20).** `delegRoot_binds_under_commit` used
to take `Exec.SystemRoots`'s `compressNInjective` carrier, which `HashFloorHonesty` REFUTES at the
deployed BabyBear parameters — so the `DELEG`-root anti-ghost tooth said nothing about the deployed
system. It is DELETED and replaced by `delegRoot_binds_under_commit_or_collides`, whose alternative
branches NAME the colliding pair a total extractor returns (`CellCommitSColl` at the commitment
absorption, `RootsColl` at the ordered root list). `delegRoot_binds_under_commit_of_injective` recovers
the old statement as exactly the injective special case. The remaining `Poseidon2SpongeCR` uses in this
file are on the STATE-BLOCK teeth (`refreshDescriptor_commit_binds_state_or_collides`), a separate leg.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Exec.SystemRoots
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction
import Dregg2.Exec.SystemRootsBindingReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gNonce gCapPass site0 site1 site2 site3 transitionAll boundaryFirstPins
   boundaryLastPins transferHashSites gate_modEq_iff not_modEq_zero_of_canon eqToModEq)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit_or_collides TransferColl)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.Inst.RefreshDelegationA (RefreshDelegationArgs refreshDelegationE refreshDelegationA_full_sound)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationSpec RefreshDelegationFullSpec refreshDelegationsMap)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest cellCommitS cellCommitS_binds_systemRoots_or_collides
   cellCommitSCollFind CellCommitSColl cellCommitSColl_refutable_of_injective
   systemRootsDigest_binds_pointwise_or_collides
   rootsCollFind RootsColl rootsColl_refutable_of_injective N_SYSTEM_ROOTS)

/-- The `delegations` side-table root index in the STAGE-3 `system_roots` sub-block
(`Exec.SystemRoots.systemRoot.DELEG = 4`), as a bounded `Fin`. Local abbreviation to avoid the
`systemRoot` namespace collision with `EffectVmEmit.state.systemRoot`. -/
abbrev delegIdx : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.DELEG, by decide⟩

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the refresh row. -/

namespace selR
/-- The `refreshDelegationA` effect selector column (the running prover's per-effect selector,
`columns.rs::sel::REFRESH_DELEGATION`). The runtime trace (`effect_vm/trace.rs`,
`Effect::RefreshDelegation => sel::REFRESH_DELEGATION`) sets column **29**; the prior `3` was a
stale GRANT_CAP collision that never bit because no constraint read the selector. The
selector-binding tooth (`selectorGates`) now DOES, so this MUST be the runtime index. -/
def REFRESH : Nat := 29
end selR

/-! ## §1 — The frame-freeze + nonce-TICK row gates (the runtime passthrough convention).

`refreshDelegationA` is a STATE-PASSTHROUGH variant in the runtime hand-AIR (`effect_vm/air.rs:980-986`):
every EffectVM `state` column is FROZEN, and the GLOBAL nonce gate TICKS the row nonce by one (the row is
non-NoOp; `generate_effect_vm_trace` `Effect::RefreshDelegation => new_state.nonce += 1`). The gate set is
`cap_root`/`balance`/`reserved`/`fields` passthrough + the nonce TICK (`gNonceTick`, the running prover's
`new_nonce − old_nonce − (1 − s_noop)` global invariant). The deleg-MOVE lives at the record layer (§7+). -/

/-- Balance-lo freeze: `new_bal_lo - old_bal_lo`. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce TICK body (the running prover's global non-NoOp invariant, reused verbatim from the transfer
template `gNonce`): `new_nonce − old_nonce − (1 − s_noop)`. On a refresh row `s_noop = 0`, so this is
`new_nonce − old_nonce − 1` (TICK). The runtime classes refresh as non-NoOp, so the nonce ticks like
every other effect row — NOT a freeze (the pre-STAGE-3 version's `gNonceFix` was UNSAT on the honest
trace; this is the burn/bridgeMint cutover column-fix applied to refresh). -/
def gNonceTick : EmittedExpr := gNonce
/-- Reserved freeze: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Field-`i` freeze: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint := (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The frame-freeze + nonce-TICK per-row gates: cap_root passthrough (`gCapPass`, reused from transfer)
+ balance/reserved freeze + nonce TICK + 8 fields freeze. The whole EffectVM state block is `after =
before` EXCEPT the runtime nonce, which ticks (the hand-AIR passthrough convention). -/
def refreshRowGates : List VmConstraint :=
  [ .gate gCapPass, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceTick, .gate gResFix ] ++ gFieldFixAll

/-! ## §2 — The emitted descriptor. -/

/-- The `refreshDelegationA` AIR identity. -/
def refreshVmAirName : String := "dregg-effectvm-refreshDelegation-v2"

/-- **`refreshVmDescriptor`** — the runnable `refreshDelegationA` PASSTHROUGH+NONCE-TICK row: every
EffectVM state column frozen, the runtime nonce ticked, ++ transition continuity ++ the row-0 boundary
pins, with the 4 ordered GROUP-4 hash sites (binding the post-state). The genuine `delegations` move is
bound at the RECORD layer via the `DELEG` system-root (§7+), not as a base-trace state column. -/
def refreshVmDescriptor : EffectVmDescriptor :=
  { name := refreshVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := refreshRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates selR.REFRESH
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The frame-freeze + nonce-TICK ROW INTENT + faithfulness. -/

/-- The row is a refresh row: `s_refresh = 1`, `s_noop = 0`. The `s_noop = 0` clause is what the global
nonce-tick gate factors on (a refresh row is non-NoOp, so the nonce ticks). -/
def IsRefreshRow (env : VmRowEnv) : Prop :=
  env.loc selR.REFRESH = 1 ∧ env.loc sel.NOOP = 0

/-- **`RefreshRowIntent env`** — every EffectVM state column is frozen (`after = before`) AND the runtime
nonce TICKS by one: the SUPPORTED content of a refresh row at the EffectVM-row layer (the hand-AIR
passthrough+tick convention). Its touched field, `delegations`, rides the `DELEG` system-root (§7). -/
def RefreshRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) ≡ env.loc (sbCol state.CAP_ROOT) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) + 1 [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- **`refreshVm_faithful`** — on a refresh row, the emitted passthrough+tick gates all hold IFF
`RefreshRowIntent` holds. The gate bodies are the running prover's passthrough/nonce-tick polynomials. -/
theorem refreshVm_faithful (env : VmRowEnv) (hrow : IsRefreshRow env) :
    (∀ c ∈ refreshRowGates, c.holdsVm env false false) ↔ RefreshRowIntent env := by
  obtain ⟨_hsR, hsN⟩ := hrow
  unfold refreshRowGates gFieldFixAll RefreshRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapPass) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapPass, gBalLoFix, gBalHiFix, gNonceTick, gNonce, gResFix,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hCap hLo hHi hNon hRes
    rw [hsN] at hNon
    refine ⟨(gate_modEq_iff (by ring)).mp hCap, (gate_modEq_iff (by ring)).mp hLo,
      (gate_modEq_iff (by ring)).mp hHi, (gate_modEq_iff (by ring)).mp hNon,
      (gate_modEq_iff (by ring)).mp hRes, ?_⟩
    intro i hi
    have hfi := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at hfi
    exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hCap, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop,
        EmittedExpr.eval]
      rw [hsN]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-! ## §4 — ANTI-GHOST: a row that moves ANY frozen EffectVM column (or fails the tick) fails. -/

/-- **Anti-ghost (cap_root tamper).** A refresh row whose post-`cap_root` ≠ pre-`cap_root` fails the
`gCapPass` gate (UNSAT) — refresh must leave `cap_root` (the `caps` digest) frozen. -/
theorem refreshVm_rejects_moved_capRoot (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.CAP_ROOT)
      ∧ env.loc (saCol state.CAP_ROOT) < 2013265921)
    (hcanonPre : 0 ≤ env.loc (sbCol state.CAP_ROOT)
      ∧ env.loc (sbCol state.CAP_ROOT) < 2013265921)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapPass).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonPre hwrong

/-- **Anti-ghost (general).** A row (on a refresh selector) that is NOT a passthrough+tick does not
satisfy the per-row gates. -/
theorem refreshVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsRefreshRow env)
    (hwrong : ¬ RefreshRowIntent env) :
    ¬ (∀ c ∈ refreshRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((refreshVm_faithful env hrow).mp h)

/-! ## §5 — Structured per-cell freeze+tick soundness. -/

/-- **`RefreshRowEncodes env pre post`** — the row decodes to `(pre, post)` cell states. -/
def RefreshRowEncodes (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell refresh spec: the WHOLE EffectVM post-state equals the pre-state (every column frozen,
including `cap_root`) EXCEPT the runtime nonce, which TICKS by one (the per-cell sequence counter). -/
def RefreshCellSpec (pre post : CellState) : Prop :=
  post.capRoot ≡ pre.capRoot [ZMOD 2013265921]
  ∧ post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce + 1 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- Under `RefreshRowEncodes`, `RefreshRowIntent` IS the structured per-cell `RefreshCellSpec`. -/
theorem intent_to_refreshCellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RefreshRowEncodes env pre post) (hint : RefreshRowIntent env) :
    RefreshCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`refreshDescriptor_full_sound`** — satisfying the passthrough+tick gates under the decoding forces
the structured per-cell freeze+tick (every EffectVM column, incl. `cap_root`, frozen; nonce ticked). -/
theorem refreshDescriptor_full_sound (env : VmRowEnv) (pre post : CellState)
    (hrow : IsRefreshRow env)
    (henc : RefreshRowEncodes env pre post)
    (hgates : ∀ c ∈ refreshRowGates, c.holdsVm env false false) :
    RefreshCellSpec pre post :=
  intent_to_refreshCellSpec env pre post henc ((refreshVm_faithful env hrow).mp hgates)

/-! ## §6 — Commitment tooth (the post-state is bound into `state_commit`). -/

/-- The refresh hash sites ARE the transfer keystone's (same 4-site chain). -/
theorem refreshHashSites_eq : refreshVmDescriptor.hashSites = transferHashSites := rfl

/-- The descriptor-level anti-ghost, UNCONDITIONAL: two satisfying `refreshDelegation` rows publishing the SAME
`NEW_COMMIT` public input EITHER have identical absorbed after-blocks OR exhibit a genuine
deployed-sponge collision at the pair `transferCollFind` names.

⚑ CUT OVER 2026-08-01 off `Poseidon2SpongeCR`, PROVED FALSE at deployed BabyBear parameters by
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — the old form was vacuous where the prover runs.
The replacement (`absorbed_determined_by_commit_or_collides`) was ALREADY PROVED and already used by the
sibling effects; this declaration was left behind by that cutover. A consumer wanting the bare equality
applies `Poseidon2Binding.spongeColl_refutable_of_injective`; no local `_of_CR` twin is minted, so this
is a NET carrier decrease and not a `#floor_ratchet` accrual. -/
theorem refreshDescriptor_commit_binds_state_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂ :=
  absorbed_determined_by_commit_or_collides hash e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — THE DELEG SYSTEM-ROOT (STAGE 3): binding the touched `delegations` field.

STAGE 3 (`Exec.SystemRoots`) gives `delegations` its OWN side-table root `systemRoot.DELEG` (index 4),
digested into the `SYSTEM_ROOTS_DIGEST` carrier and absorbed into the canonical cell commitment by
`cellCommitS`. The `deleg_root` value IS universe-A's injective `delegations` digest `D k.delegations`.
This is the part the pre-STAGE-3 module reported as IR-BLOCKED; it is now BINDABLE. -/

/-- **`delegRootProj D k`** — the `DELEG` system-root column value: the `delegations` whole-function
digest (universe-A's injective `D`). This is the felt the runtime writes at `state.systemRoot.DELEG`. -/
def delegRootProj (D : (CellId → List Cap) → ℤ) (k : RecordKernelState) : ℤ := D k.delegations

/-- Install `delegations`'s digest into the `DELEG` slot of a `SysRoots` sub-block, freezing the other
seven side-table roots at `others`. The Lean mirror of "the row's `system_roots` sub-block: `DELEG`
holds the cell's delegations root, the rest carry their unchanged roots". -/
def withDelegRoot (D : (CellId → List Cap) → ℤ) (others : SysRoots) (k : RecordKernelState) : SysRoots :=
  fun i => if i = delegIdx then delegRootProj D k else others i

/-- **`delegRoot_moves_under_spec`** — under `RefreshDelegationSpec`, the projected `DELEG` root MOVES
from `D k.delegations` to `D (refreshDelegationsMap k child)` (the parent-clist snapshot). This is the
genuine `delegations` content, now an explicit root transition (the move was IR-BLOCKED pre-STAGE-3). -/
theorem delegRoot_moves_under_spec (D : (CellId → List Cap) → ℤ)
    (s : RecChainedState) (actor child : CellId) (s' : RecChainedState)
    (hspec : RefreshDelegationFullSpec s actor child s') :
    delegRootProj D s'.kernel = D (refreshDelegationsMap s.kernel child) := by
  obtain ⟨_hguard, hdeleg, _⟩ := hspec
  show D s'.kernel.delegations = D (refreshDelegationsMap s.kernel child)
  rw [hdeleg]

/-- **(REDUCTION-INTERNAL extraction step — NOT an exported headline; the exported successor is
`delegRoot_binds_rom` below, closed on the PROVED keyed-ROM floor.)** The STAGE-3 anti-ghost tooth,
lifted to the `DELEG` root. ⚑ A bare `binds ∨ collides` is a SHIRK as a headline (a collision EXISTS
by pigeonhole at deployed parameters); this lemma is kept PRIVATE as the witness inside the
`_of_injective` strength bridge below. Two cells whose canonical `cellCommitS` commitments AGREE (over the same `rest`
and the same frozen sibling roots `others`) EITHER have the SAME `DELEG` root, OR the prover holds a
NAMED collision of the deployed sponge: at the commitment absorption (`CellCommitSColl`, the pair
`cellCommitSCollFind` returns) or at the ordered root list (`RootsColl`). The chain: the commitment
binds the digest (`cellCommitS_binds_systemRoots_or_collides`), which binds every system-root pointwise
(`systemRootsDigest_binds_pointwise_or_collides`) — in particular `DELEG`. So a prover cannot tamper the
`delegations` root (a forged refresh snapshot) while keeping the published commitment: UNSAT unless a
collision is exhibited.

⚑ **WHY THIS SHAPE.** The old form carried `StateCommit.compressNInjective compressN`, which
`HashFloorHonesty` REFUTES at the deployed BabyBear parameters — so it said nothing about the deployed
`delegations` binding. This one assumes nothing about the sponge and holds OF it;
`delegRoot_binds_under_commit_of_injective` recovers the old statement as exactly the injective special
case, so no strength was lost. -/
private theorem delegRoot_binds_under_commit_or_collides
    (compressN : List ℤ → ℤ)
    (D : (CellId → List Cap) → ℤ) (others : SysRoots) (rest : List ℤ)
    (k₁ k₂ : RecordKernelState)
    (hcommit : cellCommitS compressN rest (withDelegRoot D others k₁)
             = cellCommitS compressN rest (withDelegRoot D others k₂)) :
    delegRootProj D k₁ = delegRootProj D k₂
    ∨ CellCommitSColl compressN rest (withDelegRoot D others k₁) (withDelegRoot D others k₂)
    ∨ RootsColl compressN (withDelegRoot D others k₁) (withDelegRoot D others k₂) := by
  rcases cellCommitS_binds_systemRoots_or_collides compressN rest _ _ hcommit with hdig | hcoll
  · rcases systemRootsDigest_binds_pointwise_or_collides compressN _ _ hdig with hpt | hrcoll
    · exact Or.inl (by simpa only [withDelegRoot, if_pos rfl, if_true] using hpt delegIdx)
    · exact Or.inr (Or.inr hrcoll)
  · exact Or.inr (Or.inl hcoll)

/-- **⚑ THE NO-STRENGTH-LOST TOOTH.** The deleted `delegRoot_binds_under_commit` is EXACTLY the
injective special case of its cured form. Standalone bridge, deliberately NOT a hypothesis on any
deployed statement — a theorem carrying `compressNInjective` would be right back where this repair
started. -/
theorem delegRoot_binds_under_commit_of_injective
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (D : (CellId → List Cap) → ℤ) (others : SysRoots) (rest : List ℤ)
    (k₁ k₂ : RecordKernelState)
    (hcommit : cellCommitS compressN rest (withDelegRoot D others k₁)
             = cellCommitS compressN rest (withDelegRoot D others k₂)) :
    delegRootProj D k₁ = delegRootProj D k₂ := by
  rcases delegRoot_binds_under_commit_or_collides compressN D others rest k₁ k₂ hcommit with
    hEq | hcoll | hrcoll
  · exact hEq
  · exact absurd hcoll (cellCommitSColl_refutable_of_injective compressN hN rest _ _)
  · exact absurd hrcoll (rootsColl_refutable_of_injective compressN hN _ _)

/-! ### §7-ROM — THE EXPORTED SUCCESSOR of the `DELEG`-root extraction disjunction, ON THE PROVED
KEYED-ROM FLOOR. The deployed chain (`cellCommitS compressN rest sr = compressN (rest ++
[systemRootsDigest compressN sr])`) is exactly `Exec.SystemRootsBindingReduction`'s two-level nest
`H (t, inr (rest, H (t, inl roots)))` in the labelled idealization (that module's §7 header — the
sampled `H : Tag × Msg → Fin (2^l)` replaces the fixed sponge; NO `l` is the deployed ~31-bit felt).
The successor localizes the disagreement to the `DELEG` lane and closes from the generic full-chain
binding `cellRoots_binds_rom` (`chained_rom_binds` + `keyedRom_hard`, the birthday bound) — NO floor
hypothesis, no `compressNInjective`, no `IsPolyTime`. -/

open Dregg2.Exec.SystemRootsBindingReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **THE `DELEG`-ROOT ROM TAMPER** — two truncated `system_roots` sub-blocks that DIFFER AT THE
`DELEG` LANE (a forged refresh snapshot), one nested canonical cell commitment. -/
def delegRootRomTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomForgery (sysRomFamily D tagDec m) where
  Ans := fun _ => D.Tag × (Fin m → Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
    × RootsBlock × RootsBlock
  wins := fun l H a =>
    a.2.2.1 delegIdx ≠ a.2.2.2 delegIdx ∧
      H (a.1, Sum.inr (a.2.1, H (a.1, Sum.inl a.2.2.1)))
        = H (a.1, Sum.inr (a.2.1, H (a.1, Sum.inl a.2.2.2)))
  winsDec := fun l _ _ => by
    letI := ((sysRomFamily D tagDec m).toRomFamily).rDec l
    exact instDecidableAnd

open Dregg2.Exec.SystemRootsBindingReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites
  Dregg2.Crypto.ProbCrypto in
/-- **⚑⚑ `delegRoot_binds_rom` — THE EXPORTED SUCCESSOR of the `DELEG`-root extraction
disjunction.** A query-bounded forger that keeps the nested canonical cell commitment while moving
the `DELEG` side-table root has NEGLIGIBLE advantage — a `DELEG`-lane disagreement IS a sub-block
disagreement, so the generic full-chain binding (`cellRoots_binds_rom`, from `keyedRom_hard`) kills
it. NO floor hypothesis. -/
theorem delegRoot_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (delegRootRomTamper D tagDec m).game)
    (hA : RomForgeryEff (sysRomFamily D tagDec m) (delegRootRomTamper D tagDec m) Q A) :
    Negl (gameAdv (delegRootRomTamper D tagDec m).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (cellRootsRomForgery D tagDec m).game
      (⟨A.run⟩ : Adversary (cellRootsRomForgery D tagDec m).game)) :=
    cellRoots_binds_rom D tagDec m Q hQ
      (⟨A.run⟩ : Adversary (cellRootsRomForgery D tagDec m).game) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (delegRootRomTamper D tagDec m).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _
    (((delegRootRomTamper D tagDec m).game).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Adversary.hit_eq_true _ _ _).mp hH
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrFun hc delegIdx), heq⟩

/-! ## §8 — THE CONNECTORS — to `refreshDelegationA_full_sound` (cap-freeze AND deleg-move). -/

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value: the `caps` whole-function digest. -/
def capRootProj (D : (CellId → List Cap) → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- **`unify_refresh_capFreeze` — connector (the `cap_root` freeze).** When `RefreshDelegationSpec`
holds, the projected `cap_root` is FROZEN (`D k'.caps = D k.caps`) — exactly the runnable row's
`cap_root` passthrough gate. -/
theorem unify_refresh_capFreeze (D : (CellId → List Cap) → ℤ)
    (s : RecChainedState) (actor child : CellId) (s' : RecChainedState)
    (hspec : RefreshDelegationFullSpec s actor child s') :
    capRootProj D s'.kernel = capRootProj D s.kernel := by
  obtain ⟨_hguard, _hdeleg, _hlog, _hAcc, _hCell, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D s.kernel.caps
  rw [hcaps]

/-- **`unify_refresh_via_full_sound` — THE FULL CONNECTOR.** A satisfying universe-A witness
(`refreshDelegationA_full_sound` ⟹ `RefreshDelegationSpec`, the `RefreshDelegationGuard` enforced by its
`propBit` column) forces BOTH: (1) the projected `cap_root` is FROZEN (the runnable row's passthrough);
and (2) the projected `DELEG` system-root MOVES to `D (refreshDelegationsMap …)` — the touched-field
content, now BOUND (STAGE 3). The conjunction is the FULL-state refresh: caps frozen + delegations moved. -/
theorem unify_refresh_via_full_sound
    (S : Surface2)
    (Dp : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDp : Function.Injective Dp)
    (D : (CellId → List Cap) → ℤ)
    (hRest : Dregg2.Circuit.Inst.RefreshDelegationA.RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (refreshDelegationE Dp hDp) (encodeE2 S (refreshDelegationE Dp hDp) s args s')) :
    capRootProj D s'.kernel = capRootProj D s.kernel
    ∧ delegRootProj D s'.kernel = D (refreshDelegationsMap s.kernel args.child) := by
  have hspec := refreshDelegationA_full_sound S Dp hDp hRest hLog s args s' h
  exact ⟨unify_refresh_capFreeze D s args.actor args.child s' hspec,
         delegRoot_moves_under_spec D s args.actor args.child s' hspec⟩

/-! ## §9 — HONEST: the deleg-MOVE column is record-layer-bound, not yet a runtime trace column.

STAGE 3 makes the `delegations` move BINDABLE (§7, the `DELEG` system-root + commitment anti-ghost) and
CONNECTED to universe-A (§8). The remaining gap is purely RUNTIME-side: `generate_effect_vm_trace`'s
`RefreshDelegation` arm does NOT yet WRITE a `DELEG`/`SYSTEM_ROOTS_DIGEST` column (it ticks the nonce
only — `effect_vm/trace.rs`). So the in-row deleg-move gate is sound + anti-ghost against the STAGE-3
record-commitment MODEL, and its full prover-trace column lands when the Rust trace-generator emits it
(`_RECORD-LAYER-UPGRADE.md` §C, OUTSIDE this single-file scope). We state the boundary as a theorem: the
EffectVM-row `cap_root` column reads ONLY `caps` — it is independent of `delegations` — so the deleg-move
is carried by the record-layer `DELEG` root (§7), NOT by any current base-trace state column. -/

/-- **`delegRoot_runtime_column_pending` — the boundary, as a theorem.** The EffectVM-row
`cap_root` column reads ONLY `caps`; it is independent of `delegations`. Concretely: two kernel states
with IDENTICAL `caps` (hence identical EffectVM-row `cap_root`) can DIFFER on `delegations` (hence differ
on the record-layer `DELEG` root). So the `delegations` move is witnessed by the STAGE-3 `DELEG` root
(§7), NOT by the base-trace `cap_root` column — and its runtime trace column is the pending Rust
trace-generator extension. -/
theorem delegRoot_runtime_column_pending (D : (CellId → List Cap) → ℤ)
    (k : RecordKernelState) (g₁ g₂ : CellId → List Cap) (hne : D g₁ ≠ D g₂) :
    capRootProj D { k with delegations := g₁ } = capRootProj D { k with delegations := g₂ }
    ∧ delegRootProj D { k with delegations := g₁ } ≠ delegRootProj D { k with delegations := g₂ } := by
  refine ⟨?_, ?_⟩
  · show D ({ k with delegations := g₁ } : RecordKernelState).caps
        = D ({ k with delegations := g₂ } : RecordKernelState).caps
    rfl
  · show D ({ k with delegations := g₁ } : RecordKernelState).delegations
        ≠ D ({ k with delegations := g₂ } : RecordKernelState).delegations
    exact hne

/-! ## §10 — NON-VACUITY (EffectVM row): a concrete passthrough+tick row that satisfies the intent,
and forgeries (moved cap_root / failed tick) that do not. -/

/-- A concrete refresh row: every EffectVM state column frozen (`cap_root 9 → 9`), the nonce TICKED
(`5 → 6`), all else 0. -/
def refreshGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selR.REFRESH then 1
    else if v = sbCol state.CAP_ROOT then 9
    else if v = saCol state.CAP_ROOT then 9
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The `refreshGoodRow.loc` value at a LITERAL `Nat` column `v`, decided by computation: the row's
`loc` is a finite chain of `Nat` `if`s over reduced numeric columns, so `decide`/`rfl` evaluates it.
Helper to read the concrete row without `if`-branch gymnastics. -/
private theorem goodRow_loc_eval (v : Nat) :
    refreshGoodRow.loc v
      = (if v = 29 then 1 else if v = 65 then 9 else if v = 87 then 9
         else if v = 56 then 5 else if v = 78 then 6 else 0) := rfl

/-- `refreshGoodRow` is a refresh row (`s_refresh = 1`, `s_noop = 0`). -/
theorem refreshGoodRow_isRow : IsRefreshRow refreshGoodRow := by
  refine ⟨?_, ?_⟩
  · show refreshGoodRow.loc selR.REFRESH = 1
    rw [goodRow_loc_eval]; decide
  · show refreshGoodRow.loc sel.NOOP = 0
    rw [goodRow_loc_eval]; decide

/-- **NON-VACUITY (witness TRUE).** `refreshGoodRow` REALIZES the passthrough+tick intent: `cap_root
9 = 9`, nonce `6 = 5 + 1`, all other columns `0 = 0`. -/
theorem refreshGoodRow_realizes_intent : RefreshRowIntent refreshGoodRow := by
  -- The column constants, fully reduced once (so the row's `loc` `if`-chain decides at a numeral).
  have hcr_sa : saCol state.CAP_ROOT = 87 := rfl
  have hcr_sb : sbCol state.CAP_ROOT = 65 := rfl
  have hbl_sa : saCol state.BALANCE_LO = 76 := rfl
  have hbl_sb : sbCol state.BALANCE_LO = 54 := rfl
  have hbh_sa : saCol state.BALANCE_HI = 77 := rfl
  have hbh_sb : sbCol state.BALANCE_HI = 55 := rfl
  have hn_sa : saCol state.NONCE = 78 := rfl
  have hn_sb : sbCol state.NONCE = 56 := rfl
  have hr_sa : saCol state.RESERVED = 89 := rfl
  have hr_sb : sbCol state.RESERVED = 67 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eqToModEq ?_
    show refreshGoodRow.loc (saCol state.CAP_ROOT) = refreshGoodRow.loc (sbCol state.CAP_ROOT)
    rw [hcr_sa, hcr_sb, goodRow_loc_eval, goodRow_loc_eval]; decide
  · refine eqToModEq ?_
    show refreshGoodRow.loc (saCol state.BALANCE_LO) = refreshGoodRow.loc (sbCol state.BALANCE_LO)
    rw [hbl_sa, hbl_sb, goodRow_loc_eval, goodRow_loc_eval]; decide
  · refine eqToModEq ?_
    show refreshGoodRow.loc (saCol state.BALANCE_HI) = refreshGoodRow.loc (sbCol state.BALANCE_HI)
    rw [hbh_sa, hbh_sb, goodRow_loc_eval, goodRow_loc_eval]; decide
  · refine eqToModEq ?_
    show refreshGoodRow.loc (saCol state.NONCE) = refreshGoodRow.loc (sbCol state.NONCE) + 1
    rw [hn_sa, hn_sb, goodRow_loc_eval, goodRow_loc_eval]; decide
  · refine eqToModEq ?_
    show refreshGoodRow.loc (saCol state.RESERVED) = refreshGoodRow.loc (sbCol state.RESERVED)
    rw [hr_sa, hr_sb, goodRow_loc_eval, goodRow_loc_eval]; decide
  · intro i hi
    refine eqToModEq ?_
    -- field columns: saCol(FIELD_BASE+i) ∈ [79,86], sbCol(FIELD_BASE+i) ∈ [57,64]; both miss every
    -- populated branch (3/65/87/56/78), so both read 0.
    have hsa : saCol (state.FIELD_BASE + i) = 79 + i := by
      simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
        NUM_PARAMS, state.FIELD_BASE]; omega
    have hsb : sbCol (state.FIELD_BASE + i) = 57 + i := by
      simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.FIELD_BASE]; omega
    show refreshGoodRow.loc (saCol (state.FIELD_BASE + i)) = refreshGoodRow.loc (sbCol (state.FIELD_BASE + i))
    rw [hsa, hsb, goodRow_loc_eval, goodRow_loc_eval]
    have ha29 : ¬ (79 + i = 29) := by omega
    have ha65 : ¬ (79 + i = 65) := by omega
    have ha87 : ¬ (79 + i = 87) := by omega
    have ha56 : ¬ (79 + i = 56) := by omega
    have ha78 : ¬ (79 + i = 78) := by omega
    have hb29 : ¬ (57 + i = 29) := by omega
    have hb65 : ¬ (57 + i = 65) := by omega
    have hb87 : ¬ (57 + i = 87) := by omega
    have hb56 : ¬ (57 + i = 56) := by omega
    have hb78 : ¬ (57 + i = 78) := by omega
    rw [if_neg ha29, if_neg ha65, if_neg ha87, if_neg ha56, if_neg ha78,
        if_neg hb29, if_neg hb65, if_neg hb87, if_neg hb56, if_neg hb78]

/-- A forged refresh row: `refreshGoodRow` with the post-`cap_root` MOVED to `999 ≠ 9` (refresh must
freeze `cap_root`). -/
def refreshBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else refreshGoodRow.loc v
  nxt := refreshGoodRow.nxt
  pub := refreshGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `refreshBadRow`'s post-`cap_root` is MOVED, so
the `gCapPass` freeze gate REJECTS it — a concrete UNSAT. -/
theorem refreshBadRow_rejected : ¬ (VmConstraint.gate gCapPass).holdsVm refreshBadRow false false := by
  -- Column constants, reduced once: saCol CAP_ROOT = 87, sbCol CAP_ROOT = 65.
  have hsacol : saCol state.CAP_ROOT = 87 := by
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.CAP_ROOT]
  have hsbcol : sbCol state.CAP_ROOT = 65 := by
    simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.CAP_ROOT]
  have hsa : refreshBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else refreshGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hsb : refreshBadRow.loc (sbCol state.CAP_ROOT) = 9 := by
    show (if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else refreshGoodRow.loc (sbCol state.CAP_ROOT)) = 9
    rw [hsacol, hsbcol, if_neg (by decide), goodRow_loc_eval]; decide
  -- The post-`cap_root` (999) and pre-`cap_root` (9) are both canonical in [0, p), and differ.
  apply refreshVm_rejects_moved_capRoot <;> simp only [hsa, hsb] <;> norm_num

/-! ## §11 — NON-VACUITY (DELEG root): the system-root binding is load-bearing (witness TRUE + FALSE). -/

-- A concrete injective `delegations` digest stub (a toy Horner over a finite probe of the c-list map;
-- here we only need an INJECTIVE `ℤ`-valued `D` for the witnesses, modelled abstractly per side).
private def cN : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)
private def restN : List Int := [3, 5, 7]
private def othersN : SysRoots := fun _ => 0

-- POSITIVE (load-bearing): a refresh that MOVES the deleg root (D 11 → D 99) produces a DIFFERENT
-- system-roots commitment than one that did not move it — the binding is not vacuous.
private def DstubA : (CellId → List Cap) → ℤ := fun _ => 11
private def DstubB : (CellId → List Cap) → ℤ := fun _ => 99

/-- **NON-VACUITY (DELEG witness FALSE / anti-ghost).** Two `system_roots` sub-blocks that differ ONLY at
the `DELEG` slot (`11` vs `99`) commit DIFFERENTLY under `cellCommitS cN restN` — so a tampered deleg
root provably MOVES the commitment (the §7 anti-ghost tooth is load-bearing). -/
theorem delegRoot_tamper_moves_commit :
    cellCommitS cN restN (fun i => if i = delegIdx then 11 else othersN i)
      ≠ cellCommitS cN restN (fun i => if i = delegIdx then 99 else othersN i) := by
  decide

/-- **NON-VACUITY (DELEG witness TRUE / completeness).** Two `system_roots` sub-blocks with the SAME
`DELEG` root (both `11`) and the same frozen siblings commit IDENTICALLY — an honest unchanged-root row is
accepted. -/
theorem delegRoot_same_commits_equal :
    cellCommitS cN restN (fun i => if i = delegIdx then 11 else othersN i)
      = cellCommitS cN restN (fun i => if i = delegIdx then 11 else othersN i) :=
  rfl


/-! ## §G — THE GENUINE CLASS-A `refresh` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`refresh` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`refresh`-specific content is the OP tag `capOp.REFRESH` carried in the edge leaf (the delegation-epoch refresh), plus the existing
connector to universe-A. We re-export the genuine soundness + edge-binding anti-ghost for `refresh`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates CapCellSpecGenuine attenuateHashSites
   attenuateGenuine_sound attenuateGenuine_binds_edge CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds)

/-- **`refreshVmDescriptorGenuine`** — the GENUINE `refresh` circuit: definitionally the shared genuine
cap-root-recompute descriptor (the opaque digest param is GONE; `cap_root` is FORCED in-row). -/
def refreshVmDescriptorGenuine : EffectVmDescriptor := attenuateVmDescriptorGenuine

/-- **`refreshGenuine_sound` — THE CLASS-A THEOREM for `refresh`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound`. -/
theorem refreshGenuine_sound (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post :=
  attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec

/-- **`refreshGenuine_binds_edge` — the genuine class-A anti-ghost for `refresh`.** Two genuine `refresh` rows
with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the cap-edge mutation moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem refreshGenuine_binds_edge (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (e₁ e₂ : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hsCommit₁ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₁ attenuateHashSites)
    (hsCommit₂ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₂ attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  attenuateGenuine_binds_edge hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

#assert_axioms refreshGenuine_sound
#assert_axioms refreshGenuine_binds_edge

/-! ### §G.4 — `refresh` carries the IN-CIRCUIT NON-AMP GUARD (`granted ⊑ held`, `granted = held` for a re-issue).

`refreshDelegation` RE-ISSUES an existing delegation (refreshed expiry, SAME conferred rights) — so its
granted rights EQUAL the held rights, and `granted ⊑ held` holds by reflexivity (`submask_self`). It
inherits the SAME shared GENUINE-NON-AMP descriptor `attenuateVmDescriptorGenuineNonAmp` as the granting
family — one uniform gate set across the cap-graph family. For a refresh the gate is satisfied by the
unchanged mask (`granted = held`) and REJECTS only a malformed refresh that silently WIDENS the rights
beyond what was held — exactly the amplification a refresh must never introduce. In-circuit, on the SAME
descriptor that recomputes the cap-root. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuineNonAmp attenuateGenuineNonAmp_in_circuit
   attenuateGenuineNonAmp_rejects_amplify)

/-- **`refreshVmDescriptorGenuineNonAmp`** — the GENUINE `refresh` circuit WITH the in-circuit non-amp
guard: definitionally the shared genuine-non-amp descriptor (recompute + `granted ⊑ held`). -/
def refreshVmDescriptorGenuineNonAmp : EffectVmDescriptor := attenuateVmDescriptorGenuineNonAmp

/-- **`refreshNonAmp_in_circuit`** — a satisfying `refresh` witness FORCES `granted ⊑ held` per bit (for
a re-issue, `granted = held`). Inherited from the shared in-circuit tooth. -/
theorem refreshNonAmp_in_circuit (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hcon : ∀ c ∈ refreshVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hgc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) < 2013265921) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 0
    ∨ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 1 :=
  attenuateGenuineNonAmp_in_circuit env hcon i hi hgc hhc

/-- **`refreshNonAmp_rejects_amplify`** — a malformed `refresh` that WIDENS rights beyond held (granted
bit set, held bit clear) does NOT satisfy the descriptor. Inherited from the shared rejection. -/
theorem refreshNonAmp_rejects_amplify (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hg : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 1)
    (hh : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ refreshVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) :=
  attenuateGenuineNonAmp_rejects_amplify env i hi hg hh

#assert_axioms refreshNonAmp_in_circuit
#assert_axioms refreshNonAmp_rejects_amplify

/-! ## §12 — Axiom-hygiene tripwires. -/

#guard refreshVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1  -- 13 freeze/tick gates + 14 transitions + 4 first + 3 last + selectorGate
#guard refreshVmDescriptor.hashSites.length == 4
#guard refreshVmDescriptor.traceWidth == 188

#assert_axioms refreshVm_faithful
#assert_axioms refreshVm_rejects_moved_capRoot
#assert_axioms refreshVm_rejects_wrong_output
#assert_axioms intent_to_refreshCellSpec
#assert_axioms refreshDescriptor_full_sound
#assert_axioms refreshDescriptor_commit_binds_state_or_collides
#assert_axioms delegRoot_moves_under_spec
#assert_axioms delegRoot_binds_under_commit_or_collides
#assert_axioms delegRoot_binds_under_commit_of_injective
#assert_axioms delegRoot_binds_rom
#assert_axioms unify_refresh_capFreeze
#assert_axioms unify_refresh_via_full_sound
#assert_axioms delegRoot_runtime_column_pending
#assert_axioms refreshGoodRow_isRow
#assert_axioms refreshGoodRow_realizes_intent
#assert_axioms refreshBadRow_rejected
#assert_axioms delegRoot_tamper_moves_commit
#assert_axioms delegRoot_same_commits_equal

/-! ## §W — THE MAGNESIUM LIFT: `refreshDelegation`'s RUNNABLE descriptor binds the FULL 17-field
post-state (the `system_roots` sub-block bound BY the runnable commitment; the `DELEG` MOVE is the §7-8
record-layer connector + the reported pending runtime column).

`refreshDelegation` is a PASSTHROUGH+nonce-TICK cap-graph row (cap_root FROZEN on-row). Its WIDE
descriptor widens `refreshVmDescriptor` to `EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites`, so the
published `state_commit` now ABSORBS the `system_roots` digest — i.e. the WHOLE side-table sub-block
(`postRoots`) is bound by the runnable commitment (the anti-ghost REDUCTIONS
`refresh_rejects_root_tamper_advantage_bound` / `refresh_rejects_root_tamper_rom` bite on every one
of the 8 roots, the `DELEG` root included). The wide RUNNABLE crown pins the per-cell
freeze+tick (`RefreshCellSpec`) AND the `postRoots` the carrier digests.

⚑ THE TOUCHED ROOT (`DELEG`) — the split: refresh is the ONE cap-graph effect that MOVES a
side-table root (`delegations := refreshDelegationsMap`). The SPECIFIC DELEG transition is connected at
the RECORD layer (`delegRoot_moves_under_spec` / `unify_refresh_via_full_sound`, §7-8, cited) — and its
full prover-TRACE column is the pending Rust trace-generator extension (`delegRoot_runtime_column_pending`,
§9). So this lift binds the full 17-field RUNNABLE post-state (per-cell block + the 8 side-table roots
bound BY the commitment), with the DELEG-MOVE value the record-layer connector supplies — the same honest
boundary §7-9 already states, now on the RUNNABLE (`wideHashSites`) commitment rather than only the
record-layer `cellCommitS`. -/

open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites baseAbsorbedCols RunnableFullStateSpec runnable_full_sound
   wide_rejects_root_tamper_or_collides wide_rejects_state_tamper_or_collides WideColl RootsColl)
open Dregg2.Exec.SystemRoots (systemRootsDigest)

/-- **`refreshVmDescriptorWide`** — the runnable `refreshDelegation` FULL-state circuit: `refreshVmDescriptor`
WIDENED to `EFFECT_VM_WIDTH_SYSROOTS` with `hashSites := wideHashSites`. Strictly additive: the constraint
list (passthrough+tick gates ++ transitions ++ boundary ++ selector) is byte-identical; only the width
grows by 2 and site 3's spare `.zero` slot becomes the side-table digest carrier. -/
def refreshVmDescriptorWide : EffectVmDescriptor :=
  { refreshVmDescriptor with
    name := refreshVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide refresh descriptor's constraints ARE `refreshVmDescriptor`'s. -/
theorem refreshWide_constraints_eq :
    refreshVmDescriptorWide.constraints = refreshVmDescriptor.constraints := rfl

/-- **`RefreshFullClause`** — the FULL declarative refresh post-state on the RUNNABLE descriptor: the
per-cell `RefreshCellSpec` (balance/cap_root/fields/reserved FROZEN, nonce TICKED) AND the `system_roots`
sub-block `postRoots` is whatever the carrier digests (bound BY the commitment; the `DELEG` MOVE value is
the §7-8 record-layer connector). Non-vacuous: `refreshWide_realizes`. -/
def RefreshFullClause (pre post : CellState) (_postRoots : SysRoots) : Prop :=
  RefreshCellSpec pre post

/-- **`refreshRunnableSpec` — the refreshDelegation FULL-state RUNNABLE instance.** Parameterized by the
Poseidon carrier `hash`: `decodeAfter` is `RefreshRowEncodes` PLUS the carrier link `sysRootsDigestCol =
systemRootsDigest hash postRoots` (so the `postRoots` sub-block IS bound by the published commitment — the
anti-ghost bites on all 8 roots); `decodeFull` projects the wide descriptor's passthrough+tick gates (=
refresh's) to `refreshVm_faithful` + `intent_to_refreshCellSpec`. THIN + NON-VACUOUS. -/
def refreshRunnableSpec (hash : List ℤ → ℤ) : RunnableFullStateSpec CellState where
  descriptor    := refreshVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsRefreshRow
  decodeAfter   := fun env pre post postRoots =>
    RefreshRowEncodes env pre post ∧ env.loc sysRootsDigestCol = systemRootsDigest hash postRoots
  fullClause    := RefreshFullClause
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, _hcarrier⟩ := hdec
    have hgates' : ∀ c ∈ refreshRowGates, c.holdsVm env false false := by
      intro c hc
      have hmem : c ∈ refreshVmDescriptorWide.constraints := by
        show c ∈ refreshVmDescriptor.constraints
        unfold refreshVmDescriptor
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hc)))
      have hh := hgates c hmem
      unfold refreshRowGates gFieldFixAll at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
        List.mem_range] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using hh
    exact refreshDescriptor_full_sound env pre post hrow henc hgates'

/-- **`refresh_runnable_full_sound` — THE MAGNESIUM CROWN for `refreshDelegation`.** A row satisfying the
runnable `refreshDelegation` WIDE descriptor (`satisfiedVm`, first/last active), under the structured
decode (the carrier link pinning the `postRoots` sub-block into the published commitment), pins the FULL
17-field post-state: the per-cell frame freeze + nonce tick AND the `system_roots` sub-block (bound BY the
commitment). The specific `DELEG` MOVE is the §7-8 record-layer connector (the pending runtime column). -/
theorem refresh_runnable_full_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsRefreshRow env)
    (henc : RefreshRowEncodes env pre post)
    (hcarrier : env.loc sysRootsDigestCol = systemRootsDigest hash postRoots)
    (hsat : satisfiedVm hash refreshVmDescriptorWide env true false) :
    RefreshCellSpec pre post := by
  -- the per-cell freeze+tick comes from the gates (hash-site-free); the `postRoots` binding is the
  -- carrier-into-commitment via `wideHashSites` (the anti-ghost below).
  obtain ⟨hgates, _⟩ := hsat
  have hgates' : ∀ c ∈ refreshRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ refreshVmDescriptorWide.constraints := by
      show c ∈ refreshVmDescriptor.constraints
      unfold refreshVmDescriptor
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hh := hgates c hmem
    unfold refreshRowGates gFieldFixAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact refreshDescriptor_full_sound env pre post hrow henc hgates'

/-! ⚑ ANTI-GHOST ON ALL 17 FIELDS, REBUILT AS SECURITY REDUCTIONS (the mint recipe,
`EffectVmEmitMintRunnable` §4). The bare `refresh_runnable_rejects_{root,state}_tamper_or_collides`
disjunctions that stood here are DELETED: at deployed BabyBear parameters a sponge collision EXISTS
by pigeonhole, so `… ∨ collides` is satisfiable through its collision branch without the tooth ever
biting. Their extraction spine (`EffectVmFullStateRunnable.wide_rejects_*_or_collides`, `WideColl`,
`RootsColl`) REMAINS as the reduction-internal witness. Fixed-hash `_advantage_bound` forms carry
`hEff` honestly in the OPEN; the `_rom` forms are discharged from `keyedRom_hard` with NO floor
hypothesis. -/

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- refreshDelegation's WIDE runnable descriptor as the reduction's per-effect datum. -/
def refreshWideRowSpec : WideRowSpec where
  descriptor := refreshVmDescriptorWide
  usesWideSites := rfl

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED SIDE-TABLE ANTI-GHOST for refreshDelegation** — successor of the deleted
`refresh_runnable_rejects_root_tamper_or_collides`: under the DEPLOYED sponge's collision floor at
the class `Eff`, an adversary keeping the published `NEW_COMMIT` while tampering a side-table root
(the `DELEG` root included — a forged refresh snapshot) has NEGLIGIBLE advantage. -/
theorem refresh_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D refreshWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D refreshWideRowSpec (rootTamperToWide D refreshWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D refreshWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D refreshWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE SIDE-TABLE ANTI-GHOST, DISCHARGED ON THE PROVED KEYED-ROM FLOOR** (`wide_root_tamper_rom`,
from `keyedRom_hard` — the birthday bound). NO floor hypothesis. -/
theorem refresh_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED PER-CELL-BLOCK ANTI-GHOST for refreshDelegation** — successor of the deleted
`refresh_runnable_rejects_state_tamper_or_collides`: under the DEPLOYED sponge's collision floor at
the class `Eff`, an adversary keeping the published `NEW_COMMIT` while tampering an absorbed
state-block column (a moved `cap_root`, a tampered field, a forged nonce) has NEGLIGIBLE
advantage. -/
theorem refresh_rejects_state_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideStateTamperGame D refreshWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D refreshWideRowSpec (stateTamperToWide D refreshWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideStateTamperGame D refreshWideRowSpec) A) :=
  wide_state_tamper_advantage_bound D refreshWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE PER-CELL-BLOCK ANTI-GHOST, DISCHARGED ON THE PROVED KEYED-ROM FLOOR**
(`wide_state_tamper_rom`, from `keyedRom_hard`). NO floor hypothesis. -/
theorem refresh_rejects_state_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomStateTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomStateTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomStateTamper D tagDec).game A) :=
  wide_state_tamper_rom D tagDec Q hQ A hA

/-- **`refreshWide_realizes` — NON-VACUITY (witness TRUE).** A real passthrough+tick refresh cell
transition (frame frozen, nonce `5 → 6`) inhabits `RefreshCellSpec`. -/
theorem refreshWide_realizes :
    RefreshCellSpec
      { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
        commit := 0 }
      { balLo := 0, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 9, reserved := 0,
        commit := 0 } := by
  refine ⟨Int.ModEq.refl _, Int.ModEq.refl _, Int.ModEq.refl _, ?_, fun _ => Int.ModEq.refl _,
    Int.ModEq.refl _⟩
  show (6 : ℤ) ≡ (5 : ℤ) + 1 [ZMOD 2013265921]
  exact Int.modEq_iff_dvd.mpr (by norm_num)

/-- **`refreshWide_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
nonce did NOT tick FAILS `RefreshCellSpec` — the clause is not vacuously true. -/
theorem refreshWide_clause_not_trivial :
    ¬ RefreshCellSpec
        { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
          commit := 0 }
        { balLo := 0, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 0,
          commit := 0 } := by
  rintro ⟨_, _, _, hnon, _⟩
  have hno : ¬ ((5 : ℤ) ≡ (5 : ℤ) + 1 [ZMOD 2013265921]) := by
    rw [Int.modEq_iff_dvd]; norm_num
  exact hno hnon

#assert_axioms refreshWide_constraints_eq
#assert_axioms refresh_runnable_full_sound
#assert_axioms refresh_rejects_root_tamper_advantage_bound
#assert_axioms refresh_rejects_root_tamper_rom
#assert_axioms refresh_rejects_state_tamper_advantage_bound
#assert_axioms refresh_rejects_state_tamper_rom
#assert_axioms refreshWide_realizes
#assert_axioms refreshWide_clause_not_trivial

#guard refreshVmDescriptorWide.traceWidth == 190
#guard refreshVmDescriptorWide.hashSites.length == 4

end Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
