/-
# Dregg2.Circuit.Emit.EffectVmEmitAttenuateA — the AUTHORITY-ATTENUATION effect `attenuateA`, EMITTED
  onto the runnable EffectVM `cap_root` column, with its full-state soundness and the connector to the
  validated universe-A `attenuateA_full_sound`.

## The "ONE circuit" thesis for the cap-graph effects (this is the LOCAL TEMPLATE)

`attenuateA` is the cleanest cap-touching universe-A instance (`Inst/attenuateA.lean`): it touches the
`caps` table AS A WHOLE-FUNCTION injective digest (`funcComponent (·.caps) D hD` with the predicted post
value `attenuateSlotF caps actor idx keep`), freezes the other 16 kernel fields, and has the IN-BOUNDS
guard `idx < (caps actor).length` (attenuation FAILS CLOSED out of bounds — a `List.modify` no-op the
executor refuses). Its validation `attenuateA_full_sound ⇒ AttenuateSpec` is
DONE; this module emits the SAME effect onto the running EffectVM row layout and welds the two.

The EffectVM state block carries ONE scalar `cap_root` column (state offset 11, `state.CAP_ROOT`). The
running prover absorbs it into the GROUP-4 state-commitment chain (`site2` reads `saCol CAP_ROOT`). So at
the row level a cap-graph effect is a `cap_root` COLUMN MOVE: the post-`cap_root` is the digest of the
post cap-table, every OTHER state column frozen, and the post-state (incl. the moved `cap_root`) bound
into the published `state_commit` under Poseidon2 collision-resistance.

`attenuateVmDescriptor` emits exactly that. The post-`cap_root` is pinned to a parameter
`param.CAP_DIGEST_NEW` (the runnable column the witness generator fills with `D (attenuateSlotF …)`),
the move gate is `new_cap_root - capDigestNew = 0`, and the frame (balance limbs / nonce / 8 fields /
reserved) is frozen. We PROVE: satisfying the descriptor pins the full per-cell post-state (`cap_root`
moved to the expected digest, frame frozen) `↔` the row intent `AttenRowIntent`; and the GROUP-4 hash
sites bind the WHOLE post-state (the moved `cap_root` included) into `state_commit` — so a tampered
post-`cap_root` that still claims the published `NEW_COMMIT` is UNSAT (the anti-ghost tooth).

## The CONNECTOR — `cellProj` to universe-A's `attenuateA_full_sound`

`capRootProj D k = D k.caps` reads the SAME whole-function digest `D : Caps → ℤ` that universe-A's
`AttenuateA.capsComponent D hD` uses. `unify_attenuate` shows: when universe-A's `AttenuateSpec` holds
(so `k'.caps = attenuateSlotF k.caps actor idx keep`), the projected post-`cap_root` is EXACTLY
`D (attenuateSlotF k.caps actor idx keep)` — i.e. the column move the descriptor pins. So the runnable
`cap_root` column transition IS universe-A's `caps`-digest transition; not a fourth spec.

## THE THREE DESCRIPTOR LAYERS (read all three — the v1 boundary is CLOSED downstream in-module)

This module emits the cap-graph row at THREE layers, each a strict deepening of the last:

  1. **`attenuateVmDescriptor` (the v1 face, §1–§9).** The `cap_root` column carries the SCALAR digest
     `D caps`; the descriptor PINS the column transition `new_cap_root = param.CAP_DIGEST_NEW` (the
     witness supplies the digest) and binds that column into `state_commit`. It does NOT recompute
     `cap_root` in-row — the cap-table-is-Merkled binding rides universe-A's `Function.Injective D`
     portal (carried, realizable). The v1 BOUNDARY: the cap-table digest is a NAMED hypothesis here, not
     an in-circuit gate. This is the OPAQUE-DIGEST layer the next two layers KILL.
  2. **`attenuateVmDescriptorGenuine` (§G).** DROPS the opaque `gCapMove` and ADDS the SHARED
     `EffectVmEmitCapRoot.capRecomputeSites`: two in-row hash-sites RECOMPUTE
     `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`. The
     post `cap_root` is now a FORCED function of the bound cap-edge mutation, not a witnessed parameter
     (`attenuateGenuine_sound`), and `attenuateGenuine_binds_edge` anti-ghosts every edge field through
     the commitment. The in-circuit cap-root recompute the v1 boundary flagged as a "future IR
     extension" — DONE here, with NO deployment widening (the recomputed root rides the existing
     `saCol CAP_ROOT`, already absorbed by GROUP-4 `site2`).
  3. **`attenuateVmDescriptorGenuineNonAmp` (§G.4).** The genuine descriptor PLUS the shared
     `EffectVmEmitCapReshape.capDelegNonAmpGates`: the per-bit submask gate `granted ⊑ held` over the
     SAME `rights` felt the recompute hashes into the edge leaf. So a verifying cap-graph proof now means
     BOTH that `cap_root` is genuinely recomputed AND that the granted rights do not amplify
     (`attenuateGenuineNonAmp_in_circuit` admits, `attenuateGenuineNonAmp_rejects_amplify` rejects). This
     is the ARGUS linchpin on the delegation family, additive + width-neutral (186).

So the v1 layer's "IR GAP" is a layer boundary, not an open caveat: layers 2–3, in THIS module, supply
the in-circuit cap-root recompute + non-amplification. The remaining seam — that the recompute is the
prepend-accumulator DIGEST advance, not yet the in-row sorted-TREE update (membership-open + sorted-key
range-checks) — is Phase E (`EffectVmEmitCapReshape` §1's openable-root model is the value the digest
carries; `EffectVmEmitV2.attenuateV2_non_amp` is the Phase-B sorted open). The cap-table-as-FUNCTION
digest `D` (layer 1) is universe-A's bar, retained only for the v1 connector `capRootProj`.

  * PER-CELL / PER-ROW. Single-row AIR: one cap-graph transition + its binding into the published
    `state_commit`. Cross-row composition is the turn layer (`TurnEmit`), cited not claimed.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone);
    it is pinned only by its per-row passthrough gate.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`; the cap-table digest enters ONLY as `Function.Injective D`
(universe-A's portal). Imports
are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitAttenuateA

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop site0 site1 transitionAll boundaryFirstPins
   gate_modEq_iff not_modEq_zero_of_canon eqToModEq)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the cap-graph effect row.

The running EffectVM lays one selector per effect (`columns.rs::NUM_EFFECTS = 54`); `attenuateA` has its
own selector index. We name it `sel.ATTENUATE` abstractly (the exact index is the running prover's; we
keep the SAME gating discipline as transfer: on a genuine `attenuateA` row that selector is `1` and
`s_noop = 0`). The post cap-digest the row pins is carried in a parameter column `param.CAP_DIGEST_NEW`
(an effect parameter, the runnable column the witness generator fills with `D (attenuateSlotF …)`). -/

namespace selA
/-- The `attenuateA` effect selector column (the running prover's per-effect selector). -/
def ATTENUATE : Nat := 2
end selA

namespace paramA
/-- The post cap-table digest parameter: the value the witness fills with `D (post.caps)`. -/
def CAP_DIGEST_NEW : Nat := 2
end paramA

/-- The `attenuateA` selector as an expression. -/
def eSelAtten : EmittedExpr := .var selA.ATTENUATE

/-- The post-cap-digest param as an expression. -/
def eCapDigestNew : EmittedExpr := .var (prmCol paramA.CAP_DIGEST_NEW)

/-! ## §1 — The cap-graph row gates (term-for-term the running prover's, specialized to the row).

The cap-graph effect MOVES `cap_root` to the post cap-table digest and FREEZES the rest of the block.
Mirror of the transfer gate set, with the `cap_root` passthrough REPLACED by a `cap_root` MOVE and the
balance/nonce passthrough swapped in (a cap effect freezes the balance limbs and the nonce). -/

/-- Cap-root MOVE body: `new_cap_root - capDigestNew` (the post cap_root IS the param digest). -/
def gCapMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eCapDigestNew

/-- Balance-lo freeze body: `new_bal_lo - old_bal_lo`. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Balance-hi freeze body: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Nonce freeze body: `new_nonce - old_nonce` (a cap effect does NOT tick the cell nonce — matches the
universe-A executor, which rewrites only the `caps` field). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-- Reserved freeze body: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` freeze body: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `attenuateA` AIR identity (the fingerprint binding). -/
def attenuateVmAirName : String := "dregg-effectvm-attenuateA-v1"

/-- The cap-graph per-row gates: cap-root MOVE, balance/nonce/reserved freeze, 8 fields freeze. -/
def attenuateRowGates : List VmConstraint :=
  [ .gate gCapMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- Site 2 with the post `cap_root` absorbed (same shape as the transfer keystone's `site2`). -/
def site2 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER3
  , inputs := [ .col (saCol (state.FIELD_BASE + 5)), .col (saCol (state.FIELD_BASE + 6))
              , .col (saCol (state.FIELD_BASE + 7)), .col (saCol state.CAP_ROOT) ]
  , arity := 4 }

/-- Site 3: `state_commit = H4(inter1, inter2, inter3, record_digest)` — reading sites 0/1/2, with the
authority-residue `record_digest` (`aux_off.STATE_RECORD_DIGEST`, abs col `auxCol 96 = 186`) as the
4th input (audit P0-2; replaces the old literal `.zero`), matching the Rust GROUP-4. -/
def site3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col (auxCol aux_off.STATE_RECORD_DIGEST) ]
  , arity := 4 }

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone, so the moved `cap_root`
is bound into `state_commit` exactly as transfer binds the frozen one). -/
def attenuateHashSites : List VmHashSite :=
  [site0, site1, site2, site3]

/-- **`attenuateVmDescriptor`** — the `attenuateA` effect's concrete circuit, emitted through the
EffectVM IR: the cap-root MOVE + frame-freeze gates ++ transition continuity ++ the row-0 boundary pins,
with the 4 ordered GROUP-4 hash sites (binding the moved post-state). No balance range checks (no balance
move). -/
def attenuateVmDescriptor : EffectVmDescriptor :=
  { name := attenuateVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := attenuateRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := attenuateHashSites
  , ranges := [] }

/-! ## §3 — The cap-graph ROW INTENT (the independent faithfulness target).

`AttenRowIntent env d` is the field-level cap-graph move: the post `cap_root` IS the supplied post
cap-digest `d`, and the balance limbs / nonce / reserved / 8 fields are FIXED. This is the EffectVM-row
projection of universe-A's `AttenuateSpec` `caps` clause (the whole-function `caps` equality, projected
to the cap-DIGEST column) + the 16-field freeze (projected to the row's frozen columns). -/

/-- **`AttenRowIntent env`** — the intended cap-graph move on the row `env.loc`: post `cap_root` is the
post-cap-digest param, frame frozen. -/
def AttenRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) ≡ env.loc (prmCol paramA.CAP_DIGEST_NEW) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
  ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
  ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) [ZMOD 2013265921]
  ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
      ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921])

/-- The row is an `attenuateA` row: `s_attenuate = 1`, `s_noop = 0`. -/
def IsAttenRow (env : VmRowEnv) : Prop :=
  env.loc selA.ATTENUATE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`attenuateRowGates_holds_iff`** — on an `attenuateA` row, the emitted per-row gates all hold IFF
`AttenRowIntent` holds. The gate bodies are the running prover's polynomials (cap-root move + frame
freeze); they pin EXACTLY the intent move. -/
theorem attenuateRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ attenuateRowGates, c.holdsVm env false false) ↔ AttenRowIntent env := by
  unfold attenuateRowGates gFieldFixAll AttenRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapMove, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eCapDigestNew, eSub, EmittedExpr.eval] at hCap hLo hHi hNon hRes
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
    · simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hCap
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **`attenuateVm_faithful` — THE deliverable.** On an `attenuateA` row, the emitted descriptor's
per-row gates hold IFF the cap-graph intent holds. -/
theorem attenuateVm_faithful (env : VmRowEnv) :
    (∀ c ∈ attenuateRowGates, c.holdsVm env false false) ↔ AttenRowIntent env :=
  attenuateRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): a wrong cap-root move fails the emitted descriptor. -/

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` is NOT the supplied post-cap-digest
fails the `gCapMove` gate (UNSAT). -/
theorem attenuateVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.CAP_ROOT)
      ∧ env.loc (saCol state.CAP_ROOT) < 2013265921)
    (hcanonDig : 0 ≤ env.loc (prmCol paramA.CAP_DIGEST_NEW)
      ∧ env.loc (prmCol paramA.CAP_DIGEST_NEW) < 2013265921)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
  exact not_modEq_zero_of_canon (by ring) hcanonNew hcanonDig hwrong

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem attenuateVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ AttenRowIntent env) :
    ¬ (∀ c ∈ attenuateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((attenuateVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog).

Decode the row into a concrete `(pre, post)` `CellState` via a cap-graph `RowEncodes`. The descriptor's
satisfaction forces the post-state's `cap_root` = the post cap-digest, every other column frozen. -/

/-- **`CapRowEncodes env pre post capDigestNew`** — the row decodes to `(pre, post)` cell states with
the post cap-digest carried in `param.CAP_DIGEST_NEW`. (Same shape as the transfer keystone's
`RowEncodes`, minus the transfer params.) -/
def CapRowEncodes (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramA.CAP_DIGEST_NEW) = capDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell cap-graph spec: the moved cell's WHOLE post-state is `pre` with `cap_root` set to the
new cap-digest, every other field frozen. This is the per-cell projection of universe-A's `AttenuateSpec`
(`caps` whole-function move ⟹ cap-DIGEST column move; 16-field freeze ⟹ frame freeze). -/
def CapCellSpec (pre post : CellState) (capDigestNew : ℤ) : Prop :=
  post.capRoot ≡ capDigestNew [ZMOD 2013265921]
  ∧ post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- Under `CapRowEncodes`, `AttenRowIntent` IS the structured per-cell `CapCellSpec`. -/
theorem intent_to_capCellSpec (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew) (hint : AttenRowIntent env) :
    CapCellSpec pre post capDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hpDig]; exact hcap
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`attenuateDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under
the `CapRowEncodes` decoding forces the structured per-cell `CapCellSpec` (post `cap_root` = the
predicted cap-digest, frame frozen). -/
theorem attenuateDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateRowGates, c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  intent_to_capCellSpec env pre post capDigestNew henc ((attenuateVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, cap-root included).

The GROUP-4 sites (identical to the transfer keystone's) absorb the post `cap_root` into the published
`state_commit`. Under `Poseidon2SpongeCR hash`, two satisfying rows with the same published `NEW_COMMIT`
have identical absorbed columns — so a tampered post-`cap_root` that claims the published commitment is
impossible. We reuse the keystone's `absorbedCols`/`commit_eq_commitOf` machinery (the hash chain IS the
transfer keystone's, only the `cap_root` column now MOVES). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit_of_injective)

/-- `attenuateHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites` (same ordered
4-site chain, same absorbed columns incl. the post `cap_root`). So all the keystone's commitment-binding
lemmas apply verbatim. -/
theorem attenuateHashSites_eq : attenuateHashSites = transferHashSites := rfl

/-- **`attenuateDescriptor_commit_binds_state` — the whole-state tooth.** Two `attenuateA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved
post-`cap_root` (an absorbed column, site 2) included. So a prover CANNOT tamper the post-`cap_root` (or
any absorbed cell) while keeping the published commitment. -/
theorem attenuateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ attenuateHashSites)
    (hs₂ : siteHoldsAll hash e₂ attenuateHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [attenuateHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit_of_injective hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `capRootProj` to universe-A's `attenuateA_full_sound`.

`capRootProj D k = D k.caps` reads the SAME whole-function digest `D : Caps → ℤ` that
`AttenuateA.capsComponent D hD` uses. The unification: a committed universe-A `AttenuateSpec` makes the
projected post-`cap_root` EXACTLY `D (attenuateSlotF k.caps actor idx keep)` — the cap-digest the
descriptor's `param.CAP_DIGEST_NEW` carries. So the runnable `cap_root` column transition IS universe-A's
`caps`-digest transition. -/

open Dregg2.Circuit.Inst.AttenuateA (AttenuateArgs)
open Dregg2.Circuit.Spec.AuthorityAttenuation (AttenuateSpec)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value for kernel state `k`: the whole-function
digest `D` of the cap-table (the SAME `D` universe-A's `capsComponent D hD` digests). -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries: `D` of the attenuated
cap-table. -/
def attenCapDigestNew (D : Caps → ℤ)
    (s : RecChainedState) (args : AttenuateArgs) : ℤ :=
  D (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)

/-- **`unify_attenuate` — THE CONNECTOR.** When universe-A's `AttenuateSpec` holds, the projected
post-`cap_root` is EXACTLY the attenuated cap-digest `attenCapDigestNew D s args` — i.e. the column move
the descriptor pins. So `CapCellSpec`'s `cap_root` clause IS universe-A's `caps`-clause, projected to the
digest column. (The frame clauses are universe-A's 16-field freeze projected to the frozen columns;
`balLo`/`balHi`/`nonce`/`reserved`/`fields` are `0`-valued in the projection of a `caps`-only effect, so
they freeze trivially. We discharge the `cap_root` leg — the genuine cap-graph content.) -/
theorem unify_attenuate (D : Caps → ℤ)
    (s : RecChainedState) (args : AttenuateArgs)
    (s' : RecChainedState)
    (hspec : AttenuateSpec s args.actor args.idx args.keep s') :
    capRootProj D s'.kernel = attenCapDigestNew D s args := by
  -- AttenuateSpec is `idx < length ∧ s'.kernel.caps = attenuateSlotF s.kernel.caps actor idx keep ∧ …`.
  obtain ⟨_, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (attenuateSlotF s.kernel.caps args.actor args.idx args.keep)
  rw [hcaps]

/-- **`unify_attenuate_via_full_sound` — the runnable column move inherits the VALIDATED guarantee.**
Chaining universe-A's `attenuateA_full_sound` (a satisfying v2 full-state witness ⟹ `AttenuateSpec`)
with `unify_attenuate`: a satisfying universe-A witness forces the projected post-`cap_root` to the
attenuated cap-digest — the EXACT column value the runnable descriptor's `param.CAP_DIGEST_NEW` carries.
So the runnable `cap_root` move is universe-A's validated `caps` transition, not a fourth spec. -/
theorem unify_attenuate_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs)
    (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.AttenuateA.attenuateE D hD)
        (encodeE2 S (Dregg2.Circuit.Inst.AttenuateA.attenuateE D hD) s args s')) :
    capRootProj D s'.kernel = attenCapDigestNew D s args :=
  unify_attenuate D s args s'
    (Dregg2.Circuit.Inst.AttenuateA.attenuateA_full_sound S D hD hRest hLog s args s' h)

/-! ## §9 — NON-VACUITY: a concrete cap-graph row that satisfies the intent, and one that does not.

A row `capGoodRow`: a cap-graph move where `cap_root 11 → 77` (the new digest), nonce `5 → 5` frozen,
everything else `0`/frozen. And `capBadRow`: same but post-`cap_root` forged to `999 ≠ 77`. -/

/-- A concrete `attenuateA` row: `cap_root` moves to the param digest `77`, frame frozen at `0`. -/
def capGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selA.ATTENUATE then 1
    else if v = sbCol state.CAP_ROOT then 11
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramA.CAP_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `capGoodRow` is a genuine `attenuateA` row. -/
theorem capGoodRow_isAttenRow : IsAttenRow capGoodRow := by
  unfold IsAttenRow capGoodRow
  constructor <;> norm_num [selA.ATTENUATE, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT,
    paramA.CAP_DIGEST_NEW]

set_option backward.isDefEq.respectTransparency false in
/-- **NON-VACUITY (witness TRUE).** `capGoodRow` REALIZES the cap-graph intent: post `cap_root = 77` =
the param digest, balance/nonce/reserved/fields frozen at `0`. -/
theorem capGoodRow_realizes_intent : AttenRowIntent capGoodRow := by
  -- prove the ℤ-equality skeleton (the named cap columns vs frozen else-0 columns are distinct),
  -- then lift each conjunct to the field-faithful `≡ [ZMOD p]` move via `eqToModEq`.
  have hZ : capGoodRow.loc (saCol state.CAP_ROOT) = capGoodRow.loc (prmCol paramA.CAP_DIGEST_NEW)
      ∧ capGoodRow.loc (saCol state.BALANCE_LO) = capGoodRow.loc (sbCol state.BALANCE_LO)
      ∧ capGoodRow.loc (saCol state.BALANCE_HI) = capGoodRow.loc (sbCol state.BALANCE_HI)
      ∧ capGoodRow.loc (saCol state.NONCE) = capGoodRow.loc (sbCol state.NONCE)
      ∧ capGoodRow.loc (saCol state.RESERVED) = capGoodRow.loc (sbCol state.RESERVED)
      ∧ (∀ i, i < 8 → capGoodRow.loc (saCol (state.FIELD_BASE + i))
            = capGoodRow.loc (sbCol (state.FIELD_BASE + i))) := by
   unfold capGoodRow
   -- the named cap columns vs the frozen-frame else-0 columns are distinct; discharge by simp+omega.
   refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
   · -- both `saCol CAP_ROOT` (col 87) and `prmCol CAP_DIGEST_NEW` (col 56) read 77, via distinct branches.
     have hsa : capGoodRow.loc (saCol state.CAP_ROOT) = 77 := by
       show (if saCol state.CAP_ROOT = selA.ATTENUATE then (1:ℤ)
         else if saCol state.CAP_ROOT = sbCol state.CAP_ROOT then 11
         else if saCol state.CAP_ROOT = saCol state.CAP_ROOT then 77
         else if saCol state.CAP_ROOT = prmCol paramA.CAP_DIGEST_NEW then 77 else 0) = 77
       rw [if_neg (by simp only [saCol, selA.ATTENUATE, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
         NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]; omega),
         if_neg (by simp only [saCol, sbCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE,
           NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]; omega), if_pos rfl]
     have hprm : capGoodRow.loc (prmCol paramA.CAP_DIGEST_NEW) = 77 := by
       show (if prmCol paramA.CAP_DIGEST_NEW = selA.ATTENUATE then (1:ℤ)
         else if prmCol paramA.CAP_DIGEST_NEW = sbCol state.CAP_ROOT then 11
         else if prmCol paramA.CAP_DIGEST_NEW = saCol state.CAP_ROOT then 77
         else if prmCol paramA.CAP_DIGEST_NEW = prmCol paramA.CAP_DIGEST_NEW then 77 else 0) = 77
       rw [if_neg (by simp only [prmCol, selA.ATTENUATE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
         STATE_SIZE, paramA.CAP_DIGEST_NEW]; omega),
         if_neg (by simp only [prmCol, sbCol, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
           state.CAP_ROOT, paramA.CAP_DIGEST_NEW]; omega),
         if_neg (by simp only [prmCol, saCol, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE,
           NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramA.CAP_DIGEST_NEW]; omega),
         if_pos rfl]
     show capGoodRow.loc (saCol state.CAP_ROOT) = capGoodRow.loc (prmCol paramA.CAP_DIGEST_NEW)
     rw [hsa, hprm]
   all_goals
     simp only [saCol, sbCol, prmCol, selA.ATTENUATE, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
       NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, state.BALANCE_LO, state.BALANCE_HI,
       state.NONCE, state.RESERVED, state.FIELD_BASE, paramA.CAP_DIGEST_NEW]
   · norm_num
   · norm_num
   · norm_num
   · norm_num
   · intro i hi
     have e1 : ¬ (76 + (3 + i) = 2) := by omega
     have e2 : ¬ (76 + (3 + i) = 65) := by omega
     have e3 : ¬ (76 + (3 + i) = 87) := by omega
     have e4 : ¬ (76 + (3 + i) = 70) := by omega
     have f1 : ¬ (54 + (3 + i) = 2) := by omega
     have f2 : ¬ (54 + (3 + i) = 65) := by omega
     have f3 : ¬ (54 + (3 + i) = 87) := by omega
     have f4 : ¬ (54 + (3 + i) = 70) := by omega
     simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg f1, if_neg f2, if_neg f3, if_neg f4]
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hZ
  exact ⟨eqToModEq g1, eqToModEq g2, eqToModEq g3, eqToModEq g4, eqToModEq g5,
    fun i hi => eqToModEq (g6 i hi)⟩

/-- A forged `attenuateA` row: `capGoodRow` with the post-`cap_root` tampered to `999 ≠ 77`. -/
def capBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else capGoodRow.loc v
  nxt := capGoodRow.nxt
  pub := capGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `capBadRow`'s post-`cap_root` is NOT the
param digest, so the `gCapMove` gate REJECTS it — a concrete UNSAT. -/
theorem capBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false := by
  -- the post-cap-root column is forged to 999; the param digest column is 77.
  have hsa : capBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else capGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hne1 : ¬ (saCol state.CAP_ROOT = prmCol paramA.CAP_DIGEST_NEW) := by
    simp only [saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramA.CAP_DIGEST_NEW]
    omega
  have hprm : capBadRow.loc (prmCol paramA.CAP_DIGEST_NEW) = 77 := by
    show (if prmCol paramA.CAP_DIGEST_NEW = saCol state.CAP_ROOT then (999:ℤ)
      else capGoodRow.loc (prmCol paramA.CAP_DIGEST_NEW)) = 77
    rw [if_neg (fun h => hne1 h.symm)]
    show (if prmCol paramA.CAP_DIGEST_NEW = selA.ATTENUATE then (1:ℤ)
      else if prmCol paramA.CAP_DIGEST_NEW = sbCol state.CAP_ROOT then 11
      else if prmCol paramA.CAP_DIGEST_NEW = saCol state.CAP_ROOT then 77
      else if prmCol paramA.CAP_DIGEST_NEW = prmCol paramA.CAP_DIGEST_NEW then 77 else 0) = 77
    norm_num [prmCol, saCol, sbCol, selA.ATTENUATE, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramA.CAP_DIGEST_NEW]
  -- FIELD-FAITHFUL: the forged `999` and the digest `77` are both canonical (`0 ≤ · < p`), so the
  -- residual `999 − 77` cannot vanish mod `p` — the gate is UNSAT (no wrap-around forgery).
  apply attenuateVm_rejects_wrong_capRoot capBadRow
  · rw [hsa]; norm_num
  · rw [hprm]; norm_num
  · rw [hsa, hprm]; norm_num

/-! ## §G — THE GENUINE CLASS-A DESCRIPTOR — `cap_root` RECOMPUTED in-row (the opaque-digest KILL).

§1–§9 above bind the `cap_root` COLUMN move (`new_cap_root = param.CAP_DIGEST_NEW`), where the digest is
an OPAQUE PARAMETER the prover supplies. That is class C: the cap-table mutation is *asserted*, not
*recomputed* (the ledger's Tier-1 cap-family gap). This section CLOSES that gap, exactly as
`EffectVmEmitEscrowRoot` closed the escrow side-table gap:

  * DROP the opaque `gCapMove` gate. The `cap_root` move is not a free-parameter equality.
  * ADD the SHARED `EffectVmEmitCapRoot.capRecomputeSites`: two in-row hash-sites that RECOMPUTE
    `new_cap_root = hash[ edge_leaf, old_cap_root ]` with `edge_leaf = hash[holder,target,rights,op]`.
    The new root is FORCED by the bound cap-edge mutation + the old root, not chosen.
  * The new-root carrier IS `saCol state.CAP_ROOT` — already absorbed into `state_commit` by GROUP-4
    `site2` (it is the 12th `absorbedCols` element). So the recomputed root is bound by the SAME deployed
    commitment chain, with NO width change (unlike escrow's aux-96 root, which awaits task #91).

The class-A theorem `attenuateGenuine_sound` proves: satisfying the genuine descriptor's gates+recompute
forces the FULL per-cell post-state — frame frozen AND `post.capRoot` GENUINELY equal to
`hash[edge_leaf, pre.capRoot]` (the forced advance) — and `attenuateGenuine_binds_edge` anti-ghosts every
edge field + the old root through the commitment. The opaque additive/parameter step is GONE. -/

open Dregg2.Circuit.Emit.EffectVmEmitCapRoot
  (capRecomputeSites capRootHolds CAP_ROOT_AFTER CAP_ROOT_BEFORE CAP_EDGE_LEAF
   edgeLeafOf capAdvanceOf capRootAdvance_forced capRoot_binds_edge siteCapEdgeLeaf siteCapRootAdvance)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)

/-- The genuine cap-graph per-row gates: the frame freeze (balance/nonce/reserved/8 fields), WITHOUT the
opaque `gCapMove` — the `cap_root` move is now FORCED by the recompute sites, not a parameter gate. -/
def attenuateGenuineRowGates : List VmConstraint :=
  [ .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix, .gate gResFix ] ++ gFieldFixAll

/-- **`shiftInputDigest n`** — rebase a `.digest k` reference by `n` sites. `.col`/`.zero` are
position-free and pass through. -/
def shiftInputDigest (n : Nat) : HashInput → HashInput
  | .digest k => .digest (k + n)
  | i         => i

/-- **`shiftSiteDigests n s`** — rebase every `.digest k` reference in a site by `n`. `HashInput.digest`
is a POSITIONAL index into the descriptor's own site list, so PREPENDING `n` sites to a chain must
rebase the chain's internal cross-references or they silently resolve to the prepended sites. -/
def shiftSiteDigests (n : Nat) (s : VmHashSite) : VmHashSite :=
  { s with inputs := s.inputs.map (shiftInputDigest n) }

/-- The genuine GROUP-4 commitment chain, PRECEDED by the two cap-root recompute sites. The recompute
fires first (`leaf`, then `advance` into `saCol CAP_ROOT`); then GROUP-4 absorbs the recomputed
`cap_root` into `state_commit` exactly as the transfer keystone absorbs it.

The GROUP-4 chain is REBASED by `capRecomputeSites.length` = 2. `site3`'s `.digest 0/1/2` name
`site0/site1/site2` POSITIONALLY; prepending the two recompute sites shifts every ordinal, so without
the rebase `state_commit` would absorb `[edge_leaf(102), cap_root(87), inter1(98)]` instead of the
GROUP-4 chain `[inter1(98), inter2(99), inter3(100)]` — leaving `state_after[4..10]` UNCOMMITTED and
sites 3/4 (cols 99/100) dead carriers. That is exactly the defect this emit carried until 2026-07-17
(now asserted fixed by `circuit/src/cap_delegation_nonamp_descriptor.rs::state_commit_absorbs_group4_chain`);
all 27 other emitted descriptors index correctly because none of them prepend. -/
def attenuateGenuineHashSites : List VmHashSite :=
  capRecomputeSites ++ attenuateHashSites.map (shiftSiteDigests capRecomputeSites.length)

/-- **`attenuateVmDescriptorGenuine`** — the GENUINE `attenuateA` circuit: the frame-freeze gates ++
transition continuity ++ boundary pins, with the recompute sites PREPENDED to the GROUP-4 chain. The
post-`cap_root` is now a FORCED recomputation, not an opaque parameter. -/
def attenuateVmDescriptorGenuine : EffectVmDescriptor :=
  { name := attenuateVmAirName ++ "-genuine"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := attenuateGenuineRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := attenuateGenuineHashSites
  , ranges := [] }

/-- **`attenuateVmDescriptorGenuineNoRecompute`** — the GENUINE `attenuateA` circuit WITHOUT the cap-root
RECOMPUTE hash-site (the `capRecomputeSites` `siteCapRootAdvance` that pins `saCol CAP_ROOT` (col 87) as a
poseidon OUTPUT `hash[edge_leaf, before_root]`). The genuine frame-freeze row gates are kept (no `gCapMove`
parameter equality, no `gCapPass` freeze — `saCol CAP_ROOT` is free to MOVE), and the bare GROUP-4
commitment chain (`attenuateHashSites`) is kept — so `site2` still folds the post `cap_root` (col 87) into
`state_commit` AS AN INPUT (`.col (saCol state.CAP_ROOT)`), the note-spend-shaped commitment fold.

This is the face the cap-tree WRITE descriptors (`…WriteV3`) ride: the post cap-root must be bound by the
genuine sorted-tree `MapOp` write (`insertWriteOp`/`removeWriteOp`'s `newRoot := saCol CAP_ROOT`) AND folded
into the commitment — NOT bound a SECOND, incompatible way by the prepend-accumulator `siteCapRootAdvance`.
The `capRecomputeSites` advance is a DIFFERENT function from the sorted depth-16 CanonicalHeapTree write, so
the two disagree for any honest c-list (matching them inverts Poseidon) ⇒ the wrapper was UNPROVABLE. Mirror
of `noteSpendV3`: the nullifier root is `MapOp`-defined-ONLY and only ABSORBED into the commitment as an
input — never a hash OUTPUT. Here `cap_root` gets the same treatment. -/
def attenuateVmDescriptorGenuineNoRecompute : EffectVmDescriptor :=
  { name := attenuateVmAirName ++ "-genuine-norecompute"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := attenuateGenuineRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := attenuateHashSites
  , ranges := [] }

/-- The no-recompute genuine face DROPS exactly the two `capRecomputeSites` hash-sites (the edge-leaf +
the col-87 advance) from the genuine face — `site2` still absorbs `saCol CAP_ROOT` into the commitment, so
the cap-root remains COMMITTED, just not OUTPUT-pinned. Same width, same constraints.

The genuine face's chain is the no-recompute chain REBASED by the two prepended sites
(`shiftSiteDigests capRecomputeSites.length`) — the no-recompute face prepends nothing, so it carries the
GROUP-4 ordinals unshifted. Dropping the sites and dropping the shift go together. -/
theorem attenuateGenuineNoRecompute_drops_recompute :
    attenuateVmDescriptorGenuineNoRecompute.hashSites = attenuateHashSites
    ∧ attenuateVmDescriptorGenuine.hashSites
        = capRecomputeSites
            ++ attenuateVmDescriptorGenuineNoRecompute.hashSites.map
                 (shiftSiteDigests capRecomputeSites.length)
    ∧ attenuateVmDescriptorGenuineNoRecompute.constraints = attenuateVmDescriptorGenuine.constraints
    ∧ attenuateVmDescriptorGenuineNoRecompute.traceWidth = EFFECT_VM_WIDTH :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The genuine cap-graph per-row gates with the nonce FREEZE (`gNonceFix`: `after.nonce == before.nonce`)
swapped for the transfer/noteSpend TICK gate (`EffectVmEmitTransfer.gNonce`:
`after.nonce − before.nonce − (1 − s_noop) = 0` ⇒ the nonce ADVANCES by one on a non-NoOp row, holds
trivially on a NoOp pad). EVERY OTHER gate (the two balance freezes, the reserved freeze, the eight field
freezes) is `attenuateGenuineRowGates` verbatim.

This is the face the cap-tree WRITE descriptors (`…WriteV3`) must ride: the cap-family effects
(delegate / introduce / delegateAtten / grantCap / revokeDelegation) all TICK the agent nonce in the
genuine executor (the per-turn prologue bump — `post.nonce = pre.nonce + 1`), so the FREEZE gate
(`gNonceFix`) is jointly UNSAT with every honest cap-write trace and the wrapper is UNPROVABLE on the wire.
Mirror of `EffectVmEmitRotationV3.setFieldRowGatesTick` (the setField tick face), which fixed exactly this
class — a nonce-freeze gate pasted onto a moving effect. -/
def attenuateGenuineRowGatesTick : List VmConstraint :=
  [ .gate gBalLoFix, .gate gBalHiFix, .gate EffectVmEmitTransfer.gNonce, .gate gResFix ] ++ gFieldFixAll

/-- **`attenuateVmDescriptorGenuineNoRecomputeTick`** — the no-recompute genuine cap-graph face on the
nonce-TICK gate set (`attenuateGenuineRowGatesTick`). Identical to `attenuateVmDescriptorGenuineNoRecompute`
in name/width/PI/hashSites/ranges; only the single nonce gate moves freeze → tick, so the cap-WRITE wrappers
that ride it admit the honest nonce-advancing trace. The bare GROUP-4 commitment chain
(`attenuateHashSites`) is kept verbatim, so `site2` still folds the post `cap_root` (col 87) into
`state_commit` as an input (the cap-write map-op is what FORCES that root). -/
def attenuateVmDescriptorGenuineNoRecomputeTick : EffectVmDescriptor :=
  { name := attenuateVmAirName ++ "-genuine-norecompute-tick"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := pi.V1_PI_COUNT
  , constraints := attenuateGenuineRowGatesTick ++ transitionAll ++ boundaryFirstPins
  , hashSites := attenuateHashSites
  , ranges := [] }

/-- The tick face shares the no-recompute face's hashSites / traceWidth / PI count (only the nonce gate
moves freeze → tick in the constraint list). The cap-write wrappers' `_forces_write` lemmas read ONLY the
appended cap-write map-ops (via `List.mem_append_right`), never the nonce gate, so the gate swap is
invisible to them — this lemma records the shape parity the registry / drift checks lean on. -/
theorem attenuateGenuineNoRecomputeTick_shape :
    attenuateVmDescriptorGenuineNoRecomputeTick.hashSites
        = attenuateVmDescriptorGenuineNoRecompute.hashSites
    ∧ attenuateVmDescriptorGenuineNoRecomputeTick.traceWidth = EFFECT_VM_WIDTH
    ∧ attenuateVmDescriptorGenuineNoRecomputeTick.piCount
        = attenuateVmDescriptorGenuineNoRecompute.piCount
    ∧ attenuateVmDescriptorGenuineNoRecomputeTick.ranges
        = attenuateVmDescriptorGenuineNoRecompute.ranges :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`CapCellSpecGenuine hash pre post`** — the GENUINE per-cell cap-graph spec: `post.capRoot` is the
RECOMPUTED advance `hash[ hash[holder,target,rights,op], pre.capRoot ]` (a function of the bound edge +
old root — NOT an opaque parameter), the balance limbs / nonce / 8 fields / reserved frozen. The edge
fields are read off the row's param block. -/
def CapCellSpecGenuine (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) : Prop :=
  post.capRoot
      = capAdvanceOf hash
          (edgeLeafOf hash (env.loc (prmCol HOLDER)) (env.loc (prmCol TARGET))
            (env.loc (prmCol RIGHTS)) (env.loc (prmCol OP)))
          pre.capRoot
  ∧ post.balLo ≡ pre.balLo [ZMOD 2013265921]
  ∧ post.balHi ≡ pre.balHi [ZMOD 2013265921]
  ∧ post.nonce ≡ pre.nonce [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ pre.fields i [ZMOD 2013265921])
  ∧ post.reserved ≡ pre.reserved [ZMOD 2013265921]

/-- The genuine frame-freeze gates hold IFF the frame is frozen (no `cap_root` clause — the move is in the
recompute). -/
theorem attenuateGenuineRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false) ↔
      ( env.loc (saCol state.BALANCE_LO) ≡ env.loc (sbCol state.BALANCE_LO) [ZMOD 2013265921]
      ∧ env.loc (saCol state.BALANCE_HI) ≡ env.loc (sbCol state.BALANCE_HI) [ZMOD 2013265921]
      ∧ env.loc (saCol state.NONCE) ≡ env.loc (sbCol state.NONCE) [ZMOD 2013265921]
      ∧ env.loc (saCol state.RESERVED) ≡ env.loc (sbCol state.RESERVED) [ZMOD 2013265921]
      ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i))
          ≡ env.loc (sbCol (state.FIELD_BASE + i)) [ZMOD 2013265921]) ) := by
  unfold attenuateGenuineRowGates gFieldFixAll
  constructor
  · intro h
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hRes
    refine ⟨(gate_modEq_iff (by ring)).mp hLo, (gate_modEq_iff (by ring)).mp hHi,
      (gate_modEq_iff (by ring)).mp hNon, (gate_modEq_iff (by ring)).mp hRes, ?_⟩
    intro i hi
    have hfi := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at hfi
    exact (gate_modEq_iff (by ring)).mp hfi
  · rintro ⟨hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hLo
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hHi
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hNon
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr hRes
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      exact (gate_modEq_iff (by ring)).mpr (hFld i hi)

/-- **`attenuateGenuine_sound` — THE CLASS-A THEOREM.** Satisfying the genuine descriptor's frame-freeze
gates AND the cap-root recompute (under the abstract sponge `hash`), with the row decoded by
`CapRowEncodes`, forces the GENUINE full per-cell post-state: `post.capRoot` is the RECOMPUTED advance
`hash[edge_leaf, pre.capRoot]` (FORCED, not an opaque parameter), every other field frozen. This is the
escrow-grade class-A bar applied to the cap family — the opaque digest is GONE. -/
theorem attenuateGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hLo, hHi, hNon, hRes, hFld⟩ := (attenuateGenuineRowGates_holds_iff env).mp hgates
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.capRoot = advanceOf hash (leaf) pre.capRoot — the FORCED recompute.
    have hadv := capRootAdvance_forced hash env hrec
    -- CAP_ROOT_AFTER = saCol CAP_ROOT = post.capRoot ; CAP_ROOT_BEFORE = sbCol CAP_ROOT = pre.capRoot
    rw [show CAP_ROOT_AFTER = saCol state.CAP_ROOT from rfl, hsaCap,
        show CAP_ROOT_BEFORE = sbCol state.CAP_ROOT from rfl, hsbCap] at hadv
    exact hadv
  · rw [← hsaLo, ← hsbLo]; exact hLo
  · rw [← hsaHi, ← hsbHi]; exact hHi
  · rw [← hsaN, ← hsbN]; exact hNon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hFld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hRes

/-! ### §G.2 — The genuine anti-ghost: tampering ANY edge field / old root moves `cap_root` ⇒ UNSAT.

`capRoot_binds_edge` (the shared primitive) already proves: two recompute-honest rows with EQUAL new
`cap_root` carriers share the old root AND every edge field. Since `cap_root` IS an absorbed `state_commit`
column, two rows with equal `state_commit` have equal `cap_root` (the keystone's
`attenuateDescriptor_commit_binds_state`), hence equal edge content. So a prover CANNOT tamper the
attenuated cap-edge while keeping the published commitment. -/

/-- **`attenuateGenuine_binds_edge` — the genuine class-A tooth.** Two genuine rows whose recompute holds
and whose published `state_commit`s are EQUAL share the OLD `cap_root` AND every bound edge field
(holder/target/rights/op). Chains the commitment binding (`cap_root` is absorbed) with the shared
`capRoot_binds_edge`. Tampering ANY edge field moves `cap_root`, moves `state_commit` ⇒ UNSAT. -/
theorem attenuateGenuine_binds_edge (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsCommit₁ : siteHoldsAll hash e₁ attenuateHashSites)
    (hsCommit₂ : siteHoldsAll hash e₂ attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol HOLDER) = e₂.loc (prmCol HOLDER)
    ∧ e₁.loc (prmCol TARGET) = e₂.loc (prmCol TARGET)
    ∧ e₁.loc (prmCol RIGHTS) = e₂.loc (prmCol RIGHTS)
    ∧ e₁.loc (prmCol OP) = e₂.loc (prmCol OP) := by
  -- the commitment binds the absorbed `cap_root` column (12th absorbedCol).
  have hcols := attenuateDescriptor_commit_binds_state hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hcommit
  have hcap : e₁.loc (saCol state.CAP_ROOT) = e₂.loc (saCol state.CAP_ROOT) := by
    have := congrArg (fun l => l.getD 11 0) hcols
    simpa only [absorbedCols, List.getD_cons_succ, List.getD_cons_zero] using this
  -- the new-root carrier IS saCol CAP_ROOT; feed equality into the shared edge binding.
  have hroot : e₁.loc CAP_ROOT_AFTER = e₂.loc CAP_ROOT_AFTER := hcap
  have hedge := capRoot_binds_edge hash hCR e₁ e₂ hrec₁ hrec₂ hroot
  rw [show CAP_ROOT_BEFORE = sbCol state.CAP_ROOT from rfl] at hedge
  exact hedge

/-! ### §G.3 — NON-VACUITY for the genuine descriptor (the recompute fires + an op-tamper is refuted). -/

open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (goodCapRow goodCapRow_recomputes tampered_op_moves_root)

/-- **NON-VACUITY (witness TRUE).** `goodCapRow` satisfies the cap-root recompute under the concrete
sponge — so the genuine descriptor's recompute predicate is INHABITED. -/
theorem attenuateGenuineGoodRow_recomputes : capRootHolds Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN goodCapRow :=
  goodCapRow_recomputes

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** The genuine recomputed roots for a delegate
edge (op=1) vs a revoke edge (op=3) DIFFER — so a tampered op cannot keep the published `cap_root`: a
concrete UNSAT for the genuine descriptor. -/
theorem attenuateGenuine_op_tamper_refuted :
    capAdvanceOf Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN
        (edgeLeafOf Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN 7 13 42 1) 1000
      ≠ capAdvanceOf Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN
        (edgeLeafOf Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cN 7 13 42 3) 1000 :=
  tampered_op_moves_root

/-! ## §G.4 — THE GENUINE NON-AMP DESCRIPTOR — cap-root recompute AND in-circuit `granted ⊑ held`.

§G binds the `cap_root` GENUINELY (the recompute), and `attenuateGenuine_binds_edge` anti-ghosts every
edge field — so a tampered `rights` MOVES the root. But binding the root is not yet ENFORCING
non-amplification: a row may recompute a perfectly-bound root for an edge whose granted `rights` EXCEED
the delegator's held rights. §G.4 closes that: it appends the SHARED `EffectVmEmitCapReshape`
delegation non-amp gates (`capDelegNonAmpGates`) — the per-bit submask `granted ⊑ held`.

### The interlock, and the two emit defects that used to break it (both fixed 2026-07-17)

The delegation non-amp gates' GRANTED mask reconstructs `prmCol cp.RIGHTS` = **column 72**, the SAME
`rights` felt `siteCapEdgeLeaf` hashes into the recomputed root. So on this descriptor the two legs
INTERLOCK on one felt: an amplifying `rights` either breaks the granted-recon gate, or — if the bits are
moved to match — breaks the per-bit submask gate. `emitVmJson attenuateVmDescriptorGenuineNonAmp` now
produces

    v75 − Σ_{i<8} v(120+i)·2ⁱ     (held recon,    prmCol 7)
    v72 − Σ_{i<8} v(128+i)·2ⁱ     (granted recon, prmCol cp.RIGHTS)

**Defect 1 (was): a param-index/column conflation.** `EffectVmEmitCapReshape.dcol.GRANTED_MASK :=
cp.RIGHTS`, and `cp.RIGHTS = 4` is a param INDEX; the column is `prmCol 4 = 72`. `gMaskRecon` consumes a
raw COLUMN, so the gate emitted `v4` — an effect-SELECTOR column — and `dcol.HELD_MASK := 7` emitted
`v7`. Nothing related those to the rights param, so a prover could confer ARBITRARY rights through a
perfectly-bound `cap_root`. Fixed by `prmCol`-wrapping both `gMaskRecon` call sites.

**Defect 2 (was): the GROUP-4 `Digest k` ordinals were never rebased on the prepend.** `attenuateHashSites`
is now `.map (shiftSiteDigests capRecomputeSites.length)` at the prepend — see `attenuateGenuineHashSites`.

**What was never wrong.** `capDeleg_nonAmp_in_circuit`, `capDeleg_rejects_amplify`,
`attenuateGenuineNonAmp_in_circuit` and `attenuateGenuineNonAmp_rejects_amplify` quantify over
`dcol.grantedBit i` / `dcol.heldBit i` (cols `128+i` / `120+i`) and were TRUE under both emits — their
STATEMENTS never mention `cp.RIGHTS`. Only the PROSE claimed the link, which is why no proof and no
`#assert_axioms` flagged it: prose is not a proof, and `#assert_axioms` cannot see a false sentence. Both
defects were found by the Rust differential, not by Lean.

⚠ RESIDUAL — the HELD mask (`prmCol dcol.HELD_MASK`, col 75) is a FREE PARAM on this descriptor: no
hash-site absorbs it, no PI binds it. The interlock stops rights-felt FORGERY, but `granted ⊑ held`
bounds the committed rights only by a mask the PROVER CHOSE. Binding col 75 to an opened parent cap is
the next rung; see `EffectVmEmitCapReshape` §4D's RESIDUAL. Nothing routes to this descriptor at HEAD,
so neither defect was ever live, and this residual is likewise latent.

The ARGUS linchpin is additive + width-neutral (the delegation bit carriers are aux columns past the
GROUP-4 block, all `< EFFECT_VM_WIDTH`, which is 188 — the `186` this comment used to state was stale). -/

open Dregg2.Circuit.Emit.EffectVmEmitCapReshape
  (capDelegNonAmpGates capDeleg_nonAmp_in_circuit capDeleg_rejects_amplify gDelegSubmaskBit
   capDelegNonAmpGates_shape capDeleg_carriers_in_range)

/-- **`attenuateVmDescriptorGenuineNonAmp`** — the GENUINE cap-graph circuit WITH in-circuit
non-amplification: the §G genuine descriptor's frame-freeze + recompute + commitment, PLUS the shared
delegation non-amp submask gates (`granted ⊑ held` over the bound `rights`). The cap-root is GENUINELY
recomputed AND the granted rights are gated `⊑` held — both on the one `rights` felt. -/
def attenuateVmDescriptorGenuineNonAmp : EffectVmDescriptor :=
  { attenuateVmDescriptorGenuine with
    name        := attenuateVmDescriptorGenuine.name ++ "-nonamp"
    constraints := attenuateVmDescriptorGenuine.constraints ++ capDelegNonAmpGates }

/-- The genuine-non-amp descriptor KEEPS the §G genuine descriptor's hash-sites (the cap-root recompute
+ GROUP-4 commitment) — non-amp is pure GATES, it adds NO hash-site — and stays at the base width. -/
theorem attenuateGenuineNonAmp_keeps_recompute :
    attenuateVmDescriptorGenuineNonAmp.hashSites = attenuateVmDescriptorGenuine.hashSites
    ∧ attenuateVmDescriptorGenuineNonAmp.traceWidth = EFFECT_VM_WIDTH
    ∧ attenuateVmDescriptorGenuineNonAmp.constraints
        = attenuateVmDescriptorGenuine.constraints ++ capDelegNonAmpGates := by
  refine ⟨rfl, ?_, rfl⟩
  show attenuateVmDescriptorGenuine.traceWidth = EFFECT_VM_WIDTH
  rfl

/-- **`attenuateGenuineNonAmp_in_circuit` — the per-bit non-amp tooth on the cap-graph family.** Any
witness satisfying the genuine-non-amp descriptor's constraints FORCES, per bit, `granted ⊑ held` (the
granted bit ≤ the held bit) over `dcol.grantedBit i` / `dcol.heldBit i` (cols `128+i` / `120+i`).
Extracted from the shared `capDeleg_nonAmp_in_circuit` (the non-amp gates are a sub-list).

Since the granted bits reconstruct `prmCol cp.RIGHTS` = col 72 — the `rights` the recompute binds into
`cap_root` — this reaches the CONFERRED rights, not merely the bit carriers.

⚠ SCOPE (see §G.4's RESIDUAL): the held mask (col 75) is a free param here, so a verifying proof means
"the rights committed into `cap_root` are a submask of a mask the prover supplied". That refutes
rights-felt forgery; it is NOT yet non-amplification against an opened parent cap. The statement below
quantifies over the bit carriers only. -/
theorem attenuateGenuineNonAmp_in_circuit (env : VmRowEnv)
    (hcon : ∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hgc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) < 2013265921) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 0
    ∨ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 1 := by
  apply capDeleg_nonAmp_in_circuit env _ i hi hgc hhc
  intro c hc
  apply hcon
  show c ∈ (attenuateVmDescriptorGenuine.constraints ++ capDelegNonAmpGates)
  exact List.mem_append_right _ hc

/-- **`attenuateGenuineNonAmp_rejects_amplify` — the in-circuit anti-amplify tooth (witness FALSE).** A
genuine-non-amp row whose granted bit `i` is SET but held bit `i` is CLEAR (an over-grant: conferring a
right the delegator does not hold) does NOT satisfy the descriptor — the submask gate fails. So the
cap-graph family REJECTS over-grants in-circuit, on the SAME descriptor that recomputes the cap-root. -/
theorem attenuateGenuineNonAmp_rejects_amplify (env : VmRowEnv)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hg : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 1)
    (hh : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) := by
  intro hcon
  refine capDeleg_rejects_amplify env i hi hg hh ?_
  intro c hc
  apply hcon
  show c ∈ (attenuateVmDescriptorGenuine.constraints ++ capDelegNonAmpGates)
  exact List.mem_append_right _ hc

-- The genuine-non-amp descriptor: the genuine constraints (12+14+4 = 30) ++ the non-amp gates
-- (3·8+2 = 26), same 6 hash sites, same base width. Additive + width-neutral.
#guard attenuateVmDescriptorGenuineNonAmp.constraints.length == (12 + 14 + 4) + (3 * 8 + 2)
#guard attenuateVmDescriptorGenuineNonAmp.hashSites.length == 6
#guard attenuateVmDescriptorGenuineNonAmp.traceWidth == 188

#assert_axioms attenuateGenuineNonAmp_keeps_recompute
#assert_axioms attenuateGenuineNonAmp_in_circuit
#assert_axioms attenuateGenuineNonAmp_rejects_amplify

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard attenuateVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard attenuateVmDescriptor.hashSites.length == 4
#guard attenuateVmDescriptor.traceWidth == 188
-- The genuine descriptor: 12 frame gates (no opaque cap-move), 6 hash sites (2 recompute + 4 GROUP-4).
#guard attenuateVmDescriptorGenuine.constraints.length == 12 + 14 + 4
#guard attenuateVmDescriptorGenuine.hashSites.length == 6
#guard attenuateVmDescriptorGenuine.traceWidth == 188

#assert_axioms attenuateGenuineRowGates_holds_iff
#assert_axioms attenuateGenuine_sound
#assert_axioms attenuateGenuine_binds_edge
#assert_axioms attenuateGenuineGoodRow_recomputes
#assert_axioms attenuateGenuine_op_tamper_refuted

#assert_axioms attenuateRowGates_holds_iff
#assert_axioms attenuateVm_faithful
#assert_axioms attenuateVm_rejects_wrong_capRoot
#assert_axioms attenuateVm_rejects_wrong_output
#assert_axioms intent_to_capCellSpec
#assert_axioms attenuateDescriptor_full_sound
#assert_axioms attenuateDescriptor_commit_binds_state
#assert_axioms unify_attenuate
#assert_axioms unify_attenuate_via_full_sound
#assert_axioms capGoodRow_realizes_intent
#assert_axioms capBadRow_rejected

/-! ## §W — THE MAGNESIUM WIDENING: the cap-graph row's RUNNABLE descriptor binds the FULL 17-field
post-state (the shared cap-graph `RunnableFullStateSpec`, reused by every cap-graph effect).

`attenuateVmDescriptor` (and its re-exports `delegateVmDescriptor`, `dropRefVmDescriptor`,
`introduceVmDescriptor`, `revokeDelegationVmDescriptor`) is a `cap_root` COLUMN MOVE + frame freeze,
186-wide, whose 4-site GROUP-4 chain binds the 13 absorbed state-block columns (incl. the moved
`cap_root`) but NOT the `system_roots` sub-block — so a satisfying RUNNABLE proof pinned a PROJECTION
(13 fields), not the whole 17-field post-state. THIS section closes that with the WIDE descriptor +
the generic `EffectVmFullStateRunnable.runnable_full_sound`: the cap-graph row's RUNNABLE descriptor now
pins ALL 17 `RecordKernelState` fields (the per-cell block — `cell`/`caps`/`bal`-here + frame — AND the
8 side-table roots), with the whole-state anti-ghost tooth on every field.

The cap-graph kernel step (`attenuateSlotF` / `recDelegateCaps` / `removeEdgeCaps` / `recKDelegateAtten`)
edits ONLY `caps`; ALL 8 side-table roots are FROZEN. So the wide cap-graph clause is the per-cell
`CapCellSpec` (cap_root moved to the supplied digest, frame frozen) AND `postRoots = preRoots` — the
side-table sub-block frozen, EXACTLY the transfer reference's frozen-roots shape, but with `cap_root`
MOVING instead of frozen. (refreshDelegation, the ONE cap-graph effect that moves a side-table root —
the `DELEG` epoch — has its own wide instance in `EffectVmEmitRefreshDelegation`; this shared builder
covers the six caps-only cap-graph effects.) -/

section CapGraphWide

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites baseAbsorbedCols RunnableFullStateSpec runnable_full_sound
   runnable_full_commit_binds_or_collides wide_rejects_state_tamper_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

/-- **`attenuateVmDescriptorWide`** — the cap-graph row's descriptor WIDENED to bind the `system_roots`
sub-block: the SAME per-row `cap_root`-move + frame-freeze gates + transition continuity + boundary pins
as `attenuateVmDescriptor`, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`
(transfer's three inner sites — binding the moved `cap_root` — plus the `sysRootsDigestCol`-absorbing 4th
site). Strictly additive over `attenuateVmDescriptor`: the constraint list is byte-identical; only the
width grows by 2 and site 3's spare `.zero` slot becomes the side-table digest carrier. Every cap-graph
effect re-exports this (it IS the same runnable `cap_root`-move row). -/
def attenuateVmDescriptorWide : EffectVmDescriptor :=
  { attenuateVmDescriptor with
    name := attenuateVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide cap-graph descriptor's constraints ARE `attenuateVmDescriptor`'s (the width/site swap leaves
the per-row/transition/boundary gate list untouched), so every per-row faithfulness/soundness theorem
applies verbatim. -/
theorem attenuateWide_constraints_eq :
    attenuateVmDescriptorWide.constraints = attenuateVmDescriptor.constraints := rfl

/-- The wide cap-graph descriptor's hash-sites ARE the `system_roots`-absorbing `wideHashSites` (so
`usesWideSites := rfl` in the spec below). -/
theorem attenuateWide_hashSites_eq :
    attenuateVmDescriptorWide.hashSites = wideHashSites := rfl

/-- **`attenuateWide_rowGates_sub`** — the per-row cap-graph gates are a PREFIX sublist of the wide
descriptor's full constraint list (`attenuateRowGates ++ transitionAll ++ boundaryFirstPins`); so a row
satisfying the full descriptor satisfies the row gates. The flag-free restriction the gate-only soundness
(`attenuateDescriptor_full_sound`) consumes. -/
theorem attenuateWide_rowGates_sub (env : VmRowEnv)
    (hgates : ∀ c ∈ attenuateVmDescriptorWide.constraints, c.holdsVm env true false) :
    ∀ c ∈ attenuateRowGates, c.holdsVm env false false := by
  intro c hc
  -- the row gates are all `.gate _`; their `holdsVm` ignores the first/last flags.
  have hmem : c ∈ attenuateVmDescriptorWide.constraints := by
    show c ∈ attenuateVmDescriptor.constraints
    unfold attenuateVmDescriptor
    simp only [List.mem_append]; exact Or.inl (Or.inl hc)
  have hh := hgates c hmem
  unfold attenuateRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`CapFullClause`** — the FULL declarative cap-graph post-state over `(pre, post, postRoots)`: the
per-cell `CapCellSpec` (post `cap_root` IS the supplied post-cap-digest `capDigestNew`; balance limbs /
nonce / 8 fields / reserved FROZEN) AND the `system_roots` sub-block FROZEN (`postRoots = preRoots` — a
caps-only cap-graph effect touches no side-table). The parameter `capDigestNew` is the cap-table-move
digest the effect's connector supplies (`attenCapDigestNew` / `delegateCapDigestNew` / …); `preRoots` is
the frozen reference sub-block. Non-vacuous: `capWide_realizes` inhabits it. -/
def CapFullClause (capDigestNew : ℤ) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CapCellSpec pre post capDigestNew ∧ postRoots = preRoots

/-- **`capRunnableSpec` — THE SHARED CAP-GRAPH FULL-STATE RUNNABLE INSTANCE.** The cap-graph
`RunnableFullStateSpec`, parameterized by the post-cap-digest `capDigestNew` (the witnessed cap-table
move) and the frozen reference roots `preRoots`. `decodeAfter` is `CapRowEncodes` (the structured column
decode, pinning `cap_root`/frame) PLUS the frozen-roots witness; `decodeFull` projects the wide
descriptor's per-row gates (= `attenuateVmDescriptor`'s) to the gate-only `attenuateDescriptor_full_sound`,
then carries the frozen-roots fact. THIN — the only per-effect content is the (already-proved, hash-site-
free) `attenuateDescriptor_full_sound` + the frozen-roots decode. NON-VACUOUS: `fullClause` is the genuine
per-cell `cap_root` move + the frozen sub-block, NOT `True`. -/
def capRunnableSpec (capDigestNew : ℤ) (preRoots : SysRoots) :
    RunnableFullStateSpec CellState where
  descriptor    := attenuateVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsAttenRow
  decodeAfter   := fun env pre post postRoots =>
    CapRowEncodes env pre post capDigestNew ∧ postRoots = preRoots
  fullClause    := CapFullClause capDigestNew preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨attenuateDescriptor_full_sound env pre post capDigestNew henc
            (attenuateWide_rowGates_sub env hgates), hroots⟩

/-- **`cap_runnable_full_sound` — THE CAP-GRAPH MAGNESIUM CROWN.** A row satisfying the cap-graph WIDE
RUNNABLE descriptor (`satisfiedVm attenuateVmDescriptorWide`, first/last active), under the structured
decode, pins the FULL 17-field declarative cap-graph post-state: the per-cell `cap_root` MOVE to the
supplied digest + frame freeze (binding `cell`/`caps`/`bal`-here + frame) AND the frozen `system_roots`
sub-block (binding the 8 side-table roots). The generic `runnable_full_sound` instantiated at
`capRunnableSpec`. Every caps-only cap-graph effect (attenuate / delegate / delegateAtten / introduce /
revokeDelegation / dropRef) re-exports this with its own `capDigestNew` connector. -/
theorem cap_runnable_full_sound (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsAttenRow env)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash attenuateVmDescriptorWide env true false) :
    CapFullClause capDigestNew preRoots pre post postRoots :=
  runnable_full_sound (capRunnableSpec capDigestNew preRoots) hash env pre post postRoots
    hrow ⟨henc, hroots⟩ hsat

/-- **`cap_runnable_binds_full_state_or_collides` — the whole-17-field anti-ghost over the WIDE
commitment, UNCONDITIONALLY.** Two rows satisfying the cap-graph wide descriptor that publish the SAME
`NEW_COMMIT`, whose carriers ARE the `systemRootsDigest` of their post sub-blocks, EITHER agree on EVERY
absorbed state-block column (the moved `cap_root` included) AND every side-table root, OR exhibit a
genuine collision of the deployed sponge — on the state block (`WideColl`) or on the ordered root list
(`RootsColl`). So keeping `NEW_COMMIT` while tampering any of the 17 fields' bound content COSTS a named
sponge collision.

The old form concluded the bare conjunction from `Poseidon2SpongeCR hash`, which the deployed BabyBear
sponge REFUTES, so at deployed parameters it was vacuous. This disjunction is formally weaker and holds
of the deployed sponge. -/
theorem cap_runnable_binds_full_state_or_collides (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash attenuateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash attenuateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  runnable_full_commit_binds_or_collides (capRunnableSpec capDigestNew preRoots) hash
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`cap_runnable_rejects_cap_root_tamper_or_collides` — the cap-graph headline tooth (state-block).**
Two wide cap-graph rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose
absorbed state-block columns DIFFER (a forged balance / tampered field / forged `cap_root`) exhibit a
genuine collision of the deployed sponge: such a pair is UNSAT unless the prover holds a `WideColl` or a
`RootsColl`. The moved `cap_root` (absorbed column 11) is bound by the wide commitment.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge REFUTES,
so at deployed parameters it was vacuous. This form names what the tamper costs and holds of the deployed
sponge. -/
theorem cap_runnable_rejects_cap_root_tamper_or_collides (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash attenuateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash attenuateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : baseAbsorbedCols e₁ ≠ baseAbsorbedCols e₂) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_state_tamper_or_collides (capRunnableSpec capDigestNew preRoots) hash
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`cap_runnable_rejects_root_tamper_or_collides` — the cap-graph headline tooth (side-table).** Two
wide cap-graph rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table
sub-blocks DIFFER at some index (a dropped escrow, an omitted nullifier, a tampered DELEG/REFCOUNT root)
exhibit a genuine collision of the deployed sponge: such a pair is UNSAT unless the prover holds a
`WideColl` or a `RootsColl`. The 8 side-table roots are bound BY the runnable cap-graph commitment.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge REFUTES,
so at deployed parameters it was vacuous. This form names what the tamper costs and holds of the deployed
sponge. -/
theorem cap_runnable_rejects_root_tamper_or_collides (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash attenuateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash attenuateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (capRunnableSpec capDigestNew preRoots) hash
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### §W.NV — NON-VACUITY of the shared cap-graph clause (a real cap-move inhabits it; a forged one
does not). -/

/-- A frozen reference sub-block (the empty `system_roots`, since a caps-only cap-graph effect touches no
side-table). -/
def capPreRoots : SysRoots := emptySystemRoots

/-- A concrete pre cell-state for the non-vacuity witness: balance `100`, nonce `5`, `cap_root` `11`. -/
def capNVpre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 11, reserved := 0,
    commit := 0 }

/-- A concrete post cell-state: `capNVpre` with `cap_root` moved to the new digest `77` (the cap-graph
move), every other field frozen. -/
def capNVpost : CellState := { capNVpre with capRoot := 77 }

/-- **`capWide_realizes` — NON-VACUITY (witness TRUE).** The shared cap-graph `fullClause` is INHABITED by
a real cap-graph move: `capNVpost` is `capNVpre` with `cap_root` advanced `11 → 77` (= the supplied digest
`77`), frame frozen, and the roots frozen. So the framework's `fullClause` is NOT `True` — it is a
meaningful 17-field predicate a real cap-graph move satisfies, and it is exactly the `fullClause` field of
`capRunnableSpec`. -/
theorem capWide_realizes :
    (capRunnableSpec 77 capPreRoots).fullClause capNVpre capNVpost capPreRoots :=
  ⟨⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩, rfl⟩

/-- **`capWide_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`cap_root` is NOT the supplied digest (`capNVpre.capRoot` left at `11`, demanding `77`) FAILS
`CapFullClause` — so the shared cap-graph clause is not vacuously true (it rejects an UNMOVED cap_root),
pinning the framework's non-vacuity from BOTH sides. -/
theorem capWide_clause_not_trivial :
    ¬ CapFullClause 77 capPreRoots capNVpre
        { capNVpost with capRoot := 11 } capPreRoots := by
  rintro ⟨⟨hcap, _⟩, _⟩
  -- hcap : (11 : ℤ) = 77 — absurd
  exact absurd hcap (by decide)

/-- **`capWide_roots_clause_not_trivial` — the side-table leg is REFUTABLE too.** A post-state with the
cap-move RIGHT but a NON-frozen side-table (`postRoots ≠ preRoots`) FAILS `CapFullClause` — so the
frozen-roots conjunct bites (a `postRoots := True`-style stub would collapse it). Witnessed by a
populated `DELEG` root against the empty reference. -/
theorem capWide_roots_clause_not_trivial :
    ¬ CapFullClause 77 capPreRoots capNVpre capNVpost
        (fun i => if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.DELEG, by decide⟩ : Fin N_SYSTEM_ROOTS)
                  then 999 else emptySystemRoots i) := by
  rintro ⟨_, hroots⟩
  -- hroots would force the populated sub-block = emptySystemRoots; evaluate at DELEG: 999 = 0.
  have := congrFun hroots (⟨Dregg2.Exec.SystemRoots.systemRoot.DELEG, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [capPreRoots, emptySystemRoots] at this
  exact absurd this (by decide)

#assert_axioms attenuateWide_constraints_eq
#assert_axioms attenuateWide_hashSites_eq
#assert_axioms cap_runnable_full_sound
#assert_axioms cap_runnable_binds_full_state_or_collides
#assert_axioms cap_runnable_rejects_cap_root_tamper_or_collides
#assert_axioms cap_runnable_rejects_root_tamper_or_collides
#assert_axioms capWide_realizes
#assert_axioms capWide_clause_not_trivial
#assert_axioms capWide_roots_clause_not_trivial

#guard attenuateVmDescriptorWide.traceWidth == 190
#guard attenuateVmDescriptorWide.hashSites.length == 4
-- the wide constraint list is byte-identical to the base (13 gates + 14 transitions + 4 boundary):
#guard attenuateVmDescriptorWide.constraints.length == 13 + 14 + 4

end CapGraphWide

/-! ## §ROM — ⚑ THE ROM SUCCESSORS: the cap-graph wide commitment legs as REDUCTIONS on the
PROVED keyed floor.

⚑ STATUS (2026-07-24). The three `cap_runnable_…_or_collides` exports above carry the
DETERMINISTIC constraint-side extraction (`satisfiedVm` ⇒ shared commit + absorbed columns —
circuit content) plus collision pricing that, as a bare disjunction, was a SHIRK: at deployed
BabyBear parameters a sponge collision EXISTS by pigeonhole, so each disjunction holds through its
right branch with NO binding. The security statements are THIS section's reductions: the cap-graph
wide schedule is the keystone wide schedule (`attenuateVmDescriptorWide.hashSites = wideHashSites`,
rfl above; `attenuateHashSites_eq`), so the site's equivocations at the SAMPLED oracle are the wide
row ROM forgeries, priced by `EffectVmRowCommitReduction`'s union bound on
`KeyedRomFloor.keyedRom_hard` (the birthday bound, a THEOREM). The moved `cap_root` additionally
gets its own LOCALIZED slot tamper (block C, slot 3 — absorbed column 11), reduced into the full
wide forgery. NO refuted floor; the modelling step is `RomCarrierSites`' labelled idealisation.
The disjunctions stay as the deterministic extractor/constraint machinery. -/

section RomSuccessor

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction
  (wideRomFamily WideRomVal wideRomCommit wideRomBreakGame effectVmWideRomForgery
   wideRow_binds_rom effectVmWideRomStateTamper wide_state_tamper_rom
   effectVmWideRomRootTamper wide_root_tamper_rom)
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed)
open Dregg2.Crypto.RomCarrierSites (RomForgery RomForgeryEff)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Adversary gameAdv gameAdv_mem_unit)

/-- **⚑⚑ THE CAP-GRAPH FULL-STATE BINDING, DISCHARGED** — the ROM successor of
`cap_runnable_binds_full_state_or_collides`: every query-bounded forger that equivocates the whole
17-field nested wide commitment (the moved `cap_root` included) has NEGLIGIBLE advantage
(`wideRow_binds_rom`). -/
theorem cap_runnable_binds_full_state_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

/-- **⚑ THE CAP-GRAPH STATE-TAMPER TOOTH, DISCHARGED** — the ROM successor of
`cap_runnable_rejects_cap_root_tamper_or_collides` (whose tamper hypothesis is a disagreement
anywhere in the absorbed state blocks, the `cap_root` column included): negligible advantage,
`wide_state_tamper_rom`. -/
theorem cap_runnable_rejects_cap_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomStateTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomStateTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomStateTamper D tagDec).game A) :=
  wide_state_tamper_rom D tagDec Q hQ A hA

/-- **⚑ THE CAP-GRAPH SIDE-TABLE TOOTH, DISCHARGED** — the ROM successor of
`cap_runnable_rejects_root_tamper_or_collides` (`wide_root_tamper_rom`). -/
theorem cap_runnable_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

/-- **THE CAP-ROOT SLOT ROM TAMPER** — the cap-graph headline disagreement LOCALIZED to the moved
`cap_root` slot itself (block C, slot 3 — absorbed column 11): a forged openable c-list root under
a kept wide commitment. -/
def capRootWideRomTamper (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (wideRomFamily D tagDec) where
  Ans := fun _ => D.Tag × WideRomVal × WideRomVal
  wins := fun l H a =>
    a.2.1.1.2.2 3 ≠ a.2.2.1.2.2 3
      ∧ wideRomCommit D tagDec l H a.1 a.2.1 = wideRomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((wideRomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- **⚑⚑ THE MOVED `cap_root` IS BOUND, AS A REDUCTION ON THE PROVED FLOOR** — the sharpest form
of the cap-graph headline: a query-bounded adversary that keeps the published wide `NEW_COMMIT`
while moving ONLY the `cap_root` slot has NEGLIGIBLE advantage. A slot disagreement is payload
distinctness, so the localized tamperer IS a full wide forger and `wideRow_binds_rom` kills it. -/
theorem cap_runnable_rejects_cap_root_slot_tamper_rom (D : SpongeKeyed)
    (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (capRootWideRomTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (capRootWideRomTamper D tagDec) Q A) :
    Negl (gameAdv (capRootWideRomTamper D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  have hgen : Negl (gameAdv (wideRomBreakGame D tagDec)
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec))) :=
    wideRow_binds_rom D tagDec Q hQ
      (⟨A.run⟩ : Adversary (wideRomBreakGame D tagDec)) ⟨M, hM, hrun⟩
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (capRootWideRomTamper D tagDec).game A l).1)
    (fun l => ?_) hgen
  refine @winProb_le_of_imp _ ((capRootWideRomTamper D tagDec).game.instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr ?_
  obtain ⟨hne, heq⟩ := hH
  exact ⟨fun hc => hne (congrArg (fun v : WideRomVal => v.1.2.2 3) hc), heq⟩

end RomSuccessor

#assert_axioms cap_runnable_binds_full_state_rom
#assert_axioms cap_runnable_rejects_cap_root_tamper_rom
#assert_axioms cap_runnable_rejects_root_tamper_rom
#assert_axioms cap_runnable_rejects_cap_root_slot_tamper_rom

end Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
