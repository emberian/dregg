/-
# Dregg2.Circuit.Emit.NoteSpendingLeafRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the note-spend recursion leaf (`NoteSpendingLeafEmit.noteSpendLeafDesc`).

## What Rung-0 already proved (in `NoteSpendingLeafEmit.lean`)
`noteSpendLeafDesc` is byte-pinned to the deployed `note_spend_to_descriptor2()` and each of two
gates has a LOCAL soundness lemma (`binary_gate_zero_iff` : C1 boolean; `cont_body_zero_iff` : C7
continuity). What was MISSING: the whole-descriptor bridge — that a trace SATISFYING the descriptor
(`Satisfied2`) corresponds to the genuine note-spend semantic relation.

## What THIS file proves (Rung-1)
The census dossier for `note_spending` is `spec_status = NO_LEAN`: no proven semantic model existed.
So this file FIRST authors the missing functional spec — the genuine relation the note-spend leaf is
meant to compute over its SPEND row — then proves the emitted descriptor refines it (SAT ⟹ SEM).

### The semantic relation (authored here)
`NoteSpendLeafSpec permOut env` is the conjunction the descriptor forces on the spend row
(`is_merkle = 0`, a non-last row so the `when_transition` gates fire), against the NAMED Poseidon2
wide-permutation carrier `permOut`:
  * the FULL-WIDTH commitment binding — `COMMITMENT_FULL` is the 7-fold `permOut` chain over the
    28-limb note preimage (C2a..C2g), and `COMMITMENT = COMMITMENT_FULL` (C2-final);
  * the value / value_hi / asset PI-limb links (C2-link);
  * the two-step nullifier derivation binding the 8-limb spending key (C3/C4);
  * position validity over BabyBear (C5, as a `[ZMOD p]` root — the field reduction is honest);
  * the two-step mint-hash recompute (m1 / mint_hash);
  * the chain-continuity relation (C7);
  * the six source boundary PI pins + the two mint PI pins (row 0).

### The bridge (whole descriptor, not one gate)
`noteSpend_satisfied2_spec` (SAT ⟹ SEM, the load-bearing soundness direction): a trace that
SATISFIES the whole `noteSpendLeafDesc` binds the whole spend-row relation. It COMPOSES all 11 firing
Poseidon2 sites (through the fact-site lever `factSite_block` + the wide chip carrier), all four base
equalities, the position poly, the continuity gate, and all eight PI pins. This is the whole
descriptor's spend semantics, not a single-gate restatement.

### The fact-site lever
`factSite_block` : on the spend row (`is_merkle = 0`), a `hash_fact` chip lookup + the wide chip
soundness (`ChipTableSoundN permOut`) FORCE the site's output block to be `permOut` of the genuine
seeded inputs — the deployed selector-mux collapses to the raw absorb when the selector fires.

### Non-vacuity (the anti-scar proof)
`witnessTrace_satisfied2` builds a CONCRETE two-row trace + a concrete wide-chip table +
`witnessPerm` for which `Satisfied2` holds AND `ChipTableSoundN witnessPerm` holds — the hypothesis
chain is genuinely inhabited; `witness_spec` fires the bridge end-to-end on it. `badMerkle_rejects`
and `badCommitment_rejects` exhibit CONCRETE traces that FAIL `Satisfied2` because a constraint
BITES: a non-boolean `is_merkle` trips C1, and a `COMMITMENT ≠ COMMITMENT_FULL` trips C2-final.

### Honest residuals (NOT in this row-0 spec)
C6 (Merkle membership) is OFF on the spend row (`is_merkle = 0`); its genuine meaning — that the
committed leaf is IN the tree rooted at `merkle_root` (pi1) — lives on the `is_merkle = 1` path rows
and needs the multi-row `recomposeUp` Merkle fold (as `HeapOpenEmit` builds), out of scope for one
additive file. The last-row `merkle_root` pin is likewise a different-row pin. These are named, not
laundered.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The SOLE cryptographic carrier is the
NAMED wide Poseidon2 chip soundness `ChipTableSoundN permOut` (the deployed chip AIR's own
faithfulness — the same carrier `HeapOpenEmit`/`AccumulatorOpenEmit` ride); `permOut` is a parameter
exactly as `hash` is for the legacy lever. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.NoteSpendingLeafEmit

namespace Dregg2.Circuit.Emit.NoteSpendingLeafRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowConstraint WindowExpr Satisfied2 VmTrace
   TraceFamily envAt zeroAsg ChipTableSoundN chipRowN chip_lookup_sound_N chipLookupTupleN CHIP_RATE
   padTo padToE padTo_length padTo_of_fits padTo_inj map_eval_padToE memOpsOf mapOpsOf memLog mapLog opRow
   memCheck_nil)
open Dregg2.Circuit.Emit.NoteSpendingLeafEmit
  (noteSpendLeafDesc noteSpendConstraints unlessSite whenSite factTuple IS_MERKLE NS_FACT_MARK K0
   subE unlessFire unlessHold whenFire whenHold binaryGate invEqGate posGate contBodyW
   binary_gate_zero_iff cont_body_zero_iff)

set_option autoImplicit false

/-! ## §0 — the deployed range-check canonicality envelope (field-faithful ℤ recovery).

`VmConstraint.holdsVm` now binds every base gate `≡ 0 [ZMOD p]` and every PI pin `≡ pub [ZMOD p]`
(the DEPLOYED BabyBear field constraint), not `= 0`/`= pub` over ℤ. The base equalities the spec
carries (`COMMITMENT = COMMITMENT_FULL`, the value / asset limb links, the chain-continuity, and the
eight PI pins) are read back off the congruence through the DEPLOYED range-check invariant that every
felt is canonical (`0 ≤ · < p`). The Poseidon2 chip sites (the `permOut` chain / nullifier / mint
digests) bind over ℤ unchanged (a lookup, not a field gate), so they are NOT part of the envelope. -/

/-- A DEPLOYED range-check canonical field cell: the residue itself (`0 ≤ x < p`). -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  rw [Int.modEq_iff_dvd] at h; obtain ⟨k, hk⟩ := h
  obtain ⟨_, _⟩ := ha; obtain ⟨_, _⟩ := hb; omega

/-- **`NoteCanon env` — the deployed range-check envelope for the spend row.** Every cell a base
equality / pin reads back as a genuine ℤ equality is a canonical felt: the commitment cells and their
preimage limbs, the chain-continuity input, and the eight public inputs. Inhabited by the concrete
witness (`witness_canon`). -/
structure NoteCanon (env : VmRowEnv) : Prop where
  c1 : Canon (env.loc 1)
  c2 : Canon (env.loc 2)
  c5 : Canon (env.loc 5)
  c14 : Canon (env.loc 14)
  c18 : Canon (env.loc 18)
  c19 : Canon (env.loc 19)
  c28 : Canon (env.loc 28)
  c29 : Canon (env.loc 29)
  c30 : Canon (env.loc 30)
  c54 : Canon (env.loc 54)
  c62 : Canon (env.loc 62)
  c64 : Canon (env.loc 64)
  cnxt0 : Canon (env.nxt 0)
  p0 : Canon (env.pub 0)
  p1 : Canon (env.pub 1)
  p2 : Canon (env.pub 2)
  p3 : Canon (env.pub 3)
  p4 : Canon (env.pub 4)
  p5 : Canon (env.pub 5)
  p6 : Canon (env.pub 6)

/-! ## §1 — the firing-row seed of a `hash_fact` site (the Lean twin of the deployed absorb). -/

/-- The 5 muxed value lanes of a fact site, EVALUATED on a firing row: the input columns' values,
padded to 5 with `0` (the deployed `gated_fact_site` fills absent lanes with a literal zero). -/
def firing5 (env : VmRowEnv) (inputCols : List Nat) : List ℤ :=
  (List.range 5).map (fun i => match inputCols[i]? with | some c => env.loc c | none => (0 : ℤ))

/-- The genuine arity-7 `hash_fact` absorb seed of a site on a FIRING row: the 5 muxed value lanes
followed by the two domain constants `[0xFACF, 1]`. -/
def firingIns (env : VmRowEnv) (inputCols : List Nat) : List ℤ :=
  firing5 env inputCols ++ [NS_FACT_MARK, 1]

/-- The 7 exposed permutation lane values a site binds (columns `laneBase .. laneBase+6`). -/
def factLaneVals (env : VmRowEnv) (laneBase : Nat) : List ℤ :=
  (List.range 7).map (fun j => env.loc (laneBase + j))

theorem firingIns_length (env : VmRowEnv) (inputCols : List Nat) :
    (firingIns env inputCols).length = 7 := by
  simp [firingIns, firing5]

theorem firingIns_length_le (env : VmRowEnv) (inputCols : List Nat) :
    (firingIns env inputCols).length ≤ CHIP_RATE := by
  rw [firingIns_length]; decide

/-! ### the two firing-lane evaluation lemmas (the mux collapses on a firing row). -/

/-- On a firing row (`fire.eval = 1`) the muxed value lanes `fun i => s·col` evaluate to the raw
column values — the genuine absorb inputs. -/
theorem firingLaneExprs_eval (env : VmRowEnv) (fire : EmittedExpr) (inputCols : List Nat)
    (hf : fire.eval env.loc = 1) :
    ((List.range 5).map
        (fun i => match inputCols[i]? with
          | some c => EmittedExpr.mul fire (EmittedExpr.var c) | none => EmittedExpr.const 0)).map
        (·.eval env.loc)
      = firing5 env inputCols := by
  unfold firing5
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rcases h : inputCols[i]? with _ | c
  · simp only [h, EmittedExpr.eval]
  · simp only [h, EmittedExpr.eval, hf, one_mul]

/-- The 7 lane columns evaluate to their `env.loc` values. -/
theorem factLaneVals_eval (env : VmRowEnv) (laneBase : Nat) :
    ((List.range 7).map (fun j => EmittedExpr.var (laneBase + j))).map (·.eval env.loc)
      = factLaneVals env laneBase := by
  rw [List.map_map]; rfl

/-! ## §2 — the fact-site tuple, EVALUATED on a firing row, has the wide chip-row shape. -/

/-- **`factTuple_eval_form`** — on a firing row (`fire.eval = 1`, `hold.eval = 0`) the evaluated
`factTuple` IS the wide chip-lookup shape `(arity=7) :: padTo 16 seed ++ (digest :: lanes)`: the
value lanes are the raw seed, the digest lane is the output column, and the lanes are the exposed
permutation columns. -/
theorem factTuple_eval_form (env : VmRowEnv) (fire hold : EmittedExpr)
    (outputCol : Nat) (inputCols : List Nat) (laneBase : Nat)
    (hf : fire.eval env.loc = 1) (hh : hold.eval env.loc = 0) :
    (factTuple fire hold outputCol inputCols laneBase).map (·.eval env.loc)
      = ((7 : ℤ) :: padTo CHIP_RATE (firingIns env inputCols))
          ++ (env.loc outputCol :: factLaneVals env laneBase) := by
  -- ⚠ `padTo` is `take`-shaped now (total-correct, no obligation); `padTo_of_fits` puts it back
  -- into the plain-append form this congruence chain walks, using the bound this site already has.
  rw [padTo_of_fits (firingIns_length_le env inputCols)]
  unfold factTuple firingIns firing5 factLaneVals
  simp only [CHIP_RATE, NS_FACT_MARK, List.map_cons, List.map_append, List.map_nil, List.map_map,
    Function.comp_def, EmittedExpr.eval, hf, hh, one_mul, zero_mul, add_zero,
    List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.replicate]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  rcases h : inputCols[i]? with _ | c
  · simp only [h, EmittedExpr.eval]
  · simp only [h, EmittedExpr.eval, hf, one_mul]

/-! ## §3 — the fact-site lever: SAT + wide chip soundness ⟹ the digest is `permOut` of the seed. -/

/-- **`factSite_block`** — the WHOLE-BLOCK fact-site lever. On a firing row, a `hash_fact` chip
lookup that HOLDS against a wide-sound chip table forces the site's `(digest :: lanes)` output block
to equal `permOut` of the genuine absorb seed. Direct injection against the wide chip witness (the
arity tag + equal-length padding pin the decomposition, exactly as `chip_lookup_sound_N`). -/
theorem factSite_block (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2))
    (outputCol : Nat) (inputCols : List Nat) (laneBase : Nat)
    (fire hold : EmittedExpr) (hf : fire.eval env.loc = 1) (hh : hold.eval env.loc = 0)
    (hmem : (factTuple fire hold outputCol inputCols laneBase).map (·.eval env.loc)
              ∈ tf .poseidon2) :
    env.loc outputCol :: factLaneVals env laneBase = permOut (firingIns env inputCols) := by
  rw [factTuple_eval_form env fire hold outputCol inputCols laneBase hf hh] at hmem
  obtain ⟨ins, hlen, hrow⟩ := hChip _ hmem
  -- `hrow : ((7) :: padTo 16 firingIns) ++ (out :: lanes) = ((ins.len) :: padTo 16 ins) ++ permOut ins`
  rw [chipRowN, List.cons_append, List.cons_append] at hrow
  injection hrow with hhead htail
  have hlen7 : ins.length = 7 := by exact_mod_cast hhead.symm
  have hpadL : (padTo CHIP_RATE (firingIns env inputCols)).length = CHIP_RATE :=
    padTo_length (firingIns_length_le env inputCols)
  have hpadR : (padTo CHIP_RATE ins).length = CHIP_RATE := padTo_length (by rw [hlen7]; decide)
  have hsplit := List.append_inj htail (by rw [hpadL, hpadR])
  have hins : firingIns env inputCols = ins :=
    padTo_inj (firingIns_length_le env inputCols) (by rw [hlen7]; decide)
      (by rw [firingIns_length, hlen7]) hsplit.1
  rw [hins]; exact hsplit.2

/-! ## §4 — extraction plumbing from `Satisfied2` on the spend row (row 0, a non-last row). -/

/-- Membership of a specific constraint in the (flat) constraint list. -/
local macro "in_constraints" : tactic =>
  `(tactic| (show _ ∈ noteSpendConstraints;
             unfold noteSpendConstraints;
             simp only [List.mem_cons, List.mem_singleton];
             tauto))

/-- The fire / hold selector evaluations on the spend row (`is_merkle = 0`). -/
theorem unless_fire_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 0) :
    (unlessFire IS_MERKLE).eval env.loc = 1 := by
  simp [unlessFire, subE, EmittedExpr.eval, hm]

theorem unless_hold_eval (env : VmRowEnv) (hm : env.loc IS_MERKLE = 0) :
    (unlessHold IS_MERKLE).eval env.loc = 0 := by
  simp [unlessHold, EmittedExpr.eval, hm]

/-- A firing (`unlessSite`) hash-site's digest on the spend row is `permOut` of the genuine seed. -/
theorem unlessSite_digest (permOut : List ℤ → List ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hChip : ChipTableSoundN permOut (tf .poseidon2)) (hm : env.loc IS_MERKLE = 0)
    (outputCol : Nat) (inputCols : List Nat) (laneBase : Nat)
    (hmem : (factTuple (unlessFire IS_MERKLE) (unlessHold IS_MERKLE) outputCol inputCols laneBase).map
              (·.eval env.loc) ∈ tf .poseidon2) :
    env.loc outputCol = (permOut (firingIns env inputCols)).headD 0 := by
  have hblock := factSite_block permOut tf env hChip outputCol inputCols laneBase _ _
    (unless_fire_eval env hm) (unless_hold_eval env hm) hmem
  rw [← hblock]; rfl

/-- The base gate (`.gate body`) at a non-last row binds its body `≡ 0 [ZMOD p]` (the DEPLOYED field
constraint — `VmConstraint.holdsVm` binds a congruence, not `= 0`). -/
theorem gate_of_holdsAt (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (body : EmittedExpr)
    (h : (VmConstraint2.base (VmConstraint.gate body)).holdsAt hash tf env isFirst false) :
    body.eval env.loc ≡ 0 [ZMOD 2013265921] := h

/-- An inverted-gated equality on the spend row (`is_merkle = 0`), field-faithfully: the gate binds
`a − b ≡ 0 [ZMOD p]`, and both cells canonical (the deployed range check) recover the genuine ℤ
equality `a = b`. -/
theorem invEqGate_spend (env : VmRowEnv) (hm : env.loc IS_MERKLE = 0) (a b : Nat)
    (ha : Canon (env.loc a)) (hb : Canon (env.loc b))
    (h : (invEqGate IS_MERKLE a b).eval env.loc ≡ 0 [ZMOD 2013265921]) : env.loc a = env.loc b := by
  have hz : (invEqGate IS_MERKLE a b).eval env.loc = env.loc a - env.loc b := by
    simp only [invEqGate, subE, EmittedExpr.eval, hm]; ring
  rw [hz, Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h; obtain ⟨_, _⟩ := ha; obtain ⟨_, _⟩ := hb; omega

/-! ## §5 — the authored functional spec (NO_LEAN): the note-spend leaf's spend-row relation. -/

/-- **`NoteSpendLeafSpec permOut env`** — the genuine relation the note-spend recursion leaf computes
on its SPEND row (`is_merkle = 0`), welded to the NAMED wide Poseidon2 carrier `permOut`. Every
conjunct is a distinct constraint family of the deployed descriptor; together they ARE the whole
spend semantics (all but C6/Merkle-membership, which is off on this row — see residuals). -/
structure NoteSpendLeafSpec (permOut : List ℤ → List ℤ) (env : VmRowEnv) : Prop where
  /-- C1 : the row-type selector is boolean (here `0`, the spend row). -/
  isMerkleZero : env.loc IS_MERKLE = 0
  /-- C2a..C2f + C2g : `COMMITMENT_FULL` (col 54) is the 7-fold `permOut` chain over the 28 note limbs. -/
  chain0 : env.loc 48 = (permOut (firingIns env [20, 21, 22, 23, 24])).headD 0
  chain1 : env.loc 49 = (permOut (firingIns env [48, 25, 26, 27, 28])).headD 0
  chain2 : env.loc 50 = (permOut (firingIns env [49, 29, 30, 31, 32])).headD 0
  chain3 : env.loc 51 = (permOut (firingIns env [50, 33, 34, 35, 36])).headD 0
  chain4 : env.loc 52 = (permOut (firingIns env [51, 37, 38, 39, 40])).headD 0
  chain5 : env.loc 53 = (permOut (firingIns env [52, 41, 42, 43, 44])).headD 0
  commitmentFull : env.loc 54 = (permOut (firingIns env [53, 45, 46, 47])).headD 0
  /-- C2-final : `COMMITMENT` (col 5) equals the full-width binding `COMMITMENT_FULL`. -/
  commitmentBinds : env.loc 5 = env.loc 54
  /-- C2-link : the PI-bound value / value_hi / asset columns equal their commitment-preimage limbs. -/
  valueLink : env.loc 1 = env.loc 28
  valueHiLink : env.loc 19 = env.loc 29
  assetLink : env.loc 2 = env.loc 30
  /-- C3 / C4 : the nullifier is the two-step `permOut` derivation binding the 8-limb spending key. -/
  nullIntermediate : env.loc 17 = (permOut (firingIns env [5, 6, 7, 8, 9])).headD 0
  nullifier : env.loc 14 = (permOut (firingIns env [17, 10, 11, 12, 13])).headD 0
  /-- C5 : position validity over BabyBear — `pos·(pos−1)·(pos−2)·(pos−3) ≡ 0 (mod p)`. -/
  posValid : env.loc 4 * (env.loc 4 - 1) * (env.loc 4 - 2) * (env.loc 4 - 3)
               ≡ 0 [ZMOD 2013265921]
  /-- C7 : chain continuity — the next level's path input equals this row's `COMMITMENT`. -/
  continuity : env.nxt 0 = env.loc 5
  /-- mint recompute : `m1` then `mint_hash` bind the destination-federation mint identity. -/
  mintM1 : env.loc 63 = (permOut (firingIns env [14, 62, 18, 2])).headD 0
  mintHash : env.loc 64 = (permOut (firingIns env [63, 1, 19])).headD 0
  /-- the six source boundary PI pins + the two mint PI pins (row 0). -/
  piNullifier : env.loc 14 = env.pub 0
  piValue : env.loc 1 = env.pub 2
  piAsset : env.loc 2 = env.pub 3
  piDestFed : env.loc 18 = env.pub 4
  piValueHi : env.loc 19 = env.pub 5
  piMintRoot : env.loc 62 = env.pub 1
  piMintHash : env.loc 64 = env.pub 6

/-- C5's position polynomial vanishing (over ℤ) yields the genuine BabyBear position-root relation
`pos·(pos−1)·(pos−2)·(pos−3) ≡ 0 (mod p)` — the `p−6` coefficient is `−6` in the field. -/
theorem posGate_modeq (env : VmRowEnv) (h : posGate.eval env.loc ≡ 0 [ZMOD 2013265921]) :
    env.loc 4 * (env.loc 4 - 1) * (env.loc 4 - 2) * (env.loc 4 - 3) ≡ 0 [ZMOD 2013265921] := by
  -- the deployed field gate binds `posGate.eval ≡ 0 [ZMOD p]`; the field gate poly differs from the
  -- genuine position quartic by `p·(pos³+pos)`, so the congruence carries straight over.
  have hb : posGate.eval env.loc
      = env.loc 4 * (env.loc 4 - 1) * (env.loc 4 - 2) * (env.loc 4 - 3)
        + 2013265921 * (env.loc 4 ^ 3 + env.loc 4) := by
    simp only [posGate, EmittedExpr.eval]; ring
  rw [hb, Int.modEq_zero_iff_dvd] at h
  rw [Int.modEq_zero_iff_dvd]
  obtain ⟨k, hk⟩ := h
  exact ⟨k - (env.loc 4 ^ 3 + env.loc 4), by linear_combination hk⟩

/-! ## §6 — THE BRIDGE (SAT ⟹ SEM): a satisfying trace binds the whole spend-row relation. -/

/-- **`noteSpend_satisfied2_spec` — THE whole-descriptor soundness bridge.** A trace that satisfies
the whole `noteSpendLeafDesc` (`Satisfied2`), against the NAMED wide Poseidon2 chip carrier, binds
the genuine note-spend spec on its spend row (row 0, `is_merkle = 0`, a non-last row). Composes all
11 firing Poseidon2 sites, the four base equalities, the position poly, the continuity gate, and the
eight PI pins — the whole descriptor's spend semantics. -/
theorem noteSpend_satisfied2_spec
    (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t)
    (hChip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 1 < t.rows.length) (hspend : (envAt t 0).loc IS_MERKLE = 0)
    (hcanon : NoteCanon (envAt t 0)) :
    NoteSpendLeafSpec permOut (envAt t 0) := by
  set env := envAt t 0 with henv
  have hfalse : (0 + 1 == t.rows.length) = false := by
    rw [beq_eq_false_iff_ne]; omega
  -- every declared constraint holds on the spend row with (isFirst, isLast) = (true, false).
  have H : ∀ c ∈ noteSpendConstraints,
      c.holdsAt hash t.tf env true false := by
    intro c hc
    have := hsat.rowConstraints 0 (by omega) c hc
    rwa [hfalse] at this
  refine
    { isMerkleZero := hspend
    , chain0 := unlessSite_digest permOut t.tf env hChip hspend 48 [20, 21, 22, 23, 24] 65
        (H (unlessSite 48 [20, 21, 22, 23, 24] 65) (by in_constraints))
    , chain1 := unlessSite_digest permOut t.tf env hChip hspend 49 [48, 25, 26, 27, 28] 72
        (H (unlessSite 49 [48, 25, 26, 27, 28] 72) (by in_constraints))
    , chain2 := unlessSite_digest permOut t.tf env hChip hspend 50 [49, 29, 30, 31, 32] 79
        (H (unlessSite 50 [49, 29, 30, 31, 32] 79) (by in_constraints))
    , chain3 := unlessSite_digest permOut t.tf env hChip hspend 51 [50, 33, 34, 35, 36] 86
        (H (unlessSite 51 [50, 33, 34, 35, 36] 86) (by in_constraints))
    , chain4 := unlessSite_digest permOut t.tf env hChip hspend 52 [51, 37, 38, 39, 40] 93
        (H (unlessSite 52 [51, 37, 38, 39, 40] 93) (by in_constraints))
    , chain5 := unlessSite_digest permOut t.tf env hChip hspend 53 [52, 41, 42, 43, 44] 100
        (H (unlessSite 53 [52, 41, 42, 43, 44] 100) (by in_constraints))
    , commitmentFull := unlessSite_digest permOut t.tf env hChip hspend 54 [53, 45, 46, 47] 107
        (H (unlessSite 54 [53, 45, 46, 47] 107) (by in_constraints))
    , commitmentBinds := invEqGate_spend env hspend 5 54 hcanon.c5 hcanon.c54
        (gate_of_holdsAt hash t.tf env true _
          (H (VmConstraint2.base (VmConstraint.gate (invEqGate IS_MERKLE 5 54))) (by in_constraints)))
    , valueLink := invEqGate_spend env hspend 1 28 hcanon.c1 hcanon.c28
        (gate_of_holdsAt hash t.tf env true _
          (H (VmConstraint2.base (VmConstraint.gate (invEqGate IS_MERKLE 1 28))) (by in_constraints)))
    , valueHiLink := invEqGate_spend env hspend 19 29 hcanon.c19 hcanon.c29
        (gate_of_holdsAt hash t.tf env true _
          (H (VmConstraint2.base (VmConstraint.gate (invEqGate IS_MERKLE 19 29))) (by in_constraints)))
    , assetLink := invEqGate_spend env hspend 2 30 hcanon.c2 hcanon.c30
        (gate_of_holdsAt hash t.tf env true _
          (H (VmConstraint2.base (VmConstraint.gate (invEqGate IS_MERKLE 2 30))) (by in_constraints)))
    , nullIntermediate := unlessSite_digest permOut t.tf env hChip hspend 17 [5, 6, 7, 8, 9] 114
        (H (unlessSite 17 [5, 6, 7, 8, 9] 114) (by in_constraints))
    , nullifier := unlessSite_digest permOut t.tf env hChip hspend 14 [17, 10, 11, 12, 13] 121
        (H (unlessSite 14 [17, 10, 11, 12, 13] 121) (by in_constraints))
    , posValid := posGate_modeq env
        (gate_of_holdsAt hash t.tf env true _
          (H (VmConstraint2.base (VmConstraint.gate posGate)) (by in_constraints)))
    , continuity := ?cont
    , mintM1 := unlessSite_digest permOut t.tf env hChip hspend 63 [14, 62, 18, 2] 135
        (H (unlessSite 63 [14, 62, 18, 2] 135) (by in_constraints))
    , mintHash := unlessSite_digest permOut t.tf env hChip hspend 64 [63, 1, 19] 142
        (H (unlessSite 64 [63, 1, 19] 142) (by in_constraints))
    , piNullifier := eq_of_modEq_canon hcanon.c14 hcanon.p0
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 14 0)) (by in_constraints)) rfl)
    , piValue := eq_of_modEq_canon hcanon.c1 hcanon.p2
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 1 2)) (by in_constraints)) rfl)
    , piAsset := eq_of_modEq_canon hcanon.c2 hcanon.p3
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 2 3)) (by in_constraints)) rfl)
    , piDestFed := eq_of_modEq_canon hcanon.c18 hcanon.p4
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 18 4)) (by in_constraints)) rfl)
    , piValueHi := eq_of_modEq_canon hcanon.c19 hcanon.p5
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 19 5)) (by in_constraints)) rfl)
    , piMintRoot := eq_of_modEq_canon hcanon.c62 hcanon.p1
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 62 1)) (by in_constraints)) rfl)
    , piMintHash := eq_of_modEq_canon hcanon.c64 hcanon.p6
        ((H (VmConstraint2.base (VmConstraint.piBinding VmRow.first 64 6)) (by in_constraints)) rfl) }
  case cont =>
    -- the continuity window gate binds `nxt 0 − loc 5 ≡ 0 [ZMOD p]`; both cells canonical ⟹ genuine.
    have hw := H (VmConstraint2.windowGate ⟨contBodyW, true⟩) (by in_constraints)
    have hg : contBodyW.eval env ≡ 0 [ZMOD 2013265921] := hw rfl
    have hb : contBodyW.eval env = env.nxt 0 - env.loc 5 := by
      simp only [contBodyW, GateExpr.gThread_window, WindowExpr.eval]; ring
    rw [hb, Int.modEq_zero_iff_dvd] at hg
    obtain ⟨k, hk⟩ := hg
    obtain ⟨_, _⟩ := hcanon.cnxt0; obtain ⟨_, _⟩ := hcanon.c5; omega

/-! ## §7 — non-vacuity: a CONCRETE satisfying witness (bridge fires) + two failing ones (gate bites).

The witness is the "zero-fact" spend: `is_merkle = 0`, every note/key limb `0`, and every Poseidon2
DIGEST column pinned to the zero-fact digest `K₀`. The wide chip table carries exactly the three
distinct absorb rows the 12 sites produce, and `witnessPerm` (the constant `K₀`-headed block) makes
each a genuine `chipRowN`, so `ChipTableSoundN` holds. This is a REAL satisfying trace, not a scar:
`witness_spec` fires the whole bridge end-to-end on it, and the failing traces show teeth that BITE. -/

/-- The K₀-pinned digest columns (chain / nullifier / commitment / mint roots), everything else 0. -/
def witnessAsg : Assignment := fun c =>
  if c = 0 ∨ c = 5 ∨ c = 14 ∨ c = 17 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52 ∨ c = 53
     ∨ c = 54 ∨ c = 62 ∨ c = 63 ∨ c = 64 then K0 else 0

/-- Published inputs: nullifier (pi0), merkle_root (pi1), mint_hash (pi6) are `K₀`; the rest 0. -/
def witnessPub : Assignment := fun k => if k = 0 ∨ k = 1 ∨ k = 6 then K0 else 0

/-- The three distinct absorb rows the sites produce (`[arity, seed, 0×9, K₀, lanes]`). -/
def witnessTA : List ℤ := [7, 0, 0, 0, 0, 0, NS_FACT_MARK, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, K0, 0, 0, 0, 0, 0, 0, 0]
def witnessTB : List ℤ := [7, K0, 0, 0, 0, 0, NS_FACT_MARK, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, K0, 0, 0, 0, 0, 0, 0, 0]
def witnessTM : List ℤ := [7, K0, K0, 0, 0, 0, NS_FACT_MARK, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, K0, 0, 0, 0, 0, 0, 0, 0]

/-- The witness permutation: the constant `K₀`-headed 8-lane block (all three seeds squeeze to it). -/
def witnessPerm : List ℤ → List ℤ := fun _ => [K0, 0, 0, 0, 0, 0, 0, 0]

/-- The witness trace family: the three chip rows on `poseidon2`, empty elsewhere. -/
def witnessTf : TraceFamily := fun tid =>
  match tid with | .poseidon2 => [witnessTA, witnessTB, witnessTM] | _ => []

/-- The concrete two-row satisfying trace (both rows carry `witnessAsg`). -/
def witnessTrace : VmTrace := { rows := [witnessAsg, witnessAsg], pub := witnessPub, tf := witnessTf }

/-- **The wide chip table is genuinely sound** for `witnessPerm`: each of its three rows IS a
`chipRowN` of a length-7 absorb seed. -/
theorem witness_chipSound : ChipTableSoundN witnessPerm (witnessTf .poseidon2) := by
  intro r hr
  change r ∈ [witnessTA, witnessTB, witnessTM] at hr
  fin_cases hr
  · exact ⟨[0, 0, 0, 0, 0, NS_FACT_MARK, 1], by decide, by decide⟩
  · exact ⟨[K0, 0, 0, 0, 0, NS_FACT_MARK, 1], by decide, by decide⟩
  · exact ⟨[K0, K0, 0, 0, 0, NS_FACT_MARK, 1], by decide, by decide⟩

/-- The note-spend leaf declares no memory ops. -/
theorem witness_memOps : memOpsOf noteSpendLeafDesc = [] := rfl
/-- The note-spend leaf declares no map ops. -/
theorem witness_mapOps : mapOpsOf noteSpendLeafDesc = [] := rfl
/-- Hence the witness's gathered memory / map logs are empty. -/
theorem witness_memLog : memLog noteSpendLeafDesc witnessTrace = [] := rfl
theorem witness_mapLog : mapLog noteSpendLeafDesc witnessTrace = [] := rfl

/-- **Non-vacuity (accept) — the hypothesis is GENUINELY inhabited.** The concrete trace SATISFIES
the whole `noteSpendLeafDesc`: every one of the 27 constraints holds on both rows (the 12 chip
lookups land in the table, the base gates and PI pins close on `witnessAsg`/`witnessPub`), and the
memory legs are trivial (no mem/map ops). -/
theorem witnessTrace_satisfied2 :
    Satisfied2 (fun _ => 0) noteSpendLeafDesc (fun _ => 0) (fun _ => (0, 0)) [] witnessTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hc2 : c ∈ noteSpendConstraints := hc
    have hi2 : i < 2 := hi
    interval_cases i <;>
      (fin_cases hc2 <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
          Lookup.holdsAt, unlessSite, whenSite] <;>
        first
          | trivial
          | decide
          | (intro _; decide))
  · intro i hi; trivial
  · intro i hi r hr; simp only [noteSpendLeafDesc] at hr; cases hr
  · intro op hop; rw [witness_memLog] at hop; simp at hop
  · rw [witness_memLog]; exact (by decide)
  · rw [witness_memLog]; exact memCheck_nil _ _
  · rw [witness_memLog]; rfl
  · rw [witness_mapLog]; rfl

/-- **The range-check envelope is genuinely INHABITED** on the witness — every enveloped cell is
`K₀ = 657167757` or `0`, both small canonical felts (`< p`). So the bridge does NOT rest on a vacuous
range-check hypothesis. -/
theorem witness_canon : NoteCanon (envAt witnessTrace 0) where
  c1 := ⟨by decide, by decide⟩
  c2 := ⟨by decide, by decide⟩
  c5 := ⟨by decide, by decide⟩
  c14 := ⟨by decide, by decide⟩
  c18 := ⟨by decide, by decide⟩
  c19 := ⟨by decide, by decide⟩
  c28 := ⟨by decide, by decide⟩
  c29 := ⟨by decide, by decide⟩
  c30 := ⟨by decide, by decide⟩
  c54 := ⟨by decide, by decide⟩
  c62 := ⟨by decide, by decide⟩
  c64 := ⟨by decide, by decide⟩
  cnxt0 := ⟨by decide, by decide⟩
  p0 := ⟨by decide, by decide⟩
  p1 := ⟨by decide, by decide⟩
  p2 := ⟨by decide, by decide⟩
  p3 := ⟨by decide, by decide⟩
  p4 := ⟨by decide, by decide⟩
  p5 := ⟨by decide, by decide⟩
  p6 := ⟨by decide, by decide⟩

/-- **The bridge fires end-to-end on the concrete witness** (SAT ⟹ SEM, non-vacuously): the whole
spend-row relation is DERIVED, not assumed. -/
theorem witness_spec : NoteSpendLeafSpec witnessPerm (envAt witnessTrace 0) :=
  noteSpend_satisfied2_spec witnessPerm (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) []
    witnessTrace witnessTrace_satisfied2 witness_chipSound (by decide) (by decide) witness_canon

/-- A trace whose row-0 `is_merkle` is `2` (non-boolean) — the C1 tooth is violated. -/
def badMerkleRow : Assignment := fun c => if c = IS_MERKLE then 2 else 0
def badMerkleTrace : VmTrace :=
  { rows := [badMerkleRow, badMerkleRow], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — C1 tooth BITES).** The non-boolean `is_merkle` trace FAILS `Satisfied2`:
the C1 gate on row 0 forces `is_merkle·(is_merkle−1) = 0`, i.e. `2·1 = 0`. -/
theorem badMerkle_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs badMerkleTrace := by
  intro h
  have hc1 := h.rowConstraints 0 (by decide)
    (VmConstraint2.base (VmConstraint.gate (binaryGate IS_MERKLE))) (by in_constraints)
  -- the C1 gate binds `is_merkle·(is_merkle−1) ≡ 0 [ZMOD p]`; here it is `2·1 = 2`, and `p ∤ 2`.
  have hbad : (binaryGate IS_MERKLE).eval (envAt badMerkleTrace 0).loc ≡ 0 [ZMOD 2013265921] :=
    gate_of_holdsAt hash badMerkleTrace.tf (envAt badMerkleTrace 0) true _ hc1
  have hb2 : (binaryGate IS_MERKLE).eval (envAt badMerkleTrace 0).loc = 2 := by decide
  rw [hb2] at hbad; revert hbad; decide

/-- A spend-row trace with `is_merkle = 0` but `COMMITMENT (col 5) = 1 ≠ 0 = COMMITMENT_FULL (col 54)`
— the C2-final tooth is violated. -/
def badCommitRow : Assignment := fun c => if c = 5 then 1 else 0
def badCommitTrace : VmTrace :=
  { rows := [badCommitRow, badCommitRow], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject — C2-final tooth BITES).** The mismatched-commitment trace FAILS
`Satisfied2`: with `is_merkle = 0` the C2-final gate forces `COMMITMENT = COMMITMENT_FULL`, i.e.
`1 = 0` — exactly the "publish a commitment that is not the full-width binding" attack forbidden. -/
theorem badCommitment_rejects (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash noteSpendLeafDesc minit mfin maddrs badCommitTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide)
    (VmConstraint2.base (VmConstraint.gate (invEqGate IS_MERKLE 5 54))) (by in_constraints)
  have hbad : (invEqGate IS_MERKLE 5 54).eval (envAt badCommitTrace 0).loc ≡ 0 [ZMOD 2013265921] :=
    gate_of_holdsAt hash badCommitTrace.tf (envAt badCommitTrace 0) true _ hc
  have hcan5 : Canon ((envAt badCommitTrace 0).loc 5) := ⟨by decide, by decide⟩
  have hcan54 : Canon ((envAt badCommitTrace 0).loc 54) := ⟨by decide, by decide⟩
  have heq := invEqGate_spend (envAt badCommitTrace 0) (by decide) 5 54 hcan5 hcan54 hbad
  have h5 : (envAt badCommitTrace 0).loc 5 = 1 := by decide
  have h54 : (envAt badCommitTrace 0).loc 54 = 0 := by decide
  rw [h5, h54] at heq
  revert heq; decide

/-! ### Shape pins. -/
#guard decide (witnessTrace.rows.length = 2)
#guard decide (badMerkleTrace.rows.length = 2)
#guard decide (badCommitTrace.rows.length = 2)

#assert_axioms factSite_block
#assert_axioms noteSpend_satisfied2_spec
#assert_axioms witnessTrace_satisfied2
#assert_axioms witness_chipSound
#assert_axioms witness_spec
#assert_axioms badMerkle_rejects
#assert_axioms badCommitment_rejects

end Dregg2.Circuit.Emit.NoteSpendingLeafRefine
