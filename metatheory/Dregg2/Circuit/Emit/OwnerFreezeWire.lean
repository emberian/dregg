/-
# Dregg2.Circuit.Emit.OwnerFreezeWire — the OWNER FREEZE, on the wire.

## THE WOUND (E10), measured, not inferred

`circuit/tests/zzz_e10_freeze_owner_falsifier.rs` PASSES today, and its assertion is
`assert!(owner_forge_accepted)` — **1 passed means the hole is open.** Over the LIVE
`cellSealVmDescriptor2R24` parsed from the committed staged registry, it builds an honest seal,
proves and verifies it, then builds a SECOND self-consistent seal differing only in the AFTER owner
octet, and the deployed `verify_vm_descriptor2` ACCEPTS it. Its control (freezing the AFTER
lifecycle limb against `PI[46]`) is REJECTED, so the harness is live.

Root cause, and it is a MISSING CONSTRAINT, not an encoding weakness:

  * the committed owner-key octet `B_PUBKEY_OCTET = 105 .. 112` (the operated cell's
    `public_key`, `rotation_witness.rs::produce` → `canonical_32_to_felts_8(cell.public_key())`) is
    absorbed UNCONDITIONALLY into `state_commit`/NEW_COMMIT via the `wireCommitR` chain,
  * and is welded by NO `colEq` — `frozenAuthorityColEqs` freezes `B_RECORD_DIGEST · B_LIFECYCLE ·
    B_PERMS · B_VK · B_MODE · B_FIELDS_ROOT` plus the 7 headroom and 14 perms/vk completion limbs;
    the pubkey octet is in NONE of them — and pinned to NO PI on the plain path,
  * and `PI[43]` (rotated NEW commit) is the prover's CLAIMED post-state, tied by `pi_binding` to
    the trace's AFTER `B_STATE_COMMIT` and NOT independently recomputed (`proof_verify.rs`). So a
    self-consistent AFTER block with a forged owner mints a NEW_COMMIT the verifier adopts as the
    new ledger root. **No collision is required. The lock is irrelevant while this door stands.**

## ⚑ THE SCOPE IS THE WHOLE COHORT, AND THE MEASUREMENT SAYS SO

The scout expected a carve-out for the cell-CREATING members (`createCell`,
`createCellFromFactory`, `spawn`) and for `makeSovereign`. **Measured at HEAD, there is none, and
the reason is structural rather than a case analysis:**

  * every rotated member's AFTER cell is derived by ONE function — `cipherclerk.rs:5612`
    `let mut after_cell = before_cell.clone();` then `rw::apply_effect_to_cell(&mut after_cell, …)`
    per effect (and `:6345` for the multi-cohort producer, the same shape),
  * `apply_effect_to_cell` (`turn/src/rotation_witness.rs:764`) writes `state.balance`,
    `state.fields`, `state.nonce`, `permissions`, `verification_key`, `lifecycle` and `mode` — and
    **cannot write `public_key` at all**: `Cell::public_key` is `pub(crate)` in `dregg_cell`
    (`cell/src/cell.rs:345`) and `dregg_turn` is a different crate. `MakeSovereign`'s arm is
    `cell.mode = Sovereign` and nothing else. The creating verbs have no arm; they fall to `_ => {}`.
  * `createCell` / `spawn` do not exempt themselves either: the rotated BEFORE/AFTER pair is the
    OPERATED (parent) cell, and the child is a separate object outside this witness.

So on EVERY rotated cohort member, an honest AFTER owner octet EQUALS its BEFORE octet, by crate
privacy. The freeze rejects no honest witness anywhere in the cohort — it is not a cellSeal patch,
and confining it to cellSeal would leave the identical hole in the other 40 no-freeze members.

## THE FIX — welded on the WIRE, one transform, every member

`ownerFreezeWire` is the `fieldsCanonical9Wire` pattern: a `traceWidth`- / `piCount`- / table- /
site- / range-INVARIANT wrap that the emit driver (`metatheory/EmitRotationV3.lean`) applies to
EVERY rotated member at the v1-face width the member's own NAME declares, so the hardened
`…-v1-avail` members get it at their shifted base for free.

It appends `colEq (w + off) (w + AFTER_BLOCK_OFF + off)` for each owner-lane in-block offset `off`
— the SAME gate shape `frozenAuthorityColEqs` uses. **NOT a PI pin:** a pin binds the AFTER octet
to a prover-supplied PI, which the forger simply publishes at the forged value, and it is exactly
the prover-chooses-both-sides shape `dropUnforcedPins` deleted 157 of. The weld is a `colEq`.

⚑ **AND IT RIDES THE WHOLE DOMAIN.** Applied INNERMOST in the emit pipeline (before
`hardenLastRow`), each `.base (.gate …)` weld is re-lowered to a whole-domain `windowGate`
(`onTransition := false`), so the freeze binds on the LAST row too. That closes by construction the
"vacuous on the wrap row" residual `EffectVmEmitCellSealFrozenPubkey` had to carry, and it is
`ownerFreeze_hardened_freezes_every_row` below, not a hope about row-constancy.

## THE NINTH LANE, HANDLED WITHOUT GUESSING

`KeyLanes9`/`KeyCanonicity9Emit` prove the owner nonet injective, and `lane8_is_absorbed_iff` says
the ninth lane is a real column exactly when `lane8Off < rotatedNumPreLimbs`. This module welds a
lane exactly when that predicate holds (`ownerFreezeColPairs`), and `OWNER_LANE8_OFF` reads the
layout's own allocation (`B_PUBKEY_NINTH_LANE = 186`), so at today's 187-limb geometry the predicate
HOLDS and **nine** lanes are welded — `ownerFreeze_welds_the_ninth_lane`.
`ownerFreeze_welds_lane8_iff_absorbed` is the `iff` that ties the ninth weld to absorption.

⚑ **CORRECTED 2026-08-03.** Two sentences here were stale and one was false, and converting the
`#guard`s is what surfaced both.

  * The paragraph used to say the deployed instance passes `OWNER_LANE8_OFF := rotatedNumPreLimbs`,
    "hence 8 welds". That stopped being true when the knob was repointed at the layout; it is 9.
  * It also said the `#guard` below "cross-checks the emitted pair count against the absorption
    predicate so the two cannot drift". **It cannot.** `ownerFreezeColPairs_length` proves that
    equality for EVERY face width and EVERY offset — both sides read `laneIsColumn`, i.e. the same
    predicate — so the pin is a tautology and no layout move can make it red. The check with teeth
    is `ownerFreeze_welds_the_ninth_lane` (`= 9`), which reads the layout against the pre-limb
    extent. See §1.1.

## WHAT THIS BREAKS

Every member the rotation emit drivers render gains NINE whole-domain gates — the eight octet lanes
plus the ninth lane (`cellSealOwnerFrozen_constraints_length`: `+9`; the header's earlier "8 gates,
211 → 219 constraints" was measured before the ninth lane existed). **That is a descriptor re-emit
and a VK rotation** — both halves of
`dregg-epoch`'s `registry_fp` move, so a pre-flip binary is refused by `epoch::compare`, which is
the correct behaviour and the reason both the narrow and the wide drivers carry the wrap.
Geometry does NOT move: no column, no PI, no hash site, no range, no
table, no `traceWidth` (`ownerFreezeAt_*` below, all `rfl`). `CANONICAL_STATE_SCHEMA_EPOCH` does
not move either — no committed limb changes meaning. What REFUSES to load after the regen: any
proof minted against the pre-weld VK (`epoch::compare` returns a `registry_fp` mismatch), and any
witness whose AFTER owner octet differs from its BEFORE — which, per the measurement above, no
honest producer can construct.

RUNG, stated plainly. AUTHORED + PROVED (`lake build` of this module completes, 3148 jobs, zero
`sorry`, every `#assert_axioms` below green) and WIRED INTO THE EMIT DRIVERS. The wire RENDERING was
measured directly: `emitVmJson2 (hardenLastRow (fieldsCanonical9Wire (ownerFreezeWire cellSealV3)))`
carries `{"t":"window_gate","on_transition":false,…"loc":293…"loc":544}` — the BEFORE↔AFTER owner
limb-0 weld at the live 187 geometry — where the same pipeline WITHOUT this wrap carries zero
occurrences, and the member grows 132087 → 133287 bytes.

NOT reached: the committed descriptor bytes are NOT regenerated, and no verifier consumes the weld
yet. Two blockers, both named and neither a cost estimate. (1) `scripts/emit_descriptors.py` refuses
(`dregg2_source_dirty`, EXIT_REFUSED) while the sibling campaign's Lean is uncommitted, and
`DREGG_VK_REGEN_ALLOW_DIRTY=1` stamps `source_dirty=true`, which `--verify-provenance --strict` then
fails. (2) `EmitRotationV3.lean` cannot even be ELABORATED right now: its pre-existing imports
`UnforcedPiPins` and `CapOpenEmit` both reach `EffectVmEmitRotationWide`, which is RED mid-187
(`wideAppend_pins` / `wideAppend_binds_published` / `v3RegistryWide_binds` axiom-hygiene FAIL). That
blocker predates this wrap — importing `OwnerFreezeWire` alone is green.

WHEN THE REGEN RUNS, `circuit/tests/zzz_e10_freeze_owner_falsifier.rs` MUST FLIP. It asserts
`owner_forge_accepted` today — 1 passed means the hole is open — and its own closing comment says
"if this ever flips to REJECTED, an owner-binding gate landed." Inverting that assertion is the
acceptance test for this weld, and it is the one Rust change this lane deliberately did not make.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every result below.
-/
import Dregg2.Circuit.Emit.KeyCanonicity9Emit
import Dregg2.Circuit.Emit.FieldsCanonicity9Emit
import Dregg2.Circuit.Emit.LastRowFrameHardening

namespace Dregg2.Circuit.Emit.OwnerFreezeWire

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)
open Dregg2.Circuit.Emit.KeyCanonicity9Emit (deployedKeyCols preLimbColsAt lane8_is_absorbed_iff)
open Dregg2.Circuit.Emit.FieldsCanonicity9Emit (faceWidthOfName)
open Dregg2.Circuit.Emit.LastRowFrameHardening (hardenConstraint hardenLastRow WindowExpr.ofLocal)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the welded columns.

`deployedKeyCols w lane8Off blk l` is `KeyCanonicity9Emit`'s SINGLE SOURCE for "where lane `l` of
the owner nonet lives in block `blk`". Lanes 0..7 are the deployed octet at `B_PUBKEY_OCTET + l`;
lane 8 is at `lane8Off`, which is a column only when the pre-limb region has room for it. The weld
is BEFORE-block lane ↔ AFTER-block lane, at the same lane index. -/

/-- ⚑ **THE ONE KNOB.** The in-block offset of the owner nonet's ninth lane.
⚑ THIS READ `rotatedNumPreLimbs` FOR ONE COMMIT, AND THAT WAS ALREADY WRONG WHEN IT LANDED.
The prose said "the moment the layout allocates the ninth owner lane, set this to that offset".
The layout allocated it SIX MINUTES EARLIER, in the sibling commit of the same wave: limb 186,
absorbed by `wireCommitR` in both blocks. So the weld emitted EIGHT pairs and left the ninth lane
— the one carrying the owner key's source bits 232..255, INCLUDING THE Ed25519 SIGN BIT, the one
bit this entire flag day exists to bind — a free felt on the AFTER side. Composed and emitted,
that is the E10 forgery restored on precisely the lane the nonet was built for: flip the sign
bit in the AFTER block, mint a self-consistent NEW_COMMIT, and `-A` seals as `A`.

Read the LAYOUT's own allocation instead. `B_PUBKEY_NINTH_LANE` is
`(rotated196.octetLaneCol 2 8).getD 0`, i.e. where the octet table actually puts lane 8 — a
different source from the pre-limb COUNT.

⚠ That difference is what gives `ownerFreeze_welds_the_ninth_lane` (`= 9`) its teeth. It does NOT
rescue the pair-count pin this comment used to point at: that one compares the emitted list against
the same predicate the list is filtered by, and §1.1 proves it holds at every offset. -/
def OWNER_LANE8_OFF : Nat := B_PUBKEY_NINTH_LANE

/-- Is lane `l` of the owner nonet a real absorbed column at `lane8Off`? Lanes 0..7 always are (the
deployed octet); lane 8 is exactly when `lane8Off < rotatedNumPreLimbs`. -/
def laneIsColumn (lane8Off : Nat) (l : Fin 9) : Bool :=
  l.1 < 8 || decide (lane8Off < rotatedNumPreLimbs)

/-- The `(BEFORE column, AFTER column)` pairs the freeze welds, in lane order — every owner-nonet
lane that IS a column. -/
def ownerFreezeColPairs (w lane8Off : Nat) : List (Nat × Nat) :=
  (List.finRange 9).filterMap fun l =>
    if laneIsColumn lane8Off l
    then some (deployedKeyCols w lane8Off 0 l, deployedKeyCols w lane8Off 1 l)
    else none

/-- Lane `l < 8` welds the octet limb `B_PUBKEY_OCTET + l` of the BEFORE block to the same limb of
the AFTER block — the `frozenAuthorityColEqs` column shape, stated over `deployedKeyCols`. -/
theorem ownerFreezeColPairs_octet (w lane8Off : Nat) {l : Fin 9} (hl : l.1 < 8) :
    (w + (B_PUBKEY_OCTET + l.1), w + AFTER_BLOCK_OFF + (B_PUBKEY_OCTET + l.1))
      ∈ ownerFreezeColPairs w lane8Off := by
  simp only [ownerFreezeColPairs, List.mem_filterMap]
  refine ⟨l, List.mem_finRange l, ?_⟩
  have hcol : laneIsColumn lane8Off l = true := by
    simp only [laneIsColumn, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hl
  rw [if_pos hcol]
  have h0 := Dregg2.Circuit.Emit.KeyCanonicity9Emit.deployedKeyCols_octet_col w lane8Off 0 hl
  have h1 := Dregg2.Circuit.Emit.KeyCanonicity9Emit.deployedKeyCols_octet_col w lane8Off 1 hl
  simp only [h0, h1, AFTER_BLOCK_OFF]
  norm_num

/-- ⚑ **THE NINTH LANE, AS AN `iff`.** The freeze welds lane 8 EXACTLY when lane 8 is an absorbed
column — `lane8_is_absorbed_iff`'s condition verbatim. So the ninth weld cannot be forgotten when
the geometry grows, and cannot be faked onto a non-column before it does. -/
theorem ownerFreeze_welds_lane8_iff_absorbed (w lane8Off : Nat) :
    ((deployedKeyCols w lane8Off 0 8, deployedKeyCols w lane8Off 1 8)
        ∈ ownerFreezeColPairs w lane8Off)
      ↔ deployedKeyCols w lane8Off 0 8 ∈ preLimbColsAt (w + (0 : Fin 2).1 * B_SPAN) := by
  rw [lane8_is_absorbed_iff]
  simp only [ownerFreezeColPairs, List.mem_filterMap]
  constructor
  · rintro ⟨l, -, hl⟩
    by_cases hc : laneIsColumn lane8Off l
    · rw [if_pos hc] at hl
      -- the pair determines the lane: the BEFORE column pins `l`
      have habs : lane8Off < rotatedNumPreLimbs := by
        by_contra hno
        have hlt : l.1 < 8 := by
          simp only [laneIsColumn, Bool.or_eq_true, decide_eq_true_eq] at hc
          rcases hc with h | h
          · exact h
          · exact absurd h hno
        have hb := Dregg2.Circuit.Emit.KeyCanonicity9Emit.deployedKeyCols_octet_col w lane8Off 0 hlt
        have h8 := Dregg2.Circuit.Emit.KeyCanonicity9Emit.deployedKeyCols_lane8_col w lane8Off 0
        have hpk : B_PUBKEY_OCTET = 105 := rfl
        -- the deployed octet lives well inside the absorbed region at any pre-limb count this
        -- flag day contemplates, so a lane-8 column that ALIASED the octet would be absorbed
        have hroom : 112 < rotatedNumPreLimbs := by decide
        have := congrArg Prod.fst (Option.some.inj hl)
        simp only [hb, h8] at this
        omega
      exact habs
    · rw [if_neg hc] at hl; exact absurd hl (by simp)
  · intro habs
    refine ⟨8, List.mem_finRange 8, ?_⟩
    rw [if_pos (by simp only [laneIsColumn, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr habs)]

/-! ### §1.1 — the pair census. ⚑ AND THE PIN THAT COULD NOT GO RED.

The first assertion here was a `#guard` reading

```text
  (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).length
    == (if OWNER_LANE8_OFF < rotatedNumPreLimbs then 9 else 8)
```

and its comment said it was a gate "because the two sides come from genuinely different places:
the left from the EMITTED pair list, the right from the layout's octet table compared against the
pre-limb COUNT". **That is false, and writing it as a theorem is what makes it readable.**
`ownerFreezeColPairs_length` below proves the equality for EVERY `w` and EVERY `lane8Off` — it is a
tautology of the definition, because the left side filters by `laneIsColumn`, which IS
`lane8Off < rotatedNumPreLimbs`. Both sides read the same predicate. No layout move can make it
disagree, so the pin could never go red, before or after the repair its own comment describes.

That comment records a real defect and the real repair: the earlier `OWNER_LANE8_OFF :=
rotatedNumPreLimbs` made the condition `n < n`, the weld emitted eight pairs, and the ninth lane —
the one carrying the Ed25519 sign bit — was left free on the AFTER side, six minutes after the
layout allocated it. What is wrong is only the claim that the guard is what would catch a
recurrence. **The tooth is `ownerFreeze_welds_the_ninth_lane`: nine welds, `= 9`, against the
layout's own `B_PUBKEY_NINTH_LANE` — that one is red the moment the ninth lane leaves the absorbed
region.** The tautology is kept, since it was asserted and is true; it is just not a gate. -/

/-- ⚑ **THE GENERAL FACT — AND THE DEMONSTRATION THAT THE PIN IS A TAUTOLOGY.** The emitted pair
count agrees with the absorption predicate at every face width and every ninth-lane offset, because
it is computed FROM that predicate. -/
theorem ownerFreezeColPairs_length (w lane8Off : Nat) :
    (ownerFreezeColPairs w lane8Off).length
      = if lane8Off < rotatedNumPreLimbs then 9 else 8 := by
  by_cases h : lane8Off < rotatedNumPreLimbs
  · rw [if_pos h]
    simp only [ownerFreezeColPairs, laneIsColumn, decide_eq_true h, Bool.or_true]
    rfl
  · rw [if_neg h]
    simp only [ownerFreezeColPairs, laneIsColumn, decide_eq_false h, Bool.or_false]
    rfl

/-- The deployed instance the `#guard` asserted. True, and — by the theorem above — true of every
layout, which is exactly why it is not the gate. -/
theorem ownerFreezeColPairs_length_deployed :
    (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).length
      = if OWNER_LANE8_OFF < rotatedNumPreLimbs then 9 else 8 :=
  ownerFreezeColPairs_length _ _

/-- ⚑ **THE TOOTH.** NINE welds at the deployed offset — the ninth lane IS welded. This is the
assertion with content: it reads `OWNER_LANE8_OFF = B_PUBKEY_NINTH_LANE` against
`rotatedNumPreLimbs`, and it goes red exactly when the layout stops putting the owner key's ninth
lane inside the absorbed pre-limb region, which is the failure the `#guard` above was written for
and could not see. -/
theorem ownerFreeze_welds_the_ninth_lane :
    (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).length = 9 := by decide

/-- No welded pair is repeated. ⚑ Stated with the side condition it actually needs: if the ninth
lane were allocated INSIDE the octet band it would alias an octet lane and the list would repeat,
so `Nodup` is not a fact about the emit alone — it is a fact about the emit AND a non-aliasing
layout. The `#guard` at the deployed offset could not say which. -/
theorem ownerFreezeColPairs_nodup (w lane8Off : Nat)
    (h : ∀ k, k < 8 → lane8Off ≠ B_PUBKEY_OCTET + k) :
    (ownerFreezeColPairs w lane8Off).Nodup := by
  refine List.Nodup.filterMap ?_ (by decide)
  intro l l' p hl hl'
  by_cases hc : laneIsColumn lane8Off l
  · by_cases hc' : laneIsColumn lane8Off l'
    · rw [if_pos hc] at hl
      rw [if_pos hc'] at hl'
      have hfst := congrArg Prod.fst (Option.some.inj (hl.trans hl'.symm))
      have hll := l.isLt
      have hll' := l'.isLt
      simp only [deployedKeyCols, Fin.isValue, Fin.val_zero, Nat.zero_mul, Nat.add_zero] at hfst
      apply Fin.ext
      split_ifs at hfst with h1 h2 h2
      · omega
      · have := h l.1 h1; omega
      · have := h l'.1 h2; omega
      · omega
    · rw [if_neg hc'] at hl'; exact absurd hl' (by simp)
  · rw [if_neg hc] at hl; exact absurd hl (by simp)

/-- The deployed instance: limb 186 is outside the octet band `105..112`, so the welds are distinct.
-/
theorem ownerFreezeColPairs_nodup_deployed :
    (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).Nodup :=
  ownerFreezeColPairs_nodup _ _ (by decide)

/-- ⚑ **THE WELDED COLUMNS, IN CLOSED FORM, AT EVERY FACE.** The deployed NONET: the contiguous
octet `105..112` PLUS the ninth lane, which is NOT contiguous with it (it lives at limb 186, past
the octet band). That discontinuity is the whole reason these read the layout rather than a range: a
`List.range 9` here would silently demand column 113, which belongs to something else entirely.

Three `#guard`s pinned `map Prod.fst` and `map Prod.snd` at two hand-picked face widths; this is the
statement they were instances of, and it holds at every `w` — so the `198` instance below is a
corollary rather than a second hand-typed list. -/
theorem ownerFreezeColPairs_eq (w lane8Off : Nat) (h : lane8Off < rotatedNumPreLimbs) :
    ownerFreezeColPairs w lane8Off
      = (List.range 8).map (fun k => (w + B_PUBKEY_OCTET + k, w + B_SPAN + B_PUBKEY_OCTET + k))
        ++ [(w + lane8Off, w + B_SPAN + lane8Off)] := by
  simp only [ownerFreezeColPairs, laneIsColumn, decide_eq_true h, Bool.or_true]
  rfl

theorem ownerFreezeColPairs_fst_deployed :
    (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).map Prod.fst
      = (List.range 8).map (fun k => EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k)
        ++ [EFFECT_VM_WIDTH + B_PUBKEY_NINTH_LANE] := by
  rw [ownerFreezeColPairs_eq _ _ (by decide)]
  simp [OWNER_LANE8_OFF]

theorem ownerFreezeColPairs_snd_deployed :
    (ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).map Prod.snd
      = (List.range 8).map (fun k => EFFECT_VM_WIDTH + B_SPAN + B_PUBKEY_OCTET + k)
        ++ [EFFECT_VM_WIDTH + B_SPAN + B_PUBKEY_NINTH_LANE] := by
  rw [ownerFreezeColPairs_eq _ _ (by decide)]
  simp [OWNER_LANE8_OFF]

/-- The hardened `…-v1-avail` face, where the same nonet rides a shifted base. -/
theorem ownerFreezeColPairs_fst_avail :
    (ownerFreezeColPairs 198 OWNER_LANE8_OFF).map Prod.fst
      = (List.range 8).map (fun k => 198 + B_PUBKEY_OCTET + k) ++ [198 + B_PUBKEY_NINTH_LANE] := by
  rw [ownerFreezeColPairs_eq _ _ (by decide)]
  simp [OWNER_LANE8_OFF]

/-- ⚑ **EVERY WELDED COLUMN IS AN ABSORBED PRE-LIMB — UNCONDITIONALLY.** The weld rides the
`wireCommitR` chain; it does not freeze a free felt beside it. This needs NO hypothesis on
`lane8Off`: a lane is in the pair list only if `laneIsColumn` admitted it, and that predicate is
`lane8_is_absorbed_iff`'s condition. The two `#guard`s checked the deployed face; the fact is about
the emit. -/
theorem ownerFreeze_before_cols_absorbed (w lane8Off : Nat) :
    ∀ p ∈ ownerFreezeColPairs w lane8Off, p.1 ∈ preLimbColsAt w := by
  intro p hp
  simp only [ownerFreezeColPairs, List.mem_filterMap] at hp
  obtain ⟨l, -, hl⟩ := hp
  by_cases hc : laneIsColumn lane8Off l
  · rw [if_pos hc] at hl
    rcases Nat.lt_or_ge l.1 8 with h8 | h8
    · have := Dregg2.Circuit.Emit.KeyCanonicity9Emit.octet_cols_are_absorbed w lane8Off 0 h8
      simpa [← Option.some.inj hl] using this
    · have hl8 : l = 8 := by apply Fin.ext; have := l.isLt; omega
      subst hl8
      have habs : lane8Off < rotatedNumPreLimbs := by simpa [laneIsColumn] using hc
      have := (lane8_is_absorbed_iff w lane8Off 0).mpr habs
      simpa [← Option.some.inj hl] using this
  · rw [if_neg hc] at hl; exact absurd hl (by simp)

/-- …and every welded AFTER column is an absorbed pre-limb of the AFTER block. -/
theorem ownerFreeze_after_cols_absorbed (w lane8Off : Nat) :
    ∀ p ∈ ownerFreezeColPairs w lane8Off, p.2 ∈ preLimbColsAt (w + B_SPAN) := by
  intro p hp
  simp only [ownerFreezeColPairs, List.mem_filterMap] at hp
  obtain ⟨l, -, hl⟩ := hp
  by_cases hc : laneIsColumn lane8Off l
  · rw [if_pos hc] at hl
    rcases Nat.lt_or_ge l.1 8 with h8 | h8
    · have := Dregg2.Circuit.Emit.KeyCanonicity9Emit.octet_cols_are_absorbed w lane8Off 1 h8
      simpa [← Option.some.inj hl] using this
    · have hl8 : l = 8 := by apply Fin.ext; have := l.isLt; omega
      subst hl8
      have habs : lane8Off < rotatedNumPreLimbs := by simpa [laneIsColumn] using hc
      have := (lane8_is_absorbed_iff w lane8Off 1).mpr habs
      simpa [← Option.some.inj hl] using this
  · rw [if_neg hc] at hl; exact absurd hl (by simp)

theorem ownerFreeze_before_cols_absorbed_deployed :
    ((ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).map Prod.fst).all
      (fun c => (preLimbColsAt EFFECT_VM_WIDTH).contains c) = true := by
  simp only [List.all_eq_true, List.mem_map, List.contains_iff_mem]
  rintro c ⟨p, hp, rfl⟩
  exact ownerFreeze_before_cols_absorbed _ _ p hp

theorem ownerFreeze_after_cols_absorbed_deployed :
    ((ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF).map Prod.snd).all
      (fun c => (preLimbColsAt (EFFECT_VM_WIDTH + B_SPAN)).contains c) = true := by
  simp only [List.all_eq_true, List.mem_map, List.contains_iff_mem]
  rintro c ⟨p, hp, rfl⟩
  exact ownerFreeze_after_cols_absorbed _ _ p hp

#assert_axioms ownerFreezeColPairs_length
#assert_axioms ownerFreezeColPairs_length_deployed
#assert_axioms ownerFreeze_welds_the_ninth_lane
#assert_axioms ownerFreezeColPairs_nodup
#assert_axioms ownerFreezeColPairs_nodup_deployed
#assert_axioms ownerFreezeColPairs_eq
#assert_axioms ownerFreezeColPairs_fst_deployed
#assert_axioms ownerFreezeColPairs_snd_deployed
#assert_axioms ownerFreezeColPairs_fst_avail
#assert_axioms ownerFreeze_before_cols_absorbed
#assert_axioms ownerFreeze_after_cols_absorbed
#assert_axioms ownerFreeze_before_cols_absorbed_deployed
#assert_axioms ownerFreeze_after_cols_absorbed_deployed

/-! ## §2 — the emitted constraints and the wrap. -/

/-- The freeze's constraints at face width `w`: one `colEq` per welded lane. -/
def ownerFreezeConstraintsAt (w lane8Off : Nat) : List VmConstraint2 :=
  (ownerFreezeColPairs w lane8Off).map fun p => .base (colEq p.1 p.2)

/-- **THE WRAP.** Additive: constraints only. -/
def ownerFreezeAt (w lane8Off : Nat) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints ++ ownerFreezeConstraintsAt w lane8Off }

/-- **THE WIRE WRAP** — the freeze at the face width the member's own NAME declares, sharing
`FieldsCanonicity9Emit.faceWidthOfName` (the Lean twin of
`trace_rotated::avail_pad_for_descriptor_name`) so bare and hardened members land at the right base
from ONE source. This is the transform `EmitRotationV3.lean` applies to every rotated member. -/
def ownerFreezeWire (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  ownerFreezeAt (faceWidthOfName d.name) OWNER_LANE8_OFF d

/-! ### The shape, machine-checked: geometry does not move. -/

theorem ownerFreezeAt_name (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).name = d.name := rfl
theorem ownerFreezeAt_traceWidth (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).traceWidth = d.traceWidth := rfl
theorem ownerFreezeAt_piCount (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).piCount = d.piCount := rfl
theorem ownerFreezeAt_tables (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).tables = d.tables := rfl
theorem ownerFreezeAt_hashSites (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).hashSites = d.hashSites := rfl
theorem ownerFreezeAt_ranges (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).ranges = d.ranges := rfl
theorem ownerFreezeAt_constraints (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).constraints
      = d.constraints ++ ownerFreezeConstraintsAt w lane8Off := rfl

/-- Every appended constraint is a `.base (.gate …)` — no bus op, so no log moves. -/
theorem ownerFreeze_all_gates (w lane8Off : Nat) :
    ∀ c ∈ ownerFreezeConstraintsAt w lane8Off, ∃ b, c = .base (.gate b) := by
  intro c hc
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
  exact ⟨_, rfl⟩

/-- The wrap contributes no mem-op (the mem log is unchanged). -/
theorem memOpsOf_ownerFreezeAt (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    memOpsOf (ownerFreezeAt w lane8Off d) = memOpsOf d := by
  simp [memOpsOf, ownerFreezeAt, ownerFreezeConstraintsAt, List.filterMap_append,
    List.filterMap_map]

/-- The wrap contributes no map-op (the map log is unchanged). -/
theorem mapOpsOf_ownerFreezeAt (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    mapOpsOf (ownerFreezeAt w lane8Off d) = mapOpsOf d := by
  simp [mapOpsOf, ownerFreezeAt, ownerFreezeConstraintsAt, List.filterMap_append,
    List.filterMap_map]

/-- **THE PEEL** — `Satisfied2 (ownerFreezeAt w lane8Off d) ⟹ Satisfied2 d`. The hardened member
only REJECTS, never newly-accepts, so every existing per-effect soundness keystone lifts to the
frozen member by peeling the wrap first. -/
theorem satisfied2_of_ownerFreezeAt (hash : List ℤ → ℤ) (w lane8Off : Nat)
    (d : EffectVmDescriptor2) {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (ownerFreezeAt w lane8Off d) minit mfin maddrs t) :
    Satisfied2 hash d minit mfin maddrs t := by
  have hmem : memLog (ownerFreezeAt w lane8Off d) t = memLog d t := by
    simp [memLog, memOpsOf_ownerFreezeAt]
  have hmap : mapLog (ownerFreezeAt w lane8Off d) t = mapLog d t := by
    simp [mapLog, mapOpsOf_ownerFreezeAt]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c
        (by rw [ownerFreezeAt_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-! ## §3 — THE FREEZE: what a satisfying witness is forced to. -/

/-- On a TRANSITION row of a satisfying witness of the pre-hardening wrap, every welded owner lane
agrees BEFORE↔AFTER (mod `p`). This is the resolution the deployed `frozenAuthorityColEqs` welds
bind at; `ownerFreeze_hardened_freezes_every_row` below is the wire's stronger statement. -/
theorem ownerFreeze_freezes (hash : List ℤ → ℤ) (w lane8Off : Nat) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (ownerFreezeAt w lane8Off d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (p : Nat × Nat) (hp : p ∈ ownerFreezeColPairs w lane8Off) :
    (envAt t i).loc p.1 ≡ (envAt t i).loc p.2 [ZMOD 2013265921] := by
  have hlastb : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hin : VmConstraint2.base (colEq p.1 p.2) ∈ (ownerFreezeAt w lane8Off d).constraints := by
    rw [ownerFreezeAt_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt] at h
  exact (colEq_holds_iff (envAt t i) (i == 0) (i + 1 == t.rows.length) _ _ hlastb).mp h

/-- **THE OWNER IS DETERMINED.** With both welded columns canonical (`0 ≤ · < p`, the deployed
committed-column envelope), the AFTER owner lane is EQUAL to the BEFORE owner lane as integers —
not congruent, equal. A seal freezes the owner; it does not re-author it. -/
theorem ownerFreeze_determines_the_owner (hash : List ℤ → ℤ) (w lane8Off : Nat)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (ownerFreezeAt w lane8Off d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (p : Nat × Nat) (hp : p ∈ ownerFreezeColPairs w lane8Off)
    (hb : 0 ≤ (envAt t i).loc p.1 ∧ (envAt t i).loc p.1 < 2013265921)
    (ha : 0 ≤ (envAt t i).loc p.2 ∧ (envAt t i).loc p.2 < 2013265921) :
    (envAt t i).loc p.1 = (envAt t i).loc p.2 :=
  canon_eq_of_modEq hb ha
    (ownerFreeze_freezes hash w lane8Off d minit mfin maddrs t hsat i hi hnotlast p hp)

/-! ### §3.1 — the wire is STRONGER: the freeze binds on the LAST row too.

The emit driver applies `hardenLastRow` OUTSIDE this wrap, which re-lowers every `.base (.gate b)`
to a whole-domain `windowGate`. So the emitted owner weld is asserted on EVERY row, including the
one carrying `state_commit`/NEW_COMMIT. -/

/-- Hardening turns each owner weld into a whole-domain `windowGate` carrying the same body. -/
theorem hardenConstraint_colEq (a b : Nat) :
    hardenConstraint (.base (colEq a b))
      = .windowGate { body := WindowExpr.ofLocal (.add (.var a) (.mul (.const (-1)) (.var b)))
                    , onTransition := false } := rfl

/-- **THE WIRE FREEZE — every row, no exception.** On ANY row of a satisfying witness of the
HARDENED frozen member, every welded owner lane agrees BEFORE↔AFTER. No row-constancy assumption,
no "the weld is read at the active row" caveat: `onTransition = false` means the gate has no
transition guard to hide behind. -/
theorem ownerFreeze_hardened_freezes_every_row (hash : List ℤ → ℤ) (w lane8Off : Nat)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (hardenLastRow (ownerFreezeAt w lane8Off d)) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (p : Nat × Nat) (hp : p ∈ ownerFreezeColPairs w lane8Off) :
    (envAt t i).loc p.1 ≡ (envAt t i).loc p.2 [ZMOD 2013265921] := by
  have hin : hardenConstraint (.base (colEq p.1 p.2))
      ∈ (hardenLastRow (ownerFreezeAt w lane8Off d)).constraints := by
    simp only [hardenLastRow]
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    rw [ownerFreezeAt_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  rw [hardenConstraint_colEq] at h
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, Bool.false_eq_true, if_false,
    Dregg2.Circuit.Emit.LastRowFrameHardening.ofLocal_eval,
    Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at h
  exact (Dregg2.Circuit.Emit.EffectVmEmitTransfer.gate_modEq_iff (a := (envAt t i).loc p.1)
    (b := (envAt t i).loc p.2) (by ring)).mp h

/-! ## §4 — ⚑ THE EXHIBIT.

A CONCRETE witness with a forged AFTER owner, and its refutation with no hypotheses attached: not
"any trace satisfying `hforge` is rejected", but *this* trace, unconditionally, for every `hash`,
every memory boundary, every address list.

The exhibit is the falsifier's forge in miniature: BEFORE owner limb 0 reads `0`, AFTER owner limb 0
reads `1` — one limb, moved by one, everything else zero. The Rust falsifier's forge moves the same
limb over the real curve points and the real deployed packer. -/

/-- The BEFORE owner limb-0 column at the bare cohort face. -/
def probeBeforeCol : Nat := EFFECT_VM_WIDTH + B_PUBKEY_OCTET
/-- The AFTER owner limb-0 column at the bare cohort face. -/
def probeAfterCol : Nat := EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET

/-- The two welded columns are distinct — the AFTER block is a whole `B_SPAN` past the BEFORE one,
and `B_SPAN > 0` at any pre-limb count. Stated off `B_SPAN`, not off a numeral, so the 184 → 187
move cannot silently collapse the exhibit. -/
theorem probe_cols_distinct : probeBeforeCol ≠ probeAfterCol := by
  simp only [probeBeforeCol, probeAfterCol, AFTER_BLOCK_OFF, B_SPAN]
  omega

/-- ⚑ **THE FORGED ROW.** Owner limb 0 reads `0` BEFORE and `1` AFTER: an owner CHANGE inside a
turn whose kernel projection cannot author one. -/
def forgedOwnerRow : Assignment := fun c => if c = probeAfterCol then 1 else 0

theorem forgedOwnerRow_before : forgedOwnerRow probeBeforeCol = 0 := by
  simp only [forgedOwnerRow, if_neg probe_cols_distinct]
theorem forgedOwnerRow_after : forgedOwnerRow probeAfterCol = 1 := by
  simp [forgedOwnerRow]

/-- The exhibit trace: two rows carrying the forged row, empty public inputs, empty tables. Two
rows so that row 0 is a genuine TRANSITION row — the exhibit does not hide inside the wrap-row
vacuity the pre-hardening weld would allow. -/
def forgedOwnerTrace : VmTrace :=
  { rows := [forgedOwnerRow, forgedOwnerRow], pub := zeroAsg, tf := fun _ => [] }

/-- `0 ≢ 1` mod BabyBear's prime: the arithmetic content of the refutation, isolated. -/
theorem zero_not_modEq_one : ¬ ((0 : ℤ) ≡ 1 [ZMOD 2013265921]) := by decide

/-- **⚑ THE EXHIBIT IS UNSAT UNDER THE WELD — unconditionally.** For EVERY `hash`, every memory
boundary and every address list, the forged-owner trace does NOT satisfy any owner-frozen member at
the bare cohort face. The refutation extracts the owner weld from the appended tail and evaluates
it on row 0, a transition row; nothing about `d` is used, so this holds of `cellSeal` and of all 56
of its rotated siblings at once. -/
theorem forged_owner_is_unsat_under_the_weld (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash (ownerFreezeAt EFFECT_VM_WIDTH OWNER_LANE8_OFF d)
        minit mfin maddrs forgedOwnerTrace := by
  intro hsat
  have hp : (probeBeforeCol, probeAfterCol)
      ∈ ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF := by
    have := ownerFreezeColPairs_octet EFFECT_VM_WIDTH OWNER_LANE8_OFF (l := (0 : Fin 9))
      (by decide)
    simpa [probeBeforeCol, probeAfterCol, AFTER_BLOCK_OFF] using this
  have hrows : forgedOwnerTrace.rows.length = 2 := rfl
  have hfreeze := ownerFreeze_freezes hash EFFECT_VM_WIDTH OWNER_LANE8_OFF d minit mfin maddrs
    forgedOwnerTrace hsat 0 (by rw [hrows]; omega) (by rw [hrows]; omega) _ hp
  have hloc : (envAt forgedOwnerTrace 0).loc = forgedOwnerRow := rfl
  rw [hloc, forgedOwnerRow_before, forgedOwnerRow_after] at hfreeze
  exact zero_not_modEq_one hfreeze

/-- The same refutation against the HARDENED (wire) member, where the weld has no transition guard:
the exhibit is rejected on every row, not merely on a transition row. -/
theorem forged_owner_is_unsat_on_the_wire (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash (hardenLastRow (ownerFreezeAt EFFECT_VM_WIDTH OWNER_LANE8_OFF d))
        minit mfin maddrs forgedOwnerTrace := by
  intro hsat
  have hp : (probeBeforeCol, probeAfterCol)
      ∈ ownerFreezeColPairs EFFECT_VM_WIDTH OWNER_LANE8_OFF := by
    have := ownerFreezeColPairs_octet EFFECT_VM_WIDTH OWNER_LANE8_OFF (l := (0 : Fin 9))
      (by decide)
    simpa [probeBeforeCol, probeAfterCol, AFTER_BLOCK_OFF] using this
  have hrows : forgedOwnerTrace.rows.length = 2 := rfl
  have hfreeze := ownerFreeze_hardened_freezes_every_row hash EFFECT_VM_WIDTH OWNER_LANE8_OFF d
    minit mfin maddrs forgedOwnerTrace hsat 1 (by rw [hrows]; omega) _ hp
  have hloc : (envAt forgedOwnerTrace 1).loc = forgedOwnerRow := rfl
  rw [hloc, forgedOwnerRow_before, forgedOwnerRow_after] at hfreeze
  exact zero_not_modEq_one hfreeze

/-! ### §4.1 — ⚑ THE MUTATION: drop the weld and the exhibit is satisfiable again.

`ownerFreezeAt` with an EMPTY welded-lane set is the pre-weld status quo, and the SAME forged trace
satisfies it. Both halves are stated over the same `Satisfied2`, the same trace and the same
descriptor record — the only thing that moves is whether the owner welds are present. -/

/-- The freeze's own constraints, isolated as a descriptor: the weld and nothing else, so a full
`Satisfied2` is checkable in BOTH directions. Geometry wide enough to hold both rotated blocks. -/
def ownerWeldProbe : EffectVmDescriptor2 :=
  { name := "owner-freeze-probe"
  , traceWidth := EFFECT_VM_WIDTH + 2 * B_SPAN
  , piCount := 0
  , tables := []
  , constraints := ownerFreezeConstraintsAt EFFECT_VM_WIDTH OWNER_LANE8_OFF
  , hashSites := []
  , ranges := [] }

/-- ⚑ **THE MUTATION** — the probe with the owner welds DROPPED, and nothing else changed. -/
def ownerWeldProbeMutated : EffectVmDescriptor2 := { ownerWeldProbe with constraints := [] }

/-- The wrap appends one constraint per welded pair — at every face width, every offset, every
descriptor. The three `#guard`s below are instances of this and of
`ownerFreeze_welds_the_ninth_lane`. -/
theorem ownerFreezeConstraintsAt_length (w lane8Off : Nat) :
    (ownerFreezeConstraintsAt w lane8Off).length = (ownerFreezeColPairs w lane8Off).length := by
  simp [ownerFreezeConstraintsAt]

theorem ownerFreezeAt_constraints_length (w lane8Off : Nat) (d : EffectVmDescriptor2) :
    (ownerFreezeAt w lane8Off d).constraints.length
      = d.constraints.length + (ownerFreezeColPairs w lane8Off).length := by
  simp [ownerFreezeAt, ownerFreezeConstraintsAt]

/-- NINE, not eight: the ninth is the owner key's lane-8 column at limb 186, which the weld only
gained once `OWNER_LANE8_OFF` stopped reading the pre-limb COUNT and started reading the layout. -/
theorem ownerWeldProbe_constraints_length : ownerWeldProbe.constraints.length = 9 := by
  show (ownerFreezeConstraintsAt EFFECT_VM_WIDTH OWNER_LANE8_OFF).length = 9
  rw [ownerFreezeConstraintsAt_length]
  exact ownerFreeze_welds_the_ninth_lane

theorem ownerWeldProbeMutated_constraints_length : ownerWeldProbeMutated.constraints.length = 0 :=
  rfl

theorem ownerWeldProbe_traceWidth : ownerWeldProbe.traceWidth = ownerWeldProbeMutated.traceWidth :=
  rfl

#assert_axioms ownerFreezeConstraintsAt_length
#assert_axioms ownerFreezeAt_constraints_length
#assert_axioms ownerWeldProbe_constraints_length
#assert_axioms ownerWeldProbeMutated_constraints_length
#assert_axioms ownerWeldProbe_traceWidth

/-- **UNSAT with the weld.** -/
theorem forged_owner_unsat_on_the_probe (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash ownerWeldProbe minit mfin maddrs forgedOwnerTrace := by
  intro hsat
  refine forged_owner_is_unsat_under_the_weld hash ownerWeldProbeMutated minit mfin maddrs ?_
  exact
    { rowConstraints := fun i hi c hc => hsat.rowConstraints i hi c (by
        rw [ownerFreezeAt_constraints] at hc
        simpa [ownerWeldProbeMutated, ownerWeldProbe] using hc)
    , rowHashes := hsat.rowHashes
    , rowRanges := hsat.rowRanges
    , memAddrsNodup := hsat.memAddrsNodup
    , memClosed := fun op hop => hsat.memClosed op (by
        simp [memLog, memOpsOf, ownerFreezeAt, ownerWeldProbe, ownerWeldProbeMutated,
          ownerFreezeConstraintsAt, List.filterMap_map] at hop)
    , memDisciplined := by
        simpa [memLog, memOpsOf, ownerFreezeAt, ownerWeldProbe, ownerWeldProbeMutated,
          ownerFreezeConstraintsAt, List.filterMap_map] using hsat.memDisciplined
    , memBalanced := by
        simpa [memLog, memOpsOf, ownerFreezeAt, ownerWeldProbe, ownerWeldProbeMutated,
          ownerFreezeConstraintsAt, List.filterMap_map] using hsat.memBalanced
    , memTableFaithful := by
        simpa [memLog, memOpsOf, ownerFreezeAt, ownerWeldProbe, ownerWeldProbeMutated,
          ownerFreezeConstraintsAt, List.filterMap_map] using hsat.memTableFaithful
    , mapTableFaithful := by
        simpa [mapLog, mapOpsOf, ownerFreezeAt, ownerWeldProbe, ownerWeldProbeMutated,
          ownerFreezeConstraintsAt, List.filterMap_map] using hsat.mapTableFaithful }

/-- ⚑ **SAT once the weld is dropped.** The very same forged-owner trace satisfies the mutated
probe — with an EMPTY memory boundary, so no leg is discharged by an accident of the boundary. So
the weld is LOAD-BEARING: it is the whole of what rejects the forgery, and its removal restores
acceptance. This is the Lean half of what `zzz_e10_freeze_owner_falsifier.rs` measured over the
live descriptor and the real producer. -/
theorem forged_owner_sat_when_the_weld_is_dropped (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash ownerWeldProbeMutated minit mfin [] forgedOwnerTrace :=
  { rowConstraints := fun i hi c hc => absurd hc (by simp [ownerWeldProbeMutated])
  , rowHashes := fun i hi => by simp [ownerWeldProbeMutated, ownerWeldProbe, siteHoldsAll,
      siteHoldsAll.go]
  , rowRanges := fun i hi r hr => absurd hr (by simp [ownerWeldProbeMutated, ownerWeldProbe])
  , memAddrsNodup := List.nodup_nil
  , memClosed := fun op hop => absurd hop (by
      simp [memLog, memOpsOf, ownerWeldProbeMutated])
  , memDisciplined := by
      simp [memLog, memOpsOf, ownerWeldProbeMutated, forgedOwnerTrace]; trivial
  , memBalanced := by simp [memLog, memOpsOf, ownerWeldProbeMutated, forgedOwnerTrace,
      Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet, Dregg2.Crypto.MemoryChecking.boundarySet]
  , memTableFaithful := by simp [memLog, memOpsOf, ownerWeldProbeMutated, forgedOwnerTrace]
  , mapTableFaithful := by simp [mapLog, mapOpsOf, ownerWeldProbeMutated, forgedOwnerTrace] }

/-! ## §5 — the deployed instances and the census. -/

/-- The LIVE `cellSealVmDescriptor2R24` WITH the owner freeze — the member
`zzz_e10_freeze_owner_falsifier.rs` measured accepting the forgery. -/
def cellSealOwnerFrozen : EffectVmDescriptor2 := ownerFreezeWire cellSealV3

/-! ### BYTE-SHAPE: the freeze adds exactly the welds and NO PI, NO column.

Five `#guard`s until 2026-08-03. Four were instances of the `ownerFreezeAt_*` `rfl`-theorems three
screens up — the guard re-evaluated the whole descriptor to learn what a term already said. The
fifth ("the name-derived face IS the bare cohort face") is the one that mattered, and as a THEOREM
it does work a guard could not: `cellSealOwnerFrozen_eq` turns it into a rewrite, so §4's exhibit
applies to the NAMED deployed member by composition rather than by a reader's say-so
(`forged_owner_is_unsat_on_cellSeal`). -/

theorem cellSealOwnerFrozen_piCount : cellSealOwnerFrozen.piCount = cellSealV3.piCount :=
  ownerFreezeAt_piCount _ _ _

theorem cellSealOwnerFrozen_traceWidth : cellSealOwnerFrozen.traceWidth = cellSealV3.traceWidth :=
  ownerFreezeAt_traceWidth _ _ _

theorem cellSealOwnerFrozen_name : cellSealOwnerFrozen.name = cellSealV3.name :=
  ownerFreezeAt_name _ _ _

/-- The wire name of the live member, read off the emitted descriptor. -/
theorem cellSealV3_name : cellSealV3.name = "dregg-effectvm-cellseal-v2-rot24-v3-staged" := rfl

/-- …and the name-derived face IS the bare cohort face, so the exhibit above is about the emitted
object and not a lookalike at some other base. Cross-file: the face width comes from
`KeyCanonicity9Emit.faceWidth_cellseal`, which is the same fact its own registry census pins. -/
theorem cellSealV3_faceWidth : faceWidthOfName cellSealV3.name = EFFECT_VM_WIDTH := by
  rw [cellSealV3_name]
  exact Dregg2.Circuit.Emit.KeyCanonicity9Emit.faceWidth_cellseal

/-- ⚑ **THE DEPLOYED MEMBER IS THE FREEZE AT THE BARE COHORT FACE** — the term the face-width
`#guard` could not produce. -/
theorem cellSealOwnerFrozen_eq :
    cellSealOwnerFrozen = ownerFreezeAt EFFECT_VM_WIDTH OWNER_LANE8_OFF cellSealV3 := by
  unfold cellSealOwnerFrozen ownerFreezeWire
  rw [cellSealV3_faceWidth]

/-- The freeze adds exactly nine constraints to the live member: eight octet lanes plus the ninth
lane. `211 → 219` in the header was measured before the ninth lane existed; the ninth weld took it
to `220`. -/
theorem cellSealOwnerFrozen_constraints_length :
    cellSealOwnerFrozen.constraints.length = cellSealV3.constraints.length + 9 := by
  rw [cellSealOwnerFrozen_eq, ownerFreezeAt_constraints_length, ownerFreeze_welds_the_ninth_lane]

/-- ⚑ **AND THEREFORE THE EXHIBIT LANDS ON THE NAMED MEMBER.** §4 refuted the forged-owner trace
against `ownerFreezeAt EFFECT_VM_WIDTH OWNER_LANE8_OFF d` for an arbitrary `d`; this is that
refutation at `cellSealOwnerFrozen` itself — the member `zzz_e10_freeze_owner_falsifier.rs` measured
accepting the forgery. It is one `rw` because the face-width fact is now a theorem. -/
theorem forged_owner_is_unsat_on_cellSeal (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    ¬ Satisfied2 hash cellSealOwnerFrozen minit mfin maddrs forgedOwnerTrace := by
  rw [cellSealOwnerFrozen_eq]
  exact forged_owner_is_unsat_under_the_weld hash cellSealV3 minit mfin maddrs

#assert_axioms cellSealOwnerFrozen_piCount
#assert_axioms cellSealOwnerFrozen_traceWidth
#assert_axioms cellSealOwnerFrozen_name
#assert_axioms cellSealOwnerFrozen_constraints_length
#assert_axioms cellSealV3_name
#assert_axioms cellSealV3_faceWidth
#assert_axioms cellSealOwnerFrozen_eq
#assert_axioms forged_owner_is_unsat_on_cellSeal

/-- The owner weld of lane `k` as the emit driver RENDERS it — the wire bytes, not a Lean term. -/
def ownerWeldJson (k : Nat) : String :=
  VmConstraint2.toJson (.base (colEq (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k)
    (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k)))

/-! ### ⚑ THE CENSUS, over the RENDERED WIRE.

The DEPLOYED member carries no owner weld (the hole the Rust falsifier measured); the frozen member
carries all eight. Compared as emitted JSON, so this is a statement about the bytes a verifier
parses — and the pair flips the moment the weld reaches the wire.

Both halves were `#guard`s. The ABSENCE half stays an evaluation — it is a claim about 219 specific
committed constraints and there is nothing general to say about it — but `by decide` puts it in the
KERNEL, which the guard's `unsafe evalExpr` was not. The PRESENCE half became a `∀ k < 8` proved
from the wrap (`ownerWeld_is_on_the_wire`), so it does not depend on re-rendering the member. -/

set_option maxRecDepth 20000 in
/-- ⚑ **NO OWNER WELD ON THE DEPLOYED MEMBER.** The hole, as bytes. -/
theorem cellSealV3_carries_no_owner_weld :
    (List.range 8).all (fun k =>
      !(cellSealV3.constraints.map VmConstraint2.toJson).contains (ownerWeldJson k)) = true := by
  decide

/-- ⚑ **THE WELD IS ON THE WIRE, FOR EVERY OCTET LANE.** Proved from `ownerFreezeColPairs_octet`
through `cellSealOwnerFrozen_eq`, so it is a statement about what the wrap EMITS and not about what
one rendering happened to contain. -/
theorem ownerWeld_is_on_the_wire (k : Nat) (hk : k < 8) :
    VmConstraint2.base (colEq (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k)
        (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k))
      ∈ cellSealOwnerFrozen.constraints := by
  have hp := ownerFreezeColPairs_octet EFFECT_VM_WIDTH OWNER_LANE8_OFF
    (l := (⟨k, by omega⟩ : Fin 9)) hk
  rw [cellSealOwnerFrozen_eq, ownerFreezeAt_constraints]
  refine List.mem_append_right _ (List.mem_map.mpr ⟨_, hp, ?_⟩)
  simp only [Nat.add_assoc]

theorem cellSealOwnerFrozen_carries_every_owner_weld :
    (List.range 8).all (fun k =>
      (cellSealOwnerFrozen.constraints.map VmConstraint2.toJson).contains (ownerWeldJson k))
      = true := by
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem, List.mem_map]
  intro k hk
  exact ⟨_, ownerWeld_is_on_the_wire k hk, rfl⟩

#assert_axioms cellSealV3_carries_no_owner_weld
#assert_axioms ownerWeld_is_on_the_wire
#assert_axioms cellSealOwnerFrozen_carries_every_owner_weld

#assert_axioms ownerFreezeColPairs_octet
#assert_axioms ownerFreeze_welds_lane8_iff_absorbed
#assert_axioms ownerFreeze_all_gates
#assert_axioms satisfied2_of_ownerFreezeAt
#assert_axioms ownerFreeze_freezes
#assert_axioms ownerFreeze_determines_the_owner
#assert_axioms ownerFreeze_hardened_freezes_every_row
#assert_axioms forged_owner_is_unsat_under_the_weld
#assert_axioms forged_owner_is_unsat_on_the_wire
#assert_axioms forged_owner_unsat_on_the_probe
#assert_axioms forged_owner_sat_when_the_weld_is_dropped

end Dregg2.Circuit.Emit.OwnerFreezeWire
