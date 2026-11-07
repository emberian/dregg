/-
# Dregg2.Circuit.Emit.PiDeclarationDeployed — the FIRST deployed member routed through the gate.

`Emit.PiDeclaration` is the mechanism; `Circuit.PiDeclarationBite` is its armed refusal. Neither
is worth anything until a REAL descriptor is made to pass through it, because a side condition no
emitted object carries is decoration.

This file declares every one of the 43 published public inputs of the deployed narrow member
`burnVmDescriptor2R24` (`dregg-effectvm-burn-v1-rot24-v3-staged`, `v3Registry`), and the
declaration is CHECKED against the descriptor: `burnDecl_admitted` does not elaborate unless the
15 `.bound` entries name pins the member really carries, on the rows it really carries them, at
columns something other than the pin really reads — and unless the other **28** slots are declared
transcript-only with a written reason.

⚑ **It was 50 slots / 35 transcript-only until 2026-08-07.** The SEVEN-SLOT PI COMPACTION
(`docs/PI-DISPOSITION.md` §6) deleted v1 offsets 26..32 — `CURRENT_BLOCK_HEIGHT`,
`MAX_CUSTOM_EFFECTS`, `CUSTOM_EFFECT_COUNT`, `APPROVED_HANDOFFS[4]` — so four of the reasons below
(`rVerifierHeight`, `rCustomCaps`, `rCustomCount`, `rApprovedHandoffs`) went with them. That is
what a transcript-only reason reading "this slot should be DELETED" is FOR: it was, and the
declaration is where the compaction lane found them.

## What the 28 are, and why this file exists

They are 65% of what this member publishes. Before this file, the tree recorded nothing about
them: not that they were deliberate, not that they were forgotten, not which. The reasons below
are the record, and each one is now load-bearing in a specific way — a slot declared
transcript-only carries `PiDeclaration.transcriptOnly_admits_any_value`, i.e. the machine-checked
statement that the AIR admits ANY value there and a light client reading it is reading the
producer's word.

⚑ **`TURN_HASH` (26..29, post-compaction) is declared transcript-only UNDER PROTEST, and its
reason says so.** It
is the one slot in this file whose honest disposition is `.bound` and cannot yet be: there is no
trace carrier for the turn hash anywhere in the rotated geometry (`grep turn_hash
circuit/src/effect_vm/trace_rotated.rs` → zero hits; `columns.rs`'s `aux_off` has no entry), so
`.bound` has no column to name. The declaration records the debt where the debt is, instead of
leaving the slot silent. The conversion is a caveat-region flag day and is written up in
`docs/PI-DISPOSITION.md`.

## Cost note (why one member and not 57)

`manifestAdmitted` recomputes `forcedCols` — a `flatMap refs2` over all 302 constraints — once per
declaration. The facts about this member's concrete descriptor are checked by compiled evaluation
(`native_decide`; ember, 2026-11-06: concrete data by the compiler, general theorems by the kernel);
elaborator `decide` over them peaked this module at 14.6 GB. Routing the whole registry through
the gate belongs with the emit that regenerates the registry, not here.

## Axiom hygiene

The concrete facts rest on their own `<theorem>._native.native_decide.ax_1_1`, and
`turn_hash_slot_admits_any_value` inherits `burnDecl_admitted`'s; all are pinned with
`#assert_compiled`.
-/
import Dregg2.Circuit.Emit.PiDeclaration
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.PiDeclarationDeployed

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.PiDeclaration
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (v3Registry)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-- The deployed burn member, resolved by KEY out of the registry the emit produces. (A display
name is not a key — `reference-a-display-name-is-not-a-key`; the fallback is the empty descriptor,
which has `piCount = 0` and would make every claim below FAIL rather than pass vacuously.) -/
def burnM : EffectVmDescriptor2 :=
  (v3Registry.lookup "burnVmDescriptor2R24").getD
    { name := "MISSING-burnVmDescriptor2R24", traceWidth := 0, piCount := 0, tables := []
    , constraints := [], hashSites := [], ranges := [] }

/-- Non-vacuity: the lookup RESOLVED. Without this the manifest below could be admitted against
the empty fallback (`piCount = 0` makes `piSlotsCovered` trivially true), which is the shape a
registry rename would silently produce. -/
theorem burnM_resolved : burnM.piCount = 43 ∧ burnM.constraints.length = 308 := by native_decide

/-! ### The reasons, in one place.

Each is a claim about WHY a binding is not wanted, and each is checkable by a reader against the
code it names. Three distinct kinds appear, and the difference matters:

* **VERIFIER-SUPPLIED COMPARAND** — the verifier CHOOSES the value and hands it to the proof
  (block height, the per-cell caps). Binding it to the trace would be circular; the check that
  matters is off-AIR and is named.
* **RETIRED** — the effect that fed the slot no longer exists. The slot is a zero sentinel the PI
  layout has not yet compacted away. These are the ones that should be DELETED, and the reason
  says so; they are transcript-only only until the layout compaction lane runs.
* **CARRIED BY A WIDER BINDING** — the value IS forced, at a different width or a different slot,
  and this slot is a narrower shadow. -/

-- ⚑ FOUR REASONS WERE DELETED HERE ON 2026-08-07, WITH THE SLOTS THEY EXPLAINED.
-- `rVerifierHeight` (26 CURRENT_BLOCK_HEIGHT), `rCustomCaps` (27 MAX_CUSTOM_EFFECTS),
-- `rCustomCount` (28 CUSTOM_EFFECT_COUNT) and `rApprovedHandoffs` (29..32 APPROVED_HANDOFFS)
-- are gone because their slots are: `docs/PI-DISPOSITION.md` §6 is the removal. The last of
-- them said in so many words "This slot should be DELETED, not bound — it is case (b) of the
-- disposition question, and the reason is here so the compaction lane can find it." It did.
-- The live temporal binding is the rotated `COMMITTED_HEIGHT` pin below, which is bound on
-- every member and overridden by the verifier from the trusted committed state; the custom-proof
-- entry count is now DERIVED from the PI vector's own length (`pi::custom_entry_count`) rather
-- than read out of a felt the prover wrote.

private def rNetDelta : String :=
  "CARRIED BY A WIDER BINDING: the net balance delta is recomputable from the balance limbs, and \
   INIT_BAL_LO/HI and FINAL_BAL_LO/HI are all four pinned on this member (PI 20..23 -> cols \
   54/55/76/77). A verifier that wants the delta subtracts the bound limbs; this slot is a \
   narrower shadow of a binding that already holds."

private def rCommitLane : String :=
  "CARRIED BY A WIDER BINDING: lane 0 of the 8-felt commitment is pinned (PI 0 -> col 66 / PI 8 -> \
   col 88, the rotated state_commit carriers). Lanes 1..7 ride the WIDE 16-pin tail on the wide \
   registry member; on this narrow member they are not published-and-forced, and the executor's \
   anchoring loop supplies them."

private def rEffectsHash : String :=
  "NOT ANCHORED AT ANY WIDTH ON THIS MEMBER — and pi.rs says so at BURN_TARGET_PI: the only \
   carrier the burn target reaches is compute_effects_hash, and the deployed descriptor binds \
   none of PI[EFFECTS_HASH_BASE..+4]. Declared transcript-only because that is the TRUE state, \
   not because it is the right one. Whoever anchors this must anchor the 8 limbs."

private def rEffectsGlobal : String :=
  "CARRIED BY A WIDER BINDING, IN ANOTHER DESCRIPTOR (corrected 2026-08-07): the whole-call_forest \
   effects hash is a turn-level value no per-cell trace can see, so no pin on THIS member can reach \
   it. But it is not unread. PI 30..33 are sched::EFFECTS_HASH_GLOBAL inside the 49-felt \
   bilateral-schedule contract window inner_pi[26,75) \
   (bilateral_aggregation_air::SCHEDULE_PI_BASE = TURN_HASH_BASE = 26; the window was [33,82) \
   until the 2026-08-07 seven-slot compaction slid it down INTACT — which is precisely why those \
   seven were removable and these four were not), which \
   schedule_block_from_inner_pi projects into the deployed dregg-bilateral-aggregation-v3 at cols \
   4..7, where four window_gate transitions hold them equal on every row and a piBinding pins them \
   first AND last to that descriptor's outer PI[4..7] (EffectVmEmitBilateralAgg.turnIdBindings). \
   The column is FORCED, so that pin survives dropUnforcedPins. This reason previously read \
   'nothing binds it to the turn; gamma.1 was to make this algebraic and did not land' -- the \
   agreement half DID land, in the aggregation; what still does not exist is a binding of the \
   published value to the turn's RECOMPUTED effects hash. Do not read this slot as deletable: \
   docs/PI-DISPOSITION.md section 6 retracts exactly that."

private def rTurnHash : String :=
  "UNDER PROTEST — this one wants to be .bound and cannot be yet. There is no trace carrier for \
   the turn hash anywhere in the rotated geometry, so .bound has no column to name. MEASURED: six \
   producers fill this 4-felt slot with three different conventions (four felts in \
   turn-prover/src/proven_receipt.rs:127, ONE felt in turn-prover/src/rotation_witness.rs:166 and \
   circuit-prove/src/joint_turn_aggregation.rs, none at all on the sdk full_turn_proof production \
   path) and rotation_witness.rs's own comment relies on the absence: 'the EffectVm AIRs do not \
   constrain TURN_HASH, so overriding the carried prefix slot and proving against the edited PI \
   yields a still-valid proof binding the chosen id'. See docs/PI-DISPOSITION.md."

/-! ### The manifest. -/

/-- Every published slot of `burnVmDescriptor2R24`, dispositioned. 15 bound, 28 transcript-only. -/
def burnDecl : PiManifest :=
  -- OLD_COMMIT[0..8] — lane 0 pinned to the rotated BEFORE state_commit carrier.
  [ ⟨0, "OLD_COMMIT[0]", .bound .first 66⟩ ]
  ++ ((List.range 7).map fun i => ⟨1 + i, s!"OLD_COMMIT[{1 + i}]", .transcriptOnly rCommitLane⟩)
  -- NEW_COMMIT[0..8] — lane 0 pinned to the rotated AFTER state_commit carrier.
  ++ [ ⟨8, "NEW_COMMIT[0]", .bound .last 88⟩ ]
  ++ ((List.range 7).map fun i => ⟨9 + i, s!"NEW_COMMIT[{1 + i}]", .transcriptOnly rCommitLane⟩)
  -- EFFECTS_HASH[0..4] — anchored at no width on this member.
  ++ ((List.range 4).map fun i => ⟨16 + i, s!"EFFECTS_HASH[{i}]", .transcriptOnly rEffectsHash⟩)
  -- the four balance limbs — all bound.
  ++ [ ⟨20, "INIT_BAL_LO", .bound .first 54⟩
     , ⟨21, "INIT_BAL_HI", .bound .first 55⟩
     , ⟨22, "FINAL_BAL_LO", .bound .last 76⟩
     , ⟨23, "FINAL_BAL_HI", .bound .last 77⟩
     , ⟨24, "NET_DELTA_MAG", .transcriptOnly rNetDelta⟩
     , ⟨25, "NET_DELTA_SIGN", .transcriptOnly rNetDelta⟩ ]
  -- 26..32 (CURRENT_BLOCK_HEIGHT · MAX_CUSTOM_EFFECTS · CUSTOM_EFFECT_COUNT ·
  -- APPROVED_HANDOFFS[4]) NO LONGER EXIST — deleted 2026-08-07, so TURN_HASH starts at 26.
  ++ ((List.range 4).map fun i => ⟨26 + i, s!"TURN_HASH[{i}]", .transcriptOnly rTurnHash⟩)
  ++ ((List.range 4).map fun i =>
        ⟨30 + i, s!"EFFECTS_HASH_GLOBAL[{i}]", .transcriptOnly rEffectsGlobal⟩)
  ++ [ ⟨34, "ACTOR_NONCE", .bound .first 56⟩
     -- the four appended ROTATED pins.
     , ⟨35, "rot::OLD_COMMIT", .bound .first 385⟩
     , ⟨36, "rot::NEW_COMMIT", .bound .last 648⟩
     , ⟨37, "rot::COMMITTED_HEIGHT", .bound .last 482⟩
     , ⟨38, "rot::CAVEAT_COMMIT", .bound .last 758⟩
     -- the dsl route-commitment quartet: FORCED since the rc-FOLD flag day (absorbed into the
     -- published caveat commitment), which is why these four survive `dropUnforcedPins`.
     , ⟨39, "dsl::RC[0]", .bound .last 753⟩
     , ⟨40, "dsl::RC[1]", .bound .last 754⟩
     , ⟨41, "dsl::RC[2]", .bound .last 755⟩
     , ⟨42, "dsl::RC[3]", .bound .last 756⟩ ]

/-- ⚑ **THE ADOPTION.** The gate accepts the deployed member under this declaration — so the
mechanism is applied to a real emitted object, not only to a fixture. Every `.bound` entry below
was CHECKED against the descriptor's own constraint list and against `forcedCols`. -/
theorem burnDecl_admitted : manifestAdmitted burnM burnDecl = true := by native_decide

/-- The descriptor, routed through the gate. `withPiManifest_eq` makes this `rfl`-equal to the
member the registry already carries: adopting the gate moves no emitted byte. -/
def burnMDeclared : EffectVmDescriptor2 :=
  withPiManifest burnM burnDecl burnDecl_admitted

theorem burnMDeclared_eq : burnMDeclared = burnM := rfl

/-! ### What the declaration now lets the tree SAY. -/

/-- The producer's obligations, DERIVED — 15 `(slot, row, column)` triples. This is the fourth
source of the four-source problem replaced by a projection of the first. -/
theorem burnDecl_producer_obligations_count :
    (producerObligations burnDecl).length = 15 := by native_decide

/-- The transcript-only class, counted and REPORTED rather than silently permitted. -/
theorem burnDecl_transcript_only_count :
    (transcriptOnlySlots burnDecl).length = 28 := by native_decide

/-- Every transcript-only entry carries a non-empty reason. (`declAdmitted` already forces this;
stated separately so the count above cannot be met by 28 empty strings.) -/
theorem burnDecl_reasons_are_written :
    (transcriptOnlySlots burnDecl).all (fun e => !e.2.2.isEmpty) = true := by native_decide

/-- 15 + 28 = 43: the two classes PARTITION what this member publishes, with no residual. -/
theorem burnDecl_partitions :
    (producerObligations burnDecl).length + (transcriptOnlySlots burnDecl).length
      = burnM.piCount := by native_decide

/-- ⚑ **`TURN_HASH` is in the transcript-only class, by name.** The one fact this whole lane is
about, stated where it cannot be lost: on the deployed burn member, the four felts a stranger
would read to learn WHICH TURN THIS IS are read by no constraint. -/
theorem turn_hash_is_transcript_only :
    ((transcriptOnlySlots burnDecl).map (fun e => e.1)).filter
        (fun k => k == 26 || k == 27 || k == 28 || k == 29)
      = [26, 27, 28, 29] := by native_decide

/-- …and therefore the AIR admits ANY value in `PI[26]` — the machine-checked cost of the class,
instantiated on a deployed member. -/
theorem turn_hash_slot_admits_any_value (hash : List ℤ → ℤ) (v : ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash burnM minit mfin maddrs t) :
    Satisfied2 hash burnM minit mfin maddrs { t with pub := setPubAt t.pub 26 v } :=
  transcriptOnly_admits_any_value (slot := "TURN_HASH[0]") (reason := rTurnHash) hash v
    burnDecl_admitted (by decide) h

#assert_compiled burnM_resolved
#assert_compiled burnDecl_admitted
#assert_compiled burnDecl_producer_obligations_count
#assert_compiled burnDecl_transcript_only_count
#assert_compiled burnDecl_reasons_are_written
#assert_compiled burnDecl_partitions
#assert_compiled turn_hash_is_transcript_only
#assert_compiled turn_hash_slot_admits_any_value

end Dregg2.Circuit.Emit.PiDeclarationDeployed
