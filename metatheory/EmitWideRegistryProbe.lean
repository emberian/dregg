/-
# EmitWideRegistryProbe — ADDITIVE full wide-registry descriptor emit (STAGED slice 2).

Prints ONE TSV line per WIDE member, in the EXACT order + key set of the live `V3_STAGED_REGISTRY_TSV`
(`EmitRotationV3.lean`), so the wide registry is a member-for-member, name-stable COVER of the live V3
registry (57 members):

  `<live key>\t<member.name>\t<emitVmJson2 (wide member)>`

Each wide member is the proven `wideAppend host bb (bb + B_SPAN)` of the corresponding live descriptor — the
two 13×8 BEFORE/AFTER carriers + the 16 wide commit PIs (the 8-felt ~124-bit before/after anchors)
appended past the host, NO narrowing. The emit order is the live order:

  * positions 0..44 — `v3RegistryCapOpenWide` (the 45 emit-source members, §9);
  * position 45 — `transferCapOpenTBVmDescriptor2R24` (the turn-identity-pinned transfer cap-open),
                  wide-wrapped at its transfer FACE base;
  * position 46 — `heapWriteVmDescriptor2R24` (the Class-A sorted-Merkle splice), wide-wrapped at its
                  heap-splice FACE base;
  * positions 47..55 — the WRITE-bearing cap-open tail (`v3RegistryCapOpenWriteWide`, §10) MINUS
                  `grantCapWriteCapOpen` (NOT a live `V3_STAGED_REGISTRY_TSV` member — reconciled out);
  * position 56 — `supplyMintVmDescriptor2R24` (the dedicated `sel.MINT` mint), wide-wrapped at its
                  mint FACE base.

This is the byte source of the ADDITIVE Rust artifact `circuit/descriptors/rotation-wide-registry-
staged.tsv` the per-family wide-roundtrip slice consumes — NOTHING on the live 1-felt wire path changes
(`v3RegistryCapOpen` / the live TSV / FP / VK are UNTOUCHED).

⚑ This paragraph used to end "The wide transfer single-line TSV (`EmitWideTransferProbe.lean`) stays
beside this, byte-identical (row 0)." That had stopped being true: row 0 took the availability
hardening, the two membership-claim PIs, the gentian capacity-floor refuse weld and the E1
compaction, while the single-line probe took none of them — 1782 cols / 68 PIs here against 1819 / 66
there, with 560 of the probe's 619 constraints appearing nowhere in row 0. The probe, its driver
`EmitWideTransferProbe.lean`, its Rust const and its producer were DELETED on 2026-07-31; it had no
production consumer, and its two tests were the only prove+verify roundtrip and the only 8-felt
collision tooth for transfer — both aimed at a member no verifier resolves.

SCRATCH executable: `lake env lean --run EmitWideRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.CapOpenTurnPins
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.HeapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit
import Dregg2.Circuit.Emit.ExactFieldsRefusalEmit
import Dregg2.Circuit.Emit.AccumulatorInsertEmit
import Dregg2.Circuit.Emit.CarrierComposed
import Dregg2.Circuit.Emit.AvailWideMembers
import Dregg2.Circuit.Emit.AvailWideFeeMember
import Dregg2.Circuit.RotatedKernelRefinementExercise
-- THE GENTIAN DEPLOYED-DEFAULT FLIP: the capacity-floor refuse, lifted to ride the WIDE bare cohort
-- (aux blocks PAST the wide member width — past the two 13×8 wide carriers). Welded onto exactly the
-- 36 bare cohort members (the settle-as-transfer/burn dodge routes), mirroring the V3 `v3RegistryRefused
-- ++ drop 36`. See Dregg2.Deos.BareCohortFloorRefuseWide.declared_capacity_unsat_wide.
import Dregg2.Deos.BareCohortFloorRefuseWide
-- THE S2 DELETION (Epoch 1): every emitted wide member is compacted through the verified
-- `compactS2` (the two rotated 1-felt MD chains dropped, 992 columns removed), gated per member
-- by the decidable `compactOk` bundle — the emit FAILS CLOSED if any member's S2 stratum is not
-- the expected dead pair of chains. `s2compact` companion lines carry the (bb, laneBase) geometry
-- to the Rust producer table (`s2_compact_generated.rs`).
import Dregg2.Circuit.Emit.WideCompactTable
-- THE E1 DELETION (Epoch-1 SECOND flag-day): each S2-compact member is ADDITIONALLY compacted at
-- its DERIVED per-member kill-set (`deadColsE1 … 90` — every column at index ≥ 90 referenced by no
-- surviving constraint / hash site / range: the retired v1-face aux band 90..187, the gentian
-- refuse tail, the appendix scratch bands). Gated per member by `compactE1Ok` (fail-closed); the
-- keystone re-connects through `RotWideCompactE1.compactE1_expand`. `e1compact` companion lines
-- carry the kill-set (POST-S2 coords, as half-open runs) to the Rust producer table
-- (`e1_compact_generated.rs`).
import Dregg2.Circuit.Emit.RotWideCompactE1
-- THE UNFORCED-PIN SUBTRACTION: drop every `.piBinding` whose column nothing else reads (the pins
-- where the prover chooses BOTH sides). Proved a weakening + a no-op + a fixpoint.
import Dregg2.Circuit.Emit.UnforcedPiPins
-- THE LAST-ROW ANCHOR FORGE CLOSURE (flag day): every emitted member's row-local `gate` bodies are
-- lifted OFF the transition domain onto the WHOLE domain (`windowGate … onTransition := false`), so
-- the LAST row — the row every member pins its published 8-felt AFTER anchor on — carries algebra.
-- Applied LAST, after S2 + E1, so it is column-index-preserving: widths, PI counts and both
-- compaction kill-sets are untouched, and the `s2compact`/`e1compact` companion lines do not move.
-- See Dregg2.Circuit.Emit.LastRowFrameHardening.{satisfied2_of_hardened, hardened_gate_binds_on_last_row}.
import Dregg2.Circuit.Emit.LastRowFrameHardening
import Dregg2.Circuit.Emit.FieldsCanonicity9Emit
-- ⚑ THE OWNER FREEZE (E10) — see `emitCompact` below and `OwnerFreezeWire`'s header.
import Dregg2.Circuit.Emit.KeyCanonicity9Emit
import Dregg2.Circuit.Emit.OwnerFreezeWire
import Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide v3RegistryCapOpenWriteWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (withDfaRcPins B_SPAN)

/-- The 36 bare cohort keys (the settle-as-transfer/burn dodge routes) — the members the WIDE flag-day
refuse is welded onto, mirroring the V3 `v3RegistryRefused`. The cap-open tail / write / satisfaction /
supplyMint members are NOT bare routes and are left unwelded. -/
def bareCohortKeys : List String :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3RegistryBare.map (·.1)

/-- Weld the WIDE capacity-floor refuse onto a wide member IFF its key is a bare cohort route. A
non-cohort key (cap-open / write / supplyMint / satisfaction) is returned untouched. -/
def weldWide (key : String) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  if bareCohortKeys.contains key then
    Dregg2.Deos.BareCohortFloorRefuseWide.gentianWideBareRefuse d
  else d

/-- The E1 face ceiling for the wide members (`AUX_BASE = 90`): strictly above every `.transition`
face column (`sbCol`/`saCol` ≤ 89), matching `RotatedKernelRefinementAvailWideCompactE1.E1_FLOOR`. -/
def e1Floor : Nat := 90

/-- Compress a strictly-ascending column list into ascending half-open runs `[start, end)`.
`deadColsE1` returns a filtered `List.range`, so its output is already sorted ascending, no dups. -/
def runsOf (cols : List Nat) : List (Nat × Nat) :=
  (cols.foldl (fun (acc : List (Nat × Nat)) (c : Nat) =>
    match acc with
    | (s, e) :: rest => if c == e then (s, e + 1) :: rest else (c, c + 1) :: (s, e) :: rest
    | [] => [(c, c + 1)]) []).reverse

/-- The `e1compact` companion payload: the per-member E1 kill-set as ascending half-open `start-end`
runs (POST-S2 coordinates), for the Rust producer table (`e1_compact_generated.rs`). -/
def intervalsStr (cols : List Nat) : String :=
  String.intercalate "," ((runsOf cols).map (fun p => s!"{p.1}-{p.2}"))

/-- `deadColsE1 cm 90`, with `liveCols` HOISTED out of the per-column filter closure. The proven
`deadColsE1` inlines `liveCols M` INSIDE the predicate, so the interpreter (`lake env lean --run`)
rebuilds the whole live-reference surface once PER COLUMN (~width× redundant, ~1 min/member). This
binds `live` once and computes the DEFINITIONALLY-IDENTICAL list — the descriptor / companion line
are byte-identical to the `deadColsE1`-based path, just fast. -/
def deadColsE1Fast (cm : EffectVmDescriptor2) (ceiling : Nat) : List Nat :=
  let live := Dregg2.Circuit.Emit.RotWideCompactE1.liveCols cm
  (List.range ceiling).filter (fun c => decide (e1Floor ≤ c) && !live.contains c)

/-- The E1 kill-set CEILING for a wide member's S2-compacted `cm` at `key`: the pre-gentian column
count, i.e. `cm.traceWidth` MINUS the gentian floor-refuse weld aux block (`3·REFUSE_STRIDE`) IFF the
member is a bare-cohort route (the ones `weldWide` welds). The gentian aux columns ride the very TOP
of `cm` (`gentianWideBareRefuse` bases them at the pre-weld `traceWidth`, so after S2 they sit at
`[cm.traceWidth − 3·REFUSE_STRIDE, cm.traceWidth)`), and they are NOT emitted by the Rust wide
producer — they are filled at PROVE time (`bare_floor_refuse_weld::fill_refuse_aux`, after the
producer's `compact_s2`/`compact_e1`). So the E1 kill-set must NOT reach into them: the producer runs
`compact_e1` on the PRE-gentian S2-compacted trace, so an E1 interval at index ≥ the producer width
is unrealizable (the row is too short → the deployed producer panics). Excluding the block keeps the
kill-set exactly the host-region dead v1-face / appendix bands `deadColsE1` is proven value-preserving
over, and leaves the gentian weld a COMPLETE block (`refuse_weld_widen` recovers it, `fill_refuse_aux`
fills it) — the E1-then-gentian composition the deployed `compact_e1`→`fill_refuse_aux` path realizes.
Non-welded members (cap-open / write / supplyMint) carry no gentian, so the ceiling is the full width. -/
def e1Ceiling (key : String) (cm : EffectVmDescriptor2) : Nat :=
  if bareCohortKeys.contains key then
    cm.traceWidth - 3 * Dregg2.Deos.BareCohortFloorRefuseDeployed.REFUSE_STRIDE
  else cm.traceWidth

/-- Compact-and-print one wide member (S2 deleted, then E1 deleted, both gated), plus its
`s2compact` (bb, laneBase) geometry line and its `e1compact` kill-set line for the Rust producer
tables. Fails the whole emit if `compactOk` (S2) refuses, or if the cheap `transitionCeilingOk`
(the only member-specific E1 obligation — every `.transition` face column below 90) fails: by
`RotWideCompactE1.compactE1Ok_of_ceiling` the derived kill-set then passes the full value-preservation
gate, so `compactE1 cm ks` is value-preserving (the `compactE1_expand` bridge holds; the emitted `ks`
is a SUBSET of `deadColsE1 cm 90` — capped at `e1Ceiling` to exclude the prove-time gentian aux block
— and a subset of a `compactE1Ok`-valid pure-dead kill-set stays `compactE1Ok`-valid). The emitted
member is then the GENTIAN weld of the proof object
`RotatedKernelRefinementAvailWideCompactE1.transferWideDeployedE1` (the pre-gentian E1 row), peeled by
`BareCohortFloorRefuseWide.satisfied2_of_gentianDeployedBareRefuse` — matching the deployed producer,
whose `compact_e1` runs on the pre-gentian trace and whose `fill_refuse_aux` adds the gentian at prove
time. -/
def emitCompact (key : String) (d0 : EffectVmDescriptor2) : IO Unit := do
  -- ⚑ THE FIELDS-CANONICITY WELD, applied to the UNCOMPACTED member so the S2/E1 compactions see
  -- its 112 aux columns as LIVE and renumber them with everything else. Emitting it after
  -- compaction would name pre-compaction column indices — the avail-shift trap, one level up.
  -- ⚑ THE OWNER FREEZE (E10), applied at the SAME point and for the same reason: the eight
  -- BEFORE↔AFTER `B_PUBKEY_OCTET` welds must name UNCOMPACTED block columns so S2/E1 renumber them
  -- with everything else. The wide registry is a member-for-member cover of live V3 and its
  -- fingerprint is half the VK's `registry_fp` (`dregg-epoch/src/lib.rs:155`), so welding only the
  -- narrow registry would leave the identical owner-forgery route open through the wide cover.
  -- ⚠ UNRUN as authored (2026-08-01): `EffectVmEmitRotationWide.lean` was RED mid-187-widening
  -- (`wideAppend_pins` / `v3RegistryWide_binds` axiom-hygiene FAIL), so this emitter could not be
  -- elaborated, let alone executed. Structurally it can only ADD live columns, never remove them,
  -- so the S2 kill-set can only shrink and `transitionCeilingOk` is untouched (the weld is a
  -- `.base (.gate …)`, not a `.transition`) — and if that reasoning is wrong the emit FAILS CLOSED
  -- with `compactForEmit`'s refusal rather than minting bad bytes. CHECK THIS LINE FIRST if the
  -- wide regen refuses.
  let d := Dregg2.Circuit.Emit.OwnerFreezeWire.ownerFreezeWire d0
  -- ⚑ THE KEY-CANONICITY WELD (2026-08-02), applied at the SAME point and for the same reason: the
  -- nine `CanonicalKey9` range lookups must name UNCOMPACTED block columns so S2/E1 renumber them
  -- with everything else. Additive lookups only — no gate, no column, no PI — so the S2 kill-set
  -- can only shrink and `transitionCeilingOk` is untouched. Welding only the narrow registry would
  -- leave the identical out-of-image nonet admissible through the wide cover, whose fingerprint is
  -- half the VK's `registry_fp`.
  let d := Dregg2.Circuit.Emit.KeyCanonicity9Emit.keyCanonical9Wire d
  let d := Dregg2.Circuit.Emit.FieldsCanonicity9Emit.fieldsCanonical9Wire d
  match Dregg2.Circuit.Emit.WideCompactTable.compactForEmit key d with
  | .ok (cm, bb, lb) =>
    let ks := deadColsE1Fast cm (e1Ceiling key cm)
    if Dregg2.Circuit.Emit.RotWideCompactE1.transitionCeilingOk cm e1Floor then
      let e1cm := Dregg2.Circuit.Emit.RotWideCompactE1.compactE1 cm ks
      -- THE LAST-ROW HARDENING, applied to the FINAL emitted object: `hardenLastRow` preserves
      -- `traceWidth`, `piCount`, `tables`, `hashSites`, `ranges` and the constraint ORDER
      -- definitionally, so it commutes with everything above it and changes only which DOMAIN each
      -- `gate` body is asserted on. The existing keystone chain re-connects through
      -- `satisfied2_of_hardened` (a hardened witness IS an `e1cm` witness).
      let hardened := Dregg2.Circuit.Emit.LastRowFrameHardening.hardenLastRow e1cm
      -- THE UNFORCED-PIN SUBTRACTION (`UnforcedPiPins.dropUnforcedPins`), applied OUTERMOST so it
      -- sees the final constraint set. It removes exactly the `.piBinding`s whose column no other
      -- constraint / hash site / range tooth reads — the pins where the prover chooses both sides.
      -- `satisfied2_dropUnforcedPins` makes it a weakening (the keystone chain re-connects
      -- verbatim), `unforced_pin_row_admits_any_value` proves the removed pins refused nothing,
      -- and `unforcedPins_dropUnforcedPins` makes the post-emit census zero BY THEOREM.
      -- `piCount` is untouched: the slots survive as the verifier inputs they always were.
      let pinned := Dregg2.Circuit.Emit.UnforcedPiPins.dropUnforcedPins hardened
      IO.println s!"{key}\t{pinned.name}\t{emitVmJson2 pinned}"
      IO.println s!"s2compact\t{key}\t{bb}\t{lb}"
      IO.println s!"e1compact\t{key}\t{intervalsStr ks}"
    else throw (IO.userError
      s!"E1-compact REFUSED for {key} — transitionCeilingOk failed (a `.transition` reads a face \
         column ≥ 90, so the derived kill-set could corrupt an offset-encoded transition); the \
         emit fails closed")
  | .error e => throw (IO.userError e)

def main : IO Unit := do
  -- positions 0..44: the 45 emit-source wide members (`v3RegistryCapOpenWide`), keyed by the live
  -- registry key (`burnVmDescriptor2R24` etc., `#guard`-proven name-stable with `v3RegistryCapOpen`).
  -- EXACT V2 FIELDS EPOCH: position 7 (`refusalVmDescriptor2R24`) is replaced in place by the
  -- FLD2/FLN2 state16 update.  The 32-byte audit is published as sixteen exact u16 PIs and opened at
  -- raw key 2^32 over one shared before/after path.  No modularly-folded scalar map-op remains.
  for (key, d) in v3RegistryCapOpenWide do
    if key == "refusalVmDescriptor2R24" then
      emitCompact key (weldWide key
        Dregg2.Circuit.Emit.ExactFieldsRefusalEmit.refusalExactFieldsWide)
    -- §J′ (INSERT-shaped accumulator deploy): positions 3/4/22 (noteSpend/noteCreate/createCell) are
    -- REPLACED IN PLACE by the insert-shaped `effAccumInsertV3 … base …` host (EXACTLY as refusal is
    -- advanced to `effFieldsWriteV3`, heap to `effHeapWriteV3`, cap to `effCapOpenWriteV3`). The DEPLOYED
    -- accumulator descriptor's `Satisfied2` TRACE-FORCES the spliced-leaf membership in the REBUILT AFTER
    -- tree over the full ~124-bit BEFORE/AFTER accumulator-root groups
    -- (`AccumulatorInsertEmit.effAccumInsertV3_forces_write8`), over the GENUINE sorted fresh-key insert
    -- (NOT the non-fitting update-at-key shape) — NEVER the lane-0 squeeze the map_op-only host leaves.
    -- The wide member stays keyed by its live registry key (member count UNCHANGED at 57); only the host
    -- (name + width) grows by the heap-open READ appendix. `bb` is each accumulator's v1 FACE width (the
    -- SAME `bb` `v3RegistryWideBB` uses), aligning the wide AFTER carrier's committed accumulator-root
    -- block with the rotated AFTER block the read appendix welds to.
    else if key == "noteSpendVmDescriptor2R24" then
      -- rc-EMIT FIX (all three §J′ inserts): the insert host rides `withDfaRcPins` — the trio's
      -- committed rows dropped the 4 rc PIs the live members + producer carry (63 ≠ 67).
      let nsHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
        (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
        "dregg-effectvm-noteSpend-v1-rot24-v3-insert-heapopen")
      let nsBB := Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptor.traceWidth
      let nsWide := wideAppend nsHost nsBB (nsBB + B_SPAN)
      emitCompact key (weldWide key nsWide)
    else if key == "noteCreateVmDescriptor2R24" then
      let ncHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
        "dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen")
      let ncBB := Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.noteCreateVmDescriptor.traceWidth
      let ncWide := wideAppend ncHost ncBB (ncBB + B_SPAN)
      emitCompact key (weldWide key ncWide)
    else if key == "createCellVmDescriptor2R24" then
      let ccHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
        "dregg-effectvm-createCell-v1-rot24-v3-insert-heapopen")
      let ccBB := Dregg2.Circuit.Emit.EffectVmEmitCreateCell.createCellActorVmDescriptor.traceWidth
      let ccWide := wideAppend ccHost ccBB (ccBB + B_SPAN)
      emitCompact key (weldWide key ccWide)
    -- THE v12 BIG-BANG IN-PLACE REPLACEMENTS (the refusal precedent): the sovereign + transfer
    -- rows advance to the DEPLOYED teeth-exposing members under their LIVE keys (member count
    -- UNCHANGED at 57; the narrow live TSV / FP / VK untouched — the wide slice is the fold lane).
    else if key == "makeSovereignVmDescriptor2R24" then
      -- The DEPLOYED wide sovereign (`CarrierComposed.makeSovereignV3DeployedWide`): rc + the 4
      -- KEY_COMMIT teeth PI pins (51..54 = `SOVEREIGN_KEY_COMMIT_PI_LO`, cols 113..=116) AHEAD of
      -- the 16 wide anchors (55..70) + the in-AIR KEY_COMMIT chip gate (digest appendix at the
      -- wide end, dgBase 2683; width 2715). piCount 67 → 71.
      let msWide := Dregg2.Circuit.Emit.CarrierComposed.makeSovereignV3DeployedWide
      emitCompact key (weldWide key msWide)
    else if key == "transferVmDescriptor2R24" then
      -- AVAILABILITY RETARGET (the wide-transfer wrap-forgery closure): the wide membership-teeth
      -- transfer REBUILT over the §11.7 borrow-weld face (`AvailWideMembers.
      -- transferV3MembershipAvailWide` — teeth PIs 50..51 UNCHANGED, rc pins at the avail-shifted
      -- carrier, teeth cols 2693..2694 past the avail carriers; width 2695, piCount 61). The
      -- capacity-floor refuse rides the AVAIL caveat base (`cavBaseOf AVAIL_WIDTH = 676` — the
      -- fixed-base `gentianWideBareRefuse` would decode the WRONG columns on the widened face),
      -- i.e. the committed row is `AvailWideMembers.transferAvailWideRefused`, whose availability
      -- discharge + refuse teeth are proven (`RotatedKernelRefinementAvailWide`,
      -- `declared_*_unsat_availWideRefused`). PI-EXPOSURE leg only (the FOLD edge binds).
      let trWide := Dregg2.Circuit.Emit.AvailWideMembers.transferAvailWideRefused
      emitCompact key trWide
    else if key == "burnVmDescriptor2R24" then
      -- AVAILABILITY RETARGET, the WIDE-BURN twin (the LAST wrap-class member): the crown burn
      -- host rebuilt over the §8¾ borrow-weld face (`AvailWideMembers.burnV3AvailWide` — 66 PIs
      -- UNCHANGED, burn carries no membership teeth; rc pins at the burn-avail-shifted carrier;
      -- width 2683 → 2691). The capacity-floor refuse rides the burn AVAIL caveat base
      -- (`cavBaseOf 196 = 690` — the fixed-base `gentianWideBareRefuse` would decode the WRONG
      -- columns on the widened face), i.e. the committed row is
      -- `AvailWideMembers.burnAvailWideRefused`, whose availability discharge + refuse teeth are
      -- proven (`RotatedKernelRefinementMintBurnAvailWide`,
      -- `declared_*_unsat_burnAvailWideRefused`).
      let buWide := Dregg2.Circuit.Emit.AvailWideMembers.burnAvailWideRefused
      emitCompact key buWide
    else if key == "transferCapOpenEffVmDescriptor2R24" then
      -- AVAILABILITY RETARGET, the WIDE-CAP-OPEN-EFF twin: the live cap-open EFF crown host
      -- (position 42) rebuilt over the §11.7 borrow-weld face
      -- (`AvailWideMembers.transferCapOpenEffAvailWide` = the already-flipped narrow
      -- `transferCapOpenEffV3Avail` wide-appended at the AVAIL face base 198; width 2030 → 3022,
      -- 46 + 16 PIs). NOT a bare cohort route, so no capacity-floor refuse (`weldWide` is the
      -- identity on this key). Availability discharge + authority-intact keystones proven
      -- (`RotatedKernelRefinementCapOpenAvailWide`,
      -- `wideCapOpenEff_availability_and_exact_move_forced` / `wideCapOpenEffAvail_authorizes`).
      let ceWide := Dregg2.Circuit.Emit.AvailWideMembers.transferCapOpenEffAvailWide
      emitCompact key ceWide
    else if key == "transferFeeVmDescriptor2R24" then
      -- AVAILABILITY RETARGET, the WIDE-FEE twin: the fee'd-transfer crown host (tail position
      -- 44, the LIVE SOVEREIGN transfer's effect-vm leg) rebuilt over the §11.8 fee availability
      -- face (`AvailWideFeeMember.transferFeeAvailWide` = the already-flipped narrow
      -- `transferFeeV3AvailWire` — v3OfFrozenFeeWide + rc pins, the deployed fee member's
      -- wrapper shape — wide-appended at the FEE avail face base 204; width 2683 → 2699, the
      -- 67-PI layout UNCHANGED: 46 base + fee pin 46 + rc 47..50 + 16 anchors). NOT a bare
      -- cohort route, so no capacity-floor refuse (`weldWide` is the identity on this key).
      -- The fee availability discharge (BOTH debit legs) + wrap-forgery teeth are proven
      -- (`RotatedKernelRefinementFeeAvailWide`, `wideFee_availability_and_exact_move_forced` /
      -- `wideFee_{fee,amount}_forgery_unsat`).
      let feeWide := Dregg2.Circuit.Emit.AvailWideFeeMember.transferFeeAvailWide
      emitCompact key feeWide
    else if key == "customVmDescriptor2R24" then
      -- DELIVER #1 — THE APP-ROOT WELD LEG-EMIT (the VK epoch): the wide custom member additionally
      -- PUBLISHES the AFTER-block `fields[0..8]` octet (`withAfterOctetPins … 4`, cols 431..438 = the
      -- custom face's after rotated block, exposed at PIs 55..62) AHEAD of the 16 wide anchors (which
      -- move to 63..78; piCount 71 → 79). The per-turn FOLD's app-root arm connects
      -- `field[field_key]` to the custom sub-proof's published root R (`field[K] == R`). `bb = 188 =
      -- EFFECT_VM_WIDTH` (the custom face base), `ab = bb + B_SPAN = 435`. `withAfterOctetPins` adds NO
      -- columns (only 8 PIs), so the custom wide `traceWidth` is UNCHANGED (a TAIL-APPEND, not a
      -- geometry widen). The refuse weld (`weldWide`) keys off `traceWidth`, so it is unaffected.
      let cuHost := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withAfterFieldsRootPins
        (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withAfterOctetPins
          (withDfaRcPins Dregg2.Circuit.Emit.EffectVmEmitRotationV3.customV3) 4)
      let cuWide := wideAppend cuHost 188 (188 + B_SPAN)
      emitCompact key (weldWide key cuWide)
    else
      emitCompact key (weldWide key d)
  -- position 45: `transferCapOpenTB` made 8-felt-wide, RETARGETED to the AVAIL base (the
  -- wide-transfer wrap-forgery closure): `effCapOpenV3TB (v3OfFrozenWide transferVmDescriptorAvail)
  -- … EFF_TRANSFER` (+2 turn-identity columns / +3 PI pins, all parametric in the base), wide-appended
  -- at the AVAIL face base (`bb = AVAIL_WIDTH = 198` — rotateV3 lays the rotated limbs at the
  -- hardened FACE width). `AvailWideMembers.tbAvailWide_row_v1` forces the hardened v1 denotation.
  let tbWide := Dregg2.Circuit.Emit.AvailWideMembers.transferCapOpenTBAvailWide
  emitCompact "transferCapOpenTBVmDescriptor2R24" tbWide
  -- position 46: `heapWrite` (the after-spine membership-forcing heap-write descriptor, OPTION I) made
  -- 8-felt-wide — EXACTLY as cap deploys `effCapOpenWriteV3`. The host is `effHeapWriteV3 heapWriteV3
  -- …-write-heapopen`: the Class-A splice base (`heapWriteV3` = graduated+rotated splice + the splice
  -- `MapOp`) WIDENED by the heap-open READ appendix + the AFTER-spine membership appendix, so the
  -- DEPLOYED descriptor's `Satisfied2` FORCES the faithful 8-felt heap-write over the full ~124-bit
  -- BEFORE/AFTER root blocks (`HeapOpenEmit.effHeapWriteV3_forces_write8`) — never the lane-0 squeeze the
  -- map_op-only path would leave. `rotateV3` lays the BEFORE limbs at the splice FACE width, so `bb =
  -- heapWriteSpliceVmDescriptor.traceWidth (= EFFECT_VM_WIDTH)`, aligning the after-spine's committed
  -- heap-root blocks (`heapRootGroupCol (EFFECT_VM_WIDTH + B_SPAN)`) with the wide AFTER rotated carrier.
  let hwBB := Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor.traceWidth
  let hwHost := Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
    Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
    "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen"
  let hwWide := wideAppend hwHost hwBB (hwBB + B_SPAN)
  emitCompact "heapWriteVmDescriptor2R24" hwWide
  -- positions 47..55: the WRITE-bearing cap-open tail (`v3RegistryCapOpenWriteWide`, §10) made
  -- 8-felt-wide, in its own order, EXCEPT `grantCapWriteCapOpen` — which is NOT a member of the live
  -- `V3_STAGED_REGISTRY_TSV`, so it is reconciled OUT to keep the wide registry a member-for-member
  -- cover of live. The remaining 9 land exactly at live positions 47..55.
  for (key, d) in v3RegistryCapOpenWriteWide do
    if key != "grantCapWriteCapOpenVmDescriptor2R24" then
      emitCompact key (weldWide key d)
  -- position 56: `supplyMint` (the dedicated `sel.MINT` mint) made 8-felt-wide. `supplyMintV3 =
  -- withSelectorGate sel.MINT (v3OfFrozen mintTickFace)`; the BEFORE limbs are laid at the mint FACE
  -- width, so `bb = mintTickFace.traceWidth` (the SAME base as the cohort `mint` member, position 2).
  let smBB := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintTickFace.traceWidth
  let smWide := wideAppend Dregg2.Circuit.Emit.EffectVmEmitRotationV3.supplyMintV3 smBB (smBB + B_SPAN)
  emitCompact "supplyMintVmDescriptor2R24" smWide
  -- position 57: the SINGLE-TICK GRAIN TURN (initiative 10). `grainTurnWide = wideAppend
  -- (withDfaRcPins grainTurnVmDescriptor2R24) bb (bb + B_SPAN)` at the 188-wide face base (the same
  -- base every setField member uses). Not a bare cohort route, so no gentian weld; the same
  -- `emitCompact` chain (owner/key/fields welds, S2, E1, last-row hardening, unforced-pin drop).
  emitCompact "grainTurnVmDescriptor2R24"
    Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated.grainTurnWide
