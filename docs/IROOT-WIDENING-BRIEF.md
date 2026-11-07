# IROOT-WIDENING-BRIEF: carry all eight lanes of the receipt root through the rotated anchors

Written 2026-11-06 by the initiative-10 lane, for ember's decision. **Not started.** This circuit
stack (BabyBear/Plonky3 rotated EffectVM) is treated as legacy by the leaf-prover decision and
today's redesign. The open question is whether this multi-day flag day is worth doing here, or
whether the binding should be carried forward in the new leaf instead.

## The wound, with its falsifier

`turn/src/rotation_witness.rs` `iroot` (l.481) returns `iroot8(receipt_hashes).limbs()[0]`. The
rotated block has ONE column for the receipt root (`B_IROOT`), so lanes 1..7 of the 8-lane
receipt root are computed and then discarded. The signed state anchor therefore binds the
receipt log at one felt: about 2^30.9 possible images, so a collision costs about 2^15.45
evaluations.

The falsifier is already in the tree:

- `turn/tests/iroot_wide_old_admits_new_rejects.rs::the_residual_is_a_live_exhibited_break_at_head`
  (l.276). It constructs two well-formed receipt logs with a byte-identical 32-byte anchor in
  64,147 evaluations.
- `the_residual_is_a_gate_not_a_note` in the same file goes red by design on the day
  `NUM_PRE_LIMBS` moves off its current value.
- The named residual is `IROOT_LANES_1_TO_7_UNABSORBED` (`rotation_witness.rs:510`). Its text is
  the cutover plan below; read it first.

## Who is exposed

Every rotated anchor exposes the receipt log at 31 bits: the sovereign/rotated
`OLD_COMMIT`/`NEW_COMMIT`, the wide 8-felt anchors (`wire_commit_8_chip`), and every R3
aggregate head. For grain sessions specifically, initiative 10 closes the binding at full width
WITHOUT this flag day:

- the bundle's executor receipts are signed and chained (`verify_receipt_chain_strict`);
- receipt `i` names manifest turn `i`;
- the last cell's `HISTORY_ROOT_SLOT` binds the receipt-hash log, and the opened head absorbs that
  slot at full width.

The 31-bit gap stays for every non-grain consumer, and for the `iroot` term itself.

## The cutover, site by site

1. **Lean geometry**
   - `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` and
     `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean`. Today the block is
     `rotatedNumPreLimbs = 187` (`B_IROOT = 187`, `B_STATE_COMMIT = B_IROOT + 1`,
     `B_SPAN = rotatedNumPreLimbs + 3 + (rotatedNumPreLimbs - 4)/3 = 251`, l.210-240 and the
     `#guard`s at l.326-337).
   - Carry ir1..ir7. `Legal.bodyAligned` (the `n ≡ 1 mod 3` carrier-count law, l.214) forces the
     extent to 196, not 195.
   - Every `#guard` on `B_SPAN`, `APPENDIX_SPAN`, `CANON9_REGION_OFF` and `CAVEAT_REGION_OFF`
     moves.
2. **Wide final chain site**
   - `metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean:217`: `carrier8 ‖ iroot ‖ 0 ‖ 0`
     at arity 11 becomes `carrier8 ‖ iroot8` at arity 16. Arity 16 is already an admitted chip
     arity.
   - Re-prove `rotV3WideSpecs_admitted`.
   - The hand-listed `bodyIns`/`carrierCols` table (`rotV3WideSpecs`, entries up to carrier 62)
     grows with the extent.
3. **Narrow V3 final site** (`EffectVmEmitRotationV3.lean` around l.500). It sits at arity 9, which
   is NOT admitted, so it has to split.
4. **Manifest and emit**
   - `metatheory/EmitLayoutManifest.lean`;
   - `scripts/emit_descriptors.py` / `scripts/emit-descriptors.sh`;
   - regenerate `circuit/src/effect_vm/layout_generated.rs` (`NUM_PRE_LIMBS`, `B_IROOT`) and every
     registry (`circuit/descriptors/rotation-v3-staged-registry.tsv`,
     `rotation-wide-registry-staged.tsv`, the welded set);
   - rotate `V3_STAGED_REGISTRY_FP`, `WIDE_REGISTRY_STAGED_FP`, `WIDE_MEMBER_GEOMETRY`;
   - follow `docs/` on the descriptor regen stamp.
5. **Rust producers and twins** (each must stay byte-identical to the Lean `wireCommitR`):
   - `turn/src/rotation_witness.rs`: `produce`/`produce_in_ctx` write `iroot8(..)` lanes; delete
     `iroot`; `wire_commit`, `wire_commit_8`.
   - `cell/src/commitment.rs`: `compute_rotated_pre_limbs` (l.1210), the v9 felt and felt8
     commitments.
   - `circuit/src/poseidon2.rs`: `wire_commit_8`, `wire_commit_8_chip`.
   - `circuit/src/faithful8.rs`: `from_wire_commit*`.
   - `circuit/src/effect_vm/trace_rotated.rs`: `fill_block`, `fill_wide_block` (final absorb,
     l.4679-4687), `RotatedBlockWitness` (`iroot: BabyBear` becomes 8 lanes).
   - `circuit/src/descriptor_ir2.rs`: `rotation_probe_trace_r`.
6. **Epoch and VK**
   - Bump `CANONICAL_STATE_SCHEMA_EPOCH` (cell);
   - the recursion VK rotates;
   - the apex `Rfix` re-keys over the regenerated registry;
   - Lean `wireCommitR8` and its byte-identity tests move together.
7. **Downstream**
   - Every `*_deployed_tooth.rs` and `*_binding_*` fixture that pins an anchor;
   - `grain-turn::session_head_openings`, which then opens over `iroot8`;
   - the node's retained-history fold.

## Precedent and cost

- **Precedent.** The 184 → 187 key-nonet flag day: 94532b3a4 (2026-08-01, "key nonet: the owner
  key's ninth lane had nowhere to be absorbed"), 2fd097812 (2026-08-08), and follow-ups (1123c3d02
  "the key nonet's +22").
- **Prior block.** On 2026-08-01 this cutover was blocked because `EmitLayoutManifest.lean` could
  not load: `EffectVmEmitRotationWide` was red under the 187 flag day. Check that the emit chain
  loads before starting.
- **Cost estimate.** Several days for one dedicated lane.
  - The Lean emit and theorem repair is on bb2 (one `lake` per lane, `LEAN_NUM_THREADS=8`).
  - Then a regen and a cold Rust rebuild.
  - Then the deployed-tooth suite, filtered per family.
- **Gate.** The falsifier above must flip: the exhibited collision no longer yields one anchor, and
  `the_residual_is_a_gate_not_a_note` is updated in the same commit.

## The decision for ember

Two options:

- Run this flag day on the legacy rotated stack.
- Carry an 8-lane (or wider) receipt root forward as a requirement of the new leaf, and leave the
  legacy stack at its documented 31-bit residual. Grain sessions are covered at full width by
  initiative 10's receipt join either way.
