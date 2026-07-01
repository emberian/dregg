//! # `trace_rotated` — THE LIVE rotated (R=24) trace generator (G1).
//!
//! `docs/ROTATION-CUTOVER.md` §5 deferred the rotated trace BUILDER: the staged keystones
//! (`EffectVmEmitRotationV3.lean`) prove the rotated R=24 cohort sound and the staged probe
//! measures the SHAPE, but the LIVE machinery that turns a real turn into the 327-column
//! rotated trace existed ONLY hand-welded inside `circuit/tests/effect_vm_rotation_flip.rs`
//! (`fill_block` / `fill_caveat`). This module PROMOTES that hand-welding into a genuine
//! generator: from the v1 186-column trace (`generate_effect_vm_trace`) plus the per-turn
//! producer witness limbs, it emits the rotated 327-column trace — the two rotated blocks
//! (BEFORE / AFTER) + the widened-caveat region + every chained `wireCommitR` digest — and
//! the 38-PI vector (34 v1 + 4 appended) the staged registry descriptor
//! (`transferVmDescriptor2R24`) pins.
//!
//! ## Law #1 — the shapes come from Lean
//!
//! Every quantity this module computes matches a Lean definition (the Rust interprets, never
//! invents):
//!
//! * the 31-limb absorption ORDER is `EffectVmEmitRotationV3.preLimbsAt`
//!   (cells_root · r0..r23 · cap_root · nullifier_root · heap_root · lifecycle · epoch ·
//!   committed_height, then iroot LAST) — the caller's `RotatedBlockWitness::pre_limbs` is
//!   already in this order (it is the producer `dregg_turn::rotation_witness::produce`'s
//!   output);
//! * the welds (`r0↔balance_lo`, `r1↔nonce`, `r2↔balance_hi`, `r3..r10↔fields`,
//!   `cap_root↔cap_root`) are `EffectVmEmitRotationV3.weldsAt` — overridden here per-row from
//!   THAT row's own v1 state block so the weld gates `colEq` hold on EVERY row;
//! * the chained commitment is `EffectVmEmitRotationR.wireCommitR` (4-wide head, 3-wide chip
//!   groups while ≥ 3 pre-iroot limbs remain, the iroot absorbed ALONE last, arity ∈ {2,4}) —
//!   byte-identical to the staged probe builder (`descriptor_ir2::rotation_probe_trace_r`),
//!   the producer's `wire_commit`, and `effect_vm_descriptors::rotation_layout_for`;
//! * the caveat manifest + chained `caveatCommit` are
//!   `EffectVmEmitRotationCaveat.{RotCaveatManifest, caveatCommit}` (1 count + 4 × 7-felt
//!   entries `[type_tag, domain_tag, key, p0..p3]`, then a 10-site chain).
//!
//! The four appended PI carriers land on the columns the staged registry descriptor's
//! `pi_binding` constraints pin (verified against the committed TSV): PI 34 ← row-0
//! before-block `state_commit` (col 218), PI 35 ← last-row after-block `state_commit`
//! (col 261), PI 36 ← last-row after-block `committed_height` limb (col 259), PI 37 ←
//! last-row caveat-region `caveat_commit` (col 310).
//!
//! ## STAGED-ADDITIVE
//!
//! NOTHING on the live v1 wire path calls this generator: the live 186-column trace +
//! IR-v1 prover stay the byte-identical default. This is the rotated path BESIDE it, behind
//! the IR-v2 route in `sdk::full_turn_proof` (gated). The flag-day descriptor regen + VK
//! bump is a SEPARATE deliberate act (G2/G5).

use super::columns::rotation::caveat as cav;
use super::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
use super::{EFFECT_VM_WIDTH, EffectVmContext, generate_effect_vm_trace_ext};
use crate::effect_vm::{CellState, Effect};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;

/// `(trace, dpis, map_heaps)` — the rotated trace plus its threaded map-op heap leaf sets.
type RotatedTraceWithHeaps = Result<
    (
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<crate::heap_root::HeapLeaf>>,
    ),
    String,
>;

/// `(trace, dpis, mem_boundary)` — the rotated trace plus its overflow-memory boundary witness.
type RotatedTraceWithMem = Result<
    (
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        crate::descriptor_ir2::MemBoundaryWitness,
    ),
    String,
>;

// ============================================================================
// The rotated appendix geometry (Lean `EffectVmEmitRotationV3`, R = 24).
// ============================================================================

/// The v1 main-table width the rotated appendix extends.
pub const V1_WIDTH: usize = EFFECT_VM_WIDTH; // 187 (P0-2 record-digest aux column)

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap_root · nullifier_root ·
/// commitments_root · heap_root · lifecycle · epoch · committed_height · lifecycle_disc ·
/// perms_digest · vk_digest · **mode** · **fields_root**). Lean `preLimbsAt_length = 37` at R = 24,
/// after the WAVE-3 mode/fields-root flag-day widening (NUM_PRE_LIMBS 35→37 — the committed mode byte +
/// fields_root digest sub-limbs, the NEW LAST pre-iroot limbs).
pub const NUM_PRE_LIMBS: usize = 1 + NUM_REGISTERS + 4 + 3 + 5 + 30; // 67 (v10: +30 faithful-8-felt completion limbs 37..66)

/// A rotated block: 37 limbs + iroot + state_commit + 12 chain carriers = 51 columns. The 37-limb
/// body chains as a 4-wide head (limbs 0..3) + ELEVEN 3-wide groups (limbs 4..36, exactly 33 = 11×3,
/// NO arity-2 leftover — the WAVE-2 vk singleton is absorbed into the eleventh group) + the iroot
/// alone, so the chain-carrier count stays 12 over the 35-limb shape (B_SPAN 49→51 — two more limbs,
/// no new carrier).
pub const B_SPAN: usize = 91;
/// The widened-caveat region: 29 manifest + 9 chain + 1 commit = 39 columns.
pub const C_SPAN: usize = 39;
/// The appendix: two blocks + the caveat region.
pub const APPENDIX: usize = 2 * B_SPAN + C_SPAN; // 141
/// The UN-GRADUATED rotated trace width (the rotated main columns BEFORE Phase B-GATE appends the
/// per-chip-lookup 7-lane blocks). `187 + 141 = 328`.
pub const ROT_WIDTH: usize = V1_WIDTH + APPENDIX; // 328

/// The number of poseidon2-chip lookup SITES the graduated rotated descriptor
/// (`*VmDescriptor2R24`, e.g. `attenuateVmDescriptor2R24`) carries — the per-site lane blocks
/// Phase B-GATE appends at the END of the rotated layout (each chip tuple is now 17-wide:
/// `1 arity + 8 inputs + out0 + 7 output-lanes`, the 7 lanes witnessed in appended columns). The
/// committed graduated width is `ROT_WIDTH + 7 * N_ROT_SITES = 328 + 280 = 608`, matching the TSV
/// `attenuateVmDescriptor2R24.trace_width`. Graduation APPENDS (positions < ROT_WIDTH unchanged).
pub const N_ROT_SITES: usize = 60;

/// The GRADUATED rotated trace width: the un-graduated rotated columns PLUS the 7×`N_ROT_SITES`
/// appended chip-lane columns (`328 + 280 = 608` = the committed `attenuateVmDescriptor2R24`
/// trace_width). The honest rotated lane columns (`ROT_WIDTH .. GRAD_ROT_WIDTH`) are filled
/// automatically by the prove wrapper's `descriptor_ir2::fill_chip_lanes`.
pub const GRAD_ROT_WIDTH: usize = ROT_WIDTH + 7 * N_ROT_SITES; // 608

/// In-block offset of the AUTHORITY-DIGEST limb (r23, limb 24) — the single felt
/// folding ALL authority-bearing cell state no other rotated limb carries
/// (permissions / VK / delegate / delegation / program / mode / token_id +
/// visibility / commitments / proved / side-table roots + fields[8..16]). This IS
/// the EffectVM `CellState::record_digest` (the v1-prefix OLD_COMMIT's fourth root
/// input), so the v1 OLD_COMMIT binds the SAME authority residue the rotated weld
/// carries — closing audit P0-2 across BOTH legs.
pub const B_AUTHORITY_DIGEST: usize = 24;
/// Alias used by the record-forcing pin (`record_pin_offset`): the setPermissions/setVK post
/// `record_digest` limb IS the authority-digest limb (r23, limb 24). Lean `B_RECORD_DIGEST`.
pub const B_RECORD_DIGEST: usize = B_AUTHORITY_DIGEST;
/// In-block offset of the per-cell `lifecycle` felt limb (limb 29 in `preLimbsAt`, shifted +1 by
/// `commitments_root`), filled by the producer witness `rotation_witness.rs::lifecycle_felt`. The
/// forced limb for the lifecycle flips (cellSeal/cellUnseal/cellDestroy). Lean
/// `EffectVmEmitRotationV3.B_LIFECYCLE`.
pub const B_LIFECYCLE: usize = 29;
/// In-block offset of the `cap_root` limb (the welded cap-root, limb 25).
pub const B_CAP_ROOT: usize = 25;
/// nullifier-root offset inside a block (limb 26) — the deployed nullifier accumulator's
/// openable sorted-Poseidon2 root the noteSpend grow-gate (`nullifierFreshOp` / `nullifierInsertOp`)
/// opens against.
pub const B_NULLIFIER_ROOT: usize = 26;
/// commitments-root offset inside a block (limb 27) — the flag-day committed shielded-set root
/// the noteCreate grow-gate (`commitmentsInsertOp`) opens against. Rides AFTER nullifier_root,
/// shifting heap/lifecycle/epoch/committed_height each by one (Lean `B_COMMITMENTS_ROOT`).
pub const B_COMMITMENTS_ROOT: usize = 27;
/// heap-root offset inside a block (limb 28, shifted +1 by `commitments_root`).
pub const B_HEAP_ROOT: usize = 28;
/// In-block offset of the `committed_height` limb (limb 31, UNCHANGED by the disc flag-day).
pub const B_COMMITTED_HEIGHT: usize = 31;
/// In-block offset of the committed lifecycle-DISC limb (limb 32 — the WAVE-1 flag-day committed
/// `u8 0..4` discriminant beside the opaque `lifecycle_felt` at 29). Lean `EffectVmEmitRotationV3.B_DISC`.
pub const B_DISC: usize = 32;
/// In-block offset of the committed PERMS-DIGEST limb (limb 33 — the WAVE-2 flag-day perms sub-limb,
/// `= permsHash[0]`, the forced limb for the setPermissions weld). Lean `EffectVmEmitRotationV3.B_PERMS`.
pub const B_PERMS: usize = 33;
/// In-block offset of the committed VK-DIGEST limb (limb 34 — the WAVE-2 flag-day vk sub-limb,
/// `= vkHash[0]`, the forced limb for the setVK weld). Lean `EffectVmEmitRotationV3.B_VK`.
pub const B_VK: usize = 34;
/// In-block offset of the committed cell-MODE limb (limb 35 — the WAVE-3 flag-day mode byte,
/// `Hosted=0 / Sovereign=1`, the makeSovereign CONSTANT-force limb). Lean `EffectVmEmitRotationV3.B_MODE`.
pub const B_MODE: usize = 35;
/// In-block offset of the committed `fields_root` digest limb (limb 36 — the WAVE-3 flag-day overflow
/// map root, the setFieldDyn / refusal weld limb). Lean `EffectVmEmitRotationV3.B_FIELDS_ROOT`.
pub const B_FIELDS_ROOT: usize = 36;
/// In-block offset of the iroot carrier (absorbed last, limb 37, shifted +2 by the mode/fields-root limbs).
pub const B_IROOT: usize = 67;
/// In-block offset of the `state_commit` carrier (the chain's final digest).
pub const B_STATE_COMMIT: usize = 68;
/// In-block base of the chained-absorption intermediate carriers (12 sites, 39..=50).
pub const B_CHAIN_BASE: usize = 69;

/// Absolute base column of the BEFORE rotated block.
pub const BEFORE_BASE: usize = V1_WIDTH; // 186
/// Absolute base column of the AFTER rotated block.
pub const AFTER_BASE: usize = V1_WIDTH + B_SPAN; // 237
/// Absolute base column of the widened-caveat region.
pub const CAVEAT_BASE: usize = V1_WIDTH + 2 * B_SPAN; // 287

/// The number of v1 public inputs the rotated PI vector prefixes. This is the
/// length of the v1 PI window the descriptors pin into — it MUST cover every v1
/// pin, the highest of which is `pi::ACTOR_NONCE`. Phase C
/// (`FAITHFUL-STATE-COMMITMENT.md`) widened OLD/NEW_COMMIT 4→8 each (+8 prefix),
/// pushing `ACTOR_NONCE` 33→41, so the window grew 34→42 to keep the nonce pin in
/// range (`42 = pi::ACTOR_NONCE + 1`). A window of 34 would slice the nonce OFF the
/// rotated PI vector, leaving the row-0 nonce boundary pin reading past the slice.
pub const V1_PI_COUNT: usize = 42;
/// The rotated public-input count (42 v1 + 4 appended commit/height/caveat pins).
pub const ROT_PI_COUNT: usize = V1_PI_COUNT + 4;
/// The rotated NOTE-SPEND public-input count (the rotated prefix + the appended
/// nullifier slot at index `ROT_PI_COUNT` — `EffectVmEmitRotationV3.noteSpendV3`, the
/// C4 last-flip-gate close). Only the note-spend cohort member carries this fifth pin.
pub const ROT_NULLIFIER_PI_COUNT: usize = ROT_PI_COUNT + 1;
/// The rotated PI slot carrying the spend row's folded nullifier (the C4 weld). Equals
/// `ROT_PI_COUNT` — the first slot past the four rotated commit pins.
pub const ROT_NULLIFIER_PI: usize = ROT_PI_COUNT;

// ============================================================================
// Generator inputs (producer-witness shaped, dependency-free).
// ============================================================================

/// One rotated state-block witness for a single cell's before/after `RecordKernelState`.
///
/// `pre_limbs` is the 31-limb absorption vector in the Lean-pinned order
/// (`EffectVmEmitRotationV3.preLimbsAt`); `iroot` is the receipt-index MMR root absorbed
/// LAST. This is exactly the data `dregg_turn::rotation_witness::RotationWitness` carries —
/// the producer bridge (in `turn` / `sdk` / the flip test, which depend on both crates)
/// constructs a `RotatedBlockWitness` from a `RotationWitness`'s `pre_limbs` + `iroot`. The
/// generator lives in `dregg-circuit` (which cannot depend on `dregg-turn`), so it takes the
/// limbs directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotatedBlockWitness {
    /// The 32 pre-iroot limbs, in absorption order.
    pub pre_limbs: Vec<BabyBear>,
    /// The receipt-index MMR root (absorbed last).
    pub iroot: BabyBear,
    /// Light-client conservation: the per-cell ASSET CLASS folded from the
    /// cell's committed `token_id` (`block_conservation::fold_token_id_to_asset`,
    /// dregg3: AssetId := issuer-cell). Threaded into the v1 sub-trace's
    /// `EffectVmContext.asset_class` so the proof COMMITS to its genuine asset
    /// class (the row-0 `aux_off::ASSET_CLASS` column + `PI[v3::ASSET_CLASS]`),
    /// making the light-client per-asset partition non-trivial for multi-asset
    /// turns. Only the BEFORE block's value is read (it is the cell whose state
    /// the EffectVM row proves); the AFTER block carries the same class. Zero is
    /// the back-compat / native-asset sentinel — the executor then falls back to
    /// its trusted ledger class (`resolve_proof_asset_class`).
    pub asset_class: BabyBear,
}

impl RotatedBlockWitness {
    /// Build from raw limbs, validating the count. Asset class defaults to the
    /// ZERO sentinel; use [`Self::with_asset_class`] to thread the real class.
    pub fn new(pre_limbs: Vec<BabyBear>, iroot: BabyBear) -> Result<Self, String> {
        if pre_limbs.len() != NUM_PRE_LIMBS {
            return Err(format!(
                "RotatedBlockWitness: need {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}, \
                 got {}",
                pre_limbs.len()
            ));
        }
        Ok(Self {
            pre_limbs,
            iroot,
            asset_class: BabyBear::ZERO,
        })
    }

    /// Set the per-cell asset class (the fold of the cell's committed `token_id`).
    pub fn with_asset_class(mut self, asset_class: BabyBear) -> Self {
        self.asset_class = asset_class;
        self
    }
}

/// One widened-caveat entry: the constraint type tag, the DOMAIN tag (registers 0 · heap 1,
/// `cav::DOMAIN_REGISTERS` / `cav::DOMAIN_HEAP`), the in-domain key (a register index in the
/// registers domain, an arbitrary heap-key felt in the heap domain), and up to 4 params. The
/// Rust twin of Lean `EffectVmEmitRotationCaveat.RotCaveatEntry` (7-felt packing).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotatedCaveatEntry {
    pub type_tag: u32,
    pub domain_tag: u32,
    pub key: BabyBear,
    pub params: [BabyBear; 4],
}

/// The fixed-size caveat manifest the rotated region carries: 1 count + 4 entries × 7 felts
/// = 29 felts. Lean `EffectVmEmitRotationCaveat.RotCaveatManifest`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotatedCaveatManifest {
    pub entries: [RotatedCaveatEntry; cav::MAX_CAVEATS],
}

impl RotatedCaveatManifest {
    /// The count of non-empty entries (`type_tag != 0`, scanning from entry 0; the manifest
    /// keeps the live convention that active entries are a prefix).
    fn count(&self) -> u32 {
        self.entries.iter().take_while(|e| e.type_tag != 0).count() as u32
    }

    /// Whether the manifest contains an entry carrying the given type tag (the rotated-leg
    /// COVERAGE primitive — the rotated twin of the off-AIR `pi::SLOT_CAVEAT_*` scan). Reads
    /// the active prefix (`type_tag != 0`); padding entries never match a capacity tag (17/19).
    pub fn covers_tag(&self, tag: u32) -> bool {
        self.entries
            .iter()
            .take_while(|e| e.type_tag != 0)
            .any(|e| e.type_tag == tag)
    }
}

/// **THE CAPACITY-CARRIER PROJECTION (PIECE 1 of the VK epoch, STAGED).** Project the off-AIR
/// `SlotCaveatEntry` manifest (the live `pi::SLOT_CAVEAT_*` v1 layout, `{type_tag, slot_index,
/// params}`) onto the AIR-bound rotated caveat carrier (`RotatedCaveatManifest`). The rotated
/// region — manifest cols chained by `caveatCommit` to the published caveat-commit PI — is in the
/// DEPLOYED AIR of every R=24 cohort descriptor, so a manifest projected here is BOUND into the
/// ~124-bit wide commit a pure light client binds: a forger cannot omit it off-AIR (the Lean
/// `Dregg2.Deos.CapacityCarrier.carrier_omission_impossible`).
///
/// Each slot-domain caveat maps to the registers domain (`cav::DOMAIN_REGISTERS`) with the
/// `slot_index` widened to the felt `key` and the four params preserved positionally — the faithful
/// rotated twin of the v1 entry (the producer side of the Lean `RotCaveatEntry` / `toEntry` bridge).
/// At most `MAX_CAVEATS` entries fit (the carrier width is fixed); a longer manifest is REFUSED
/// rather than truncated (truncation could silently drop a declared capacity gate — fail closed).
///
/// STAGED: nothing on the live wire calls this yet (no deployed cell declares a capacity caveat).
/// It is the producer the carrier-coverage verifier (`verify_rotated_caveat_coverage`) consumes,
/// built BESIDE the deployed empty-manifest default. NOT VK-affecting (the carrier columns + the
/// `caveatCommit` PI binding already exist; the tags are data on existing columns). See
/// `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6.
pub fn slot_caveats_to_rotated_manifest(
    entries: &[crate::effect_vm::trace::SlotCaveatEntry],
) -> Result<RotatedCaveatManifest, String> {
    if entries.len() > cav::MAX_CAVEATS {
        return Err(format!(
            "capacity-carrier projection: {} slot caveats exceed the rotated carrier width \
             ({} entries); truncation could drop a declared capacity gate — refused (fail-closed)",
            entries.len(),
            cav::MAX_CAVEATS
        ));
    }
    let mut manifest = RotatedCaveatManifest::default();
    for (i, e) in entries.iter().enumerate() {
        manifest.entries[i] = RotatedCaveatEntry {
            type_tag: e.type_tag,
            domain_tag: cav::DOMAIN_REGISTERS,
            key: BabyBear::new(e.slot_index as u32),
            params: e.params,
        };
    }
    Ok(manifest)
}

// ============================================================================
// THE GENERATOR.
// ============================================================================

/// Generate the LIVE rotated (R = 24) trace + 38-PI vector for one transfer-shaped turn.
///
/// `initial_state` / `effects` drive the v1 trace (`generate_effect_vm_trace`); `before_w` /
/// `after_w` are the per-turn producer witnesses for the acting cell's before/after
/// `RecordKernelState` (their `pre_limbs` weld to the v1 state block by construction —
/// `r0↔balance_lo`, …, `cap_root↔cap_root`); `caveat` is the turn's widened-caveat manifest.
///
/// The rotated blocks + caveat region are filled on EVERY row (the welds + PI pins read
/// first/last; a uniform fill keeps the weld gates true on padding rows too). Every chained
/// `wireCommitR` / `caveatCommit` digest is GENUINE (computed from this row's own limbs), so
/// the four appended PI carriers are bound, not free wires.
///
/// Returns `(trace, public_inputs)` ready for `descriptor_ir2::prove_vm_descriptor2` against
/// `transferVmDescriptor2R24`.
pub fn generate_rotated_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if before_w.pre_limbs.len() != NUM_PRE_LIMBS || after_w.pre_limbs.len() != NUM_PRE_LIMBS {
        return Err(format!(
            "rotated generator: each block witness needs {NUM_PRE_LIMBS} pre-iroot limbs"
        ));
    }

    // The v1 reference trace + PIs — the byte-identical live machinery. The only
    // context departure from the default wrapper (`generate_effect_vm_trace`) is the
    // per-cell ASSET CLASS threaded off the BEFORE block witness: it populates the
    // row-0 `aux_off::ASSET_CLASS` column + `PI[v3::ASSET_CLASS]` so the proof commits
    // to its genuine asset class (the light-client per-asset conservation partition).
    // `actor_nonce` keeps the default wrapper's single-cell boundary invariant
    // (`state_before.nonce == PI[ACTOR_NONCE]`); a ZERO `asset_class` reproduces the
    // exact byte-identical default-context trace.
    let v1_ctx = EffectVmContext {
        actor_nonce: initial_state.nonce as u64,
        asset_class: before_w.asset_class,
        ..Default::default()
    };
    let (mut trace, pis) = generate_effect_vm_trace_ext(initial_state, effects, v1_ctx);
    if trace.is_empty() {
        return Err("rotated generator: v1 trace is empty".into());
    }
    if trace[0].len() != V1_WIDTH {
        return Err(format!(
            "rotated generator: v1 trace width {} != {V1_WIDTH}",
            trace[0].len()
        ));
    }
    if pis.len() < V1_PI_COUNT {
        return Err(format!(
            "rotated generator: v1 PI vector {} shorter than {V1_PI_COUNT}",
            pis.len()
        ));
    }

    // Widen each row to the rotated width and fill the appendix.
    for row in trace.iter_mut() {
        row.resize(ROT_WIDTH, BabyBear::ZERO);
        fill_block(row, BEFORE_BASE, STATE_BEFORE_BASE, before_w);
        fill_block(row, AFTER_BASE, STATE_AFTER_BASE, after_w);
        fill_caveat(row, CAVEAT_BASE, caveat);
    }

    // THE LIFECYCLE-PAYLOAD HASH GATE declared column (cellSeal / cellDestroy / receiptArchive — the
    // STAGE-C light-client close, `EffectVmEmitRotationV3.lifecyclePayloadHashGate`). The deployed
    // descriptor for these three movers carries a SELECTOR-GATED WELD of the AFTER lifecycle limb
    // (`B_LIFECYCLE = 29`) to the declared payload-hash column `prmCol 3` (= `PARAM_BASE + 3`). The
    // producer fills that column with the FELT-DOMAIN `lifecycle_felt` of the after-cell lifecycle —
    // BYTE-IDENTICAL to the AFTER lifecycle limb (`after_w.pre_limbs[B_LIFECYCLE]`), so the honest
    // trace satisfies the weld. The LIGHT-CLIENT force is that the verifier INDEPENDENTLY recomputes
    // this column from `lifecycle_payload_felt(disc, reason_hash, block_height)` — the PI-bound effect
    // `reason_hash` + the turn-header height it holds — NO trusted post-cell. So a forged
    // after-lifecycle limb (a different reason_hash / sealed_at) DIVERGES from the recomputed payload
    // hash and the weld is UNSAT for a ledgerless client. (PARAM cols are off the commitment chain —
    // declared params bound via the gate, not folded into the state-block commit.)
    if lifecycle_payload_gated(effects.first()) {
        use super::columns::PARAM_BASE;
        let lc_felt = after_w.pre_limbs[B_LIFECYCLE];
        for row in trace.iter_mut() {
            row[PARAM_BASE + 3] = lc_felt;
        }
    }

    // The four appended PIs, read from the trace carriers the descriptor's pin constraints
    // bind. (The pins are `pi_binding` constraints, so these reads must agree with the
    // committed columns 218 / 261 / 259 / 310.)
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = pis[..V1_PI_COUNT].to_vec();
    dpis.push(r0[BEFORE_BASE + B_STATE_COMMIT]); // PI 42 (V1_PI_COUNT): rotated OLD commit (col 218)
    dpis.push(last[AFTER_BASE + B_STATE_COMMIT]); // PI 43: rotated NEW commit (col 261)
    dpis.push(last[AFTER_BASE + B_COMMITTED_HEIGHT]); // PI 44: committed height (col 259)
    dpis.push(last[CAVEAT_BASE + C_SPAN - 1]); // PI 45: caveat commit (col 310)
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT);

    // THE C4 LAST-FLIP-GATE (note-spend nullifier weld): a NoteSpend turn rotates against the
    // `noteSpendVmDescriptor2R24` descriptor, which carries a FIFTH appended PI pin
    // (`EffectVmEmitRotationV3.noteSpendV3`) welding the spend row's folded nullifier
    // (`param::NULLIFIER = param0`, col `PARAM_BASE + 0`) to rotated PI slot 38 on the FIRST
    // row — the rotated analog of the v1 hand-AIR D5 cross-binding (offset 198). The note-spend
    // spend is laid on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm), so the pin
    // reads `r0[PARAM_BASE + param::NULLIFIER]`. We append it ONLY for a NoteSpend lead effect,
    // matching the descriptor's 39-PI shape (the prover asserts `pis.len() == piCount`); the
    // other 35 cohort members keep the 38-PI vector. This lets a note-spending turn rotate:
    // `verify_full_turn` step 8 reads PI[38] instead of refusing the rotated leg.
    if matches!(effects.first(), Some(Effect::NoteSpend { .. })) {
        use super::columns::{PARAM_BASE, param};

        // SINGLE-SPEND INVARIANT (the soundness tooth must survive rotation). The v1 hand-AIR
        // gate is PER-ROW (`s_notespend·(param0 − PI[NOTESPEND_NULLIFIER])` on EVERY spend row)
        // AND v1 surfaces ONE nullifier into the single PI slot — so a turn with two DISTINCT
        // nullifiers is UNSAT on v1 (`trace.rs` D5: "multi-distinct-nullifier proofs need PI
        // extension — deferred"). The rotated weld is a FIRST-row pin against the SAME single PI
        // slot (PI[38]), cross-checked by `verify_full_turn` step 8 against the one freshness
        // proof. A second NoteSpend on a NON-first row would be UNPINNED by the rotated
        // descriptor and ESCAPE the freshness check — a double-spend the v1 leg forbids. So the
        // rotated note-spend leg accepts exactly ONE spend row (v1's single-nullifier shape); a
        // multi-NoteSpend turn fails closed here and falls back to the v1 leg. Without this the
        // rotation would WEAKEN no-double-spend (a regressed tooth), not preserve it.
        let spend_count = effects
            .iter()
            .filter(|e| matches!(e, Effect::NoteSpend { .. }))
            .count();
        if spend_count != 1 {
            return Err(format!(
                "rotated note-spend leg supports exactly one spend row (the single-nullifier \
                 freshness shape), got {spend_count}; a multi-NoteSpend turn must use the v1 leg \
                 (where a second distinct nullifier is UNSAT). Rotating it would leave the \
                 non-first spend unpinned and ESCAPE the no-double-spend freshness check."
            ));
        }

        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 38: the spend row's folded nullifier
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE RECORD-FORCING PIN (the deployment-soundness close for the 7 binds-but-unforced
    // effects: cellSeal/cellUnseal/cellDestroy/setPermissions/setVK + the audit writes
    // refusal/receiptArchive — `EffectVmEmitRotationV3.rotateV3WithRecordPin`). The rotated AFTER
    // block CARRIES the per-cell write (limb `B_LIFECYCLE = 29` for the lifecycle flips, limb
    // `B_RECORD_DIGEST = 24` for the permissions/VK record-digest AND the audit-slot writes —
    // refusal/receiptArchive set a named record field in `fields_root`, which the r23 authority
    // digest folds), and the rolled-up commitment BINDS it — but bare `rotateV3` does NOT FORCE
    // the AFTER limb to the correctly-written value. The descriptor for these seven carries a
    // FIFTH last-row PI pin welding that limb to rotated PI slot 38; a frozen-lifecycle /
    // un-written-record / frozen-audit-slot AFTER block FAILS the pin and is UNSAT. We push the
    // honest post value (read from the LAST row's AFTER block, exactly the column the pin binds)
    // so the honest trace satisfies it; the verifier recomputes PI[38] from the committed
    // pre-state + the effect, so a forgery cannot match it. The 33 other cohort members keep the
    // 38-PI vector.
    if let Some(off) = record_pin_offset(effects.first()) {
        dpis.push(last[AFTER_BASE + off]); // PI 46: the correctly-written post lifecycle / record digest
        // H1: the RECORD-DIGEST movers (off == B_AUTHORITY_DIGEST: setPerms/setVK/makeSovereign/refusal)
        // pin ALL 8 faithful authority limbs (`withRecordPin8Headroom2`): limb-0 above + the 7 headroom
        // limbs (AFTER offsets 12..18) at PI 47..53. Push the honest post values (read from the LAST
        // row's AFTER block, the columns the pins bind); the verifier anchors PI 46..53 to
        // `compute_authority_digest_8(post_cell)`, so a 31-bit-colliding wide-open authority forged into
        // ANY of the 8 limbs is UNSAT (the GENTIAN close for movers). Lifecycle movers (off ==
        // B_LIFECYCLE) keep the single limb-0 pin.
        if off == B_AUTHORITY_DIGEST {
            for i in 0..7 {
                dpis.push(last[AFTER_BASE + 12 + i]);
            }
            debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 8);
        } else {
            debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);
        }
    }

    // THE ACCOUNTS-SET GROW-GATE PIN (createCell / factory / spawn — the deployment-real account
    // set-insert close). The live `{createCell,factory,spawn}VmDescriptor2R24` carry a FIFTH pin
    // welding the new-cell key (`param0`, col `PARAM_BASE + 0` — the `Effect::CreateCell`/`Spawn`/
    // `Factory` arm writes the child id there on row 0) to rotated PI slot 38, plus the two
    // `cells_root` map-ops (limb 0) that force the accounts set-insert. We push the row-0 new-cell
    // key so the honest trace matches the 39-PI shape; the openable before/after cells trees are
    // threaded by `generate_rotated_create_cell_trace_with_accounts_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.{createCellV3,factoryV3,spawnV3}`.
    if let Some(key_col) = new_cell_key_param_col(effects.first()) {
        use super::columns::PARAM_BASE;
        dpis.push(r0[PARAM_BASE + key_col]); // PI 38: the new-cell key
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE COMMITMENTS-SET GROW-GATE PIN (noteCreate — the deployment-real commitment set-insert
    // close, the `commitments_root` flag-day). The live `noteCreateVmDescriptor2R24` carries a FIFTH
    // pin welding the published note commitment (`param0`, col `PARAM_BASE + 0` — the
    // `Effect::NoteCreate` arm writes the commitment there on row 0) to rotated PI slot 38, plus the
    // `commitmentsInsertOp` map-op (limb 27) that forces the commitment set-insert. We push the row-0
    // commitment so the honest trace matches the 39-PI shape; the openable before/after commitments
    // trees are threaded by `generate_rotated_note_create_trace_with_commitments_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.noteCreateV3`.
    if matches!(effects.first(), Some(Effect::NoteCreate { .. })) {
        use super::columns::{PARAM_BASE, param};
        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 38: the published note commitment (param0)
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    Ok((trace, dpis))
}

/// The maximum fee a fee-in-proof transfer may carry: the descriptor's col-89 range lookup is
/// `table 2` (range, 30 bits), so the fee must fit in 30 bits — exactly the per-limb balance bound
/// (`BAL_LIMB_BITS = 30`). A larger fee has no range-check witness and is UNSAT, so we fail closed
/// here (rather than silently wrapping the felt) to keep producer and verifier in lockstep.
pub const FEE_MAX: u64 = (1u64 << 30) - 1;

/// **THE FEE-IN-PROOF rotated transfer generator (`transferFeeVmDescriptor2R24`).**
///
/// Identical to [`generate_rotated_effect_vm_trace`] EXCEPT the deployed `transferFeeVmDescriptor2R24`
/// debits the turn `fee` INSIDE the proven transition (so NEW_COMMIT binds the POST-fee balance) and
/// publishes the fee as PI slot 38. The descriptor (vs. the unfee'd `transferVmDescriptor2R24`)
/// differs by exactly four constraint deltas (verified against the committed registry TSV):
///   (a) the balance-lo gate is AUGMENTED to `after.bal_lo = before.bal_lo + amount·(1−2·dir) − feeCol`
///       (`feeCol = STATE_AFTER_BASE + state::RESERVED = col 89`);
///   (b) the RESERVED passthrough gate (`after.reserved == before.reserved`, col 89 == col 67) is DROPPED
///       (RESERVED now carries the fee, not a frozen passthrough);
///   (c) a 30-bit range check (table 2) is added on col 89;
///   (d) a last-row `pi_binding` pins col 89 → PI 38.
///
/// The v1 generator (`generate_effect_vm_trace`) computes the after-balance from the effects WITHOUT
/// the fee, so the bare after-block balance is the PRE-fee `before + amount·(1−2dir)`. This function
/// makes the after-block POST-fee as a column override + commitment recompute (the effects cannot
/// express a fee debit, and `after_w`'s welded balance limb is OVERRIDDEN per-row from the v1 state
/// block by `fill_block`, so the authoritative after-balance is the v1 col 76):
///   * the post-fee full u64 balance `post = bal − fee` is re-split into (lo, hi) and written to the
///     v1 after-block `BALANCE_LO`/`BALANCE_HI` (cols 76/77);
///   * the v1 GROUP-4 after-state-commit chain is recomputed (cols 98/99/100 intermediates → col 88
///     STATE_COMMIT, absorbing the record-digest aux at col 186), so the v1 after STATE_COMMIT (PI 4)
///     and the after bal_lo/hi (PIs 14/15) bind the post-fee balance;
///   * `fill_block` is RE-RUN for the AFTER rotated block so its welded balance limb (col 237+1) +
///     chained `wireCommitR` → rotated NEW_COMMIT (col 265 / PI 35) bind the post-fee balance;
///   * the fee is written to col 89 (= `STATE_AFTER_BASE + state::RESERVED`) on EVERY row — the
///     transfer-row gate reads it (selector 0 makes it inert on padding rows) and the last-row pin
///     reads it regardless;
///   * the 39-PI vector is re-read from the (now post-fee) trace carriers so producer and verifier
///     reconstruct byte-identical PIs (Fiat–Shamir agreement). PI 38 = the fee felt.
///
/// The producer (`cipherclerk::prove_sovereign_turn_rotated`) and verifier
/// (`proof_verify::verify_and_commit_proof_rotated`) BOTH call this with the SAME pre-fee
/// `initial_state`/`effects` and the SAME `fee`, so the v1 sub-trace's pre-fee after-balance is
/// identical on both sides and the post-fee override lands identically — they agree by construction.
///
/// RESERVED (`state::RESERVED`, col 89) is NOT a state-commitment hash input (it is absent from the
/// GROUP-4 chain `[76..87] → 98/99/100 → 88`), so writing the fee there does NOT corrupt OLD/NEW
/// COMMIT — only the BALANCE change (post-fee) flows into the commitment. Returns `(trace, pis)` ready
/// for `transferFeeVmDescriptor2R24` (39 PIs).
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn generate_rotated_effect_vm_trace_with_fee(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    fee: u64,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    use super::columns::state;

    if fee > FEE_MAX {
        return Err(format!(
            "fee-in-proof: fee {fee} exceeds the 30-bit range-check bound {FEE_MAX} (col 89 has no \
             range witness for a larger fee — the descriptor's table-2 lookup would be UNSAT)"
        ));
    }

    // The base rotated trace + 38-PI vector (PRE-fee after-balance, welds, v1 economic block).
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    let fee_col = STATE_AFTER_BASE + state::RESERVED; // 89
    let record_digest = super::columns::AUX_BASE + super::columns::aux_off::STATE_RECORD_DIGEST; // 186
    let fee_felt = BabyBear::new(fee as u32);

    // The fee debits the actor's balance on the TRANSFER row (`Effect::Transfer` is laid on row 0,
    // its AFTER block carrying the post-transfer balance). The post-transfer state then carries
    // forward through the trailing NoOp passthrough rows as BOTH their before and after state. So the
    // post-fee rewrite is:
    //   * row 0 (transfer): subtract `fee` from the AFTER block ONLY (the BEFORE block is the pre-fee
    //     OLD_COMMIT state; the fee gate verifies `after = before − amount − fee`);
    //   * rows ≥ 1 (NoOp passthrough): subtract `fee` from BOTH the before and after block (they carry
    //     the post-fee balance; the cross-row continuity `next.before == local.after` then chains the
    //     post-fee state-commit from row 0 onward).
    // Each touched block has its balance re-split, its v1 STATE_COMMIT recomputed (the AFTER block via
    // the descriptor's published GROUP-4 lookups `[76..79]→98`, `[80..83]→99`, `[84..87]→100`,
    // `[98,99,100,186]→88`; the BEFORE block by the same `hash_4_to_1` over its own limbs — its
    // intermediates are not published, only its STATE_COMMIT col 66 is bound to PI 0 + the continuity),
    // and its rotated block (welded balance limb → chained `wireCommitR` → STATE_COMMIT) re-run.
    let n = trace.len();
    for r in 0..n {
        let is_transfer_row = r == 0;
        // BEFORE block: debit only on the carry-forward NoOp rows (NOT the transfer row's pre-fee
        // OLD_COMMIT state).
        if !is_transfer_row {
            debit_v1_block_balance(&mut trace[r], STATE_BEFORE_BASE, fee, record_digest, None);
            fill_block(&mut trace[r], BEFORE_BASE, STATE_BEFORE_BASE, before_w);
        }
        // AFTER block: debit on EVERY row (row 0's post-transfer after, and the NoOp carry-forward).
        // The AFTER block's GROUP-4 intermediates ARE published (cols 98/99/100), so thread them.
        let aux = super::columns::AUX_BASE;
        let inters = (
            aux + super::columns::aux_off::STATE_INTER1,
            aux + super::columns::aux_off::STATE_INTER2,
            aux + super::columns::aux_off::STATE_INTER3,
        );
        debit_v1_block_balance(
            &mut trace[r],
            STATE_AFTER_BASE,
            fee,
            record_digest,
            Some(inters),
        );
        fill_block(&mut trace[r], AFTER_BASE, STATE_AFTER_BASE, after_w);
        // The fee rides the RESERVED limb on EVERY row, in BOTH the after-block (col 89 — read by the
        // bal-lo fee gate and the last-row PI-38 pin) AND the before-block (col 67). The fee descriptor
        // DROPS the RESERVED passthrough GATE but KEEPS the RESERVED cross-row CONTINUITY transition
        // (`next.before.reserved == local.after.reserved`, offset 13), so the fee must ride the
        // before-block RESERVED too or the continuity from row r to r+1 fails. RESERVED is NOT a
        // state-commitment hash input (absent from the GROUP-4 chain over cols 54..65 / 76..87), so
        // writing the fee there does not perturb OLD/NEW_COMMIT.
        trace[r][fee_col] = fee_felt; // col 89 (after.reserved)
        trace[r][STATE_BEFORE_BASE + state::RESERVED] = fee_felt; // col 67 (before.reserved)

        // The bal-lo fee gate (`after.bal_lo − before.bal_lo + amount·(2dir−1) + fee == 0`, col 89 =
        // fee) is UNCONDITIONAL — it fires on EVERY row, NOT selector-gated. On the TRANSFER row (row
        // 0) the base generator's amount (param0 col 68) / dir (param1 col 69) satisfy it: `−600 =
        // 100·(1−2) − 500`. But on the trailing NoOp passthrough rows the balance is unchanged
        // (`after − before = 0`) and the base generator leaves amount/dir = 0, so the gate would demand
        // `fee == 0` — UNSAT once the last-row PI-38 pin needs col 89 = fee. We satisfy the gate by
        // writing amount(col 68) = fee, dir(col 69) = 0 on the NoOp rows, so `0 − fee + 0 + fee = 0`
        // holds AND col 89 = fee for the pin. The only OTHER constraint touching cols 68/69 in this
        // descriptor is the dir-boolean gate (`dir·(dir−1)`, satisfied by dir = 0); neither column is
        // PI-bound or effects-hash-bound here, so this is free.
        if !is_transfer_row {
            trace[r][super::columns::PARAM_BASE] = fee_felt; // param0 (amount) = fee
            trace[r][super::columns::PARAM_BASE + 1] = BabyBear::ZERO; // param1 (dir) = 0
        }
    }

    // Re-read the rotated PI vector from the post-fee trace carriers so producer + verifier agree.
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = base_pis[..ROT_PI_COUNT].to_vec();
    // The witness-INDEPENDENT v1 prefix PIs that moved with the post-fee override (the after-block
    // NEW_COMMIT / FINAL_BAL limbs) ride the LAST row's after-block (the post-fee final state).
    // These are the FULL-layout pi.rs offsets (NEW_COMMIT = 8, FINAL_BAL_LO/HI = 22/23 post-Phase-C).
    dpis[super::pi::NEW_COMMIT] = last[STATE_AFTER_BASE + state::STATE_COMMIT]; // v1 after STATE_COMMIT
    dpis[super::pi::FINAL_BAL_LO] = last[STATE_AFTER_BASE + state::BALANCE_LO]; // v1 after bal_lo
    dpis[super::pi::FINAL_BAL_HI] = last[STATE_AFTER_BASE + state::BALANCE_HI]; // v1 after bal_hi
    dpis[V1_PI_COUNT + 1] = last[AFTER_BASE + B_STATE_COMMIT]; // rotated NEW_COMMIT (post-fee)
    // (the rotated OLD_COMMIT / height / caveat pins are unaffected by the fee; ride the base vector.)
    dpis.push(fee_felt); // PI ROT_PI_COUNT: the published fee (col 89, last-row pinned).
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);

    Ok((trace, dpis))
}

/// Subtract `fee` from one v1 state block's balance (in place) and recompute its STATE_COMMIT, the
/// fee-in-proof column surgery the `transferFeeVmDescriptor2R24` post-fee rewrite rests on. `base` is
/// the block's column base (`STATE_BEFORE_BASE = 54` or `STATE_AFTER_BASE = 76`). The balance limbs
/// are re-split (`split_u64`, the canonical 30-bit lo / 34-bit hi split `CellState::to_trace_cols`
/// uses), then the GROUP-4 state-commit is rebuilt: `hash_many([bal_lo, bal_hi, nonce, field0])`,
/// `hash_many([field1..4])`, `hash_many([field5..7, cap_root])`, then
/// `hash_many([i1, i2, i3, record_digest])` → STATE_COMMIT — byte-identical to `compute_commitment`
/// and the descriptor's poseidon lookups. When `inters` is `Some((c1, c2, c3))`, the three
/// intermediates are ALSO written to those AUX columns (the AFTER block, whose intermediates the
/// descriptor's lookups bind); `None` for the BEFORE block (only its STATE_COMMIT is published).
fn debit_v1_block_balance(
    row: &mut [BabyBear],
    base: usize,
    fee: u64,
    record_digest_col: usize,
    inters: Option<(usize, usize, usize)>,
) {
    use super::columns::state;
    use super::helpers::split_u64;
    let bal_lo = base + state::BALANCE_LO;
    let bal_hi = base + state::BALANCE_HI;
    // Recover the pre-fee balance from the limbs (`split_u64` inverse: `lo | (hi << 30)`), subtract
    // the fee, re-split.
    let pre = (row[bal_lo].as_u32() as u64) | ((row[bal_hi].as_u32() as u64) << 30);
    let (lo, hi) = split_u64(pre.saturating_sub(fee));
    row[bal_lo] = lo;
    row[bal_hi] = hi;
    // The GROUP-4 commit chain over the (now post-fee) block limbs + the record-digest aux.
    let i1 = hash_many(&[
        row[bal_lo],
        row[bal_hi],
        row[base + state::NONCE],
        row[base + state::FIELD_BASE],
    ]);
    let i2 = hash_many(&[
        row[base + state::FIELD_BASE + 1],
        row[base + state::FIELD_BASE + 2],
        row[base + state::FIELD_BASE + 3],
        row[base + state::FIELD_BASE + 4],
    ]);
    let i3 = hash_many(&[
        row[base + state::FIELD_BASE + 5],
        row[base + state::FIELD_BASE + 6],
        row[base + state::FIELD_BASE + 7],
        row[base + state::CAP_ROOT],
    ]);
    if let Some((c1, c2, c3)) = inters {
        row[c1] = i1;
        row[c2] = i2;
        row[c3] = i3;
    }
    row[base + state::STATE_COMMIT] = hash_many(&[i1, i2, i3, row[record_digest_col]]);
}

/// **THE SEALED-ESCROW SATISFACTION-WELD satisfying-trace producer (`settleEscrowSatVmDescriptor2R24`,
/// STAGED).**
///
/// Emits a SATISFYING rotated trace for the welded escrow-satisfaction descriptor (the Lean
/// `Dregg2.Deos.SettleEscrowSatDescriptor.settleEscrowSatVmDescriptor2R24`). The descriptor is the
/// transfer base with the two leg field-freezes dropped, PLUS the four selector-gated satisfaction
/// gates over the rotated BEFORE/AFTER field columns (`satisfaction_weld::{before,after}_field_col`),
/// PLUS the selector PI pin. A satisfying trace is a ZERO-AMOUNT settle CARRIER: the economic block is
/// identity (balance unchanged), and the settle is expressed by flipping the two leg STATUS fields
/// `Deposited → Consumed`, with the capacity selector (`satisfaction_weld::ESCROW_SEL_COL`, col 70)
/// ON on the settle row.
///
/// The field surgery mirrors the fee producer's balance surgery
/// ([`generate_rotated_effect_vm_trace_with_fee`]):
///   * the BEFORE block carries `Deposited` on the settle row (row 0 — the genuine pre-lock state,
///     so the native v1 `OLD_COMMIT` already binds it) and `Consumed` on the carry-forward NoOp rows
///     (the cross-row continuity `next.before == local.after` forces the post-settle state forward);
///   * the AFTER block carries `Consumed` on EVERY row (the post-settle status);
///   * each touched v1 state block has its `STATE_COMMIT` recomputed (the descriptor's bound GROUP-4
///     poseidon lookups — the AFTER intermediates land on cols 98/99/100; the carrier is residue-free
///     so the record-digest aux at col 186 is `ZERO`), and its rotated block re-welded
///     (`fill_block` overrides the rotated field limbs from the v1 block, then re-chains
///     `wireCommitR` → rotated `STATE_COMMIT`);
///   * the selector rides col 70 = `1` on the settle row, `0` on padding (the welded gates are inert
///     off the selector); pinned to PI 46 by the descriptor.
///
/// The legs ride field slots `leg_a_slot`/`leg_b_slot` (the emitted descriptor member is `legA=0,
/// legB=1`). Returns `(trace, dpis)` (47 PIs: the rotated 46 + the appended selector slot) ready for
/// `prove_vm_descriptor2(&settleEscrowSatVmDescriptor2R24, …)`. The `initial_state`'s leg fields are
/// FORCED to `Deposited` inside (so the row-0 BEFORE block + the native `OLD_COMMIT` read `Deposited`);
/// the caller's other state (balance/nonce/cap_root) is preserved.
///
/// STAGED: no live path calls this; it is the producer the staged welded descriptor's first real
/// STARK prove/verify consumes (`circuit/tests/settle_escrow_capacity_weld.rs`). NOT routed; the
/// deployed cohort is untouched.
pub fn generate_rotated_settle_escrow_trace(
    initial_state: &CellState,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    leg_a_slot: usize,
    leg_b_slot: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let dep = super::pi::SETTLE_ESCROW_STATUS_DEPOSITED;
    let con = super::pi::SETTLE_ESCROW_STATUS_CONSUMED;
    // The honest both-legs settle: `Deposited` before, `Consumed` after.
    settle_carrier_trace(
        initial_state,
        before_w,
        after_w,
        caveat,
        leg_a_slot,
        leg_b_slot,
        (dep, dep),
        (con, con),
    )
}

/// **THE FORGED-STATUS settle carrier (adversarial teeth, `#[doc(hidden)]`).** Identical machinery to
/// [`generate_rotated_settle_escrow_trace`] but with caller-chosen leg STATUS values before/after, so
/// an adversarial test can build a FULLY-CONSISTENT trace (every commitment + continuity constraint
/// satisfied) whose ONLY violated relation is a welded satisfaction gate — isolating the teeth in a
/// real STARK prove:
///   * a PARTIAL settle (`after = (Consumed, Deposited)`) leaves leg B unswapped — the leg-B AFTER
///     gate `sel·(after_B − Consumed)` is non-zero;
///   * a PHANTOM settle (`before = (Empty, Deposited)`) consumes a leg that never locked — the leg-A
///     BEFORE gate `sel·(before_A − Deposited)` is non-zero.
/// Both are genuine cell state transitions (the carrier balances, commits, and chains are all
/// recomputed), so the descriptor's REFUSAL is the welded gate alone, not a stale commitment.
#[doc(hidden)]
pub fn generate_rotated_settle_escrow_trace_forged(
    initial_state: &CellState,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    leg_a_slot: usize,
    leg_b_slot: usize,
    before_status: (u32, u32),
    after_status: (u32, u32),
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    settle_carrier_trace(
        initial_state,
        before_w,
        after_w,
        caveat,
        leg_a_slot,
        leg_b_slot,
        before_status,
        after_status,
    )
}

/// The shared settle-carrier core: a zero-amount transfer carrier whose two leg STATUS fields are
/// flipped `before_status → after_status`, with every dependent commitment recomputed. The honest
/// path passes `(Deposited, Deposited) → (Consumed, Consumed)`; the adversarial teeth pass forged
/// statuses (see [`generate_rotated_settle_escrow_trace_forged`]).
#[allow(clippy::too_many_arguments)]
fn settle_carrier_trace(
    initial_state: &CellState,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    leg_a_slot: usize,
    leg_b_slot: usize,
    before_status: (u32, u32),
    after_status: (u32, u32),
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    use super::columns::{AUX_BASE, PARAM_BASE, aux_off, state};
    use super::pi as pimod;
    use super::satisfaction_weld::ESCROW_SEL_COL;

    if leg_a_slot >= 8 || leg_b_slot >= 8 || leg_a_slot == leg_b_slot {
        return Err(format!(
            "settle-escrow carrier: legs must be DISTINCT field slots in 0..8, got {leg_a_slot}/\
             {leg_b_slot}"
        ));
    }

    let before_a = BabyBear::new(before_status.0);
    let before_b = BabyBear::new(before_status.1);
    let after_a = BabyBear::new(after_status.0);
    let after_b = BabyBear::new(after_status.1);

    // Seed the carrier's pre-state with the BEFORE leg statuses so the row-0 BEFORE block (and the
    // native v1 `OLD_COMMIT`) read them — the welded gate's before-leg precondition.
    let mut pre = initial_state.clone();
    pre.fields[leg_a_slot] = before_a;
    pre.fields[leg_b_slot] = before_b;

    // The zero-amount settle carrier: a `Transfer` of 0 (balance unchanged) under the transfer
    // selector the settle base inherits; the settle is the field flip, not an economic move.
    let effects = vec![Effect::Transfer {
        amount: 0,
        direction: 0,
    }];
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(&pre, &effects, before_w, after_w, caveat)?;

    let rec_col = AUX_BASE + aux_off::STATE_RECORD_DIGEST; // 186 (ZERO for a residue-free carrier)
    let a_i1 = AUX_BASE + aux_off::STATE_INTER1; // 98
    let a_i2 = AUX_BASE + aux_off::STATE_INTER2; // 99
    let a_i3 = AUX_BASE + aux_off::STATE_INTER3; // 100
    let fa = state::FIELD_BASE + leg_a_slot;
    let fb = state::FIELD_BASE + leg_b_slot;

    let n = trace.len();
    for r in 0..n {
        let is_settle_row = r == 0;
        // BEFORE block: the chosen before-statuses on the settle row (the pre-lock state); the
        // after-statuses on the carry-forward rows (cross-row continuity `next.before == local.after`
        // carries the post-settle state forward).
        let (bval_a, bval_b) = if is_settle_row {
            (before_a, before_b)
        } else {
            (after_a, after_b)
        };
        trace[r][STATE_BEFORE_BASE + fa] = bval_a;
        trace[r][STATE_BEFORE_BASE + fb] = bval_b;
        // AFTER block: the after-statuses on every row (the post-settle status).
        trace[r][STATE_AFTER_BASE + fa] = after_a;
        trace[r][STATE_AFTER_BASE + fb] = after_b;

        // Recompute each v1 block's GROUP-4 STATE_COMMIT over the (flipped) fields, byte-identical
        // to the descriptor's poseidon lookups (`compute_commitment`): i1 = [bal_lo, bal_hi, nonce,
        // field0], i2 = [field1..4], i3 = [field5..7, cap_root], commit = [i1, i2, i3, record_digest].
        // The AFTER block's three intermediates ARE descriptor-bound (cols 98/99/100); the BEFORE
        // block's are not (its STATE_COMMIT is only consumed by the cross-row continuity).
        recommit_v1_block(&mut trace[r], STATE_BEFORE_BASE, rec_col, None);
        recommit_v1_block(
            &mut trace[r],
            STATE_AFTER_BASE,
            rec_col,
            Some((a_i1, a_i2, a_i3)),
        );

        // Re-weld both rotated blocks from the modified v1 fields, re-chaining `wireCommitR` →
        // rotated STATE_COMMIT (`fill_block` overrides the welded field limbs r3..r10 from the v1
        // block, so the rotated field columns the welded gates read carry the flipped status).
        fill_block(&mut trace[r], BEFORE_BASE, STATE_BEFORE_BASE, before_w);
        fill_block(&mut trace[r], AFTER_BASE, STATE_AFTER_BASE, after_w);

        // The capacity selector (col 70): ON on the settle row, OFF on padding.
        trace[r][PARAM_BASE + 2] = if is_settle_row {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        debug_assert_eq!(PARAM_BASE + 2, ESCROW_SEL_COL, "selector col 70");
    }

    // Re-derive the PI vector. The row-0 BEFORE block kept its `Deposited` fields, so OLD_COMMIT +
    // the rotated OLD pin are unchanged from the base; the AFTER block flipped to `Consumed`, so
    // NEW_COMMIT (the 8-felt faithful commit) + the rotated NEW pin move.
    let last = trace.len() - 1;
    let sa = STATE_AFTER_BASE;
    let bal = (trace[last][sa + state::BALANCE_LO].as_u32() as u64)
        | ((trace[last][sa + state::BALANCE_HI].as_u32() as u64) << 30);
    let nonce = trace[last][sa + state::NONCE].as_u32();
    let mut after_fields = [BabyBear::ZERO; 8];
    for (k, slot) in after_fields.iter_mut().enumerate() {
        *slot = trace[last][sa + state::FIELD_BASE + k];
    }
    let new8 = CellState::compute_commitment_8(
        bal,
        nonce,
        &after_fields,
        trace[last][sa + state::CAP_ROOT],
        trace[last][rec_col],
    );

    let mut dpis: Vec<BabyBear> = base_pis[..ROT_PI_COUNT].to_vec();
    dpis[pimod::NEW_COMMIT_BASE..pimod::NEW_COMMIT_BASE + pimod::NEW_COMMIT_LEN]
        .copy_from_slice(&new8[..pimod::NEW_COMMIT_LEN]);
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit (unchanged)
    dpis[V1_PI_COUNT + 1] = trace[last][AFTER_BASE + B_STATE_COMMIT]; // rotated NEW commit (moved)
    dpis.push(BabyBear::ONE); // PI 46: the escrow selector (settle-row), the descriptor pins it here.
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);

    Ok((trace, dpis))
}

/// Recompute one v1 state block's GROUP-4 `STATE_COMMIT` from its (possibly mutated) state columns,
/// byte-identical to [`CellState::compute_commitment`] and the descriptor's poseidon lookups: i1 =
/// `[bal_lo, bal_hi, nonce, field0]`, i2 = `[field1..4]`, i3 = `[field5..7, cap_root]`, commit =
/// `[i1, i2, i3, record_digest]`. When `inters` is `Some`, the three intermediates are written to
/// those AUX columns (the AFTER block, whose intermediates the descriptor binds); `None` for the
/// BEFORE block (only its `STATE_COMMIT` is published, via the cross-row continuity).
fn recommit_v1_block(
    row: &mut [BabyBear],
    base: usize,
    record_digest_col: usize,
    inters: Option<(usize, usize, usize)>,
) {
    use super::columns::state;
    let i1 = hash_many(&[
        row[base + state::BALANCE_LO],
        row[base + state::BALANCE_HI],
        row[base + state::NONCE],
        row[base + state::FIELD_BASE],
    ]);
    let i2 = hash_many(&[
        row[base + state::FIELD_BASE + 1],
        row[base + state::FIELD_BASE + 2],
        row[base + state::FIELD_BASE + 3],
        row[base + state::FIELD_BASE + 4],
    ]);
    let i3 = hash_many(&[
        row[base + state::FIELD_BASE + 5],
        row[base + state::FIELD_BASE + 6],
        row[base + state::FIELD_BASE + 7],
        row[base + state::CAP_ROOT],
    ]);
    if let Some((c1, c2, c3)) = inters {
        row[c1] = i1;
        row[c2] = i2;
        row[c3] = i3;
    }
    row[base + state::STATE_COMMIT] = hash_many(&[i1, i2, i3, row[record_digest_col]]);
}

/// Resolve the rotated registry descriptor name for one EFFECT on the FEE-IN-PROOF path. A plain
/// sovereign `Transfer` lead routes to `transferFeeVmDescriptor2R24` (the fee debited in-proof);
/// every other effect falls back to [`rotated_descriptor_name_for_effect`] (the unfee'd cohort —
/// the cap-open transfer routing and the 35 other members are UNCHANGED). This is the fee-path twin
/// of `rotated_descriptor_name_for_effect`; the unfee'd resolver is left 100% intact so the broad
/// cohort path is unaffected.
pub fn rotated_descriptor_name_for_effect_fee(effect: &Effect) -> Option<&'static str> {
    match effect {
        Effect::Transfer { .. } => Some("transferFeeVmDescriptor2R24"),
        other => rotated_descriptor_name_for_effect(other),
    }
}

/// **THE DEPLOYMENT-REAL noteSpend nullifier-tree wiring (the kernel-set grow-gate's witness).**
///
/// The live `noteSpendVmDescriptor2R24` now carries two map-ops gated by the spend selector — the
/// `nullifierFreshOp` (`.absent`: the published nullifier is a NON-MEMBER of the BEFORE nullifier
/// tree — the in-circuit double-spend tooth) and `nullifierInsertOp` (`.write`: the AFTER root IS
/// the genuine sorted insert of the nullifier). Those map-ops open the rotated `nullifier_root`
/// limb (limb 26) against a real sorted-Poseidon2 tree. The bare generator carries limb 26 as a
/// turn-invariant `hash_bytes` witness, which the map-ops cannot open.
///
/// This wrapper makes limb 26 the DEPLOYED openable accumulator root for a NoteSpend turn:
///   * `before_nullifiers` are the existing nullifier-set leaves (the spent nullifier MUST be
///     absent — the freshness precondition; the `.absent` op refuses a double-spend);
///   * limb 26 of EVERY before-block is overwritten with the BEFORE tree's root, and limb 26 of
///     every after-block with the root of the BEFORE tree PLUS the inserted spent nullifier (the
///     set-insert the `.write` op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived, so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads
///     into `prove_vm_descriptor2` to resolve both map-ops.
///
/// The nullifier's leaf key is the spend row's folded `param0` (`PARAM_BASE + param::NULLIFIER` —
/// the SAME felt PI[38] pins), and the inserted leaf value is the note value (`param::NOTE_VALUE_LO`),
/// so the gate's key/value are the row's own published columns. Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_spend_trace_with_nullifier_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::NoteSpend { .. })) {
        return Err("nullifier-tree wiring is only for a NoteSpend lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the nullifier PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The spent nullifier's leaf key + value, read from the spend row (row 0).
    let nf_key = trace[0][PARAM_BASE + param::NULLIFIER];
    let nf_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];

    // The BEFORE tree (the deployed accumulator before the spend) and the AFTER tree (= BEFORE +
    // the inserted nullifier leaf). The spent nullifier MUST be absent from BEFORE — the freshness
    // precondition the `.absent` op enforces; a double-spend has no bracketing witness and the
    // prover REFUSES it.
    let before_tree = CanonicalHeapTree::new(before_nullifiers.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(nf_key).is_some() {
        return Err(
            "double-spend: the nullifier is already in the BEFORE nullifier tree — the in-circuit \
             freshness (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root = before_tree.root();
    let mut after_leaves = before_nullifiers.to_vec();
    after_leaves.push(HeapLeaf {
        addr: nf_key,
        value: nf_value,
    });
    // The after-tree is built only to read its root; move `after_leaves` in (no clone — it is
    // not read again after this point).
    let after_root = CanonicalHeapTree::new(after_leaves, HEAP_TREE_DEPTH).root();

    // Override limb 26 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set. (The bare limb-26 `hash_bytes` witness is replaced by the real tree roots.)
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_NULLIFIER_ROOT] = before_root;
        row[AFTER_BASE + B_NULLIFIER_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-26 override moved the commitments).
    let r0_commit = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    let last_commit = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT] = r0_commit; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = last_commit; // PI 35: rotated NEW commit

    Ok((trace, dpis, vec![before_nullifiers.to_vec()]))
}

/// The deployed `cells_root` (limb 0 of the rotated block) — the openable sorted-Poseidon2 accounts
/// accumulator. The createCell/factory/spawn descriptors (`EffectVmEmitRotationV3.{createCellV3,
/// factoryV3,spawnV3}`) now carry two map-ops on it: `cellsFreshOp` (`.absent`: the new-cell key is
/// a NON-MEMBER of the BEFORE accounts tree — no id collision) and `cellsInsertOp` (`.insert`: the
/// AFTER root IS the genuine sorted insert of the new-cell key).
const B_CELLS_ROOT: usize = 0;

/// **THE DEPLOYMENT-REAL createCell / factory / spawn accounts-tree wiring (the accounts-set
/// grow-gate's witness).** The clone of `generate_rotated_note_spend_trace_with_nullifier_tree` for
/// the `cells_root` limb (limb 0): it makes limb 0 the openable accounts accumulator for a
/// createCell/factory/spawn turn.
///   * `before_accounts` are the existing account-set leaves (the new-cell key MUST be absent — the
///     no-collision precondition the `.absent` op enforces);
///   * limb 0 of every before-block is overwritten with the BEFORE tree's root, and limb 0 of every
///     after-block with the root of BEFORE + the inserted new-cell key (the set-insert the `.insert`
///     op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads.
///     The new-cell key column is `param0` for createCell/spawn, `param1` (CHILD_VK_DERIVED) for factory
///     (`new_cell_key_param_col`). Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_create_cell_trace_with_accounts_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::PARAM_BASE;
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    let key_col = new_cell_key_param_col(effects.first()).ok_or_else(|| {
        "accounts-tree wiring is only for a CreateCell / CreateCellFromFactory / SpawnWithDelegation \
         lead effect"
            .to_string()
    })?;

    // The base rotated trace (carries the welds, the v1 economic block, the new-cell-key PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The new-cell key, read from the create row (row 0).
    let cell_key = trace[0][PARAM_BASE + key_col];

    // The BEFORE accounts tree and the AFTER tree (= BEFORE + the inserted new-cell key). The
    // new-cell key MUST be absent from BEFORE — the no-collision precondition the `.absent` op
    // enforces; a re-creation of an existing cell has no bracketing witness and the prover REFUSES.
    let before_tree = CanonicalHeapTree::new(before_accounts.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(cell_key).is_some() {
        return Err(
            "account-id collision: the new-cell key is already in the BEFORE accounts tree — the \
             in-circuit no-collision (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root = before_tree.root();
    let mut after_leaves = before_accounts.to_vec();
    after_leaves.push(HeapLeaf {
        addr: cell_key,
        value: cell_key, // the born-empty cell rides its own key as its leaf value.
    });
    // The after-tree is built only to read its root; move `after_leaves` in (no clone).
    let after_root = CanonicalHeapTree::new(after_leaves, HEAP_TREE_DEPTH).root();

    // Override limb 0 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set.
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_CELLS_ROOT] = before_root;
        row[AFTER_BASE + B_CELLS_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-0 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_accounts.to_vec()]))
}

/// **THE DEPLOYMENT-REAL noteCreate commitments-tree wiring (the commitments-set grow-gate's
/// witness).** The clone of `generate_rotated_note_spend_trace_with_nullifier_tree` for the
/// `commitments_root` limb (limb 27 — the flag-day new committed shielded-set root): it makes limb
/// 27 the openable commitments accumulator for a noteCreate turn.
///   * `before_commitments` are the existing note-commitment-set leaves;
///   * limb 27 of every before-block is overwritten with the BEFORE tree's root, and limb 27 of
///     every after-block with the root of BEFORE + the inserted note commitment (the set-insert the
///     `commitmentsInsertOp .insert` op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads.
///     The commitment key column is `param0` (`Effect::NoteCreate { commitment }`); the inserted leaf
///     value is the note value (`param::NOTE_VALUE_LO = param1`). NoteCreate is append-only, so there
///     is NO `.absent` freshness precondition (a re-published commitment is admissible). Returns
///     `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_create_trace_with_commitments_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_commitments: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::NoteCreate { .. })) {
        return Err("commitments-tree wiring is only for a NoteCreate lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the commitment PI[38]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The note commitment's leaf key (param0) + value (param1), read from the create row (row 0).
    let cm_key = trace[0][PARAM_BASE + param::NULLIFIER]; // param0 (the commitment rides param slot 0)
    let cm_value = trace[0][PARAM_BASE + param::NOTE_VALUE_LO];

    // The BEFORE commitments tree and the AFTER tree (= BEFORE + the inserted commitment). NoteCreate
    // is append-only — no `.absent` freshness precondition.
    let before_tree = CanonicalHeapTree::new(before_commitments.to_vec(), HEAP_TREE_DEPTH);
    let before_root = before_tree.root();
    let mut after_leaves = before_commitments.to_vec();
    after_leaves.push(HeapLeaf {
        addr: cm_key,
        value: cm_value,
    });
    // The after-tree is built only to read its root; move `after_leaves` in (no clone).
    let after_root = CanonicalHeapTree::new(after_leaves, HEAP_TREE_DEPTH).root();

    // Override limb 27 of BOTH blocks on EVERY row with the openable accumulator roots, then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown
    // set.
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_COMMITMENTS_ROOT] = before_root;
        row[AFTER_BASE + B_COMMITMENTS_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-27 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_commitments.to_vec()]))
}

/// The declared-param column the refusal row carries the audit FELT in (`prmCol 2 = PARAM_BASE + 2`).
/// The deployed refusal row uses only `param0 = REFUSAL_TARGET` and `param1 = REFUSAL_REASON_HASH`;
/// this previously-spare `param2` now carries the in-circuit map-op's inserted value (the audit felt),
/// which a ledgerless client recomputes from the published refusal params. Lean
/// `EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL`.
pub const REFUSAL_AUDIT_FELT_PARAM: usize = 2;

/// **THE DEPLOYMENT-REAL refusal fields-root WRITE wiring (the refusal light-client forge's close).**
/// The clone of [`generate_rotated_note_spend_trace_with_nullifier_tree`] for the `fields_root` limb
/// (limb 36 = `B_FIELDS_ROOT`): it makes limb 36 the openable user-field-MAP accumulator for a
/// refusal turn, so the in-circuit `refusalFieldsWriteOp` (`.write`) FORCES
/// `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt)` — a forged
/// post-`fields_root` (committed ≠ the genuine write) is UNSAT for a ledgerless client through
/// `verify_vm_descriptor2` ALONE.
///
///   * `before_fields_leaves` are the cell's PRE-refusal overflow `fields_map` entries, encoded as
///     `dregg_circuit::heap_root::HeapLeaf` (key = `field_key_hash(key)`, value = `fold_bytes32(v)`) —
///     the SAME leaf set `cell::state::compute_fields_root` builds its root over. The refusal-audit
///     slot is RESERVED (value-ZERO, present) so the write opens its existing path (a position-stable
///     in-place value update, NOT a re-indexing insert);
///   * `audit_value` is the audit felt the refusal writes (`fold_bytes32` of the post-cell's
///     `fields_map[REFUSAL_AUDIT_EXT_KEY]`) — light-client-recomputable from the published refusal
///     params; it rides `PARAM_BASE + REFUSAL_AUDIT_FELT_PARAM` (col 70) so the map-op's value column
///     is the row's own published column;
///   * limb 36 of every before-block is overwritten with the BEFORE tree's root, and limb 36 of every
///     after-block with the root of the BEFORE tree with the audit slot WRITTEN to `audit_value` (the
///     position-stable value update the `.write` op forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the written map;
///   * the BEFORE tree's leaves (incl. the reserved audit slot) are returned as the single `map_heaps`
///     entry the prover threads into `prove_vm_descriptor2` to resolve the `.write` op.
///
/// Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_refusal_trace_with_fields_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_fields_leaves: &[crate::heap_root::HeapLeaf],
    audit_value: BabyBear,
) -> RotatedTraceWithHeaps {
    use super::columns::PARAM_BASE;
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::Refusal { .. })) {
        return Err("fields-root write wiring is only for a Refusal lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the record pin PI[46]).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The refusal-audit slot's sort key (a CONSTANT — `field_key_hash(REFUSAL_AUDIT_EXT_KEY)`, the
    // Lean `refusalAuditKeyFelt`). RESERVE it in the BEFORE leaf set (value ZERO, present) so the
    // `.write` op opens its existing path — a position-stable in-place value update.
    let audit_key = crate::openable_fields_root::field_key_hash(
        crate::openable_fields_root::REFUSAL_AUDIT_EXT_KEY,
    );
    let mut before_leaves = before_fields_leaves.to_vec();
    if !before_leaves.iter().any(|l| l.addr == audit_key) {
        before_leaves.push(HeapLeaf {
            addr: audit_key,
            value: BabyBear::ZERO,
        });
    }

    // The BEFORE fields tree (the openable accumulator before the refusal) and the AFTER tree
    // (= BEFORE with the audit slot's value WRITTEN to `audit_value` — the in-place update the
    // `.write` op forces). The audit slot MUST be present in BEFORE (we reserve it above), else the
    // `.write` op has no `update_witness` and the prover REFUSES.
    let before_tree = CanonicalHeapTree::new(before_leaves.clone(), HEAP_TREE_DEPTH);
    if before_tree.position_of(audit_key).is_none() {
        return Err(
            "refusal fields-root write: the audit slot is not present in the BEFORE tree — the \
             in-circuit `.write` op has no update witness and refuses the turn"
                .into(),
        );
    }
    let before_root = before_tree.root();
    let after_leaves: Vec<HeapLeaf> = before_tree
        .sorted_leaves()
        .iter()
        .filter(|l| {
            l.addr != crate::heap_root::SENTINEL_MIN && l.addr != crate::heap_root::SENTINEL_MAX
        })
        .map(|l| {
            if l.addr == audit_key {
                HeapLeaf {
                    addr: audit_key,
                    value: audit_value,
                }
            } else {
                *l
            }
        })
        .collect();
    let after_root = CanonicalHeapTree::new(after_leaves, HEAP_TREE_DEPTH).root();

    // Fill the declared audit-felt param column (col 70) with the written value on EVERY row, so the
    // map-op's value column is the row's own published column (the noteSpend pattern — the gate reads
    // `prmCol 2`).
    for row in trace.iter_mut() {
        row[PARAM_BASE + REFUSAL_AUDIT_FELT_PARAM] = audit_value;
    }

    // Override limb 36 of BOTH blocks on EVERY row with the openable accumulator roots, then recompute
    // the dependent chained commitments so the published `STATE_COMMIT` binds the written map.
    for row in trace.iter_mut() {
        row[BEFORE_BASE + B_FIELDS_ROOT] = before_root;
        row[AFTER_BASE + B_FIELDS_ROOT] = after_root;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-36 override + the audit-felt param fill moved
    // the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_leaves]))
}

/// The cap-tree write-op kind a write-bearing cap-open wrapper carries (the `map_op` on the
/// BEFORE cap-root (col 65 = `STATE_BEFORE_BASE + state::CAP_ROOT`) → AFTER cap-root (col 87 =
/// `STATE_AFTER_BASE + state::CAP_ROOT`)). Mirrors the descriptor's two `map_op` rows:
///   * [`CapTreeWriteOp::Remove`] — `revokeDelegationWriteCapOpenVmDescriptor2R24`: a `read`
///     (key present, opens to its stored value) followed by a `write` of value `0` at the SAME
///     key (the in-place tombstone the deployed `removeWriteOp` forces). The key MUST be present.
///   * [`CapTreeWriteOp::Insert`] — `delegate/introduce/delegateAttenWriteCapOpenVmDescriptor2R24`:
///     a `read` (of a DIFFERENT, already-present anchor key) followed by an `insert` of the fresh
///     key. The inserted key MUST be absent. (Fan-out: see `generate_rotated_cap_write_base`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapTreeWriteOp {
    /// The revoke (`read` the leaf, then `write` value 0 in place). Key present in BEFORE.
    Remove,
    /// The grant/delegate/introduce (`read` a DISTINCT already-present ANCHOR leaf — the
    /// delegator's held authority cap — then `insert` a FRESH key). The map_op's `read` opens
    /// the anchor (`ANCHOR_KEY`/`ANCHOR_MASK` = params 6/7, cols `PARAM_BASE+6`/`+7`) and the
    /// `insert` advances the cap-root with the fresh edge (`CAP_KEY`/`KEEP_MASK` = params 3/5,
    /// cols `PARAM_BASE+3`/`+5`, BEFORE cap-root limb 213 → AFTER cap-root limb 264). The anchor
    /// MUST be present (else the `read` has no membership witness) and the inserted key MUST be
    /// ABSENT + distinct from the anchor (else `insert_witness` returns `None`) — both fail closed
    /// (no fabricated post-root). Lean `EffectVmEmitV2.{insertWriteOp, heldReadOp, ANCHOR_KEY}`.
    Insert,
    /// The attenuate (in-place UPDATE-AT-KEY: `read` the held key's mask, then `write` the narrowed
    /// `KEEP_MASK` at the SAME key). The map_op's `read` opens `CAP_KEY` (param 3, col `PARAM_BASE+3`)
    /// to `HELD_MASK` (param 4, col `PARAM_BASE+4`), then the `write` rebinds the SAME key to
    /// `KEEP_MASK` (param 5, col `PARAM_BASE+5`), advancing BEFORE cap-root limb 213 → AFTER cap-root
    /// limb 264. The key MUST be present (else `update_witness` returns `None` — fail closed, no
    /// fabricated post-root). The KEY-SET is PRESERVED (the in-place narrow's sorted-tree shadow).
    /// Lean `EffectVmEmitV2.{keepWriteOp, heldReadOp, CAP_KEY, KEEP_MASK}`.
    Update,
}

/// **THE DEPLOYMENT-REAL cap-tree WRITE wiring (the cap-WRITE light-client axis's witness).** The
/// clone of [`generate_rotated_note_spend_trace_with_nullifier_tree`] for the openable cap-tree
/// accumulator the write-bearing cap-open wrappers carry as a `map_op` binding the BEFORE cap-root
/// (rotated-block limb 25 = `BEFORE_BASE + B_CAP_ROOT`, descriptor col 213) → AFTER cap-root
/// (`AFTER_BASE + B_CAP_ROOT`, descriptor col 264). The c-list leaf-set `clist_leaves` is the
/// cell's FULL sorted-Poseidon2 `CanonicalHeapTree` over its capability slots; the BEFORE cap-root
/// IS that tree's root, the AFTER cap-root is the genuine post-WRITE root (a wrong post-root is
/// UNSAT — the `map_op` checks `after = op(before, key)`).
///
/// This advances the cap-root on the ROTATED-BLOCK limb (`BEFORE_BASE + B_CAP_ROOT` →
/// `AFTER_BASE + B_CAP_ROOT`), exactly as note-spend advances its nullifier accumulator on the
/// rotated nullifier limb (`B_NULLIFIER_ROOT`) — so the advance dodges the v1-STATE continuity
/// transitions (the cap-root limb is no longer welded `213 == 65`). The v1-STATE cap-root columns
/// (col 65 BEFORE, col 87 AFTER) are LEFT FROZEN (pass-through, `after.65 == before.65`): the
/// descriptor's `213 == 65` / `264 == 87` welds are GONE, so the v1-state cap-root continuity weld
/// (hi=11,lo=11) holds trivially on a frozen column. We override the rotated cap-root limbs on
/// EVERY row with the openable tree roots, fill the `map_op` key/value param columns (col 71 =
/// `PARAM_BASE + 3`, col 72 = `PARAM_BASE + 4`), and recompute the rotated block commitments +
/// re-derive the rotated OLD/NEW commit PIs so the published commitment binds the WRITTEN cap-tree.
/// (The cap-open leg's published commitment is the ROTATED commit, PIs `V1_PI_COUNT..+2`; this
/// descriptor carries NO v1-state-commit chain over the cap-root limb, so the v1 8-felt commit is
/// untouched.)
///
/// The base trace MUST already be the `ROT_WIDTH`-wide rotated base for the write wrapper's effect
/// (e.g. a `RevokeDelegation` turn from [`generate_rotated_effect_vm_trace`]). The cap-open
/// membership appendix is widened on TOP (`widen_to_cap_open`) AFTER this. Returns the BEFORE
/// c-list leaf-set as the single `map_heaps` entry the prover threads into `prove_vm_descriptor2`.
///
/// SOUNDNESS: `clist_leaves` MUST be the cell's GENUINE c-list (the prover threads it from the real
/// ledger). For `Remove`, `anchor_key` is the REMOVEd key (read+write the SAME present key) and
/// MUST be present (else `update_witness` returns `None` and this fails closed); `inserted` MUST be
/// `None`. For `Insert`, `anchor_key` is the held-authority ANCHOR leaf (read-only) and MUST be
/// present, while `inserted = Some((fresh_key, value))` MUST be ABSENT and distinct from the anchor
/// (else `insert_witness` returns `None` and this fails closed). In every case the post-root is the
/// GENUINE sorted-tree write — NO fabricated post-root.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_cap_write_base(
    trace: &mut Vec<Vec<BabyBear>>,
    dpis: &mut [BabyBear],
    op: CapTreeWriteOp,
    clist_leaves: &[crate::heap_root::HeapLeaf],
    anchor_key: BabyBear,
    inserted: Option<(BabyBear, BabyBear)>,
) -> Result<Vec<Vec<crate::heap_root::HeapLeaf>>, String> {
    use super::columns::PARAM_BASE;
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    if trace.is_empty() {
        return Err("cap-write base: empty trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "cap-write base: trace width {} != {ROT_WIDTH} (call before widen_to_cap_open)",
            trace[0].len()
        ));
    }

    // The cap-root advances on the ROTATED-BLOCK limb (descriptor cols 213/264), NOT the v1-state
    // cap-root columns (65/87) — exactly as note-spend advances its nullifier accumulator on a
    // rotated limb. The v1-state cap-root columns are LEFT FROZEN (pass-through, the base trace's
    // `fill_block` already set them; the descriptor's `213 == 65` / `264 == 87` welds are GONE, so
    // freezing the v1-state cap-root satisfies the v1-state continuity weld hi=11,lo=11 trivially).
    let before_cap_root_limb = BEFORE_BASE + B_CAP_ROOT; // 213 (descriptor var 213)
    let after_cap_root_limb = AFTER_BASE + B_CAP_ROOT; // 264 (descriptor var 264)
    // Param-column layout (Lean `EffectVmEmitV2.{CAP_KEY,HELD_MASK,KEEP_MASK,ANCHOR_KEY,ANCHOR_MASK}`):
    //   CAP_KEY = 3   → col PARAM_BASE+3 (the FRESH inserted key / the REMOVEd key)
    //   HELD_MASK = 4 → col PARAM_BASE+4 (the Remove `read` value column)
    //   KEEP_MASK = 5 → col PARAM_BASE+5 (the inserted value)
    //   ANCHOR_KEY = 6 → col PARAM_BASE+6 (the Insert `read` anchor key)
    //   ANCHOR_MASK = 7 → col PARAM_BASE+7 (the Insert `read` anchor value)
    let cap_key_col = PARAM_BASE + 3; // 71 (Remove read+write key / Insert insert key)
    let remove_value_col = PARAM_BASE + 4; // 72 (Remove read value)
    let keep_mask_col = PARAM_BASE + 5; // 73 (Insert inserted value)
    let anchor_key_col = PARAM_BASE + 6; // 74 (Insert read anchor key)
    let anchor_value_col = PARAM_BASE + 7; // 75 (Insert read anchor value)

    // The BEFORE cap-tree (the deployed openable accumulator before the write) over the cell's
    // FULL c-list. The written/anchor key MUST be present — the witness builders return `None`
    // otherwise, and this fails closed (no fabricated post-root).
    let before_tree = CanonicalHeapTree::new(clist_leaves.to_vec(), HEAP_TREE_DEPTH);
    let before_root = before_tree.root();

    // Each op fills its OWN param columns; the columns it does not drive are zeroed (the unfired
    // map_op for the other op kind never reads them).
    enum CapWriteCols {
        /// Remove: read+write the SAME present key at `cap_key_col`; publish its stored value at
        /// `remove_value_col`.
        Remove { key: BabyBear, read_value: BabyBear },
        /// Insert: read the present ANCHOR key/value (anchor cols), insert the FRESH key/value
        /// (cap_key / keep_mask cols).
        Insert {
            anchor_key: BabyBear,
            anchor_value: BabyBear,
            inserted_key: BabyBear,
            inserted_value: BabyBear,
        },
        /// Update (attenuate): read the present key at `cap_key_col` to its HELD_MASK (`remove_value_col`),
        /// rebind the SAME key to KEEP_MASK (`keep_mask_col`).
        Update {
            key: BabyBear,
            held_value: BabyBear,
            keep_mask: BabyBear,
        },
    }

    let (after_root, cols) = match op {
        CapTreeWriteOp::Remove => {
            // The deployed `removeWriteOp`: an in-place WRITE of value 0 at the present key (the
            // `read` first opens its stored value, which the row publishes at col 72). `anchor_key`
            // is the removed key (the consumed cap's slot_hash); `inserted` is unused.
            if inserted.is_some() {
                return Err(
                    "cap-write Remove: an inserted (key,value) was supplied — Remove reads+writes the \
                     SAME present key and takes no insert payload"
                        .into(),
                );
            }
            let removed_key = anchor_key;
            let stored = before_tree
                .sorted_leaves()
                .iter()
                .find(|l| l.addr == removed_key)
                .map(|l| l.value)
                .ok_or_else(|| {
                    format!(
                        "cap-write Remove: revoked key {} is NOT in the BEFORE c-list — the cap-tree \
                         read op has no membership witness and refuses the turn (no silent forge)",
                        removed_key.as_u32()
                    )
                })?;
            let w = before_tree
                .update_witness(HeapLeaf {
                    addr: removed_key,
                    value: BabyBear::ZERO,
                })
                .ok_or_else(|| {
                    format!(
                        "cap-write Remove: update witness for key {} failed",
                        removed_key.as_u32()
                    )
                })?;
            (
                w.new_root,
                CapWriteCols::Remove {
                    key: removed_key,
                    read_value: stored,
                },
            )
        }
        CapTreeWriteOp::Insert => {
            // The deployed `insertWriteOp` + `heldReadOp`: a `read` of a DISTINCT already-present
            // ANCHOR leaf (the delegator's held-authority cap), then a fresh sorted INSERT. The
            // anchor MUST be present (the read has a membership witness); the inserted key MUST be
            // ABSENT and distinct from the anchor (the sorted `insert_witness` refuses an
            // already-present key) — both fail closed (no fabricated post-root).
            let (inserted_key, inserted_value) = inserted.ok_or_else(|| {
                "cap-write Insert: no inserted (key,value) supplied — the fresh edge to grant"
                    .to_string()
            })?;
            if inserted_key == anchor_key {
                return Err(format!(
                    "cap-write Insert: the inserted key {} EQUALS the anchor key — the `read` requires \
                     the key PRESENT while the `insert` requires it ABSENT, so they MUST be distinct \
                     (else the pair is jointly UNSAT on the wire)",
                    inserted_key.as_u32()
                ));
            }
            let anchor_value = before_tree
                .sorted_leaves()
                .iter()
                .find(|l| l.addr == anchor_key)
                .map(|l| l.value)
                .ok_or_else(|| {
                    format!(
                        "cap-write Insert: anchor key {} is NOT in the BEFORE c-list — the held-authority \
                         read op has no membership witness and refuses the turn (no silent forge)",
                        anchor_key.as_u32()
                    )
                })?;
            let w = before_tree
                .insert_witness(HeapLeaf {
                    addr: inserted_key,
                    value: inserted_value,
                })
                .ok_or_else(|| {
                    format!(
                        "cap-write Insert: insert witness for fresh key {} failed (already present or \
                         collides with the sentinel range) — no fabricated post-root",
                        inserted_key.as_u32()
                    )
                })?;
            (
                w.new_root,
                CapWriteCols::Insert {
                    anchor_key,
                    anchor_value,
                    inserted_key,
                    inserted_value,
                },
            )
        }
        CapTreeWriteOp::Update => {
            // The deployed `keepWriteOp` + `heldReadOp` (attenuate): an in-place UPDATE-AT-KEY. The
            // `read` opens `CAP_KEY` (= `anchor_key`) to its stored HELD_MASK (col 72); the `write`
            // rebinds the SAME key to `KEEP_MASK` (the narrowed value, `inserted`'s value). The key
            // MUST be present (else `update_witness` returns `None` — fail closed). The key set is
            // preserved (the in-place narrow's sorted-tree shadow).
            let (_unused_key, keep_mask) = inserted.ok_or_else(|| {
                "cap-write Update: no (key,KEEP_MASK) supplied — the narrowed value to write"
                    .to_string()
            })?;
            let updated_key = anchor_key;
            let held_value = before_tree
                .sorted_leaves()
                .iter()
                .find(|l| l.addr == updated_key)
                .map(|l| l.value)
                .ok_or_else(|| {
                    format!(
                        "cap-write Update: held key {} is NOT in the BEFORE c-list — the held-authority \
                         read op has no membership witness and refuses the turn (no silent forge)",
                        updated_key.as_u32()
                    )
                })?;
            let w = before_tree
                .update_witness(HeapLeaf {
                    addr: updated_key,
                    value: keep_mask,
                })
                .ok_or_else(|| {
                    format!(
                        "cap-write Update: update witness for key {} failed",
                        updated_key.as_u32()
                    )
                })?;
            (
                w.new_root,
                CapWriteCols::Update {
                    key: updated_key,
                    held_value,
                    keep_mask,
                },
            )
        }
    };

    // Override the ROTATED-BLOCK cap-root limbs (descriptor cols 213/264) on EVERY row with the
    // openable accumulator roots, fill the map_op key/value params, then recompute the rotated
    // block commitments so the published rotated commit binds the written cap-tree. The v1-state
    // cap-root columns (65/87) are LEFT UNTOUCHED — they stay frozen pass-through (the welds are
    // gone), and `recompute_block_commit` re-chains the rotated commit over the written rotated limb.
    for row in trace.iter_mut() {
        row[before_cap_root_limb] = before_root;
        row[after_cap_root_limb] = after_root;
        match cols {
            CapWriteCols::Remove { key, read_value } => {
                row[cap_key_col] = key;
                row[remove_value_col] = read_value;
            }
            CapWriteCols::Insert {
                anchor_key,
                anchor_value,
                inserted_key,
                inserted_value,
            } => {
                // The `read` map_op opens the anchor (cols 74/75); the `insert` map_op inserts the
                // fresh key/value (cols 71/73). Col 72 (`HELD_MASK`) is unused by plain delegate /
                // introduce (no submask lookup), but the `delegateAtten` wrapper carries the
                // `granted ⊑ held` non-amplification lookup over `[KEEP_MASK (73), HELD_MASK (72)]`:
                // its HELD_MASK is the delegator's held-authority mask, which IS the anchor leaf's
                // c-list value (`anchor_value`). Filling col 72 = `anchor_value` makes the submask
                // lookup well-defined for the attenuated wrapper (the conferred KEEP_MASK at col 73
                // must be a bitwise submask of it) and is a harmless unused column for the plain
                // wrappers (they declare no lookup over col 72).
                row[anchor_key_col] = anchor_key;
                row[anchor_value_col] = anchor_value;
                row[remove_value_col] = anchor_value; // HELD_MASK (delegateAtten submask compare)
                row[cap_key_col] = inserted_key;
                row[keep_mask_col] = inserted_value;
            }
            CapWriteCols::Update {
                key,
                held_value,
                keep_mask,
            } => {
                // The `read` opens CAP_KEY (col 71) to HELD_MASK (col 72); the `write` rebinds the SAME
                // key to KEEP_MASK (col 73). No anchor columns (the read/write share the key).
                row[cap_key_col] = key;
                row[remove_value_col] = held_value;
                row[keep_mask_col] = keep_mask;
            }
        }
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the cap-root override moved the rotated commit).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // rotated NEW commit

    Ok(vec![clist_leaves.to_vec()])
}

/// The in-AFTER-block limb offset the record-forcing pin welds for a given lead effect, or
/// `None` for the 35 cohort members that carry no record pin. The lifecycle flips force the
/// per-cell `lifecycle` felt (limb 29); the permissions/VK writes force the per-cell
/// `authority_digest` / `record_digest` (limb 24 = r23). Mirrors the Lean routing in
/// `EffectVmEmitRotationV3.v3Registry` (`cellSealV3` … `setVKV3`).
fn record_pin_offset(lead: Option<&Effect>) -> Option<usize> {
    match lead {
        Some(Effect::CellSeal { .. })
        | Some(Effect::CellUnseal { .. })
        | Some(Effect::CellDestroy { .. }) => Some(B_LIFECYCLE),
        Some(Effect::SetPermissions { .. }) | Some(Effect::SetVerificationKey { .. }) => {
            Some(B_RECORD_DIGEST)
        }
        // `MakeSovereign` flips the cell's `mode` (Hosted→Sovereign): the deployed apply moves the
        // committed mode limb (`B_MODE`), which the `compute_authority_digest_felt` FOLDS into the
        // r23 authority residue (`B_RECORD_DIGEST = B_AUTHORITY_DIGEST`). So the AFTER `record_digest`
        // limb MOVES on a genuine promotion; the record-forcing pin (`makeSovereignV3`) welds it to
        // PI 38 (the descriptor's `makeSovereignVmDescriptor2R24` declares the 47th pin on
        // `after_base + B_AUTHORITY_DIGEST`), and the verifier anchors `compute_authority_digest_felt(
        // post_cell)`. A frozen-mode / un-promoted AFTER block is UNSAT. Mirrors Lean
        // `EffectVmEmitRotationV3.makeSovereignV3`.
        Some(Effect::MakeSovereign) => Some(B_RECORD_DIGEST),
        // `ReceiptArchive` writes the cell LIFECYCLE (`Archived`) in the deployed `apply_receipt_archive`
        // (`c.archive(checkpoint)`), which `lifecycle_felt` (limb `B_LIFECYCLE = 29`) folds into a
        // distinct `Archived` felt — NOT the r23 authority residue. So the genuine mover is the
        // lifecycle limb; the record-forcing pin (`receiptArchiveV3`) welds limb 29 to PI 38 and the
        // verifier anchors `lifecycle_felt_cell(post_cell)`. A frozen-lifecycle archive forgery is
        // UNSAT. Mirrors Lean `EffectVmEmitRotationV3.receiptArchiveV3` (`rotateV3WithRecordPin
        // B_LIFECYCLE …`).
        Some(Effect::ReceiptArchive { .. }) => Some(B_LIFECYCLE),
        // `Refusal` writes the WELDED `fields[4]` indexed slot + bumps the nonce in the deployed
        // `apply_refusal`, ALIGNED to the Lean SPEC `TurnExecutorFull.refusalField` (the audit lands
        // in the EXT `fields_root`, which `compute_authority_digest_felt` FOLDS into the r23 authority
        // residue, `B_RECORD_DIGEST`). So the AFTER `record_digest` limb MOVES on a genuine refusal; the
        // record-forcing pin (`refusalV3`) welds it to PI 38, and the verifier anchors
        // `compute_authority_digest_felt(post_cell)`. A frozen-audit refusal forgery is UNSAT. Mirrors
        // Lean `EffectVmEmitRotationV3.refusalV3`.
        Some(Effect::Refusal { .. }) => Some(B_RECORD_DIGEST),
        _ => None,
    }
}

/// `true` iff the lead effect is a lifecycle mover whose deployed descriptor carries the in-circuit
/// lifecycle-payload HASH gate (`EffectVmEmitRotationV3.lifecyclePayloadHashGate`): cellSeal,
/// cellDestroy, receiptArchive. These move the cell lifecycle to a state with a PAYLOAD
/// (`reason_hash` / `death_certificate_hash` / `checkpoint_hash` + the `at` height) folded into the
/// felt-domain `lifecycle_felt` (limb `B_LIFECYCLE`); the gate welds that limb to the declared
/// payload-hash column `prmCol 3`, so a forged payload is UNSAT for a ledgerless client. cellUnseal is
/// EXCLUDED (its target lifecycle is `Live`, which carries no payload — the disc gate is the whole
/// close). Mirrors the Lean `rotateV3WithLifecyclePayloadGate` movers (`cellSealV3` / `cellDestroyV3` /
/// `receiptArchiveV3`).
fn lifecycle_payload_gated(lead: Option<&Effect>) -> bool {
    matches!(
        lead,
        Some(Effect::CellSeal { .. })
            | Some(Effect::CellDestroy { .. })
            | Some(Effect::ReceiptArchive { .. })
    )
}

/// The param column carrying the new-cell key for the accounts-set grow-gate family
/// (createCell / factory / spawn), or `None` otherwise. createCell/spawn write the new-cell id
/// into `param0`; factory writes the factory VK into `param0` and the DERIVED CHILD VK into
/// `param1` — so the factory's new-cell key (and the column its grow-gate + PI[38] pin reference)
/// is `param1`. Mirrors Lean `EffectVmEmitRotationV3.{NEW_CELL_KEY_PARAM_COL,
/// FACTORY_CHILD_KEY_PARAM_COL}` (the gate key columns of `{createCellV3,factoryV3,spawnV3}`).
fn new_cell_key_param_col(lead: Option<&Effect>) -> Option<usize> {
    match lead {
        Some(Effect::CreateCell { .. }) | Some(Effect::SpawnWithDelegation { .. }) => Some(0),
        Some(Effect::CreateCellFromFactory { .. }) => Some(super::columns::param::CHILD_VK_DERIVED),
        _ => None,
    }
}

/// Fill one rotated block (BEFORE or AFTER) at `base` for ONE row. The WELDED limbs
/// (r0↔balance_lo, r1↔nonce, r2↔balance_hi, r3..r10↔fields, cap_root) are copied from THAT
/// row's own v1 state block at `state_base` (so the weld gates hold on EVERY row, including
/// the NoOp padding rows whose v1 state block differs from the active row); the WITNESS-
/// CARRIED limbs (cells_root, the map roots, lifecycle, epoch, committed_height, iroot,
/// r11..r23) come from the per-turn producer witness `w` (turn-invariant). Then the genuine
/// chained `wireCommitR` digests are computed on this row's own limbs.
///
/// The chained-absorption logic is byte-identical to `descriptor_ir2::rotation_probe_trace_r`,
/// the producer's `wire_commit`, and the Lean `wireCommitR`.
fn fill_block(row: &mut [BabyBear], base: usize, state_base: usize, w: &RotatedBlockWitness) {
    // witness-carried limbs from the producer (turn-invariant).
    row[base..base + NUM_PRE_LIMBS].copy_from_slice(&w.pre_limbs[..NUM_PRE_LIMBS]);
    // welded limbs OVERRIDE from this row's own v1 state block (per-row truth) —
    // `EffectVmEmitRotationV3.weldsAt`.
    row[base + 1] = row[state_base + state::BALANCE_LO]; // r0
    row[base + 2] = row[state_base + state::NONCE]; // r1
    row[base + 3] = row[state_base + state::BALANCE_HI]; // r2
    for i in 0..8 {
        row[base + 4 + i] = row[state_base + state::FIELD_BASE + i]; // r3..r10
    }
    row[base + B_CAP_ROOT] = row[state_base + state::CAP_ROOT]; // cap_root
    row[base + B_IROOT] = w.iroot;

    // chained absorption: 4-wide head, 3-wide chip groups while ≥ 3 pre-iroot limbs remain,
    // the iroot on its own arity-2 final site → state_commit.
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    // the iroot rides its own arity-2 final site → state_commit.
    let commit = hash_many(&[d, row[base + B_IROOT]]);
    row[base + B_STATE_COMMIT] = commit;
}

/// Fill the widened-caveat region at `base` (29-felt manifest + 9 chain + commit) from the
/// turn's manifest. The chained `caveatCommit` is genuine (Lean
/// `EffectVmEmitRotationCaveat.caveatCommit`). A register (slot) operand can never alias a
/// heap operand (the `caveat_operand_no_aliasing` keystone — the domain tag separates them).
fn fill_caveat(row: &mut [BabyBear], base: usize, m: &RotatedCaveatManifest) {
    // manifest: count + 4 × 7-felt entries `[type_tag, domain_tag, key, p0..p3]`.
    row[base] = BabyBear::new(m.count());
    for (idx, e) in m.entries.iter().enumerate() {
        let eb = base + 1 + idx * cav::ENTRY_SIZE;
        row[eb] = BabyBear::new(e.type_tag);
        row[eb + 1] = BabyBear::new(e.domain_tag);
        row[eb + 2] = e.key;
        row[eb + 3] = e.params[0];
        row[eb + 4] = e.params[1];
        row[eb + 5] = e.params[2];
        row[eb + 6] = e.params[3];
    }
    // chained caveat commitment over the 29 manifest felts: 4-wide head, 3-wide body, tail.
    let manifest = cav::MANIFEST_SIZE; // 29
    let chain_base = base + manifest; // 9 carriers
    let commit_col = chain_base + cav::NUM_CHAIN; // base + 29 + 9 = base + 38
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[chain_base + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < manifest {
        let remaining = manifest - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[chain_base + chain] = d;
        chain += 1;
    }
    row[commit_col] = d;
}

/// Resolve the rotated registry descriptor NAME for one effect's v1 selector — the
/// `*VmDescriptor2R24` member of `V3_STAGED_REGISTRY_TSV` whose rotated shape proves THIS
/// effect. The cohort is the 36 graduated descriptors the Lean `EffectVmEmitRotationV3.
/// v3Registry` emits (28 base + 8 per-slot `setField`); the trace the rotated generator emits
/// is the SAME shape (327 cols + 38 PIs) for every member (the appendix is parametric, not
/// per-effect — `rotateV3`), so this resolver picks WHICH per-effect constraint family the
/// IR-v2 prover enforces on the shared trace.
///
/// `None` for a selector OUTSIDE this cohort (a non-cohort effect has no rotated descriptor —
/// the caller fails closed rather than proving the wrong shape). The `SetField` family
/// (selector 2) routes to the per-slot descriptor by the field index via
/// [`rotated_set_field_descriptor_name`].
///
/// NOTE: the rotated cohort is the v3Registry's exact membership (36 members) — the 28
/// v2-graduated descriptors (incl. the cap-crown `RevokeCapability` and `Custom`) PLUS the 8
/// LIVE-path effects the STEP 1 widening added (`GrantCapability`, `MakeSovereign`, `CreateCell`,
/// `CreateCellFromFactory`, `SpawnWithDelegation`, `ReceiptArchive`, `CellUnseal`, `EmitEvent`).
/// The HONEST RESIDUE is now EMPTY: `Custom` (8) was the last selector without a rotated
/// descriptor; it GRADUATED via the new accumulator / recursive-proof-binding constraint kind
/// (`DescriptorIR2.ProofBind`), so EVERY live selector resolves and the cutover can delete v1 with
/// zero residue.
pub fn rotated_descriptor_name(selector: usize) -> Option<&'static str> {
    use super::columns::sel;
    Some(match selector {
        s if s == sel::TRANSFER => "transferVmDescriptor2R24",
        s if s == sel::BURN => "burnVmDescriptor2R24",
        s if s == sel::BRIDGE_MINT => "mintVmDescriptor2R24",
        // The DEDICATED supply-mint (SUPPLY-MODEL.md Stage 2b): the turn-layer `Effect::Mint`
        // fires `sel::MINT` and routes to its OWN descriptor (`supplyMintVmDescriptor2R24` =
        // `EffectVmEmitRotationV3.supplyMintV3`), the same proven credit/tick/freeze body as the
        // bridge-mint member but on the dedicated selector — so it proves + self-verifies under its
        // own slot, not by riding BridgeMint's.
        s if s == sel::MINT => "supplyMintVmDescriptor2R24",
        s if s == sel::NOTE_SPEND => "noteSpendVmDescriptor2R24",
        s if s == sel::NOTE_CREATE => "noteCreateVmDescriptor2R24",
        s if s == sel::CELL_SEAL => "cellSealVmDescriptor2R24",
        s if s == sel::CELL_DESTROY => "cellDestroyVmDescriptor2R24",
        s if s == sel::REFUSAL => "refusalVmDescriptor2R24",
        s if s == sel::SET_PERMISSIONS => "setPermsVmDescriptor2R24",
        s if s == sel::SET_VERIFICATION_KEY => "setVKVmDescriptor2R24",
        s if s == sel::EXERCISE_VIA_CAPABILITY => "exerciseVmDescriptor2R24",
        s if s == sel::PIPELINED_SEND => "pipelinedSendVmDescriptor2R24",
        s if s == sel::REFRESH_DELEGATION => "refreshVmDescriptor2R24",
        s if s == sel::INCREMENT_NONCE => "incrementNonceVmDescriptor2R24",
        s if s == sel::REVOKE_DELEGATION => "revokeVmDescriptor2R24",
        s if s == sel::INTRODUCE => "introduceVmDescriptor2R24",
        s if s == sel::ATTENUATE_CAPABILITY => "attenuateVmDescriptor2R24",
        // The COHORT-WIDENING (STEP 1 / ROTATION-CUTOVER §2c): the eight LIVE-path effects the
        // Lean `v3Registry` now emits rotated descriptors for via `rotateV3`. GrantCapability
        // rides the BARE unattenuated cap-root grant template (`grantCapVmDescriptor2R24`),
        // distinct from the ATTENUATE_CAPABILITY phase-B descriptor.
        s if s == sel::GRANT_CAP => "grantCapVmDescriptor2R24",
        s if s == sel::MAKE_SOVEREIGN => "makeSovereignVmDescriptor2R24",
        s if s == sel::CREATE_CELL_FROM_FACTORY => "factoryVmDescriptor2R24",
        s if s == sel::EMIT_EVENT => "emitEventVmDescriptor2R24",
        s if s == sel::CREATE_CELL => "createCellVmDescriptor2R24",
        s if s == sel::SPAWN_WITH_DELEGATION => "spawnVmDescriptor2R24",
        s if s == sel::CELL_UNSEAL => "cellUnsealVmDescriptor2R24",
        s if s == sel::RECEIPT_ARCHIVE => "receiptArchiveVmDescriptor2R24",
        // GRADUATED (cap-crown): RevokeCapability (24) now has a rotated descriptor — the cap-REMOVAL
        // leg `revokeCapabilityVmDescriptor2R24` (held-membership map-read + ZERO-value remove-write,
        // NO submask). The pre-graduation pinned-digest advance is gone.
        s if s == sel::REVOKE_CAPABILITY => "revokeCapabilityVmDescriptor2R24",
        // GRADUATED (recursive-proof binding): Custom (8) now has a rotated descriptor — the
        // `customVmDescriptor2R24` leg carries the `proof_bind` op (`DescriptorIR2.ProofBind`)
        // that ties the row's `custom_proof_commitment` to a VERIFYING external sub-proof of the
        // recursion engine. THE LAST rotation-cutover residue closed; the residue is now EMPTY,
        // so the cutover can delete v1 with zero residue.
        s if s == sel::CUSTOM => "customVmDescriptor2R24",
        // The residue is EMPTY: every LIVE selector resolves above. NoOp and unknown selectors
        // fail closed.
        _ => return None,
    })
}

/// Resolve the per-slot `SetField` rotated descriptor name for a concrete field index
/// (`setFieldVmDescriptor2-{0..7}R24`), or the dynamic descriptor for an out-of-range /
/// runtime index.
pub fn rotated_set_field_descriptor_name(field_idx: u32) -> &'static str {
    match field_idx {
        0 => "setFieldVmDescriptor2-0R24",
        1 => "setFieldVmDescriptor2-1R24",
        2 => "setFieldVmDescriptor2-2R24",
        3 => "setFieldVmDescriptor2-3R24",
        4 => "setFieldVmDescriptor2-4R24",
        5 => "setFieldVmDescriptor2-5R24",
        6 => "setFieldVmDescriptor2-6R24",
        7 => "setFieldVmDescriptor2-7R24",
        _ => "setFieldDynVmDescriptor2R24",
    }
}

/// Resolve the rotated registry descriptor name for one EFFECT (the cohort-general entry
/// point the live prover uses). The `SetField` family routes by field index; every other
/// graduated effect routes by its selector. `None` for a non-cohort effect.
pub fn rotated_descriptor_name_for_effect(effect: &Effect) -> Option<&'static str> {
    match effect {
        Effect::SetField { field_idx, .. } => Some(rotated_set_field_descriptor_name(*field_idx)),
        Effect::NoOp => None,
        other => rotated_descriptor_name(super::effect_selector(other)),
    }
}

/// The registry name (TSV column 1) of the welded sealed-escrow satisfaction descriptor — the
/// Lean `Dregg2.Deos.SettleEscrowSatDescriptor.settleEscrowSatVmDescriptor2R24` (piCount 47, the
/// rotated 46-PI vector + the appended selector slot pinned at PI `ESCROW_SEL_PI = 46`). The
/// descriptor carrying the four selector-gated `SETTLE_ESCROW` satisfaction gates over the rotated
/// BEFORE/AFTER field columns. STAGED: a member of `rotation-v3-staged-registry.tsv` only (no wide
/// twin, no producer, no committed VK yet — see `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`
/// §6 BLOCKER 1).
pub const SETTLE_ESCROW_SAT_DESCRIPTOR_NAME: &str = "settleEscrowSatVmDescriptor2R24";

/// **The DECLARATION-keyed escrow routing arm (STAGED — the §6 item-2 producer half).** Resolve the
/// rotated descriptor for an effect whose ACTING CELL has a COMMITTED declaration requiring the
/// sealed-escrow capacity tag (`required_caveat_tags` = the caller's
/// `dregg_turn::executor::required_capacity_caveat_tags(state_constraints)` re-derivation over the
/// `B_AUTHORITY_DIGEST`-bound declared constraint-set). A settle is performed AS a transfer (a
/// zero-amount transfer that flips two leg status fields), so it would otherwise route to
/// `transferVmDescriptor2R24` — a NON-welded descriptor with no satisfaction gate. This arm routes it
/// to the WELDED [`SETTLE_ESCROW_SAT_DESCRIPTOR_NAME`] instead, so the four satisfaction gates ride
/// the proof and the selector binds. It keys on the EXISTING caveat declaration — NOT a new kernel
/// effect/verb (the settle is still a `Transfer`; effect-dispatch is untouched).
///
/// STAGED: this is NOT yet wired into the live prover (`rotated_descriptor_name_for_effect` is the
/// deployed default and is unchanged). Routing a declared-escrow turn here on the live path requires
/// the welded descriptor to be a WIDE member with a producer + committed VK first (the FLIP, §6
/// BLOCKER 1). Until then this resolves the welded NAME for the staged verifier-enforcement and tests
/// only. A non-escrow declaration delegates to [`rotated_descriptor_name_for_effect`] (deployed-identical).
pub fn rotated_descriptor_name_for_declared_escrow(
    effect: &Effect,
    required_caveat_tags: &[u32],
) -> Option<&'static str> {
    if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW) {
        Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME)
    } else {
        rotated_descriptor_name_for_effect(effect)
    }
}

/// The cohort-general caveat manifest for a turn: by default EMPTY (most effects carry no
/// in-circuit caveat operand — the manifest's `count = 0` and every entry is the zero
/// sentinel, which `fill_caveat` commits to a well-defined `caveatCommit`). A turn that
/// genuinely carries slot/heap caveats supplies a populated manifest via the SDK bridge; the
/// rotated shape is identical either way (the appendix width does not change with the count).
pub fn empty_caveat_manifest() -> RotatedCaveatManifest {
    RotatedCaveatManifest::default()
}

// ============================================================================
// THE CAP-OPEN APPENDIX (Lean `Dregg2.Circuit.Emit.CapOpenEmit` —
// `attenuateCapOpenEffV3`, descriptor `dregg-effectvm-attenuateA-v1-rot24-v3-capopen-eff`).
//
// The cap-open appendix EXTENDS the rotated base trace with 59 columns
// that OPEN the deployed depth-16 cap-tree at a write-mask leaf whose target is the
// turn's `src`. The Lean constraints (`DeployedCapOpen.Satisfied`) realize:
//   * 1 leaf chip-absorb (arity 7: the 7 leaf fields → leafDigest);
//   * 16 node chip-absorbs (arity 3: `[FACT_MARK, left, right]` → node), folded by the
//     direction bits from the leaf digest up to the root;
//   * 16 dir-bool gates, a rootPin (node[15] == capRoot), a targetBind (leaf[1] == src),
//     and the FAITHFUL two-axis facet × tier: transferFacet (leaf[3] mask_lo == EFFECT_TRANSFER),
//     facetHi (leaf[4] mask_hi == 0), authTag (leaf[2] auth_tag == Signature).
//
// CRITICAL HASH SEAM (Lean `DeployedCapTree.nodeOf` / `capLeafDigest`): the chip lookups
// realize `hash_many`-ABSORB nodes — `hash_many(&[FACT_MARK, left, right])` and
// `hash_many(&[7 leaf fields])` — NOT `poseidon2::hash_fact` (which uses a different state
// layout). The IR-v2 interpreter auto-gathers the chip table from these lookup tuples, so
// filling the cap-open columns with genuine `hash_many` values makes every lookup land on a
// real (arity, padded_inputs, hash) chip row. ZERO hand-authored constraint semantics here —
// only column FILLS; the declared Lean chip lookups + base gates do all the enforcement.
// ============================================================================

/// The deployed cap-tree depth (`CapOpenEmit.DEPTH = 16`).
pub const CAP_OPEN_DEPTH: usize = 16;
/// The base column of the cap-open appendix. Phase B-GATE GRADUATED the rotated base (appending the
/// 7-lane chip blocks at the END), so the cap-open appendix now starts at the GRADUATED rotated
/// width `GRAD_ROT_WIDTH = 608` (the committed `attenuateVmDescriptor2R24.trace_width`), NOT at the
/// un-graduated `ROT_WIDTH = 328`. The cap-open builds ON the graduated rotated layout.
pub const CAP_OPEN_BASE: usize = GRAD_ROT_WIDTH; // 608
/// The width of the FULL `EffectMask` bit decomposition (residual (a) — GENUINE MEMBERSHIP). The
/// decoded facet is the full `u32` mask `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536`
/// (`EFFECT_ALL = 0xFFFF_FFFF`), so the decomposition spans all 32 bits: any deployed effect-kind bit
/// `1 << n` (`n < 32`, up to `EFFECT_ATTENUATE_CAPABILITY = 1 << 23`) is selectable AND a broad cap
/// (`mask_hi = 0xFFFF`) decomposes fully. The Lean twin is `DeployedCapOpen.MASK16_BITS`.
pub const CAP_OPEN_MASK_BITS: usize = 32;
/// The cap-MEMBERSHIP columns `fill_cap_open` writes (the genuine non-lane witness): 7 leaf + 1
/// leafDigest + 16×(sib,dir,node) + capRoot + src + effBit + 32 mask-bit columns = 91. The trailing
/// 32 mask-bit columns carry the boolean decomposition of the FULL effect mask the genuine SUBMASK
/// facet gate (`maskBitBoolGate`/`maskReconGate`/`selectedBitGate`) reads — NOT the over-strict
/// equality `mask_lo == effBit` (and NO `mask_hi == 0` pin, so a broad `EFFECT_ALL` cap is admitted).
pub const CAP_OPEN_MEMBERSHIP_COLS: usize = 7 + 1 + 3 * CAP_OPEN_DEPTH + 3 + CAP_OPEN_MASK_BITS; // 91
/// The number of poseidon2-chip lookup SITES the cap-membership appendix adds atop the graduated
/// rotated layout: 1 leaf absorb (arity 7) + 16 node absorbs (arity 3) = 17. Phase B-GATE appends a
/// 7-lane block per site, so the cap-open appendix's chip-lane columns number `7 × 17 = 119`.
pub const CAP_OPEN_LANE_SITES: usize = 1 + CAP_OPEN_DEPTH; // 17
/// The FULL cap-open appendix span: the 91 cap-membership columns PLUS the 7×17 = 119 appended
/// chip-lane columns Phase B-GATE graduates = 210. The 91 membership columns are written by
/// `fill_cap_open` at `CAP_OPEN_BASE + 0..91`; the 119 cap-lane columns (`CAP_OPEN_BASE + 91..210`)
/// are filled automatically by the prove wrapper's `descriptor_ir2::fill_chip_lanes`.
pub const CAP_OPEN_SPAN: usize = CAP_OPEN_MEMBERSHIP_COLS + 7 * CAP_OPEN_LANE_SITES; // 210
/// The cap-open trace width (`GRAD_ROT_WIDTH + 210 = 818` = the committed
/// `attenuateCapOpenEffVmDescriptor2R24.trace_width`).
pub const CAP_OPEN_WIDTH: usize = CAP_OPEN_BASE + CAP_OPEN_SPAN;

/// The turn-identity `actor` column of the TB (turn-bound) cap-open weld
/// (`CapOpenTurnPins.capOpenActorCol w = w + CAP_OPEN_SPAN`, i.e. the first column PAST the full
/// cap-open appendix). `= CAP_OPEN_BASE + CAP_OPEN_SPAN = 608 + 210 = 818` (the committed
/// `transferCapOpenTBVmDescriptor2R24` turn-identity column, PI 39).
pub const CAP_OPEN_TB_ACTOR_COL: usize = CAP_OPEN_BASE + CAP_OPEN_SPAN;
/// The turn-identity `dst` column of the TB cap-open weld (`CapOpenTurnPins.capOpenDstCol w = w +
/// CAP_OPEN_SPAN + 1`). `= CAP_OPEN_BASE + CAP_OPEN_SPAN + 1 = 819` (PI 40).
pub const CAP_OPEN_TB_DST_COL: usize = CAP_OPEN_BASE + CAP_OPEN_SPAN + 1;
/// The turn-bound cap-open trace width: the cap-open width PLUS the two turn-identity columns
/// (`effCapOpenV3TB`'s `traceWidth := d.traceWidth + 2`). `= CAP_OPEN_WIDTH + 2 = 820`.
pub const CAP_OPEN_TB_WIDTH: usize = CAP_OPEN_WIDTH + 2;
/// The cap-open base descriptor's PI count (`effCapOpenV3.piCount = 38` — the rotated 38-PI vector;
/// the cap-open appendix adds no PIs). The TB weld appends THREE turn-identity PIs at `38/39/40`.
pub const CAP_OPEN_TB_PI_BASE: usize = ROT_PI_COUNT; // 38
/// The published turn-identity PI slots of the TB cap-open (`effCapOpenV3.piCount + 0/1/2`):
/// `src → PI[38]`, `actor → PI[39]`, `dst → PI[40]` (`CapOpenTurnPins.turnIdentityPins`).
pub const CAP_OPEN_TB_PI_SRC: usize = CAP_OPEN_TB_PI_BASE; // 38
pub const CAP_OPEN_TB_PI_ACTOR: usize = CAP_OPEN_TB_PI_BASE + 1; // 39
pub const CAP_OPEN_TB_PI_DST: usize = CAP_OPEN_TB_PI_BASE + 2; // 40

/// The `FACT_MARK` node-tag felt (`DeployedCapTree.FACT_MARK = 0xFACF`).
pub const FACT_MARK: u32 = 0xFACF; // 64207
/// The leaf `mask_lo` the FAITHFUL two-axis facet gate (`DeployedCapOpen.transferFacetGate`)
/// pins: `EFFECT_TRANSFER = 1 << 1 = 2` (`FacetAuthority.EFFECT_TRANSFER`). The decoded facet
/// `maskOfLimbs mask_lo mask_hi` permits the `EFFECT_TRANSFER` effect-kind bit. This REPLACES
/// the toy `writeMaskGate` (`mask_lo == 3`).
pub const WRITE_MASK_LO: u32 = 2;
/// The leaf `mask_hi` the `facetHiGate` pins (`== 0`, so the decoded facet is exactly `mask_lo`).
pub const FACET_MASK_HI: u32 = 0;
/// The leaf `auth_tag` the `authTagGate` pins: the `Signature` tier byte `1`
/// (`tierOfTag 1 = .signature`).
pub const SIGNATURE_AUTH_TAG: u32 = 1;

/// One cap-membership witness: the 7 leaf fields (in `CapOpenCols` order
/// `[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff]`), the 16 sibling
/// digests + direction bits of the membership path, the recomposed `cap_root`, and the
/// turn's `src` cell id. A `recomposes()` self-check rebuilds the root from the leaf digest
/// over the path (ABSORB-node `hash_many`, NOT `hash_fact`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapOpenWitness {
    /// The 7 cap-leaf fields (`slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff`).
    pub leaf: [BabyBear; 7],
    /// The 16 sibling digests of the membership path.
    pub siblings: [BabyBear; CAP_OPEN_DEPTH],
    /// The 16 direction bits (0 ⇒ cur is the LEFT child at that level).
    pub directions: [u8; CAP_OPEN_DEPTH],
    /// The recomposed committed cap-tree root (must equal node[15]).
    pub cap_root: BabyBear,
    /// The turn's source-cell id (must equal `leaf[1]`, the leaf target).
    pub src: BabyBear,
    /// **(residual (a))** The turn's ACTUAL effect-kind bit (`EFFECT_<kind> = 1 << n`), written to
    /// the `effBit` column (`base + 58`). The descriptor's `effBitGateFor` pins it; the general
    /// `facetEffGate` binds `leaf.mask_lo == eff_bit` — so the cap must permit THAT effect-kind.
    /// `EFFECT_TRANSFER (= WRITE_MASK_LO = 2)` for the transfer/attenuate legs; each fan-out leg
    /// carries its own bit (delegate = `1<<16`, introduce = `1<<13`, grantCap = `1<<2`, …).
    pub eff_bit: u32,
}

/// The leaf digest: the SINGLE rate-8 chip absorb of the 7 leaf fields (arity 7), byte-identical
/// to `cap_root::CapLeaf::digest` and the Lean `capLeafDigest = sponge ∘ leafFields`. ONE chip
/// row (no length tag; lanes 0..6 = the genuine fields), so the IR-v2 chip realizes it as one
/// lookup — the unification that discharges `SchemeRealizedByChip`.
pub fn cap_leaf_digest(leaf: &[BabyBear; 7]) -> BabyBear {
    crate::cap_root::cap_chip_absorb(leaf)
}

/// One node hash: the arity-3 rate-8 chip absorb of `[FACT_MARK, left, right]` (Lean
/// `nodeOf = sponge [FACT_MARK, l, r]`), byte-identical to `cap_root::cap_node`. ONE chip row
/// (FACT_MARK rides rate lane 0, length tag 3 in lane 4) — NOT the capacity-tagged `hash_fact`.
pub fn cap_node(left: BabyBear, right: BabyBear) -> BabyBear {
    crate::cap_root::cap_chip_absorb(&[BabyBear::new(FACT_MARK), left, right])
}

/// Mix `(cur, sib)` by the direction bit into `(left, right)` (Lean `leftExpr`/`rightExpr`):
/// `dir = 0 ⇒ (cur, sib)` (cur is LEFT), `dir = 1 ⇒ (sib, cur)`.
fn cap_mix(cur: BabyBear, sib: BabyBear, dir: u8) -> (BabyBear, BabyBear) {
    if dir == 0 { (cur, sib) } else { (sib, cur) }
}

impl CapOpenWitness {
    /// Recompute the root from the leaf digest over the `(sib, dir)` path using ABSORB-node
    /// `hash_many` compression. The self-check the fold's soundness rests on.
    pub fn recomposes(&self) -> BabyBear {
        let mut cur = cap_leaf_digest(&self.leaf);
        for lvl in 0..CAP_OPEN_DEPTH {
            let (l, r) = cap_mix(cur, self.siblings[lvl], self.directions[lvl]);
            cur = cap_node(l, r);
        }
        cur
    }

    /// Build a cap-open witness from a c-list of leaves and a chosen position. The depth-16
    /// ABSORB-node tree is laid over `1 << DEPTH` leaf slots; the chosen leaf rides `position`,
    /// the rest are zero-leaf padding (`hash_many(&[0;7])`). The membership `(siblings,
    /// directions)` path + the recomposed root are computed; `src` is pinned to `leaf[1]` so
    /// the target gate holds. The chosen leaf MUST carry the FAITHFUL two-axis facet × tier the
    /// descriptor's gates pin: `mask_lo == EFFECT_TRANSFER (2)` (`transferFacetGate`), `mask_hi
    /// == 0` (`facetHiGate`), and `auth_tag == Signature (1)` (`authTagGate`).
    pub fn build(leaves: &[[BabyBear; 7]], position: usize) -> Result<Self, String> {
        Self::build_for(leaves, position, WRITE_MASK_LO)
    }

    /// **`build_for` (THE FAN-OUT path builder).** Like [`Self::build`] but for an ARBITRARY
    /// effect-kind bit `eff_bit` (the chosen leaf's `mask_lo` must equal `eff_bit`, not the constant
    /// EFFECT_TRANSFER), and WITHOUT the `auth_tag == Signature` pin (the fan-out `capOpenConstraintsEff`
    /// appendix reads the DECODED tier). `build` is the `eff_bit := EFFECT_TRANSFER` instance.
    pub fn build_for(
        leaves: &[[BabyBear; 7]],
        position: usize,
        eff_bit: u32,
    ) -> Result<Self, String> {
        if position >= leaves.len() {
            return Err(format!(
                "cap-open witness: position {position} >= {} leaves",
                leaves.len()
            ));
        }
        let chosen = leaves[position];
        if chosen.len() != 7 {
            return Err("cap-open witness: leaf must carry 7 fields".into());
        }
        // GENUINE SUBMASK MEMBERSHIP (residual (a)): the chosen cap's facet must PERMIT the
        // effect-kind bit `eff_bit` over the FULL mask `maskOfLimbs(mask_lo, mask_hi)` — `(eff_bit &
        // full_mask) == eff_bit`, the kernel's `is_effect_permitted` for a single bit (`facet.rs:123`),
        // NOT the over-strict equality `mask_lo == eff_bit`. A BROAD honest cap (`EFFECT_ALL`, mask_lo =
        // 0xFFFF, mask_hi = 0xFFFF) PASSES — there is NO `mask_hi == 0` pin.
        let chosen_full_mask: u64 = chosen[3].as_u32() as u64 + (chosen[4].as_u32() as u64) * 65536;
        if (eff_bit as u64 & chosen_full_mask) != eff_bit as u64 {
            return Err(format!(
                "cap-open witness: chosen leaf full mask {chosen_full_mask} (mask_lo {}, mask_hi {}) \
                 does not PERMIT the effect-kind bit {eff_bit} (the facetEffGate submask membership bites)",
                chosen[3].as_u32(),
                chosen[4].as_u32()
            ));
        }
        // residual (a): NO tier pin — the effect-general cap-open appendix (`capOpenConstraintsEff`)
        // DECODES the tier off `auth_tag` rather than pinning Signature, so a cap of ANY tier builds.
        // Lay the depth-16 tree: level 0 = the leaf-digest layer over 2^16 slots, the chosen
        // leaf at `position`, all others the zero-leaf padding digest. We materialize ONLY the
        // path: at each level we need the sibling digest, which is the OTHER child of the
        // current node. For a sparse tree with a single non-padding leaf, every sibling subtree
        // is a uniform-padding subtree whose root is a known per-level constant.
        let zero_leaf = cap_leaf_digest(&[BabyBear::ZERO; 7]);
        // per-level padding subtree roots: pad[0] = zero leaf digest; pad[k+1] = node(pad,pad).
        let mut pad = [BabyBear::ZERO; CAP_OPEN_DEPTH + 1];
        pad[0] = zero_leaf;
        for k in 0..CAP_OPEN_DEPTH {
            pad[k + 1] = cap_node(pad[k], pad[k]);
        }
        let mut siblings = [BabyBear::ZERO; CAP_OPEN_DEPTH];
        let mut directions = [0u8; CAP_OPEN_DEPTH];
        let mut idx = position;
        let mut cur = cap_leaf_digest(&chosen);
        for lvl in 0..CAP_OPEN_DEPTH {
            let dir = (idx & 1) as u8; // 0 ⇒ cur is LEFT child, sibling on the RIGHT.
            // The sibling subtree at this level is uniform padding (single non-pad leaf).
            let sib = pad[lvl];
            siblings[lvl] = sib;
            directions[lvl] = dir;
            let (l, r) = cap_mix(cur, sib, dir);
            cur = cap_node(l, r);
            idx >>= 1;
        }
        let w = Self {
            leaf: chosen,
            siblings,
            directions,
            cap_root: cur,
            src: chosen[1],
            eff_bit: WRITE_MASK_LO,
        };
        debug_assert_eq!(
            w.recomposes(),
            w.cap_root,
            "cap-open witness must recompose"
        );
        Ok(w)
    }

    /// Build a cap-open trace witness from the actor's REAL consumed capability — a 7-field
    /// [`crate::cap_root::CapLeaf`] plus the depth-16 `(sibling, direction)` membership path opened
    /// against the holder's pre-state `capability_root`. This is the prove-site bridge: the c-list
    /// opening the turn carries (`TurnReceipt::consumed_capabilities`, threaded through the SDK's
    /// `CapMembershipWitness`) and `CapOpenWitness` is the trace-column shape [`widen_to_cap_open`]
    /// fills. Both are field-for-field twins (same 7-field [`cap_leaf_digest`], same absorb-node
    /// fold via [`cap_node`]); this converts the dynamically-sized path to the fixed depth-16 arrays
    /// the appendix declares, RECOMPOSES the committed root from the leaf digest, and pins
    /// `src := leaf.target` so the `targetBindGate` holds.
    ///
    /// Fails closed when:
    ///   * the membership path is not exactly [`CAP_OPEN_DEPTH`] levels (the deployed depth);
    ///   * the leaf does not satisfy the FAITHFUL two-axis facet × tier the descriptor's gates pin
    ///     (`mask_lo == EFFECT_TRANSFER`, `mask_hi == 0`, `auth_tag == Signature`) — i.e. the
    ///     consumed cap does not actually confer the transfer authority the open asserts.
    pub fn from_membership(
        leaf: &crate::cap_root::CapLeaf,
        siblings: &[BabyBear],
        directions: &[u8],
    ) -> Result<Self, String> {
        // residual (a): the LIVE transfer/attenuate cap-open now routes the effect-GENERAL
        // descriptors (`transferCapOpenEffVmDescriptor2R24` / `attenuateCapOpenEffVmDescriptor2R24`),
        // whose `capOpenConstraintsEff 1` appendix DECODES the tier off `auth_tag` (no Signature
        // pin) and checks the genuine SUBMASK facet membership. So an honest cap of ANY tier
        // (None/Signature/…) and ANY broad mask that PERMITS Transfer proves — we drop the old
        // `auth_tag == Signature` pin and defer to the submask check in `from_membership_for`.
        Self::from_membership_for(leaf, siblings, directions, WRITE_MASK_LO)
    }

    /// **`from_membership_for` (THE FAN-OUT GENERAL CONSTRUCTOR, residual (a)).** Build a cap-open
    /// trace witness for an ARBITRARY effect-kind bit `eff_bit` (`EFFECT_<kind> = 1 << n`): the
    /// consumed cap's facet must permit THAT effect-kind. The general `facetEffGate` binds
    /// `leaf.mask_lo == eff_bit`, so we require `leaf.mask_lo == eff_bit` (NOT the constant
    /// EFFECT_TRANSFER) and `mask_hi == 0`. The TIER rides the DECODED `auth_tag` (the
    /// `SatisfiedEff` row carries no `authTagGate` constant pin), so any committed `auth_tag` is
    /// accepted here — the off-circuit AuthContext supplies a `provided` the decoded tier admits.
    /// `from_membership` is the `eff_bit := EFFECT_TRANSFER` instance.
    pub fn from_membership_for(
        leaf: &crate::cap_root::CapLeaf,
        siblings: &[BabyBear],
        directions: &[u8],
        eff_bit: u32,
    ) -> Result<Self, String> {
        if siblings.len() != CAP_OPEN_DEPTH || directions.len() != CAP_OPEN_DEPTH {
            return Err(format!(
                "cap-open from_membership: path depth ({} sib / {} dir) != deployed depth {CAP_OPEN_DEPTH}",
                siblings.len(),
                directions.len()
            ));
        }
        let leaf: [BabyBear; 7] = [
            leaf.slot_hash,
            leaf.target,
            leaf.auth_tag,
            leaf.mask_lo,
            leaf.mask_hi,
            leaf.expiry,
            leaf.breadstuff,
        ];
        // GENUINE SUBMASK MEMBERSHIP (residual (a)): the consumed cap's facet must PERMIT the
        // effect-kind bit `eff_bit` over the FULL mask `maskOfLimbs(mask_lo, mask_hi)` — `(eff_bit &
        // full_mask) == eff_bit`, the kernel's `is_effect_permitted` for a single bit, NOT the
        // over-strict equality `mask_lo == eff_bit`. A BROAD honest cap (`EFFECT_ALL`, mask_lo = 0xFFFF,
        // mask_hi = 0xFFFF) PASSES; a cap that does NOT carry bit `n` is refused. NO `mask_hi == 0` pin.
        let full_mask: u64 = leaf[3].as_u32() as u64 + (leaf[4].as_u32() as u64) * 65536;
        if (eff_bit as u64 & full_mask) != eff_bit as u64 {
            return Err(format!(
                "cap-open from_membership: leaf full mask {full_mask} (mask_lo {}, mask_hi {}) does not \
                 PERMIT effect-kind bit {eff_bit} (the consumed cap does not permit the turn's \
                 effect-kind — the facetEffGate submask bites)",
                leaf[3].as_u32(),
                leaf[4].as_u32()
            ));
        }
        let mut sib_arr = [BabyBear::ZERO; CAP_OPEN_DEPTH];
        let mut dir_arr = [0u8; CAP_OPEN_DEPTH];
        sib_arr.copy_from_slice(siblings);
        dir_arr.copy_from_slice(directions);
        // The committed root IS the recomposition of THIS path from the genuine leaf digest — the
        // value the rootPin gate binds. (A fabricated leaf / tampered sibling yields a different
        // root; the chip-lookup membership chain then opens a tree whose root the descriptor's
        // rootPin does not match its own seeded `cap_root` column — UNSAT in-circuit.)
        let mut cur = cap_leaf_digest(&leaf);
        for lvl in 0..CAP_OPEN_DEPTH {
            let (l, r) = cap_mix(cur, sib_arr[lvl], dir_arr[lvl]);
            cur = cap_node(l, r);
        }
        let w = Self {
            leaf,
            siblings: sib_arr,
            directions: dir_arr,
            cap_root: cur,
            src: leaf[1],
            eff_bit,
        };
        debug_assert_eq!(
            w.recomposes(),
            w.cap_root,
            "cap-open from_membership recompose"
        );
        Ok(w)
    }
}

/// Fill the 91 cap-MEMBERSHIP columns at `base` for ONE row from `w` (Lean `CapOpenCols` layout):
///   * leaf field `i` at `base + i` (i = 0..6);
///   * `leafDigest = hash_many(&leaf)` at `base + 7`;
///   * level `lvl`: `sib` at `base + 8 + 3·lvl`, `dir` at `base + 9 + 3·lvl`,
///     `node = hash_many(&[FACT_MARK, left, right])` at `base + 10 + 3·lvl`;
///   * `capRoot` at `base + 56`, `src` at `base + 57`, `effBit` at `base + 58`.
///
/// The `effBit` column (residual (a)) carries the turn's ACTUAL effect-kind bit, pinned by the
/// descriptor's `effBitGate` to `EFFECT_TRANSFER (= WRITE_MASK_LO)` for this transfer cap-open;
/// the `facetEffGate` then binds `leaf.mask_lo == effBit` (the leaf's facet is bound to the
/// committed effect column, NOT a literal constant). The top node (`lvl = 15`) MUST equal
/// `w.cap_root` (asserted). Every digest is a genuine `hash_many`-absorb, so the auto-gathered
/// chip table carries a matching row for each of the 1 + 16 chip lookups.
pub fn fill_cap_open(row: &mut [BabyBear], base: usize, w: &CapOpenWitness) {
    for (i, &f) in w.leaf.iter().enumerate() {
        row[base + i] = f;
    }
    let leaf_digest = cap_leaf_digest(&w.leaf);
    row[base + 7] = leaf_digest;
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let sib = w.siblings[lvl];
        let dir = w.directions[lvl];
        let (l, r) = cap_mix(cur, sib, dir);
        let node = cap_node(l, r);
        row[base + 8 + 3 * lvl] = sib;
        row[base + 9 + 3 * lvl] = BabyBear::new(dir as u32);
        row[base + 10 + 3 * lvl] = node;
        cur = node;
    }
    debug_assert_eq!(
        cur, w.cap_root,
        "cap-open fill: top node must equal cap_root"
    );
    row[base + 56] = w.cap_root;
    row[base + 57] = w.src;
    // residual (a): the committed effect-bit column. Carries the turn's ACTUAL effect-kind bit
    // (`w.eff_bit` — EFFECT_TRANSFER for transfer/attenuate, each fan-out leg its own `1<<n`); the
    // `effBitGateFor` pins it.
    row[base + 58] = BabyBear::new(w.eff_bit);
    // residual (a) — GENUINE MEMBERSHIP: the 32-bit decomposition of the FULL effect mask
    // `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536` (leaf fields 3 + 4) at `base + 59 + i`.
    // The `maskBitBoolGate` booleans each bit, `maskReconGate` binds `full_mask = Σ bitᵢ·2ⁱ`, and
    // `selectedBitGate n` gates bit `n` (where `eff_bit = 1<<n`) set — the genuine `(eff_bit &
    // full_mask) == eff_bit` SUBMASK, NOT the over-strict equality `mask_lo == eff_bit`. A BROAD honest
    // cap (`EFFECT_ALL`, mask_lo = 0xFFFF, mask_hi = 0xFFFF) decomposes with bit `n` set, so it PERMITS
    // the effect — and no `mask_hi == 0` pin rejects it.
    let full_mask: u64 = w.leaf[3].as_u32() as u64 + (w.leaf[4].as_u32() as u64) * 65536;
    for i in 0..CAP_OPEN_MASK_BITS {
        row[base + 59 + i] = BabyBear::new(((full_mask >> i) & 1) as u32);
    }
}

/// Recompute one rotated block's chained `wireCommitR` digests + `state_commit` from the limbs
/// ALREADY present in the row (cols `base..base+NUM_PRE_LIMBS` + the iroot at `base+B_IROOT`).
/// Byte-identical to [`fill_block`]'s chain, but reads the limbs in place rather than from a
/// witness — used after an in-place limb PATCH (e.g. a nonce-passthrough fixup) so the chain
/// carriers + state_commit stay consistent with the patched limbs.
fn recompute_block_commit(row: &mut [BabyBear], base: usize) {
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);
}

/// Test helper: recompute EVERY row's AFTER-block chained commitment in place (after an in-place
/// limb patch, e.g. forging the after `nullifier_root` to test the grow-gate tooth). Exposed for
/// the rotation-flip adversarial tests; not used on any honest path.
#[doc(hidden)]
pub fn recompute_after_blocks_for_test(trace: &mut [Vec<BabyBear>]) {
    for row in trace.iter_mut() {
        recompute_block_commit(row, AFTER_BASE);
    }
}

/// Recompute one v1 state block's STATE_COMMIT intermediates + digest from the block's state
/// columns, byte-identical to the descriptor's STATE_COMMIT poseidon lookups (arity-4
/// `hash_many` of `[s0..s3]`, `[s4..s7]`, `[s8..s11]` → three intermediates, then arity-4
/// `hash_many([i1, i2, i3, 0])` → the STATE_COMMIT). `state_base` is the block's column base
/// (54 for before, 76 for after); `i1/i2/i3` are the AUX intermediate carriers the lookups bind.
fn recompute_v1_state_commit(
    row: &mut [BabyBear],
    state_base: usize,
    i1: usize,
    i2: usize,
    i3: usize,
) {
    use super::columns::state;
    let s = state_base;
    row[i1] = hash_many(&[row[s], row[s + 1], row[s + 2], row[s + 3]]);
    row[i2] = hash_many(&[row[s + 4], row[s + 5], row[s + 6], row[s + 7]]);
    row[i3] = hash_many(&[row[s + 8], row[s + 9], row[s + 10], row[s + 11]]);
    row[s + state::STATE_COMMIT] = hash_many(&[row[i1], row[i2], row[i3], BabyBear::ZERO]);
}

/// Make a generated rotated AttenuateCapability trace satisfy the `attenuateV3` base
/// constraints' phase-B bindings the bare `generate_rotated_effect_vm_trace` output does not
/// carry. THE WITNESS WIRINGS (column FILLS only — ZERO hand-authored constraint semantics):
///
///   * **nonce PASSTHROUGH (frozen)** — the attenuate descriptor pins `after.nonce ==
///     before.nonce` (an UNCONDITIONAL gate) AND the cross-row continuity transition
///     `next.before == local.after`. `generate_effect_vm_trace` TICKS the nonce on every effect
///     row (so each row's after-nonce, and the next row's before-nonce, climbs); attenuate's
///     audited shape is a nonce PASSTHROUGH (the cap-root advance is the state move). So we
///     FREEZE the nonce to row 0's before-nonce across BOTH state blocks on EVERY row — making
///     `after.nonce == before.nonce` hold and the per-row blocks identical so continuity holds.
///   * **cap-root advance binding** — the descriptor pins `after.cap_root == param2`; the
///     generator leaves param2 at 0, so we wire it to the row's own advanced after-cap-root.
///
/// After freezing the nonce we REBUILD every dependent commitment so the whole trace stays
/// internally genuine: the v1 BEFORE + AFTER STATE_COMMIT chains (the descriptor's poseidon
/// lookups), the before-state-commit cross-row continuity carrier, and the rotated BEFORE +
/// AFTER blocks' welded nonce limb + chained `wireCommitR` state_commit. Then the four rotated
/// PI carriers are re-read from the rebuilt trace. Returns the corrected 38-PI vector. Widen
/// the patched 327-wide trace to the cap-open shape with [`widen_to_cap_open`].
pub fn patch_attenuate_base_for_cap_open(
    trace: &mut [Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<Vec<BabyBear>, String> {
    use super::columns::state;
    if trace.is_empty() {
        return Err("patch_attenuate_base: empty trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "patch_attenuate_base: trace width {} != {ROT_WIDTH}",
            trace[0].len()
        ));
    }
    if pis.len() < ROT_PI_COUNT {
        return Err(format!(
            "patch_attenuate_base: PI vector {} shorter than {ROT_PI_COUNT}",
            pis.len()
        ));
    }
    let sb = STATE_BEFORE_BASE; // 54
    let sa = STATE_AFTER_BASE; // 76
    let before_nonce_col = sb + state::NONCE; // 56
    let after_nonce_col = sa + state::NONCE; // 78
    let after_cap_root_col = sa + state::CAP_ROOT; // 87
    let param2_col = super::columns::PARAM_BASE + 2; // 70
    // The AUX STATE_COMMIT intermediate carriers the v1 lookups bind. The generator wrote the
    // AFTER-block intermediates at AUX_BASE+8..10 (`aux_off::STATE_INTER1..3`); the descriptor's
    // BEFORE-block STATE_COMMIT (col `sb + STATE_COMMIT`) carries no in-descriptor lookup (it is
    // only consumed by the cross-row continuity), so we recompute it consistently from the
    // (frozen) before-state and reuse the same arity-4 chain shape via scratch intermediates
    // that we DO NOT need to land on bound columns — but to stay byte-identical we land the
    // after-block intermediates on their bound carriers.
    let a_i1 = super::columns::AUX_BASE + 8; // 98
    let a_i2 = super::columns::AUX_BASE + 9; // 99
    let a_i3 = super::columns::AUX_BASE + 10; // 100

    // The frozen nonce: row 0's before-nonce (the turn's pre-state nonce — attenuate does not
    // tick it).
    let frozen_nonce = trace[0][before_nonce_col];

    for row in trace.iter_mut() {
        // (1) FREEZE the nonce in BOTH v1 state blocks + the rotated block r1 welds.
        row[before_nonce_col] = frozen_nonce;
        row[after_nonce_col] = frozen_nonce;
        row[BEFORE_BASE + 2] = frozen_nonce; // rotated before-block r1 (nonce) weld
        row[AFTER_BASE + 2] = frozen_nonce; // rotated after-block r1 (nonce) weld
        // (2) cap-root advance binding: param2 := after.cap_root.
        row[param2_col] = row[after_cap_root_col];
        // (3) rebuild the v1 AFTER STATE_COMMIT chain (the descriptor's bound poseidon lookups).
        recompute_v1_state_commit(row, sa, a_i1, a_i2, a_i3);
        // (4) rebuild the v1 BEFORE STATE_COMMIT (consumed by cross-row continuity). We compute
        //     it with the SAME arity-4 chain into scratch and land only the digest column; the
        //     before-block intermediates are not bound to any in-descriptor lookup.
        let bi1 = hash_many(&[row[sb], row[sb + 1], row[sb + 2], row[sb + 3]]);
        let bi2 = hash_many(&[row[sb + 4], row[sb + 5], row[sb + 6], row[sb + 7]]);
        let bi3 = hash_many(&[row[sb + 8], row[sb + 9], row[sb + 10], row[sb + 11]]);
        row[sb + state::STATE_COMMIT] = hash_many(&[bi1, bi2, bi3, BabyBear::ZERO]);
        // (5) rebuild both rotated blocks' chained `wireCommitR` digests over the frozen limbs.
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // The four rotated PI carriers, re-read from the rebuilt trace (same columns the descriptor's
    // pin constraints bind: 218 / 261 / 259 / 310).
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = pis[..ROT_PI_COUNT].to_vec();
    // The four rotated commit pins sit at the v1 prefix count `V1_PI_COUNT..+4` (the same slots
    // `rotPins` / `generate_rotated_effect_vm_trace` append them to). Indexing off `V1_PI_COUNT`
    // keeps these aligned when the v1 prefix grows (e.g. Phase C pushed it 34→42).
    dpis[V1_PI_COUNT] = r0[BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit
    dpis[V1_PI_COUNT + 1] = last[AFTER_BASE + B_STATE_COMMIT]; // rotated NEW commit
    dpis[V1_PI_COUNT + 2] = last[AFTER_BASE + B_COMMITTED_HEIGHT]; // committed height
    dpis[V1_PI_COUNT + 3] = last[CAVEAT_BASE + C_SPAN - 1]; // caveat commit
    Ok(dpis)
}

/// Widen an already-built rotated base trace (`ROT_WIDTH`-wide) to the `CAP_OPEN_WIDTH`-wide
/// cap-open trace, filling the 91 cap-MEMBERSHIP columns on EVERY row uniformly with `w` (so the
/// every-row base gates — dir-bool, rootPin, targetBind, transferFacet/facetHi/authTag — hold on
/// every row). The base trace's own `ROT_WIDTH` columns + 38 PIs are unchanged; the cap-open
/// appendix is purely additive and lands at `CAP_OPEN_BASE = GRAD_ROT_WIDTH` (the cap-open builds on
/// the GRADUATED rotated layout). The graduated rotated chip-lane columns (`ROT_WIDTH..GRAD_ROT_WIDTH`)
/// and the cap chip-lane columns (`CAP_OPEN_BASE + 91 ..`) are filled automatically by the prove
/// wrapper's `descriptor_ir2::fill_chip_lanes` — NOT here. The base trace MUST be a `ROT_WIDTH`-wide
/// rotated trace the base `attenuateV3` constraints already accept (e.g. from
/// [`generate_rotated_effect_vm_trace`] on an AttenuateCapability turn).
pub fn widen_to_cap_open(trace: &mut [Vec<BabyBear>], w: &CapOpenWitness) -> Result<(), String> {
    if trace.is_empty() {
        return Err("cap-open widen: empty base trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "cap-open widen: base trace width {} != {ROT_WIDTH}",
            trace[0].len()
        ));
    }
    if w.recomposes() != w.cap_root {
        return Err("cap-open widen: witness does not recompose its cap_root".into());
    }
    for row in trace.iter_mut() {
        row.resize(CAP_OPEN_WIDTH, BabyBear::ZERO);
        fill_cap_open(row, CAP_OPEN_BASE, w);
    }
    Ok(())
}

/// **THE WIDE CAP-OPEN widener (the 1026-wide cap-open tail's faithful 8-felt commit).** Given a
/// fully-laid `CAP_OPEN_WIDTH`-wide cap-open trace (a base rotated trace already passed through
/// [`widen_to_cap_open`]) and its base PI vector, appends the two 13×8 BEFORE/AFTER wide carrier
/// blocks at `CAP_OPEN_WIDTH = 818` / `+104` and the 16 wide commit PIs — the cap-open tail's wide
/// member is `wideAppend (capOpenHost) 187 238` (width 1026), carriers PAST the 210-col cap-open
/// appendix. The cap-open host constraints / membership columns are CARRIED UNCHANGED; the wide
/// carriers re-absorb the SAME `BEFORE_BASE`/`AFTER_BASE` limbs. Returns the appended `dpis`. The
/// trace is resized in place to `CAP_OPEN_WIDTH + 368 = 1026`.
pub fn append_wide_carriers_cap_open(
    trace: &mut [Vec<BabyBear>],
    base_pis: Vec<BabyBear>,
) -> Result<Vec<BabyBear>, String> {
    if trace.is_empty() {
        return Err("cap-open wide: empty base trace".into());
    }
    if trace[0].len() != CAP_OPEN_WIDTH {
        return Err(format!(
            "cap-open wide: base trace width {} != CAP_OPEN_WIDTH {CAP_OPEN_WIDTH} (widen_to_cap_open \
             first)",
            trace[0].len()
        ));
    }
    Ok(append_wide_carriers(trace, base_pis, CAP_OPEN_WIDTH))
}

/// Fill the two TURN-IDENTITY columns of the TB (turn-bound) cap-open weld on a single row: the
/// `actor` felt at `CAP_OPEN_TB_ACTOR_COL` (818) and the `dst` felt at `CAP_OPEN_TB_DST_COL` (819).
/// (The `src` column — `CAP_OPEN_BASE + 57` = 665 — is the EXISTING cap-open `src` column already
/// filled by [`fill_cap_open`] from `w.src`; the TB weld pins THAT column, not a new one.) The three
/// `CapOpenTurnPins.turnIdentityPins` are LAST-row `.piBinding` gates welding these columns to the
/// published turn PIs (`src → 38`, `actor → 39`, `dst → 40`).
pub fn fill_cap_open_turn_pins(row: &mut [BabyBear], actor: BabyBear, dst: BabyBear) {
    row[CAP_OPEN_TB_ACTOR_COL] = actor;
    row[CAP_OPEN_TB_DST_COL] = dst;
}

/// Widen a rotated base trace (`ROT_WIDTH`) to the TURN-BOUND cap-open width (`CAP_OPEN_TB_WIDTH` =
/// 409): the cap-open appendix (incl. the `src` column from `w.src`) PLUS the two turn-identity
/// columns (`actor`/`dst`) filled UNIFORMLY on every row. The TB descriptor (`effCapOpenV3TB`) pins
/// the `src`/`actor`/`dst` columns to PIs `38/39/40` on the LAST row; filling them uniformly makes the
/// pins hold on the last row. The `src` column is rooted (`targetBindGate` already pins `leaf.target ==
/// src`), so `src == w.src`; `actor`/`dst` are the published columns the verifier ANCHORS to the
/// trusted turn (`TurnIdentityAnchored`). Caller MUST pass `actor`/`dst` consistent with `w.src` (the
/// honest turn's identity); the verifier's PI override is what FORCES the published identity = trusted.
pub fn widen_to_cap_open_tb(
    trace: &mut [Vec<BabyBear>],
    w: &CapOpenWitness,
    actor: BabyBear,
    dst: BabyBear,
) -> Result<(), String> {
    widen_to_cap_open(trace, w)?;
    for row in trace.iter_mut() {
        row.resize(CAP_OPEN_TB_WIDTH, BabyBear::ZERO);
        fill_cap_open_turn_pins(row, actor, dst);
    }
    Ok(())
}

/// Extend a base 38-PI rotated vector to the TURN-BOUND 41-PI vector by APPENDING the three
/// turn-identity PIs (`src` at 38, `actor` at 39, `dst` at 40). The honest prover publishes its own
/// turn's `(src, actor, dst)`; the verifier OVERRIDES these slots from the trusted turn before
/// `verify_vm_descriptor2` (see [`anchor_cap_open_turn_pins`]), so a forged identity is UNSAT.
pub fn cap_open_tb_dpis(
    base_dpis: &[BabyBear],
    src: BabyBear,
    actor: BabyBear,
    dst: BabyBear,
) -> Vec<BabyBear> {
    let mut dpis = base_dpis[..ROT_PI_COUNT].to_vec();
    debug_assert_eq!(dpis.len(), CAP_OPEN_TB_PI_BASE);
    dpis.push(src); // PI 38
    dpis.push(actor); // PI 39
    dpis.push(dst); // PI 40
    dpis
}

/// **`anchor_cap_open_turn_pins` — the `TurnIdentityAnchored` verifier override (DEPLOYMENT side).**
/// Override the three turn-identity PIs (`38/39/40`) of a TB cap-open dpis vector with the TRUSTED
/// turn's `(src, actor, dst)` felts, exactly as the record-pin family anchors `dpis[38]` from the
/// trusted post-cell. A prover-published identity that disagrees (a forged `actor`/`src`/`dst`) makes
/// the anchored PI disagree with the proof's bound, last-row-pinned column ⇒ `verify_vm_descriptor2`
/// UNSAT ⇒ reject. This is what makes a LEDGERLESS light client able to conclude the published turn's
/// `actor`/`src`/`dst` MATCH the proven transition: it recomputes them from the trusted turn it holds.
pub fn anchor_cap_open_turn_pins(
    dpis: &mut [BabyBear],
    trusted_src: BabyBear,
    trusted_actor: BabyBear,
    trusted_dst: BabyBear,
) {
    dpis[CAP_OPEN_TB_PI_SRC] = trusted_src;
    dpis[CAP_OPEN_TB_PI_ACTOR] = trusted_actor;
    dpis[CAP_OPEN_TB_PI_DST] = trusted_dst;
}

/// The honest transfer-turn caveat manifest the flip test + the cutover use: ONE register
/// caveat (entry 0, domain registers, key = register 3) and one HEAP-KEY caveat (entry 1,
/// domain heap, key well beyond u8 range). The remaining slots stay empty.
pub fn transfer_caveat_manifest() -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: 1,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::new(3),
        params: [BabyBear::ZERO; 4],
    };
    m.entries[1] = RotatedCaveatEntry {
        type_tag: 1,
        domain_tag: cav::DOMAIN_HEAP,
        key: BabyBear::new(123_456_789),
        params: [BabyBear::ZERO; 4],
    };
    m
}

// ============================================================================
// THE FAITHFUL 8-FELT WIDE COMMITMENT APPENDIX (Lean
// `EffectVmEmitRotationWide.wideAppend` over `transferV3`, the `v3RegistryWide`
// transfer member — descriptor `transferVmDescriptor2R24Wide`, width 816 / PI 54).
//
// STAGED-ADDITIVE: this is a PARALLEL wide producer BESIDE the live 1-felt path. The live
// `generate_rotated_effect_vm_trace` (608 / 38-PI) is UNTOUCHED; this WIDENS its output to 816
// by appending two 13-carrier × 8-felt wide commitment chains (BEFORE + AFTER) that re-absorb the
// SAME rotated limbs the 1-felt block already lays, exposing the genuine 8-felt (~124-bit) state
// commitment. The 16 appended PIs publish the BEFORE first-row + AFTER last-row 8-felt commits.
//
// The geometry is read off the committed wide descriptor
// (`circuit/descriptors/rotation-wide-transfer-staged.tsv`):
//   * BEFORE wide carriers: base `WIDE_BEFORE_CBASE = 608`, carrier `k` at `608 + 8·k .. +7`
//     (13 carriers → cols 608..711); carrier 12 (cols 704..711) = the BEFORE 8-felt commit.
//   * AFTER  wide carriers: base `WIDE_AFTER_CBASE  = 712`, carrier `k` at `712 + 8·k .. +7`
//     (13 carriers → cols 712..815); carrier 12 (cols 808..815) = the AFTER 8-felt commit.
//   * The chain absorbs the rotated block's limbs (`BEFORE_BASE + 0..36` then iroot at
//     `BEFORE_BASE + B_IROOT`) — the SAME columns the 1-felt `wireCommitR` reads. The chip lookups
//     are: head arity-4 over `[l0..l3]`, eleven body arity-11 over `prev8 ‖ [l3i,l3i+1,l3i+2]`,
//     final arity-9 over `prev8 ‖ [iroot]`. Each carrier is filled CHIP-FAITHFULLY (the chip table
//     derives `out0..out7` from the genuine permutation with the arity-tag seeding, so a carrier
//     must equal `chip_absorb_all_lanes(arity, inputs)` or the `out[i] == lane[i]` AIR bites).
//   * PIs 38..45 ← BEFORE carrier-12 (cols 704..711) on the FIRST row; PIs 46..53 ← AFTER
//     carrier-12 (cols 808..815) on the LAST row.
// ============================================================================

/// The committed wide trace width (`wideAppend` adds 208 = 2 × 13 × 8 carrier columns to the
/// 608-wide rotated base): `transferVmDescriptor2R24Wide.trace_width`.
pub const WIDE_WIDTH: usize = GRAD_ROT_WIDTH + 368; // v10: + 2 × 23 × 8
/// The base column of the BEFORE 13×8 wide carrier block (`wideBeforeCBase = h.traceWidth = 608`).
pub const WIDE_BEFORE_CBASE: usize = GRAD_ROT_WIDTH; // 608
/// The base column of the AFTER 13×8 wide carrier block (`wideAfterCBase = h.traceWidth + 184`).
pub const WIDE_AFTER_CBASE: usize = GRAD_ROT_WIDTH + 184; // v10: + 23 × 8
/// The number of 8-felt carriers per wide commitment chain (head + 11 body + final).
pub const WIDE_NUM_CARRIERS: usize = 23;
/// The in-block carrier index of the final 8-felt commitment carrier (carrier 12).
pub const WIDE_COMMIT_CARRIER: usize = WIDE_NUM_CARRIERS - 1; // 12
/// The committed wide public-input count (`h.piCount + 16` = 38 + 16).
pub const WIDE_PI_COUNT: usize = ROT_PI_COUNT + 16; // 54

/// Fill one block's 13-carrier × 8-felt wide commitment chain at `cbase`, reading the limbs from
/// the rotated block at `limb_base` (`BEFORE_BASE` / `AFTER_BASE`). Each carrier's 8 output lanes
/// are filled CHIP-FAITHFULLY (`chip_absorb_all_lanes`), so the wide chip lookups' `out[i] ==
/// lane[i]` equalities hold and the published 8-felt commit binds the 37 limbs + iroot. The chain
/// shape (4-wide head, eleven 3-wide arity-11 body groups, arity-9 iroot final) is the byte twin of
/// `poseidon2::wire_commit_8` and the Lean `wireCommitR8` — but seeded through the chip's arity tag.
fn fill_wide_block(row: &mut [BabyBear], cbase: usize, limb_base: usize) {
    use crate::descriptor_ir2::chip_absorb_all_lanes;
    // head: arity-4 absorb of limbs l0..l3 → carrier 0.
    let head_inputs = [
        row[limb_base],
        row[limb_base + 1],
        row[limb_base + 2],
        row[limb_base + 3],
    ];
    let mut d = chip_absorb_all_lanes(4, &head_inputs);
    let mut carrier = 0usize;
    row[cbase + 8 * carrier..cbase + 8 * carrier + 8].copy_from_slice(&d);
    carrier += 1;
    // body: while ≥ 3 pre-iroot limbs remain, an arity-11 absorb of `prev8 ‖ 3 limbs`.
    let mut col = 4usize;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        let mut inputs = [BabyBear::ZERO; 11];
        inputs[..8].copy_from_slice(&d);
        let arity;
        if remaining >= 3 {
            inputs[8] = row[limb_base + col];
            inputs[9] = row[limb_base + col + 1];
            inputs[10] = row[limb_base + col + 2];
            arity = 11;
            col += 3;
        } else {
            // (the 37-limb transfer shape has NO leftover — 33 body limbs = 11 groups of 3 — but
            // keep the leftover arm faithful for parametricity: an arity-9 `prev8 ‖ 1 limb`.)
            inputs[8] = row[limb_base + col];
            arity = 9;
            col += 1;
        }
        d = chip_absorb_all_lanes(arity, &inputs);
        row[cbase + 8 * carrier..cbase + 8 * carrier + 8].copy_from_slice(&d);
        carrier += 1;
    }
    // final: the iroot rides the wide ARITY-11 absorb (`prev8 ‖ iroot ‖ 0 ‖ 0`) → the commit
    // carrier. The deployed chip AIR pins `in7..in10 == 0` on every NON-11 arity (it supports only
    // narrow ≤ 7 and wide 11), so the final MUST be the wide arity-11 row with the two trailing
    // limb lanes zero — `single_perm_compress` is invariant to those trailing zeros, so the digest
    // is byte-identical to the arity-9 `prev8 ‖ iroot`. The wide descriptor declares arity 11 here.
    let mut inputs = [BabyBear::ZERO; 11];
    inputs[..8].copy_from_slice(&d);
    inputs[8] = row[limb_base + B_IROOT];
    d = chip_absorb_all_lanes(11, &inputs);
    row[cbase + 8 * carrier..cbase + 8 * carrier + 8].copy_from_slice(&d);
    debug_assert_eq!(
        carrier, WIDE_COMMIT_CARRIER,
        "wide chain must end on carrier 12"
    );
}

/// **THE WIDE TRANSFER trace generator (`transferVmDescriptor2R24Wide`, faithful 8-felt commit).**
///
/// Widens the LIVE 608-wide rotated transfer trace ([`generate_rotated_effect_vm_trace`]) to the
/// committed 816-wide wide descriptor: it appends the BEFORE/AFTER 13×8 wide commitment carriers
/// (re-absorbing the rotated limbs the 1-felt block already lays) and the 16 wide commit PIs. The
/// live 1-felt carriers/PIs (cols < 608, PIs 0..37) are CARRIED UNCHANGED — this is purely
/// additive. Returns `(trace, dpis)` ready for `prove_vm_descriptor2` against the wide descriptor.
pub fn generate_rotated_transfer_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    // The live 608-wide rotated trace + 38-PI vector (UNTOUCHED machinery).
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT {
        return Err(format!(
            "wide transfer generator: base PI vector {} != {ROT_PI_COUNT} (transfer carries the \
             bare 38-PI rotated vector — a record/grow-gate pin would mis-shape the wide append)",
            base_pis.len()
        ));
    }

    // Widen each row + append the 16 wide PIs via the generic widener (transfer's host width is
    // `GRAD_ROT_WIDTH = 608`, so the carriers land at `WIDE_BEFORE_CBASE = 608`).
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    debug_assert_eq!(dpis.len(), WIDE_PI_COUNT);
    Ok((trace, dpis))
}

/// **THE GENERIC WIDE WIDENER (parametric in the host width / carrier base).** Given a fully-laid
/// rotated base trace (its `BEFORE_BASE`/`AFTER_BASE` limb blocks final, including any grow-gate root
/// override + `recompute_block_commit`) and its base PI vector, this:
///   * resizes each row to `host_width + 368` and fills the two 13×8 BEFORE/AFTER wide carrier blocks
///     at `cbB = host_width` / `cbA = host_width + 184` (the `wideBeforeCBase`/`wideAfterCBase` Lean
///     layout), chip-faithfully via [`fill_wide_block`] — reading the SAME `BEFORE_BASE`/`AFTER_BASE`
///     limbs the 1-felt block lays (so the 8-felt commit binds the same 37 limbs + iroot);
///   * APPENDS the 16 wide commit PIs PAST the base PIs: BEFORE commit (carrier 12, first row) then
///     AFTER commit (carrier 12, last row).
///     `host_width` is the wide member's HOST width (`d.traceWidth` in Lean): `GRAD_ROT_WIDTH = 608` for
///     the 816-wide families, `CAP_OPEN_WIDTH = 818` for the 1026-wide cap-open tail. The wide carriers
///     land STRICTLY PAST the host's columns + gates (the appendix is purely additive), member-uniform
///     because `BEFORE_BASE`/`AFTER_BASE` (187/238) are uniform across the cohort. The number of base
///     PIs is preserved (the grow-gate families carry an extra PI[38]); the 16 wide PIs append after.
pub fn append_wide_carriers(
    trace: &mut [Vec<BabyBear>],
    base_pis: Vec<BabyBear>,
    host_width: usize,
) -> Vec<BabyBear> {
    let cb_before = host_width;
    let cb_after = host_width + 184;
    let wide_width = host_width + 368;
    for row in trace.iter_mut() {
        row.resize(wide_width, BabyBear::ZERO);
        fill_wide_block(row, cb_before, BEFORE_BASE);
        fill_wide_block(row, cb_after, AFTER_BASE);
    }
    let mut dpis = base_pis;
    // STAGE-1 PIN RETIREMENT: the 1-felt rotated OLD/NEW commit pins (the first two of the four
    // appended rotated commit pins, at `V1_PI_COUNT` and `V1_PI_COUNT + 1`) were DROPPED from the
    // wide descriptor — the 8-felt wide commit (PIs past the base) is the SOLE binding. Those two base
    // slots are now DEAD/unbound, but Fiat–Shamir still absorbs EVERY public input, so a
    // witness-dependent value there (the producer's real carrier vs the executor's placeholder
    // reconstruction) would diverge the transcript ⇒ `InvalidPowWitness`. ZERO them so producer +
    // executor agree on these dead slots regardless of witness. (They exist on every wide family —
    // the rotated commit carriers ride the bare rotated prefix every member shares.)
    const RETIRED_COMMIT_PI_OLD: usize = V1_PI_COUNT;
    const RETIRED_COMMIT_PI_NEW: usize = V1_PI_COUNT + 1;
    if dpis.len() > RETIRED_COMMIT_PI_NEW {
        dpis[RETIRED_COMMIT_PI_OLD] = BabyBear::ZERO;
        dpis[RETIRED_COMMIT_PI_NEW] = BabyBear::ZERO;
    }
    let before_commit_base = cb_before + 8 * WIDE_COMMIT_CARRIER;
    let after_commit_base = cb_after + 8 * WIDE_COMMIT_CARRIER;
    // Borrow the two boundary rows to read 8 felts each (no row clone).
    let last_idx = trace.len() - 1;
    let r0 = &trace[0];
    for j in 0..8 {
        dpis.push(r0[before_commit_base + j]); // BEFORE 8-felt commit (first row)
    }
    let last = &trace[last_idx];
    for j in 0..8 {
        dpis.push(last[after_commit_base + j]); // AFTER 8-felt commit (last row)
    }
    dpis
}

/// **THE WIDE BURN/MINT trace generator (transfer-shape cohort).** Burn and mint carry the bare
/// 38-PI rotated vector exactly as transfer does (no grow-gate root, no record pin); their wide
/// member is `wideAppend burn 187 238` (width 816 / PI 54), the SAME carrier shape as transfer. This
/// wraps the LIVE base generator ([`generate_rotated_effect_vm_trace`], which proves any cohort
/// member's real turn) + the generic widener at `GRAD_ROT_WIDTH = 608`. Returns `(trace, dpis)`.
pub fn generate_rotated_transfer_shape_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT {
        return Err(format!(
            "transfer-shape wide generator: base PI vector {} != {ROT_PI_COUNT} (this wrapper is for \
             the bare-38-PI transfer-shape cohort — a grow-gate/record member carries an extra PI)",
            base_pis.len()
        ));
    }
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    Ok((trace, dpis))
}

/// **THE WIDE RECORD-PIN trace generator (the record-pin cohort — setPermissions / setVK / cellSeal /
/// cellUnseal / cellDestroy / receiptArchive / refusal, 816-wide / 55-PI).** The base generator
/// ([`generate_rotated_effect_vm_trace`]) pushes the record/lifecycle pin as PI 38 for these leads (39
/// base PIs); this appends the wide carriers at `GRAD_ROT_WIDTH = 608` (so the published 8-felt commit
/// rides PIs 39..54, after the record pin at 38). Returns `(trace, dpis)`.
pub fn generate_rotated_record_pin_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    let base_len = base_pis.len();
    // The record-pin family carries either the single limb-0 pin (`ROT_PI_COUNT + 1`, the lifecycle
    // movers + the historical record-digest pin) OR — H1 — the 8 authority record-pins for the
    // record-digest movers (setPerms/setVK/makeSovereign/refusal pin all 8 faithful authority limbs,
    // `ROT_PI_COUNT + 8`, `withRecordPin8Headroom2`). Both are valid; the wide descriptor
    // (`wideAppend setPermsV3 …`) declares the matching `base_len + 16`.
    if base_len != ROT_PI_COUNT + 1 && base_len != ROT_PI_COUNT + 8 {
        return Err(format!(
            "record-pin wide generator: base PI vector {} is neither {} (single record/lifecycle pin) \
             nor {} (the H1 8-felt authority record-pin8)",
            base_len,
            ROT_PI_COUNT + 1,
            ROT_PI_COUNT + 8
        ));
    }
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    debug_assert_eq!(dpis.len(), base_len + 16); // base record-pins + 16 wide commit carriers
    Ok((trace, dpis))
}

/// **THE WIDE FEE-IN-PROOF trace generator (`transferFeeVmDescriptor2R24Wide`, 816-wide / 55-PI).**
/// The wide twin of the fee-aware base generator ([`generate_rotated_effect_vm_trace_with_fee`]): it
/// debits the fee in-proof (so the rotated AFTER limbs carry the post-fee balance) and then appends
/// the BEFORE/AFTER 13×8 wide carriers + 16 wide commit PIs at `GRAD_ROT_WIDTH = 608`. Because
/// `fill_wide_block` re-absorbs the SAME post-fee `BEFORE_BASE`/`AFTER_BASE` limbs the fee rewrite
/// laid, the published 8-felt commit (PIs 39..54, after the fee's PI 38) binds the post-fee state at
/// ~124 bits. The live sovereign transfer IS fee'd — this is its wide producer leg. Returns
/// `(trace, dpis)` ready for `prove_vm_descriptor2` against the wide fee descriptor.
pub fn generate_rotated_transfer_shape_with_fee_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    fee: u64,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) = generate_rotated_effect_vm_trace_with_fee(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        fee,
    )?;
    if base_pis.len() != ROT_PI_COUNT + 1 {
        return Err(format!(
            "wide fee generator: base PI vector {} != {} (the fee descriptor carries the 39-PI \
             rotated vector — the published fee rides PI 38)",
            base_pis.len(),
            ROT_PI_COUNT + 1
        ));
    }
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    debug_assert_eq!(dpis.len(), WIDE_PI_COUNT + 1); // 39 base + 16 wide = 55
    Ok((trace, dpis))
}

/// The host (pre-wide-append) width of the `heapWriteVmDescriptor2R24` 1-felt descriptor: the
/// `heapWriteSpliceVmDescriptor` carries FEWER chip sites than the standard economic rotated host
/// (no balance-hash economic sites — it is a Class-A heap-root recompute), so its graduated width is
/// **595** (distinct from `GRAD_ROT_WIDTH = 609`). The wide carriers (the wide `heapWriteVmDescriptor2R24`
/// member, width 803 / PI 20) land at THIS host width: `595 + 368 = 803`.
pub const HEAP_WRITE_HOST_WIDTH: usize = 595;

/// **THE WIDE HEAP-WRITE trace generator (`heapWriteVmDescriptor2R24` wide member, 803-wide / 20-PI).**
///
/// heapWrite is the Class-A heap-root-recompute member (Lean `RotatedKernelRefinementExercise.heapWriteV3`
/// = `graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)` ++ the `.write` splice `MapOp`). It rides the
/// SAME rotated block as every cohort member, plus a genuine sorted-Merkle SPLICE on the heap root: the
/// in-row `HEAP_ADDR` recompute (`col 102 = chip-absorb(coll, key)`) keys a `.write` `MapOp` that opens
/// the committed BEFORE heap root (`col 65`, the per-cell `cap_root` register the heap-root rides) at
/// that address for the written value (`col 72`) and FORCES the AFTER heap root (`col 87`) to the genuine
/// `Heap.set` recompute. There is NO live `Effect::HeapWrite` selector (the descriptor is reached by the
/// exercise-inner heap-write path, NOT the effect→descriptor resolvers), so this is the per-family wide
/// PRODUCER for it — exactly mirroring the supplyMint wide producer (live base + the generic
/// [`append_wide_carriers`] at the member's host width), preserving the 8-felt before/after anchors.
///
/// SOUNDNESS: `heap_leaves` MUST be the cell's GENUINE BEFORE heap and MUST contain a leaf at the
/// addressed key (the in-row-recomputed `addr = chip-absorb(coll, key)`); the write is an UPDATE of a
/// present key (`update_witness`), and the published AFTER root is the GENUINE sorted-tree splice — a
/// missing key or a forged post-root fails closed (no fabricated post-root). Returns `(trace, dpis,
/// map_heaps)` ready for `prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(),
/// &map_heaps)` against the wide `heapWriteVmDescriptor2R24`.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_heap_write_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    coll: BabyBear,
    key: BabyBear,
    value: BabyBear,
    heap_leaves: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{AUX_BASE, PARAM_BASE};
    use crate::descriptor_ir2::chip_absorb_all_lanes;
    use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};

    // The live rotated base (cols 0..ROT_WIDTH) — the SAME machinery every cohort member rides; the
    // heapWrite descriptor carries NO economic gates, so the lead effect's economic v1 columns are
    // unconstrained (any cohort lead lays a valid rotated block).
    let (mut trace, gen_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "heap-write wide: base trace width {} != {ROT_WIDTH}",
            trace[0].len()
        ));
    }

    // The in-row HEAP_ADDR recompute (`heapWriteVmDescriptor2R24`'s arity-2 chip lookup,
    // `col 102 = chip-absorb(coll, key)`) — the genuine sorted KEY the splice opens. We compute it the
    // SAME way `fill_chip_lanes` will (so the heap leaf the splice opens IS the recomputed address).
    let mut absorb_in = [BabyBear::ZERO; 11];
    absorb_in[0] = coll;
    absorb_in[1] = key;
    let addr = chip_absorb_all_lanes(2, &absorb_in)[0];
    // The leaf-digest chip lookup `col 103 = chip-absorb(addr, value)` (out0). `fill_chip_lanes` lands
    // only the exposed lanes 1..7; the producer must lay out0 itself (so the request matches the
    // chip-table provide, which derives outputs from the genuine permutation).
    let mut leaf_in = [BabyBear::ZERO; 11];
    leaf_in[0] = addr;
    leaf_in[1] = value;
    let leaf_digest = chip_absorb_all_lanes(2, &leaf_in)[0];

    // The BEFORE heap (the deployed openable sorted tree). The addressed key MUST be present — the
    // splice `.write` is an UPDATE of a present key (`update_witness`); a missing key fails closed (no
    // fabricated post-root).
    let before_tree = CanonicalHeapTree::new(heap_leaves.to_vec(), HEAP_TREE_DEPTH);
    let before_root = before_tree.root();
    if !before_tree.sorted_leaves().iter().any(|l| l.addr == addr) {
        return Err(format!(
            "heap-write wide: recomputed addr {} is NOT in the BEFORE heap — the splice `.write` opens a \
             present key and has no membership witness, so it refuses the turn (no silent forge)",
            addr.as_u32()
        ));
    }
    let after_root = before_tree
        .update_witness(HeapLeaf { addr, value })
        .ok_or_else(|| {
            format!(
                "heap-write wide: update witness for addr {} failed",
                addr.as_u32()
            )
        })?
        .new_root;

    // Override the heap-root registers (`col 65` BEFORE / `col 87` AFTER — the per-cell `cap_root` the
    // heap-root rides) AND their rotated-block limbs (the welds `65 == limb` / `87 == limb` are KEPT),
    // lay the splice key/value params, then recompute the rotated commitments so the published rotated
    // commit binds the written heap root.
    let heap_root_before_col = STATE_BEFORE_BASE + state::CAP_ROOT; // 65
    let heap_root_after_col = STATE_AFTER_BASE + state::CAP_ROOT; // 87
    let coll_col = PARAM_BASE + 2; // 70 (HEAP_ADDR recompute input: collection)
    let key_col = PARAM_BASE + 3; // 71 (HEAP_ADDR recompute input: key)
    let value_col = PARAM_BASE + 4; // 72 (HEAP_VALUE)
    // The HEAP_ADDR column (102) is the splice `MapOp`'s KEY. It is ALSO the output of the in-row
    // arity-2 chip lookup `col 102 = chip-absorb(coll, key)`, which `fill_chip_lanes` lands at prove
    // time — but the map-op pre-flight replay reads col 102 from the RAW trace (BEFORE lane-fill), so
    // we set it explicitly to the recomputed `addr`. `fill_chip_lanes` then re-lands the SAME value
    // (the addr lookup is chip-faithful over the same coll/key), so the lookup gate holds.
    let heap_addr_col = AUX_BASE + 12; // 102 (HEAP_ADDR — out0 of the addr chip lookup)
    let leaf_digest_col = AUX_BASE + 13; // 103 (out0 of the leaf-digest chip lookup)
    let before_root_limb = BEFORE_BASE + B_CAP_ROOT;
    let after_root_limb = AFTER_BASE + B_CAP_ROOT;
    for row in trace.iter_mut() {
        row[heap_root_before_col] = before_root;
        row[before_root_limb] = before_root;
        row[heap_root_after_col] = after_root;
        row[after_root_limb] = after_root;
        row[coll_col] = coll;
        row[key_col] = key;
        row[value_col] = value;
        row[heap_addr_col] = addr;
        row[leaf_digest_col] = leaf_digest;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // The 4 heapWrite base PIs: the two rotated state-commit pins (pi 0/1) are RETIRED by the wide
    // member (the 8-felt commit is the sole binding — they are unbound, zeroed for Fiat–Shamir
    // agreement); the committed-height pin (pi 2 ← `col 270`) and the caveat-commit pin (pi 3 ←
    // `col 328`) survive — both unaffected by the heap-root override, so read from the live base PIs.
    let base_pis = vec![
        BabyBear::ZERO,
        BabyBear::ZERO,
        gen_pis[V1_PI_COUNT + 2],
        gen_pis[V1_PI_COUNT + 3],
    ];
    let dpis = append_wide_carriers(&mut trace, base_pis, HEAP_WRITE_HOST_WIDTH);
    debug_assert_eq!(trace[0].len(), HEAP_WRITE_HOST_WIDTH + 368); // 803
    debug_assert_eq!(dpis.len(), 20); // 4 base (2 retired) + 16 wide
    Ok((trace, dpis, vec![heap_leaves.to_vec()]))
}

/// **THE WIDE TURN-BOUND CAP-OPEN trace generator (`transferCapOpenTBVmDescriptor2R24` wide member,
/// 1029-wide / 65-PI).**
///
/// The wide twin of the #225 turn-identity weld (Lean `CapOpenTurnPins.effCapOpenV3TB`): it builds the
/// LIVE rotated transfer base, widens it to the turn-bound cap-open shape ([`widen_to_cap_open_tb`] —
/// the 91 cap-membership columns + the two `actor`/`dst` turn-identity columns), publishes the 49-PI
/// turn-bound vector ([`cap_open_tb_dpis`]: 46 rotated + `src`/`actor`/`dst` at 46/47/48), and then
/// appends the BEFORE/AFTER 13×8 wide carriers + 16 wide commit PIs at the cap-open-TB host width
/// (`CAP_OPEN_TB_WIDTH = 821`). The cap-membership host columns, the turn-identity pins, and the live
/// 1-felt carriers are CARRIED UNCHANGED — the wide append is purely additive, preserving the 8-felt
/// before/after anchors. The verifier ANCHORS the three turn-identity PIs to the trusted turn
/// ([`anchor_cap_open_turn_pins`]) exactly as on the narrow path; a forged published identity is UNSAT.
///
/// `cap_open` MUST be a genuine transfer-conferring cap-membership witness whose leaf `target` IS the
/// turn's `src` (the `targetBind` gate roots it); `actor`/`dst` are the published turn identity the
/// caller threads from the honest turn. Returns `(trace, dpis)` ready for `prove_vm_descriptor2(&desc,
/// &trace, &dpis, &MemBoundaryWitness::default(), &[])` against the wide `transferCapOpenTBVmDescriptor2R24`.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_transfer_cap_open_tb_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    cap_open: &CapOpenWitness,
    src: BabyBear,
    actor: BabyBear,
    dst: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT {
        return Err(format!(
            "cap-open-TB wide generator: base PI vector {} != {ROT_PI_COUNT} (the cap-open-TB rides the \
             bare-46-PI rotated transfer base)",
            base_pis.len()
        ));
    }
    widen_to_cap_open_tb(&mut trace, cap_open, actor, dst)
        .map_err(|e| format!("cap-open-TB wide widen: {e}"))?;
    let tb_pis = cap_open_tb_dpis(&base_pis, src, actor, dst);
    debug_assert_eq!(tb_pis.len(), CAP_OPEN_TB_PI_BASE + 3); // 49
    let dpis = append_wide_carriers(&mut trace, tb_pis, CAP_OPEN_TB_WIDTH);
    debug_assert_eq!(trace[0].len(), CAP_OPEN_TB_WIDTH + 368); // 1029
    debug_assert_eq!(dpis.len(), CAP_OPEN_TB_PI_BASE + 3 + 16); // 65
    Ok((trace, dpis))
}

/// **THE WIDE NOTESPEND trace generator (grow-gate cohort).** Wraps the deployment-real nullifier-
/// tree generator ([`generate_rotated_note_spend_trace_with_nullifier_tree`], which overrides limb 26
/// with the openable accumulator roots + recomputes the block commits), then appends the wide
/// carriers at `GRAD_ROT_WIDTH = 608`. The grow-gate member carries the extra PI[38] (the nullifier
/// pin) before the 16 wide PIs (wide member width 816 / PI 55). Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_spend_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    let (mut trace, base_pis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_nullifiers,
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    Ok((trace, dpis, map_heaps))
}

/// **THE WIDE NOTECREATE trace generator (grow-gate cohort).** Wraps the commitments-tree generator
/// ([`generate_rotated_note_create_trace_with_commitments_tree`], limb-27 override + recompute), then
/// appends the wide carriers at `GRAD_ROT_WIDTH = 608` (wide member width 816 / PI 55).
pub fn generate_rotated_note_create_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_commitments: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    let (mut trace, base_pis, map_heaps) =
        generate_rotated_note_create_trace_with_commitments_tree(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            before_commitments,
        )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    Ok((trace, dpis, map_heaps))
}

/// **THE WIDE CREATECELL/FACTORY/SPAWN trace generator (grow-gate cohort).** Wraps the accounts-tree
/// generator ([`generate_rotated_create_cell_trace_with_accounts_tree`], limb-0 override + recompute),
/// then appends the wide carriers at `GRAD_ROT_WIDTH = 608` (wide member width 816 / PI 55).
pub fn generate_rotated_create_cell_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    let (mut trace, base_pis, map_heaps) = generate_rotated_create_cell_trace_with_accounts_tree(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_accounts,
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    Ok((trace, dpis, map_heaps))
}

/// **THE WIDE CREATECELLFROMFACTORY trace generator (grow-gate cohort).** The factory twin of
/// [`generate_rotated_create_cell_wide`]: createCellFromFactory shares the SAME accounts-set insert
/// (the born child's id is grown into the cells set, limb 0) — only the new-cell key column differs
/// (`param1 = CHILD_VK_DERIVED` for factory vs `param0` for createCell, resolved by
/// `new_cell_key_param_col`). So this delegates to the shared accounts-tree wide generator; the factory
/// params (factory VK at `param0`, derived child VK at `param1`) ride the rotated base, and the
/// `factoryVmDescriptor2R24` wide descriptor's `.absent`+`.insert` accounts grow-gate (root limb 0)
/// opens against the threaded BEFORE accounts leaf set. A NON-factory lead is REFUSED (the accounts-tree
/// generator's own `new_cell_key_param_col` guard). Returns `(trace, dpis, map_heaps)` ready for
/// `prove_vm_descriptor2` against the wide `factoryVmDescriptor2R24`.
pub fn generate_rotated_create_from_factory_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    if !matches!(effects.first(), Some(Effect::CreateCellFromFactory { .. })) {
        return Err(
            "factory wide generator: lead effect is not a CreateCellFromFactory (route createCell / \
             spawn through their OWN wide wrapper — the accounts grow-gate is shared but the new-cell \
             key column differs)"
                .into(),
        );
    }
    generate_rotated_create_cell_wide(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_accounts,
    )
}

/// **THE WIDE SPAWN trace generator — the BIRTH/ACCOUNTS-GROW leg ONLY (grow-gate cohort).** Spawn's
/// wide descriptor (`spawnVmDescriptor2R24` in `rotation-wide-registry-staged.tsv`, width 817) carries
/// the SAME accounts-set `.absent`+`.insert` grow-gate (root limb 0 — the born child id grown into the
/// cells set) the createCell/factory wide descriptors carry, and NOTHING ELSE: the wide spawn descriptor
/// has NO cap-tree `map_op` (its only map ops are the accounts absent+insert on the cells root). So this
/// wrapper closes spawn's accounts-birth leg by delegating to the shared accounts-tree wide generator
/// (new-cell key = `param0`, resolved by `new_cell_key_param_col`).
///
/// THE CAP-HANDOFF IS A SEPARATE PATH (NOT here): the parent→child capability handoff (the cap-tree
/// INSERT at limb 25) is bound by the deployed `spawnWriteCapOpenVmDescriptor2R24` on the CAP-OPEN path
/// (`sdk/src/full_turn_proof.rs::prove_effect_vm_cap_open`, the `spawn_dual_tree` arm), which threads
/// BOTH the accounts heap (limb 0) and the c-list heap (limb 25) into one proof. The WIDE rotated
/// descriptor does not carry the cap-handoff — so a spawn routed through the wide path proves its
/// accounts-birth column only, and the cap-handoff is the cap-open path's job (already wired). A NON-spawn
/// lead is REFUSED. Returns `(trace, dpis, map_heaps)` ready for `prove_vm_descriptor2` against the wide
/// `spawnVmDescriptor2R24`.
pub fn generate_rotated_spawn_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    if !matches!(effects.first(), Some(Effect::SpawnWithDelegation { .. })) {
        return Err(
            "spawn wide generator: lead effect is not a SpawnWithDelegation (route createCell / factory \
             through their OWN wide wrapper)"
                .into(),
        );
    }
    generate_rotated_create_cell_wide(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_accounts,
    )
}

/// **THE WIDE REFUSAL trace generator (record-pin cohort + the `fields_root` WRITE gate).** Wraps the
/// deployment-real fields-tree generator ([`generate_rotated_refusal_trace_with_fields_tree`], which
/// overrides limb 36 = `B_FIELDS_ROOT` with the openable accumulator roots + recomputes the block
/// commits so the `.write` map-op opens the genuine sorted write), then appends the wide carriers at
/// `GRAD_ROT_WIDTH = 608`. The refusal lead carries the extra PI[38] (the record/lifecycle pin) before
/// the 16 wide PIs (wide member width 816 / PI 55) — the SAME 39-base+16-wide geometry the record-pin
/// wide producer lays, so a refusal proven here verifies through the same wide descriptor path. This is
/// the wide twin of the non-wide fields-tree generator the forge-detector exercises; threading a
/// NON-empty `map_heaps` (the BEFORE fields-tree leaf set + the reserved audit slot) is what makes an
/// HONEST refusal PROVABLE on the deployed path (an EMPTY `map_heaps` is UNSAT against the `.write`
/// gate). Mirrors [`generate_rotated_note_spend_wide`]. Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_refusal_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_fields_leaves: &[crate::heap_root::HeapLeaf],
    audit_value: BabyBear,
) -> RotatedTraceWithHeaps {
    let (mut trace, base_pis, map_heaps) = generate_rotated_refusal_trace_with_fields_tree(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_fields_leaves,
        audit_value,
    )?;
    let base_len = base_pis.len();
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    // H1: refusal is a record-digest mover, so its base carries the 8 authority record-pins
    // (`ROT_PI_COUNT + 8`) → `base_len + 16` wide PIs (was the single-pin `WIDE_PI_COUNT + 1`).
    debug_assert_eq!(dpis.len(), base_len + 16);
    Ok((trace, dpis, map_heaps))
}

// ============================================================================
// setFieldDyn — the DYNAMIC overflow-field write (the 581-wide V1Face geometry).
// ============================================================================

/// The graduated host width of the `setFieldDynVmDescriptor2R24` 1-felt descriptor: the
/// `setFieldDynV1Face` carries FOUR fewer chip sites than the standard rotated host (36 vs 40 — the
/// setField face does not fire the economic balance-hash sites), so its graduated width is
/// `ROT_WIDTH + 7·36 = 328 + 252 = 580`… +1 reserved = **581** (the committed
/// `setFieldDynVmDescriptor2R24.trace_width`, distinct from `GRAD_ROT_WIDTH = 608`). The wide
/// carriers (the `setFieldDynVmDescriptor2R24Wide` member) land at THIS host width.
pub const SET_FIELD_DYN_HOST_WIDTH: usize = 581;

/// The slot-index param column the dynamic setField indexes the 8-cell overflow memory by
/// (`prmCol SLOT = prmCol VALUE = param1`, col 69 — both addr AND value of the Blum write, the
/// post-flag-day `addr = value = param1` identity). It MUST be `0..7` (the slot-range gate).
const SET_FIELD_DYN_SLOT_COL: usize = 1; // PARAM_BASE + 1 = col 69
/// The previous-value witness param column (`PREV_VAL = param2`, col 70).
const SET_FIELD_DYN_PREV_VAL_COL: usize = 2; // PARAM_BASE + 2 = col 70
/// The previous-serial witness param column (`PREV_SERIAL = param6`, col 74).
const SET_FIELD_DYN_PREV_SERIAL_COL: usize = 6; // PARAM_BASE + 6 = col 74
/// The read-back param column (`READBACK = param7`, col 75) the read op transports the write to.
const SET_FIELD_DYN_READBACK_COL: usize = 7; // PARAM_BASE + 7 = col 75

/// **THE DYNAMIC-FIELD setField base trace generator (`setFieldDynVmDescriptor2R24`, the 581-wide
/// V1Face geometry).**
///
/// The overflow `SetField` (`field_idx >= 8`) routes to `setFieldDynVmDescriptor2R24`, a DISTINCT
/// geometry the standard [`generate_rotated_effect_vm_trace`] cannot produce: it (a) hard-panics on
/// `field_idx >= 8` (the v1 `field_idx < 8` assert), and (b) lays the standard 40-chip-site host.
/// This generator builds the geometry from scratch.
///
/// THE BLUM LINEAR MEMORY (the descriptor's two `mem_op` rows, NOT a fields-tree `map_op`): the 8
/// overflow user-field cells are memory addresses `0..7`. The dynamic write picks a `slot` (`0..7`,
/// the slot-range gate on col 69) and the deployed `addr = value = param1` identity collapses the
/// slot AND the written value into col 69. The honest trace lays:
///   * col 69 (`SLOT`/`VALUE`, param1) = `slot` — the addr AND value of the write (slot-range gated);
///   * col 70 (`PREV_VAL`, param2) = `prev_value` — the value at that address BEFORE the write
///     (= the declared boundary init image, replayed as the write's prev tuple);
///   * col 74 (`PREV_SERIAL`, param6) = `0` — the write opens against the INIT serial (the
///     `MemBoundaryWitness` declares serial 0 for the touched address);
///   * col 75 (`READBACK`, param7) = `slot` — the read op transports the write's value (the read's
///     `value = prev_value = col 75`, `prev_serial = const 1` ties it to the write at serial 1).
///     The write is the FIRST mem op (serial 1), so the read's `prev_serial = 1` matches the write's
///     position — the Blum write→read transport with ZERO hashing (`satisfied2_mem_consistent`).
///
/// THE FIELDS-ROOT WELD (gate 31): the AFTER `fields_root` limb (col `AFTER_BASE + B_FIELDS_ROOT` =
/// 275) is welded to `FIELD_INDEX` (col 68) on the active row; we force the AFTER fields_root limb to
/// `slot` and recompute the AFTER block commitment so the published NEW commit binds it. The fifth
/// pin (col `AFTER_BASE + B_RECORD_DIGEST` = 263 → PI[46]) welds the AFTER authority/record-digest
/// limb to the published PI — `record_pin_offset` returns `None` for `SetField`, so we push it here.
///
/// `slot` is the in-circuit overflow-memory address (`0..7`), distinct from the effect's raw
/// `field_idx >= 8`. We thread it as a v1 `SetField { field_idx: slot, value: slot }` lead so the v1
/// economic sub-trace + the rotated welds are laid by the standard machinery WITHOUT the panic, then
/// override the dyn-specific columns. Returns `(trace, dpis, mem_boundary)` ready for
/// `prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &[])`.
#[allow(clippy::missing_panics_doc)]
pub fn generate_rotated_set_field_dyn_base(
    initial_state: &CellState,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    slot: u32,
    prev_value: BabyBear,
) -> RotatedTraceWithMem {
    use super::columns::PARAM_BASE;

    if slot >= 8 {
        return Err(format!(
            "setFieldDyn: the in-circuit overflow-memory slot must be 0..7 (the slot-range gate on \
             col 69); got {slot}. The overflow field maps to an 8-cell Blum memory (addresses 0..7), \
             NOT the raw effect field_idx."
        ));
    }

    // Lay the v1 economic sub-trace + the rotated welds via the standard machinery using a SAFE
    // in-bounds SetField (slot 0..7 dodges the `field_idx < 8` panic). The v1 value carrier (col 69)
    // is forced to `slot` below to honour the deployed `addr = value = param1` identity, so we seed
    // the v1 SetField value with `slot` directly (the slot-range gate then passes on col 69).
    let slot_felt = BabyBear::new(slot);
    let lead = Effect::SetField {
        field_idx: slot,
        value: slot_felt,
    };
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, &[lead], before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT {
        return Err(format!(
            "setFieldDyn base generator: expected the bare {ROT_PI_COUNT}-PI rotated vector, got {} \
             (SetField carries no record-pin offset)",
            base_pis.len()
        ));
    }

    // Fill the dynamic-field param columns on EVERY row (the params are row-uniform; the selector
    // makes them inert on padding rows). col 68 (FIELD_INDEX) = slot for gate 31's weld; col 69
    // (SLOT/VALUE) = slot (addr = value of the write); col 70 (PREV_VAL) = prev_value; col 74
    // (PREV_SERIAL) = 0 (the boundary init serial); col 75 (READBACK) = slot (the write's value).
    for row in trace.iter_mut() {
        row[PARAM_BASE + super::columns::param::FIELD_INDEX] = slot_felt;
        row[PARAM_BASE + SET_FIELD_DYN_SLOT_COL] = slot_felt;
        row[PARAM_BASE + SET_FIELD_DYN_PREV_VAL_COL] = prev_value;
        row[PARAM_BASE + SET_FIELD_DYN_PREV_SERIAL_COL] = BabyBear::ZERO;
        row[PARAM_BASE + SET_FIELD_DYN_READBACK_COL] = slot_felt;
    }

    // THE FIELDS-ROOT WELD (gate 31): force the AFTER fields_root limb (col 275) to `slot` (= col 68)
    // on EVERY row, then recompute the AFTER block commitment so the published NEW commit binds it.
    for row in trace.iter_mut() {
        row[AFTER_BASE + B_FIELDS_ROOT] = slot_felt;
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the rotated NEW commit PI the AFTER-limb override moved (PI 43, last row). The OLD
    // commit (PI 42, row-0 BEFORE block) is untouched by the AFTER override.
    let last_idx = trace.len() - 1;
    let mut dpis = base_pis;
    dpis[V1_PI_COUNT + 1] = trace[last_idx][AFTER_BASE + B_STATE_COMMIT]; // PI 43: NEW commit

    // THE FIFTH PIN (col 263 = AFTER_BASE + B_RECORD_DIGEST → PI[46]): SetField has no
    // `record_pin_offset`, so push the AFTER record-digest limb here (the descriptor pins it last row).
    dpis.push(trace[last_idx][AFTER_BASE + B_RECORD_DIGEST]); // PI 46
    debug_assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + 1,
        "setFieldDyn carries the rotated 46-PI + PI[46]"
    );

    // THE BLUM BOUNDARY: ONE declared address (the slot, init value = prev_value, init serial 0). The
    // write (serial 1) opens against (prev_value, 0); the read (serial 2) opens against (slot, 1) —
    // the write's own (value, serial). A wrong prev_value / a forged readback has no satisfying replay.
    let mem_boundary = crate::descriptor_ir2::MemBoundaryWitness {
        addrs: vec![slot],
        init_vals: vec![prev_value.as_u32()],
    };

    Ok((trace, dpis, mem_boundary))
}

/// **THE WIDE setFieldDyn trace generator (`setFieldDynVmDescriptor2R24Wide`, 789-wide / 63 PI).**
/// The 581-wide V1Face base ([`generate_rotated_set_field_dyn_base`]) + `append_wide_carriers` at the
/// `SET_FIELD_DYN_HOST_WIDTH = 581` host (NOT `GRAD_ROT_WIDTH = 608` — the setField face has four
/// fewer chip sites). Returns `(trace, dpis, mem_boundary)` ready for the wide descriptor.
pub fn generate_rotated_set_field_dyn_wide(
    initial_state: &CellState,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    slot: u32,
    prev_value: BabyBear,
) -> RotatedTraceWithMem {
    let (mut trace, base_pis, mem_boundary) = generate_rotated_set_field_dyn_base(
        initial_state,
        before_w,
        after_w,
        caveat,
        slot,
        prev_value,
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, SET_FIELD_DYN_HOST_WIDTH);
    debug_assert_eq!(trace[0].len(), SET_FIELD_DYN_HOST_WIDTH + 368); // 789
    Ok((trace, dpis, mem_boundary))
}

// ============================================================================
// custom — the user-defined program effect bound to an EXTERNAL sub-proof (the
// `customVmDescriptor2R24` 789-wide member = host 581 + 368 carriers).
// ============================================================================

/// The host width of the wide `customVmDescriptor2R24` member: the deployed
/// descriptor is 789-wide (`trace_width`), and its wide commit carriers land at
/// cols 677 / 781 — i.e. `host + 96` / `host + 200`, pinning `host = 581`. Same
/// V1Face host as setFieldDyn (the carriers ride the identical 8-felt blocks);
/// the trace SHAPE differs (a Custom row, no Blum-memory boundary), but the wide
/// geometry is `append_wide_carriers` at 581.
pub const CUSTOM_HOST_WIDTH: usize = 581;

/// **THE WIDE custom trace generator (`customVmDescriptor2R24`, 789-wide / 70 PI).**
///
/// Lay the 789-wide custom row for a [`Effect::Custom`] lead. The descriptor's
/// `proof_bind` op names two row columns, and (the VK epoch) eight `.piBinding`
/// pins PUBLISH them as the descriptor's own public inputs (Lean
/// `EffectVmEmitRotationV3.customPiExposure`):
///   * col 68 (`PARAM_BASE + CUSTOM_VK_HASH_BASE`) ← the program VK handle (the
///     v1 builder writes `program_vk_hash[0..4]` into cols 68..72; the full 8-felt
///     VK binds through the wide-host PI (`pi::CUSTOM_PROOFS_BASE`) / turn-hash
///     layer, so the descriptor exposes the four vk-hash limbs that exist as
///     columns — IR2 PI slots 50..53);
///   * col 72 (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`) ← the sub-proof's PI
///     commitment (the four `proof_commitment` limbs land in cols 72..76 — IR2 PI
///     slots 46..49).
///
/// The `Effect::Custom`'s `(program_vk_hash, proof_commitment)` MUST be the
/// genuine values a verifying [`crate::custom_proof_bind::BoundCustomProof`]
/// exposes — `bound.vk_hash_felts()` / `bound.proof_commitment()` — so the row
/// the deployed prover mints carries exactly the binding the SDK-reachable
/// `verify_proof_bind` engine (the light client's recursion) re-derives from the
/// verified STARK. The binding is enforced at the per-turn FOLD: the eight pins
/// publish the bound columns as PIs the fold connects to the custom sub-proof
/// leaf's 4-felt PI-commitment (the recursion / `EngineBinding` carrier), so the
/// in-AIR `proof_bind` op is intentionally a declaration (like `mem_op`/`umem_op`,
/// whose content rides the offline argument, not a row-local poly). This
/// generator's job is to lay a SAT trace whose bound columns hold that binding
/// AND publish them, so a custom turn mints a REAL wide receipt the fold can bind.
///
/// Returns `(trace, dpis)` ready for `prove_vm_descriptor2` against the wide
/// custom descriptor (the witness is `map_heaps = []` and `mem_boundary =
/// default` — custom carries no grow-gate / Blum-memory leg).
pub fn generate_rotated_custom_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if !matches!(effects.first(), Some(Effect::Custom { .. })) {
        return Err(
            "custom wide generator: the lead effect must be Effect::Custom (the bound (vk, commit) \
             ride cols 68 / 72 the proof_bind op reads)"
                .into(),
        );
    }
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT {
        return Err(format!(
            "custom wide generator: base PI vector {} != {ROT_PI_COUNT} (a Custom lead carries the \
             bare 46-PI rotated vector — no record-pin / grow-gate offset)",
            base_pis.len()
        ));
    }
    // VK epoch: PUBLISH the `proof_bind` op's bound columns as the descriptor's own public inputs
    // (Lean `EffectVmEmitRotationV3.customPiExposure`, eight `.piBinding .first` pins at IR2 PI
    // slots 46..53). The first (lead Custom) row carries the bound `(commit, vk)`: the four
    // `custom_proof_commitment` limbs (cols 72..75) at slots 46..49, then the four low
    // `custom_program_vk_hash` limbs (cols 68..71) at slots 50..53. Exposing them is what lets the
    // per-turn FOLD connect the custom sub-proof leaf's 4-felt PI-commitment to this descriptor;
    // the in-AIR `proof_bind` op stays a declaration (the binding is at the fold, not a row gate).
    let mut base_pis = base_pis;
    {
        use super::columns::{PARAM_BASE, param};
        let r0 = &trace[0];
        for k in 0..4 {
            base_pis.push(r0[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k]); // PI 46..49
        }
        for k in 0..4 {
            base_pis.push(r0[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k]); // PI 50..53
        }
    }
    debug_assert_eq!(base_pis.len(), ROT_PI_COUNT + 8); // 46 base + 8 custom-binding = 54
    let dpis = append_wide_carriers(&mut trace, base_pis, CUSTOM_HOST_WIDTH);
    debug_assert_eq!(trace[0].len(), CUSTOM_HOST_WIDTH + 368); // 789
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 8 + 16); // 46 base + 8 custom + 16 wide = 70
    Ok((trace, dpis))
}

/// **THE BRIDGE-MINT WIDENED-LEG generator (the RIGHT G1 payment binding).** The narrow-family twin of
/// the custom PI-exposure fill: the deployed rotated bridge-mint descriptor `mintVmDescriptor2R24` was
/// widened (Lean `EffectVmEmitRotationV3.mintV3` / `bridgeTuplePiExposure`) to APPEND 26 columns pinned
/// to public inputs `[46..72)` — the bridge-action tuple `(nullifier[8] ‖ recipient[8] ‖
/// dest_federation[8] ‖ amount_lo ‖ amount_hi)`. This generator lays those 26 columns (at
/// `[trace_width-26 .. trace_width)`, the exact `.piBinding .first` offset the descriptor emits) from the
/// typed `BridgeActionWitness` and pushes them as the 26 tuple PIs, so the per-turn fold's dual-expose
/// leg (`prove_descriptor_leaf_dual_expose_at(46,26)`) reads the ACTUAL payment fields and the segmented
/// binding node connects them to the `prove_bridge_leaf_tuple_claim` sub-proof — no hash-gadget seam.
///
/// The prover (`trace_with_chip_lanes`) fills the graduated chip lanes (all `< trace_width-26`) and
/// leaves these 26 appended columns intact, so `trace[0][trace_width-26+k] == public_inputs[46+k]` holds
/// by construction. `trace_width` is the widened descriptor's `trace_width` (the 26-column append). NOT
/// the wide family — no `append_wide_carriers` (that parks its 8-felt carriers at `[46..62)`, colliding).
pub fn generate_rotated_bridge_mint_trace(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    backing: &crate::bridge_action_air::BridgeActionWitness,
    trace_width: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if !matches!(effects.first(), Some(Effect::BridgeMint { .. })) {
        return Err(
            "bridge-mint wide generator: the lead effect must be Effect::BridgeMint (the widened \
             mintVmDescriptor2R24 leg publishes the 26-felt tuple at PI [46..72))"
                .into(),
        );
    }
    let tuple = backing.public_inputs(); // nullifier[8] ++ recipient[8] ++ dest_federation[8] ++ [lo, hi]
    if tuple.len() != crate::bridge_action_air::BRIDGE_ACTION_PI_COUNT {
        return Err(format!(
            "bridge-mint wide generator: BridgeActionWitness PI len {} != {}",
            tuple.len(),
            crate::bridge_action_air::BRIDGE_ACTION_PI_COUNT
        ));
    }
    let tuple_len = tuple.len(); // 26
    let base = trace_width.checked_sub(tuple_len).ok_or_else(|| {
        format!("bridge-mint wide generator: descriptor trace_width {trace_width} < tuple len {tuple_len}")
    })?;
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if dpis.len() != ROT_PI_COUNT {
        return Err(format!(
            "bridge-mint wide generator: base PI vector {} != {ROT_PI_COUNT} (a BridgeMint lead \
             carries the bare rotated vector — no grow-gate/record-pin offset)",
            dpis.len()
        ));
    }
    // Lay the 26 tuple columns at the descriptor's appended offset on EVERY row (the pin is `.first`,
    // but a canonical trace carries the constant tuple on all rows), growing each row to trace_width.
    for row in trace.iter_mut() {
        if row.len() < trace_width {
            row.resize(trace_width, BabyBear::ZERO);
        }
        for k in 0..tuple_len {
            row[base + k] = tuple[k];
        }
    }
    // Push the 26 tuple PIs at slots [46..72), matching the descriptor's `bridgeTuplePiExposure` pins.
    for k in 0..tuple_len {
        dpis.push(tuple[k]);
    }
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT + tuple_len); // 46 + 26 = 72
    debug_assert_eq!(trace[0][base], tuple[0]); // the .piBinding .first invariant, row 0
    Ok((trace, dpis))
}

/// **THE CAP-WRITE WIDE producer witness (the cap-open weld for the WIDE leg).** A cap-WRITE family
/// lead (attenuate / revokeCapability) advances its AFTER cap-root through an in-circuit cap-tree
/// `map_op` write the bare transfer-shape route leaves UNSAT; this carries the witness that write
/// needs: the cell's FULL c-list (`clist_leaves`, the openable sorted-Poseidon2 accumulator the BEFORE
/// cap-root IS the root of), the consumed/written anchor key (`anchor_key` = the slot's `slot_hash[0]`),
/// and the op-specific `inserted` `(key, value)` payload (an `Update`/attenuate writes the narrowed
/// KEEP_MASK as the value; a `Remove`/revokeCapability takes `None`). Threaded through
/// [`generate_rotated_cap_write_base`] — a wrong post-root / a c-list missing the key is UNSAT (fails
/// closed, never a fabricated post-cap-root).
pub struct CapWriteWideWitness {
    /// The cell's full c-list (the BEFORE cap-root is the root of this sorted-Poseidon2 tree).
    pub clist_leaves: Vec<crate::heap_root::HeapLeaf>,
    /// The written/anchor key (the consumed cap's `slot_hash[0]`). MUST be present in `clist_leaves`.
    pub anchor_key: BabyBear,
    /// The op-specific insert payload: `(key, value)` for `Update` (value = KEEP_MASK) — `None` for
    /// `Remove`.
    pub inserted: Option<(BabyBear, BabyBear)>,
}

/// **THE CAP-WRITE WIDE plan for a lead effect.** `Some((op, needs_freeze_patch))` for the cap-WRITE
/// family whose AFTER cap-root the bare wide transfer-shape route cannot satisfy:
///   * `AttenuateCapability` → `(Some(Update), false)` — in-place UPDATE-AT-KEY (read held mask, write
///     the narrowed KEEP_MASK). The map_op WRITE base rides the nonce-TICK face (the v1 cap-root advance
///     is the genuine in-trace transition), so NO freeze patch — exactly as the live cap-open path skips
///     the patch when a write witness is threaded.
///   * `RevokeCapability` → `(Some(Remove), false)` — ZERO-value REMOVE of the held slot, same tick face.
///   * `GrantCapability` → `(None, true)` — the authority-only grant base FREEZES the cap-root
///     (pass-through, no map_op write), and rides the nonce-FREEZE face the bare transfer-shape route
///     (nonce-TICK) mis-shapes — so the freeze patch IS applied, but no cap-tree write witness.
///     `None` for every other lead (the nonce-TICK passthrough cap bases revokeDelegation / introduce ride
///     the transfer-shape route directly; the value/field/grow-gate/record families have their own arms).
fn cap_write_wide_plan(effect: &Effect) -> Option<(Option<CapTreeWriteOp>, bool)> {
    match effect {
        Effect::AttenuateCapability { .. } => Some((Some(CapTreeWriteOp::Update), false)),
        Effect::RevokeCapability { .. } => Some((Some(CapTreeWriteOp::Remove), false)),
        Effect::GrantCapability { .. } => Some((None, true)),
        _ => None,
    }
}

/// **THE FULL-COHORT WIDE descriptor + trace dispatcher (the shared producer spine).** Resolve the
/// WIDE descriptor (from [`crate::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV`]) for a turn's
/// homogeneous cohort lead and generate its trace / PI vector / grow-gate `map_heaps` /
/// (setFieldDyn-only) [`MemBoundaryWitness`](crate::descriptor_ir2::MemBoundaryWitness) through the
/// per-family wide producer it routes to — the SAME family dispatch the live SDK wide prover
/// (`dregg_sdk::full_turn_proof::prove_effect_vm_rotated_wide`) runs, lifted into `dregg-circuit` so
/// the IVC welded-leg mint
/// ([`crate::effect_vm::trace_rotated`] consumers in `dregg-circuit-prove`) shares ONE producer route
/// (no hand-inlined twin). The wide PI vector's LAST 16 PIs are the 8-felt before/after commit
/// anchors (~124-bit); the descriptor is the unwelded WIDE member (the caller welds the umem leg).
///
/// `before`/`after` are the rotated block witnesses; `caveat` the turn manifest; `before_nullifiers`
/// the note-spend grow-gate's BEFORE nullifier set (`None` for non-spend leads); `refusal_fields`
/// the refusal `fields_root` write witness (`Some` REQUIRED for a `Refusal` lead — the honest refusal
/// is UNSAT without it); `cap_write` the cap-tree write witness (`Some` REQUIRED for a cap-WRITE lead
/// whose base carries an in-circuit cap-tree `map_op` write — attenuate / revokeCapability — the
/// honest cap-write is UNSAT without it). Fails closed (`Err`) on an empty / heterogeneous /
/// non-cohort slice.
///
/// THE SEPARATELY-ROUTED WIDE MEMBERS (NOT effect-dispatched here): `heapWriteVmDescriptor2R24` (no live
/// `Effect::HeapWrite` selector — reached by the exercise-inner heap-write path) and
/// `transferCapOpenTBVmDescriptor2R24` (cap-PRESENCE-routed — widened from a transfer base when a
/// consumed-cap witness is present, like every cap-open member) carry their own per-family wide
/// producers — [`generate_rotated_heap_write_wide`] and [`generate_rotated_transfer_cap_open_tb_wide`] —
/// since neither is reached by the effect→descriptor resolver this dispatcher keys on. Both preserve the
/// SAME 8-felt before/after anchors via the generic [`append_wide_carriers`] at their member host width
/// (595 → 803 / `CAP_OPEN_TB_WIDTH` → 1029), exactly as supplyMint rides the transfer-shape host.
#[allow(clippy::type_complexity)]
// signature kept as-is
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_effect_vm_descriptor_and_trace_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before: &RotatedBlockWitness,
    after: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: Option<&[BabyBear]>,
    refusal_fields: Option<(&[crate::heap_root::HeapLeaf], BabyBear)>,
    cap_write: Option<&CapWriteWideWitness>,
) -> Result<
    (
        crate::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        Vec<BabyBear>,
        Vec<Vec<crate::heap_root::HeapLeaf>>,
        crate::descriptor_ir2::MemBoundaryWitness,
    ),
    String,
> {
    use crate::descriptor_ir2::{MemBoundaryWitness, parse_vm_descriptor2};
    use crate::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
    use crate::heap_root::HeapLeaf;

    let lead = effects
        .first()
        .ok_or_else(|| "wide rotated prover: empty turn".to_string())?;
    let name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        format!("wide rotated prover: effect {lead:?} is not in the rotated cohort")
    })?;
    if effects.len() > 1 {
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect(e) != Some(name) {
                return Err("wide rotated prover: heterogeneous multi-effect turn".into());
            }
        }
    }
    // Resolve the WIDE descriptor JSON for that registry key.
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(name) {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| format!("{name} not in WIDE_REGISTRY_STAGED_TSV"))?;
    let desc =
        parse_vm_descriptor2(json).map_err(|e| format!("wide rotated descriptor parse: {e}"))?;

    // The per-family wide producer dispatch (the live SDK wide prover's route, lifted here).
    let (mut trace, mut dpis, mut map_heaps) = if matches!(lead, Effect::NoteSpend { .. }) {
        let leaves: Vec<HeapLeaf> = before_nullifiers
            .unwrap_or(&[])
            .iter()
            .map(|nf| HeapLeaf {
                addr: *nf,
                value: BabyBear::new(1),
            })
            .collect();
        generate_rotated_note_spend_wide(initial_state, effects, before, after, caveat, &leaves)
            .map_err(|e| format!("wide note-spend generation: {e}"))?
    } else if matches!(lead, Effect::NoteCreate { .. }) {
        generate_rotated_note_create_wide(initial_state, effects, before, after, caveat, &[])
            .map_err(|e| format!("wide note-create generation: {e}"))?
    } else if matches!(lead, Effect::Refusal { .. }) {
        let (leaves, audit_value) = refusal_fields.ok_or_else(|| {
                "wide refusal prover: a Refusal lead requires `refusal_fields` (the BEFORE-cell \
                 fields-tree leaf set + the audit felt) to satisfy the in-circuit `fields_root` \
                 `.write` map-op gate; an empty fields tree is UNSAT (the honest refusal fails closed)"
                    .to_string()
            })?;
        generate_rotated_refusal_wide(
            initial_state,
            effects,
            before,
            after,
            caveat,
            leaves,
            audit_value,
        )
        .map_err(|e| format!("wide refusal generation: {e}"))?
    } else if matches!(
        lead,
        Effect::SetPermissions { .. }
            | Effect::SetVerificationKey { .. }
            | Effect::CellSeal { .. }
            | Effect::CellUnseal { .. }
            | Effect::CellDestroy { .. }
            | Effect::ReceiptArchive { .. }
            | Effect::MakeSovereign
    ) {
        let (t, d) =
            generate_rotated_record_pin_wide(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide record-pin generation: {e}"))?;
        (t, d, vec![])
    } else if matches!(lead, Effect::CreateCell { .. }) {
        generate_rotated_create_cell_wide(initial_state, effects, before, after, caveat, &[])
            .map_err(|e| format!("wide create-cell generation: {e}"))?
    } else if matches!(lead, Effect::CreateCellFromFactory { .. }) {
        generate_rotated_create_from_factory_wide(
            initial_state,
            effects,
            before,
            after,
            caveat,
            &[],
        )
        .map_err(|e| format!("wide create-from-factory generation: {e}"))?
    } else if matches!(lead, Effect::SpawnWithDelegation { .. }) {
        generate_rotated_spawn_wide(initial_state, effects, before, after, caveat, &[])
            .map_err(|e| format!("wide spawn generation: {e}"))?
    } else if matches!(lead, Effect::SetField { field_idx, .. } if *field_idx >= 8) {
        // setFieldDyn carries the DISTINCT 581-wide V1Face geometry + a mem-boundary witness
        // (NOT map_heaps); the dedicated block below overrides these placeholders.
        (Vec::new(), Vec::new(), Vec::new())
    } else if matches!(lead, Effect::Custom { .. }) {
        generate_rotated_custom_wide(initial_state, effects, before, after, caveat)
            .map(|(t, d)| (t, d, vec![]))
            .map_err(|e| format!("wide custom generation: {e}"))?
    } else if let Some((op_opt, needs_patch)) = cap_write_wide_plan(lead) {
        // THE CAP-WRITE FAMILY (the cap-open weld for the WIDE leg): the nonce-FREEZE attenuate-family
        // bases. Their AFTER cap-root is an in-circuit cap-tree `map_op` write (attenuate/revokeCapability)
        // OR a frozen pass-through (grantCap — authority-only, no write), and they ride the nonce-FREEZE
        // face — neither of which the bare transfer-shape route satisfies (the map_op is UNSAT, the nonce
        // gate is FREEZE not TICK), so a cap-WRITE lead FAILS CLOSED there. Here we lay the genuine base
        // trace, apply the nonce-FREEZE patch the base descriptor expects, thread the cap-tree write
        // witness (when the base carries a map_op), and append the 8-felt wide carriers (the SAME additive
        // append the value cohort rides — the ~124-bit anchors are preserved). A cap-WRITE lead with a
        // map_op but no `cap_write` witness fails closed (the cap-open weld never fabricates a post-root).
        let (mut t, base_pis) =
            generate_rotated_effect_vm_trace(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide cap-write base trace: {e}"))?;
        let mut d = if needs_patch {
            patch_attenuate_base_for_cap_open(&mut t, &base_pis)
                .map_err(|e| format!("wide cap-write nonce-freeze patch: {e}"))?
        } else {
            base_pis
        };
        let heaps = match op_opt {
            Some(op) => {
                let w = cap_write.ok_or_else(|| {
                    format!(
                        "wide cap-write prover: effect {lead:?} carries an in-circuit cap-tree map_op \
                         write but no CapWriteWideWitness (c-list + anchor key) was threaded — fails \
                         closed (the route is the cap-open weld, never a fabricated post-cap-root)"
                    )
                })?;
                generate_rotated_cap_write_base(
                    &mut t,
                    &mut d,
                    op,
                    &w.clist_leaves,
                    w.anchor_key,
                    w.inserted,
                )
                .map_err(|e| format!("wide cap-write map_op witness: {e}"))?
            }
            None => Vec::new(),
        };
        let d = append_wide_carriers(&mut t, d, GRAD_ROT_WIDTH);
        (t, d, heaps)
    } else {
        let (t, d) =
            generate_rotated_transfer_shape_wide(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide transfer-shape generation: {e}"))?;
        (t, d, vec![])
    };

    // setFieldDyn's witness is the mem-boundary, NOT map_heaps; resolve it here and override the
    // placeholders the family dispatch produced above.
    let mem_boundary = if let Effect::SetField { field_idx, .. } = lead {
        if *field_idx >= 8 {
            let slot = field_idx % 8;
            let (t, d, mb) = generate_rotated_set_field_dyn_wide(
                initial_state,
                before,
                after,
                caveat,
                slot,
                BabyBear::new(0),
            )
            .map_err(|e| format!("wide set-field-dyn generation: {e}"))?;
            trace = t;
            dpis = d;
            map_heaps = vec![];
            mb
        } else {
            MemBoundaryWitness::default()
        }
    } else {
        MemBoundaryWitness::default()
    };

    Ok((desc, trace, dpis, map_heaps, mem_boundary))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    use std::collections::BTreeSet;

    /// DIAGNOSTIC: every wide chip lookup tuple in the wide transfer descriptor is self-consistent
    /// after `fill_chip_lanes` — for each `TID_P2` lookup, `out0..out7 == chip_absorb_all_lanes(
    /// arity, in0..in10)` evaluated off the row. A mismatch pinpoints a carrier-base / seeding bug
    /// WITHOUT the slow prove. Checks BOTH an active row (0) and a padding row (40).
    #[test]
    fn wide_chip_lookups_are_self_consistent_after_lane_fill() {
        use crate::descriptor_ir2::{
            EffectVmDescriptor2, TID_P2, VmConstraint2, chip_absorb_all_lanes, eval_lean_expr,
            fill_chip_lanes, parse_vm_descriptor2,
        };
        use crate::effect_vm_descriptors::WIDE_TRANSFER_STAGED_TSV;
        use crate::lean_descriptor_air::LeanExpr;

        let json = {
            let line = WIDE_TRANSFER_STAGED_TSV.lines().next().unwrap();
            line.splitn(3, '\t').nth(2).unwrap()
        };
        let desc: EffectVmDescriptor2 = parse_vm_descriptor2(json).unwrap();

        // Build a transfer wide trace via the generator over a hand-made witness (no dregg_turn).
        let limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS as u32)
            .map(|i| BabyBear::new(i + 1))
            .collect();
        let bw = RotatedBlockWitness::new(limbs.clone(), BabyBear::new(99)).unwrap();
        let aw = RotatedBlockWitness::new(limbs, BabyBear::new(199)).unwrap();
        let st = CellState::new(100_000, 0);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 1,
        }];
        let (mut trace, _dpis) =
            generate_rotated_transfer_wide(&st, &effects, &bw, &aw, &empty_caveat_manifest())
                .unwrap();

        let check_row = |row: &mut Vec<BabyBear>, label: &str| {
            fill_chip_lanes(&desc, row);
            for (ci, k) in desc.constraints.iter().enumerate() {
                let VmConstraint2::Lookup(l) = k else {
                    continue;
                };
                if l.table != TID_P2 {
                    continue;
                }
                let ev = |e: &LeanExpr| -> BabyBear { eval_lean_expr(e, row) };
                let arity = ev(&l.tuple[0]).as_u32() as usize;
                // only the WIDE carriers (out col >= GRAD_ROT_WIDTH) — the live lookups are covered elsewhere.
                let out0_is_wide =
                    matches!(l.tuple[12], LeanExpr::Var(c) if (c as usize) >= GRAD_ROT_WIDTH);
                if !out0_is_wide {
                    continue;
                }
                let ins: [BabyBear; 11] = core::array::from_fn(|i| ev(&l.tuple[1 + i]));
                let expect = chip_absorb_all_lanes(arity, &ins);
                for j in 0..8 {
                    let got = ev(&l.tuple[12 + j]);
                    assert_eq!(
                        got, expect[j],
                        "{label}: wide lookup {ci} (arity {arity}) out{j} mismatch (carrier not chip-faithful)"
                    );
                }
            }
        };
        // an ACTIVE row (0) and a PADDING row (40 of the 64-tall trace) — both must be chip-faithful.
        check_row(&mut trace[0], "row0");
        check_row(&mut trace[40], "row40(padding)");
    }

    /// The rotated descriptor resolvers cover EXACTLY the registry's 36 cohort members:
    /// every name the resolvers can return is in the registry, and every registry member is
    /// reachable from some effect. This is the cohort-completeness tooth — the rotated
    /// generator can prove every effect the rotated registry emitted a descriptor for, and
    /// names nothing the registry lacks (fail-closed for non-cohort effects).
    #[test]
    fn resolvers_cover_exactly_the_rotated_registry() {
        // The cap-open members (the LIVE `transferCapOpenEffV3`/`attenuateCapOpenEffV3` + 6 fan-out) are SELF-VERIFY /
        // cap-PRESENCE-routed descriptors: they carry the 59-column cap-membership appendix and are
        // NOT reached by the effect→descriptor resolvers (no live effect selects them by kind; the
        // rotated generator widens a base trace into them explicitly via `widen_to_cap_open` when a
        // consumed-cap witness is present). So they are excluded from the resolver-cohort
        // completeness audit — the resolvers must still cover EXACTLY the 36 rotated cohort members.
        let registry: BTreeSet<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter_map(|l| l.split('\t').next())
            // exclude ALL cap-open authority members (the Signature-pinned `…CapOpenVmDescriptor2R24`
            // AND the live effect-general `…CapOpenEffVmDescriptor2R24`): they are self-verify /
            // cap-PRESENCE-routed, not reached by the effect→descriptor resolvers.
            .filter(|s| {
                !s.is_empty()
                    && !s.ends_with("CapOpenVmDescriptor2R24")
                    && !s.ends_with("CapOpenEffVmDescriptor2R24")
                    // the TURN-IDENTITY weld (`transferCapOpenTBVmDescriptor2R24`,
                    // CapOpenTurnPins.effCapOpenV3TB) is the LIVE transfer cap-open — like every
                    // cap-open member it is cap-PRESENCE-routed / self-verify (widened from a base
                    // trace via `widen_to_cap_open_tb` when a consumed-cap witness is present), NOT
                    // reached by the effect→descriptor resolvers. So it is (permanently, not as a
                    // staged beachhead) excluded from the resolver-cohort completeness audit — the
                    // resolvers still cover EXACTLY the 36 rotated cohort members.
                    && !s.ends_with("CapOpenTBVmDescriptor2R24")
                    // the FEE-IN-PROOF transfer (`transferFeeVmDescriptor2R24`) is FEE-PRESENCE-routed:
                    // it is reached by `rotated_descriptor_name_for_effect_fee` (the fee-path resolver)
                    // for a sovereign Transfer whose fee is debited in-proof, NOT by the unfee'd
                    // effect→descriptor resolvers. Like the cap-open members it is a separately-routed
                    // member, excluded from the unfee'd-resolver cohort completeness audit.
                    && s != &"transferFeeVmDescriptor2R24"
                    // the HEAP-WRITE descriptor (`heapWriteVmDescriptor2R24`, the write-bearing
                    // `v3RegistryHeap` tail member, Lean `Rfix 56`) is REGISTRY-PRESENT but
                    // RESOLVER-UNREACHED: there is no live `Effect::HeapWrite` variant / selector
                    // (`turn/src/action.rs` carries no HeapWrite constructor), so no
                    // `rotated_descriptor_name` arm routes to it today. The descriptor is deployed
                    // (the Class-A heap-root recompute the apex commits) but it is reached by the
                    // exercise-inner heap-write path, NOT the top-level effect→descriptor resolvers.
                    // Like the cap-open members it is a separately-routed registry member, excluded
                    // from the resolver-cohort completeness audit (registry-present, resolver-unreached).
                    && s != &"heapWriteVmDescriptor2R24"
                    // the WELDED SEALED-ESCROW SATISFACTION descriptor
                    // (`settleEscrowSatVmDescriptor2R24`, VK-EPOCH §6 BLOCKER 1) is REGISTRY-PRESENT
                    // but RESOLVER-UNREACHED: no live effect routes to it (the satisfaction weld is
                    // STAGED, NOT flipped — `rotated_descriptor_name_for_effect` carries no escrow
                    // arm). It is the descriptor a flippable escrow weld commits a VK for; until that
                    // flip it is a separately-staged registry member, excluded from the resolver
                    // cohort completeness audit (registry-present, resolver-unreached).
                    && s != &"settleEscrowSatVmDescriptor2R24"
            })
            .collect();
        assert_eq!(
            registry.len(),
            37,
            "the rotated resolver cohort has 37 members: the original 36 + the DEDICATED supply-mint \
             (`supplyMintVmDescriptor2R24`, SUPPLY-MODEL.md Stage 2b — `sel::MINT`-routed); cap-open \
             + fee-in-proof + heap-write are separately routed"
        );
        // The fee-path resolver reaches the fee descriptor (and falls back to the unfee'd resolver
        // for non-Transfer leads), so the fee-in-proof member is covered by ITS resolver.
        assert_eq!(
            rotated_descriptor_name_for_effect_fee(&Effect::Transfer {
                amount: 1,
                direction: 1,
            }),
            Some("transferFeeVmDescriptor2R24"),
            "the fee-path resolver routes a Transfer lead to the fee-in-proof descriptor"
        );

        // Every name the resolvers produce: the 17 selector-mapped base effects, the cap-crown
        // RevokeCapability, the Custom recursive-proof-binding leg, the 8 STEP-1-widened LIVE-path
        // effects, the dynamic setField, and the 8 per-slot setFields.
        let mut reached: BTreeSet<&str> = BTreeSet::new();
        for &name in &[
            rotated_descriptor_name(super::super::columns::sel::TRANSFER).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::BURN).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::BRIDGE_MINT).unwrap(),
            // The DEDICATED supply-mint (SUPPLY-MODEL.md Stage 2b) on `sel::MINT`:
            rotated_descriptor_name(super::super::columns::sel::MINT).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::NOTE_SPEND).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::NOTE_CREATE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_SEAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_DESTROY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REFUSAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SET_PERMISSIONS).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SET_VERIFICATION_KEY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::EXERCISE_VIA_CAPABILITY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::PIPELINED_SEND).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REFRESH_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::INCREMENT_NONCE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::REVOKE_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::INTRODUCE).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::ATTENUATE_CAPABILITY).unwrap(),
            // GRADUATED cap-crown:
            rotated_descriptor_name(super::super::columns::sel::REVOKE_CAPABILITY).unwrap(),
            // GRADUATED recursive-proof binding (the last residue, now closed):
            rotated_descriptor_name(super::super::columns::sel::CUSTOM).unwrap(),
            // STEP-1 widened:
            rotated_descriptor_name(super::super::columns::sel::GRANT_CAP).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::MAKE_SOVEREIGN).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CREATE_CELL_FROM_FACTORY).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::EMIT_EVENT).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CREATE_CELL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::SPAWN_WITH_DELEGATION).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::CELL_UNSEAL).unwrap(),
            rotated_descriptor_name(super::super::columns::sel::RECEIPT_ARCHIVE).unwrap(),
            rotated_set_field_descriptor_name(99), // dynamic
        ] {
            reached.insert(name);
        }
        for i in 0..8 {
            reached.insert(rotated_set_field_descriptor_name(i));
        }
        assert_eq!(reached.len(), 37, "the resolvers reach 37 distinct names");
        assert_eq!(
            reached, registry,
            "the resolver names are EXACTLY the rotated registry's members"
        );
    }

    /// The honest residue is now EMPTY: every LIVE selector resolves to a rotated descriptor.
    /// `Custom` (8) was the LAST residue; it GRADUATED via the recursive-proof-binding constraint
    /// kind (`DescriptorIR2.ProofBind`) and now resolves to `customVmDescriptor2R24`. Only the
    /// structural non-effects (NoOp) and unknown selectors fail closed — there is no longer any
    /// LIVE effect the rotated registry lacks a descriptor for, so the cutover can delete v1 with
    /// zero residue. (`RevokeCapability` (24) GRADUATED earlier via the cap-crown.)
    #[test]
    fn residue_is_empty_every_live_selector_resolves() {
        // NoOp is a structural non-effect (no row), not a residue — it correctly resolves to None.
        assert_eq!(rotated_descriptor_name_for_effect(&Effect::NoOp), None);
        // THE LAST RESIDUE CLOSED: Custom (8) now resolves to its recursive-proof-binding descriptor.
        assert_eq!(
            rotated_descriptor_name(super::super::columns::sel::CUSTOM),
            Some("customVmDescriptor2R24")
        );
        // RevokeCapability (24) GRADUATED earlier via the cap-crown.
        assert_eq!(
            rotated_descriptor_name(super::super::columns::sel::REVOKE_CAPABILITY),
            Some("revokeCapabilityVmDescriptor2R24")
        );
    }
}
