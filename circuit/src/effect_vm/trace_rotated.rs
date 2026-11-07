//! # `trace_rotated` — the live rotated (R=24) trace generator.
//!
//! From the 188-column v1 face plus a per-turn rotated witness, this module builds the current
//! 709-column ungraduated trace: two 239-column state blocks and the 43-column caveat region.
//! Chip graduation appends 7 lanes at each of 134 sites, producing the deployed 1647-column base
//! shape. The common rotated PI vector is [`ROT_PI_COUNT`] entries ([`V1_PI_COUNT`] v1 + four
//! rotated commit pins) — 39 = 35 + 4 since the 2026-08-07 seven-slot compaction, 46 = 42 + 4
//! before it; wide members append the DFA and faithful-commitment carriers from that base.
//!
//! ⚠ **PROSE RESIDUE, MEASURED 2026-08-07 AND NOT SWEPT.** Roughly thirty comments and docblocks
//! below this line still say `46` / `PI 46` / `PIs 46..=52` / `47..50` where they mean
//! `ROT_PI_COUNT` / `ROT_PI_COUNT + k`, and `effect_vm_descriptors.rs` carries about twenty-five
//! more (`"rotated 46-PI"`). Every LOAD-BEARING literal in the rotated family was resolved against
//! the emitted registry and converted to a derivation; these are narration only, and they are
//! listed here rather than half-corrected because a partly-updated set of numbers reads worse than
//! a uniformly stale one. `docs/PI-DISPOSITION.md` §6 is the authority; when in doubt read
//! `V1_PI_COUNT` / `ROT_PI_COUNT` below, never a number in a sentence.
//!
//! ## Law #1 — the shapes come from Lean
//!
//! Every quantity this module computes matches a Lean definition (the Rust interprets, never
//! invents):
//!
//! * the 178-limb absorption order is `EffectVmEmitRotationV3.preLimbsAt`; the caller's
//!   `RotatedBlockWitness::pre_limbs` is already in that order, and `NUM_PRE_LIMBS` plus every
//!   faithful-8 group coordinate are generated from the verified Lean `rotated178` layout;
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
//! The four appended PI carriers are PI 42..45: row-0 BEFORE `state_commit`, last-row AFTER
//! `state_commit`, last-row AFTER `committed_height`, and last-row `caveat_commit`.
//!
//! The deployed per-turn proof uses the wide rotated registry path. Layout refactors here must remain
//! byte-preserving unless a separately acknowledged federation re-key deliberately regenerates VKs.

use super::bare_floor_refuse_weld;
use super::columns::rotation::caveat as cav;
use super::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
use super::{EFFECT_VM_WIDTH, EffectVmContext, generate_effect_vm_trace_ext};
// The rotated-layout SPINE is Lean-authored: `metatheory/EmitLayoutManifest.lean` emits it into
// `layout_generated.rs`. Read it here instead of re-declaring the 25 constants by hand (the mirror
// that drifted and made every honest setPermissions/setVK turn UNSAT). Renamed twins below alias
// the emitted const (`B_NULLIFIER_ROOT = B_NULLIFIER_ROOT_OFF`, …) so the value still comes from Lean.
pub use crate::effect_vm::layout_generated::*;
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
pub const V1_WIDTH: usize = EFFECT_VM_WIDTH; // 188

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

// `NUM_PRE_LIMBS` is emitted from `rotated178.numPreLimbs` and re-exported above. The circuit and
// both live Rust producers consume that one generated value.

// `B_SPAN` (a rotated block: 178 pre-iroot limbs + iroot + state_commit + 59 chain carriers = 239
// columns) and `C_SPAN` (the widened-caveat region = 43 columns) are Lean-emitted — read from the
// `pub use layout_generated::*` above (Lean `EffectVmEmitRotationV3.{B_SPAN, C_SPAN}`).
/// In-region offset of the PUBLISHED chained caveat commitment — `caveatCommitRc`, the manifest
/// fold EXTENDED over the 4-felt DFA route-commitment carrier. Lean-emitted as `C_COMMIT`.
///
/// ⚑ It used to be the manifest fold alone (in-region 38, now `C_MANIFEST_COMMIT`), with the rc
/// carrier riding beside it, read by nothing. That is why the `withDfaRcPins` pins bound nothing
/// and were deleted by `dropUnforcedPins`. The rc FOLD moved this to in-region 44.
pub const C_CAVEAT_COMMIT: usize = C_COMMIT;
/// In-region base of the 4-felt DFA ROUTE-COMMITMENT carrier (offsets 39..=42 — the dsl rc-EMIT).
/// Carries [`dfa_route_commitment`] of the turn's `Witnessed{Dfa}` proof-wire public inputs on a
/// Dfa-gated turn, ZERO otherwise (the absent sentinel). Filled uniformly on every row by
/// [`fill_caveat`] from [`RotatedCaveatManifest::dfa_rc`]; published as each cohort member's LAST 4
/// member PIs by the Lean `withDfaRcPins` wrap. Lean-emitted as `C_RC_OFF`.
pub const C_DFA_RC_OFF: usize = C_RC_OFF;
/// Width of the DFA route-commitment carrier (4 felts — the same shape as the custom carrier's
/// `custom_proof_commitment`).
pub const DFA_RC_LEN: usize = 4;
/// The appendix: two blocks + the caveat region (2·239 + 43 = 521). Lean-emitted as `APPENDIX_SPAN`.
pub const APPENDIX: usize = APPENDIX_SPAN;
/// The UN-GRADUATED rotated trace width (the rotated main columns BEFORE Phase B-GATE appends the
/// per-chip-lookup 7-lane blocks). `188 + 521 = 709`.
pub const ROT_WIDTH: usize = V1_WIDTH + APPENDIX; // 709

/// The poseidon2-chip lookup SITES a bare graduated v1 FACE contributes, ahead of the rotated
/// appendix (`EffectVmEmit`'s own state/param absorption chain). The rotated cohort's faces all
/// carry the same four.
pub const V1_FACE_SITES: usize = 4;

/// The number of poseidon2-chip lookup SITES the graduated rotated descriptor
/// (`*VmDescriptor2R24`, e.g. `attenuateVmDescriptor2R24`) carries — the per-site lane blocks
/// Phase B-GATE appends at the END of the rotated layout (each chip tuple is 17-wide:
/// `1 arity + 8 inputs + out0 + 7 output-lanes`, the 7 lanes witnessed in appended columns). The
/// committed graduated width is `ROT_WIDTH + 7 * N_ROT_SITES`, matching the regen'd
/// `*VmDescriptor2R24` trace_width. Graduation APPENDS (positions < ROT_WIDTH unchanged).
///
/// ⚑ This used to be the hand-carried arithmetic `2 * (1 + (NUM_PRE_LIMBS - 4) / 3) + 16`, whose
/// own doc-comment had drifted two flag days out of date ("2·59 = 118 sites + the 16 caveat-region
/// sites = 134" described neither the 184-limb value 138 nor the caveat region's actual 10 sites).
/// The appendix site count is now Lean-emitted (`ROT_APPENDIX_SITES`, from `rotV3Appendix` itself),
/// so the rc FOLD's two extra sites arrive here without anyone editing a literal.
pub const N_ROT_SITES: usize = ROT_APPENDIX_SITES + V1_FACE_SITES;

/// The GRADUATED rotated trace width: the un-graduated rotated columns PLUS the 7×`N_ROT_SITES`
/// appended chip-lane columns (`709 + 938 = 1647` = the committed `transferVmDescriptor2R24`
/// trace_width). The honest rotated lane columns (`ROT_WIDTH .. GRAD_ROT_WIDTH`) are filled
/// automatically by the prove wrapper's `descriptor_ir2::fill_chip_lanes`.
pub const GRAD_ROT_WIDTH: usize = ROT_WIDTH + 7 * N_ROT_SITES; // 1647 (REVOKED-ROOT + cells-relocation clean 58×3)

// ============================================================================
// THE AVAILABILITY-WELD PAD (GAP #4 close — the hardened transfer/burn geometry).
// ============================================================================

/// The AVAILABILITY-WELD v1-face pad of the HARDENED transfer member
/// (`transferVmDescriptorAvail`, Lean §11.7): 10 witness columns (3×2 operand limbs + 2 borrow
/// bits + 2 credit-carry bits) at `[V1_WIDTH, V1_WIDTH + 10)`. The rotated appendix of the
/// hardened member rides at `V1_WIDTH + TRANSFER_AVAIL_PAD` (Lean `rotateV3` appends at
/// `d.traceWidth`), so EVERY appendix base shifts by the pad on the hardened trace.
pub const TRANSFER_AVAIL_PAD: usize = super::transfer_avail_weld::AVAIL_WIDTH - EFFECT_VM_WIDTH; // 10
/// The burn twin (`burnVmDescriptorAvail`, Lean §8¾): 8 witness columns — burn is debit-only
/// (no credit carry chain).
pub const BURN_AVAIL_PAD: usize = super::burn_avail_weld::AVAIL_WIDTH - EFFECT_VM_WIDTH; // 8
/// The FEE'D-transfer twin (`transferFeeVmDescriptorAvail`, Lean §11.8): 16 witness columns — the
/// transfer weld's 10 (same indices) + MID intermediate limbs + fee limbs + fee borrow bits (the
/// fee subtraction gets its OWN borrow chain; reusing the transfer chain blind would force
/// `fee = 0`).
pub const TRANSFER_FEE_AVAIL_PAD: usize =
    super::transfer_fee_avail_weld::FEE_AVAIL_WIDTH - EFFECT_VM_WIDTH; // 16

/// The availability-weld pad a ROTATED COHORT DESCRIPTOR demands of its producer trace, read off
/// the descriptor's wire name (the hardened v1 faces are named `…-v1-avail` / `…-v1-fee-avail` and
/// every rotation / refuse-weld wrapper only APPENDS suffixes, so the mark survives to the
/// registry TSV name). `0` for every bare member — the pre-flip registry produces byte-identical
/// traces.
pub fn avail_pad_for_descriptor_name(name: &str) -> usize {
    if name.starts_with("dregg-effectvm-transfer-v1-avail") {
        TRANSFER_AVAIL_PAD
    } else if name.starts_with("dregg-effectvm-transfer-v1-fee-avail") {
        TRANSFER_FEE_AVAIL_PAD
    } else if name.starts_with("dregg-effectvm-burn-v1-avail") {
        BURN_AVAIL_PAD
    } else {
        0
    }
}

/// **The availability pad a COMMITTED WIDE REGISTRY MEMBER demands of its per-family producer.**
///
/// A per-family wide producer (heapWrite / supplyMint / the turn-bound cap-open) is NOT reached by
/// the effect→descriptor resolver, so it never sees a parsed descriptor and cannot call
/// [`avail_pad_for_descriptor_name`] on `desc.name` the way the dispatcher does. It must still lay
/// the face its committed member was emitted at: resolve the member's WIRE NAME out of
/// [`crate::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV`] (field 1 of `key\tname\tjson`) and read
/// the pad off it — derived from the committed bytes, never a literal beside them.
///
/// CROSS-CHECKED AGAINST THE COMPACTION GEOMETRY, and FAIL-CLOSED. The S2 table records each
/// member's block base `bb` — the width of the v1 face its rotated BEFORE limbs sit at — and that is
/// exactly `V1_WIDTH + avail_pad`. If the two disagree the producer would compact the RIGHT column
/// COUNT out of the WRONG BANDS (the avail-shift trap: an honest proof that is silently UNSAT), so
/// this refuses instead of emitting such a row.
pub fn wide_member_avail_pad(registry_key: &str) -> Result<usize, String> {
    let name = crate::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(registry_key) {
                it.next()
            } else {
                None
            }
        })
        .ok_or_else(|| {
            format!("wide_member_avail_pad: {registry_key} not in WIDE_REGISTRY_STAGED_TSV")
        })?;
    let pad = avail_pad_for_descriptor_name(name);
    let (_, bb, _) = super::s2_compact_generated::S2_COMPACT_TABLE
        .iter()
        .find(|(k, _, _)| *k == registry_key)
        .ok_or_else(|| format!("wide_member_avail_pad: {registry_key} not in S2_COMPACT_TABLE"))?;
    if *bb != V1_WIDTH + pad {
        return Err(format!(
            "wide_member_avail_pad: {registry_key} ('{name}') resolves avail pad {pad} (v1 face \
             {}) but its S2 block base is {bb} — the producer would compact the right column COUNT \
             out of the WRONG BANDS and leave the honest proof UNSAT; refusing",
            V1_WIDTH + pad
        ));
    }
    Ok(pad)
}

/// Fill one row's availability-weld witness columns (`[V1_WIDTH, V1_WIDTH + pad)`) from the row's
/// OWN v1 state/param columns: the 15-bit operand limb decompositions + the borrow (and, for
/// transfer, credit-carry; for the fee'd member, MID/fee) bits. Runs on EVERY row — the weld's
/// assembly/range teeth are unconditional, and a NoOp padding row (`amount = 0`, `before = after`)
/// closes the chains with zero bits. Fails closed (the descriptor's UNSAT) on an over-debit /
/// credit-overflow / fee-underflow row. `avail_pad` selects the weld SHAPE — a Transfer lead rides
/// either the bare-transfer 10-col weld or the fee'd 16-col weld, by target descriptor.
fn fill_avail_aux_row(
    row: &mut [BabyBear],
    lead: &Effect,
    avail_pad: usize,
    fee_for_weld: Option<u32>,
) -> Result<(), String> {
    use super::columns::{PARAM_BASE, param};
    let bef = row[STATE_BEFORE_BASE + state::BALANCE_LO].as_u32();
    let aft = row[STATE_AFTER_BASE + state::BALANCE_LO].as_u32();
    match lead {
        Effect::Transfer { .. } if avail_pad == TRANSFER_FEE_AVAIL_PAD => {
            let amount = row[PARAM_BASE + param::AMOUNT].as_u32();
            let direction = row[PARAM_BASE + param::DIRECTION].as_u32();
            // The fee rides the after-block RESERVED carrier (`feeCol`, col 89) — but on the BASE
            // generator pass col 89 still holds the v1 passthrough (`sealed_mask | mode_flag`,
            // pre-surgery), so the fee'd generator passes the REAL fee explicitly. The post-fee
            // surgery RE-RUNS this fill after writing the fee + post-fee balances, so the base
            // pass's aft limbs are transient.
            let fee =
                fee_for_weld.unwrap_or_else(|| row[STATE_AFTER_BASE + state::RESERVED].as_u32());
            for (c, v) in super::transfer_fee_avail_weld::try_fill_transfer_fee_avail_aux(
                bef, aft, amount, fee, direction,
            )? {
                row[c] = BabyBear::new(v);
            }
        }
        Effect::Transfer { .. } => {
            let amount = row[PARAM_BASE + param::AMOUNT].as_u32();
            let direction = row[PARAM_BASE + param::DIRECTION].as_u32();
            for (c, v) in super::transfer_avail_weld::try_fill_transfer_avail_aux(
                bef, aft, amount, direction,
            )? {
                row[c] = BabyBear::new(v);
            }
        }
        Effect::Burn { .. } => {
            let amount = row[PARAM_BASE + param::BURN_AMOUNT_LO].as_u32();
            for (c, v) in super::burn_avail_weld::try_fill_burn_avail_aux(bef, aft, amount)? {
                row[c] = BabyBear::new(v);
            }
        }
        other => {
            return Err(format!(
                "availability weld: no hardened member exists for lead effect {other:?} \
                 (only transfer/burn carry the avail pad)"
            ));
        }
    }
    Ok(())
}

/// In-block offset of the AUTHORITY-DIGEST limb (r23, limb 24) — the single felt
/// folding ALL authority-bearing cell state no other rotated limb carries
/// (permissions / VK / delegate / delegation / program / mode / token_id +
/// visibility / commitments / proved / side-table roots + fields[8..16]). This IS
/// the EffectVM `CellState::record_digest` (the v1-prefix OLD_COMMIT's fourth root
/// input), so the v1 OLD_COMMIT binds the SAME authority residue the rotated weld
/// carries — closing audit P0-2 across BOTH legs.
pub const B_AUTHORITY_DIGEST: usize = B_RECORD_DIGEST;
// The committed base limbs `B_RECORD_DIGEST`(=B_AUTHORITY_DIGEST) · `B_LIFECYCLE` · `B_CAP_ROOT` ·
// `B_COMMITMENTS_ROOT` · `B_HEAP_ROOT` · `B_COMMITTED_HEIGHT` · `B_DISC` · `B_PERMS` · `B_VK` ·
// `B_MODE` · `B_FIELDS_ROOT` · `B_REVOKED_ROOT` are Lean-emitted — read from `layout_generated`
// (`pub use` above), Lean `EffectVmEmitRotationV3.B_*`. The producer writes the corresponding lanes
// and the in-circuit welds read them; a drift here was the setPermissions/setVK UNSAT bug.
/// nullifier-root offset inside a block (limb 26) — the deployed nullifier accumulator's openable
/// sorted-Poseidon2 root the noteSpend grow-gate (`nullifierFreshOp` / `nullifierInsertOp`) opens
/// against. Lean-emitted as `B_NULLIFIER_ROOT_OFF`.
pub const B_NULLIFIER_ROOT: usize = B_NULLIFIER_ROOT_OFF;
// The v12 carrier-octet in-block bases `B_CHILD_VK_OCTET`(89, `child_vk` on a factory block) ·
// `B_CONTRACT_HASH_OCTET`(97, hatchery `contract_hash`) · `B_PUBKEY_OCTET`(105, the operated cell's
// owner key — the one octet non-zero on a generic turn, so it moves every turn's `state_commit`) are
// Lean-emitted — read from `layout_generated` (`pub use` above), Lean
// `EffectVmEmitRotationV3.{B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, B_PUBKEY_OCTET}`.
// `B_IROOT` (in-block offset of the iroot carrier, absorbed last, limb 178) is Lean-emitted — read
// from `layout_generated` (`pub use` above), Lean `EffectVmEmitRotationV3.B_IROOT`.

// ── THE CANONICAL FAITHFUL-8-FELT GROUP TABLE — the ONE Rust source ───────────────────────────────
//
// This table is generated from the verified `rotated178.groupTable`; the setPermissions/setVK
// overlap class is no longer representable as a producer/circuit mirror drift.

// `Felt8Group`, every named `*_GROUP`, and `ROTATED_GROUP_TABLE`/`ALL_FELT8_GROUPS` are
// Lean-generated and re-exported from `layout_generated`; this module carries no coordinate copy.
// `B_STATE_COMMIT` (in-block offset of the `state_commit` carrier, the chain's final digest
// `= hash(last carrier, iroot)`) is Lean-emitted — read from `layout_generated` (`pub use` above),
// Lean `EffectVmEmitRotationV3.B_STATE_COMMIT`.
//
// ⚑ `B_CHAIN_BASE` (in-block base of the chained-absorption intermediate carriers) and
// `B_NUM_CHAIN` (how many of them) are Lean-emitted TOO, as of 2026-07-31 — read from
// `layout_generated` (`pub use` above), projected in `EmitLayoutManifest.lean` off the FIRST SITE
// of `EffectVmEmitRotationV3.rotV3SitesAt`, which is the very object the descriptors are built
// from.
//
// They were `pub const B_CHAIN_BASE: usize = 180;` here — the ONE geometry number on this page
// that was never emitted. The 178 -> 184 flag day moved `B_STATE_COMMIT` 179 -> 185 and the
// committed descriptors' carrier band 180.. -> 186.., and this literal did not move. Both
// producers ([`fill_block`], [`recompute_block_commit`]) then wrote their chain digests ON TOP of
// pre-limbs 180..183, the iroot at 184 and the state-commit carrier at 185, while the descriptor
// audit looked for carriers six columns below where the emitted registry puts them. That is the
// exact class this module's Lean-emitted header exists to make unrepresentable, and it cost 143
// reds in `dregg-circuit` presenting as "the registry is wrong".

/// Absolute base column of the BEFORE rotated block.
pub const BEFORE_BASE: usize = V1_WIDTH; // 188
/// Absolute base column of the AFTER rotated block.
pub const AFTER_BASE: usize = V1_WIDTH + B_SPAN; // 427
/// Absolute base column of the widened-caveat region.
pub const CAVEAT_BASE: usize = V1_WIDTH + 2 * B_SPAN; // 666

/// The number of v1 public inputs the rotated PI vector prefixes. This is the
/// length of the v1 PI window the descriptors pin into — it MUST cover every v1
/// pin, the highest of which is `pi::ACTOR_NONCE`, so it is exactly
/// `pi::ACTOR_NONCE + 1` (held by `pi::v3_drift_guard::v1_window_covers_the_highest_v1_pin`,
/// and by the Lean twin `EffectVmEmit.pi.V1_PI_COUNT` which every v1 descriptor's `piCount`
/// now reads by name). A shorter window would slice the nonce OFF the rotated PI vector,
/// leaving the row-0 nonce boundary pin reading past the slice.
///
/// History, so the number is legible: Phase C (`FAITHFUL-STATE-COMMITMENT.md`) widened
/// OLD/NEW_COMMIT 4→8 each (+8 prefix), pushing `ACTOR_NONCE` 33→41 and the window 34→42. The
/// 2026-08-07 SEVEN-SLOT COMPACTION then deleted v1 offsets 26..32 (`docs/PI-DISPOSITION.md`
/// §6), taking `ACTOR_NONCE` 41→34 and the window 42→35.
pub const V1_PI_COUNT: usize = 35;
/// The rotated public-input count ([`V1_PI_COUNT`] v1 + 4 appended commit/height/caveat pins).
/// 39 since the 2026-08-07 seven-slot compaction; 46 before it.
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
/// `pre_limbs` is the 178-limb absorption vector in the Lean-pinned order
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
///
/// `dfa_rc` is the 4-felt DFA ROUTE-COMMITMENT carrier (the dsl rc-EMIT): on a turn gated by a
/// `Witnessed{Dfa}` predicate it carries [`dfa_route_commitment`] of the verified `DfaProofWire`'s
/// public inputs; on every other turn it is ZERO (the absent sentinel — the default). It rides the
/// caveat region at [`C_DFA_RC_OFF`] (past the `caveatCommit` fold, which stays over the 29
/// manifest felts) and each cohort descriptor publishes it as its LAST 4 member PIs (`withDfaRcPins`),
/// so the per-turn fold can `connect` the re-proven DSL leaf's in-circuit PI-commitment to the
/// deployed leg.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotatedCaveatManifest {
    pub entries: [RotatedCaveatEntry; cav::MAX_CAVEATS],
    /// The DFA route-commitment carrier (ZERO = no Dfa caveat on this turn).
    pub dfa_rc: [BabyBear; DFA_RC_LEN],
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

/// The domain tag of the DFA route-commitment derivation. **This IS
/// `dregg_circuit_prove::custom_proof_bind::CUSTOM_PROOF_PI_DOMAIN`** — the dsl rc anchor reuses
/// the custom proof-bind mechanism term-for-term (a `Witnessed{Dfa}` predicate transition is,
/// byte for byte, the same `CellProgram` STARK object a custom effect re-proves; see
/// `circuit-prove/src/dsl_leaf_adapter.rs`). Duplicated here (with a cross-pin test in
/// `sdk/tests`) because `dregg-circuit` cannot depend on `dregg-circuit-prove`; the fold lane's
/// `custom_proof_pi_commitment` and this function MUST stay byte-identical.
pub const DFA_ROUTE_COMMIT_DOMAIN: &str = "dregg-custom-proof-bind-pi-v1";

/// The canonical 4-felt DFA ROUTE-COMMITMENT of a `Witnessed{Dfa}` proof wire's public inputs —
/// the value the producer lands in the caveat-region rc carrier ([`C_DFA_RC_OFF`]) and the
/// deployed descriptor publishes at its LAST 4 member PIs. Byte-identical to
/// `dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment` (the first 4 felts of the
/// canonical `WideHash::from_poseidon2` squeeze under the custom proof-bind domain), so the fold's
/// re-proven DSL leaf exposes EXACTLY this value in-circuit and the binding node's `connect` bites.
pub fn dfa_route_commitment(public_inputs: &[BabyBear]) -> [BabyBear; DFA_RC_LEN] {
    let felts =
        crate::binding::WideHash::from_poseidon2(DFA_ROUTE_COMMIT_DOMAIN, public_inputs).to_felts();
    [felts[0], felts[1], felts[2], felts[3]]
}

// ============================================================================
// THE GENERATOR.
// ============================================================================

/// Generate the live rotated (R = 24) trace plus its 46-PI vector for one transfer-shaped turn.
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
    generate_rotated_effect_vm_trace_avail(0, initial_state, effects, before_w, after_w, caveat)
}

/// The AVAILABILITY-WELD-AWARE rotated trace generator (the GAP #4 hardened-member producer).
///
/// `avail_pad` is the hardened member's v1-face widening — `0` for every bare cohort member
/// (byte-identical to [`generate_rotated_effect_vm_trace`]), [`TRANSFER_AVAIL_PAD`] /
/// [`BURN_AVAIL_PAD`] for the `…-v1-avail` hardened transfer/burn members (derive it from the
/// TARGET DESCRIPTOR with [`avail_pad_for_descriptor_name`] — the pad is a property of the
/// descriptor being proven, NOT of the lead effect: a transfer routed to the cap-open / fee'd /
/// wide members stays on the bare `0`-pad shape). With a pad the generator:
///  * fills the availability-weld witness columns `[V1_WIDTH, V1_WIDTH + pad)` on EVERY row from
///    that row's own v1 state/param columns (`fill_avail_aux_row` — fails closed on the forgery);
///  * lays the rotated appendix at the SHIFTED bases (`V1_WIDTH + pad + …`, exactly where the
///    hardened descriptor's welds/pins/sites read — Lean `rotateV3` appends at `d.traceWidth`).
pub fn generate_rotated_effect_vm_trace_avail(
    avail_pad: usize,
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    generate_rotated_effect_vm_trace_avail_core(
        avail_pad,
        None,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
    )
}

/// The core of [`generate_rotated_effect_vm_trace_avail`], with the fee'd weld's REAL fee threaded
/// (`fee_for_weld`) — the fee'd generator's base pass runs BEFORE the post-fee column surgery, so
/// the fee weld's availability check (`fee ≤ mid`) must read the published fee, not the transient
/// pre-surgery RESERVED column. `None` everywhere else (byte-identical to the public wrapper).
fn generate_rotated_effect_vm_trace_avail_core(
    avail_pad: usize,
    fee_for_weld: Option<u32>,
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    // The shifted appendix bases (identical to the module constants at pad 0).
    let before_base = V1_WIDTH + avail_pad;
    let after_base = before_base + B_SPAN;
    let caveat_base = before_base + 2 * B_SPAN;
    match (avail_pad, effects.first()) {
        (0, _) => {}
        (p, Some(Effect::Transfer { .. })) if p == TRANSFER_AVAIL_PAD => {}
        (p, Some(Effect::Transfer { .. })) if p == TRANSFER_FEE_AVAIL_PAD => {}
        (p, Some(Effect::Burn { .. })) if p == BURN_AVAIL_PAD => {}
        (p, lead) => {
            return Err(format!(
                "rotated generator: avail pad {p} does not match lead effect {lead:?} \
                 (transfer pad = {TRANSFER_AVAIL_PAD}, fee'd transfer pad = \
                 {TRANSFER_FEE_AVAIL_PAD}, burn pad = {BURN_AVAIL_PAD})"
            ));
        }
    }
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

    // Widen each row to the rotated width and fill the appendix (at the avail-shifted bases).
    // With a pad, first lay the availability-weld witness columns from the row's OWN v1 columns
    // — the hardened member's borrow/carry teeth read them beside the unmoved v1 layout.
    for row in trace.iter_mut() {
        row.resize(ROT_WIDTH + avail_pad, BabyBear::ZERO);
        if avail_pad > 0 {
            fill_avail_aux_row(row, &effects[0], avail_pad, fee_for_weld)?;
        }
        // ⚑ Each `fill_block` also lays ITS OWN block's fields-canonicity aux (`fill_canon9_block`,
        // 2026-07-31) — the aux reads the nonet lanes `fill_block` writes, so the two are one act.
        fill_block(row, before_base, 0, STATE_BEFORE_BASE, before_w);
        fill_block(row, before_base, 1, STATE_AFTER_BASE, after_w);
        fill_caveat(row, caveat_base, caveat);
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
    // current committed carrier columns.)
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    let mut dpis: Vec<BabyBear> = pis[..V1_PI_COUNT].to_vec();
    dpis.push(r0[before_base + B_STATE_COMMIT]); // PI V1_PI_COUNT: rotated OLD commit
    dpis.push(last[after_base + B_STATE_COMMIT]); // PI 43: rotated NEW commit
    dpis.push(last[after_base + B_COMMITTED_HEIGHT]); // PI 44: committed height
    dpis.push(last[caveat_base + C_CAVEAT_COMMIT]); // PI 45: caveat commit
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT);

    // THE C4 LAST-FLIP-GATE (note-spend nullifier weld): a NoteSpend turn rotates against the
    // `noteSpendVmDescriptor2R24` descriptor, which carries a FIFTH appended PI pin
    // (`EffectVmEmitRotationV3.noteSpendV3`) welding the spend row's folded nullifier
    // (`param::NULLIFIER = param0`, col `PARAM_BASE + 0`) to rotated PI slot 46 on the FIRST
    // row — the rotated analog of the v1 hand-AIR D5 cross-binding (offset 198). The note-spend
    // spend is laid on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm), so the pin
    // reads `r0[PARAM_BASE + param::NULLIFIER]`. We append it ONLY for a NoteSpend lead effect,
    // matching the descriptor's 47-PI shape (the prover asserts `pis.len() == piCount`); the
    // other cohort members keep the 46-PI vector. This lets a note-spending turn rotate:
    // `verify_full_turn` step 8 reads PI[46] instead of refusing the rotated leg.
    if matches!(effects.first(), Some(Effect::NoteSpend { .. })) {
        use super::columns::{PARAM_BASE, param};

        // SINGLE-SPEND INVARIANT (the soundness tooth must survive rotation). The v1 hand-AIR
        // gate is PER-ROW (`s_notespend·(param0 − PI[NOTESPEND_NULLIFIER])` on EVERY spend row)
        // AND v1 surfaces ONE nullifier into the single PI slot — so a turn with two DISTINCT
        // nullifiers is UNSAT on v1 (`trace.rs` D5: "multi-distinct-nullifier proofs need PI
        // extension — deferred"). The rotated weld is a FIRST-row pin against the SAME single PI
        // slot (PI[46]), cross-checked by `verify_full_turn` step 8 against the one freshness
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

        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 46: the spend row's folded nullifier
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
    // FIFTH last-row PI pin welding that limb to rotated PI slot 46; a frozen-lifecycle /
    // un-written-record / frozen-audit-slot AFTER block FAILS the pin and is UNSAT. We push the
    // honest post value (read from the LAST row's AFTER block, exactly the column the pin binds)
    // so the honest trace satisfies it; the verifier recomputes PI[46] from the committed
    // pre-state + the effect, so a forgery cannot match it. Other cohort members keep the
    // 46-PI vector.
    if let Some(off) = record_pin_offset(effects.first()) {
        dpis.push(last[after_base + off]); // PI 46: the correctly-written post lifecycle / record digest
        // H1: the RECORD-DIGEST movers (off == B_AUTHORITY_DIGEST: setPerms/setVK/makeSovereign/refusal)
        // pin ALL 8 faithful authority limbs (`withRecordPin8Headroom2`): limb-0 above + the 7 headroom
        // limbs (AFTER offsets 12..18) at PI 47..53. Push the honest post values (read from the LAST
        // row's AFTER block, the columns the pins bind); the verifier anchors PI 46..53 to
        // `compute_authority_digest_8(post_cell)`, so a 31-bit-colliding wide-open authority forged into
        // ANY of the 8 limbs is UNSAT (the GENTIAN close for movers). Lifecycle movers (off ==
        // B_LIFECYCLE) keep the single limb-0 pin.
        if off == B_AUTHORITY_DIGEST {
            for i in 0..7 {
                dpis.push(last[after_base + 12 + i]);
            }
            debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 8);
        } else {
            debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);
        }
    }

    // THE ACCOUNTS-SET GROW-GATE PIN (createCell / factory / spawn — the deployment-real account
    // set-insert close). The live `{createCell,factory,spawn}VmDescriptor2R24` carry a FIFTH pin
    // welding the new-cell key (`param0`, col `PARAM_BASE + 0` — the `Effect::CreateCell`/`Spawn`/
    // `Factory` arm writes the child id there on row 0) to rotated PI slot 46, plus the two
    // `cells_root` map-ops (limb 0) that force the accounts set-insert. We push the row-0 new-cell
    // key so the honest trace matches the 47-PI shape; the openable before/after cells trees are
    // threaded by `generate_rotated_create_cell_trace_with_accounts_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.{createCellV3,factoryV3,spawnV3}`.
    if let Some(key_col) = new_cell_key_param_col(effects.first()) {
        use super::columns::PARAM_BASE;
        dpis.push(r0[PARAM_BASE + key_col]); // PI 38: the new-cell key
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE FACTORY CARRIER-OCTET PINS (STEP 3 — the direct child_vk8 / contract_hash8 PI exposure).
    // The deployed `factoryVmDescriptor2R24` is `withAfterOctetPins (withAfterOctetPins factoryV3
    // B_CHILD_VK_OCTET) B_CONTRACT_HASH_OCTET` (Lean `factoryV3Carriers`, piCount 47 → 63): 16 TAIL
    // pins publishing the committed AFTER-block carrier octets — child_vk8 (limbs 89..=96,
    // PI 47..54: the executor's REAL installed child VK, which the hatchery-INVARIANT carrier also
    // rides) then contract_hash8 (limbs 97..=104, PI 55..62: the hatchery-mint
    // `HpresProof::Attested` content hash, ZERO on a plain factory turn). The octet columns are the
    // STEP-2/2.5 committed fills (carrier material absorbed into `state_commit`), so the pins read
    // the LAST row's AFTER block — exactly the columns the Lean pins bind, and a forged octet
    // mismatches the committed commitment. They ride AFTER the grow-gate pin (PI 46) and BEFORE
    // the dsl rc tail (PI 63..66) — per-effect extras first, rc last-pre-wide.
    if matches!(effects.first(), Some(Effect::CreateCellFromFactory { .. })) {
        for k in 0..8 {
            dpis.push(last[after_base + B_CHILD_VK_OCTET + k]); // PI 47..54: child_vk8
        }
        for k in 0..8 {
            dpis.push(last[after_base + B_CONTRACT_HASH_OCTET + k]); // PI 55..62: contract_hash8
        }
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT + 16);
    }

    // THE BRIDGE-MINT FELT MINT-HASH PIN (STEP 2/3 — the bridge carrier's deployed-leg exposure).
    // The deployed `mintVmDescriptor2R24` (Lean `mintV3BridgeHash`) carries a FIFTH appended PI
    // pin welding the mint row's `mint_hash` (`param::MINT_HASH = param0`, col `PARAM_BASE + 0`)
    // to rotated PI slot 46 on the FIRST row — the bridge twin of the noteSpend nullifier weld.
    // Since the STEP-1 executor re-align, `mint_hash` is the FELT-DOMAIN
    // `note_spend_mint_hash_felt` (`dsl::note_spending::bridge_mint_hash_felt` over the six
    // compressed felts `apply_bridge_mint` enforces the note-spend STARK against), so the
    // published PI is the value the recursion note-spend leaf recomputes IN-AIR at its claim
    // lane 6 — the fold's `connect` anchor. Rides BEFORE the dsl rc tail (rc 47..50) —
    // per-effect extras first, rc last-pre-wide. The supply-mint member (`sel::MINT`,
    // `supplyMintVmDescriptor2R24`) keeps the 46-PI shape (no pin).
    if matches!(effects.first(), Some(Effect::BridgeMint { .. })) {
        use super::columns::{PARAM_BASE, param};

        // SINGLE-MINT INVARIANT (the noteSpend single-spend discipline, same reasoning): the
        // pin is a FIRST-row pin against ONE PI slot, and the fold's binding node connects ONE
        // exposed mint identity to ONE re-proven note-spend leaf. A second BridgeMint on a
        // non-first row would be UNPINNED — its mint identity would escape the fold's backing
        // check (fail-open). So the rotated bridge-mint leg accepts exactly ONE mint row; a
        // multi-BridgeMint turn fails closed here and falls back to the v1 leg.
        let mint_count = effects
            .iter()
            .filter(|e| matches!(e, Effect::BridgeMint { .. }))
            .count();
        if mint_count != 1 {
            return Err(format!(
                "rotated bridge-mint leg supports exactly one mint row (the single-identity \
                 fold-backing shape), got {mint_count}; a multi-BridgeMint turn must use the v1 \
                 leg. Rotating it would leave the non-first mint's identity unpinned and ESCAPE \
                 the note-spend fold backing."
            ));
        }

        dpis.push(r0[PARAM_BASE + param::MINT_HASH]); // PI 46: the felt-domain bridge-mint identity
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE COMMITMENTS-SET GROW-GATE PIN (noteCreate — the deployment-real commitment set-insert
    // close, the `commitments_root` flag-day). The live `noteCreateVmDescriptor2R24` carries a FIFTH
    // pin welding the published note commitment (`param0`, col `PARAM_BASE + 0` — the
    // `Effect::NoteCreate` arm writes the commitment there on row 0) to rotated PI slot 46, plus the
    // `commitmentsInsertOp` map-op (limb 27) that forces the commitment set-insert. We push the row-0
    // commitment so the honest trace matches the 47-PI shape; the openable before/after commitments
    // trees are threaded by `generate_rotated_note_create_trace_with_commitments_tree`. Mirrors Lean
    // `EffectVmEmitRotationV3.noteCreateV3`.
    if matches!(effects.first(), Some(Effect::NoteCreate { .. })) {
        use super::columns::{PARAM_BASE, param};
        dpis.push(r0[PARAM_BASE + param::NULLIFIER]); // PI 38: the published note commitment (param0)
        debug_assert_eq!(dpis.len(), ROT_NULLIFIER_PI_COUNT);
    }

    // THE setField VALUE8 TAIL (PIs 46..=52) — the written slot's 7 freed completion lanes, i.e. the
    // HIGH 224 BITS of the written 32-byte field value. The deployed `setFieldVmDescriptor2-{slot}R24`
    // is freeze-EXCEPT + `withSetFieldCompletionPins slot` (Lean `v3RegistryBare`): those lanes are no
    // longer frozen to the pre-state — which is what made an honest `[u8;32]` write with any nonzero
    // byte outside `28..32` UNPROVABLE — but PUBLISHED, so a light client reads them off the PI vector
    // and a lane forged off its published PI is UNSAT (`withSetFieldCompletionPins_rejects_forged_pi`).
    // Same shape as the NoteSpend / NoteCreate arms above; the pins are `.last`, so they read the LAST
    // row, and they ride BEFORE the rc tail (rc is `withDfaRcPins`, the outermost wrap).
    // ⚠ STATIC SLOTS ONLY. `field_idx >= 8` is the setFieldDyn family — a DISTINCT member
    // (`setFieldDynVmDescriptor2R24`, its own V1Face geometry + mem-boundary witness) that carries
    // no completion-lane weld and still wants the bare `ROT_PI_COUNT + rc` shape.
    if let Some(Effect::SetField { field_idx, .. }) = effects.first()
        && (*field_idx as usize) < 8
    {
        let slot = *field_idx as usize;
        // ⚑ READ THE EMITTED NONET TABLE, never a stride. This was
        // `after_base + SETFIELD_VALUE8_LANE_BASE + SETFIELD_VALUE8_PI_LEN * slot + k` — i.e.
        // `113 + LEN·slot + k`, the exact formula `RotatedLayout.fieldLaneCol`'s docstring
        // forbids ("the nonet is deliberately NON-CONTIGUOUS"). It agreed with the layout only
        // while `LEN` happened to equal the completion stride 7; at the nine-lane epoch (`LEN` 7
        // → 8) it would have published slot `j`'s lanes starting inside slot `j+1`'s window, and
        // the ninth lane at `176 + slot` would never have been published at all.
        for lane in 1..=crate::effect_vm::layout_generated::ROTATED_FIELD_COMPLETION_LANES {
            dpis.push(
                last[after_base
                    + crate::effect_vm::layout_generated::ROTATED_FIELD_LANE_COL[slot][lane]],
            );
        }
        debug_assert_eq!(
            dpis.len(),
            ROT_PI_COUNT + crate::effect_vm_descriptors::SETFIELD_VALUE8_PI_LEN
        );
    }

    // THE GRAIN-TURN TAIL (initiative 10, Lean `EffectVmEmitGrainTurnRotated`): the fee pin
    // (`.piBinding .first (prmCol 5)` at `ROT_PI_COUNT`, the `ROT_FEE_PI` slot) then the five
    // written slots' completion lanes (slots 3..=7 in order, each `withSetFieldCompletionPins`'s
    // `.last` pins), all before the rc tail. Read through the emitted nonet table, never a stride.
    if matches!(effects.first(), Some(Effect::GrainTurn { .. })) {
        use super::columns::PARAM_BASE;
        if effects.len() != 1 {
            return Err(format!(
                "rotated grain-turn leg proves exactly ONE grain row (the single-tick shape: the \
                 first-row pin + the window gate make row 0 the only active row), got {}",
                effects.len()
            ));
        }
        dpis.push(r0[PARAM_BASE + 5]);
        for slot in 3..8 {
            for lane in 1..=crate::effect_vm::layout_generated::ROTATED_FIELD_COMPLETION_LANES {
                dpis.push(
                    last[after_base
                        + crate::effect_vm::layout_generated::ROTATED_FIELD_LANE_COL[slot][lane]],
                );
            }
        }
        debug_assert_eq!(dpis.len(), ROT_PI_COUNT + GRAIN_TURN_EXTRA_PIS);
    }

    // THE DSL rc-EMIT TAIL (the `Witnessed{Dfa}` route-commitment exposure). EVERY deployed cohort
    // member is wrapped OUTERMOST through Lean `withDfaRcPins`, publishing the caveat-region DFA
    // route-commitment carrier (cols `CAVEAT_BASE + C_DFA_RC_OFF ..+4`, filled by `fill_caveat`
    // from `caveat.dfa_rc`) as its LAST 4 member PIs — AFTER every per-effect extra pin above and
    // BEFORE the 16 wide commit PIs the wide twin appends. A Dfa-gated turn lands
    // `dfa_route_commitment(DfaProofWire.public_inputs)` here (the fold's `connect` anchor); a turn
    // WITHOUT a Dfa caveat publishes the ZERO sentinel and proves identically (the pins are plain
    // PI bindings over the uniformly-filled carrier).
    for k in 0..DFA_RC_LEN {
        dpis.push(last[caveat_base + C_DFA_RC_OFF + k]);
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
/// publishes the fee as PI slot 46. The descriptor (vs. the unfee'd `transferVmDescriptor2R24`)
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
///   * the 47-PI vector is re-read from the (now post-fee) trace carriers so producer and verifier
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
    generate_rotated_effect_vm_trace_with_fee_avail(
        0,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        fee,
    )
}

/// The AVAILABILITY-WELD-AWARE fee-in-proof generator (the §11.8 hardened fee-member producer).
/// `avail_pad = 0` is byte-identical to [`generate_rotated_effect_vm_trace_with_fee`];
/// [`TRANSFER_FEE_AVAIL_PAD`] targets the hardened `…-v1-fee-avail` member: the appendix bases
/// shift by the pad and the fee-weld witness columns (`[V1_WIDTH, V1_WIDTH + 16)`: operand/MID/fee
/// limbs + borrow/carry/fee-borrow bits) are RE-LAID on every row AFTER the post-fee balance
/// surgery, from the row's own post-fee v1 columns + the published fee. Fails closed (the
/// hardened descriptor's UNSAT) if the fee exceeds the post-move balance on any row.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn generate_rotated_effect_vm_trace_with_fee_avail(
    avail_pad: usize,
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
    if avail_pad != 0 && avail_pad != TRANSFER_FEE_AVAIL_PAD {
        return Err(format!(
            "fee-in-proof generator: avail pad {avail_pad} is neither 0 (bare member) nor the \
             fee'd transfer pad {TRANSFER_FEE_AVAIL_PAD}"
        ));
    }
    // The (pad-shifted) appendix bases — identical to the module constants at pad 0.
    let before_base = V1_WIDTH + avail_pad;
    let after_base = before_base + B_SPAN;
    let caveat_base = before_base + 2 * B_SPAN;

    // The base rotated trace plus 46-PI vector (PRE-fee after-balance, welds, v1 economic block).
    // The REAL fee is threaded to the base pass's fee-weld fill so its availability check
    // (`fee ≤ mid`) is the genuine one, not a read of the pre-surgery RESERVED column.
    let (mut trace, base_pis) = generate_rotated_effect_vm_trace_avail_core(
        avail_pad,
        Some(fee as u32),
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
    )?;

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
            fill_block(&mut trace[r], before_base, 0, STATE_BEFORE_BASE, before_w);
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
        fill_block(&mut trace[r], before_base, 1, STATE_AFTER_BASE, after_w);
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

        // HARDENED MEMBER (§11.8): re-lay the fee-weld witness columns from the row's OWN
        // post-surgery v1 columns (post-fee balances, the NoOp rows' amount = fee / dir = 0
        // rewrite, the fee at col 89) — the base pass's aft/mid limbs were pre-fee transients.
        // The NoOp rows close as a CREDIT chain (`mid = before + fee`, then `mid − fee = after =
        // before`); the transfer row closes its own direction's chain. Fails closed if the fee
        // exceeds the post-move balance (the fee-leg forgery).
        if avail_pad == TRANSFER_FEE_AVAIL_PAD {
            fill_avail_aux_row(&mut trace[r], &effects[0], avail_pad, Some(fee as u32))?;
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
    dpis[V1_PI_COUNT + 1] = last[after_base + B_STATE_COMMIT]; // rotated NEW_COMMIT (post-fee)
    // (the rotated OLD_COMMIT / height / caveat pins are unaffected by the fee; ride the base vector.)
    dpis.push(fee_felt); // PI ROT_PI_COUNT: the published fee (col 89, last-row pinned).
    debug_assert_eq!(dpis.len(), ROT_PI_COUNT + 1);
    // The dsl rc TAIL rides AFTER the fee pin (`withDfaRcPins transferFeeV3`: rc at PI 47..50).
    // The fee surgery never touches the caveat region, so the base generator's rc values are
    // still the trace's carrier values — re-read them from the post-fee last row all the same.
    for k in 0..DFA_RC_LEN {
        dpis.push(last[caveat_base + C_DFA_RC_OFF + k]);
    }

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
    //
    // `CellState.state_commitment` is a CARRIED felt, not a derived one: mutating `fields` leaves it
    // stale, `to_trace_cols` copies the stale value verbatim into row 0's
    // `state_before.state_commit`, and `PI[OLD_COMMIT_BASE..]` is recomputed FRESH from the fields —
    // so the trace and the public input silently disagree. Refresh it here (the same hand repair the
    // other direct-mutation sites carry), which is what `verify_state_integrity`, the
    // witness-generation precondition at the `generate_effect_vm_trace_ext` funnel, requires.
    let mut pre = initial_state.clone();
    pre.fields[leg_a_slot] = before_a;
    pre.fields[leg_b_slot] = before_b;
    pre.refresh_commitment();

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
        // ⚑ THE LANE-0 RE-WELD IS A CANONICITY INPUT. The leg-STATUS flip above moved this row's v1
        // `fields[leg_a]`/`fields[leg_b]`, and `fill_block` welds those into rotated lane 0 — an
        // input to the `2·v = q(q−1)·L0` gate. Before `fill_block` carried `fill_canon9_block`, the
        // aux here kept the PRE-flip lane 0 and the member was UNSAT for any pre-state whose lane 8
        // carried carry digit 2. Today's carrier statuses are small (lane 8 = 0 ⇒ the selector is
        // dead ⇒ the stale value was still 0), which is why nothing had failed yet.
        fill_block(&mut trace[r], BEFORE_BASE, 0, STATE_BEFORE_BASE, before_w);
        fill_block(&mut trace[r], BEFORE_BASE, 1, STATE_AFTER_BASE, after_w);

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

/// **The UNDELEGATED spend's delegation-ancestor id** — the felt an honest producer parks in the
/// deployed `SPEND_ANCESTOR_PARAM_COL` (`prmCol 3` = `PARAM_BASE + 3`, col 71) when the spend is
/// authorized DIRECTLY by the note holder and so rides no delegated capability.
///
/// It is the felt-domain image of the ROOT (mint) derivation node's credential-revocation
/// nullifier — `fold_bytes32_to_bb(cred_nul(mint_provenance()))` in `dregg_cell::derivation` terms.
/// The mint root is the terminus of every derivation chain and is never itself a `RevokeDelegation`
/// target (that verb inserts a CHILD cap's id — `trace.rs`'s `child_hash[0]`), so opening THIS id
/// `.absent` against the committed revoked set is the honest statement "this spend rides no revoked
/// delegation", not a fabricated one.
///
/// The two BLAKE3 domain strings are the ones `dregg_cell::derivation::{mint_provenance, cred_nul}`
/// use. `dregg-cell` depends on `dregg-circuit` (never the reverse), so the agreement cannot be a
/// call across the edge; it is pinned from the cell side by
/// `dregg_cell::derivation`'s `undelegated_spend_ancestor_matches_mint_root` test.
///
/// # FAITHFUL-COMMITMENT-LAW residual (felt-width site #20, kind D — availability, NOT soundness)
///
/// **WHAT IS FOLDED.** A 32-byte BLAKE3 credential-revocation nullifier → ONE BabyBear (~31 bits).
///
/// **WHERE IT LANDS — not a commitment.** The returned felt is written to exactly one place:
/// `row[PARAM_BASE + SPEND_ANCESTOR_PARAM_SLOT]` (col 71) in
/// `generate_rotated_note_spend_trace_with_nullifier_tree`. Col 71 is a v1 PARAM column; the rotated
/// state commitment is `recompute_block_commit`'s Horner chain over `row[BEFORE_BASE .. +
/// NUM_PRE_LIMBS]` / `row[AFTER_BASE .. + NUM_PRE_LIMBS]` (bases 188 / 427), and no PI binds col 71
/// (`rotateV3WithNullifierPin` pins `prmCol 0` only). So this felt is a **map-op KEY in a witness
/// column**, never a committed 32-byte component — the case the law itself calls "a fine per-effect
/// param projector". The accumulator ROOT it opens against IS faithful: the producer writes the
/// 8-lane `revoked_tree.root8()` into `REVOKED_ROOT_GROUP` of both blocks.
///
/// **WHY THE WIDTH IS FORCED (widening is not representable producer-side).** The deployed IR types
/// a map-op key as ONE felt: `Dregg2/Circuit/DescriptorIR2.lean:301-313` has `root, newRoot : Fin 8
/// → EmittedExpr` (the 8-felt groups) but `key : EmittedExpr` — a single expression — and the
/// deployed op is `key := .var SPEND_ANCESTOR_PARAM_COL` (`EffectVmEmitRotationV3.lean:2410`). A
/// producer physically cannot supply eight felts to a one-felt column. The INSERT side is one felt
/// too (`revokedInsertOp` keys on `param0` = `child_hash[0]`, `trace.rs:683`), so widening only the
/// open side would make the `.absent` op unopenable rather than safer. Widening = changing `MapOp`
/// itself + the sorted-bracket/AAFI gadgets to lex-compare 8-felt keys: **VK-affecting, Lean AIR**,
/// and it must ride the same epoch as felt-width #5/#11 (the compare gadget already exists —
/// `Circuit/Emit/LexCompare8Emit.lean::lexLt8_refines`; the leaf-schema widening + kernel flip is
/// the ember-gated part). Not this commit's business.
///
/// **WHAT THE ~31 BITS DO NOT BUY (soundness).** A collision cannot make a revoked ancestor look
/// fresh. The revoked set is keyed by the SAME projection on both sides, and a projection is a
/// function: `A` revoked ⟹ `key(A)` is IN the set ⟹ the `.absent` open for `key(A)` has no
/// bracketing witness, whatever else collides with it. Collisions only ever ADD members to the
/// key-space preimage of the set — they OVER-revoke, never under-revoke. (The real soundness hole on
/// this op is that col 71 is an unbound witness column — a prover parks any non-revoked felt, e.g.
/// this public constant, and the op is satisfied regardless of the exercised lineage. That is
/// `7d49b0f449`'s named follow-up; it costs ZERO work and is unaffected by key width, so widening
/// alone would not close it either.)
///
/// **WHAT THE ~31 BITS DO BUY (availability — the residual's own, real cost).** The revoked set is
/// GROW-ONLY and its key domain is attacker-writable: `RevokeDelegation` inserts
/// `hash_to_8(child_id)[0]` and `CellId::derive_raw` is BLAKE3 over an attacker-chosen
/// `(public_key, token_id)`, so candidate keys are ground OFFLINE. ~2^31 offline hashes find a child
/// id whose lane-0 equals a chosen 31-bit target; one legitimate create+delegate+revoke then plants
/// it permanently. Targeted at THIS constant — which is public, fixed, and system-wide — that
/// permanently bricks every undelegated `NoteSpend` (the guard below starts failing closed, and the
/// in-circuit `.absent` op is UNSAT). Targeted at a victim's real ancestor id it bricks that lineage.
/// With no adversary at all, N live ancestors × M revocations collide with probability ≈ N·M/2^31,
/// which caps the honest scale of the registry. This denial gets HARDER to work around, not easier,
/// once the lineage weld lands: today a producer could sidestep a poisoned key only by exploiting the
/// very unbound-witness hole that weld closes.
///
/// **WHAT CLOSES IT:** the 8-felt map-op key column (`MapOp.key : Fin 8 → EmittedExpr` + lex-8 sorted
/// bracketing, both open and insert sides) AND the col-71 lineage weld, as ONE Lean AIR / VK epoch.
/// Registered as site **#20** in `docs/WOUND-felt-width-boundaries-2026-07-19.md`.
pub fn undelegated_spend_ancestor() -> BabyBear {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-cap-mint-root-v1");
    let mint_provenance: [u8; 32] = *h.finalize().as_bytes();
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-cred-revocation-v1");
    h.update(&mint_provenance);
    let cred_nul: [u8; 32] = *h.finalize().as_bytes();
    // FAITHFUL-COMMITMENT-LAW residual (see the `# FAITHFUL-COMMITMENT-LAW residual` section above,
    // and wound site #20): this felt is a one-felt MAP-OP KEY in witness column 71, not a committed
    // component — and the deployed `MapOp.key : EmittedExpr` is one felt, so 8-felt is not
    // representable without a VK-affecting Lean AIR change. Soundness-neutral (collisions can only
    // over-revoke); the residual is a ~2^31-grind availability wound, registered and priced.
    crate::effect_vm::fold_bytes32_to_bb(&cred_nul) // ast-grep-ignore: degraded-felt-commitment
}

/// The param SLOT the deployed `spendAncestorFreshOp` keys on — Lean
/// `EffectVmEmitRotationV3.SPEND_ANCESTOR_PARAM_COL := prmCol 3`, so the absolute column is
/// `PARAM_BASE + 3 = 71` (the Lean-side `#guard SPEND_ANCESTOR_PARAM_COL == 71`). Free on a
/// noteSpend row: the only other declared user of `prmCol 3` is the lifecycle-payload-hash gate
/// (cellSeal / cellDestroy / receiptArchive), a disjoint descriptor family.
pub const SPEND_ANCESTOR_PARAM_SLOT: usize = 3;

/// **The spend-side DELEGATION-ANCESTOR REVOCATION witness** — the producer input the deployed
/// `spendAncestorFreshOp` (`EffectVmEmitRotationV3.spendAncestorFreshOp`, the THIRD map-op on
/// `noteSpendV3`) consumes: an `.absent` open of the spend's delegation-ancestor id
/// (`SPEND_ANCESTOR_PARAM_COL`) against the limb-37 `revoked_root` accumulator that
/// `revokedInsertOp` grows on `RevokeDelegation` turns.
///
/// A spend does NOT mutate the revoked set, so `before_revoked` is the set on BOTH sides of the
/// turn: the generator writes its `root8` into the `REVOKED_ROOT_GROUP` of the BEFORE *and* the
/// AFTER block (the `.absent` op's `root` and `newRoot` are BOTH `beforeRevokedRootGroup`).
///
/// `before_revoked` must be the set the committed `revoked_root` limb actually stands for. Every
/// live producer today threads `dregg_turn::rotation_witness::empty_revoked_root_8()` (the
/// grow-only registry starts empty), whose `root8` is exactly this witness's with `&[]` — so the
/// override is byte-identical to the committed limb and moves no commitment.
#[derive(Clone, Copy, Debug)]
pub struct SpendRevocationWitness<'a> {
    /// The exercised capability's delegation-ancestor id, in the revoked set's key domain.
    pub ancestor: BabyBear,
    /// The BEFORE (= AFTER) revoked-set leaves the `.absent` open brackets against.
    pub before_revoked: &'a [crate::heap_root::HeapLeaf],
}

impl<'a> SpendRevocationWitness<'a> {
    /// The spend exercises NO delegated capability (direct holder authority): the ancestor is the
    /// mint root ([`undelegated_spend_ancestor`]), opened against `before_revoked`.
    pub fn undelegated(before_revoked: &'a [crate::heap_root::HeapLeaf]) -> Self {
        Self {
            ancestor: undelegated_spend_ancestor(),
            before_revoked,
        }
    }

    /// The spend exercises a DELEGATED capability whose derivation-ancestor id is `ancestor`.
    pub fn under_ancestor(
        ancestor: BabyBear,
        before_revoked: &'a [crate::heap_root::HeapLeaf],
    ) -> Self {
        Self {
            ancestor,
            before_revoked,
        }
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
/// so the gate's key/value are the row's own published columns.
///
/// **THE THIRD MAP-OP (`spendAncestorFreshOp`, limb 37).** The live descriptor also opens the
/// spend's delegation-ancestor id `.absent` against the committed revoked set. `revocation` carries
/// the honest producer's answer to that op: the ancestor id goes into `SPEND_ANCESTOR_PARAM_COL`
/// (`PARAM_BASE + 3`), the revoked set's `root8` into the `REVOKED_ROOT_GROUP` of BOTH blocks (a
/// spend does not revoke, so the set is unchanged), and the set's leaves are returned as the SECOND
/// `map_heaps` entry — the prover resolves each op by matching its `root8` against the threaded
/// heaps. Returns `(trace, dpis, map_heaps)` with `map_heaps = [nullifiers, revoked]`.
pub fn generate_rotated_note_spend_trace_with_nullifier_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: &[crate::heap_root::HeapLeaf],
    revocation: &SpendRevocationWitness<'_>,
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{
        CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX, SENTINEL_MIN,
    };

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
    // The BEFORE tree at NATIVE 8-FELT width (`CanonicalHeapTree8`) — the openable accumulator's
    // FAITHFUL ~124-bit `root8`, NOT the lossy 1-felt scalar. The spent nullifier MUST be absent from
    // BEFORE (the `.absent` freshness precondition); a double-spend has no bracketing witness and the
    // prover REFUSES it.
    let before_tree = CanonicalHeapTree8::new(before_nullifiers.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(nf_key).is_some() {
        return Err(
            "double-spend: the nullifier is already in the BEFORE nullifier tree — the in-circuit \
             freshness (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root8 = before_tree.root8();
    // GAP #5 AAFI FLIP (F1): the committed AFTER nullifier root is now the append-at-free-index
    // fold (`insert_witness_aafi`), NOT the sorted-compacted rebuild — so it EXACTLY equals the
    // `new_root` the deployed `nullifierInsertOp` (now `MapKind::AafiInsert`, op=4) fill recomputes
    // from the SAME before tree. The two-path AAFI gate (low-update → R1, append-at-empty-slot →
    // new_root, + the pointer-bracket range gate) forces sorted-preservation at STABLE positions,
    // closing the double-spend the op=3 single-shared-path insert could not bind. A present /
    // out-of-gap nullifier has no bracketing low leaf ⇒ `insert_witness_aafi` returns `None` ⇒ the
    // turn is UNSAT (the deployed effect-level double-spend refusal).
    let aafi = before_tree
        .insert_witness_aafi(HeapLeaf::entry(nf_key, nf_value))
        .ok_or_else(|| {
            "double-spend / out-of-gap nullifier: the AAFI insert has no bracketing low leaf — the \
             in-circuit two-path (`aafi_insert`) gate refuses the turn"
                .to_string()
        })?;
    let after_root8 = aafi.new_root;

    // THE DELEGATION-ANCESTOR REVOCATION OPEN (`spendAncestorFreshOp`, limb 37). The revoked set is
    // NOT mutated by a spend, so ONE tree serves the op's `root` and `newRoot` (both
    // `beforeRevokedRootGroup`). The ancestor must be openable: sentinel-colliding keys have no
    // bracketing witness and the in-circuit gap teeth would refuse them, so fail closed HERE with a
    // named error rather than mint an unprovable trace.
    let revoked_tree = CanonicalHeapTree8::new(revocation.before_revoked.to_vec(), HEAP_TREE_DEPTH);
    let ancestor = revocation.ancestor;
    if ancestor == SENTINEL_MIN || ancestor.as_u32() >= SENTINEL_MAX.as_u32() {
        return Err(format!(
            "spend delegation-ancestor id {} collides with the revoked-set sentinel range — the \
             `.absent` open has no bracketing witness",
            ancestor.as_u32()
        ));
    }
    if revoked_tree.position_of(ancestor).is_some() {
        return Err(
            "revoked delegation ancestor: the spend's delegation-ancestor id IS in the committed \
             revoked set — the in-circuit `spendAncestorFreshOp` (`.absent`) open has no bracketing \
             witness and refuses the turn"
                .into(),
        );
    }
    let revoked_root8 = revoked_tree.root8();

    let nullifier_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + NULLIFIER_ROOT_GROUP[lane] };
    let revoked_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + REVOKED_ROOT_GROUP[lane] };

    // Write the FAITHFUL 8-felt before/after nullifier-root GROUP into BOTH rotated blocks (lane 0 the
    // scalar limb 26, lanes 1..7 the dedicated completion limbs 68..74 — the map-op `.absent`/`.insert`
    // root/newRoot groups the deployed AIR binds all eight lanes of), NEVER the lane-0 squeeze. The
    // revoked-root GROUP (lane 0 the scalar limb 37, lanes 1..7 the completion limbs 82..88) takes the
    // SAME root on both sides — the spend leaves the revoked set untouched. The ancestor id rides the
    // declared param column the third map-op keys on. Then recompute the dependent chained commitments
    // so the published `STATE_COMMIT` binds the grown nullifier set and the opened revoked set.
    for row in trace.iter_mut() {
        for lane in 0..HEAP_DIGEST_W {
            row[nullifier_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[nullifier_group_col(AFTER_BASE, lane)] = after_root8[lane];
            row[revoked_group_col(BEFORE_BASE, lane)] = revoked_root8[lane];
            row[revoked_group_col(AFTER_BASE, lane)] = revoked_root8[lane];
        }
        row[PARAM_BASE + SPEND_ANCESTOR_PARAM_SLOT] = ancestor;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-26/limb-37 overrides moved the commitments).
    let r0_commit = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    let last_commit = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];
    dpis[V1_PI_COUNT] = r0_commit; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = last_commit; // PI 35: rotated NEW commit

    Ok((
        trace,
        dpis,
        vec![
            before_nullifiers.to_vec(),
            revocation.before_revoked.to_vec(),
        ],
    ))
}

/// The deployed `cells_root` (limb 0 of the rotated block) — the openable sorted-Poseidon2 accounts
/// accumulator. The createCell/factory/spawn descriptors (`EffectVmEmitRotationV3.{createCellV3,
/// factoryV3,spawnV3}`) now carry two map-ops on it: `cellsFreshOp` (`.absent`: the new-cell key is
/// a NON-MEMBER of the BEFORE accounts tree — no id collision) and `cellsInsertOp` (`.insert`: the
/// AFTER root IS the genuine sorted insert of the new-cell key).
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
    use crate::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};

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
    let before_tree = CanonicalHeapTree8::new(before_accounts.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(cell_key).is_some() {
        return Err(
            "account-id collision: the new-cell key is already in the BEFORE accounts tree — the \
             in-circuit no-collision (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root8 = before_tree.root8();
    // GAP #6 AAFI FLIP: the committed AFTER accounts root is now the append-at-free-index fold
    // (`insert_witness_aafi`), NOT the sorted-compacted rebuild — so it EXACTLY equals the `new_root`
    // the deployed `cellsInsertOp` (now `MapKind::AafiInsert`, op=4) fill recomputes from the SAME
    // before tree. The two-path AAFI gate (low-update → R1, append-at-empty-slot → new_root, + the
    // pointer-bracket range gate) forces sorted-preservation at STABLE positions, installing the
    // ImtSorted well-linked invariant `cellsFreshOp`'s pointer-bracket presupposes — closing the
    // forged-cell-birth / identity-takeover the op=3 single-shared-path insert could not bind. A
    // present / out-of-gap new-cell key has no bracketing low leaf ⇒ `insert_witness_aafi` returns
    // `None` ⇒ the turn is UNSAT (the deployed effect-level forged-cell-birth refusal).
    // The born-empty cell rides its own key as its leaf value (tree relinks next_addr).
    let aafi = before_tree
        .insert_witness_aafi(HeapLeaf::entry(cell_key, cell_key))
        .ok_or_else(|| {
            "forged-cell-birth / out-of-gap new-cell key: the AAFI insert has no bracketing low leaf \
             — the in-circuit two-path (`aafi_insert`) gate refuses the turn"
                .to_string()
        })?;
    let after_root8 = aafi.new_root;

    // Mirror of `EffectVmEmitRotationV3.cellsRootGroupCol`: lane 0 = limb 0 (accounts root); the seven
    // DEDICATED completion limbs 169..175 for lanes 1..7. RELOCATED off `revoked_root`'s committed group
    // (82..88) to the fresh clean-alignment lanes the 178-limb widen opened: `cells_root` is circuit-only
    // (ZERO in the producer pre_limbs), so on a createCell/factory/spawn turn this fill no longer clobbers
    // the producer-committed `revoked_root` group. Lanes 176..177 stay pure pad.
    let cells_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + CELLS_ROOT_GROUP[lane] };

    // Write the FAITHFUL 8-felt before/after cells-root GROUP into BOTH rotated blocks (lane 0 the
    // scalar limb 0, lanes 1..7 the dedicated completion limbs 169..175), NEVER the lane-0 squeeze. Then
    // recompute the dependent chained commitments so `STATE_COMMIT` binds the grown set.
    for row in trace.iter_mut() {
        for lane in 0..HEAP_DIGEST_W {
            row[cells_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[cells_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
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
    use crate::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};

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
    let before_tree = CanonicalHeapTree8::new(before_commitments.to_vec(), HEAP_TREE_DEPTH);
    let before_root8 = before_tree.root8();
    // GAP #5 AAFI FLIP (F1): the committed AFTER commitments root is the append-at-free-index fold
    // (`insert_witness_aafi`), matching the `new_root` the deployed `commitmentsInsertOp` (now
    // `MapKind::AafiInsert`, op=4) fill recomputes from the SAME before tree. Routing the
    // grow-only commitment set to AAFI tightens it to a proper SET-insert of a FRESH commitment
    // (the two-path gate binds sorted-preservation at stable positions); a re-published commitment
    // already present has no bracketing low leaf ⇒ `insert_witness_aafi` returns `None` ⇒ UNSAT.
    let aafi = before_tree
        .insert_witness_aafi(HeapLeaf::entry(cm_key, cm_value))
        .ok_or_else(|| {
            "note-create commitment is already present / out-of-gap: the AAFI insert has no \
             bracketing low leaf — the in-circuit two-path (`aafi_insert`) gate refuses the turn"
                .to_string()
        })?;
    let after_root8 = aafi.new_root;

    let commitments_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + COMMITMENTS_ROOT_GROUP[lane] };

    // Write the FAITHFUL 8-felt before/after commitments-root GROUP into BOTH rotated blocks (lane 0
    // the scalar limb 27, lanes 1..7 the dedicated completion limbs 75..81), NEVER the lane-0 squeeze.
    // Then recompute the dependent chained commitments so `STATE_COMMIT` binds the grown set.
    for row in trace.iter_mut() {
        for lane in 0..HEAP_DIGEST_W {
            row[commitments_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[commitments_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-27 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_commitments.to_vec()]))
}

/// **THE DEPLOYMENT-REAL revokeDelegation revoked-set INSERT wiring (the revoked set-insert
/// grow-gate's witness; hole #3 close).** The clone of
/// [`generate_rotated_note_spend_trace_with_nullifier_tree`] for the `revoked_root` limb (limb 37 =
/// [`B_REVOKED_ROOT`]): it makes limb 37 the openable revoked-set accumulator for a RevokeDelegation
/// turn, FORCING the AFTER root from the AAFI two-path insert of the revoked id — never a
/// producer-supplied witness limb.
///   * `before_revoked` are the existing revoked-set leaves in the revoked store's APPEND ORDER (the
///     revoked id MUST be absent — the no-double-revoke precondition the `revokedFreshOp .absent` op
///     enforces);
///   * limb 37 of every before-block is overwritten with the BEFORE tree's root, and limb 37 of every
///     after-block with the `insert_witness_aafi(...).new_root` of BEFORE + the revoked id (the
///     AAFI-native set-insert the `revokedInsertOp .aafiInsert` op=4 forces);
///   * the affected `wireCommitR` chain + `STATE_COMMIT` carriers are recomputed in place, and the
///     OLD/NEW rotated commit PIs are re-derived so the published commitment binds the grown set;
///   * the BEFORE tree's leaves are returned as the single `map_heaps` entry the prover threads.
///
/// The revoked key is the revoke row's `param0` (`PARAM_BASE + param::NULLIFIER` — the `child_hash[0]`
/// the runtime parks per `trace.rs`), mirroring `NULLIFIER_PARAM_COL`; the revoked set is a pure
/// MEMBERSHIP set, so the inserted leaf value is `0` (Lean `revokedInsertOp.value = .const 0`). A
/// double-revoke / out-of-gap id has no bracketing low leaf ⇒ `insert_witness_aafi` returns `None` ⇒
/// the turn is UNSAT (the deployed no-double-revoke refusal). Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_revoke_trace_with_revoked_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_revoked: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    use crate::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};

    if !matches!(effects.first(), Some(Effect::RevokeDelegation { .. })) {
        return Err("revoked-tree wiring is only for a RevokeDelegation lead effect".into());
    }

    // The base rotated trace (carries the welds, the v1 economic block, the revoked-id param0).
    let (mut trace, mut dpis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;

    // The revoked child-capability id, read from the revoke row (row 0): `param0` = `child_hash[0]`.
    // The revoked set is a pure membership set — the leaf value is `0` (Lean `revokedInsertOp.value`).
    let revoked_key = trace[0][PARAM_BASE + param::NULLIFIER];
    let revoked_value = BabyBear::ZERO;

    // The BEFORE revoked tree (the deployed accumulator before the revoke) built from the revoked
    // store's APPEND ORDER at NATIVE 8-FELT width. The revoked id MUST be absent from BEFORE (the
    // `revokedFreshOp .absent` no-double-revoke precondition); an already-revoked id has no bracketing
    // witness and the prover REFUSES it before proving.
    let before_tree = CanonicalHeapTree8::new(before_revoked.to_vec(), HEAP_TREE_DEPTH);
    if before_tree.position_of(revoked_key).is_some() {
        return Err(
            "double-revoke: the revoked id is already in the BEFORE revoked tree — the in-circuit \
             no-double-revoke (`.absent`) op has no bracketing witness and refuses the turn"
                .into(),
        );
    }
    let before_root8 = before_tree.root8();
    // HOLE #3 CLOSE: the committed AFTER revoked root is the append-at-free-index fold
    // (`insert_witness_aafi`), FORCED — it EXACTLY equals the `new_root` the deployed `revokedInsertOp`
    // (`MapKind::AafiInsert`, op=4) fill recomputes from the SAME before tree. The two-path AAFI gate
    // (low-update → R1, append-at-empty-slot → new_root, + the pointer-bracket range gate) forces
    // sorted-preservation at STABLE positions. A present / out-of-gap revoked id has no bracketing low
    // leaf ⇒ `insert_witness_aafi` returns `None` ⇒ the turn is UNSAT.
    let aafi = before_tree
        .insert_witness_aafi(HeapLeaf::entry(revoked_key, revoked_value))
        .ok_or_else(|| {
            "double-revoke / out-of-gap revoked id: the AAFI insert has no bracketing low leaf — the \
             in-circuit two-path (`aafi_insert`) gate refuses the turn"
                .to_string()
        })?;
    let after_root8 = aafi.new_root;

    let revoked_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + REVOKED_ROOT_GROUP[lane] };

    // Write the FAITHFUL 8-felt before/after revoked-root GROUP into BOTH rotated blocks (lane 0 the
    // scalar limb 37, lanes 1..7 the dedicated completion limbs 82..88 — the map-op `.absent`/`.aafiInsert`
    // root/newRoot groups the deployed AIR binds all eight lanes of), NEVER the lane-0 squeeze. Then
    // recompute the dependent chained commitments so the published `STATE_COMMIT` binds the grown set.
    for row in trace.iter_mut() {
        for lane in 0..HEAP_DIGEST_W {
            row[revoked_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[revoked_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }

    // Re-derive the OLD/NEW rotated commit PIs (the limb-37 override moved the commitments).
    dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // PI 34: rotated OLD commit
    dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT]; // PI 35: NEW commit

    Ok((trace, dpis, vec![before_revoked.to_vec()]))
}

/// The exact refusal appendix opens the protocol-reserved audit slot in the V2 fields tree.  The
/// old refusal path reduced both the raw `u64` key and the 32-byte audit value modulo BabyBear before
/// hashing.  This appendix instead constrains the live `FLD2`/`FLN2` state16 sponge schedule over the
/// raw key/value limbs, matching [`crate::openable_fields_root::CanonicalExactFieldsTree8`].
pub const REFUSAL_EXACT_BEFORE_BASE: usize = GRAD_ROT_WIDTH;
pub const REFUSAL_EXACT_OCC_COL: usize = REFUSAL_EXACT_BEFORE_BASE;
pub const REFUSAL_EXACT_OLD_VALUE_BASE: usize = REFUSAL_EXACT_OCC_COL + 1;
pub const REFUSAL_EXACT_OLD_LEAF_STATE_BASE: usize = REFUSAL_EXACT_OLD_VALUE_BASE + 16;
pub const REFUSAL_EXACT_OLD_CUR_BASE: usize = REFUSAL_EXACT_OLD_LEAF_STATE_BASE + 7 * 16;
pub const REFUSAL_EXACT_SIBLING_BASE: usize = REFUSAL_EXACT_OLD_CUR_BASE + 8;
pub const REFUSAL_EXACT_OLD_LEFT_BASE: usize = REFUSAL_EXACT_SIBLING_BASE + 8;
pub const REFUSAL_EXACT_OLD_RIGHT_BASE: usize = REFUSAL_EXACT_OLD_LEFT_BASE + 8;
pub const REFUSAL_EXACT_OLD_NODE_STATE_BASE: usize = REFUSAL_EXACT_OLD_RIGHT_BASE + 8;
pub const REFUSAL_EXACT_DIR_COL: usize = REFUSAL_EXACT_OLD_NODE_STATE_BASE + 6 * 16;
pub const REFUSAL_EXACT_AFTER_BASE: usize = REFUSAL_EXACT_DIR_COL + 1;
pub const REFUSAL_EXACT_NEW_VALUE_BASE: usize = REFUSAL_EXACT_AFTER_BASE;
pub const REFUSAL_EXACT_NEW_LEAF_STATE_BASE: usize = REFUSAL_EXACT_NEW_VALUE_BASE + 16;
pub const REFUSAL_EXACT_NEW_CUR_BASE: usize = REFUSAL_EXACT_NEW_LEAF_STATE_BASE + 7 * 16;
pub const REFUSAL_EXACT_NEW_LEFT_BASE: usize = REFUSAL_EXACT_NEW_CUR_BASE + 8;
pub const REFUSAL_EXACT_NEW_RIGHT_BASE: usize = REFUSAL_EXACT_NEW_LEFT_BASE + 8;
pub const REFUSAL_EXACT_NEW_NODE_STATE_BASE: usize = REFUSAL_EXACT_NEW_RIGHT_BASE + 8;
pub const REFUSAL_EXACT_ACTIVE_COL: usize = REFUSAL_EXACT_NEW_NODE_STATE_BASE + 6 * 16;
pub const REFUSAL_EXACT_COUNT_COL: usize = REFUSAL_EXACT_ACTIVE_COL + 1;
pub const REFUSAL_WRITE_HOST_WIDTH: usize = REFUSAL_EXACT_COUNT_COL + 1;
pub const REFUSAL_EXACT_AUDIT_PI_BASE: usize = ROT_PI_COUNT + 8;
pub const REFUSAL_EXACT_AUDIT_PI_LEN: usize = 16;

fn refusal_exact_sponge_states(preimage: &[BabyBear]) -> Vec<[BabyBear; 16]> {
    use crate::poseidon2::Poseidon2State;

    let mut sponge = Poseidon2State::new();
    sponge.state[4] = BabyBear::new(preimage.len() as u32);
    let mut states = Vec::with_capacity(preimage.len().div_ceil(4) + 1);
    for chunk in preimage.chunks(4) {
        for (lane, value) in chunk.iter().copied().enumerate() {
            sponge.state[lane] += value;
        }
        sponge.permute();
        states.push(sponge.state);
    }
    sponge.permute();
    states.push(sponge.state);
    states
}

fn refusal_exact_sponge_digest(states: &[[BabyBear; 16]]) -> [BabyBear; 8] {
    let absorb = states[states.len() - 2];
    let squeeze = states[states.len() - 1];
    core::array::from_fn(|lane| {
        if lane < 4 {
            absorb[lane]
        } else {
            squeeze[lane - 4]
        }
    })
}

fn refusal_write_states(row: &mut [BabyBear], base: usize, states: &[[BabyBear; 16]]) {
    for (step, state) in states.iter().enumerate() {
        row[base + step * 16..base + (step + 1) * 16].copy_from_slice(state);
    }
}

/// Build the exact pre-wide refusal host.  The returned `map_heaps` is empty: the V2 opening is a
/// first-class state16 appendix, not a legacy scalar `map_op`.  The 16 exact audit limbs are spliced
/// before the uniform four-PI DFA route tail, so the public ABI is
/// `rotated46 || authority8 || audit16 || dfa4` before the faithful wide anchors.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_refusal_trace_with_fields_tree(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_fields_leaves: &[crate::openable_fields_root::ExactFieldsLeaf],
    audit_value: [u8; 32],
) -> RotatedTraceWithHeaps {
    use crate::exact_nullifier_aafi::raw_to_u16_le;
    use crate::heap_root::{HEAP_DIGEST_W, HEAP_TREE_DEPTH};
    use crate::openable_fields_root::{
        EXACT_FIELDS_NODE_DOMAIN, ExactFieldsLeaf, exact_fields_node8, exact_fields_with_reserved,
    };

    if !matches!(effects.first(), Some(Effect::Refusal { .. })) {
        return Err("exact fields-root write wiring is only for a Refusal lead effect".into());
    }

    let (mut trace, mut base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT + 8 + DFA_RC_LEN {
        return Err(format!(
            "exact refusal: base PI vector {} != {} (authority8 + dfa4)",
            base_pis.len(),
            ROT_PI_COUNT + 8 + DFA_RC_LEN
        ));
    }

    let audit_key = crate::openable_fields_root::REFUSAL_AUDIT_EXT_KEY;
    let before_tree =
        exact_fields_with_reserved(before_fields_leaves.to_vec(), &[audit_key], HEAP_TREE_DEPTH)
            .map_err(|error| format!("exact refusal: invalid BEFORE fields tree: {error}"))?;
    let update = before_tree
        .update_witness(ExactFieldsLeaf::present(audit_key, audit_value))
        .ok_or_else(|| "exact refusal: reserved audit slot has no update witness".to_string())?;
    if !update.is_genuine()
        || update.siblings.len() != HEAP_TREE_DEPTH
        || update.directions.len() != HEAP_TREE_DEPTH
    {
        return Err("exact refusal: malformed exact update witness".into());
    }

    let old_leaf_states = refusal_exact_sponge_states(&update.old_leaf.preimage());
    let new_leaf_states = refusal_exact_sponge_states(&update.new_leaf.preimage());
    if old_leaf_states.len() != 7
        || new_leaf_states.len() != 7
        || refusal_exact_sponge_digest(&old_leaf_states) != update.old_leaf.digest8()
        || refusal_exact_sponge_digest(&new_leaf_states) != update.new_leaf.digest8()
    {
        return Err("exact refusal: FLD2 state16 schedule drifted".into());
    }

    let old_value_limbs = raw_to_u16_le(update.old_leaf.value());
    let new_value_limbs = raw_to_u16_le(audit_value);
    let mut old_cur = update.old_leaf.digest8();
    let mut new_cur = update.new_leaf.digest8();
    for level in 0..HEAP_TREE_DEPTH {
        let sibling = update.siblings[level];
        let direction = update.directions[level];
        let (old_left, old_right) = if direction == 0 {
            (old_cur, sibling)
        } else {
            (sibling, old_cur)
        };
        let (new_left, new_right) = if direction == 0 {
            (new_cur, sibling)
        } else {
            (sibling, new_cur)
        };
        let node_states = |left: [BabyBear; 8], right: [BabyBear; 8]| {
            let mut preimage = [BabyBear::ZERO; 17];
            preimage[0] = BabyBear::new(EXACT_FIELDS_NODE_DOMAIN);
            preimage[1..9].copy_from_slice(&left);
            preimage[9..17].copy_from_slice(&right);
            refusal_exact_sponge_states(&preimage)
        };
        let old_node_states = node_states(old_left, old_right);
        let new_node_states = node_states(new_left, new_right);
        let old_parent = refusal_exact_sponge_digest(&old_node_states);
        let new_parent = refusal_exact_sponge_digest(&new_node_states);
        if old_node_states.len() != 6
            || new_node_states.len() != 6
            || old_parent != exact_fields_node8(old_left, old_right)
            || new_parent != exact_fields_node8(new_left, new_right)
        {
            return Err(format!(
                "exact refusal: FLN2 state16 schedule drifted at level {level}"
            ));
        }

        let row = &mut trace[level];
        row.resize(REFUSAL_WRITE_HOST_WIDTH, BabyBear::ZERO);
        row[REFUSAL_EXACT_OCC_COL] = BabyBear::new(update.old_leaf.occupancy() as u32);
        for limb in 0..16 {
            row[REFUSAL_EXACT_OLD_VALUE_BASE + limb] =
                BabyBear::new(u32::from(old_value_limbs[limb]));
            row[REFUSAL_EXACT_NEW_VALUE_BASE + limb] =
                BabyBear::new(u32::from(new_value_limbs[limb]));
        }
        refusal_write_states(row, REFUSAL_EXACT_OLD_LEAF_STATE_BASE, &old_leaf_states);
        refusal_write_states(row, REFUSAL_EXACT_NEW_LEAF_STATE_BASE, &new_leaf_states);
        refusal_write_states(row, REFUSAL_EXACT_OLD_NODE_STATE_BASE, &old_node_states);
        refusal_write_states(row, REFUSAL_EXACT_NEW_NODE_STATE_BASE, &new_node_states);
        row[REFUSAL_EXACT_DIR_COL] = BabyBear::new(u32::from(direction));
        row[REFUSAL_EXACT_ACTIVE_COL] = BabyBear::ONE;
        row[REFUSAL_EXACT_COUNT_COL] = BabyBear::new(level as u32);
        for lane in 0..HEAP_DIGEST_W {
            row[REFUSAL_EXACT_OLD_CUR_BASE + lane] = old_cur[lane];
            row[REFUSAL_EXACT_NEW_CUR_BASE + lane] = new_cur[lane];
            row[REFUSAL_EXACT_SIBLING_BASE + lane] = sibling[lane];
            row[REFUSAL_EXACT_OLD_LEFT_BASE + lane] = old_left[lane];
            row[REFUSAL_EXACT_OLD_RIGHT_BASE + lane] = old_right[lane];
            row[REFUSAL_EXACT_NEW_LEFT_BASE + lane] = new_left[lane];
            row[REFUSAL_EXACT_NEW_RIGHT_BASE + lane] = new_right[lane];
        }
        old_cur = old_parent;
        new_cur = new_parent;
    }
    if old_cur != update.old_root || new_cur != update.new_root {
        return Err("exact refusal: update paths do not recompose committed roots".into());
    }

    // State16 lookups are unconditional table receives.  Inactive main-trace rows therefore repeat
    // one genuine tuple, while the constrained `(active,count)` prefix selects exactly rows 0..15
    // for Merkle recomposition.  The `active=1,next.active=0` edge is the intrinsic root row.
    if trace.len() <= HEAP_TREE_DEPTH {
        return Err(format!(
            "exact refusal: trace height {} must exceed path depth {HEAP_TREE_DEPTH}",
            trace.len()
        ));
    }
    let inactive_template = trace[0][REFUSAL_EXACT_BEFORE_BASE..REFUSAL_WRITE_HOST_WIDTH].to_vec();
    for row in trace.iter_mut().skip(HEAP_TREE_DEPTH) {
        row.resize(REFUSAL_WRITE_HOST_WIDTH, BabyBear::ZERO);
        row[REFUSAL_EXACT_BEFORE_BASE..REFUSAL_WRITE_HOST_WIDTH]
            .copy_from_slice(&inactive_template);
        row[REFUSAL_EXACT_ACTIVE_COL] = BabyBear::ZERO;
        row[REFUSAL_EXACT_COUNT_COL] = BabyBear::new(HEAP_TREE_DEPTH as u32);
    }

    let fields_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + FIELDS_ROOT_GROUP[lane] };
    for row in trace.iter_mut() {
        for lane in 0..HEAP_DIGEST_W {
            row[fields_group_col(BEFORE_BASE, lane)] = update.old_root[lane];
            row[fields_group_col(AFTER_BASE, lane)] = update.new_root[lane];
        }
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }
    base_pis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT];
    base_pis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];

    let rc_at = base_pis.len() - DFA_RC_LEN;
    let audit_pis: Vec<BabyBear> = new_value_limbs
        .into_iter()
        .map(|limb| BabyBear::new(u32::from(limb)))
        .collect();
    base_pis.splice(rc_at..rc_at, audit_pis);
    debug_assert_eq!(
        base_pis.len(),
        ROT_PI_COUNT + 8 + REFUSAL_EXACT_AUDIT_PI_LEN + DFA_RC_LEN
    );

    // No scalar map heap participates in this descriptor.  The state16 appendix above is the
    // complete exact membership/update witness.
    Ok((trace, base_pis, Vec::new()))
}

/// The deployed exact refusal producer: exact FLD2/FLN2 opening first, then the common faithful
/// before/after wide carriers.  Final PI order is
/// `rotated46 || authority8 || audit16 || dfa4 || before_commit8 || after_commit8` (90 PIs).
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_refusal_write_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_fields_leaves: &[crate::openable_fields_root::ExactFieldsLeaf],
    audit_value: [u8; 32],
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
    let dpis = append_wide_carriers(&mut trace, base_pis, REFUSAL_WRITE_HOST_WIDTH);
    debug_assert_eq!(
        trace[0].len(),
        REFUSAL_WRITE_HOST_WIDTH + 2 * WIDE_NUM_CARRIERS * 8
    );
    // ⚑ DERIVED, and this one was a DEBUG-ONLY landmine: `debug_assert_eq!(dpis.len(), 90)` is
    // compiled out of `--release`, so the 2026-08-07 seven-slot compaction (which took this vector
    // to 83) left a producer that is green in every release run and PANICS in debug — the same
    // shape as `daf38eb87`. The exact-refusal wide ABI: the rotated base, the 8 faithful authority
    // record-pins, the 16 raw-audit limbs spliced above them, the dsl rc tail, and the 16 wide
    // commit anchors.
    debug_assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + 8 + REFUSAL_EXACT_AUDIT_PI_LEN + DFA_RC_LEN + 16
    );
    Ok((trace, dpis, map_heaps))
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
                .update_witness(HeapLeaf::entry(removed_key, BabyBear::ZERO))
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
                .insert_witness(HeapLeaf::entry(inserted_key, inserted_value))
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
                .update_witness(HeapLeaf::entry(updated_key, keep_mask))
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

/// Fill rotated block `blk` (`0` = BEFORE, `1` = AFTER) of the appendix based at `before_base`,
/// for ONE row. The WELDED limbs
/// (r0↔balance_lo, r1↔nonce, r2↔balance_hi, r3..r10↔fields, cap_root) are copied from THAT
/// row's own v1 state block at `state_base` (so the weld gates hold on EVERY row, including
/// the NoOp padding rows whose v1 state block differs from the active row); the WITNESS-
/// CARRIED limbs (cells_root, the map roots, lifecycle, epoch, committed_height, iroot,
/// r11..r23) come from the per-turn producer witness `w` (turn-invariant). Then the genuine
/// chained `wireCommitR` digests are computed on this row's own limbs.
///
/// ⚑ **AND THEN THIS BLOCK'S FIELDS-CANONICITY AUX IS RE-LAID** ([`fill_canon9_block`]) — the
/// pairing is INSIDE this function on purpose. This routine is the ONLY writer of a fields nonet
/// lane anywhere in the tree (lanes 1..8 arrive with the `pre_limbs` copy, lane 0 with the weld
/// two lines down), and every one of those lanes is an input to the canonicity gadget. A caller
/// that re-runs `fill_block` after mutating v1 state — the fee producer's post-fee surgery, the
/// settle carrier's leg-STATUS flip — moves lane 0 and would leave a STALE aux behind, i.e. an
/// HONEST turn going UNSAT with no hint as to why. Taking `(before_base, blk)` instead of an
/// absolute `base` is what lets the aux be located from inside here, so the pairing cannot be
/// forgotten at a call site rather than merely remembered at three of them.
///
/// The carrier-material octets (`B_CHILD_VK_OCTET` 89..=96 · `B_CONTRACT_HASH_OCTET` 97..=104 ·
/// `B_PUBKEY_OCTET` 105..=112) ride the `pre_limbs` COPY above — the trace is the third producer of
/// them, and it fills them byte-identically to the two flat-record twins
/// (`rotation_witness::produce` / `commitment::compute_rotated_pre_limbs`) BY COPY: the octets are
/// filled in `pre_limbs` at their source, so this generator carries them into the block and the
/// chained `state_commit` absorbs them (they are `< NUM_PRE_LIMBS`). The 3-way agreement is the
/// `effect_vm_rotation_flip` differential.
///
/// The chained-absorption logic is byte-identical to `descriptor_ir2::rotation_probe_trace_r`,
/// the producer's `wire_commit`, and the Lean `wireCommitR`.
fn fill_block(
    row: &mut [BabyBear],
    before_base: usize,
    blk: usize,
    state_base: usize,
    w: &RotatedBlockWitness,
) {
    debug_assert!(blk < 2, "a rotated appendix carries exactly two blocks");
    let base = before_base + blk * B_SPAN;
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
    // ⚑ THE FIELDS-CANONICITY AUX FOR THIS BLOCK — laid here, not at the call site (see above).
    fill_canon9_block(row, before_base, blk);
}

/// **Fill ONE rotated block's FIELDS-CANONICITY aux** — the seven witness columns per
/// `(block, slot)` that make `Canonical9`'s third leg (`NoWrap`) expressible in-AIR. Lean twin:
/// `Dregg2.Circuit.Emit.FieldsCanonicity9Emit.canon9ConstraintsAt` (this is its `blk` slice;
/// `auxColAt w blk slot k = w + CANON9_REGION_OFF + blk·56 + slot·7 + k`, and 56 is
/// `8 · CANON9_PER_SLOT`).
///
/// ⚑ **ONLY [`fill_block`] CALLS THIS, AND THAT IS THE POINT** — a block's aux is a function of
/// that block's nonet lanes and nothing else, and `fill_block` is the only writer of those lanes,
/// so laying the aux as `fill_block`'s last act makes the two impossible to separate. Do not add a
/// second call site; add the `fill_block` the trace was missing.
///
/// The gadget, per slot, reads lanes 0/1/8 of that slot's committed nonet and writes
/// `r, q0, q1, v0, v0b, v1, v1b`:
///
/// ```text
///   c  = L8 >> 24         r  = L8 & 0xFFFFFF        (the carry digit, split off lane 8)
///   q0 = c % 4            q1 = c / 4                (the two restored `mod p` quotients)
///   t  = 1 iff q == 2                               (the selector `q(q−1)/2`)
///   v  = t·L              vb = v + 2·t
/// ```
///
/// ⚑ **THIS IS NOT OPTIONAL PLUMBING.** These columns are read by seven gates and five lookups per
/// slot. Leave them zero and `L8 = (q0 + 4·q1)·2^24 + r` fails on every row where lane 8 is
/// nonzero, i.e. on every field value that reaches past `b[24..32]` — an honest turn, UNSAT.
///
/// ⚑ **AND IT RUNS BEFORE COMPACTION.** The wide members are S2/E1-compacted (dead columns deleted,
/// survivors renumbered) by `compact_s2_columns` / `compact_e1_columns` AFTER the row is laid, so
/// filling here — at the uncompacted geometry, the same place `fill_block` and `fill_caveat` work —
/// is the only place the `ROTATED_FIELD_LANE_COL` indices mean what they say.
///
/// A dishonest lane (lane 8 ≥ 2^28, or lane 0 ≥ 2^28 while its quotient is 2) makes some aux value
/// exceed its declared width; `descriptor_ir2::fill_main_layout_row` then refuses the row rather
/// than emitting an unprovable trace. That refusal IS the completeness pole's tooth.
fn fill_canon9_block(row: &mut [BabyBear], before_base: usize, blk: usize) {
    let canon_base = before_base + CANON9_REGION_OFF + blk * (8 * CANON9_PER_SLOT);
    let bb = before_base + blk * B_SPAN;
    for slot in 0..8usize {
        let l0 = row[bb + ROTATED_FIELD_LANE_COL[slot][0]].as_u32() as u64;
        let l1 = row[bb + ROTATED_FIELD_LANE_COL[slot][1]].as_u32() as u64;
        let l8 = row[bb + ROTATED_FIELD_LANE_COL[slot][8]].as_u32() as u64;
        let c = l8 >> 24;
        let r = l8 & 0x00ff_ffff;
        let q0 = c % 4;
        let q1 = c / 4;
        // `q(q−1)/2` — 1 exactly at q == 2, which is the only quotient that can wrap.
        let t0 = u64::from(q0 == 2);
        let t1 = u64::from(q1 == 2);
        let a = canon_base + slot * CANON9_PER_SLOT;
        row[a] = BabyBear::new(r as u32);
        row[a + 1] = BabyBear::new(q0 as u32);
        row[a + 2] = BabyBear::new(q1 as u32);
        row[a + 3] = BabyBear::new((t0 * l0) as u32);
        row[a + 4] = BabyBear::new((t0 * l0 + 2 * t0) as u32);
        row[a + 5] = BabyBear::new((t1 * l1) as u32);
        row[a + 6] = BabyBear::new((t1 * l1 + 2 * t1) as u32);
    }
}

/// Fill the widened-caveat region at `base` (29-felt manifest + 9 chain + manifest commit + the
/// 4-felt DFA route-commitment carrier + its 2 absorbing carriers + the PUBLISHED commit) from the
/// turn's manifest. The chained commitment is genuine (Lean
/// `EffectVmEmitRotationCaveat.caveatCommitRc`). A register (slot) operand can never alias a
/// heap operand (the `caveat_operand_no_aliasing` keystone — the domain tag separates them).
///
/// ⚑ **THE rc FOLD.** The published commitment is no longer the manifest fold: it EXTENDS it over
/// the route-commitment carrier, under the same `chunk31` arity-{2,4} chunking
/// (`[[rc0,rc1,rc2],[rc3]]` → one arity-4 site then one arity-2 site). That extension is what
/// makes columns `base + C_DFA_RC_OFF ..+4` READ by a constraint — before it they were read by
/// nothing, the `withDfaRcPins` pins on them bound nothing, and `dropUnforcedPins` deleted them.
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
    // The DFA route-commitment carrier (the dsl rc-EMIT): 4 felts past the MANIFEST fold's
    // carrier, uniformly on every row (the descriptor's rc pins read the last row; a uniform fill
    // keeps any-row reads coherent). ZERO when the turn carries no Dfa caveat (the Default
    // manifest). Written BEFORE the chain, because the chain now absorbs it.
    for k in 0..DFA_RC_LEN {
        row[base + C_DFA_RC_OFF + k] = m.dfa_rc[k];
    }
    // chained caveat commitment over the 29 manifest felts: 4-wide head, 3-wide body, tail.
    let manifest = cav::MANIFEST_SIZE; // 29
    let chain_base = base + manifest; // 9 carriers
    let manifest_commit_col = chain_base + cav::NUM_CHAIN; // base + 29 + 9 = base + C_MANIFEST_COMMIT
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
    row[manifest_commit_col] = d;
    debug_assert_eq!(manifest_commit_col, base + C_MANIFEST_COMMIT);
    // THE rc EXTENSION — the two further sites that make the carrier a BOUND datum. `chunk31` over
    // the 4 rc felts is `[[rc0, rc1, rc2], [rc3]]`: one (digest+3) absorption then one (digest+1),
    // arity 4 then 2, never the chip-refused 3. The final digest is the PUBLISHED caveat
    // commitment (PI `piBase + 3`), so moving the carrier moves the published felt.
    let rc = base + C_DFA_RC_OFF;
    row[base + C_RC_CARRIER] = hash_many(&[d, row[rc], row[rc + 1], row[rc + 2]]);
    row[base + C_COMMIT] = hash_many(&[row[base + C_RC_CARRIER], row[rc + 3]]);
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
        // The SINGLE-TICK GRAIN TURN (initiative 10): one executor grain turn as one row on its own
        // repurposed selector (6). A TAIL registry member (the supplyMint precedent), Lean
        // `EffectVmEmitGrainTurnRotated.grainTurnHost` / `grainTurnWide`.
        s if s == sel::GRAIN_TURN => GRAIN_TURN_DESCRIPTOR_NAME,
        // The residue is EMPTY: every LIVE selector resolves above. NoOp and unknown selectors
        // fail closed.
        _ => return None,
    })
}

/// The registry key of the single-tick grain-turn member (`grainTurnVmDescriptor2R24`).
pub const GRAIN_TURN_DESCRIPTOR_NAME: &str = "grainTurnVmDescriptor2R24";

/// The grain-turn member's extra PI block past `ROT_PI_COUNT`: the published fee (1) + the five
/// written slots' completion lanes (5 × `ROTATED_FIELD_COMPLETION_LANES`). Lean
/// `grainTurnVmDescriptor2R24.piCount = GRAIN_FEE_PI + 1 + 40`.
pub const GRAIN_TURN_EXTRA_PIS: usize =
    1 + 5 * crate::effect_vm::layout_generated::ROTATED_FIELD_COMPLETION_LANES;

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
/// rotated `ROT_PI_COUNT`-PI vector + the appended selector slot pinned at PI `ESCROW_SEL_PI`). The
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
/// This is the declaration-keyed sibling of the deployed-default [`rotated_descriptor_name_for_effect`]
/// (which routes by effect kind alone): a live prover holding the turn's caveat manifest calls this to
/// name the satisfaction descriptor a declared-escrow cell MUST take — the LIVENESS complement of the
/// flag-day bare-descriptor refuse (the refuse makes the declared turn UNSAT under the bare member,
/// this names the member it takes instead). A non-escrow declaration delegates to
/// [`rotated_descriptor_name_for_effect`] (deployed-identical). See
/// [`rotated_descriptor_name_for_declared_capacity`] for the unified escrow/discharge/vault route.
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

/// The registry name of the welded discharge-obligation satisfaction descriptor
/// (Lean `Dregg2.Deos.DischargeSatDescriptor.dischargeSatVmDescriptor2R24`, piCount 47). A member of
/// `rotation-v3-staged-registry.tsv` carrying the cursor/total/due satisfaction gates + the G5
/// free-param binds over the rotated field columns. Reached by the declaration-keyed route below (a
/// discharge is performed AS a transfer; effect-dispatch is untouched).
pub const DISCHARGE_SAT_DESCRIPTOR_NAME: &str = "dischargeSatVmDescriptor2R24";

/// The registry name of the welded vault-deposit satisfaction descriptor
/// (Lean `Dregg2.Deos.VaultSatDescriptor.vaultSatVmDescriptor2R24`, piCount 47). A member of
/// `rotation-v3-staged-registry.tsv` carrying the no-dilution (`Ta·m ≤ Sa·d`) satisfaction gates over
/// the rotated field columns. Reached by the declaration-keyed route below.
pub const VAULT_SAT_DESCRIPTOR_NAME: &str = "vaultSatVmDescriptor2R24";

/// The DECLARATION-keyed discharge routing arm (the discharge analog of
/// [`rotated_descriptor_name_for_declared_escrow`]). A discharge executes AS a transfer, so it would
/// otherwise route to the (now refuse-welded) bare `transferVmDescriptor2R24` — where the flag-day
/// refuse makes a declared-discharge cell UNSAT. This arm routes it to the WELDED
/// [`DISCHARGE_SAT_DESCRIPTOR_NAME`] instead, so the satisfaction gates ride the proof. Keys on the
/// EXISTING caveat declaration (`SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION`), NOT a new kernel effect. A
/// non-discharge declaration delegates to [`rotated_descriptor_name_for_effect`] (deployed-identical).
pub fn rotated_descriptor_name_for_declared_discharge(
    effect: &Effect,
    required_caveat_tags: &[u32],
) -> Option<&'static str> {
    if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION) {
        Some(DISCHARGE_SAT_DESCRIPTOR_NAME)
    } else {
        rotated_descriptor_name_for_effect(effect)
    }
}

/// The DECLARATION-keyed vault routing arm (the vault analog of
/// [`rotated_descriptor_name_for_declared_escrow`]). A vault deposit executes AS a transfer; this arm
/// routes a declared-vault cell to the WELDED [`VAULT_SAT_DESCRIPTOR_NAME`] (carrying the no-dilution
/// satisfaction gates), off the refuse-welded bare descriptor. Keys on
/// `SLOT_CAVEAT_TAG_VAULT_DEPOSIT`; a non-vault declaration delegates to
/// [`rotated_descriptor_name_for_effect`].
pub fn rotated_descriptor_name_for_declared_vault(
    effect: &Effect,
    required_caveat_tags: &[u32],
) -> Option<&'static str> {
    if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT) {
        Some(VAULT_SAT_DESCRIPTOR_NAME)
    } else {
        rotated_descriptor_name_for_effect(effect)
    }
}

/// The UNIFIED declaration-keyed capacity route: resolve the welded satisfaction descriptor for an
/// effect whose acting cell carries ANY of the three deployed capacity tags (escrow 17 / discharge 18 /
/// vault 19), else the deployed-default [`rotated_descriptor_name_for_effect`]. This is the single
/// entry point a live prover with the caveat manifest in hand calls to route an honest declared-capacity
/// turn onto its satisfaction descriptor (the liveness complement of the bare-descriptor refuse: the
/// refuse makes the declared turn UNSAT under the bare member, this names the member it MUST take). At
/// most one capacity tag is present per cohort turn (the manifest declares one capacity); escrow is
/// checked first, then discharge, then vault.
pub fn rotated_descriptor_name_for_declared_capacity(
    effect: &Effect,
    required_caveat_tags: &[u32],
) -> Option<&'static str> {
    if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW) {
        Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME)
    } else if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION) {
        Some(DISCHARGE_SAT_DESCRIPTOR_NAME)
    } else if required_caveat_tags.contains(&super::pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT) {
        Some(VAULT_SAT_DESCRIPTOR_NAME)
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
/// width `GRAD_ROT_WIDTH` (the committed `attenuateVmDescriptor2R24.trace_width`), NOT at the
/// un-graduated `ROT_WIDTH = 328`. The cap-open builds ON the graduated rotated layout.
pub const CAP_OPEN_BASE: usize = GRAD_ROT_WIDTH; // 1647
/// The width of the FULL `EffectMask` bit decomposition (residual (a) — GENUINE MEMBERSHIP). The
/// decoded facet is the full `u32` mask `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536`
/// (`EFFECT_ALL = 0xFFFF_FFFF`), so the decomposition spans all 32 bits: any deployed effect-kind bit
/// `1 << n` (`n < 32`, up to `EFFECT_ATTENUATE_CAPABILITY = 1 << 23`) is selectable AND a broad cap
/// (`mask_hi = 0xFFFF`) decomposes fully. The Lean twin is `DeployedCapOpen.MASK16_BITS`.
pub const CAP_OPEN_MASK_BITS: usize = 32;
/// The number of felts in a native cap-tree digest (Phase H-CAP-8): a leaf-digest / sibling / node /
/// cap-root group is 8-felt wide, byte-identical to `cap_root::CAP_DIGEST_W` (the arity-16 `node8`
/// chip compression `cap_node8` + the 8-lane `CapLeaf::digest`), faithful to the FRI ~124-bit floor.
pub const CAP_OPEN_DIGEST_W: usize = crate::cap_root::CAP_DIGEST_W; // 8
/// The cap-MEMBERSHIP columns `fill_cap_open` writes — Phase H-CAP-8 NATIVE 8-FELT: 7 leaf (scalar) +
/// 8 leafDigest + `DEPTH·(8 sib + 1 dir + 8 node) = DEPTH·17` + 8 capRoot + src + effBit + 32 mask-bit
/// columns = `7 + 8 + 16·17 + 8 + 2 + 32 = 329`. The 7 spare permutation lanes per absorb are PROMOTED
/// into the bound 8-felt fold (the whole `node8` group is committed), so there is NO separate
/// chip-lane tail — the membership span IS the full appendix. The trailing 32 mask-bit columns carry
/// the PER-16-BIT-LIMB decomposition of the FULL effect mask the genuine SUBMASK facet gate reads
/// (`maskBitBoolGate` + the two per-limb recon gates `maskReconLoGate`/`maskReconHiGate` (MASK-RECON-WRAP
/// FIX) + `selectedBitGate`). Mirrors the Lean
/// `CapOpenEmit.CAP_OPEN_SPAN = 7 + 8 + DEPTH·17 + 8 + 2 + MASK_BITS = 329`.
pub const CAP_OPEN_MEMBERSHIP_COLS: usize = 7
    + CAP_OPEN_DIGEST_W
    + CAP_OPEN_DEPTH * (2 * CAP_OPEN_DIGEST_W + 1)
    + CAP_OPEN_DIGEST_W
    + 2
    + CAP_OPEN_MASK_BITS; // 329
/// The number of poseidon2-chip lookup SITES the cap-membership appendix carries: 1 leaf absorb
/// (arity 7, 8-lane) + 16 node absorbs (arity-16 `node8`) = 17. Phase H-CAP-8 promotes the lane
/// outputs INTO the committed 8-felt digest groups, so a site no longer adds a separate lane block.
pub const CAP_OPEN_LANE_SITES: usize = 1 + CAP_OPEN_DEPTH; // 17
/// The FULL cap-open appendix span (Phase H-CAP-8): the native 8-felt membership columns ARE the whole
/// appendix — `CAP_OPEN_SPAN = CAP_OPEN_MEMBERSHIP_COLS = 329`. No separate chip-lane tail (the `node8`
/// groups are committed in place). Written by `fill_cap_open` at `CAP_OPEN_BASE + 0..329`. Mirrors the
/// Lean `CapOpenEmit.CAP_OPEN_SPAN = 329`.
pub const CAP_OPEN_SPAN: usize = CAP_OPEN_MEMBERSHIP_COLS; // 329
/// The AFTER-SPINE recompute appendix span the cap-WRITE descriptors (`effCapOpenWriteV3`: attenuate +
/// the delegation-mutating writes) carry PAST the 329-col read appendix — `15 + 8·DEPTH = 143`
/// (after-leaf + after-leaf-digest + `DEPTH·8` after-node), forcing the faithful 8-felt cap-WRITE
/// (Lean `CapOpenEmit.AFTER_SPINE_SPAN`, the `*_forces_write8` weld). A WRITE cap-open descriptor's
/// `trace_width` is `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`; a READ-only one is `CAP_OPEN_WIDTH`.
pub const CAP_OPEN_AFTER_SPINE_SPAN: usize = 15 + 8 * CAP_OPEN_DEPTH; // 143
/// The cap-open trace width (`GRAD_ROT_WIDTH + 329 = 1976` = the committed
/// `attenuateCapOpenEffVmDescriptor2R24.trace_width` under the native 8-felt cap tree).
pub const CAP_OPEN_WIDTH: usize = CAP_OPEN_BASE + CAP_OPEN_SPAN;

/// The turn-bound cap-open trace width. **It EQUALS [`CAP_OPEN_WIDTH`]**: `effCapOpenV3TB` adds
/// `piCount + 1` and NO column — the pin it appends names the EXISTING `capOpenCols.src` column.
///
/// ⚑ FLAG DAY 2026-07-31. This was `CAP_OPEN_WIDTH + 2` for the two turn-identity columns
/// (`actor`/`dst`) the TB weld used to add. `CapOpenTurnPins` deleted them at the source on
/// 2026-07-30 and the re-emit shipped it: the committed `transferCapOpenTBVmDescriptor2R24` and
/// `transferCapOpenEffVmDescriptor2R24` now carry the SAME `trace_width`, and the TB member's
/// `public_input_count` is `ROT_PI_COUNT + 1`, not `+ 3`. The two columns were introduced by that weld and read by
/// no other constraint, so their `.piBinding`s were `local[c] == pi[k]` with the prover choosing
/// both sides — no producer, verifier or light client loses a check by their removal, and the
/// successor that publishes `actor`/`dst` FORCED (through the Lamport turn-digest lookup) is
/// `Dregg2/Circuit/Emit/TurnAuthCapOpenWeld.lean`.
pub const CAP_OPEN_TB_WIDTH: usize = CAP_OPEN_WIDTH;
/// The cap-open base descriptor's PI count (`effCapOpenV3.piCount == ROT_PI_COUNT`; the cap-open
/// appendix adds no PIs). The TB weld appends exactly ONE turn-identity PI, at that slot.
///
/// ⚑ THE WELD FOLLOWS `ROT_PI_COUNT` BY CONSTRUCTION, not by transcription — checked at the source
/// on 2026-08-07 rather than re-typed. `CapOpenTurnPins.withTurnIdentityPins` is
/// `{ d with piCount := d.piCount + 1, constraints := d.constraints ++ turnIdentityPins _ d.piCount }`:
/// the index is `d.piCount`, symbolic, and its own docblock says "the turn-identity pin rides the
/// first slot past those four: `base.piCount`". So the `46` this pair used to carry was a snapshot
/// of `ROT_PI_COUNT`, not an independent claim, and the seven-slot PI compaction moves it to 39.
pub const CAP_OPEN_TB_PI_BASE: usize = ROT_PI_COUNT;
/// The one published turn-identity PI slot of the TB cap-open (`effCapOpenV3.piCount + 0`):
/// `src → PI[CAP_OPEN_TB_PI_BASE]` (`CapOpenTurnPins.turnIdentityPins`, a singleton).
pub const CAP_OPEN_TB_PI_SRC: usize = CAP_OPEN_TB_PI_BASE;
/// The TB cap-open's public-input count: the rotated prefix plus the one turn-identity slot.
pub const CAP_OPEN_TB_PI_COUNT: usize = CAP_OPEN_TB_PI_BASE + 1;

// CAP-OPEN GEOMETRY PINS — the twin of the wide-carrier FLAG-DAY block below, and it exists
// because this family's numbers ROTTED IN PLACE ONCE ALREADY. Docs on the widener, the wide
// lift and the TB turn-pin filler carried `818 / 1026 / 210 / 91 / +608` and the TB PI slots
// `38/39/40` long after Phase H-CAP-8 moved the span to 329 (host 1976) and the TB pins to
// 46/47/48 — a doc comment that is wrong about a width is how the next reader derives a wrong
// descriptor, and a prose number cannot go red. (That `46/47/48` is HISTORY, not the current
// shape: the 2026-07-31 subtraction left ONE TB pin, at 46. See `CAP_OPEN_TB_WIDTH`.)
// These CAN. Any drift in `GRAD_ROT_WIDTH`,
// `CAP_OPEN_DEPTH`, `CAP_OPEN_MASK_BITS` or the digest width now breaks the BUILD here, at the
// definitions, rather than rotting a paragraph a reader will believe.
//
// ⚑ AND THEY MUST BE LITERALS. On 2026-07-31 five of these were "re-expressed as the relation they
// were checking" — `CAP_OPEN_BASE == GRAD_ROT_WIDTH` beside `pub const CAP_OPEN_BASE: usize =
// GRAD_ROT_WIDTH`, `CAP_OPEN_WIDTH == CAP_OPEN_BASE + CAP_OPEN_SPAN` beside its identical
// definition three lines up. Every one became `x == x`: TRUE AT EVERY GEOMETRY, including a wrong
// one. That is not a softer tripwire, it is no tripwire — this block's whole job is to be the
// place a `GRAD_ROT_WIDTH` drift goes red, and a tautology cannot go red. Re-typing a literal per
// epoch IS the cost of a tripwire; a relation that restates the definition beside it buys nothing
// and reads as though it still guards something.
//
// (The genuinely relational pins — the ones whose two sides come from DIFFERENT sources — stay
// relations; see the `NUM_PRE_LIMBS`-derived wide block below.)
const _: () = {
    assert!(
        CAP_OPEN_BASE == 1841,
        "cap-open rides the graduated rotated base (1647 -> 1691 nine-lane -> 1707 dsl-rc carrier -> 1819 fields-canonicity -> 1841 KEY NONET at 187 limbs: APPENDIX +8, sites +2)"
    );
    assert!(
        CAP_OPEN_SPAN == 329,
        "Phase H-CAP-8 native 8-felt membership span"
    );
    assert!(
        CAP_OPEN_WIDTH == 2170,
        "cap-open READ host width = 1841 + 329 (was 1819 + 329 at 184 limbs)"
    );
    assert!(
        CAP_OPEN_AFTER_SPINE_SPAN == 143,
        "cap-WRITE after-spine appendix = 15 + 8·16"
    );
    // The committed narrow `attenuateCapOpenEffVmDescriptor2R24.trace_width`
    // (`circuit/descriptors/rotation-v3-staged-registry.tsv`). ⚑ RESTORED: the nine-lane re-emit
    // moved this 2119 -> 2163 and the pin was DELETED rather than re-typed, leaving the comment
    // above dangling over an assertion about something else. It is the only line in this block that
    // ties the Rust constants to a committed descriptor byte, so losing it lost the whole point.
    assert!(
        CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN == 2313,
        "cap-WRITE narrow width"
    );
    // The TB PI geometry. `CAP_OPEN_TB_WIDTH` gets NO pin here on purpose: it is now *defined* as
    // `CAP_OPEN_WIDTH`, so `CAP_OPEN_TB_WIDTH == 2020` beside `CAP_OPEN_WIDTH == 2020` four lines
    // up is one fact typed twice — the two can only ever go red together. The claim worth guarding
    // ("the TB member and the non-TB member carry the SAME committed `trace_width`, and the TB
    // member's `public_input_count` is `ROT_PI_COUNT + 1`") relates two COMMITTED ARTIFACTS, which a const-assert
    // cannot reach; it is pinned in `circuit/tests/cap_open_avail_roundtrip.rs` against the
    // registry bytes. What IS local and non-redundant is the PI slot arithmetic:
    assert!(
        CAP_OPEN_TB_PI_SRC == 39 && CAP_OPEN_TB_PI_COUNT == 40,
        "the TB weld appends exactly ONE turn-identity PI, at the first slot past ROT_PI_COUNT \
         (39 since the 2026-08-07 seven-slot PI compaction, 46 before it — the Lean weld indexes \
         `d.piCount` symbolically, so this literal transcribes ROT_PI_COUNT and is re-typed with it)"
    );
};

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
    /// The 16 NATIVE 8-FELT sibling digests of the membership path (Phase H-CAP-8: each level's
    /// sibling subtree root is the full 8-felt `cap_node8` image, not the lossy 1-felt scalar).
    pub siblings: [[BabyBear; CAP_OPEN_DIGEST_W]; CAP_OPEN_DEPTH],
    /// The 16 direction bits (0 ⇒ cur is the LEFT child at that level).
    pub directions: [u8; CAP_OPEN_DEPTH],
    /// The recomposed committed 8-felt cap-tree root (must equal the top `node8` group, lane-for-lane).
    pub cap_root: [BabyBear; CAP_OPEN_DIGEST_W],
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
pub fn cap_leaf_digest(leaf: &[BabyBear; 7]) -> [BabyBear; CAP_OPEN_DIGEST_W] {
    // The SINGLE rate-8 chip absorb of the 7 leaf fields (arity 7), squeezing ALL 8 output lanes —
    // byte-identical to `cap_root::CapLeaf::digest` and the Lean `capLeafDigest8 = chipAbsorb8 ∘
    // leafFields`. Native 8-felt, faithful to the FRI ~124-bit floor.
    crate::descriptor_ir2::chip_absorb_all_lanes(7, leaf)
}

/// One node hash: the NATIVE 8-FELT arity-16 `node8` chip compression `perm(L8 ‖ R8)[0..8]` (Lean
/// `nodeOf8 = chipAbsorb8 (pack8 l r)`), byte-identical to `cap_root::cap_node8`. EQUALITY-binds all 8
/// output lanes to both 8-felt children, so the per-node collision floor is full 8-felt width.
pub fn cap_node(
    left: [BabyBear; CAP_OPEN_DIGEST_W],
    right: [BabyBear; CAP_OPEN_DIGEST_W],
) -> [BabyBear; CAP_OPEN_DIGEST_W] {
    crate::cap_root::cap_node8(left, right)
}

/// Mix `(cur, sib)` 8-felt groups by the direction bit into `(left, right)` (Lean
/// `leftExpr`/`rightExpr`): `dir = 0 ⇒ (cur, sib)` (cur is LEFT), `dir = 1 ⇒ (sib, cur)`.
fn cap_mix(
    cur: [BabyBear; CAP_OPEN_DIGEST_W],
    sib: [BabyBear; CAP_OPEN_DIGEST_W],
    dir: u8,
) -> ([BabyBear; CAP_OPEN_DIGEST_W], [BabyBear; CAP_OPEN_DIGEST_W]) {
    if dir == 0 { (cur, sib) } else { (sib, cur) }
}

impl CapOpenWitness {
    /// Recompute the 8-felt root from the leaf digest over the `(sib, dir)` path using the native
    /// arity-16 `node8` compression. The self-check the fold's soundness rests on.
    pub fn recomposes(&self) -> [BabyBear; CAP_OPEN_DIGEST_W] {
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
        // per-level 8-felt padding subtree roots: pad[0] = zero leaf digest; pad[k+1] = node8(pad,pad).
        let mut pad = [[BabyBear::ZERO; CAP_OPEN_DIGEST_W]; CAP_OPEN_DEPTH + 1];
        pad[0] = zero_leaf;
        for k in 0..CAP_OPEN_DEPTH {
            pad[k + 1] = cap_node(pad[k], pad[k]);
        }
        let mut siblings = [[BabyBear::ZERO; CAP_OPEN_DIGEST_W]; CAP_OPEN_DEPTH];
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
            // ⚑ WAS `WRITE_MASK_LO`, DROPPING THE PARAMETER (fixed 2026-07-27). `build_for` validated
            // `eff_bit` against the leaf mask and then stored the transfer constant, so every witness
            // built for a fan-out bit (delegate/spawn/revoke/refresh = 1<<16, introduce = 1<<13,
            // grantCap = 1<<2, revokeCapability = 1<<3) came back claiming EFFECT_TRANSFER.
            // `fill_cap_open` writes this field to the `effBit` column, whose `effBitGateFor` pins the
            // member's own bit — so the honest trace was UNSAT on every fan-out member. Every
            // in-tree call site (8, all in `sdk/src/full_turn_proof.rs`) reads only `siblings` /
            // `directions` off the result, and `build` is `build_for(_, _, WRITE_MASK_LO)`, so storing
            // the parameter is behaviour-identical everywhere it was already correct.
            eff_bit,
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
        siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
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
        siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
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
        let mut sib_arr = [[BabyBear::ZERO; CAP_OPEN_DIGEST_W]; CAP_OPEN_DEPTH];
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

/// Fill the 329 cap-MEMBERSHIP columns at `base` for ONE row from `w` — Phase H-CAP-8 NATIVE 8-FELT
/// `CapOpenCols` layout (Lean `CapOpenEmit.capOpenCols`):
///   * leaf field `i` (scalar) at `base + i` (i = 0..6);
///   * `leafDigest` (8 felts, `CapLeaf::digest`) at `base + 7 + j` (j = 0..7);
///   * level `lvl` 17-col block at `base + 15 + 17·lvl`: `sib` (8) at `+0..7`, `dir` at `+8`,
///     `node = cap_node8(left, right)` (8) at `+9..16`;
///   * `capRoot` (8) at `base + 15 + 17·DEPTH + j` (= `base + 287 + j`, j = 0..7);
///   * `src` at `base + 295`, `effBit` at `base + 296`;
///   * the 32 mask-bit columns at `base + 297 + i` (i = 0..31).
///
/// The `effBit` column (residual (a)) carries the turn's ACTUAL effect-kind bit, pinned by the
/// descriptor's `effBitGateFor` to `EFFECT_TRANSFER (= WRITE_MASK_LO)` for the transfer cap-open;
/// the `facetEffGate` then binds the leaf facet to the committed effect column, NOT a literal
/// constant. The top `node8` GROUP (`lvl = 15`) MUST equal `w.cap_root` lane-for-lane (asserted).
/// Every digest is a genuine `chip_absorb_all_lanes` absorb (arity-7 leaf, arity-16 `node8`), so the
/// auto-gathered chip table carries a matching row for each of the 1 + 16 chip lookups.
pub fn fill_cap_open(row: &mut [BabyBear], base: usize, w: &CapOpenWitness) {
    // 7 scalar leaf fields at base + 0..6.
    for (i, &f) in w.leaf.iter().enumerate() {
        row[base + i] = f;
    }
    // 8-felt leaf digest at base + 7..14.
    let leaf_digest = cap_leaf_digest(&w.leaf);
    for (j, &d) in leaf_digest.iter().enumerate() {
        row[base + 7 + j] = d;
    }
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let sib = w.siblings[lvl];
        let dir = w.directions[lvl];
        let (l, r) = cap_mix(cur, sib, dir);
        let node = cap_node(l, r);
        let blk = base + 15 + 17 * lvl;
        // 8-felt sibling group at blk + 0..7.
        for (j, &s) in sib.iter().enumerate() {
            row[blk + j] = s;
        }
        // direction bit at blk + 8.
        row[blk + 8] = BabyBear::new(dir as u32);
        // 8-felt node group at blk + 9..16.
        for (j, &n) in node.iter().enumerate() {
            row[blk + 9 + j] = n;
        }
        cur = node;
    }
    debug_assert_eq!(
        cur, w.cap_root,
        "cap-open fill: top node8 group must equal cap_root"
    );
    // 8-felt cap_root group at base + 287..294.
    let root_base = base + 15 + 17 * CAP_OPEN_DEPTH;
    for (j, &r) in w.cap_root.iter().enumerate() {
        row[root_base + j] = r;
    }
    row[root_base + 8] = w.src; // base + 295
    // residual (a): the committed effect-bit column at base + 296. Carries the turn's ACTUAL
    // effect-kind bit (`w.eff_bit` — EFFECT_TRANSFER for transfer/attenuate, each fan-out leg its own
    // `1<<n`); the `effBitGateFor` pins it.
    row[root_base + 9] = BabyBear::new(w.eff_bit);
    // residual (a) — GENUINE MEMBERSHIP: the PER-16-BIT-LIMB decomposition of the FULL effect mask
    // `maskOfLimbs(mask_lo, mask_hi) = mask_lo + mask_hi·65536` (leaf fields 3 + 4) at `base + 297 + i`.
    // MASK-RECON-WRAP FIX (verdict A, deployed soundness gap #2): the `maskBitBoolGate` booleans each
    // bit; the two per-limb recon gates `maskReconLoGate` (`mask_lo == Σ_{i<16} bitᵢ·2ⁱ`, bits 0..15) and
    // `maskReconHiGate` (`mask_hi == Σ_{i<16} bit_{16+i}·2ⁱ`, bits 16..31) bind EACH limb from its OWN 16
    // bits — each sum `< 2^16 < p`, so the mod-`p` gate + cell canonicality (mask_lo/mask_hi `< p`) pins
    // the limb EXACTLY (a genuine `< 2^16` range check), with NO `p`-shifted decomposition possible (the
    // old single 32-bit `maskReconGate` admitted `M+2p` bits because `2p < 2^32`). `selectedBitGate n`
    // then gates bit `n` (`eff_bit = 1<<n`) set — the genuine `(eff_bit & full_mask) == eff_bit` SUBMASK.
    // A BROAD honest cap (`EFFECT_ALL`, mask_lo = mask_hi = 0xFFFF) still decomposes (each limb 0xFFFF <
    // 2^16). The FILL is unchanged: `full_mask >> i & 1` for i<16 IS mask_lo's bit i, for 16≤i<32 IS
    // mask_hi's bit (i-16), since honest limbs are each < 2^16 — so the honest witness satisfies both
    // per-limb gates. Twin: Lean `DeployedCapOpen.maskReconLoGate`/`maskReconHiGate`, `CapOpenEmit`.
    let full_mask: u64 = w.leaf[3].as_u32() as u64 + (w.leaf[4].as_u32() as u64) * 65536;
    for i in 0..CAP_OPEN_MASK_BITS {
        row[root_base + 10 + i] = BabyBear::new(((full_mask >> i) & 1) as u32);
    }
}

/// **`fill_heap_open_read`** — lay the heap-open READ membership appendix at `base` (the Lean
/// `effHeapOpenV3`'s `capOpenCols base` layout, SHARED byte-for-byte with cap's [`fill_cap_open`] but
/// with the arity-3 IMT heap leaf `(addr, value, next_addr)` + `heap_node8`/`digest8` instead of the
/// 7-field `CapLeaf`). The 7-field leaf slot carries `(addr, value, next_addr, 0, 0, 0, 0)` — the leaf
/// carries NO authority, so the `src`/`effBit`/mask-bit columns (`base + 295..`) are UNUSED
/// (`heapOpenConstraints` reads only leaf(3)/leafDigest/sib/dir/node/rootPin). Leaf col 2 IS the gap-#5
/// IMT `next_addr` pointer the arity-3 `digest8` absorbs (`heapLeafInputs = [leaf0, leaf1, leaf2]`), so
/// the emitted arity-3 chip lookup's request matches the `digest8()` provide. The `capRoot` group
/// (`base + 287..294`) is the committed BEFORE heap `root8` (the top `node8` fold reaches it, and the
/// after-spine's `beforeRootWeldsH` pins it to the rotated BEFORE heap limb).
fn fill_heap_open_read(
    row: &mut [BabyBear],
    base: usize,
    leaf: crate::heap_root::HeapLeaf,
    siblings: &[[BabyBear; crate::heap_root::HEAP_DIGEST_W]],
    directions: &[u8],
    heap_root8: [BabyBear; crate::heap_root::HEAP_DIGEST_W],
) {
    use crate::heap_root::heap_node8;
    // arity-3 IMT heap leaf: addr @ base+0, value @ base+1, next_addr @ base+2; leaf cols 3..6 unused
    // (zero). Leaf col 2 = the linked-list pointer the arity-3 `digest8` absorbs — the emitted arity-3
    // chip lookup reads exactly [leaf0, leaf1, leaf2], so the request matches the digest8 provide.
    row[base] = leaf.addr;
    row[base + 1] = leaf.value;
    row[base + 2] = leaf.next_addr;
    // 8-felt leaf digest at base + 7..14.
    let leaf_digest = leaf.digest8();
    for (j, &d) in leaf_digest.iter().enumerate() {
        row[base + 7 + j] = d;
    }
    // per-level `(sib8, dir, node8)` blocks (stride 17), SHARED layout with `fill_cap_open`.
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let sib = siblings[lvl];
        let dir = directions[lvl];
        let (l, r) = if dir == 0 { (cur, sib) } else { (sib, cur) };
        let node = heap_node8(l, r);
        let blk = base + 15 + 17 * lvl;
        for (j, &s) in sib.iter().enumerate() {
            row[blk + j] = s;
        }
        row[blk + 8] = BabyBear::new(dir as u32);
        for (j, &n) in node.iter().enumerate() {
            row[blk + 9 + j] = n;
        }
        cur = node;
    }
    debug_assert_eq!(
        cur, heap_root8,
        "heap-open read fill: top node8 fold must equal the BEFORE heap root8"
    );
    // 8-felt capRoot group at base + 287..294 (the committed BEFORE heap root8).
    let root_base = base + 15 + 17 * CAP_OPEN_DEPTH;
    for (j, &r) in heap_root8.iter().enumerate() {
        row[root_base + j] = r;
    }
    // src/effBit/mask columns (root_base + 8..) UNUSED by the heap read appendix — left zero.
}

/// **`fill_heap_after_spine`** — lay the heap AFTER-spine appendix at `base_as`
/// (= `AFTER_SPINE_BASE base_ro = base_ro + CAP_OPEN_SPAN`, the Lean `afterSpineColsH`): the
/// IN-PLACE-UPDATED leaf `(addr, new_value)` folded over the SHARED sibling path (`siblings`/
/// `directions` — the read's sib/dir columns, which `afterSpineColsH` reuses defeq) to the committed
/// AFTER heap `root8`. The after-spine carries ONLY after-leaf(2) + after-leafDigest(8) +
/// after-node(`DEPTH·8`) = 143 cols; its `capRoot` is the rotated AFTER heap limb (already laid on the
/// row), NOT in the appendix. The after-node fold's top reaches `after_root8`, so the after rootPins
/// hold against that rotated limb.
fn fill_heap_after_spine(
    row: &mut [BabyBear],
    base_as: usize,
    addr: BabyBear,
    new_value: BabyBear,
    next_addr: BabyBear,
    siblings: &[[BabyBear; crate::heap_root::HEAP_DIGEST_W]],
    directions: &[u8],
) {
    use crate::heap_root::{HEAP_DIGEST_W, HeapLeaf, heap_node8};
    row[base_as] = addr;
    row[base_as + 1] = new_value;
    // Leaf col 2 = the IMT `next_addr` pointer the arity-3 `digest8` absorbs (the `afterLeafWeldsH`
    // pointer weld pins after-leaf 2 == read-leaf 2 — a value update HOLDS the pointer fixed).
    row[base_as + 2] = next_addr;
    // The UPDATED leaf's arity-3 IMT digest `hash[addr, new_value, next_addr]` — a value update
    // holds the pointer fixed, so `next_addr` is the committed leaf's pointer.
    let leaf_digest = HeapLeaf {
        addr,
        value: new_value,
        next_addr,
    }
    .digest8();
    for (j, &d) in leaf_digest.iter().enumerate() {
        row[base_as + 7 + j] = d;
    }
    // after-node blocks (8 felts each, NO sib/dir — those are SHARED with the read) at
    // `base_as + 15 + 8·lvl`.
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let sib = siblings[lvl];
        let dir = directions[lvl];
        let (l, r) = if dir == 0 { (cur, sib) } else { (sib, cur) };
        let node = heap_node8(l, r);
        let blk = base_as + 15 + HEAP_DIGEST_W * lvl;
        for (j, &n) in node.iter().enumerate() {
            row[blk + j] = n;
        }
        cur = node;
    }
}

/// **`fill_cap_after_spine`** — the ARITY-7 cap-tree AFTER-spine appendix, the exact twin of
/// [`fill_heap_after_spine`] but over the native-8-felt cap tree (`cap_leaf_digest` = arity-7 leaf
/// absorb, `cap_node` = arity-16 `node8`). Lays, at `base_as` (= `AFTER_SPINE_BASE w = CAP_OPEN_WIDTH`,
/// the Lean `afterSpineCols`): the in-place-narrowed AFTER `CapLeaf` (7 scalar fields) at `+0..6`, its
/// 8-felt `cap_leaf_digest` at `+7..14`, then `DEPTH` 8-felt `cap_node` groups at `+15+8·lvl` folded
/// over the SHARED sibling path (`siblings`/`directions` — reused from the cap-open READ appendix, the
/// Lean `afterSpineCols.dir = capOpenCols.dir` defeq). NO sib/dir cols (shared with the read) and NO
/// `capRoot` col in the appendix (the after `capRoot` is the committed AFTER-block cap-root GROUP the
/// rootPin binds to). Returns the recomposed AFTER `cap_root8` (the top `node8`), which the caller MUST
/// lay into the AFTER-block cap-root group so `afterSpineCols.rootPin` holds against it. This is the
/// producer half of `CapOpenEmit.effCapOpenWriteV3_forces_write8` (the arity-7 `writesTo8`, UPDATE-at-key:
/// same `slot_hash`, `mask_lo := KEEP_MASK`) — the cap-write forced WITHOUT the arity-2 map-op.
fn fill_cap_after_spine(
    row: &mut [BabyBear],
    base_as: usize,
    after_leaf: &[BabyBear; 7],
    siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
    directions: &[u8],
) -> [BabyBear; CAP_OPEN_DIGEST_W] {
    // 7 scalar after-leaf fields at base_as + 0..6.
    for (i, &f) in after_leaf.iter().enumerate() {
        row[base_as + i] = f;
    }
    // 8-felt after-leaf digest at base_as + 7..14.
    let leaf_digest = cap_leaf_digest(after_leaf);
    for (j, &d) in leaf_digest.iter().enumerate() {
        row[base_as + 7 + j] = d;
    }
    // after-node blocks (8 felts each, NO sib/dir — SHARED with the read) at base_as + 15 + 8·lvl.
    let mut cur = leaf_digest;
    for lvl in 0..CAP_OPEN_DEPTH {
        let (l, r) = cap_mix(cur, siblings[lvl], directions[lvl]);
        let node = cap_node(l, r);
        let blk = base_as + 15 + CAP_OPEN_DIGEST_W * lvl;
        for (j, &n) in node.iter().enumerate() {
            row[blk + j] = n;
        }
        cur = node;
    }
    cur
}

/// **The TOMBSTONE after-spine column filler** — the REMOVE twin of [`fill_cap_after_spine`]. The
/// deployed post-remove root is `CanonicalCapTree::remove_witness`'s
/// `recompose_membership(CAP_ZERO8, siblings, directions)`: the EMPTY-SLOT digest folded up the
/// REMOVED LEAF'S OWN path (positions do not shift), so there is no after-LEAF at all — the level-0
/// input is a CONSTANT.
///
/// Fills the same `afterSpineCols` layout the UPDATE spine uses, with one substitution: the 7
/// leaf-field columns and the 8 leaf-digest columns are left at ZERO (the Lean
/// `CapOpenEmit.tombstoneZeroPins` PINS the digest group to `0`, and there is no leaf absorb), and
/// the fold starts from [`CAP_ZERO8`]. Returns the recomposed tombstone root.
///
/// LAW #1: this is a COLUMN filler. The constraints it satisfies are authored in
/// `metatheory/Dregg2/Circuit/Emit/CapOpenEmit.lean` (`removeTombstoneConstraints`) and proved in
/// `CapRemoveEmit.lean` (`effCapRemoveV3_forces_tombstoneFold`).
fn fill_cap_tombstone_spine(
    row: &mut [BabyBear],
    base_as: usize,
    siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
    directions: &[u8],
) -> [BabyBear; CAP_OPEN_DIGEST_W] {
    // base_as + 0..6 (leaf fields) and base_as + 7..14 (leaf digest) stay ZERO — the tombstone's
    // level-0 input IS `CAP_ZERO8`, which the 8 `tombstoneZeroPins` gates pin.
    for i in 0..15 {
        row[base_as + i] = BabyBear::ZERO;
    }
    let mut cur = crate::cap_root::CAP_ZERO8;
    for lvl in 0..CAP_OPEN_DEPTH {
        let (l, r) = cap_mix(cur, siblings[lvl], directions[lvl]);
        let node = cap_node(l, r);
        let blk = base_as + 15 + CAP_OPEN_DIGEST_W * lvl;
        for (j, &n) in node.iter().enumerate() {
            row[blk + j] = n;
        }
        cur = node;
    }
    cur
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
/// PI carriers are re-read from the rebuilt trace.
///
/// Returns the corrected PI vector at the INPUT's length — the patch is phase-B WIRING only and
/// never reshapes the PI vector: any tail PIs past the rotated `ROT_PI_COUNT` (the dsl rc on the
/// rc-wrapped PLAIN cohort members — e.g. the committed `grantCapVmDescriptor2R24` at 50) ride
/// through unchanged. The ROUTE owns the tail shape: the cap-open faces were never rc-wrapped in
/// the Lean emit (every committed `*CapOpen*` member carries the UNWRAPPED 46/47/49 base), so the
/// cap-open leg builder strips the rc BEFORE patching; the plain wide dispatcher keeps it. Widen
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
    let mut dpis: Vec<BabyBear> = pis.to_vec();
    // The four rotated commit pins sit at the v1 prefix count `V1_PI_COUNT..+4` (the same slots
    // `rotPins` / `generate_rotated_effect_vm_trace` append them to). Indexing off `V1_PI_COUNT`
    // keeps these aligned when the v1 prefix grows (e.g. Phase C pushed it 34→42).
    dpis[V1_PI_COUNT] = r0[BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit
    dpis[V1_PI_COUNT + 1] = last[AFTER_BASE + B_STATE_COMMIT]; // rotated NEW commit
    dpis[V1_PI_COUNT + 2] = last[AFTER_BASE + B_COMMITTED_HEIGHT]; // committed height
    dpis[V1_PI_COUNT + 3] = last[CAVEAT_BASE + C_CAVEAT_COMMIT]; // caveat commit
    Ok(dpis)
}

/// Widen an already-built rotated base trace (`ROT_WIDTH`-wide) to the `CAP_OPEN_WIDTH`-wide
/// cap-open trace, filling the [`CAP_OPEN_MEMBERSHIP_COLS`] (329) cap-MEMBERSHIP columns on EVERY
/// row uniformly with `w` (so the every-row base gates — dir-bool, rootPin, targetBind,
/// transferFacet/facetHi/authTag — hold on every row). The base trace's own `ROT_WIDTH` columns +
/// 38 PIs are unchanged; the cap-open appendix is purely additive and lands at `CAP_OPEN_BASE =
/// GRAD_ROT_WIDTH` (the cap-open builds on the GRADUATED rotated layout). The graduated rotated
/// chip-lane columns (`ROT_WIDTH..GRAD_ROT_WIDTH`) are filled automatically by the prove wrapper's
/// `descriptor_ir2::fill_chip_lanes` — NOT here. Since Phase H-CAP-8 there is NO separate cap
/// chip-lane tail: the 17 [`CAP_OPEN_LANE_SITES`] absorb their lane outputs directly into the
/// committed `node8` groups, so `CAP_OPEN_SPAN == CAP_OPEN_MEMBERSHIP_COLS` and the membership
/// columns ARE the whole appendix. The base trace MUST be a `ROT_WIDTH`-wide
/// rotated trace the base `attenuateV3` constraints already accept (e.g. from
/// [`generate_rotated_effect_vm_trace`] on an AttenuateCapability turn).
pub fn widen_to_cap_open(trace: &mut [Vec<BabyBear>], w: &CapOpenWitness) -> Result<(), String> {
    widen_to_cap_open_avail(trace, w, 0)
}

/// The AVAIL-AWARE cap-open widener (GAP #4, cap-open member): [`widen_to_cap_open`] for a base
/// trace produced at a NONZERO availability pad ([`generate_rotated_effect_vm_trace_avail`]). The
/// hardened `…-v1-avail` transfer cap-open members widen their v1 FACE by `avail_pad` witness
/// columns, so the rotated appendix, the graduated lanes, and hence the cap-open appendix base ALL
/// shift by the pad (Lean `effCapOpenV3` appends at `base.traceWidth`). At `avail_pad = 0` this is
/// byte-identical to the bare widener. Derive the pad from the TARGET DESCRIPTOR's name
/// ([`avail_pad_for_descriptor_name`]) — the pad is a property of the descriptor being proven.
pub fn widen_to_cap_open_avail(
    trace: &mut [Vec<BabyBear>],
    w: &CapOpenWitness,
    avail_pad: usize,
) -> Result<(), String> {
    if trace.is_empty() {
        return Err("cap-open widen: empty base trace".into());
    }
    if trace[0].len() != ROT_WIDTH + avail_pad {
        return Err(format!(
            "cap-open widen: base trace width {} != {} (ROT_WIDTH {ROT_WIDTH} + avail pad {avail_pad})",
            trace[0].len(),
            ROT_WIDTH + avail_pad
        ));
    }
    if w.recomposes() != w.cap_root {
        return Err("cap-open widen: witness does not recompose its cap_root".into());
    }
    for row in trace.iter_mut() {
        row.resize(CAP_OPEN_WIDTH + avail_pad, BabyBear::ZERO);
        fill_cap_open(row, CAP_OPEN_BASE + avail_pad, w);
    }
    Ok(())
}

/// **THE WIDE CAP-OPEN widener (the cap-open READ tail's faithful 8-felt commit).** Given a
/// fully-laid `CAP_OPEN_WIDTH`-wide cap-open trace (a base rotated trace already passed through
/// [`widen_to_cap_open`]) and its base PI vector, appends the two [`WIDE_NUM_CARRIERS`]×8
/// BEFORE/AFTER wide carrier blocks at `CAP_OPEN_WIDTH` (1976) / `+ WIDE_CARRIER_BLOCK_SPAN`
/// (2456) and the 16 wide commit PIs — the cap-open tail's wide member is
/// `wideAppend (capOpenHost) 187 238`, carriers PAST the [`CAP_OPEN_SPAN`] (329) cap-open
/// appendix. The cap-open host constraints / membership columns are CARRIED UNCHANGED; the wide
/// carriers re-absorb the SAME `BEFORE_BASE`/`AFTER_BASE` limbs. Returns the appended `dpis`. The
/// trace is resized in place to `CAP_OPEN_WIDTH + WIDE_CARRIER_APPENDIX = 2936`.
///
/// ⚠ That RAW appended width is NOT a deployed descriptor's `trace_width`. The committed wide
/// cap-WRITE member (`attenuateCapOpenEffVmDescriptor2R24` in
/// `circuit/descriptors/rotation-wide-registry-staged.tsv`) is **2021** wide, because the
/// deployed producer lays the after-spine FIRST (so its host is
/// `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`, see
/// [`generate_rotated_cap_attenuate_after_spine_wide`]) and then runs
/// [`compact_s2_columns`] ∘ [`compact_e1_columns`] over the appended row. Do not derive a
/// descriptor width by adding this appendix to a host width; read the registry.
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

/// The AVAIL-AWARE wide cap-open lift (GAP #4, the wide cap-open-EFF member): a hardened
/// `…-v1-avail` cap-open member (the `transferCapOpenEffVmDescriptor2R24` key post-regen) widens
/// its v1 FACE by the availability witness columns, so the cap-open appendix — and hence the
/// wide carrier base — rides at `CAP_OPEN_WIDTH + avail_pad` (the retargeted wide row is Lean
/// `wideAppend transferCapOpenEffV3Avail TR_AVAIL_BB (TR_AVAIL_BB + 239)`), and the carriers
/// re-absorb the limbs at the avail-shifted rotated bases (`BEFORE/AFTER_BASE + avail_pad`).
/// At `avail_pad = 0` this is byte-identical to [`append_wide_carriers_cap_open`]. Derive the
/// pad from the RESOLVED descriptor's name ([`avail_pad_for_descriptor_name`]) — the pad is a
/// property of the descriptor being proven.
pub fn append_wide_carriers_cap_open_avail(
    trace: &mut [Vec<BabyBear>],
    base_pis: Vec<BabyBear>,
    avail_pad: usize,
) -> Result<Vec<BabyBear>, String> {
    if trace.is_empty() {
        return Err("cap-open wide: empty base trace".into());
    }
    if trace[0].len() != CAP_OPEN_WIDTH + avail_pad {
        return Err(format!(
            "cap-open wide: base trace width {} != {} (CAP_OPEN_WIDTH {CAP_OPEN_WIDTH} + avail pad \
             {avail_pad}; widen_to_cap_open_avail first)",
            trace[0].len(),
            CAP_OPEN_WIDTH + avail_pad
        ));
    }
    Ok(append_wide_carriers_avail(
        trace,
        base_pis,
        CAP_OPEN_WIDTH + avail_pad,
        avail_pad,
    ))
}

/// The cap-root group column, projected from the Lean-generated group table.
fn cap_root_group_col(block_base: usize, lane: usize) -> usize {
    block_base + CAP_ROOT_GROUP[lane]
}

/// **THE ATTENUATE cap-WRITE AFTER-SPINE producer (`attenuateCapOpenEffVmDescriptor2R24` wide member).**
/// The cap twin of [`generate_rotated_refusal_write_wide`]: given a `CAP_OPEN_WIDTH`-wide cap-open trace
/// (a rotated attenuate base already passed through [`widen_to_cap_open`], whose READ appendix opened the
/// held `CapLeaf` against the BEFORE cap-root8), this FORCES the faithful 8-felt in-place UPDATE-AT-KEY
/// (`effCapOpenWriteV3_forces_write8`) WITHOUT the arity-2 map-op:
///   * lays the AFTER-spine appendix at `CAP_OPEN_WIDTH` ([`fill_cap_after_spine`]) — the held leaf with
///     `mask_lo := keep_mask` folded over the SHARED sibling path (`cap_open.siblings`/`directions`) to the
///     recomposed AFTER `cap_root8`;
///   * writes the BEFORE `cap_root8` (`cap_open.cap_root`) into the BEFORE-block cap-root GROUP and the
///     recomposed AFTER `cap_root8` into the AFTER-block cap-root GROUP (lane 0 + the 7 completion limbs),
///     so the READ appendix's `beforeRootWelds` and the after-spine's `rootPin` both hold;
///   * fills the submask-lookup param columns (`CAP_KEY @ 71`, `HELD_MASK @ 72`, `KEEP_MASK @ 73`) so the
///     `granted ⊑ held` non-amplification tooth is well-defined WITHOUT the map-op;
///   * recomputes the two rotated block commits (the overridden 8-felt groups now bind), then appends the
///     generic wide carriers at `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`.
///
/// Returns the wide `dpis` (the 16 wide commit PIs re-absorb the SAME overridden cap-root groups, so the
/// published ~124-bit anchor binds the genuine faithful write — never the lane-0 squeeze). NO map heaps.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_cap_attenuate_after_spine_wide(
    trace: &mut Vec<Vec<BabyBear>>,
    base_pis: Vec<BabyBear>,
    cap_open: &CapOpenWitness,
    cap_key: BabyBear,
    held_value: BabyBear,
    keep_mask: BabyBear,
) -> Result<Vec<BabyBear>, String> {
    generate_rotated_cap_attenuate_after_spine(trace, cap_open, cap_key, held_value, keep_mask)?;
    Ok(append_wide_carriers(
        trace,
        base_pis,
        CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN,
    ))
}

/// **The NARROW half of [`generate_rotated_cap_attenuate_after_spine_wide`]** — everything that lift
/// does to the trace COLUMNS, stopping before the wide carriers. This is the producer for the NARROW
/// cap-write member (`attenuateCapOpenEffVmDescriptor2R24` at
/// `CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN`), which had no Rust producer at all: the only caller
/// of the after-spine lift was the SDK's wide leg, so nothing could build a trace matching the narrow
/// descriptor's width, and the circuit-level prove-through tests were left ignored.
///
/// The wide lift is now literally this plus [`append_wide_carriers`], so the two cannot drift.
pub fn generate_rotated_cap_attenuate_after_spine(
    trace: &mut [Vec<BabyBear>],
    cap_open: &CapOpenWitness,
    cap_key: BabyBear,
    held_value: BabyBear,
    keep_mask: BabyBear,
) -> Result<(), String> {
    use super::columns::PARAM_BASE;
    if trace.is_empty() {
        return Err("attenuate after-spine: empty trace".into());
    }
    if trace[0].len() != CAP_OPEN_WIDTH {
        return Err(format!(
            "attenuate after-spine: trace width {} != CAP_OPEN_WIDTH {CAP_OPEN_WIDTH} \
             (widen_to_cap_open first)",
            trace[0].len()
        ));
    }
    // The AFTER leaf: the held `CapLeaf` with `mask_lo` (field 3) rebound to the narrowed KEEP_MASK —
    // the exact `writesTo8` UPDATE-AT-KEY the deployed after-spine forces (same slot_hash/target/…).
    let mut after_leaf = cap_open.leaf;
    after_leaf[3] = keep_mask;
    let before_root8 = cap_open.cap_root;

    // The submask-lookup param columns (Lean `EffectVmEmitV2.{CAP_KEY=3, HELD_MASK=4, KEEP_MASK=5}`); the
    // `submaskLookup` reads `[prmCol KEEP_MASK, prmCol HELD_MASK]` = cols 73/72.
    let cap_key_col = PARAM_BASE + 3; // 71
    let held_mask_col = PARAM_BASE + 4; // 72
    let keep_mask_col = PARAM_BASE + 5; // 73

    let after_spine_base = CAP_OPEN_WIDTH;
    let host_width = CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN;
    for row in trace.iter_mut() {
        row.resize(host_width, BabyBear::ZERO);
        let after_root8 = fill_cap_after_spine(
            row,
            after_spine_base,
            &after_leaf,
            &cap_open.siblings,
            &cap_open.directions,
        );
        // Override the BEFORE/AFTER rotated-block cap-root 8-felt GROUPS with the genuine roots so the
        // READ `beforeRootWelds` (BEFORE group == membership root8) and the after-spine `rootPin` (AFTER
        // group == recomposed narrowed root8) hold, and the wide carriers re-absorb the full 8-felt write.
        for lane in 0..CAP_OPEN_DIGEST_W {
            row[cap_root_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[cap_root_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        row[cap_key_col] = cap_key;
        row[held_mask_col] = held_value;
        row[keep_mask_col] = keep_mask;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }
    Ok(())
}

/// **The CAP-TREE INSERT/REMOVE after-spine OVERRIDE** — the shared column work of the INSERT-shaped
/// (`effCapInsertV3`: delegate / introduce / delegateAtten) and REMOVE-shaped (`effCapRemoveV3`:
/// revokeDelegation) keystone deploys. The cap-open READ appendix was already laid by
/// [`widen_to_cap_open`] from the SHAPE-matched witness (INSERT: the spliced leaf's membership in the
/// REBUILT AFTER tree, `cap_root.rs::CanonicalCapTree::insert_witness`; REMOVE: the removed leaf's
/// membership in BEFORE, whose zero-fold is `remove_witness`). This helper:
///   * overrides the BEFORE/AFTER rotated-block cap-root 8-felt GROUPS with the genuine
///     `CanonicalCapTree` roots — so the keystone's root welds (INSERT: read `capRoot` == AFTER group;
///     REMOVE: read `capRoot` == BEFORE group) hold, and the wide carriers re-absorb the full 8-felt
///     write (never the lane-0 squeeze);
///   * fills the cap-write param columns (`CAP_KEY @ 71`, `HELD_MASK @ 72`, `KEEP_MASK @ 73`,
///     `ANCHOR_KEY @ 74`, `ANCHOR_MASK @ 75`) so the surviving base legs (delegateAtten's
///     `granted ⊑ held` submask lookup over cols 73/72) are well-defined — NO map-op, NO map heap
///     (the arity-2 scalar pair is DROPPED from the Lean bases);
///   * recomputes the two rotated block commits (the overridden 8-felt groups now bind).
///
/// The trace stays at `CAP_OPEN_WIDTH` (the keystone wraps add NO columns beyond the cap-open
/// appendix); the caller appends the wide carriers ([`append_wide_carriers_cap_open`]) for the wide leg.
#[allow(clippy::too_many_arguments)]
pub fn apply_rotated_cap_write_after_spine(
    trace: &mut [Vec<BabyBear>],
    dpis: &mut [BabyBear],
    before_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    after_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    cap_key: BabyBear,
    held_mask: BabyBear,
    keep_mask: BabyBear,
    anchor_key: BabyBear,
    anchor_mask: BabyBear,
) -> Result<(), String> {
    use super::columns::PARAM_BASE;
    if trace.is_empty() {
        return Err("cap insert/remove after-spine: empty trace".into());
    }
    if trace[0].len() != CAP_OPEN_WIDTH {
        return Err(format!(
            "cap insert/remove after-spine: trace width {} != CAP_OPEN_WIDTH {CAP_OPEN_WIDTH} \
             (widen_to_cap_open first)",
            trace[0].len()
        ));
    }
    let cap_key_col = PARAM_BASE + 3; // 71 (the fresh inserted key / the removed key)
    let held_mask_col = PARAM_BASE + 4; // 72 (the held/read value — submask RHS)
    let keep_mask_col = PARAM_BASE + 5; // 73 (the conferred/narrowed value — submask LHS)
    let anchor_key_col = PARAM_BASE + 6; // 74 (the held-authority anchor key)
    let anchor_value_col = PARAM_BASE + 7; // 75 (the anchor's committed value)
    for row in trace.iter_mut() {
        for lane in 0..CAP_OPEN_DIGEST_W {
            row[cap_root_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[cap_root_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        row[cap_key_col] = cap_key;
        row[held_mask_col] = held_mask;
        row[keep_mask_col] = keep_mask;
        row[anchor_key_col] = anchor_key;
        row[anchor_value_col] = anchor_mask;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }
    // Re-derive the OLD/NEW rotated commit PIs (the cap-root group override moved the rotated
    // commit) — exactly as `generate_rotated_cap_write_base` re-derives them. The WIDE member
    // retires these 1-felt pins (`dropLegacyCommitPins1`), but the NARROW keystone leg still
    // binds them.
    if dpis.len() > V1_PI_COUNT + 1 {
        dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT]; // rotated OLD commit
        dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];
        // rotated NEW commit
    }
    Ok(())
}

/// **THE CAP-TREE INSERT AFTER-SPINE producer (`delegate`/`introduce`/`delegateAttenWriteCapOpen…R24`
/// wide members).** The insert twin of [`generate_rotated_cap_attenuate_after_spine_wide`]: given a
/// `CAP_OPEN_WIDTH`-wide cap-open trace whose READ appendix opened the SPLICED (conferred) `CapLeaf`
/// against the REBUILT AFTER cap-root8 (the `CanonicalCapTree::insert_witness` after-membership path —
/// [`widen_to_cap_open`] with the spliced witness), this forces the faithful 8-felt fresh-key INSERT
/// (`CapInsertEmit.effCapInsertV3_forces_write8`) WITHOUT any arity-2 map-op: the BEFORE group carries
/// the genuine pre-insert root (witness-carried, folding into the committed rotated state-commit), the
/// AFTER group the rebuilt post-insert root the read's rootPin + the keystone's AFTER welds bind. Then
/// appends the generic wide carriers at the descriptor's host width (`CAP_OPEN_WIDTH`). NO map heaps. -/
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_cap_insert_after_spine_wide(
    trace: &mut Vec<Vec<BabyBear>>,
    base_pis: Vec<BabyBear>,
    before_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    after_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    inserted_key: BabyBear,
    inserted_value: BabyBear,
    held_mask: BabyBear,
    anchor_key: BabyBear,
    anchor_mask: BabyBear,
) -> Result<Vec<BabyBear>, String> {
    let mut base_pis = base_pis;
    apply_rotated_cap_write_after_spine(
        trace,
        &mut base_pis,
        before_root8,
        after_root8,
        inserted_key,
        held_mask,
        inserted_value,
        anchor_key,
        anchor_mask,
    )?;
    Ok(append_wide_carriers(trace, base_pis, CAP_OPEN_WIDTH))
}

/// **THE CAP-TREE REMOVE AFTER-SPINE producer (`revokeDelegationWriteCapOpenVmDescriptor2R24` wide
/// member).** The remove mirror: given a `CAP_OPEN_WIDTH`-wide cap-open trace whose READ appendix
/// opened the REMOVED `CapLeaf` against the BEFORE cap-root8 (exactly the consumed-cap membership
/// witness the revoke route already carries), this forces the faithful 8-felt tombstone REMOVE
/// (`CapRemoveEmit.effCapRemoveV3_forces_write8`): the BEFORE group carries the membership-opened
/// pre-remove root the keystone's BEFORE welds bind; the AFTER group the deployed tombstone zero-fold
/// (`CanonicalCapTree::remove_witness` `new_root`). Then appends the wide carriers at the host width.
/// NO map heaps. The base's §14.EPOCH bump gate rides the base trace's genuine epoch limbs. -/
pub fn generate_rotated_cap_remove_after_spine_wide(
    trace: &mut Vec<Vec<BabyBear>>,
    base_pis: Vec<BabyBear>,
    before_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    after_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    removed_key: BabyBear,
    held_value: BabyBear,
    siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
    directions: &[u8],
) -> Result<Vec<BabyBear>, String> {
    let mut base_pis = base_pis;
    apply_rotated_cap_remove_after_spine(
        trace,
        &mut base_pis,
        before_root8,
        after_root8,
        removed_key,
        held_value,
        siblings,
        directions,
    )?;
    Ok(append_wide_carriers(
        trace,
        base_pis,
        CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN,
    ))
}

/// **THE CAP-TREE REMOVE TOMBSTONE AFTER-SPINE OVERRIDE** — the REMOVE-shaped keystone's column
/// work, at the width the Lean `effCapRemoveV3` now commits
/// (`CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN` = 2119). It replaces the REMOVE members' old use of
/// [`apply_rotated_cap_write_after_spine`], which left the trace at `CAP_OPEN_WIDTH` and therefore
/// put **nothing** on the committed AFTER cap-root group.
///
/// The cap-open READ appendix was already laid by [`widen_to_cap_open`] from the removed leaf's
/// membership witness in BEFORE (`cap_root.rs::CanonicalCapTree::remove_witness`). This helper:
///   * resizes each row to the write width and lays the TOMBSTONE after-spine
///     ([`fill_cap_tombstone_spine`]) — the empty-slot digest `CAP_ZERO8` folded up the SHARED
///     sibling path, which is exactly `remove_witness`'s `new_root`;
///   * writes the BEFORE cap-root group (the read's root, bound by the keystone's BEFORE welds) and
///     the AFTER cap-root group (`after_root8`, the root the prover CLAIMS);
///   * fills the cap-write param columns (`CAP_KEY @ 71` = the removed key, `HELD_MASK @ 72` = the
///     read value; a tombstone confers nothing, so `KEEP_MASK`/`ANCHOR_*` are zero);
///   * recomputes both rotated block commits and re-derives the two commit PIs.
///
/// ⚠ `after_root8` is the value WRITTEN into the committed AFTER group — it is the prover's claim,
/// not a computation this function trusts. The in-circuit tombstone spine PINS that group to the
/// zero-fold (`removeTombstoneConstraints`'s 8 `rootPinGate`s), so a claim that is not the fold is
/// **UNSAT at the prover**. Honest callers pass `remove_witness().new_root`; the adversarial tests
/// pass a fabrication and get a refusal. That asymmetry is the whole point of the member.
pub fn apply_rotated_cap_remove_after_spine(
    trace: &mut [Vec<BabyBear>],
    dpis: &mut [BabyBear],
    before_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    after_root8: [BabyBear; CAP_OPEN_DIGEST_W],
    removed_key: BabyBear,
    held_value: BabyBear,
    siblings: &[[BabyBear; CAP_OPEN_DIGEST_W]],
    directions: &[u8],
) -> Result<(), String> {
    use super::columns::PARAM_BASE;
    if trace.is_empty() {
        return Err("cap remove tombstone spine: empty trace".into());
    }
    if trace[0].len() != CAP_OPEN_WIDTH {
        return Err(format!(
            "cap remove tombstone spine: trace width {} != CAP_OPEN_WIDTH {CAP_OPEN_WIDTH} \
             (widen_to_cap_open first)",
            trace[0].len()
        ));
    }
    if siblings.len() < CAP_OPEN_DEPTH || directions.len() < CAP_OPEN_DEPTH {
        return Err(format!(
            "cap remove tombstone spine: need {CAP_OPEN_DEPTH} sibling/direction levels, got {}/{}",
            siblings.len(),
            directions.len()
        ));
    }
    let cap_key_col = PARAM_BASE + 3; // 71 — the removed key
    let held_mask_col = PARAM_BASE + 4; // 72 — the read value
    let keep_mask_col = PARAM_BASE + 5; // 73 — a remove confers nothing
    let anchor_key_col = PARAM_BASE + 6; // 74
    let anchor_value_col = PARAM_BASE + 7; // 75
    let host_width = CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN;
    for row in trace.iter_mut() {
        row.resize(host_width, BabyBear::ZERO);
        let _fold = fill_cap_tombstone_spine(row, CAP_OPEN_WIDTH, siblings, directions);
        for lane in 0..CAP_OPEN_DIGEST_W {
            row[cap_root_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[cap_root_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        row[cap_key_col] = removed_key;
        row[held_mask_col] = held_value;
        row[keep_mask_col] = BabyBear::ZERO;
        row[anchor_key_col] = BabyBear::ZERO;
        row[anchor_value_col] = BabyBear::ZERO;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }
    // Re-derive the OLD/NEW rotated commit PIs (the cap-root group override moved the commit).
    if dpis.len() > V1_PI_COUNT + 1 {
        dpis[V1_PI_COUNT] = trace[0][BEFORE_BASE + B_STATE_COMMIT];
        dpis[V1_PI_COUNT + 1] = trace[trace.len() - 1][AFTER_BASE + B_STATE_COMMIT];
    }
    Ok(())
}

/// Widen a rotated base trace (`ROT_WIDTH`) to the TURN-BOUND cap-open width
/// ([`CAP_OPEN_TB_WIDTH`], which EQUALS [`CAP_OPEN_WIDTH`]): the cap-open appendix, including the
/// `src` column laid by [`fill_cap_open`] from `w.src`. The TB descriptor (`effCapOpenV3TB`) adds
/// NO column — it pins that EXISTING `src` column to [`CAP_OPEN_TB_PI_SRC`] on the FIRST row.
///
/// ⚑ 2026-07-31: this used to take `actor`/`dst` and lay them in two extra columns. Those columns
/// and their pins are gone (see [`CAP_OPEN_TB_WIDTH`]); the TB widener is now exactly the cap-open
/// widener, retained as a named entry point because the TB *PI* vector still differs
/// ([`cap_open_tb_dpis`]).
pub fn widen_to_cap_open_tb(trace: &mut [Vec<BabyBear>], w: &CapOpenWitness) -> Result<(), String> {
    widen_to_cap_open_tb_avail(trace, w, 0)
}

/// The AVAIL-AWARE turn-bound widener (GAP #4, cap-open TB member): [`widen_to_cap_open_tb`] for a
/// base trace produced at a NONZERO availability pad — the hardened
/// `transferCapOpenTBVmDescriptor2R24` member's cap-open appendix rides `avail_pad` past the bare
/// layout (the turn-identity PI slot is UNCHANGED: the pad shifts columns, never PI indices). At
/// `avail_pad = 0` this is byte-identical to the bare TB widener.
pub fn widen_to_cap_open_tb_avail(
    trace: &mut [Vec<BabyBear>],
    w: &CapOpenWitness,
    avail_pad: usize,
) -> Result<(), String> {
    widen_to_cap_open_avail(trace, w, avail_pad)
}

/// Extend a base 46-PI rotated vector to the turn-bound 47-PI vector by appending the ONE
/// turn-identity PI (`src` at 46, [`CAP_OPEN_TB_PI_SRC`]; the deployed
/// `transferCapOpenTBVmDescriptor2R24.public_input_count` is [`CAP_OPEN_TB_PI_COUNT`] = 47). The
/// honest prover publishes its own turn's `src`; the verifier OVERRIDES that slot from the trusted
/// turn before `verify_vm_descriptor2` (see [`anchor_cap_open_turn_pins`]), so a forged `src` is
/// UNSAT — the pinned column is the one `targetBindGate` and the depth-16 membership open read.
///
/// ⚑ 2026-07-31: this used to append `actor` at 47 and `dst` at 48. Those two slots pinned columns
/// no other constraint read, so the prover chose both sides and a light client that believed them
/// attested was believing nothing. `TurnAuthCapOpenWeld` is the staged successor that publishes
/// `actor`/`dst` again with the Lamport turn-digest lookup FORCING them.
pub fn cap_open_tb_dpis(base_dpis: &[BabyBear], src: BabyBear) -> Vec<BabyBear> {
    let mut dpis = base_dpis[..ROT_PI_COUNT].to_vec();
    debug_assert_eq!(dpis.len(), CAP_OPEN_TB_PI_BASE);
    dpis.push(src); // PI 46 (CAP_OPEN_TB_PI_SRC)
    debug_assert_eq!(dpis.len(), CAP_OPEN_TB_PI_COUNT);
    dpis
}

/// **`anchor_cap_open_turn_pins` — the `TurnIdentityAnchored` verifier override (DEPLOYMENT side).**
/// Override the turn-identity PI (`46`) of a TB cap-open dpis vector with the TRUSTED turn's `src`
/// felt, exactly as the record-pin family anchors its own PI from the trusted post-cell. A
/// prover-published `src` that disagrees makes the anchored PI disagree with the proof's bound,
/// first-row-pinned column ⇒ `verify_vm_descriptor2` UNSAT ⇒ reject. This is what makes a LEDGERLESS
/// light client able to conclude the published turn's `src` MATCHES the proven transition — and the
/// binding is real because `targetBindGate` chains that column to the opened leaf and thence to the
/// committed cap root.
///
/// ⚑ It used to override `actor` and `dst` as well. Doing so *looked* like it forced them, and it
/// did force the published PI to equal a trace column — but that column was read by nothing else,
/// so an honest anchor rejected only a prover who forgot to move the column too. Both are gone.
pub fn anchor_cap_open_turn_pins(dpis: &mut [BabyBear], trusted_src: BabyBear) {
    dpis[CAP_OPEN_TB_PI_SRC] = trusted_src;
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
// transfer member — descriptor `transferVmDescriptor2R24Wide`, width `WIDE_WIDTH` = 2607 /
// PI `WIDE_PI_COUNT`).
//
// STAGED-ADDITIVE: this is a PARALLEL wide producer BESIDE the live 1-felt path. The live
// `generate_rotated_effect_vm_trace` (GRAD_ROT_WIDTH = 1647) is UNTOUCHED; this WIDENS its
// output to `WIDE_WIDTH` by appending two `WIDE_NUM_CARRIERS` (60) × 8-felt wide commitment
// chains (BEFORE + AFTER) that re-absorb the SAME rotated limbs the 1-felt block already lays,
// exposing the genuine 8-felt (~124-bit) state commitment. The 16 appended PIs publish the
// BEFORE first-row + AFTER last-row 8-felt commits.
//
// The geometry (v2 flag-day, derived from `NUM_PRE_LIMBS = 178` via `wide_carriers_for_limbs`;
// the emitted twin was `circuit/descriptors/rotation-wide-transfer-staged.tsv`, DELETED
// 2026-07-31 as a diverged fork; the deployed twin is `rotation-wide-registry-staged.tsv` row 0):
//   * BEFORE wide carriers: base `WIDE_BEFORE_CBASE = 1647`, carrier `k` at `1647 + 8·k .. +7`
//     (60 carriers → cols 1647..2126); carrier 59 (cols 2119..2126) = the BEFORE 8-felt commit.
//   * AFTER  wide carriers: base `WIDE_AFTER_CBASE  = 2127`, carrier `k` at `2127 + 8·k .. +7`
//     (60 carriers → cols 2127..2606); carrier 59 (cols 2599..2606) = the AFTER 8-felt commit,
//     ending FLUSH at `WIDE_WIDTH − 1` (const-asserted below).
//   * The chain absorbs the rotated block's limbs (`BEFORE_BASE + 0..NUM_PRE_LIMBS` then iroot
//     at `BEFORE_BASE + B_IROOT`) — the SAME columns the 1-felt `wireCommitR` reads. The chip
//     lookups are: head arity-4 over `[l0..l3]`, fifty-eight body arity-11 over
//     `prev8 ‖ [l3i,l3i+1,l3i+2]`, final arity-11 over `prev8 ‖ [iroot, 0, 0]`. Each carrier is
//     filled CHIP-FAITHFULLY (the chip table derives `out0..out7` from the genuine permutation
//     with the arity-tag seeding, so a carrier must equal `chip_absorb_all_lanes(arity, inputs)`
//     or the `out[i] == lane[i]` AIR bites).
//   * The 8 PIs after the host's ← BEFORE carrier-59 on the FIRST row; the final 8 ← AFTER
//     carrier-59 on the LAST row.
// ============================================================================

/// The number of 8-felt carriers one wide commitment chain needs for `n` pre-iroot limbs — the
/// SHARED const derivation both the allocation constants below and the generator
/// ([`fill_wide_block`]'s loop) obey: one arity-4 head (consumes 4 limbs), then the body loop
/// (3 limbs per arity-11 carrier while ≥ 3 remain, else 1 limb per arity-9 carrier), then the
/// final iroot carrier. MUST mirror `fill_wide_block` exactly (const-asserted below; the
/// generator debug-asserts it lands on [`WIDE_COMMIT_CARRIER`]).
pub const fn wide_carriers_for_limbs(n: usize) -> usize {
    let body = n - 4;
    // head + 3-limb body groups + 1-limb leftover carriers + the final iroot carrier.
    1 + body / 3 + body % 3 + 1
}
/// The number of 8-felt carriers per wide commitment chain, DERIVED from [`NUM_PRE_LIMBS`]
/// (178 → head + 58 clean three-limb body groups + the final iroot carrier = 60). The RETIRED
/// v1 geometry (169 limbs → 57 carriers) is version-refused at the registry boundary
/// (`effect_vm_descriptors::WIDE_CARRIER_GEOMETRY_VERSION`), never silently widened.
pub const WIDE_NUM_CARRIERS: usize = wide_carriers_for_limbs(NUM_PRE_LIMBS);
/// One wide carrier block's column span (8 columns per carrier): 480.
pub const WIDE_CARRIER_BLOCK_SPAN: usize = WIDE_NUM_CARRIERS * 8;
/// The two-block (BEFORE + AFTER) wide carrier appendix span: 960.
pub const WIDE_CARRIER_APPENDIX: usize = 2 * WIDE_CARRIER_BLOCK_SPAN;
/// The committed wide trace width (`wideAppend` adds the [`WIDE_CARRIER_APPENDIX`] carrier columns
/// to the graduated rotated base): `transferVmDescriptor2R24Wide.trace_width` (1647 + 960 = 2607).
pub const WIDE_WIDTH: usize = GRAD_ROT_WIDTH + WIDE_CARRIER_APPENDIX;
/// The base column of the BEFORE wide carrier block (`wideBeforeCBase = h.traceWidth = GRAD_ROT_WIDTH`).
pub const WIDE_BEFORE_CBASE: usize = GRAD_ROT_WIDTH;
/// The base column of the AFTER wide carrier block (`wideAfterCBase = h.traceWidth + WIDE_CARRIER_BLOCK_SPAN`).
pub const WIDE_AFTER_CBASE: usize = GRAD_ROT_WIDTH + WIDE_CARRIER_BLOCK_SPAN;
/// The in-block carrier index of the final 8-felt commitment carrier (59).
pub const WIDE_COMMIT_CARRIER: usize = WIDE_NUM_CARRIERS - 1; // 59

// FLAG-DAY GEOMETRY PINS (the wide-carrier rotation, v2): the derived constants must land on the
// exact 184-limb / 62-carrier shape (the nine-lane epoch) — a drift in `NUM_PRE_LIMBS` or the derivation
// breaks the build here, not at proving time. (The Lean twins are `wideNumCarriers_eq` /
// `wideCarrierBlockSpan_eq` / `wideAppendixSpan_eq` / `wideCommitCarrier_eq` in
// `EffectVmEmitRotationWide.lean`.)
const _: () = {
    assert!(
        NUM_PRE_LIMBS == 187,
        "wide geometry v2 is pinned to 187 pre-iroot limbs (the KEY NONET epoch: 184 + 3, giving the owner key its ninth lane at limb 186 — the Ed25519 sign bit. 185/186 were traps: B_SPAN's floor division vs chunkCount needs n = 1 mod 3)"
    );
    assert!(
        WIDE_NUM_CARRIERS == 63,
        "187 limbs need 63 wide carriers (head + 61 body + iroot); the extra body group absorbs limbs 184..186, the last of which IS the owner nonet's ninth lane"
    );
    assert!(
        WIDE_COMMIT_CARRIER == 62,
        "the final (commitment) carrier is 62"
    );
    // ⚑ LITERALS, deliberately. These read `== WIDE_NUM_CARRIERS * 8` and `== 2 *
    // WIDE_CARRIER_BLOCK_SPAN` for one day — verbatim restatements of the two definitions ~20 lines
    // up, so both were `x == x` and neither could ever fail.
    assert!(
        WIDE_CARRIER_BLOCK_SPAN == 504,
        "one wide carrier block spans 504 columns (63 carriers × 8)"
    );
    assert!(
        WIDE_CARRIER_APPENDIX == 1008,
        "the two-block wide appendix spans 1008 columns"
    );
    // The AFTER block's commit carrier ends FLUSH at the allocated width (no slack, no overrun).
    assert!(WIDE_AFTER_CBASE + 8 * WIDE_COMMIT_CARRIER + 8 == WIDE_WIDTH);
};
/// The committed wide public-input count for the bare transfer-shape member
/// (`h.piCount + 16`, where `h.piCount = ROT_PI_COUNT + DFA_RC_LEN` — the wide host is the
/// `withDfaRcPins`-wrapped member, so the 4 dsl rc PIs ride BETWEEN the `ROT_PI_COUNT` base and
/// the 16 wide commit PIs).
pub const WIDE_PI_COUNT: usize = ROT_PI_COUNT + DFA_RC_LEN + 16;

/// Fill one block's [`WIDE_NUM_CARRIERS`]-carrier × 8-felt wide commitment chain at `cbase`,
/// reading the limbs from the rotated block at `limb_base` (`BEFORE_BASE` / `AFTER_BASE`). Each
/// carrier's 8 output lanes are filled CHIP-FAITHFULLY (`chip_absorb_all_lanes`), so the wide chip
/// lookups' `out[i] == lane[i]` equalities hold and the published 8-felt commit binds the
/// [`NUM_PRE_LIMBS`] limbs + iroot. The chain shape (4-wide head, fifty-eight 3-wide arity-11 body
/// groups, the arity-11 `iroot ‖ 0 ‖ 0` final) is the byte twin of `poseidon2::wire_commit_8` and
/// the Lean `wireCommitR8` — but seeded through the chip's arity tag. The loop's carrier count is
/// the SAME derivation as [`wide_carriers_for_limbs`] (debug-asserted at the end).
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
            // (the 178-limb shape has NO leftover — 174 body limbs = 58 groups of 3 — but
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
        "wide chain must end on the derived commitment carrier (59 at 178 limbs) — \
         `wide_carriers_for_limbs` and this loop have diverged"
    );
}

// ⚑ DELETED 2026-07-31 — `generate_rotated_transfer_wide` (34 lines), the trace generator for the
// committed one-row descriptor `transferVmDescriptor2R24Wide`
// (`circuit/descriptors/rotation-wide-transfer-staged.tsv`, also deleted). It had NO callers outside
// two tests that went with it. The descriptor it produced traces for was a diverged fork of
// `WIDE_REGISTRY_STAGED_TSV` row 0 — the deployed transfer member is availability-hardened,
// membership-teeth-advanced, gentian-refuse-welded and E1-compacted, none of which the fork was. The
// live wide producer is `generate_rotated_effect_vm_descriptor_and_trace_wide` (the dispatcher the
// SDK and executor actually reach); this was a parallel one that only ever fed itself.

/// **THE GENERIC WIDE WIDENER (parametric in the host width / carrier base).** Given a fully-laid
/// rotated base trace (its `BEFORE_BASE`/`AFTER_BASE` limb blocks final, including any grow-gate root
/// override + `recompute_block_commit`) and its base PI vector, this:
///   * resizes each row to `host_width + WIDE_CARRIER_APPENDIX` and fills the two
///     `WIDE_NUM_CARRIERS`×8 BEFORE/AFTER wide carrier blocks at `cbB = host_width` /
///     `cbA = host_width + WIDE_CARRIER_BLOCK_SPAN` (the `wideBeforeCBase`/`wideAfterCBase` Lean
///     layout), chip-faithfully via [`fill_wide_block`] — reading the SAME `BEFORE_BASE`/`AFTER_BASE`
///     limbs the 1-felt block lays (so the 8-felt commit binds the same `NUM_PRE_LIMBS` limbs + iroot);
///   * APPENDS the 16 wide commit PIs PAST the base PIs: BEFORE commit (carrier `WIDE_COMMIT_CARRIER`,
///     first row) then AFTER commit (carrier `WIDE_COMMIT_CARRIER`, last row).
///     `host_width` is the wide member's HOST width (`d.traceWidth` in Lean): `GRAD_ROT_WIDTH` for
///     the rotated-cohort families, wider for the cap-open/after-spine tails. The wide carriers
///     land STRICTLY PAST the host's columns + gates (the appendix is purely additive), member-uniform
///     because `BEFORE_BASE`/`AFTER_BASE` (187/238) are uniform across the cohort. The number of base
///     PIs is preserved (the grow-gate families carry an extra PI[38]); the 16 wide PIs append after.
/// **THE S2 DELETION (Epoch 1).** Drop the two rotated 1-felt Merkle-Damgard chain carrier
/// bands and their 840 graduated chip-lane columns from an OLD-geometry wide trace, so the rows
/// match the committed S2-COMPACTED wide descriptor (Lean `RotWideCompactS2.compactS2`; every
/// member passed the `compactOk` emit gate). Geometry comes from the Lean-emitted single source
/// (`s2_compact_generated::S2_COMPACT_TABLE`); the three dropped bands per member are
/// `[bb+S2_CARRIER_OFF, bb+B_SPAN) ∪ [bb+B_SPAN+S2_CARRIER_OFF, bb+2·B_SPAN) ∪ [lane_base,
/// lane_base+S2_LANE_SPAN)`. Every published PI is UNCHANGED (the retired 1-felt commit slots stay
/// zeroed). Fails closed on an unknown key or a row too short to span the lane band (a mis-staged
/// producer, never a silent misalignment).
///
/// ⚑ The AFTER band used to be reached with a bare `bb + 239` — the 178-geometry `B_SPAN` written
/// out as a literal in the middle of an otherwise Lean-sourced routine. At 184 limbs it aimed the
/// second drain 8 columns short of the AFTER block's carrier band and 8 columns into its LIMBS.
pub fn compact_s2_columns(trace: &mut [Vec<BabyBear>], registry_key: &str) -> Result<(), String> {
    use super::s2_compact_generated::{
        S2_CARRIER_OFF, S2_CARRIER_SPAN, S2_COMPACT_TABLE, S2_LANE_SPAN,
    };
    let (_, bb, lane_base) = S2_COMPACT_TABLE
        .iter()
        .find(|(k, _, _)| *k == registry_key)
        .ok_or_else(|| format!("compact_s2_columns: {registry_key} not in S2_COMPACT_TABLE"))?;
    let (bb, lane_base) = (*bb, *lane_base);
    if bb + 2 * B_SPAN > lane_base {
        return Err(format!(
            "compact_s2_columns: {registry_key} geometry inconsistent (bb={bb}, lane_base={lane_base})"
        ));
    }
    for row in trace.iter_mut() {
        if row.len() < lane_base + S2_LANE_SPAN {
            return Err(format!(
                "compact_s2_columns: {registry_key} row width {} < lane band end {} — the trace \
                 is not the full old-geometry wide row (compact AFTER the wide append)",
                row.len(),
                lane_base + S2_LANE_SPAN
            ));
        }
        // descending order, so earlier drains do not shift later band positions
        row.drain(lane_base..lane_base + S2_LANE_SPAN);
        row.drain(bb + B_SPAN + S2_CARRIER_OFF..bb + B_SPAN + S2_CARRIER_OFF + S2_CARRIER_SPAN);
        row.drain(bb + S2_CARRIER_OFF..bb + S2_CARRIER_OFF + S2_CARRIER_SPAN);
    }
    Ok(())
}

/// **THE E1 DELETION (Epoch-1 SECOND flag-day).** After [`compact_s2_columns`], additionally drop
/// the DEAD v1-face column bands from an S2-compacted wide trace, so the rows match the committed
/// E1-COMPACTED wide descriptor (Lean `RotWideCompactE1.compactE1` at the DERIVED per-member kill-set
/// `deadColsE1 M 90` — every column at index ≥ 90 referenced by no surviving constraint / hash site /
/// range: the retired aux band `90..187`, the gentian refuse tail, and the note/heap/refusal/cap-open
/// appendix scratch bands). Geometry comes from the Lean-emitted single source
/// (`e1_compact_generated::E1_COMPACT_TABLE`) — ascending half-open `[start, end)` runs in POST-S2
/// coordinates. The kill-set constrains NOTHING that survives (`compactE1Ok` gated the emit), so the
/// deletion is value-preserving and every published PI is UNCHANGED. Drains DESCENDING so earlier
/// drains do not shift later positions. Fails closed on an unknown key or a row too short to span a
/// band (a mis-staged producer, never a silent misalignment). MUST be called AFTER `compact_s2_columns`
/// (the intervals are in the S2-compacted geometry).
pub fn compact_e1_columns(trace: &mut [Vec<BabyBear>], registry_key: &str) -> Result<(), String> {
    use super::e1_compact_generated::E1_COMPACT_TABLE;
    let (_, intervals) = E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == registry_key)
        .ok_or_else(|| format!("compact_e1_columns: {registry_key} not in E1_COMPACT_TABLE"))?;
    for row in trace.iter_mut() {
        // descending: drain the highest band first so lower band positions do not shift
        for &(start, end) in intervals.iter().rev() {
            if row.len() < end {
                return Err(format!(
                    "compact_e1_columns: {registry_key} row width {} < E1 band end {} — the trace \
                     is not the S2-compacted wide row (compact E1 AFTER S2)",
                    row.len(),
                    end
                ));
            }
            row.drain(start..end);
        }
    }
    Ok(())
}

/// **THE COMPACTION IMAGE of a LAYOUT column — where a pre-compaction column lands in the
/// COMMITTED wide member.** `Ok(Some(c))` = the surviving committed column; `Ok(None)` = the S2/E1
/// kill-set DELETED it, so no committed constraint can reference it.
///
/// ⚑ WHY THIS EXISTS, AND WHAT IT IS THE INVERSE OF. Every layout constant in this file
/// (`CAVEAT_BASE + …`, `AFTER_BASE + …`, `PARAM_BASE + …`) names a column in the ORIGINAL rotated
/// geometry — the geometry the NARROW `rotation-v3-staged-registry.tsv` still commits. The WIDE
/// registries are S2- and E1-COMPACTED (`compact_s2_columns` ∘ `compact_e1_columns`, the deletion
/// the Lean emit performed and this producer mirrors), so a consumer that computes a column from
/// the constants and then looks it up in a WIDE committed descriptor is comparing two DIFFERENT
/// coordinate systems. It finds nothing, and — because these lookups are fail-closed — it REFUSES
/// silently forever instead of reporting a geometry error. Measured 2026-07-29: `dsl_rc_claim_pi_lo`
/// looked for the DFA route-commitment carrier at raw column 715; the committed wide transfer row
/// binds it at 501 (715 → −120 across the two S2 carrier bands → 595 → −94 across the three E1
/// bands → 501), so the Dsl carrier fold arm refused EVERY deployed leg.
///
/// The mapping is computed by running the DEPLOYED compaction over a row of column IDENTITIES, so
/// it cannot drift from the deletion it inverts — a table regen that removes a DIFFERENT band of
/// the same size renumbers these columns and every caller moves with it. The identity row is sized
/// past both compactions' length guards and past the queried columns; the image of a surviving
/// column does not depend on the row's total width, since a deletion only removes columns BELOW it.
pub fn compacted_columns(
    registry_key: &str,
    raw_cols: &[usize],
) -> Result<Vec<Option<usize>>, String> {
    use super::e1_compact_generated::E1_COMPACT_TABLE;
    use super::s2_compact_generated::{S2_COMPACT_TABLE, S2_DELETED_COLS, S2_LANE_SPAN};

    let (_, _, lane_base) = S2_COMPACT_TABLE
        .iter()
        .find(|(k, _, _)| *k == registry_key)
        .ok_or_else(|| format!("compacted_columns: {registry_key} not in S2_COMPACT_TABLE"))?;
    let (_, e1) = E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == registry_key)
        .ok_or_else(|| format!("compacted_columns: {registry_key} not in E1_COMPACT_TABLE"))?;
    let e1_end = e1.iter().map(|&(_, end)| end).max().unwrap_or(0);
    let width = (lane_base + S2_LANE_SPAN)
        .max(e1_end + S2_DELETED_COLS)
        .max(raw_cols.iter().copied().max().unwrap_or(0) + 1)
        + 1;
    let mut identity: Vec<Vec<BabyBear>> =
        vec![(0..width).map(|c| BabyBear::new(c as u32)).collect()];
    compact_s2_columns(&mut identity, registry_key)?;
    compact_e1_columns(&mut identity, registry_key)?;
    Ok(raw_cols
        .iter()
        .map(|&raw| {
            identity[0]
                .iter()
                .position(|&v| v == BabyBear::new(raw as u32))
        })
        .collect())
}

/// [`compacted_columns`] for a single column.
pub fn compacted_column(registry_key: &str, raw_col: usize) -> Result<Option<usize>, String> {
    Ok(compacted_columns(registry_key, &[raw_col])?[0])
}

/// The WIDE registry KEY (TSV column 1) whose committed row carries `display_name`
/// (`EffectVmDescriptor2::name`, TSV column 2) — the key [`compacted_columns`] and the two
/// compaction passes are keyed by.
///
/// ⚑ SEVERAL KEYS SHARE ONE DISPLAY NAME (`attenuateVmDescriptor2R24` and
/// `revokeCapabilityVmDescriptor2R24` are both `dregg-effectvm-attenuateA-v1-genuine-…`), which is
/// exactly why this returns the key rather than letting a caller guess: the S2/E1 geometry is
/// per-KEY, so a display name matching keys with DIFFERENT geometry has no single answer and this
/// refuses rather than picking one. Where they agree — the case that actually occurs — the answer
/// is unambiguous whichever key is returned.
pub fn wide_registry_key_for_descriptor_name(display_name: &str) -> Result<&'static str, String> {
    use super::e1_compact_generated::E1_COMPACT_TABLE;
    use super::s2_compact_generated::S2_COMPACT_TABLE;
    use crate::effect_vm_descriptors::{UMEM_WELD_TABLE, WIDE_REGISTRY_STAGED_TSV};

    // Both forms, because a WELDED leg carries the `…-umem-wide-welded-staged` display name while
    // keying the SAME registry key (and the same S2/E1 geometry — the weld appends columns ABOVE
    // the compaction, so every committed column below it is unmoved). The welded names come from
    // the Lean derivation contract now that the welded registry TSV is derived, not shipped.
    let keys: Vec<&'static str> = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .filter_map(|line| {
            let mut it = line.splitn(3, '\t');
            let key = it.next()?;
            let display = it.next()?;
            (display == display_name).then_some(key)
        })
        .chain(
            UMEM_WELD_TABLE
                .iter()
                .filter(|r| r.name == display_name)
                .map(|r| r.key),
        )
        .collect();
    let first = *keys.first().ok_or_else(|| {
        format!(
            "wide_registry_key_for_descriptor_name: '{display_name}' is in no WIDE registry row"
        )
    })?;
    let geom = |k: &str| {
        (
            S2_COMPACT_TABLE.iter().find(|(n, _, _)| *n == k).copied(),
            E1_COMPACT_TABLE.iter().find(|(n, _)| *n == k).copied(),
        )
    };
    let (s2_first, e1_first) = geom(first);
    for k in &keys[1..] {
        let (s2, e1) = geom(k);
        if s2 != s2_first || e1 != e1_first {
            return Err(format!(
                "wide_registry_key_for_descriptor_name: '{display_name}' names >1 registry key \
                 ({first}, {k}) with DIFFERENT S2/E1 geometry — the column image is ambiguous; \
                 resolve the key at the call site"
            ));
        }
    }
    Ok(first)
}

pub fn append_wide_carriers(
    trace: &mut [Vec<BabyBear>],
    base_pis: Vec<BabyBear>,
    host_width: usize,
) -> Vec<BabyBear> {
    append_wide_carriers_avail(trace, base_pis, host_width, 0)
}

/// The AVAIL-AWARE generic wide widener (GAP #4, the wide leg of the availability weld):
/// [`append_wide_carriers`] for a base trace produced at a NONZERO availability pad. A hardened
/// `…-v1-avail` member lays its rotated BEFORE/AFTER limb blocks `avail_pad` past the bare layout
/// (`generate_rotated_effect_vm_trace_avail` — the pad shifts every appendix base), so the wide
/// carriers must RE-ABSORB the limbs at `BEFORE_BASE + avail_pad` / `AFTER_BASE + avail_pad`, and
/// the caller passes the member's avail-shifted HOST width (`GRAD_ROT_WIDTH + avail_pad` for the
/// transfer-shape cohort, `CAP_OPEN_TB_WIDTH + avail_pad` for the TB route). PI indices are
/// UNCHANGED (the pad shifts columns, never PIs). At `avail_pad = 0` byte-identical to the bare
/// widener.
pub fn append_wide_carriers_avail(
    trace: &mut [Vec<BabyBear>],
    base_pis: Vec<BabyBear>,
    host_width: usize,
    avail_pad: usize,
) -> Vec<BabyBear> {
    let cb_before = host_width;
    let cb_after = host_width + WIDE_NUM_CARRIERS * 8;
    let wide_width = host_width + 2 * WIDE_NUM_CARRIERS * 8;
    for row in trace.iter_mut() {
        row.resize(wide_width, BabyBear::ZERO);
        fill_wide_block(row, cb_before, BEFORE_BASE + avail_pad);
        fill_wide_block(row, cb_after, AFTER_BASE + avail_pad);
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
/// 46-PI rotated vector exactly as transfer does (no grow-gate root, no record pin); their wide
/// member is `wideAppend burn 187 238` (width `WIDE_WIDTH` / PI `WIDE_PI_COUNT`), the SAME carrier shape as transfer. This
/// wraps the LIVE base generator ([`generate_rotated_effect_vm_trace`], which proves any cohort
/// member's real turn) + the generic widener at `GRAD_ROT_WIDTH`. Returns `(trace, dpis)`.
pub fn generate_rotated_transfer_shape_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    generate_rotated_transfer_shape_wide_avail(0, initial_state, effects, before_w, after_w, caveat)
}

/// The AVAIL-AWARE transfer-shape wide generator (GAP #4, the wide leg): the base trace at the
/// availability pad ([`generate_rotated_effect_vm_trace_avail`] — witness limbs at
/// `[V1_WIDTH, V1_WIDTH + pad)`, every appendix base shifted) + the generic widener at the
/// avail-shifted host width (`GRAD_ROT_WIDTH + avail_pad`), limbs re-absorbed at the shifted
/// rotated bases. The wide dispatcher routes here with
/// [`avail_pad_for_descriptor_name`]`(&desc.name)` — a hardened `…-v1-avail` WIDE member (the
/// post-retarget `transferVmDescriptor2R24` row) gets the pad; every bare member takes pad 0
/// (byte-identical to the legacy path).
pub fn generate_rotated_transfer_shape_wide_avail(
    avail_pad: usize,
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) = generate_rotated_effect_vm_trace_avail(
        avail_pad,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
    )?;
    // The bare transfer-shape cohort carries `ROT_PI_COUNT + DFA_RC_LEN`; the setField family
    // additionally carries the VALUE8 completion block (the written slot's 7 published high-byte
    // lanes, PIs 46..=52, ahead of the rc tail — Lean `withSetFieldCompletionPins`). Both shapes take
    // the SAME wide append (the 16 anchors land at the end either way); anything else is a
    // grow-gate/record member that must not be widened here.
    let value8 = if matches!(effects.first(), Some(Effect::SetField { field_idx, .. }) if (*field_idx as usize) < 8)
    {
        crate::effect_vm_descriptors::SETFIELD_VALUE8_PI_LEN
    } else if matches!(effects.first(), Some(Effect::GrainTurn { .. })) {
        GRAIN_TURN_EXTRA_PIS
    } else {
        0
    };
    if base_pis.len() != ROT_PI_COUNT + value8 + DFA_RC_LEN {
        return Err(format!(
            "transfer-shape wide generator: base PI vector {} != {} (this wrapper is for the bare \
             transfer-shape cohort + the 4 dsl rc PIs, plus the setField VALUE8 block — a \
             grow-gate/record member carries an extra PI)",
            base_pis.len(),
            ROT_PI_COUNT + value8 + DFA_RC_LEN
        ));
    }
    let dpis =
        append_wide_carriers_avail(&mut trace, base_pis, GRAD_ROT_WIDTH + avail_pad, avail_pad);
    Ok((trace, dpis))
}

/// **THE WIDE RECORD-PIN trace generator (the record-pin cohort — setPermissions / setVK / cellSeal /
/// cellUnseal / cellDestroy / receiptArchive / refusal, `WIDE_WIDTH`-wide).** The base generator
/// ([`generate_rotated_effect_vm_trace`]) pushes the record/lifecycle pin as PI 38 for these leads (39
/// base PIs); this appends the wide carriers at `GRAD_ROT_WIDTH` (so the published 8-felt commit
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
    if base_len != ROT_PI_COUNT + 1 + DFA_RC_LEN && base_len != ROT_PI_COUNT + 8 + DFA_RC_LEN {
        return Err(format!(
            "record-pin wide generator: base PI vector {} is neither {} (single record/lifecycle pin \
             + the 4 dsl rc PIs) nor {} (the H1 8-felt authority record-pin8 + rc)",
            base_len,
            ROT_PI_COUNT + 1 + DFA_RC_LEN,
            ROT_PI_COUNT + 8 + DFA_RC_LEN
        ));
    }
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    debug_assert_eq!(dpis.len(), base_len + 16); // base record-pins + 16 wide commit carriers
    Ok((trace, dpis))
}

/// The sovereign KEY_COMMIT chip appendix span: 4 quads × 8 digest lanes (Lean
/// `CarrierOctetGates.KEY_COMMIT_SPAN` — the committed `makeSovereignV3DeployedWide` widens the
/// wide record-pin host by exactly these 32 columns, `1771 + 32 = 1803`).
pub const SOVEREIGN_KEY_COMMIT_SPAN: usize = 32;

/// **THE SOVEREIGN KEY_COMMIT PRODUCER RIDER** — lift a wide `MakeSovereign` record-pin trace/PI
/// pair (from [`generate_rotated_record_pin_wide`], 74 PIs / `WIDE_WIDTH` columns) to the
/// committed DEPLOYED keyed member (`CarrierComposed.makeSovereignV3DeployedWide`, 78 PIs /
/// `WIDE_WIDTH + 32` columns):
///
///   * the 4 KEY_COMMIT teeth columns (`columns.rs` `aux_off::WITNESS_KEY_COMMIT_0..3`, absolute
///     cols 113..=116 — dead-zero from `EffectVmContext::default` in the base trace) are filled
///     with the executor's compress of the committed BEFORE-block pubkey octet, on EVERY row
///     (the deployed edge holds them constant; the pin reads row 0);
///   * the 32-column chip-compress digest appendix (`dg_base = WIDE_WIDTH`, 4 quads × 8 lanes)
///     gets its lane-0 producer columns (`row[dg_base + 8·q] = kc[q]`; the prove wrapper's
///     `fill_chip_lanes` fills lanes 1..7 from the genuine permutation);
///   * the 4 teeth claim PIs are SPLICED ahead of the 16 wide anchors (`insert_at =
///     dpis.len() − 16` = the committed `SOVEREIGN_KEY_COMMIT_PI_LO`, post-rc-wrap).
///
/// The teeth values are DERIVED FROM THE COMMITTED TRACE, never caller-supplied:
/// `kc = key_commit_teeth_from_nonet(committed BEFORE-block pubkey NONET)`, i.e. the NINE columns
/// [`super::PUBKEY_NONET_LANE_COL`] names — lanes 0..7 at `B_PUBKEY_OCTET`, lane 8 at
/// `B_PUBKEY_NINTH_LANE`, all nine ABSORBED pre-limbs the operated cell's owner key fills. That
/// function is the ONE denotation `TurnExecutor::pubkey_to_witness_key_commit` also calls, and its
/// interleave matrix is generated from the AIR's own `CarrierOctetGates.quadIdx`, so the fill
/// satisfies the in-AIR chip gate AND matches the executor's check by construction — a producer
/// that committed a forged nonet gets teeth the executor refuses (the third edge stays
/// fail-closed).
///
/// ⚑ **2026-08-08.** This read the EIGHT octet columns through a hand-typed
/// `const QUAD_IDX = [[0,1,2,3],[4,5,6,7],[0,4,2,6],[1,5,3,7]]` and called
/// `dregg_commit::typed::canonical_32_to_felts_4` "the executor's function". Both halves were
/// false: `6441705e8` had already re-pointed that executor function at a single arity-16 nonet
/// absorb (so the two DISAGREED and `makeSovereign` no longer verified), and the octet cover left
/// lane 8 — an Ed25519 key's x-sign — out of every quad, so a key and its NEGATION published
/// identical teeth. The matrix is now emitted, not typed, and it covers all nine lanes.
pub fn append_sovereign_key_commit_rider(
    trace: &mut [Vec<BabyBear>],
    dpis: &mut Vec<BabyBear>,
) -> Result<(), String> {
    use super::columns::{AUX_BASE, aux_off};

    let dg_base = trace
        .first()
        .map(Vec::len)
        .ok_or_else(|| "sovereign key-commit rider: empty trace".to_string())?;
    if dg_base != WIDE_WIDTH {
        return Err(format!(
            "sovereign key-commit rider: trace width {dg_base} != the wide record-pin host \
             {WIDE_WIDTH} (the appendix lands past the wide carriers)"
        ));
    }
    if dpis.len() < 16 {
        return Err(format!(
            "sovereign key-commit rider: PI vector {} carries no 16-PI wide anchor tail",
            dpis.len()
        ));
    }
    // The committed BEFORE-block pubkey NONET. ⚠ NOT a stride and NOT `B_IROOT − 8`: lanes 0..7 sit
    // at `B_PUBKEY_OCTET` and lane 8 sits at `B_PUBKEY_NINTH_LANE`, 81 columns past the octet's end
    // and past the whole completion band. `PUBKEY_NONET_LANE_COL` is the Lean-emitted table that
    // says so; `[B_PUBKEY_OCTET + i; 9]` would silently read `fields[0]`'s completion window.
    let nonet: [BabyBear; 9] =
        std::array::from_fn(|i| trace[0][BEFORE_BASE + super::PUBKEY_NONET_LANE_COL[i]]);
    let kc: [BabyBear; 4] = super::key_commit_teeth_from_nonet(&nonet);

    let kc_col = AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0;
    for row in trace.iter_mut() {
        row.resize(dg_base + SOVEREIGN_KEY_COMMIT_SPAN, BabyBear::ZERO);
        for (k, v) in kc.iter().enumerate() {
            row[kc_col + k] = *v; // the KEY_COMMIT teeth (constant per row, row-0-pinned)
            row[dg_base + 8 * k] = *v; // quad k's digest lane 0 (the genuine producer column)
        }
    }

    // Splice the 4 teeth claim PIs ahead of the 16 wide anchors (the committed
    // `SOVEREIGN_KEY_COMMIT_PI_LO` on the wide record-pin vector).
    let insert_at = dpis.len() - 16;
    let mut spliced = Vec::with_capacity(dpis.len() + kc.len());
    spliced.extend_from_slice(&dpis[..insert_at]);
    spliced.extend_from_slice(&kc);
    spliced.extend_from_slice(&dpis[insert_at..]);
    *dpis = spliced;
    Ok(())
}

/// **THE WIDE FEE-IN-PROOF trace generator (`transferFeeVmDescriptor2R24Wide`, `WIDE_WIDTH`-wide).**
/// The wide twin of the fee-aware base generator ([`generate_rotated_effect_vm_trace_with_fee`]): it
/// debits the fee in-proof (so the rotated AFTER limbs carry the post-fee balance) and then appends
/// the BEFORE/AFTER `WIDE_NUM_CARRIERS`×8 wide carriers + 16 wide commit PIs at `GRAD_ROT_WIDTH`. Because
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
    generate_rotated_transfer_shape_with_fee_wide_avail(
        0,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        fee,
    )
}

/// The AVAIL-AWARE wide fee-in-proof generator (GAP #4, the wide FEE leg): the fee-aware base
/// trace at the availability pad ([`generate_rotated_effect_vm_trace_with_fee_avail`] — the
/// 16-col §11.8 fee weld witness at `[V1_WIDTH, V1_WIDTH + 16)`, every appendix base shifted,
/// the weld RE-LAID post-fee-surgery from the published fee) + the generic widener at the
/// avail-shifted host width (`GRAD_ROT_WIDTH + avail_pad`), limbs re-absorbed at the shifted
/// rotated bases. The SDK wide fee provers route here with
/// [`avail_pad_for_descriptor_name`]`(&desc.name)` — a hardened `…-v1-fee-avail` WIDE member
/// (the post-retarget `transferFeeVmDescriptor2R24` row) gets [`TRANSFER_FEE_AVAIL_PAD`];
/// every bare member takes pad 0 (byte-identical to the legacy path).
pub fn generate_rotated_transfer_shape_with_fee_wide_avail(
    avail_pad: usize,
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    fee: u64,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) = generate_rotated_effect_vm_trace_with_fee_avail(
        avail_pad,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        fee,
    )?;
    if base_pis.len() != ROT_PI_COUNT + 1 + DFA_RC_LEN {
        return Err(format!(
            "wide fee generator: base PI vector {} != {} (the fee descriptor carries the rotated \
             vector + the published fee at PI 46 + the 4 dsl rc PIs at 47..50)",
            base_pis.len(),
            ROT_PI_COUNT + 1 + DFA_RC_LEN
        ));
    }
    let dpis =
        append_wide_carriers_avail(&mut trace, base_pis, GRAD_ROT_WIDTH + avail_pad, avail_pad);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH + avail_pad);
    debug_assert_eq!(dpis.len(), WIDE_PI_COUNT + 1); // ROT_PI_COUNT + fee + 4 rc + 16 wide
    Ok((trace, dpis))
}

/// **THE WIDE BRIDGE-MINT trace generator (`mintVmDescriptor2R24` wide, 67-PI).** The bridge-mint
/// member carries the FELT mint-hash pin at PI `ROT_PI_COUNT` — the STEP-2/3 bridge-carrier
/// exposure (Lean `mintV3BridgeHash`; base 46 + mint_hash + 4 dsl rc = 51) — so it can no longer
/// ride the bare transfer shape. This appends the 16 wide commit PIs at `GRAD_ROT_WIDTH`:
/// `WIDE_PI_COUNT + 1`. The published PI `ROT_PI_COUNT` is the projector-derived
/// `note_spend_mint_hash_felt` (see the base generator's bridge-mint arm); the verifier's
/// reconstruction recomputes it from the turn's OWN `PortableNoteProof` via
/// `convert_turn_effects_to_vm`, so the anchor is executor-derived, never prover-supplied.
/// Returns `(trace, dpis)`.
pub fn generate_rotated_bridge_mint_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let (mut trace, base_pis) =
        generate_rotated_effect_vm_trace(initial_state, effects, before_w, after_w, caveat)?;
    if base_pis.len() != ROT_PI_COUNT + 1 + DFA_RC_LEN {
        return Err(format!(
            "bridge-mint wide generator: base PI vector {} != {} (the bridge-mint descriptor \
             carries the rotated vector + the felt mint-hash pin at PI 46 + the 4 dsl rc PIs at \
             47..50)",
            base_pis.len(),
            ROT_PI_COUNT + 1 + DFA_RC_LEN
        ));
    }
    let dpis = append_wide_carriers(&mut trace, base_pis, GRAD_ROT_WIDTH);
    debug_assert_eq!(trace[0].len(), WIDE_WIDTH);
    debug_assert_eq!(dpis.len(), WIDE_PI_COUNT + 1); // ROT_PI_COUNT + mint_hash + 4 rc + 16 wide
    Ok((trace, dpis))
}

/// **THE DECO/Stripe money-in DEPLOYED-LEG PRODUCER (`generate_rotated_stripe_mint_wide`).**
///
/// The 8th carrier's producer (`docs/deos/DECO-CARRIER-PLAN.md` §2, Step 1). A Stripe
/// money-in mint is minted through the SAME committed, PI-46-pinned mint row the bridge
/// carrier rides — `mintVmDescriptor2R24` (Lean `mintV3BridgeHash`) — because that row
/// ALREADY publishes the FIRST-row `param0` (`param::MINT_HASH`) at PI 46
/// ([`generate_rotated_bridge_mint_wide`], NON-VK). The ONLY difference from a bridge
/// mint is the FELT the row publishes: for DECO it is the FELT-DOMAIN payment identity
/// [`crate::dsl::deco_payment::deco_payment_hash_felt`] over the `PaymentFacts` (the
/// executor writes the SAME felt to [`VerifiedPayment::payment_hash`]), NOT the
/// note-spend identity. The DECO fold arm dispatches on `CarrierWitness::Deco` (not
/// `Bridge`), so the DECO commitment leaf — NOT the note-spend leaf — recomputes this
/// felt IN-AIR and the fold's `connect` binds them; a Stripe payment identity no
/// verifying DECO commitment backs is UNSAT.
///
/// This shares the pinned mint descriptor with bridge by design: PI 46 is the ONE
/// mint-identity lane a mint row publishes (`DECO_PAYMENT_HASH_PI == BRIDGE_MINT_HASH_PI
/// == 46`), and the carrier is distinguished by the witness/leaf, not the deployed
/// descriptor — so the Stripe path goes light-client-live with NO descriptor/VK change.
/// `payment_hash` MUST be the felt-domain [`crate::dsl::deco_payment::deco_payment_hash_felt`]
/// (the anti-vacuity law), never the executor's byte-domain BLAKE3 `payment_nullifier`.
pub fn generate_rotated_stripe_mint_wide(
    initial_state: &CellState,
    value_full: u64,
    payment_hash: BabyBear,
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let value_lo_u = value_full & ((1u64 << 30) - 1);
    // The pinned mint row: `param0` carries the felt payment identity (the DECO leaf's
    // in-AIR-recomputed anchor), exactly as bridge's `param0` carries its note-spend
    // identity. Both ride `mintVmDescriptor2R24` — the carrier is the witness, not the row.
    let effects = vec![Effect::BridgeMint {
        value_lo: BabyBear::new(value_lo_u as u32),
        mint_hash: payment_hash,
        value_full,
    }];
    let (trace, dpis) =
        generate_rotated_bridge_mint_wide(initial_state, &effects, before_w, after_w, caveat)?;
    debug_assert_eq!(
        dpis[ROT_PI_COUNT], payment_hash,
        "the deployed stripeMint leg publishes the felt payment identity at PI 46 (param0)"
    );
    Ok((trace, dpis))
}

/// The host (pre-wide-append) width of the `heapWriteVmDescriptor2R24` descriptor. OPTION I: the
/// DEPLOYED host is the after-spine membership-forcing `effHeapWriteV3 heapWriteV3` (Lean
/// `HeapOpenEmit.effHeapWriteV3`), EXACTLY as cap deploys `effCapOpenWriteV3` — the Class-A splice base
/// (`heapWriteV3`, **815** wide) WIDENED by the heap-open READ appendix (`CAP_OPEN_SPAN = 329`) + the
/// AFTER-spine appendix (`AFTER_SPINE_SPAN = 143`): `815 + 329 + 143 = 1287`. A satisfying trace FORCES
/// the faithful 8-felt heap-write over the full ~124-bit BEFORE/AFTER root blocks
/// (`effHeapWriteV3_forces_write8`) — never the lane-0 squeeze the map_op-only host would leave. The
/// wide carriers land at THIS host width.
pub const HEAP_WRITE_HOST_WIDTH: usize =
    (GRAD_ROT_WIDTH - HEAP_BASE_NARROWING) + CAP_OPEN_SPAN + CAP_OPEN_AFTER_SPINE_SPAN; // 2098 = 1626 + 329 + 143
/// How many columns the graduated Class-A heap base is NARROWER than the rotated cohort base:
/// `7 × (cohort graduated constraints − heapWrite's)`, because `graduateV1` gives every graduated
/// constraint its own 7-column chip-lane block. **It was 14 (two blocks) until 2026-07-26, when the
/// arity-2 leaf vestige `EffectVmEmitHeapRoot.siteHeapLeaf` was deleted from the emit and took a third
/// block with it** — the narrow committed member went `trace_width 1633 → 1626`. This is the one
/// producer-side number the deletion did not move on its own; `heap_write_roundtrip.rs` asserts
/// producer width == committed descriptor width, so a stale value here REDs there rather than laying
/// the membership appendix against the wrong columns.
const HEAP_BASE_NARROWING: usize = 21;
// NB: the READ appendix base is `HEAP_WRITE_HOST_WIDTH − CAP_OPEN_SPAN − AFTER_SPINE_SPAN`
// (the graduated Class-A heap base); see [`HEAP_WRITE_READ_BASE`] below.
/// The heap-open READ appendix base column (the splice base `heapWriteV3`'s trace width = the
/// graduated Class-A heap base, `GRAD_ROT_WIDTH − HEAP_BASE_NARROWING`): `HEAP_WRITE_HOST_WIDTH −
/// CAP_OPEN_SPAN(329) − AFTER_SPINE_SPAN(143) = 2098 − 472 = 1626`. Derived, so it tracks the
/// graduated base. (Historically a too-low literal here laid the membership columns against
/// zero-padding and the deployed after-spine constraints rejected.)
pub const HEAP_WRITE_READ_BASE: usize =
    HEAP_WRITE_HOST_WIDTH - CAP_OPEN_SPAN - CAP_OPEN_AFTER_SPINE_SPAN;

/// **THE WIDE HEAP-WRITE trace generator (`heapWriteVmDescriptor2R24` wide member, 1183-wide / 20-PI).**
///
/// heapWrite is the Class-A heap-root-recompute member (Lean `RotatedKernelRefinementExercise.heapWriteV3`
/// = `graduateV1 (rotateV3 heapWriteSpliceVmDescriptor)` ++ the 8-felt `.write` splice `MapOp`). It rides
/// the SAME rotated block as every cohort member, plus a genuine sorted-Merkle SPLICE on the FAITHFUL
/// 8-felt heap root: the in-row `HEAP_ADDR` recompute (`col 102 = chip-absorb(coll, key)`) keys a `.write`
/// `MapOp` that opens the committed BEFORE heap-root GROUP (cols `216 ‖ 246..252` — lane 0 = limb 28,
/// lanes 1..7 = completion limbs 59..65) at that address for the written value (`col 72`) and FORCES the
/// AFTER heap-root GROUP (cols `307 ‖ 337..343`) to the genuine 8-felt `CanonicalHeapTree8` update. There
/// is NO live `Effect::HeapWrite` selector (the descriptor is reached by the exercise-inner heap-write
/// path, NOT the effect→descriptor resolvers), so this is the per-family wide PRODUCER for it — exactly
/// mirroring the supplyMint wide producer (live base + the generic [`append_wide_carriers`] at the
/// member's host width), preserving the 8-felt before/after anchors.
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
    let (mut trace, dpis, map_heaps) = generate_rotated_heap_write_wide_raw(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        coll,
        key,
        value,
        heap_leaves,
    )?;
    compact_s2_columns(&mut trace, "heapWriteVmDescriptor2R24")?;
    compact_e1_columns(&mut trace, "heapWriteVmDescriptor2R24")?;
    Ok((trace, dpis, map_heaps))
}

/// **THE PRE-COMPACTION STAGE of [`generate_rotated_heap_write_wide`]** — the assembled RAW wide row
/// (`HEAP_WRITE_HOST_WIDTH + WIDE_CARRIER_APPENDIX` = the OPTION-I after-spine host + wide carriers),
/// *before* the two Epoch flag-day deletions the deployed producer applies. Identical body; the
/// deployed entry above is exactly this plus `compact_s2_columns ∘ compact_e1_columns`, so the emitted
/// (compacted) trace is byte-unchanged.
///
/// **Why it is exposed.** An ADVERSARIAL tooth on this member has to build its forgery at the RAW
/// rotated coordinates and then carry it through the SAME compaction as the honest row — the S2 band
/// `[bb+418, bb+478)` deletes the AFTER block's whole 1-felt chain-carrier stratum, so on a compacted
/// row there is nothing left to recompute a patched AFTER block-commit into, and the wide carriers no
/// longer sit at `HEAP_WRITE_HOST_WIDTH`. A tooth that patches the compacted row and re-runs
/// [`append_wide_carriers`] re-inflates it to the raw width, and the prover then refuses on SHAPE
/// (`base row width 3058 must equal descriptor trace_width 1955`) — a refusal the tooth reads as an
/// unsat verdict while the forgery was never examined. `circuit/tests/heap_write_roundtrip.rs` pins
/// that the two entries agree byte-for-byte, so this accessor cannot drift from what deploys.
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_heap_write_wide_raw(
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
    use crate::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};

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
    // NB: there is NO second (leaf-digest) chip lookup to fill any more. The arity-2
    // `col 103 = chip-absorb(addr, value)` site was DELETED from the Lean emit on 2026-07-26
    // (`EffectVmEmitHeapRoot` §8: it committed a retired arity-2 leaf shape that no deployed tree folds,
    // and nothing read its column). Rust CALLS the emission, so the fill goes with it. The leaf that
    // authenticates against the committed root is the arity-3 IMT leaf laid at native 8-felt width by
    // `fill_heap_open_read` / `fill_heap_after_spine` below.

    // The BEFORE heap (the deployed openable sorted tree) at NATIVE 8-FELT width. The addressed key MUST
    // be present — the splice `.write` is an UPDATE of a present key (8-felt `update_witness`); a missing
    // key fails closed (no fabricated post-root). We thread the faithful 8-felt roots (before = `root8`,
    // after = the update witness's recomposed `new_root`), NOT the lossy 1-felt scalar the GENTIAN tooth
    // refutes.
    let before_tree = CanonicalHeapTree8::new(heap_leaves.to_vec(), HEAP_TREE_DEPTH);
    let before_root8 = before_tree.root8();
    if !before_tree.sorted_leaves().iter().any(|l| l.addr == addr) {
        return Err(format!(
            "heap-write wide: recomputed addr {} is NOT in the BEFORE heap — the splice `.write` opens a \
             present key and has no membership witness, so it refuses the turn (no silent forge)",
            addr.as_u32()
        ));
    }
    let update = before_tree
        .update_witness(HeapLeaf::entry(addr, value))
        .ok_or_else(|| {
            format!(
                "heap-write wide: 8-felt update witness for addr {} failed",
                addr.as_u32()
            )
        })?;
    let after_root8: [BabyBear; HEAP_DIGEST_W] = update.new_root;
    // The 8-felt membership path (siblings + directions) the DEPLOYED after-spine descriptor
    // (`effHeapWriteV3`, OPTION I) opens: `update_witness` recomposes the AFTER root over the SAME
    // sibling path, so the before-open (OLD leaf) and after-open (UPDATED leaf) share `(siblings,
    // directions)` — exactly the keystone `heapOpen_writesTo8`'s `hsib`/`hdir`.
    let heap_siblings: Vec<[BabyBear; HEAP_DIGEST_W]> = update.siblings.clone();
    let heap_directions: Vec<u8> = update.directions.clone();
    if heap_siblings.len() != HEAP_TREE_DEPTH || heap_directions.len() != HEAP_TREE_DEPTH {
        return Err(format!(
            "heap-write wide: membership path length {}/{} != depth {HEAP_TREE_DEPTH}",
            heap_siblings.len(),
            heap_directions.len()
        ));
    }
    // The OLD value at the addressed key (the read-leaf value the before-open authenticates).
    let _old_value = before_tree
        .sorted_leaves()
        .iter()
        .find(|l| l.addr == addr)
        .map(|l| l.value)
        .ok_or_else(|| "heap-write wide: BEFORE leaf vanished".to_string())?;

    // Write the FAITHFUL 8-felt heap root into the HEAP GROUP of both rotated blocks — lane 0 the
    // scalar heap-root limb (`B_HEAP_ROOT = 28`), lanes 1..7 the completion limbs 59..65 (the Lean
    // `heapRootGroupCol`: `BEFORE_BASE + 28` / `BEFORE_BASE + 59..65` = cols 216 + 247..253; `AFTER_BASE
    // + 28` / `+ 59..65` = cols 307 + 338..344 — EXACTLY the map-op `.write` root/newRoot groups). This
    // REPLACES the old (wrong) scalar override of the cap limb (`BEFORE_BASE + B_CAP_ROOT`, col 213) —
    // the heap root has its OWN group and never rides the cap register. The v1-state `cap_root` cols
    // (65/87) and the cap rotated limbs (213/304) are LEFT UNTOUCHED (the base gen lays a consistent cap
    // block; the `213 == 65` weld holds).
    let heap_group_col =
        |block_base: usize, lane: usize| -> usize { block_base + HEAP_ROOT_GROUP[lane] };
    let coll_col = PARAM_BASE + 2; // 70 (HEAP_ADDR recompute input: collection)
    let key_col = PARAM_BASE + 3; // 71 (HEAP_ADDR recompute input: key)
    let value_col = PARAM_BASE + 4; // 72 (HEAP_VALUE — the map-op `.write` value column)
    // The HEAP_ADDR column (102) is the splice `MapOp`'s KEY. It is ALSO the output of the in-row
    // arity-2 chip lookup `col 102 = chip-absorb(coll, key)`, which `fill_chip_lanes` lands at prove
    // time — but the map-op pre-flight replay reads col 102 from the RAW trace (BEFORE lane-fill), so
    // we set it explicitly to the recomputed `addr`. `fill_chip_lanes` then re-lands the SAME value
    // (the addr lookup is chip-faithful over the same coll/key), so the lookup gate holds.
    let heap_addr_col = AUX_BASE + 12; // 102 (HEAP_ADDR — out0 of the addr chip lookup)
    // `AUX_BASE + 13` (col 103) is the RETIRED leaf-digest carrier and is deliberately left at zero: the
    // arity-2 lookup that drove it is gone from the emitted bytes (2026-07-26 flag-day), so laying a
    // value there would be a producer writing into a column no constraint mentions. The absence is
    // pinned by `circuit/tests/heap_write_deployed_root_forced.rs`.
    // OPTION I: the deployed host is the after-spine membership descriptor — the heap-open READ appendix
    // sits at `HEAP_WRITE_READ_BASE` (815, the splice base's width) and the AFTER-spine appendix at
    // `815 + CAP_OPEN_SPAN(329) = 1144`. Fill both on EVERY row (the membership gates are per-row).
    let read_base = HEAP_WRITE_READ_BASE; // 815
    let after_spine_base = read_base + CAP_OPEN_SPAN; // 1144
    // The committed BEFORE leaf (carries the IMT next_addr pointer); the value update holds the
    // pointer fixed, so the after-spine UPDATED leaf shares it.
    let read_leaf = update.old_leaf;
    let heap_next = update.old_leaf.next_addr;
    for row in trace.iter_mut() {
        // FAITHFUL 8-felt before/after heap-root groups (never the lane-0 scalar squeeze).
        for lane in 0..HEAP_DIGEST_W {
            row[heap_group_col(BEFORE_BASE, lane)] = before_root8[lane];
            row[heap_group_col(AFTER_BASE, lane)] = after_root8[lane];
        }
        row[coll_col] = coll;
        row[key_col] = key;
        row[value_col] = value;
        row[heap_addr_col] = addr;
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
        // Grow the row to the deployed host width and lay the membership appendix (the READ open of the
        // OLD leaf against the BEFORE root8, and the after-spine open of the UPDATED leaf against the
        // AFTER root8, over the SHARED sibling path).
        row.resize(HEAP_WRITE_HOST_WIDTH, BabyBear::ZERO);
        fill_heap_open_read(
            row,
            read_base,
            read_leaf,
            &heap_siblings,
            &heap_directions,
            before_root8.limbs(),
        );
        fill_heap_after_spine(
            row,
            after_spine_base,
            addr,
            value,
            heap_next,
            &heap_siblings,
            &heap_directions,
        );
    }

    // The 4 heapWrite base PIs. pi 0 = the rotated OLD state-commit (UNBOUND in the wide descriptor —
    // the 8-felt before-commit is the faithful binding — but read the genuine value for Fiat–Shamir
    // agreement); pi 1 = the rotated NEW state-commit (`AFTER_BASE + B_STATE_COMMIT` = col 347, BOUND on
    // the last row); pi 2 = committed height; pi 3 = caveat commit. Read all from the rebuilt trace so
    // the last-row pins hold after the heap-root override + `recompute_block_commit`.
    let last_row_idx = trace.len() - 1;
    let base_pis = vec![
        trace[0][BEFORE_BASE + B_STATE_COMMIT],
        trace[last_row_idx][AFTER_BASE + B_STATE_COMMIT],
        gen_pis[V1_PI_COUNT + 2],
        gen_pis[V1_PI_COUNT + 3],
    ];
    let dpis = append_wide_carriers(&mut trace, base_pis, HEAP_WRITE_HOST_WIDTH);
    debug_assert_eq!(
        trace[0].len(),
        HEAP_WRITE_HOST_WIDTH + 2 * WIDE_NUM_CARRIERS * 8
    ); // 3058 (HEAP_WRITE_HOST_WIDTH 2098 + WIDE_CARRIER_APPENDIX 960 — OPTION I after-spine host)
    debug_assert_eq!(dpis.len(), 20); // 4 base (2 retired) + 16 wide
    Ok((trace, dpis, vec![heap_leaves.to_vec()]))
}

/// **THE WIDE TURN-BOUND CAP-OPEN trace generator (`transferCapOpenTBVmDescriptor2R24` wide member).**
///
/// The wide twin of the #225 turn-identity weld (Lean `CapOpenTurnPins.effCapOpenV3TB`): it builds the
/// LIVE rotated transfer base, widens it to the turn-bound cap-open shape ([`widen_to_cap_open_tb_avail`]
/// — the cap-membership columns; the TB weld adds NO column of its own), publishes the 47-PI
/// turn-bound vector ([`cap_open_tb_dpis`]: 46 rotated + `src` at 46), and then
/// appends the BEFORE/AFTER `WIDE_NUM_CARRIERS`×8 wide carriers + 16 wide commit PIs at the
/// cap-open-TB host width. The cap-membership host columns, the turn-identity pin, and the live
/// 1-felt carriers are CARRIED UNCHANGED — the wide append is purely additive, preserving the 8-felt
/// before/after anchors. The verifier ANCHORS the turn-identity PI to the trusted turn
/// ([`anchor_cap_open_turn_pins`]) exactly as on the narrow path; a forged published `src` is UNSAT.
///
/// THE FACE IS THE COMMITTED MEMBER'S, NOT THE BARE ONE. `transferCapOpenTBVmDescriptor2R24` is
/// emitted at the AVAIL-HARDENED transfer v1 face (`dregg-effectvm-transfer-v1-avail-…-capopen-eff-tb`,
/// S2 block base 198 = `V1_WIDTH + TRANSFER_AVAIL_PAD`), so the whole stack — base trace, cap-open
/// widen, turn-identity columns, wide-carrier host, re-absorbed limb bases — rides that pad, read off
/// the committed registry by [`wide_member_avail_pad`]. Laying the BARE face here and compacting at the
/// member's avail-shifted bands is the avail-shift trap: the same column count out of the wrong bands,
/// which leaves the honest proof UNSAT (`p3: constraints not satisfied on row 0`) with nothing to point
/// at. This mirrors the live SDK cap-open route (`sdk::full_turn_proof`, which derives the same pad from
/// the resolved descriptor's name).
///
/// `cap_open` MUST be a genuine transfer-conferring cap-membership witness whose leaf `target` IS the
/// turn's `src` (the `targetBind` gate roots it). Returns `(trace, dpis)` ready for `prove_vm_descriptor2(&desc,
/// &trace, &dpis, &MemBoundaryWitness::default(), &[])` against the wide `transferCapOpenTBVmDescriptor2R24`.
///
/// ⚑ 2026-07-31: the `actor`/`dst` arguments are GONE. They fed two columns and two PI slots this
/// member no longer carries; see [`CAP_OPEN_TB_WIDTH`].
#[allow(clippy::too_many_arguments)]
pub fn generate_rotated_transfer_cap_open_tb_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    cap_open: &CapOpenWitness,
    src: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    const TB_KEY: &str = "transferCapOpenTBVmDescriptor2R24";
    // The committed member's v1 face, read off its own registry name and cross-checked against its S2
    // block base (refuses rather than mis-compacting; see `wide_member_avail_pad`).
    let avail_pad = wide_member_avail_pad(TB_KEY)?;
    let (mut trace, base_pis) = generate_rotated_effect_vm_trace_avail(
        avail_pad,
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
    )?;
    if base_pis.len() != ROT_PI_COUNT + DFA_RC_LEN {
        return Err(format!(
            "cap-open-TB wide generator: base PI vector {} != {} (the base generator emits the \
             rotated 46 + the 4 dsl rc PIs; the TB descriptor is UNWRAPPED, so `cap_open_tb_dpis` \
             strips the rc tail and appends the ONE turn-identity PI at 46)",
            base_pis.len(),
            ROT_PI_COUNT + DFA_RC_LEN
        ));
    }
    widen_to_cap_open_tb_avail(&mut trace, cap_open, avail_pad)
        .map_err(|e| format!("cap-open-TB wide widen: {e}"))?;
    let tb_pis = cap_open_tb_dpis(&base_pis, src);
    debug_assert_eq!(tb_pis.len(), CAP_OPEN_TB_PI_COUNT); // 47
    let dpis =
        append_wide_carriers_avail(&mut trace, tb_pis, CAP_OPEN_TB_WIDTH + avail_pad, avail_pad);
    debug_assert_eq!(
        trace[0].len(),
        CAP_OPEN_TB_WIDTH + avail_pad + 2 * WIDE_NUM_CARRIERS * 8
    );
    debug_assert_eq!(dpis.len(), CAP_OPEN_TB_PI_COUNT + 16); // 63
    compact_s2_columns(&mut trace, TB_KEY)?;
    compact_e1_columns(&mut trace, TB_KEY)?;
    Ok((trace, dpis))
}

/// The §J′ INSERT-shaped accumulator host geometry (the DEPLOYED `effAccumInsertV3 … baseV3 …`): the
/// `effHeapOpenV3` heap-open READ appendix sits at the base descriptor's width (`GRAD_ROT_WIDTH`, where
/// `graduateV1` ends), spanning `CAP_OPEN_SPAN` columns, so the insert host is `GRAD_ROT_WIDTH +
/// CAP_OPEN_SPAN` wide (the wide member is `+480` on top). Matches the Lean `effAccumInsertV3 =
/// effHeapOpenV3 base ++ accumInsertConstraints` (the weld/bind gates add no columns).
pub const ACCUM_INSERT_READ_BASE: usize = GRAD_ROT_WIDTH;
pub const ACCUM_INSERT_HOST_WIDTH: usize = GRAD_ROT_WIDTH + CAP_OPEN_SPAN;

/// **`lay_accum_insert_read_appendix`** — lay the §J′ `effAccumInsertV3` heap-open READ appendix on every
/// row of a grow-gate wide trace. Opens the spliced `(key, value)` leaf against the AFTER accumulator
/// root over the after-membership path, so a `Satisfied2` of the deployed insert descriptor TRACE-FORCES
/// `MembersAt8 afterRoot (key, value)`. The read's `capRoot` group lands `= new_root`, which the
/// descriptor's `afterGroupWeldsI` gates weld to the AFTER accumulator block the tree generator already
/// laid; the read leaf's `(addr, value)` IS `(key, value)`, satisfying the KEY / VALUE bind gates.
///
/// `aafi` selects the AFTER-root lineage to MATCH what the narrow tree generator committed:
///   * `aafi = true` (noteSpend limb 26 / noteCreate limb 27, F1-flipped, op=4): open the appended leaf
///     at its `free_index` over the PATH2 free-slot membership (`AafiInsertWitness8::new_leaf_membership`)
///     against the APPEND-AT-FREE-INDEX `insert_witness_aafi().new_root`.
///   * `aafi = false` (createCell accounts limb 0, op=3): open the sorted spliced leaf over the sorted
///     `insert_witness` after-membership path against the SORTED-compacted rebuilt root (the accounts
///     narrow producer has NOT been flipped to AAFI — a separate lane).
///
/// `before_leaves` is the BEFORE accumulator leaf-set (the SAME set threaded into the tree generator, so
/// `new_root` matches the AFTER block). The key MUST be FRESH (and in-gap for AAFI) — else the witness
/// refuses (fail closed, no fabricated post-root). Grows each row to [`ACCUM_INSERT_HOST_WIDTH`].
fn lay_accum_insert_read_appendix(
    trace: &mut [Vec<BabyBear>],
    before_leaves: &[crate::heap_root::HeapLeaf],
    key_col: usize,
    value_col: usize,
    gated: bool,
    aafi: bool,
) -> Result<(), String> {
    use crate::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};
    // The spliced leaf's `(key, value)` are read from the descriptor's KEY / VALUE param columns on the
    // active spend row (row 0). The read appendix's `(addr, value)` IS `(key, value)`, so the KEY/VALUE
    // bind gates hold on the active row. Two regimes:
    //   * `gated = false` (noteCreate / createCell): the bind gates are UNCONDITIONAL `eqGate`s, so the
    //     key/value param columns are held CONSTANT across ALL rows (mirroring
    //     `generate_rotated_heap_write_wide`). Those families' base economics do not force the value
    //     column to `0` off-row, so a constant write is consistent.
    //   * `gated = true` (noteSpend): the bind gates are SELECTOR-GATED (`sel::NOTE_SPEND · (leaf −
    //     col)`), VACUOUS on padding (`sel = 0`). The base noteSpend economics force `NOTE_VALUE_LO = 0`
    //     on non-spend rows, so we must LEAVE the base key/value columns untouched (0 on padding); the
    //     active row already carries the real key/value from the tree generator, satisfying the ACTIVE
    //     bind. The UNCONDITIONAL after-root membership weld is laid on every row regardless (below).
    // (Param columns are OFF the commitment chain, so this does not disturb the block commits the tree
    // generator already recomputed.)
    let key = trace[0][key_col];
    let value = trace[0][value_col];
    let before_tree = CanonicalHeapTree8::new(before_leaves.to_vec(), HEAP_TREE_DEPTH);
    // The read appendix must open the spliced leaf against the SAME AFTER accumulator root the narrow
    // tree generator committed into the rotated block — otherwise the descriptor's `afterGroupWeldsI`
    // gate (capRoot == committed AFTER limb) fights the trace. Two lineages, keyed by `aafi`:
    //   * `aafi = true`  (noteSpend limb 26 / noteCreate limb 27): F1 flipped these narrow producers to
    //     commit `insert_witness_aafi().new_root` (the APPEND-AT-FREE-INDEX fold, op=4). The appended
    //     leaf opens at its `free_index` over the PATH2 free-slot membership against that AAFI root.
    //   * `aafi = false` (createCell accounts limb 0): the accounts narrow producer still commits the
    //     SORTED-compacted `insert_witness().new_root` (op=3), so the read appendix opens the sorted
    //     spliced leaf against the sorted rebuilt root. (Flipping accounts to AAFI is a SEPARATE lane —
    //     its narrow producer has not been flipped, so forcing AAFI here would break the weld.)
    // A present / out-of-gap key has NO witness on either lineage ⇒ fail closed, no fabricated post-root.
    let (read_leaf, siblings, directions, new_root): (
        HeapLeaf,
        Vec<[BabyBear; HEAP_DIGEST_W]>,
        Vec<u8>,
        [BabyBear; HEAP_DIGEST_W],
    ) = if aafi {
        let w = before_tree
            .insert_witness_aafi(HeapLeaf::entry(key, value))
            .ok_or_else(|| {
                format!(
                    "accum insert wide: 8-felt insert_witness_aafi for the fresh key {} failed (key \
                     already present in the BEFORE accumulator, a sentinel, or out of the bracketing \
                     low leaf's pointer gap) — the AAFI insert refuses (fail closed, no fabricated \
                     post-root)",
                    key.as_u32()
                )
            })?;
        // The appended leaf's PATH2 free-slot membership against the append-ordered AAFI `new_root`.
        let (siblings, directions) = w.new_leaf_membership(HEAP_TREE_DEPTH);
        (w.new_leaf, siblings, directions, w.new_root)
    } else {
        let w = before_tree
            .insert_witness(HeapLeaf::entry(key, value))
            .ok_or_else(|| {
                format!(
                    "accum insert wide: 8-felt insert_witness for the fresh key {} failed (key \
                     already present in the BEFORE accumulator, or a sentinel) — the sorted insert \
                     refuses (fail closed, no fabricated post-root)",
                    key.as_u32()
                )
            })?;
        (w.new_leaf, w.siblings, w.directions, w.new_root)
    };
    if siblings.len() != HEAP_TREE_DEPTH || directions.len() != HEAP_TREE_DEPTH {
        return Err(format!(
            "accum insert wide: after-membership path length {}/{} != depth {HEAP_TREE_DEPTH}",
            siblings.len(),
            directions.len()
        ));
    }
    for row in trace.iter_mut() {
        // Ungated families pin the key/value columns constant on every row; the selector-gated
        // noteSpend leaves them as the base generator laid them (real on the active row, 0 on padding),
        // so the gated bind is satisfied on the active row and vacuous (never violated) on padding.
        if !gated {
            row[key_col] = key;
            row[value_col] = value;
        }
        row.resize(ACCUM_INSERT_HOST_WIDTH, BabyBear::ZERO);
        fill_heap_open_read(
            row,
            ACCUM_INSERT_READ_BASE,
            read_leaf,
            &siblings,
            &directions,
            new_root,
        );
    }
    Ok(())
}

/// **THE WIDE NOTESPEND trace generator (grow-gate cohort, §J′ INSERT-shaped deploy).** Wraps the
/// deployment-real nullifier-tree generator ([`generate_rotated_note_spend_trace_with_nullifier_tree`],
/// which overrides limb 26 with the openable accumulator roots + recomputes the block commits), lays the
/// `effAccumInsertV3` heap-open READ appendix (the spliced nullifier leaf opening against the AFTER
/// nullifier root over the `insert_witness` after-membership path — the deployed insert host), then
/// appends the wide carriers at [`ACCUM_INSERT_HOST_WIDTH`]. Returns `(trace, dpis, map_heaps)`.
pub fn generate_rotated_note_spend_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_nullifiers: &[crate::heap_root::HeapLeaf],
    revocation: &SpendRevocationWitness<'_>,
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    let (mut trace, base_pis, map_heaps) = generate_rotated_note_spend_trace_with_nullifier_tree(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_nullifiers,
        revocation,
    )?;
    // §J′: the nullifier key rides param slot 0 (`NULLIFIER_PARAM_COL = prmCol 0`), value slot 1
    // (`prmCol NOTE_VALUE_LO`) — the SAME columns the tree generator reads. Lay the insert read appendix.
    lay_accum_insert_read_appendix(
        &mut trace,
        before_nullifiers,
        PARAM_BASE + param::NULLIFIER,
        PARAM_BASE + param::NOTE_VALUE_LO,
        true, // selector-gated: base noteSpend forces NOTE_VALUE_LO=0 off-row; gate the value bind
        true, // AAFI: F1 flipped the nullifier narrow producer (limb 26) to insert_witness_aafi (op=4)
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, ACCUM_INSERT_HOST_WIDTH);
    Ok((trace, dpis, map_heaps))
}

/// **THE WIDE NOTECREATE trace generator (grow-gate cohort).** Wraps the commitments-tree generator
/// ([`generate_rotated_note_create_trace_with_commitments_tree`], limb-27 override + recompute), then
/// appends the wide carriers at `GRAD_ROT_WIDTH` (wide member width `WIDE_WIDTH`).
pub fn generate_rotated_note_create_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_commitments: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    let (mut trace, base_pis, map_heaps) =
        generate_rotated_note_create_trace_with_commitments_tree(
            initial_state,
            effects,
            before_w,
            after_w,
            caveat,
            before_commitments,
        )?;
    // §J′: the commitment key rides param slot 0 (`COMMITMENT_KEY_PARAM_COL = prmCol 0`), value slot 1.
    lay_accum_insert_read_appendix(
        &mut trace,
        before_commitments,
        PARAM_BASE + param::NULLIFIER,
        PARAM_BASE + param::NOTE_VALUE_LO,
        false, // unconditional bind: noteCreate economics do not force the value column to 0 off-row
        true, // AAFI: F1 flipped the commitments narrow producer (limb 27) to insert_witness_aafi (op=4)
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, ACCUM_INSERT_HOST_WIDTH);
    Ok((trace, dpis, map_heaps))
}

/// **THE BARE accounts-grow wide trace (NO §J′ insert appendix).** factory / spawn ride THIS: their wide
/// descriptors (`factoryVmDescriptor2R24` / `spawnVmDescriptor2R24`) stay BARE — only createCell (tag 17)
/// is deployed as the §J′ `effAccumInsertV3` insert host. The shared accounts-tree generator (limb-0
/// override + recompute) + wide carriers at `GRAD_ROT_WIDTH`. Returns `(trace, dpis, map_heaps)`.
fn generate_rotated_accounts_grow_wide_bare(
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

/// **THE WIDE CREATECELL trace generator (grow-gate cohort, §J′ INSERT-shaped deploy).** Wraps the
/// accounts-tree generator ([`generate_rotated_create_cell_trace_with_accounts_tree`], limb-0 override +
/// recompute), lays the `effAccumInsertV3` accounts-insert READ appendix (the born cell id opening
/// against the AFTER cells root over the `insert_witness` after-membership path — the deployed insert
/// host), then appends the wide carriers at [`ACCUM_INSERT_HOST_WIDTH`]. factory / spawn route through
/// [`generate_rotated_accounts_grow_wide_bare`] instead (their descriptors stay bare).
pub fn generate_rotated_create_cell_wide(
    initial_state: &CellState,
    effects: &[Effect],
    before_w: &RotatedBlockWitness,
    after_w: &RotatedBlockWitness,
    caveat: &RotatedCaveatManifest,
    before_accounts: &[crate::heap_root::HeapLeaf],
) -> RotatedTraceWithHeaps {
    use super::columns::{PARAM_BASE, param};
    let (mut trace, base_pis, map_heaps) = generate_rotated_create_cell_trace_with_accounts_tree(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_accounts,
    )?;
    // §J′: the new-cell key rides param slot 0 (`NEW_CELL_KEY_PARAM_COL = prmCol 0`), and IS its own leaf
    // value (a born-empty cell — the descriptor's valueCol = keyCol). Lay the accounts insert appendix.
    lay_accum_insert_read_appendix(
        &mut trace,
        before_accounts,
        PARAM_BASE + param::NULLIFIER,
        PARAM_BASE + param::NULLIFIER,
        false, // unconditional bind: createCell births an empty cell (valueCol = keyCol), consistent off-row
        true, // AAFI: gap-#6 flipped the accounts narrow producer (limb 0) to insert_witness_aafi (op=4)
    )?;
    let dpis = append_wide_carriers(&mut trace, base_pis, ACCUM_INSERT_HOST_WIDTH);
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
    generate_rotated_accounts_grow_wide_bare(
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
    generate_rotated_accounts_grow_wide_bare(
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
/// `GRAD_ROT_WIDTH`. The refusal lead carries the extra record/lifecycle pin before
/// the 16 wide PIs — the SAME base+16-wide geometry the record-pin
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
    before_fields_leaves: &[crate::openable_fields_root::ExactFieldsLeaf],
    audit_value: [u8; 32],
) -> RotatedTraceWithHeaps {
    generate_rotated_refusal_write_wide(
        initial_state,
        effects,
        before_w,
        after_w,
        caveat,
        before_fields_leaves,
        audit_value,
    )
}

// ============================================================================
// setFieldDyn — the DYNAMIC overflow-field write (the 581-wide V1Face geometry).
// ============================================================================

/// The graduated host width of the `setFieldDynVmDescriptor2R24` 1-felt descriptor: the
/// `setFieldDynV1Face` carries FOUR fewer chip sites than the standard rotated host (36 vs 40 — the
/// setField face does not fire the economic balance-hash sites), so its graduated width is
/// `ROT_WIDTH + 7·36 = 328 + 252 = 580`… +1 reserved = **581** (the committed
/// `setFieldDynVmDescriptor2R24.trace_width`, distinct from `GRAD_ROT_WIDTH`). The wide
/// carriers (the `setFieldDynVmDescriptor2R24Wide` member) land at THIS host width.
pub const SET_FIELD_DYN_HOST_WIDTH: usize = GRAD_ROT_WIDTH - 28; // 1647 − 4·7 sites = 1619 (wide 2579 − WIDE_CARRIER_APPENDIX)

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
    let (mut trace, mut base_pis) =
        generate_rotated_effect_vm_trace(initial_state, &[lead], before_w, after_w, caveat)?;
    // ⚠ DROP THE VALUE8 BLOCK. The synthetic in-bounds `SetField { field_idx: slot }` above is a
    // borrowed vehicle for the shared rotated machinery, NOT a static-slot write: the deployed
    // member here is `setFieldDynVmDescriptor2R24`, which carries no completion-lane weld and wants
    // the bare `ROT_PI_COUNT + rc` shape. The base generator publishes the 7 value8 completion PIs
    // for a static-slot setField (Lean `withSetFieldCompletionPins`), so strip them back out —
    // exactly as the supplyMint arm lifts the rc pins its unwrapped member does not carry.
    if base_pis.len()
        == ROT_PI_COUNT + crate::effect_vm_descriptors::SETFIELD_VALUE8_PI_LEN + DFA_RC_LEN
    {
        base_pis.drain(
            ROT_PI_COUNT..ROT_PI_COUNT + crate::effect_vm_descriptors::SETFIELD_VALUE8_PI_LEN,
        );
    }
    let base_pis = base_pis;
    if base_pis.len() != ROT_PI_COUNT + DFA_RC_LEN {
        return Err(format!(
            "setFieldDyn base generator: expected the rotated vector + the 4 dsl rc PIs, got {} \
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
    // `record_pin_offset`, so INSERT the AFTER record-digest limb at PI 46 (the descriptor pins the
    // per-effect extra FIRST, the dsl rc tail LAST: fifth@46, rc@47..50 — the base generator already
    // appended the 4 rc PIs at 46..49, so the insert shifts them to 47..50).
    dpis.insert(ROT_PI_COUNT, trace[last_idx][AFTER_BASE + B_RECORD_DIGEST]);
    debug_assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + 1 + DFA_RC_LEN,
        "setFieldDyn carries the rotated 46-PI + PI[46] + the 4 dsl rc PIs (47..50)"
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
/// `SET_FIELD_DYN_HOST_WIDTH` host (NOT `GRAD_ROT_WIDTH` — the setField face has four
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
    debug_assert_eq!(
        trace[0].len(),
        SET_FIELD_DYN_HOST_WIDTH + 2 * WIDE_NUM_CARRIERS * 8
    ); // 2579 (SET_FIELD_DYN_HOST_WIDTH + WIDE_CARRIER_APPENDIX)
    Ok((trace, dpis, mem_boundary))
}

// ============================================================================
// custom — the user-defined program effect bound to an EXTERNAL sub-proof
// (`customVmDescriptor2R24`; see [`CUSTOM_HOST_WIDTH_TEETH`] for the wide geometry).
// ============================================================================

/// The bare host width of the wide `customVmDescriptor2R24` member (BEFORE the
/// commitment/VK teeth — [`CUSTOM_HOST_WIDTH_TEETH`] is the base the wide carrier
/// appendix is actually appended at). Same V1Face host as setFieldDyn (the carriers
/// ride the identical 8-felt blocks); the trace SHAPE differs (a Custom row, no
/// Blum-memory boundary).
///
/// ⚠ This docstring used to read "the deployed descriptor is 789-wide, carriers at
/// 677 / 781, pinning host = 581", from a geometry three flag-days dead — the const's
/// own value has been `GRAD_ROT_WIDTH − 28` since. Deployed widths come from
/// `circuit/descriptors/*.tsv`, never from a paragraph.
pub const CUSTOM_HOST_WIDTH: usize = GRAD_ROT_WIDTH - 28; // 1647 − 4·7 sites = 1619

/// **THE CUSTOM COMMIT-TEETH COLUMNS (proof-bind flag-day rotation, 4 → 8 felts).**
/// The Custom row's param union carries only 4 commitment slots (cols 72..76 =
/// limbs 0..4 of the 8-felt `custom_proof_pi_commitment`); the SECOND SQUEEZE
/// BLOCK's limbs 4..8 ride these four member-local teeth columns appended at the
/// END of the custom host (Lean `EffectVmEmitRotationV3.CUSTOM_COMMIT_TEETH_COL`,
/// the custom twin of the membership/sovereign teeth). Filled uniformly on every
/// row (the `.piBinding .first` pins read row 0; a uniform fill keeps padding
/// rows consistent), published at IR2 PI 50..53.
pub const CUSTOM_COMMIT_TEETH_BASE: usize = CUSTOM_HOST_WIDTH; // 1619..1623
/// The number of commit-teeth columns (commitment limbs 4..8).
pub const CUSTOM_COMMIT_TEETH_LEN: usize = 4;
/// Faithful program-VK teeth: limbs 4..8 of `Effect::Custom.program_vk_hash`.
/// The param union carries limbs 0..4; these exact columns complete VK8 without
/// folding, truncation, or zero-extension.
pub const CUSTOM_VK_TEETH_BASE: usize = CUSTOM_COMMIT_TEETH_BASE + CUSTOM_COMMIT_TEETH_LEN;
pub const CUSTOM_VK_TEETH_LEN: usize = 4;

/// **THE APP-ROOT WELD FIELD OCTET (the wide custom leg-emit).** The wide custom descriptor
/// additionally PUBLISHES the AFTER-block committed `fields[0..8]` octet — the cell's
/// faithfully-carried field lane-0 limbs the `new8` commitment absorbs — as 8 TAIL PIs, placed
/// AHEAD of the 16 wide anchors (leg PI count 78 → 86; anchors shift to `[70..86)`). The per-turn
/// FOLD's app-root arm (`dregg_circuit_prove::ivc_turn_chain` `Some(binding)`) reads
/// `field[binding.field_key]` from this octet and connects it to the custom sub-proof's published
/// root `R`, forcing `R == field[K]`.
///
/// `CUSTOM_APP_FIELD_OCTET_LEN`(8) and `CUSTOM_APP_FIELD_ROT_BASE`(4 — the in-block offset of the
/// AFTER rotated block's `fields[0..8]` lane-0 octet: field registers r(FIELD_BASE+i) ride offsets
/// `CUSTOM_APP_FIELD_ROT_BASE + i`, Lean `weldsAt base+4 ↔ state.FIELD_BASE`; absolute column is
/// [`AFTER_BASE`] `+ CUSTOM_APP_FIELD_ROT_BASE + i`) are Lean-emitted — read from `layout_generated`
/// (`pub use` above), Lean `EffectVmEmitRotationV3.{CUSTOM_APP_FIELD_OCTET_LEN, CUSTOM_APP_FIELD_ROT_BASE}`.
/// The custom member's host width INCLUDING the commit teeth — the base the wide
/// carrier appendix is appended at (wide trace = 1627 + 960 = 2587; the deployed
/// wide member additionally carries the gentian bare-refuse block past that).
pub const CUSTOM_HOST_WIDTH_TEETH: usize =
    CUSTOM_HOST_WIDTH + CUSTOM_COMMIT_TEETH_LEN + CUSTOM_VK_TEETH_LEN; // 1627

/// **THE WIDE custom trace generator (`customVmDescriptor2R24`, host 1627 incl the
/// commitment/VK teeth / 82 base PIs [46 rot + 16 exposure + 4 rc + 8 app-root field octet +
/// 8 faithful fields-root lanes] + 16 wide anchors = 98).**
///
/// Lay the wide custom row for a [`Effect::Custom`] lead. The descriptor's
/// `proof_bind` op names two row columns, and (the VK epoch + the proof-bind
/// flag-day rotation) SIXTEEN `.piBinding` pins PUBLISH the full binding as the
/// descriptor's own public inputs (Lean `EffectVmEmitRotationV3.customPiExposure`):
///   * col 72 (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`) ← the sub-proof's 8-felt PI
///     commitment, limbs 0..4 (cols 72..76 — IR2 PI slots 46..49);
///   * cols 1619..1623 ([`CUSTOM_COMMIT_TEETH_BASE`]) ← commitment limbs 4..8 (the
///     genuine second squeeze block — IR2 PI slots 50..53);
///   * cols 68..72 (`PARAM_BASE + CUSTOM_VK_HASH_BASE`) ← program VK limbs 0..4
///     at IR2 PI 54..57;
///   * [`CUSTOM_VK_TEETH_BASE`]..+4 ← program VK limbs 4..8 at IR2 PI 58..61.
///
/// The `Effect::Custom`'s `(program_vk_hash, proof_commitment)` MUST be the
/// genuine values a verifying [`crate::custom_proof_bind::BoundCustomProof`]
/// exposes — `bound.vk_hash_felts()` / `bound.proof_commitment()` — so the row
/// the deployed prover mints carries exactly the binding the fold re-derives.
/// (The off-AIR `verify_proof_bind` engine that once re-derived it from a
/// hand-verified STARK died with stark-kill; there is no such SDK-reachable
/// entry point.) The binding is enforced at the per-turn FOLD: the sixteen pins
/// publish the bound columns as PIs the fold connects to the custom sub-proof
/// leaf's 8-felt PI-commitment (the recursion / `EngineBinding` carrier), so the
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
    if base_pis.len() != ROT_PI_COUNT + DFA_RC_LEN {
        return Err(format!(
            "custom wide generator: base PI vector {} != {} (a Custom lead carries the bare 46-PI \
             rotated vector + the 4 dsl rc PIs — no record-pin / grow-gate offset)",
            base_pis.len(),
            ROT_PI_COUNT + DFA_RC_LEN
        ));
    }
    // THE COMMIT TEETH (proof-bind flag-day rotation): lay the 8-felt commitment's SECOND
    // SQUEEZE BLOCK (limbs 4..8, straight from the lead `Effect::Custom.proof_commitment`)
    // into the four member-local teeth columns at the end of the host, on EVERY row (the
    // `.piBinding .first` pins read row 0; a uniform fill keeps padding rows consistent).
    let (commit_hi, vk_hi): (
        [BabyBear; CUSTOM_COMMIT_TEETH_LEN],
        [BabyBear; CUSTOM_VK_TEETH_LEN],
    ) = match effects.first() {
        Some(Effect::Custom {
            proof_commitment,
            program_vk_hash,
        }) => (
            core::array::from_fn(|k| proof_commitment[4 + k]),
            core::array::from_fn(|k| program_vk_hash[4 + k]),
        ),
        _ => unreachable!("guarded above: the lead effect is Effect::Custom"),
    };
    for row in trace.iter_mut() {
        if row.len() < CUSTOM_HOST_WIDTH_TEETH {
            row.resize(CUSTOM_HOST_WIDTH_TEETH, BabyBear::ZERO);
        }
        for k in 0..CUSTOM_COMMIT_TEETH_LEN {
            row[CUSTOM_COMMIT_TEETH_BASE + k] = commit_hi[k];
        }
        for k in 0..CUSTOM_VK_TEETH_LEN {
            row[CUSTOM_VK_TEETH_BASE + k] = vk_hi[k];
        }
    }
    // VK epoch + proof-bind rotation: PUBLISH the `proof_bind` op's bound columns as the
    // descriptor's own public inputs (Lean `EffectVmEmitRotationV3.customPiExposure`, SIXTEEN
    // `.piBinding .first` pins at IR2 PI slots 46..61). The first (lead Custom) row carries the
    // bound `(commit, vk)`: the four low `custom_proof_commitment` limbs (cols 72..75) at slots
    // 46..49, the four HIGH commitment limbs (the commit-teeth cols 1619..1623) at slots 50..53,
    // then the eight `custom_program_vk_hash` limbs at slots 54..61 (low4 in params, high4 in
    // exact VK-teeth columns). Exposing them is what lets the per-turn FOLD connect the custom
    // sub-proof leaf's full canonical program identity and 8-felt
    // PI-commitment to this descriptor; the in-AIR `proof_bind` op stays a declaration (the
    // binding is at the fold, not a row gate).
    let mut base_pis = base_pis;
    {
        use super::columns::{PARAM_BASE, param};
        let r0 = &trace[0];
        // The dsl rc tail rides LAST on the wrapped member (`withDfaRcPins customV3`: exposure at
        // 46..61, rc at 62..65) — the base generator appended rc at 46..49, so lift it off, lay
        // the 16 exposure PIs, then re-append it.
        let rc_tail: Vec<BabyBear> = base_pis.split_off(base_pis.len() - DFA_RC_LEN);
        for k in 0..4 {
            base_pis.push(r0[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + k]);
            // PI 46..49
        }
        for k in 0..CUSTOM_COMMIT_TEETH_LEN {
            base_pis.push(r0[CUSTOM_COMMIT_TEETH_BASE + k]); // PI 50..53 (commit limbs 4..8)
        }
        for k in 0..4 {
            base_pis.push(r0[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + k]); // PI 54..57
        }
        for k in 0..CUSTOM_VK_TEETH_LEN {
            base_pis.push(r0[CUSTOM_VK_TEETH_BASE + k]); // PI 58..61 (VK limbs 4..8)
        }
        base_pis.extend_from_slice(&rc_tail); // PI 62..65: the dsl rc tail

        // THE APP-ROOT WELD LEG-EMIT (Lean `withAfterOctetPins customV3 4`): publish the AFTER-block
        // committed `fields[0..8]` octet — the faithfully-carried field lane-0 limbs the `new8`
        // commitment absorbs — as 8 TAIL PIs (slots 66..73), AHEAD of the 16 wide anchors. These are
        // `.piBinding .last` pins, so read the AFTER rotated block's field registers r3..r10
        // (`AFTER_BASE + CUSTOM_APP_FIELD_ROT_BASE + k`, cols 431..438) on the LAST row (the rotated
        // block is producer-filled uniformly). The fold's app-root arm reads `field[field_key]` from
        // this octet and connects it to the sub-proof's published root R (`field[K] == R`).
        let last = trace
            .last()
            .expect("custom wide trace has at least one row");
        for k in 0..CUSTOM_APP_FIELD_OCTET_LEN {
            base_pis.push(last[AFTER_BASE + CUSTOM_APP_FIELD_ROT_BASE + k]); // PI 66..73
        }

        // THE AUTHENTICATED OVERFLOW-MAP WELD (Lean `withAfterFieldsRootPins`): publish the
        // non-contiguous native-eight `fields_root` group at PI 74..81.  The Descent census
        // relation opens its eight custody leaves against this root; the direct-IR2 recursion
        // node connects all eight lanes to these exact post-state columns.  Reading
        // `AFTER_BASE + B_FIELDS_ROOT + k` would be WRONG: only lane 0 is contiguous, while the
        // completion lanes are Lean-generated as `FIELDS_ROOT_GROUP = [36,66,67,19..23]`.
        for col in FIELDS_ROOT_GROUP {
            base_pis.push(last[AFTER_BASE + col]); // PI 74..81
        }
    }
    // 46 base + 16 custom exposure + 4 rc + 8 app-root field octet + fields_root8 = 82
    debug_assert_eq!(
        base_pis.len(),
        ROT_PI_COUNT + 16 + DFA_RC_LEN + CUSTOM_APP_FIELD_OCTET_LEN + FIELDS_ROOT_GROUP.len()
    );
    let dpis = append_wide_carriers(&mut trace, base_pis, CUSTOM_HOST_WIDTH_TEETH);
    debug_assert_eq!(
        trace[0].len(),
        CUSTOM_HOST_WIDTH_TEETH + 2 * WIDE_NUM_CARRIERS * 8
    );
    // 82 + 16 wide anchors = 98 (anchors at [82..98))
    debug_assert_eq!(
        dpis.len(),
        ROT_PI_COUNT + 16 + DFA_RC_LEN + CUSTOM_APP_FIELD_OCTET_LEN + FIELDS_ROOT_GROUP.len() + 16
    );
    Ok((trace, dpis))
}

/// **THE CAP-WRITE WIDE producer witness (the cap-open WRITE route's c-list).** A cap-WRITE family
/// lead (attenuate / revokeCapability / a witnessed grant) advances its AFTER cap-root through an
/// in-circuit cap-tree write that only the `…WriteCapOpen…` / `attenuateCapOpenEff` members bind; this
/// carries what that write needs: the holder's FULL **7-field** c-list (`cap_leaves` + the
/// `cap_tombstones` whose positions are retained with a ZERO digest — the openable
/// [`CanonicalCapTree`](crate::cap_root::CanonicalCapTree) the BEFORE cap-root IS the root of), the
/// consumed cap's `anchor_key` (`slot_hash`), and the op-specific `inserted` `(key, value)` payload
/// (`Update`/attenuate writes the narrowed KEEP_MASK as the value and ignores the key; `Remove`/
/// revokeCapability takes `None`; `Insert` takes the FRESH conferred edge).
///
/// ⚑ **THIS USED TO BE A 2-FIELD `HeapLeaf` c-list, and that was the defect.** The old shape fed
/// [`generate_rotated_cap_write_base`] — the arity-2 `map_op` bridge — and `30ff508fe` replaced the
/// cap-tree `map_op` with a Merkle SPINE: **every** cap member in **all three** registries now declares
/// `map_ops == 0`, so supplying a witness heap is refused outright ("descriptor declares no map ops but
/// witness heaps were supplied"). The cap-open READ crown needs the 7 leaf fields anyway (the
/// `targetBind` / `effBitGateFor` / decoded-tier gates read them), which a `(key, value)` pair cannot
/// carry. The producer now REBUILDS the tree and takes the shape-matched witness off it
/// ([`generate_rotated_cap_write_capopen_wide`]) — so a fabricated membership path is not even
/// representable, let alone provable.
pub struct CapWriteWideWitness {
    /// The holder's FULL 7-field c-list (the BEFORE cap-root is this sorted cap-tree's root).
    pub cap_leaves: Vec<crate::cap_root::CapLeaf>,
    /// The TOMBSTONED slot keys (revoked positions: sort key retained, digest forced to
    /// [`CAP_ZERO8`](crate::cap_root::CAP_ZERO8)), so a c-list carrying earlier revocations rebuilds
    /// the genuine committed root rather than a compacted one.
    pub cap_tombstones: Vec<BabyBear>,
    /// The consumed cap's `slot_hash`: the UPDATEd / REMOVEd key, or the INSERT's held-authority
    /// ANCHOR. MUST be live in `cap_leaves` (else the witness builders fail closed).
    pub anchor_key: BabyBear,
    /// The op payload: `(fresh_key, conferred_value)` for `Insert`, `(_ignored, KEEP_MASK)` for
    /// `Update`, `None` for `Remove`.
    pub inserted: Option<(BabyBear, BabyBear)>,
    /// ⚠ **THE ADVERSARIAL POLE — honest producers pass `None`.** When `Some(root8)`, THIS value is
    /// written into the committed AFTER cap-root group instead of the genuine fold: it is the prover's
    /// CLAIM, not a computation the producer trusts. The in-circuit spine PINS that group to the fold
    /// (`CapOpenEmit.removeTombstoneConstraints` for REMOVE, `effCapOpenWriteV3_forces_write8` for
    /// UPDATE/INSERT), so a claim that is not the fold is **UNSAT at the prover** — no proof exists to
    /// hand a ledgerless light client. Exactly the asymmetry
    /// [`apply_rotated_cap_remove_after_spine`]'s `after_root8` documents, lifted to the wide+welded
    /// leg so the tooth can be exercised through the ONE mint route rather than a re-implemented twin.
    pub claimed_post_cap_root8: Option<[BabyBear; CAP_OPEN_DIGEST_W]>,
}

/// **THE CAP-OPEN *WRITE* ROUTE for a cap-WRITE lead** — the committed member the light-client wire
/// DEMANDS, its cap-tree write shape, and the crown facet bit the wrapper binds.
///
/// ⚑ **WHY THE BARE MEMBER IS NOT A DESTINATION.** `rotated_descriptor_name_for_effect` resolves
/// `attenuateVmDescriptor2R24` / `revokeCapabilityVmDescriptor2R24` / `grantCapVmDescriptor2R24` for
/// these leads, and all three are on the light-client deny-list
/// (`dregg_sdk::full_turn_proof::is_forbidden_plain_cap_descriptor`): a cap effect proven WITHOUT the
/// in-circuit membership crown launders host-trusted authority, so such a leg self-verifies and the
/// WIRE refuses it. The write-bearing cap-open wrappers are the wire-ACCEPTED members
/// (`DescriptorAuthorityClass::CrownedWriteRoute`), and they are already committed — byte-for-byte — in
/// `V3_STAGED_REGISTRY_TSV` and [`WIDE_REGISTRY_STAGED_TSV`](crate::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV)
/// (and, derived from the latter, in the welded set —
/// [`derive_welded_wide_member`](crate::effect_vm_descriptors::derive_welded_wide_member)).
/// Nothing re-emits and no VK rotates to take this route.
///
/// SCOPE: exactly the three leads the wide dispatcher's cap-WRITE arm lays a base trace for. The other
/// write-bearing wrappers (`introduceWriteCapOpen` / `revokeDelegationWriteCapOpen` /
/// `refreshDelegationWriteCapOpen` / `spawnWriteCapOpen`) are reached by their OWN dispatcher arms (the
/// revoked-set grow-gate, the accounts birth leg, …) whose base traces differ; routing them here would
/// pair a WriteCapOpen descriptor with a foreign trace. They stay named tails until their arm threads
/// this route explicitly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapWriteCapOpenRoute {
    /// The committed registry key (the SAME key in all three registries).
    pub key: &'static str,
    /// The cap-tree write shape the member's after-spine forces.
    pub op: CapTreeWriteOp,
    /// The crown facet bit the wrapper's `effBitGateFor` pins (the deployed `cell/facet.rs`
    /// `EFFECT_<kind> = 1 << n`). The opened leaf must PERMIT it or the producer fails closed.
    pub crown_eff_bit: u32,
}

// The deployed `cell/facet.rs` effect-kind bits the WRITE wrappers bind. These DIFFER from the
// authority-only twins' for the grant family: `delegateWriteCapOpen` binds DELEGATION_OPS (1<<16)
// while `grantCapCapOpen` binds GRANT_CAPABILITY (1<<2) — a delegate IS a delegation op.
/// `EFFECT_TRANSFER` (`1 << 1`) — the crown facet `attenuateCapOpenEff` binds (== [`WRITE_MASK_LO`]).
const CAP_WRITE_EFFECT_TRANSFER: u32 = 1 << 1;
/// `EFFECT_REVOKE_CAPABILITY` (`1 << 3`) — the crown facet `revokeCapabilityWriteCapOpen` binds.
const CAP_WRITE_EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;
/// `EFFECT_DELEGATION_OPS` (`1 << 16`) — the crown facet `delegateWriteCapOpen` binds.
const CAP_WRITE_EFFECT_DELEGATION_OPS: u32 = 1 << 16;

/// Resolve the [`CapWriteCapOpenRoute`] for a lead effect. `None` ⇒ this lead has no cap-open WRITE
/// route wired through the wide dispatcher's cap-WRITE arm.
///
/// The three rows mirror `dregg_sdk::full_turn_proof::cap_open_route_for_run`'s `write` field
/// member-for-member (key, op and crown bit), so the IVC leg and the live SDK cap-open leg prove the
/// SAME committed member for the same effect.
pub fn cap_write_capopen_route(effect: &Effect) -> Option<CapWriteCapOpenRoute> {
    match effect {
        // The in-place UPDATE-AT-KEY: the READ opens the held leaf against BEFORE, the 143-column
        // after-spine re-opens it with `mask_lo := KEEP_MASK` against AFTER. This member carries the
        // Update DIRECTLY (there is no separate `attenuateWriteCapOpen` key).
        Effect::AttenuateCapability { .. } => Some(CapWriteCapOpenRoute {
            key: "attenuateCapOpenEffVmDescriptor2R24",
            op: CapTreeWriteOp::Update,
            crown_eff_bit: CAP_WRITE_EFFECT_TRANSFER,
        }),
        // The TOMBSTONE remove: the AFTER group is pinned to `CAP_ZERO8` folded up the removed leaf's
        // own path, so a fabricated post-remove root is UNSAT at the prover.
        Effect::RevokeCapability { .. } => Some(CapWriteCapOpenRoute {
            key: "revokeCapabilityWriteCapOpenVmDescriptor2R24",
            op: CapTreeWriteOp::Remove,
            crown_eff_bit: CAP_WRITE_EFFECT_REVOKE_CAPABILITY,
        }),
        // The fresh-edge INSERT (the cross-vat grant). Reached ONLY when a c-list witness is threaded;
        // a witnessless grant keeps the authority-only freeze base (see `cap_write_wide_plan`).
        Effect::GrantCapability { .. } => Some(CapWriteCapOpenRoute {
            key: "delegateWriteCapOpenVmDescriptor2R24",
            op: CapTreeWriteOp::Insert,
            crown_eff_bit: CAP_WRITE_EFFECT_DELEGATION_OPS,
        }),
        _ => None,
    }
}

/// **THE PROMOTED CAP-OPEN *WRITE* WIDE PRODUCER — the write-spine trace producer, in `dregg-circuit`.**
/// Given a `ROT_WIDTH`-wide rotated base trace for a cap-WRITE lead plus its base PI vector, lay the
/// full committed shape of the member `route.key` names and return the WIDE PI vector:
///
///   1. rebuild the holder's openable [`CanonicalCapTree`](crate::cap_root::CanonicalCapTree) from the
///      7-field c-list + tombstones — the BEFORE cap-root IS its root;
///   2. take the SHAPE-MATCHED witness off THAT tree (`membership_witness` for UPDATE, `remove_witness`
///      for REMOVE, `insert_witness` for INSERT) — a key that is absent, already-ghosted or
///      sentinel-colliding fails closed here, so no membership path is ever fabricated;
///   3. lift it to the cap-open READ crown ([`CapOpenWitness::from_membership_for`], which refuses a
///      leaf whose facet does not PERMIT `route.crown_eff_bit`) and widen ([`widen_to_cap_open`]);
///   4. lay the member's AFTER-SPINE + the wide carriers through the EXISTING per-shape producers
///      ([`generate_rotated_cap_attenuate_after_spine_wide`] /
///      [`generate_rotated_cap_remove_after_spine_wide`] /
///      [`generate_rotated_cap_insert_after_spine_wide`]).
///
/// The rc tail is lifted first: the cap-open family was never `withDfaRcPins`-wrapped in the Lean emit
/// (the committed wide members carry `46 + 16 = 62` PIs, not `46 + 4 + 16 = 66`), exactly as the live
/// SDK cap-open leg builder lifts it.
///
/// **NO map heaps, and that is the point.** The faithful 8-felt cap-tree write is forced by the
/// descriptor's own depth-16 `node8` fold, not by a map table — `map_ops == 0` on every one of these
/// members. The caller supplies an EMPTY `map_heaps`.
///
/// ⚑ **LAW #1.** This fills COLUMNS only. Every constraint is the Lean-emitted descriptor's
/// (`metatheory/Dregg2/Circuit/Emit/{CapOpenEmit,CapInsertEmit,CapRemoveEmit}.lean`); no constraint,
/// gadget or descriptor is authored here, and nothing re-emits or rotates a VK to take this route.
///
/// ⚠ **NO `patch_attenuate_base_for_cap_open`.** Every write-bearing wrapper rides the nonce-TICK face
/// (`(col78 − col56) == 1 − sel[NOOP]`); the patch FREEZES the nonce against that gate. The bare
/// generator already ticks it, and the deployed SDK leg skips the patch for exactly this reason.
pub fn generate_rotated_cap_write_capopen_wide(
    trace: &mut Vec<Vec<BabyBear>>,
    base_pis: Vec<BabyBear>,
    route: &CapWriteCapOpenRoute,
    w: &CapWriteWideWitness,
) -> Result<Vec<BabyBear>, String> {
    use crate::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf};

    if trace.is_empty() {
        return Err("cap-open write wide: empty base trace".into());
    }
    if trace[0].len() != ROT_WIDTH {
        return Err(format!(
            "cap-open write wide: base trace width {} != {ROT_WIDTH} (call on the bare rotated base, \
             before widen_to_cap_open)",
            trace[0].len()
        ));
    }
    // THE CAP-OPEN rc STRIP: the committed cap-open members carry the UNWRAPPED base (46 PIs); the
    // bare generators append the 4 dsl rc pins unconditionally.
    let mut base_pis = base_pis;
    if base_pis.len() < DFA_RC_LEN {
        return Err(format!(
            "cap-open write wide: base PI vector {} shorter than the dsl rc tail {DFA_RC_LEN}",
            base_pis.len()
        ));
    }
    base_pis.truncate(base_pis.len() - DFA_RC_LEN);

    let tree = CanonicalCapTree::new_with_tombstones(
        w.cap_leaves.clone(),
        &w.cap_tombstones,
        CAP_TREE_DEPTH,
    );
    let key = route.key;

    match route.op {
        CapTreeWriteOp::Update => {
            let (_ignored_key, keep_mask) = w.inserted.ok_or_else(|| {
                format!(
                    "cap-open write wide ({key}): the UPDATE-AT-KEY route needs `inserted = Some((_, \
                     KEEP_MASK))` — the narrowed mask the after-spine rebinds the held leaf to"
                )
            })?;
            let mw = tree.membership_witness(w.anchor_key).ok_or_else(|| {
                format!(
                    "cap-open write wide ({key}): the held key {} is NOT live in the supplied 7-field \
                     c-list — the held-authority READ has no membership witness and the turn is \
                     refused (no fabricated post-cap-root)",
                    w.anchor_key.as_u32()
                )
            })?;
            // THE SUBMASK NON-AMPLIFICATION, producer side: the after-spine writes `KEEP_MASK` into
            // col 73 and the held leaf's own `mask_lo` into col 72, and the member's surviving
            // `submaskLookup` forces `KEEP ⊑ HELD`. An amplifying narrow is UNSAT in-circuit; say so
            // here rather than emitting a trace whose only defect is an opaque lookup miss.
            let held = mw.leaf.mask_lo.as_u32();
            let keep = keep_mask.as_u32();
            if keep & held != keep {
                return Err(format!(
                    "cap-open write wide ({key}): the narrowed KEEP_MASK {keep:#x} is NOT a submask of \
                     the held leaf's committed mask_lo {held:#x} — an attenuate that AMPLIFIES is UNSAT \
                     in-circuit (the `granted ⊑ held` non-amplification lookup)"
                ));
            }
            let open = CapOpenWitness::from_membership_for(
                &mw.leaf,
                &mw.siblings,
                &mw.directions,
                route.crown_eff_bit,
            )
            .map_err(|e| format!("cap-open write wide ({key}): {e}"))?;
            if open.cap_root != tree.root() {
                return Err(format!(
                    "cap-open write wide ({key}): the held leaf's membership path does not recompose \
                     the rebuilt c-list root (the supplied c-list is not the holder's pre-state)"
                ));
            }
            widen_to_cap_open(trace, &open)
                .map_err(|e| format!("cap-open write wide ({key}): READ crown widen: {e}"))?;
            // The NARROW after-spine first, so the adversarial re-stamp lands BEFORE the wide carriers
            // re-absorb the limbs — a claimed post-root then rides an INTERNALLY CONSISTENT trace whose
            // published ~124-bit anchors agree with the lie, and whose only defect is the write itself.
            generate_rotated_cap_attenuate_after_spine(
                trace,
                &open,
                mw.leaf.slot_hash,
                mw.leaf.mask_lo,
                keep_mask,
            )
            .map_err(|e| format!("cap-open write wide ({key}): UPDATE after-spine: {e}"))?;
            restamp_claimed_post_cap_root(trace, w.claimed_post_cap_root8, key)?;
            Ok(append_wide_carriers(
                trace,
                base_pis,
                CAP_OPEN_WIDTH + CAP_OPEN_AFTER_SPINE_SPAN,
            ))
        }
        CapTreeWriteOp::Remove => {
            if w.inserted.is_some() {
                return Err(format!(
                    "cap-open write wide ({key}): the TOMBSTONE remove takes no insert payload — it \
                     collapses the removed position to CAP_ZERO8 and confers nothing"
                ));
            }
            let rmw = tree.remove_witness(w.anchor_key).ok_or_else(|| {
                format!(
                    "cap-open write wide ({key}): the revoked key {} is NOT live in the supplied \
                     7-field c-list (absent, sentinel, or already tombstoned) — the remove has no \
                     declared membership and the turn is refused (no fabricated post-cap-root)",
                    w.anchor_key.as_u32()
                )
            })?;
            let open = CapOpenWitness::from_membership_for(
                &rmw.removed,
                &rmw.siblings,
                &rmw.directions,
                route.crown_eff_bit,
            )
            .map_err(|e| format!("cap-open write wide ({key}): {e}"))?;
            if open.cap_root != rmw.old_root {
                return Err(format!(
                    "cap-open write wide ({key}): the removed leaf's membership path does not \
                     recompose the rebuilt c-list root (the supplied c-list is not the holder's \
                     pre-state)"
                ));
            }
            if rmw.new_root == rmw.old_root {
                return Err(format!(
                    "cap-open write wide ({key}): the tombstone fold did not MOVE the cap-root — a \
                     remove that leaves the root fixed would make the write tooth vacuous"
                ));
            }
            widen_to_cap_open(trace, &open)
                .map_err(|e| format!("cap-open write wide ({key}): READ crown widen: {e}"))?;
            // `after_root8` is the value written into the committed AFTER group: the prover's CLAIM.
            // The tombstone spine's 8 `rootPinGate`s force it to the zero-fold, so a fabrication is
            // UNSAT at the prover.
            let claimed = w.claimed_post_cap_root8.unwrap_or(rmw.new_root);
            let dpis = generate_rotated_cap_remove_after_spine_wide(
                trace,
                base_pis,
                open.cap_root,
                claimed,
                rmw.removed.slot_hash,
                rmw.removed.mask_lo,
                &rmw.siblings,
                &rmw.directions,
            )
            .map_err(|e| format!("cap-open write wide ({key}): REMOVE tombstone spine: {e}"))?;
            Ok(dpis)
        }
        CapTreeWriteOp::Insert => {
            let (fresh_key, conferred) = w.inserted.ok_or_else(|| {
                format!(
                    "cap-open write wide ({key}): the INSERT route needs `inserted = Some((fresh_key, \
                     conferred_value))` — the edge the turn grafts into the cap-tree"
                )
            })?;
            if fresh_key == w.anchor_key {
                return Err(format!(
                    "cap-open write wide ({key}): the inserted key {} EQUALS the held-authority anchor \
                     — the anchor must be PRESENT and the fresh key ABSENT, so they must be distinct",
                    fresh_key.as_u32()
                ));
            }
            let anchor = tree
                .membership_witness(w.anchor_key)
                .ok_or_else(|| {
                    format!(
                        "cap-open write wide ({key}): the held-authority anchor {} is NOT live in the \
                         supplied 7-field c-list — the delegator cannot exhibit the right it confers \
                         (no fabricated post-cap-root)",
                        w.anchor_key.as_u32()
                    )
                })?
                .leaf;
            // The conferred edge rides the anchor's own target/tier/mask/expiry (a delegation confers
            // the HELD edge, so the crown facet the wrapper binds on the spliced leaf is permitted
            // exactly when the anchor permits it); the conferred payload datum rides `breadstuff`.
            let spliced = CapLeaf {
                slot_hash: fresh_key,
                breadstuff: conferred,
                ..anchor
            };
            let iw = tree.insert_witness(spliced).ok_or_else(|| {
                format!(
                    "cap-open write wide ({key}): the sorted INSERT of the fresh key {} was refused \
                     (already present, tombstoned, or sentinel-colliding) — fail closed, no \
                     fabricated after-root",
                    fresh_key.as_u32()
                )
            })?;
            let open = CapOpenWitness::from_membership_for(
                &spliced,
                &iw.siblings,
                &iw.directions,
                route.crown_eff_bit,
            )
            .map_err(|e| format!("cap-open write wide ({key}): the spliced leaf: {e}"))?;
            widen_to_cap_open(trace, &open)
                .map_err(|e| format!("cap-open write wide ({key}): READ crown widen: {e}"))?;
            let claimed = w.claimed_post_cap_root8.unwrap_or(iw.new_root);
            let dpis = generate_rotated_cap_insert_after_spine_wide(
                trace,
                base_pis,
                iw.old_root,
                claimed,
                fresh_key,
                conferred,
                anchor.mask_lo,
                anchor.slot_hash,
                anchor.mask_lo,
            )
            .map_err(|e| format!("cap-open write wide ({key}): INSERT after-spine: {e}"))?;
            Ok(dpis)
        }
    }
}

/// The UPDATE arm's adversarial pole. The attenuate after-spine COMPUTES the AFTER group from the
/// re-opened leaf, so a claimed post-root cannot be threaded through it as a parameter (unlike the
/// REMOVE/INSERT spines, whose `after_root8` IS the claim). Re-stamp the committed AFTER cap-root
/// group with the claim and recompute both rotated block commits, BEFORE the wide carriers are
/// appended — the published ~124-bit anchors then agree with the claim, so the trace is INTERNALLY
/// CONSISTENT and its ONLY defect is that the AFTER group is not the after-spine's fold. The spine's
/// own `rootPin`s have nothing to match: **UNSAT at the prover**.
fn restamp_claimed_post_cap_root(
    trace: &mut [Vec<BabyBear>],
    claimed: Option<[BabyBear; CAP_OPEN_DIGEST_W]>,
    key: &str,
) -> Result<(), String> {
    let Some(claimed) = claimed else {
        return Ok(());
    };
    if trace.is_empty() {
        return Err(format!("cap-open write wide ({key}): empty trace"));
    }
    for row in trace.iter_mut() {
        for lane in 0..CAP_OPEN_DIGEST_W {
            row[cap_root_group_col(AFTER_BASE, lane)] = claimed[lane];
        }
        recompute_block_commit(row, BEFORE_BASE);
        recompute_block_commit(row, AFTER_BASE);
    }
    Ok(())
}

/// **THE CAP-WRITE WIDE plan for a WITNESSLESS cap-WRITE lead.** `Some((needs_write_witness,
/// needs_freeze_patch))` for the cap-WRITE family the bare wide transfer-shape route cannot satisfy.
/// This arm is reached ONLY when no [`CapWriteWideWitness`] was threaded — a witnessed lead takes
/// [`cap_write_capopen_route`] and the committed cap-open WRITE member instead:
///   * `AttenuateCapability` / `RevokeCapability` → `(true, false)`. Their AFTER cap-root is an
///     in-circuit cap-tree write that ONLY the cap-open WRITE members bind; the bare member is both
///     UNSAT on the write and light-client FORBIDDEN. Without the holder's c-list there is nothing to
///     open, so the turn FAILS CLOSED (never a fabricated post-cap-root).
///   * `GrantCapability` → `(false, true)` — the authority-only grant base FREEZES the cap-root
///     (pass-through, no write) and rides the nonce-FREEZE face the bare transfer-shape route
///     (nonce-TICK) mis-shapes, so the freeze patch IS applied and no witness is needed.
///     ⚠ NAMED RESIDUAL: the member this mints (`grantCapVmDescriptor2R24`) is itself on the
///     light-client deny-list, so the leg self-verifies and the WIRE refuses it. Threading a c-list
///     witness takes the wire-accepted `delegateWriteCapOpen` INSERT route instead.
///
/// `None` for every other lead (the nonce-TICK passthrough cap bases revokeDelegation / introduce ride
/// their own arms; the value/field/grow-gate/record families have theirs).
fn cap_write_wide_plan(effect: &Effect) -> Option<(bool, bool)> {
    match effect {
        Effect::AttenuateCapability { .. } | Effect::RevokeCapability { .. } => Some((true, false)),
        Effect::GrantCapability { .. } => Some((false, true)),
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
/// is UNSAT without it); `cap_write` the cap-tree write witness — `Some` REQUIRED for a cap-WRITE lead
/// (attenuate / revokeCapability), which then RESOLVES A DIFFERENT MEMBER: the committed cap-open WRITE
/// wrapper [`cap_write_capopen_route`] names, not the bare `…VmDescriptor2R24` the effect→name resolver
/// returns (see that route's doc — the bare cap members are light-client FORBIDDEN); `membership_teeth`
/// the producer-honest
/// `(sender_leaf, authorized_root)` pair for the committed transfer row's membership-teeth tail
/// (`None` = the ZERO no-caveat sentinel — see the registry-tail block below). Fails closed
/// (`Err`) on an empty / heterogeneous / non-cohort slice.
///
/// ## The post-regen registry TAIL (v12 exposure regen — hoisted here from the leg-mint recipe)
///
/// The committed wide registry row a member proves against may demand MORE PIs (and trace columns)
/// than the per-family wide producer emits. This dispatcher derives that tail FROM THE DESCRIPTOR
/// (`public_input_count − emitted`, `trace_width − row width` — never a hardcoded count; members
/// differ) and fills it producer-honest, so EVERY route through the shared spine (the live SDK wide
/// prover, the IVC leg mints, the leg-mint recipe) emits the committed shape:
///
///   * the committed transfer row (`CarrierComposed.transferV3MembershipWide`, 68): the
///     membership-teeth pair `(sender_leaf, authorized_root)` — 2 constant teeth columns past the
///     carriers + 2 claim PIs spliced ahead of the 16 wide anchors. The values come
///     from `membership_teeth` (the caller's BEFORE-cell derivation — `compress_member` over the
///     owner key + the `SenderAuthorized { PublicRoot }` slot felt); `None` fills the ZERO pair,
///     exactly the no-caveat sentinel the fold's membership arm refuses to bind.
///     ⚑ This said "(row-0-pinned)" until 2026-08-01 and that was FALSE. Measured on the emitted
///     bytes: `transferVmDescriptor2R24` has NO `pi_binding` for PI 50 or 51, and the two teeth
///     columns it fills below (1735/1736 = `trace_width − refuse_weld_widen(45) − 2/−1`) are
///     referenced by NO constraint of any kind. This arm writes them; the AIR never reads them.
///     `carrier_forgery_forge.rs:143` is RED on precisely that, and `ivc_turn_chain.rs:4734`
///     admits the claim column-free ("parametric until the regen pins them"). Creating the pin is
///     necessary but NOT sufficient — a pin on an unread column is deleted again by
///     `UnforcedPiPins.dropUnforcedPins`, which is correct. The column has to become FORCED first,
///     and the two Lean gates that would do it (`CarrierOctetGates.withMembershipPubkeyCompress`,
///     `effFieldsReadOpenV3`) are UNCONDITIONAL, so wiring either as-is is UNSAT on every
///     no-caveat transfer — i.e. on the dominant path — because of the ZERO sentinel three lines
///     up. A selector is the missing gadget, not a bigger budget.
///   * the committed makeSovereign row (`CarrierComposed.makeSovereignV3DeployedWide`, 78): the 4
///     KEY_COMMIT teeth + the 32-column chip appendix, filled IN the record-pin arm
///     ([`append_sovereign_key_commit_rider`] — derived from the committed pubkey octet, so the
///     generic pairing check below sees a zero tail).
///
/// A member whose committed row demands a tail this dispatcher has no producer fill for FAILS
/// CLOSED (mint it through its dedicated carrier minter) — never a guessed value.
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
    refusal_fields: Option<(&[crate::openable_fields_root::ExactFieldsLeaf], [u8; 32])>,
    cap_write: Option<&CapWriteWideWitness>,
    membership_teeth: Option<(BabyBear, BabyBear)>,
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
    let base_name = rotated_descriptor_name_for_effect(lead).ok_or_else(|| {
        format!("wide rotated prover: effect {lead:?} is not in the rotated cohort")
    })?;
    if effects.len() > 1 {
        for e in &effects[1..] {
            if rotated_descriptor_name_for_effect(e) != Some(base_name) {
                return Err("wide rotated prover: heterogeneous multi-effect turn".into());
            }
        }
    }
    // ⚑ THE CAP-OPEN *WRITE* REROUTE. A cap-WRITE lead carrying the holder's c-list does NOT prove
    // the bare `…VmDescriptor2R24` this resolver names: that member is light-client FORBIDDEN (it
    // launders host-trusted authority) AND it declares `map_ops == 0` since the Merkle-spine flag day,
    // so the write it is supposed to bind is bound by nothing. The witnessed route is the committed
    // cap-open WRITE wrapper — resolved HERE, before the registry lookup, so descriptor and trace
    // cannot disagree (the arm below is the ONLY producer for these keys).
    let cap_write_route = match (cap_write_capopen_route(lead), cap_write) {
        (Some(route), Some(_)) => Some(route),
        _ => None,
    };
    let name = cap_write_route.map_or(base_name, |r| r.key);
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
            .map(|nf| HeapLeaf::entry(*nf, BabyBear::new(1)))
            .collect();
        // No delegated-capability context reaches this dispatch, and the committed `revoked_root`
        // every live rotation witness carries is `empty_revoked_root_8()`; park the mint-root
        // ancestor against that same empty set.
        generate_rotated_note_spend_wide(
            initial_state,
            effects,
            before,
            after,
            caveat,
            &leaves,
            &SpendRevocationWitness::undelegated(&[]),
        )
        .map_err(|e| format!("wide note-spend generation: {e}"))?
    } else if matches!(lead, Effect::NoteCreate { .. }) {
        generate_rotated_note_create_wide(initial_state, effects, before, after, caveat, &[])
            .map_err(|e| format!("wide note-create generation: {e}"))?
    } else if matches!(lead, Effect::Refusal { .. }) {
        let (leaves, audit_value) = refusal_fields.ok_or_else(|| {
                "wide refusal prover: a Refusal lead requires `refusal_fields` (the exact BEFORE-cell \
                 fields-tree leaves + the raw 32-byte audit value) to satisfy the FLD2/FLN2 update; \
                 missing exact context fails closed"
                    .to_string()
            })?;
        // Exact V2: the raw-key/raw-value FLD2 leaf and FLN2 path are replayed through the full
        // state16 bus; no scalar map-op heap or modularly-folded audit felt remains.
        generate_rotated_refusal_write_wide(
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
        let (mut t, mut d) =
            generate_rotated_record_pin_wide(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide record-pin generation: {e}"))?;
        // The committed makeSovereign row is the DEPLOYED KEYED member
        // (`CarrierComposed.makeSovereignV3DeployedWide`, 78 PIs / +32 chip-appendix columns):
        // fill the 4 KEY_COMMIT teeth + the digest appendix from the committed pubkey octet and
        // splice the teeth claim PIs ahead of the 16 wide anchors. The other record-pin members
        // commit the bare wide record-pin shape (no rider).
        if matches!(lead, Effect::MakeSovereign) {
            append_sovereign_key_commit_rider(&mut t, &mut d)
                .map_err(|e| format!("wide record-pin generation: {e}"))?;
        }
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
    } else if matches!(lead, Effect::RevokeDelegation { .. }) {
        // ⚑ THE REVOKED-SET GROW-GATE, WIRED. `revokeVmDescriptor2R24` declares TWO map-ops on the
        // limb-37 revoked-root group (`revokedFreshOp .absent` + `revokedInsertOp .aafiInsert`), and
        // this dispatch used to drop a RevokeDelegation into the bare transfer-shape arm below, which
        // supplies NO map heap. Result: `map op 0: no witness heap with root8 …` — revokeDelegation
        // was UNPROVABLE on the deployed wide path, and the SDK's own
        // `wide_completeness_ledger::provability_scoreboard_deployed_wide_path` had been printing it
        // as `[UNPROVABLE]` for exactly that reason. The producer that fills the group and returns the
        // openable BEFORE leaf-set already existed —
        // `generate_rotated_revoke_trace_with_revoked_tree` — with ZERO callers outside one
        // `circuit/tests` file. This is the call.
        //
        // ⚠ NAMED RESIDUAL: the BEFORE revoked set is `&[]` here, exactly as the note-spend arm above
        // parks its revocation ancestor — every live `RotationWitness` on this route carries
        // `empty_revoked_root_8()`, so an openable set with prior members needs the same threading the
        // nullifier set got (`before_nullifiers`) and does not exist yet. A second revoke against a
        // non-empty committed revoked root still fails closed (loudly, on the root mismatch), never
        // silently.
        generate_rotated_revoke_trace_with_revoked_tree(
            initial_state,
            effects,
            before,
            after,
            caveat,
            &[],
        )
        .map(|(mut t, base_pis, heaps)| {
            let d = append_wide_carriers(&mut t, base_pis, GRAD_ROT_WIDTH);
            (t, d, heaps)
        })
        .map_err(|e| format!("wide revoke revoked-set generation: {e}"))?
    } else if matches!(lead, Effect::BridgeMint { .. }) {
        // The felt mint-hash pin member (51 base PIs) — no longer the bare transfer shape.
        let (t, d) =
            generate_rotated_bridge_mint_wide(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide bridge-mint generation: {e}"))?;
        (t, d, vec![])
    } else if matches!(lead, Effect::SetField { field_idx, .. } if *field_idx >= 8) {
        // setFieldDyn carries the DISTINCT 581-wide V1Face geometry + a mem-boundary witness
        // (NOT map_heaps); the dedicated block below overrides these placeholders.
        (Vec::new(), Vec::new(), Vec::new())
    } else if matches!(lead, Effect::Custom { .. }) {
        generate_rotated_custom_wide(initial_state, effects, before, after, caveat)
            .map(|(t, d)| (t, d, vec![]))
            .map_err(|e| format!("wide custom generation: {e}"))?
    } else if let Some(route) = cap_write_route {
        // ⚑ THE CAP-OPEN *WRITE* ARM — the witnessed cap-WRITE family, on the committed member the
        // light-client wire ACCEPTS. `name` above already resolved to `route.key`, so this lays the
        // matching shape: the genuine rotated base (nonce-TICK — NO freeze patch, every write wrapper
        // rides the tick face), the cap-open READ crown off the REBUILT c-list tree, the member's
        // after-spine, and the 8-felt wide carriers. NO map heaps: these members declare `map_ops == 0`
        // and the write is forced by the descriptor's own depth-16 `node8` fold.
        let w = cap_write.ok_or_else(|| {
            "wide cap-write prover: the cap-open WRITE route was resolved without a witness"
                .to_string()
        })?;
        let (mut t, base_pis) =
            generate_rotated_effect_vm_trace(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide cap-write base trace: {e}"))?;
        let d = generate_rotated_cap_write_capopen_wide(&mut t, base_pis, &route, w)?;
        (t, d, Vec::new())
    } else if let Some((needs_write_witness, needs_patch)) = cap_write_wide_plan(lead) {
        // THE WITNESSLESS cap-WRITE FAMILY. attenuate / revokeCapability FAIL CLOSED here: their AFTER
        // cap-root is an in-circuit cap-tree write, the bare member both leaves it unbound (`map_ops ==
        // 0` since the Merkle-spine flag day) and is light-client FORBIDDEN, and without the holder's
        // c-list there is no membership to open. grantCap's authority-only base carries no write, so it
        // rides the nonce-FREEZE patch + the bare wide carriers (⚠ on a member the wire still refuses —
        // thread a c-list to take the `delegateWriteCapOpen` INSERT route).
        if needs_write_witness {
            return Err(format!(
                "wide cap-write prover: effect {lead:?} performs an in-circuit cap-tree write, but no \
                 CapWriteWideWitness (the holder's 7-field c-list + the consumed cap's slot_hash) was \
                 threaded. The honest route is the committed cap-open WRITE member '{}' — resolve it by \
                 threading the witness. FAILS CLOSED: the bare member '{base_name}' neither binds the \
                 post-cap-root (it declares no map ops and carries no cap-open spine) nor rides the \
                 light-client wire (it is a forbidden plain cap descriptor), so there is no fabricated \
                 post-cap-root to publish.",
                cap_write_capopen_route(lead).map_or("<none>", |r| r.key)
            ));
        }
        let (mut t, base_pis) =
            generate_rotated_effect_vm_trace(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide cap-write base trace: {e}"))?;
        let d = if needs_patch {
            patch_attenuate_base_for_cap_open(&mut t, &base_pis)
                .map_err(|e| format!("wide cap-write nonce-freeze patch: {e}"))?
        } else {
            base_pis
        };
        let d = append_wide_carriers(&mut t, d, GRAD_ROT_WIDTH);
        (t, d, Vec::new())
    } else if matches!(lead, Effect::Mint { .. }) {
        // supplyMint (`sel::MINT` → `supplyMintVmDescriptor2R24`): the committed row is UNWRAPPED
        // (62 = 46 base + 16 anchors — the Lean `supplyMintV3` was never rc-wrapped, exactly like
        // the cap-open family), so lift the 4 dsl rc PIs off the transfer-shape emission (they sit
        // between the base 46 and the 16 wide anchors). The rc COLUMNS stay in the trace (zero /
        // unpinned on this member).
        let (t, mut d) =
            generate_rotated_transfer_shape_wide(initial_state, effects, before, after, caveat)
                .map_err(|e| format!("wide supply-mint generation: {e}"))?;
        d.drain(ROT_PI_COUNT..ROT_PI_COUNT + DFA_RC_LEN);
        (t, d, vec![])
    } else {
        // THE AVAILABILITY-WELD PAD (GAP #4, wide leg): the resolved committed WIDE row for a
        // hardened `…-v1-avail` member (the post-retarget `transferVmDescriptor2R24` row) demands
        // the avail-padded geometry — witness limbs at `[V1_WIDTH, V1_WIDTH + pad)`, every
        // appendix + carrier base shifted by the pad. Descriptor-name-driven: 0 for every bare
        // member (byte-identical legacy path).
        let avail_pad = avail_pad_for_descriptor_name(&desc.name);
        let (t, d) = generate_rotated_transfer_shape_wide_avail(
            avail_pad,
            initial_state,
            effects,
            before,
            after,
            caveat,
        )
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

    // THE S2 + E1 DELETION (Epoch 1): the committed wide registry rows are S2-COMPACTED (the two
    // dead 1-felt chains) and then E1-COMPACTED (the dead v1-face bands) — drop the same columns the
    // Lean emit deleted, BEFORE the descriptor-derived tail pairing below (which reasons in the
    // committed compact geometry). E1 follows S2 (its kill-set is in the S2-compacted coordinates).
    compact_s2_columns(&mut trace, name)?;
    compact_e1_columns(&mut trace, name)?;

    // THE POST-REGEN REGISTRY TAIL (hoisted from `rotation_witness::mint_rotated_participant_leg`
    // so EVERY route through this spine emits the committed shape): the committed row may carry
    // claim PIs (+ matching teeth columns) PAST what the per-family producer emits — derived from
    // the descriptor, never hardcoded (members differ: the teeth transfer row, the KEY_COMMIT
    // sovereign — filled in its arm above — the factory octet pins all carry different totals).
    // The claim PIs sit AHEAD of the 16 wide anchors (`carrier_pin_twin::insert_tail_claim_pins`
    // geometry), the teeth columns at the wide end.
    let emitted_pis = dpis.len();
    let row_width = trace
        .first()
        .map(Vec::len)
        .ok_or_else(|| "wide rotated prover: empty wide trace".to_string())?;
    let pi_tail = desc
        .public_input_count
        .checked_sub(emitted_pis)
        .ok_or_else(|| {
            format!(
                "wide rotated prover: descriptor '{}' PI count {} < the wide producer's {}",
                desc.name, desc.public_input_count, emitted_pis
            )
        })?;
    let raw_col_tail = desc.trace_width.checked_sub(row_width).ok_or_else(|| {
        format!(
            "wide rotated prover: descriptor '{}' trace width {} < the wide producer's {}",
            desc.name, desc.trace_width, row_width
        )
    })?;
    // THE GENTIAN REFUSE-WELD EXCLUSION. The flag-day welds the per-tag floor-refuse decode
    // witnesses (bit/inv/OR/floor) onto every deployed BARE cohort member's `trace_width`. Those
    // columns are NOT producer-emitted exposure teeth — they carry no claim PI, they are the
    // floor-refuse GATE, filled from the zero-resized headroom by
    // `bare_floor_refuse_weld::fill_refuse_aux` at prove time (`descriptor_ir2` build, after
    // `fill_chip_lanes`). So they must NOT enter the exposure 1:1 pairing: subtract them from the
    // teeth-column tail before matching it against the claim-PI tail.
    //
    // The widen is HETEROGENEOUS across the post-GAP-1-6 cohort, so it MUST be derived PER-MEMBER
    // from the descriptor's own committed floor-refuse gates (`refuse_weld_widen` = `trace_width −
    // aux_base`), never a fixed constant. The two avail-hardened members (transfer/burn) ride the
    // refuse block at the very top of the trace → widen 45; the other 34 members carry a 3-column
    // dead stride-tail above the block → widen 48. A fixed `REFUSE_WELD_WIDEN` (45) is correct only
    // for the avail members: it underflowed the tail for teeth-less members like IncrementNonce
    // (raw_col_tail 48 − 45 = 3 ≠ 0 = pi_tail → "tail mismatch"). The per-member widen restores
    // `col_tail = pi_tail` for every member (48 − 48 = 0 for IncrementNonce; 47 − 45 = 2 for the
    // Transfer membership-teeth pair).
    let refuse_aux_cols = if desc
        .name
        .contains(bare_floor_refuse_weld::REFUSE_WELD_SUFFIX)
    {
        bare_floor_refuse_weld::refuse_weld_widen(&desc)
    } else {
        0
    };
    let col_tail = raw_col_tail.checked_sub(refuse_aux_cols).ok_or_else(|| {
        format!(
            "wide rotated prover: refuse-welded descriptor '{}' teeth-column tail {raw_col_tail} < \
             the {refuse_aux_cols} gate-internal refuse-aux columns — the weld geometry is \
             inconsistent with the producer shape",
            desc.name
        )
    })?;
    if pi_tail != col_tail {
        return Err(format!(
            "wide rotated prover: descriptor '{}' tail mismatch — {pi_tail} claim PI(s) vs \
             {col_tail} teeth column(s) past the wide producer's shape (the exposure regen pairs \
             them 1:1)",
            desc.name
        ));
    }
    if pi_tail > 0 {
        match lead {
            // The committed transfer row (`CarrierComposed.transferV3MembershipWide`): the
            // membership-teeth pair `(sender_leaf, authorized_root)` — 2 constant teeth columns
            // past the carriers (row-0-pinned) + 2 claim PIs ahead of the 16 anchors. `None`
            // fills the ZERO pair (the no-caveat sentinel the fold's membership arm refuses to
            // bind — a bundle claim never equals the zero pair for a real member).
            Effect::Transfer { .. } if pi_tail == 2 => {
                let (sender_leaf, authorized_root) =
                    membership_teeth.unwrap_or((BabyBear::ZERO, BabyBear::ZERO));
                for row in trace.iter_mut() {
                    row.push(sender_leaf);
                    row.push(authorized_root);
                }
                let insert_at = emitted_pis - 16; // ahead of the 16 wide anchor PIs
                let mut spliced = Vec::with_capacity(emitted_pis + 2);
                spliced.extend_from_slice(&dpis[..insert_at]);
                spliced.push(sender_leaf);
                spliced.push(authorized_root);
                spliced.extend_from_slice(&dpis[insert_at..]);
                dpis = spliced;
            }
            other => {
                return Err(format!(
                    "wide rotated prover: committed descriptor '{}' demands {pi_tail} tail PI(s) \
                     past the wide producer's {emitted_pis} for lead {other:?} — this dispatcher \
                     has no producer fill for that member's tail (mint it through its dedicated \
                     carrier minter); refusing to guess",
                    desc.name
                ));
            }
        }
    }
    debug_assert_eq!(dpis.len(), desc.public_input_count);

    Ok((desc, trace, dpis, map_heaps, mem_boundary))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
    use std::collections::BTreeSet;

    // ⚑ DELETED 2026-07-31 — `wide_chip_lookups_are_self_consistent_after_lane_fill`, together with
    // its subject `generate_rotated_transfer_wide` and the committed one-row descriptor it parsed
    // (`WIDE_TRANSFER_STAGED_TSV` / `circuit/descriptors/rotation-wide-transfer-staged.tsv`). The
    // descriptor was a diverged fork of `WIDE_REGISTRY_STAGED_TSV` row 0 with no production
    // consumer, and the producer had no callers outside this module and one deleted flip test.

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
                    // the THREE WELDED CAPACITY-SATISFACTION descriptors — escrow
                    // (`settleEscrowSatVmDescriptor2R24`, tag 17), discharge
                    // (`dischargeSatVmDescriptor2R24`, tag 18) and vault
                    // (`vaultSatVmDescriptor2R24`, tag 19) — are DECLARATION-ROUTED, not effect-routed.
                    // A declared-capacity turn executes AS a plain transfer, so the effect→descriptor
                    // resolvers (`rotated_descriptor_name` / `rotated_descriptor_name_for_effect`) name
                    // its BARE member; the flag-day refuse then makes it UNSAT there, and the
                    // declaration-keyed `rotated_descriptor_name_for_declared_{escrow,discharge,vault}`
                    // (unified: `…_for_declared_capacity`) names the satisfaction member it MUST take.
                    // Like the fee-in-proof / cap-open members they are reached by a SEPARATE resolver
                    // family (keyed on the caveat manifest, not the effect kind), so they are excluded
                    // from the effect-resolver cohort audit and covered by the positive
                    // declared-resolver assertions below.
                    && s != &"settleEscrowSatVmDescriptor2R24"
                    && s != &"dischargeSatVmDescriptor2R24"
                    && s != &"vaultSatVmDescriptor2R24"
            })
            .collect();
        // The FULL set of registry member names (no exclusions) — used to assert the declaration-routed
        // capacity members are genuine committed rows, not phantom targets.
        let registry_full: BTreeSet<&str> = V3_STAGED_REGISTRY_TSV
            .lines()
            .filter_map(|l| l.split('\t').next())
            .filter(|s| !s.is_empty())
            .collect();
        assert_eq!(
            registry.len(),
            38,
            "the rotated resolver cohort has 38 members: the original 36 + the DEDICATED supply-mint \
             (`supplyMintVmDescriptor2R24`, SUPPLY-MODEL.md Stage 2b — `sel::MINT`-routed) + the \
             single-tick grain turn (`grainTurnVmDescriptor2R24`, `sel::GRAIN_TURN`-routed); cap-open \
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

        // The DECLARATION-keyed resolver family reaches the three capacity-satisfaction members (the
        // liveness route that complements the flag-day refuse). A settle/discharge/vault executes AS a
        // zero-amount Transfer; the declared-capacity resolver names its satisfaction descriptor. This
        // is the positive coverage for the members excluded from the effect-resolver audit above — the
        // satisfaction cohort IS covered, by its own (manifest-keyed) resolver family.
        let settle = Effect::Transfer {
            amount: 0,
            direction: 0,
        };
        for (tags, want) in [
            (
                super::super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
                SETTLE_ESCROW_SAT_DESCRIPTOR_NAME,
            ),
            (
                super::super::pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
                DISCHARGE_SAT_DESCRIPTOR_NAME,
            ),
            (
                super::super::pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
                VAULT_SAT_DESCRIPTOR_NAME,
            ),
        ] {
            assert!(
                registry_full.contains(want),
                "the declared-capacity target {want} is a committed registry member"
            );
            assert_eq!(
                rotated_descriptor_name_for_declared_capacity(&settle, &[tags]),
                Some(want),
                "the declared-capacity resolver routes tag {tags} to its satisfaction descriptor {want}"
            );
        }
        // A declared-capacity turn with NO capacity tag falls back to the deployed-default effect route
        // (deployed-identical) — the declaration route never HIDES a bare member.
        assert_eq!(
            rotated_descriptor_name_for_declared_capacity(&settle, &[]),
            rotated_descriptor_name_for_effect(&settle),
            "no capacity tag ⟹ the declaration route is deployed-identical"
        );
        // Each single-tag resolver agrees with the unified capacity route on its own tag.
        assert_eq!(
            rotated_descriptor_name_for_declared_escrow(
                &settle,
                &[super::super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW]
            ),
            Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME)
        );
        assert_eq!(
            rotated_descriptor_name_for_declared_discharge(
                &settle,
                &[super::super::pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION]
            ),
            Some(DISCHARGE_SAT_DESCRIPTOR_NAME)
        );
        assert_eq!(
            rotated_descriptor_name_for_declared_vault(
                &settle,
                &[super::super::pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT]
            ),
            Some(VAULT_SAT_DESCRIPTOR_NAME)
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
            rotated_descriptor_name(super::super::columns::sel::GRAIN_TURN).unwrap(),
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
        assert_eq!(reached.len(), 38, "the resolvers reach 38 distinct names");
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

    /// Rust re-check of the Lean-generated table's complete tiling — an end-to-end
    /// artifact-integrity tooth over the full pre-limb layout: every emitted region assembled,
    /// sorted, and required to be EXACTLY `0..NUM_PRE_LIMBS`. A regen that drops a region,
    /// duplicates a column, or emits a `NUM_PRE_LIMBS` its region lists do not cover fails here.
    ///
    /// ⚑ Every region is now READ from `layout_generated`. Until 2026-07-31 the non-group regions
    /// were hand-listed here (`[176, 177]` pads, `113 + k` for `k in 0..56` field lanes) — the
    /// 178-geometry restated beside the generated group table. The nine-lane epoch consumed both
    /// pads into the fields NONET and this tooth went red for the one region it was not reading
    /// from Lean, which is the drift it was written to catch, pointed at itself.
    ///
    /// ⚑ And it happened AGAIN, one region over, at the KEY NONET epoch (`76c3f7b9b`,
    /// `NUM_PRE_LIMBS` 184 → 187). The three new columns are the carrier octets' ninth lanes
    /// (184/185/186 = `B_{CHILD_VK,CONTRACT_HASH,PUBKEY}_NINTH_LANE`), which Lean emits as their
    /// OWN region — `ROTATED_OCTET_NINTH_LANES` — precisely because they are not adjacent to the
    /// octets they complete. This tooth assembled every region except that one and reported a
    /// 184-column cover of a 187-column layout. The repair is to extend the region, never to move
    /// the `0..NUM_PRE_LIMBS` expectation: the expectation is the Lean export.
    #[test]
    fn rotated_layout_is_a_complete_disjoint_tiling() {
        let mut occ: Vec<usize> = Vec::new();
        // scalars with no completion group: r0/r1/r2, fields[0..7] lane-0, lifecycle/epoch/height/disc/mode
        occ.extend(ROTATED_SINGLES);
        for g in ROTATED_GROUP_TABLE {
            occ.extend(g);
        }
        // carrier-material octets (each base .. base+8)
        for base in ROTATED_OCTET_BASES {
            for k in 0..8 {
                occ.push(base + k);
            }
        }
        // ...and each octet's NINTH lane. NOT adjacent to its octet (184/185/186 sit past the
        // fields nonet), so this is a separate emitted region and must be extended separately —
        // reconstructing it as `base + 8` would put it back on top of the octet next door.
        occ.extend(ROTATED_OCTET_NINTH_LANES);
        occ.extend(ROTATED_FIELDS_LANE_COLS);
        occ.extend(ROTATED_CELLS_COMPLETION);
        occ.extend(ROTATED_PADS);
        occ.sort_unstable();
        let expected: Vec<usize> = (0..NUM_PRE_LIMBS).collect();
        assert_eq!(
            occ, expected,
            "rotated pre-iroot layout must be a complete disjoint tiling of 0..{NUM_PRE_LIMBS} \
             (matches Lean rotated187_legal + rotated187_complete)"
        );
        // The named octet bases the rest of this module reads ARE the emitted octet list — the one
        // place a consumer could still drift off the table it just checked.
        assert_eq!(
            ROTATED_OCTET_BASES,
            [B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, B_PUBKEY_OCTET]
        );
        // ...and the same for the ninth lanes, POSITIONALLY parallel to the bases above (lane 8 of
        // octet `i` is `ROTATED_OCTET_NINTH_LANES[i]`, not `ROTATED_OCTET_BASES[i] + 8`). This is
        // what makes the extend above a tiling claim rather than three loose columns: the owner
        // key's ninth lane (the Ed25519 sign bit) is `B_PUBKEY_NINTH_LANE`, and it is covered.
        assert_eq!(
            ROTATED_OCTET_NINTH_LANES,
            [
                B_CHILD_VK_NINTH_LANE,
                B_CONTRACT_HASH_NINTH_LANE,
                B_PUBKEY_NINTH_LANE
            ]
        );
        // The nine-lane epoch left NO spare column: the tiling above is only complete because the
        // pads are gone. Stated so a future bump that re-introduces a pad has to say so here.
        assert!(
            ROTATED_PADS.is_empty(),
            "the nine-lane geometry consumed both former pads (176, 177) into the fields nonet"
        );
    }

    /// The v1 EffectVM face width is still hand-computed in `columns.rs` (`AUX_BASE + NUM_AUX`); this
    /// pin guards that lone hand copy against the Lean export until Step 8 emits the v1 sel/state face.
    ///
    /// The group-table mirror tooth that used to live here (`hand_written_group_table_mirrors_the_lean_export`,
    /// cross-checking the HAND `PERMS_GROUP`/`VK_GROUP`/`REVOKED_ROOT_GROUP` integers against the Lean
    /// export) is GONE: the faithful-8 group table is now Lean-authored (`ROTATED_GROUP_TABLE`, a
    /// projection of the proven-`Legal` `rotated178`), so the completion-lane aliasing the setPermissions/
    /// setVK UNSAT bug lived in is disjoint-by-construction — unrepresentable, not merely guarded.
    #[test]
    fn v1_face_width_matches_lean_export() {
        use crate::effect_vm::layout_generated as lean;

        assert_eq!(
            V1_WIDTH,
            lean::EFFECT_VM_WIDTH,
            "V1_WIDTH (columns AUX_BASE + NUM_AUX) vs Lean EFFECT_VM_WIDTH"
        );
    }

    /// THE GROUP-TABLE DISJOINTNESS TOOTH: no two faithful-8-felt roots may share a column. Two
    /// groups overlapping means one committed digest's felt IS another's, so forging one forges the
    /// other — the completion felts are precisely the reused-slot region the base widens opened, so
    /// this is the standing guard that a future re-lay does not collide them.
    #[test]
    fn faithful8_groups_are_pairwise_disjoint() {
        let mut seen = std::collections::HashMap::<usize, usize>::new();
        for (gi, group) in ALL_FELT8_GROUPS.iter().enumerate() {
            for &col in group.iter() {
                if let Some(prev) = seen.insert(col, gi) {
                    panic!(
                        "faithful-8-felt column {col} is shared by group {prev} and group {gi} — \
                         two committed roots would alias the same felt"
                    );
                }
            }
        }
    }
}
