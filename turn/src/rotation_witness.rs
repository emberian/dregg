//! # `rotation_witness` — the per-turn ROTATION producers (the deferred long pole).
//!
//! `docs/ROTATION-CUTOVER.md` §5 items 3-5 name three witness columns of the rotated
//! state block that no v1 column carries, and that no producer existed for: `cells_root`
//! (the turn-level boundary view over present cells), `iroot` (the MMR root over the
//! receipt log — whole-history non-omission, Lean `mroot_injective` /
//! `metatheory/Dregg2/Lightclient/MMR.lean`), and the `lifecycle` / `epoch` scalar limbs.
//!
//! The cutover doc is explicit that these were DELIBERATELY UNBUILT: a producer is only
//! validatable against the rotated trace builder that consumes it, and that builder is the
//! flip's act. THIS module is that producer, built TOGETHER with its consumer (the
//! circuit-side rotated trace builder + the cell≡circuit differential in
//! `circuit/tests/effect_vm_rotation_flip.rs`): the producer derives the limbs from the
//! REAL executed turn's `RecordKernelState` (`Ledger` after-state + the receipt-hash log),
//! the differential proves the limbs it derives EQUAL the limbs the circuit trace carries,
//! and the rotated transfer descriptor (`transferVmDescriptor2R24`) proves+verifies over a
//! trace welded to exactly these values.
//!
//! ## The rotated block (R = 24, CONFIRMED — `ROTATION-CUTOVER.md` §2b)
//!
//! The 32 pre-iroot limbs ride in the absorption order the Lean keystone
//! (`EffectVmEmitRotationV3.preLimbsAt`, `EffectVmEmitRotationR.wireCommitR`) pins:
//!
//! ```text
//!   cells_root · r0..r23 · cap_root · nullifier_root · commitments_root · heap_root
//!              · lifecycle · epoch · committed_height · iroot   (LAST)
//! ```
//!
//! The register file welds where the datum already lives in the v1 state block
//! (`EffectVmEmitRotationV3.weldsAt`): `r0 ↔ balance_lo` · `r1 ↔ nonce` · `r2 ↔ balance_hi`
//! · `r3..r10 ↔ fields[0..7]` · `cap_root ↔ cap_root`. The producer fills those welded
//! limbs with the SAME felt encodings the v1 trace uses (`split_u64`, `BabyBear::new`), so
//! the rotated trace's weld gates `colEq` are satisfied by construction; the remaining
//! limbs (`cells_root`, the map roots, `lifecycle`, `epoch`, `committed_height`, `iroot`,
//! and `r11..r23`) are witness-carried and commitment-bound — THIS module produces them.
//!
//! ## Honest boundary notes
//!
//! * The `iroot` MMR is a left-leaning Poseidon2 fold over the per-position receipt
//!   leaves — the Rust twin of the Lean MMR whose root `mroot_injective` makes
//!   tamper/truncate/extend/reorder all move (`MMR.lean:313`). No Rust MMR primitive
//!   existed before this module (`ROTATION-CUTOVER.md` §5 item 4).
//! * `cells_root` is the sorted-Poseidon2 boundary root over the present cells' existence
//!   leaves (`dregg_circuit::heap_root` — the SAME tree the heap domain commits to), the
//!   `boundary_root_derived` analogue at the turn level (`UNIVERSAL-MEMORY.md`).
//! * The per-cell scalar limbs (balance/nonce/fields/cap_root/lifecycle/epoch/height)
//!   read a SINGLE cell's `RecordKernelState` — the rotated per-effect descriptor is a
//!   per-cell shape (the v1 state block is one cell's before/after). The turn-level
//!   `cells_root` and `iroot` are the same for every effect row of the turn.

use crate::action::Effect;
use dregg_cell::commitment::{compute_authority_digest_8, compute_canonical_capability_root_felt};
use dregg_cell::{Cell, Ledger, lifecycle::CellLifecycle};
use dregg_circuit::effect_vm::{fold_bytes32_to_bb, split_u64};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{compute_heap_root_entries, empty_heap_root};
use dregg_circuit::poseidon2::{hash_bytes, hash_many};

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap_root · nullifier_root ·
/// commitments_root · heap_root · lifecycle · epoch · committed_height · lifecycle_disc ·
/// perms_digest · vk_digest · mode · fields_root). Matches Lean `preLimbsAt_length = 37` at R = 24,
/// after the WAVE-3 mode/fields-root flag-day widening (NUM_PRE_LIMBS 35→37 — the committed mode byte +
/// fields_root digest sub-limbs, the NEW LAST pre-iroot limbs).
pub const NUM_PRE_LIMBS: usize = 1 + NUM_REGISTERS + 4 + 3 + 5 + 30; // v10: 1 + 24 + 4 + 3 + 5 + 30 = 67 (+30 faithful-8-felt completion limbs 37..66)

/// The collection id under which a present-cell existence leaf is keyed in the cells tree.
const CELLS_COLLECTION: u32 = 0;

/// One turn's rotated state-block witness for a single cell's before/after RecordKernelState.
///
/// `pre_limbs` is the 32-limb absorption vector in the Lean-pinned order; `iroot` is the
/// MMR root absorbed LAST. `state_commit = wireCommitR(pre_limbs, iroot)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotationWitness {
    /// The 32 pre-iroot limbs, in absorption order.
    pub pre_limbs: Vec<BabyBear>,
    /// The receipt-index MMR root (absorbed last).
    pub iroot: BabyBear,
    /// The chained state commitment `wireCommitR(pre_limbs, iroot)`.
    pub state_commit: BabyBear,
    /// Light-client conservation: the per-cell ASSET CLASS folded from this
    /// cell's committed `token_id`
    /// (`dregg_circuit::block_conservation::fold_token_id_to_asset`, dregg3:
    /// AssetId := issuer-cell). This is the EXACT fold the executor's per-asset
    /// collector keys on (`TurnExecutor::asset_class_for_cell`), so the
    /// proof-bound class (surfaced as `PI[v3::ASSET_CLASS]` when the BEFORE
    /// witness carries it) agrees with the ledger-derived class by construction.
    /// The prover threads this into the rotated v1 sub-trace's
    /// `EffectVmContext.asset_class` so the proof COMMITS to its genuine asset
    /// class, making the light-client per-asset partition non-trivial for
    /// multi-asset turns.
    pub asset_class: BabyBear,
}

/// Felt-encode a cell's signed balance LOW limb — the `r0 ↔ balance_lo` weld value,
/// byte-identical to the v1 trace (`CellState::compute_commitment`'s `split_u64`).
#[inline]
pub fn balance_lo_felt(balance: i64) -> BabyBear {
    split_u64(balance as u64).0
}

/// Felt-encode a cell's signed balance HIGH limb — the `r2 ↔ balance_hi` weld value.
#[inline]
pub fn balance_hi_felt(balance: i64) -> BabyBear {
    split_u64(balance as u64).1
}

/// Felt-encode the nonce — the `r1 ↔ nonce` weld value.
#[inline]
pub fn nonce_felt(nonce: u64) -> BabyBear {
    BabyBear::new((nonce & 0x7FFF_FFFF) as u32)
}

/// The canonical scalar limb of a cell's lifecycle: the discriminant folded with its
/// payload bytes so two distinct lifecycle states (Live / Sealed / Destroyed / …) yield
/// distinct limbs — the in-circuit twin of `cell::commitment::hash_lifecycle_into`'s
/// anti-omission tooth (a malicious executor must not present a Destroyed cell as Live).
pub fn lifecycle_felt(lc: &CellLifecycle) -> BabyBear {
    // The variant discriminant (a distinct base value per state) folded with payload, now in the
    // FELT domain (`dregg_circuit::poseidon2::lifecycle_payload_felt`) so the in-circuit
    // lifecycle-payload hash gate (`EffectVmEmitRotationV3.lifecyclePayloadHashGate`) can RECOMPUTE
    // it from the LIGHT-CLIENT-KNOWN inputs — the disc (gate-pinned), the 32-byte payload hash split
    // into the SAME 8 felts the light client holds as `h8(reason)`, and the `at` height (turn-header
    // `block_height`). The prior byte-packed `hash_bytes` had a 4-byte packing no felt view matched —
    // the SNARK-hostile divergence the refusal `fields_root` openable fix hit. MUST agree byte-for-byte
    // with `dregg_cell::commitment::v9_lifecycle_felt` (the limb-29 the per-cell commitment binds).
    use dregg_circuit::poseidon2::lifecycle_payload_felt;
    match lc {
        // `Live` carries no payload — a bare disc felt (the all-zero payload + at fold).
        CellLifecycle::Live => lifecycle_payload_felt(0, &[0u8; 32], 0),
        CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } => lifecycle_payload_felt(1, reason_hash, *sealed_at),
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => {
            // Migrated keeps a richer payload (to + attestation) — fold its two 32-byte hashes via
            // the same felt-domain sponge, distinct from the light-client movers this gate forces.
            let mut inputs: Vec<BabyBear> = Vec::with_capacity(18);
            inputs.push(BabyBear::new(2));
            inputs.extend_from_slice(&fold_bytes32_to_bb_limbs(to.as_bytes()));
            inputs.extend_from_slice(&dregg_circuit::effect_vm::bytes32_to_8_limbs(attestation));
            inputs.push(BabyBear::new((*migrated_at & 0x7FFF_FFFF) as u32));
            dregg_circuit::poseidon2::hash_many(&inputs)
        }
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => lifecycle_payload_felt(3, death_certificate_hash, *destroyed_at),
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => lifecycle_payload_felt(4, checkpoint_hash, *archived_through),
    }
}

/// Split a 32-byte hash into 8 felts (the `bytes32_to_8_limbs` shape) — the migration `to` cell-id
/// fold, keeping the migrated arm felt-domain too.
#[inline]
fn fold_bytes32_to_bb_limbs(b: &[u8; 32]) -> [BabyBear; 8] {
    dregg_circuit::effect_vm::bytes32_to_8_limbs(b)
}

/// The committed lifecycle DISCRIMINANT limb (the `u8 0..4` — Live=0, Sealed=1, Migrated=2,
/// Destroyed=3, Archived=4) as a bare felt, committed BESIDE the opaque `lifecycle_felt`. The
/// in-circuit twin of `EffectVmEmitRotationV3.B_DISC` (the disc flag-day's new last pre-iroot limb):
/// the per-effect disc-transition gate FORCES this column to the effect's mandated discriminant, so a
/// ledgerless light client cannot be fooled about the lifecycle STATE (a frozen seal / a resurrection
/// / a wrong-disc archive). UNLIKE `lifecycle_felt`, this is the raw discriminant (not a hash), so it
/// can be gated to a constant in-circuit.
pub fn lifecycle_disc_felt(lc: &CellLifecycle) -> BabyBear {
    let disc: u8 = match lc {
        CellLifecycle::Live => 0,
        CellLifecycle::Sealed { .. } => 1,
        CellLifecycle::Migrated { .. } => 2,
        CellLifecycle::Destroyed { .. } => 3,
        CellLifecycle::Archived { .. } => 4,
    };
    BabyBear::new(disc as u32)
}

/// The committed PERMISSIONS-DIGEST limb (`B_PERMS = 33`, the WAVE-2 perms/VK flag-day). Delegates to
/// the CANONICAL `dregg_cell::commitment::perms_digest_felt` (the single definition, no Rust copy to
/// differential): `bytes32_to_8_limbs(blake3(postcard(permissions)))[0]` — BYTE-IDENTICAL to the
/// deployed `params[0]` of a setPermissions row (`effect_vm_bridge.rs::SetPermissions` → `hash_to_8`).
/// The setPermissions weld (`EffectVmEmitRotationV3.rotateV3WithPermsVKGate`) FORCES the AFTER
/// perms-digest limb EQUAL to the in-circuit declared-param column (this felt, PI-anchored via
/// `effects_hash`), so a ledgerless light client cannot be shown a forged post-permissions.
pub fn perms_digest_felt(perms: &dregg_cell::Permissions) -> BabyBear {
    dregg_cell::commitment::perms_digest_felt(perms)
}

/// The committed VERIFICATION-KEY-DIGEST limb (`B_VK = 34`, the WAVE-2 flag-day). Delegates to the
/// canonical `dregg_cell::commitment::vk_digest_felt` — BYTE-IDENTICAL to the deployed `params[0]` of
/// a setVK row, `None` (revoke) → the all-zero limb (the deployed `vk_hash == [0; 8]` convention). The
/// setVK weld FORCES the AFTER vk-digest limb to this declared param, closing the upgrade-safety
/// (post-VK) light-client forgery.
pub fn vk_digest_felt(vk: &Option<dregg_cell::VerificationKey>) -> BabyBear {
    dregg_cell::commitment::vk_digest_felt(vk)
}

/// The committed cell-MODE limb (`B_MODE = 35`, the WAVE-3 mode/fields-root flag-day). Delegates to the
/// canonical `dregg_cell::commitment::mode_felt`: the raw `mode_flag` byte (`Hosted=0 / Sovereign=1`)
/// as a felt. The makeSovereign mode gate (`EffectVmEmitRotationV3.rotateV3WithModeGate`) FORCES the
/// AFTER mode limb to `Sovereign(1)` as a CONSTANT, so a ledgerless client cannot be shown an
/// un-promoted sovereign.
pub fn mode_felt(mode: &dregg_cell::CellMode) -> BabyBear {
    dregg_cell::commitment::mode_felt(mode)
}

/// The committed `fields_root` digest limb (`B_FIELDS_ROOT = 36`, the WAVE-3 flag-day). Delegates to
/// the canonical `dregg_cell::commitment::fields_root_felt`, which now recovers the OPENABLE
/// sorted-Poseidon2 `fields_root` (`cell::state::compute_fields_root` IS a felt root) — NOT the opaque
/// `hash_bytes(blake3_sponge)` it replaced. The refusal `.write` map-op gate
/// (`EffectVmEmitRotationV3.refusalFieldsWriteV3`) opens this limb and FORCES the AFTER fields_root to
/// `write(before_root, REFUSAL_AUDIT_KEY → audit_felt)`, so a forged post-`fields_root` is UNSAT for a
/// ledgerless light client through `verify_vm_descriptor2` ALONE (the refusal map-op generator
/// `generate_rotated_refusal_trace_with_fields_tree` threads the BEFORE leaf set as `map_heaps`).
pub fn fields_root_felt(fields_root: &[u8; 32]) -> BabyBear {
    dregg_cell::commitment::fields_root_felt(fields_root)
}

/// Felt-encode the parent-side delegation epoch — the `epoch` scalar limb.
#[inline]
pub fn epoch_felt(epoch: u64) -> BabyBear {
    BabyBear::new((epoch & 0x7FFF_FFFF) as u32)
}

/// Felt-encode the committed height — the `committed_height` scalar limb (PI-v3, §2.6).
#[inline]
pub fn committed_height_felt(height: u64) -> BabyBear {
    BabyBear::new((height & 0x7FFF_FFFF) as u32)
}

/// Pack a 32-byte root (a BLAKE3 / table-map root carried in cell state) into a single
/// BabyBear limb. The same packing the heap domain uses to lift byte roots into the field
/// (`dregg_circuit::poseidon2::hash_bytes`).
#[inline]
pub fn root_felt(root: &[u8; 32]) -> BabyBear {
    hash_bytes(root)
}

/// **THE `cells_root` PRODUCER** — the turn-level boundary view over the present cells.
///
/// The sorted-Poseidon2 root over one existence leaf per present cell (`value = 1`,
/// keyed by a felt digest of the cell id under `CELLS_COLLECTION`). Input-order
/// independent (the underlying `CanonicalHeapTree` sorts by address — see
/// `heap_root::root_is_input_order_independent`), so the root is a function of the SET of
/// present cells, never the ledger's iteration order. The empty ledger yields the empty
/// sorted-tree sentinel root.
pub fn cells_root(ledger: &Ledger) -> BabyBear {
    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    for (id, _) in ledger.iter() {
        let key = hash_bytes(id.as_bytes());
        entries.push((
            (BabyBear::new(CELLS_COLLECTION), key),
            BabyBear::ONE, // existence bit
        ));
    }
    if entries.is_empty() {
        return empty_heap_root();
    }
    compute_heap_root_entries(&entries)
}

/// **THE `iroot` PRODUCER** — the MMR root over the receipt log.
///
/// A left-leaning Poseidon2 fold over the per-position receipt leaves: each leaf is the
/// felt digest of `(position, receipt_hash)`, and the running root accumulates
/// `root := hash[root, leaf]` in chronological order. This is the Rust realization of the
/// Lean MMR whose `mroot_injective` (`MMR.lean:313`) makes the root bind the WHOLE log:
/// tampering any leaf, truncating, extending, or reordering all move the fold. The empty
/// log yields the zero root (a uniform no-op for a turn that appends nothing).
pub fn iroot(receipt_hashes: &[[u8; 32]]) -> BabyBear {
    let mut root = BabyBear::ZERO;
    for (position, rh) in receipt_hashes.iter().enumerate() {
        let leaf = hash_many(&[BabyBear::new(position as u32), hash_bytes(rh)]);
        root = hash_many(&[root, leaf]);
    }
    root
}

/// The chained rotated state commitment — the Rust twin of Lean `wireCommitR`
/// (`EffectVmEmitRotationR.lean`): the 4-wide head over the first four limbs, 3-wide chip
/// groups while ≥ 3 pre-iroot limbs remain, the iroot absorbed ALONE last. Byte-identical
/// to the chained absorption the rotated descriptor's hash sites realize
/// (`descriptor_ir2.rs::rotation_probe_trace_r`), so the producer's `state_commit` is the
/// value the rotated trace's `STATE_COMMIT` carrier MUST carry.
pub fn wire_commit(pre_limbs: &[BabyBear], iroot: BabyBear) -> BabyBear {
    assert_eq!(
        pre_limbs.len(),
        NUM_PRE_LIMBS,
        "wire_commit: {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}"
    );
    let mut d = hash_many(&[pre_limbs[0], pre_limbs[1], pre_limbs[2], pre_limbs[3]]);
    let mut col = 4;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, pre_limbs[col], pre_limbs[col + 1], pre_limbs[col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, pre_limbs[col]]);
            col += 1;
        }
    }
    hash_many(&[d, iroot])
}

/// **THE FAITHFUL 8-FELT chained rotated commitment (Phase B-ROTATION)** — the producer twin of
/// `dregg_cell::commitment::compute_canonical_state_commitment_v9_felt8`, delegating to the shared
/// `dregg_circuit::poseidon2::wire_commit_8`. Each chain step is a single arity-11 permutation over
/// the 8-felt carrier ‖ 3 limbs, exposing 8 lanes — every intermediate carrier is 8 felts (no
/// 31-bit waist). Byte-identical to the cell twin and the Lean `wireCommitR8`.
///
/// ADDITIVE: the live `wire_commit` is the 1-felt chain until the trace/PI/executor flag-day cuts
/// the proof-bound `STATE_COMMIT` to all 8 felts.
pub fn wire_commit_8(pre_limbs: &[BabyBear], iroot: BabyBear) -> [BabyBear; 8] {
    assert_eq!(
        pre_limbs.len(),
        NUM_PRE_LIMBS,
        "wire_commit_8: {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}"
    );
    dregg_circuit::poseidon2::wire_commit_8(pre_limbs, iroot)
}

/// The full witness producer for one cell's before/after state in a real turn.
///
/// `cell` is the per-cell `RecordKernelState` (after-state for the AFTER block; supply the
/// before-cell for the BEFORE block), `ledger` is the after-ledger (for `cells_root`),
/// `nullifier_root` / `heap_root` are the cell's committed map roots, and
/// `receipt_hashes` is the turn's receipt log (for `iroot`). `r11..r23` are witness-free
/// in this turn (no app data) → zero; a real app's hot scalars would fill them.
pub fn produce(
    cell: &Cell,
    ledger: &Ledger,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_hashes: &[[u8; 32]],
) -> RotationWitness {
    let mut pre_limbs = vec![BabyBear::ZERO; NUM_PRE_LIMBS];
    // limb 0: cells_root (turn-level).
    pre_limbs[0] = cells_root(ledger);
    // limbs 1..=24: r0..r23. Welded scalars first (r0,r1,r2,r3..r10), then app registers.
    pre_limbs[1] = balance_lo_felt(cell.state.balance()); // r0
    pre_limbs[2] = nonce_felt(cell.state.nonce()); // r1
    pre_limbs[3] = balance_hi_felt(cell.state.balance()); // r2
    for i in 0..8 {
        // r3..r10 ↔ fields[0..7]: the 32-byte record field packed into the field limb the
        // v1 circuit state block carries (`fold_bytes32_to_bb`, the same Horner packing).
        // FAITHFUL-COMMITMENT-LAW residual (producer twin of cell::commitment compute_rotated_pre_limbs):
        // fields[0..7] still fold 32B→1 felt (~31-bit); the 8-felt grind is TODO. Allowlisted; a
        // NET-NEW degrading fold in this commitment producer fails the gate.
        pre_limbs[4 + i] = fold_bytes32_to_bb(&cell.state.fields[i]); // ast-grep-ignore: degraded-felt-commitment
    }
    // r11..r17 (limbs 12..=18) + r23 (limb 24): THE FAITHFUL 8-FELT AUTHORITY DIGEST (H1) — the
    // ~124-bit blake3-rooted commitment folding ALL authority-bearing cell state that no other
    // rotated limb carries (permissions/VK/delegate/delegation/program/mode/token_id +
    // visibility/commitments/proved/side-table roots + fields[8..16]). limb 24 = limb-0 (historical
    // position + v1 cross-anchor); the 7 previously-zero headroom limbs 12..=18 carry limb-1..7.
    // Byte-identical to the cell-side `commitment::compute_rotated_pre_limbs` so the three-way
    // agreement holds; the chained `wireCommitR` binds all 8, the record-pin / continuity freezes
    // WELD them (GENTIAN law). r18..r22 (limbs 19..=23): remaining headroom — zero for this turn.
    let auth8 = compute_authority_digest_8(cell);
    pre_limbs[24] = auth8[0];
    for i in 0..7 {
        pre_limbs[12 + i] = auth8[1 + i];
    }
    // limb 25: cap_root (welded) — the SAME openable sorted-Poseidon2 felt the circuit's
    // `cap_root` column carries (cell and circuit compute it through the SAME impl, the A2
    // differential guards it), so the `cap_root ↔ cap_root` weld holds by construction.
    pre_limbs[25] = compute_canonical_capability_root_felt(&cell.capabilities);
    // limb 26: nullifier_root (the noteSpend shielded-set root).
    pre_limbs[26] = root_felt(nullifier_root);
    // limb 27: commitments_root (the noteCreate shielded-set root — the flag-day new limb).
    pre_limbs[27] = root_felt(commitments_root);
    // limb 28: heap_root.
    pre_limbs[28] = root_felt(&cell.state.heap_root);
    // limbs 29,30,31: lifecycle (opaque felt), epoch, committed_height.
    pre_limbs[29] = lifecycle_felt(&cell.lifecycle);
    pre_limbs[30] = epoch_felt(cell.state.delegation_epoch());
    pre_limbs[31] = committed_height_felt(cell.state.committed_height());
    // limb 32: lifecycle_disc (the WAVE-1 flag-day committed discriminant — the gated disc-transition
    // limb).
    pre_limbs[32] = lifecycle_disc_felt(&cell.lifecycle);
    // limbs 33,34: perms_digest, vk_digest (the WAVE-2 flag-day committed authority sub-limbs — the
    // setPerms / setVK welds force these to the declared param). limb-0 stays here (historical); the
    // v10 weld lands the seven completion felts at extras 37..=43 (perms) / 44..=50 (vk).
    let perms8 = dregg_cell::commitment::perms_digest_8(&cell.permissions);
    let vk8 = dregg_cell::commitment::vk_digest_8(&cell.verification_key);
    pre_limbs[33] = perms8[0];
    pre_limbs[34] = vk8[0];
    // v10 perms/vk faithful 8-felt completion (byte-identical to `commitment::compute_rotated_pre_limbs`).
    for i in 0..7 {
        pre_limbs[37 + i] = perms8[1 + i];
        pre_limbs[44 + i] = vk8[1 + i];
    }
    // limbs 35,36: mode, fields_root (the WAVE-3 flag-day committed authority sub-limbs — the
    // makeSovereign mode CONSTANT-force limb and the setFieldDyn / refusal fields-root weld limb, the
    // NEW LAST pre-iroot limbs).
    pre_limbs[35] = mode_felt(&cell.mode);
    pre_limbs[36] = fields_root_felt(&cell.state.fields_root);

    let iroot_val = iroot(receipt_hashes);
    let state_commit = wire_commit(&pre_limbs, iroot_val);
    // The per-cell asset class (the fold of the cell's committed token_id) the
    // light-client conservation partition keys on — the SAME fold the executor's
    // collector uses, so the proof-bound class agrees with the ledger class.
    let asset_class = dregg_circuit::block_conservation::fold_token_id_to_asset(cell.token_id());
    RotationWitness {
        pre_limbs,
        iroot: iroot_val,
        state_commit,
        asset_class,
    }
}

/// **THE ROTATED-LEG MINTING RECIPE (Bucket-F / PATH-PRESERVE Phase 5a).** Build a
/// [`RotatedParticipantLeg`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg) for a
/// single homogeneous-cohort turn from the real before/after actor `Cell`s: run [`produce`] over
/// each cell to derive its rotated block witness (`pre_limbs` + `iroot`), then hand those to the
/// pure-circuit
/// [`RotatedParticipantLeg::mint_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_from_block_witnesses),
/// which generates the 311-column rotated trace + 38-PI vector and proves it through the IR-v2
/// batch prover under the leaf-wrap config (so the minted `Ir2BatchProof` folds directly as a
/// `NativeBatchStark` recursion leaf). The proof self-verifies natively before return.
///
/// This lives in `dregg-turn` (NOT `dregg-circuit`) because it drives [`produce`] over
/// `dregg_cell::Cell`s, and `dregg-circuit` cannot depend on `dregg-cell` / `dregg-turn` (a
/// dependency cycle — both depend on `dregg-circuit`). It is the ONE recipe the recursion
/// consumers (lightclient / wasm / `circuit/tests/proof_economics.rs`) use to build a mandatory
/// rotated participant; it mirrors `circuit/tests/rotation_batchstark_leaf_smoke.rs`'s mint
/// sequence exactly.
///
/// `turn_id`, when `Some`, overrides the `TURN_HASH` slot of the carried PI prefix (the joint
/// aggregator's shared-turn-id projection) — pass it for joint-turn participants that must agree
/// on a shared id; pass `None` for whole-chain turns (the carried hash from the witness stands).
///
/// Fails closed if the turn's effect is not a single rotated R=24 cohort member (the generator
/// rejects a non-cohort / empty / heterogeneous slice).
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn mint_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    // The turn-context ledger snapshot: a single-cell ledger holding the after-cell (the
    // cells_root shape `produce` reads).
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_rotated_participant_leg: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map_err(|e| format!("mint_rotated_participant_leg: rotated block witness: {e}"))
    };

    RotatedParticipantLeg::mint_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
    )
}

/// **THE CUSTOM-WIDE LEG MINTING RECIPE — the production custom-binding fold plug.** Build a
/// [`RotatedParticipantLeg`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg) for
/// an [`Effect::Custom`](dregg_circuit::effect_vm::Effect::Custom) turn from the real before/after
/// actor `Cell`s, routing through the WIDE custom mint
/// ([`RotatedParticipantLeg::mint_custom_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_custom_wide_from_block_witnesses))
/// — the `customVmDescriptor2R24` leg that publishes the claimed `custom_proof_commitment` at PI
/// 46..49 — and ATTACHING the prover-side re-provable [`CustomWitnessBundle`](dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle).
///
/// This is the path that makes the custom binding REAL-FOLDED in production: the chain prover folds
/// the attached witness's sub-proof leaf into the recursion tree a PURE LIGHT CLIENT verifies, so a
/// forged `custom_proof_commitment` (one no verifying sub-proof of the bundle's PIs backs) is UNSAT
/// — rejected without any off-AIR re-execution. Build `bundle` via
/// [`CustomWitnessBundle::from_bound_custom_proof`](dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle::from_bound_custom_proof)
/// over the SAME `BoundCustomProof` whose `proof_commitment()` was threaded into the
/// `Effect::Custom`'s `proof_commitment` field at turn-build.
///
/// Fails closed if the lead effect is not `Effect::Custom`, or if the bound proof carried no
/// retained witness (a wire-reconstructed proof — `from_bound_custom_proof` returns `None`).
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn mint_custom_wide_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    bundle: dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).map_err(|e| {
        format!("mint_custom_wide_rotated_participant_leg: ledger seed failed: {e:?}")
    })?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).map_err(|e| {
            format!("mint_custom_wide_rotated_participant_leg: rotated block witness: {e}")
        })
    };

    RotatedParticipantLeg::mint_custom_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        bundle,
    )
}

/// **THE BRIDGE-MINT WIDENED-LEG minting recipe (the RIGHT G1 payment binding).** The bridge twin of
/// [`mint_custom_wide_rotated_participant_leg`]: converts the before/after `Cell`s into rotated block
/// witnesses and mints the WIDENED narrow `mintVmDescriptor2R24` leg (855-wide / 72-PI) that publishes
/// the bridge-action tuple `(nullifier, recipient, dest_federation, amount)` at PI `[46..72)`, retaining
/// the `BridgeWitnessBundle` so the chain prover folds the bridge sub-proof + segmented binding node —
/// the ACTUAL payment fields bound for a pure light client, no hash-gadget seam.
pub fn mint_bridge_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    bundle: dregg_circuit_prove::joint_turn_aggregation::BridgeWitnessBundle,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).map_err(|e| {
        format!("mint_bridge_rotated_participant_leg: ledger seed failed: {e:?}")
    })?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).map_err(|e| {
            format!("mint_bridge_rotated_participant_leg: rotated block witness: {e}")
        })
    };

    RotatedParticipantLeg::mint_bridge_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        bundle,
    )
}

/// **THE WELDED ROTATED+UMEM LEG MINTING RECIPE (STAGED, VK-RISK-FREE) — the IVC half of the
/// flag-day weld.** Like [`mint_rotated_participant_leg`], but the minted leg carries the WELDED
/// rotated+umem descriptor: it derives the SAME turn's universal-memory touch (the pre→post
/// projection diff, the single-domain cohort rows + REAL boundary via
/// [`crate::umem::umem_cohort_proving_inputs_from`]) and hands it to
/// [`RotatedParticipantLeg::mint_welded_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_from_block_witnesses),
/// which welds the umem leg INTO the rotated descriptor and proves both in ONE leaf under the
/// leaf-wrap config. The leg's 46-PI vector (the rotated commit pins) is intact, so the IVC chain
/// fold's `old_root`/`new_root` accessors keep working over the welded leg.
///
/// `before_cell`/`after_cell` are the real actor cells (their projection diff IS the umem touch).
/// Fails closed if the turn is not a single rotated R=24 cohort member, or if its umem touch is
/// multi-domain (such effects stay on the per-map path until their own cohort design).
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_umem_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use crate::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_umem: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_umem: rotated block witness: {e}"))
    };

    // The SAME transition's universal-memory touch: the pre→post projection diff as a Blum write
    // trace, bridged into the single-domain cohort rows + REAL boundary.
    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_umem: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
    )
}

/// **THE WIDE WELDED ROTATED+UMEM LEG MINTING RECIPE (STAGED, VK-RISK-FREE) — the IVC half of the
/// genuine flip precursor.** The WIDE (8-felt / ~124-bit) twin of
/// [`mint_welded_umem_rotated_participant_leg`]: it derives the SAME turn's universal-memory touch
/// (the pre→post projection diff, the single-domain cohort rows + REAL boundary) and hands it to
/// [`RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_from_block_witnesses),
/// which welds the umem leg INTO the WIDE descriptor and proves both in ONE leaf under the leaf-wrap
/// config. The leg's wide PI vector is intact (the 16 wide commit PIs ride through the additive
/// weld), so the IVC chain fold's `old_root`/`new_root` accessors keep working over the welded leg
/// AND the 8-felt anchors are preserved for the ~124-bit binding.
///
/// SCOPE: the FULL single-domain wide cohort — any effect whose WIDE producer is SAT on the bare wide
/// sovereign path (the value/field families: transfer / burn / bridgeMint / setField / setFieldDyn,
/// heap domain), routed through the shared
/// [`RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_from_block_witnesses)
/// dispatch. The cap-WRITE family (grant/attenuate/revoke — AFTER cap-root is an in-circuit cap-tree
/// MAP-OP write) needs the SEPARATE cap-open path and is a named tail; the multi-domain note/bridge
/// economic verbs stay on the multi-domain cohort path (not yet welded/folded — a named tail on the
/// narrow path too). `before_cell`/`after_cell` are the real actor cells (their projection diff IS the
/// umem touch); a multi-domain touch fails closed at `umem_cohort_proving_inputs_from`.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use crate::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem: rotated block witness: {e}"))
    };

    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_wide_umem: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
        // The value/field cohort needs no grow-gate / refusal context (heap-domain balance/field
        // moves). A note/refusal lead would thread these — but those leads are named tails here.
        None,
        None,
        // No cap-tree write witness — a cap-WRITE lead routes through the dedicated cap-write entry
        // (`mint_welded_wide_umem_cap_write_rotated_participant_leg`); reaching here it fails closed.
        None,
    )
}

/// **THE CAP-WRITE WIDE+umem WELDED LEG (STAGED, VK-RISK-FREE).** The cap-open weld twin of
/// [`mint_welded_wide_umem_rotated_participant_leg`] for the nonce-FREEZE cap-WRITE family — the
/// `grant` / `attenuate` / `revoke(Capability)` bases whose AFTER cap-root is an in-circuit cap-tree
/// `map_op` write (attenuate / revokeCapability) or a frozen authority-only pass-through (grantCap).
/// It threads the cap-tree write witness ([`CapWriteWideWitness`](dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness)
/// — the cell's c-list + the consumed anchor key + the op payload) through the SAME shared full-cohort
/// wide producer dispatch the value cohort rides, then welds the umem leg onto the WIDE descriptor —
/// purely additive, so the 8-felt (~124-bit) anchors ride through INTACT (no narrowing). A cap-WRITE
/// lead whose base carries a map_op but is given no witness — or any non-cap-WRITE lead — fails closed
/// at the dispatcher (the cap-open weld never fabricates a post-cap-root). STAGED: a welded WIDE
/// descriptor BESIDE the deployed wide registry; no VK bump, nothing on the wire.
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_cap_write_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    cap_write: &dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use crate::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem_cap_write: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem_cap_write: rotated block witness: {e}"))
    };

    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_wide_umem_cap_write: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
        None,
        None,
        Some(cap_write),
    )
}

/// **THE WIDE+umem MULTI-DOMAIN WELDED LEG (STAGED, VK-RISK-FREE) — the last family tail.** The
/// two-domain twin of [`mint_welded_wide_umem_rotated_participant_leg`] for the NOTE/BRIDGE economic
/// verbs (`NoteSpend` / `BridgeMint`) whose state touch spans TWO domains in one effect — a
/// `nullifiers` freshness insert + a `heap` balance credit. It bridges the leg's MULTI-DOMAIN
/// universal-memory touch (`pre` + the Blum op trace `ops`, the same shape the standalone multi-domain
/// cohort prover consumes) into the width-`6 + #domains` cohort rows + the REAL boundary via
/// [`crate::umem::umem_cohort_multidomain_proving_inputs_from`] (fails closed on a single-domain leg),
/// then hands it to
/// [`RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses),
/// which welds one guarded `umemOp` per domain onto the WIDE descriptor — purely additive, so the
/// 8-felt (~124-bit) anchors ride through INTACT (no narrowing). The cross-DOMAIN economic invariant
/// (credit == spent/minted value) rides the effect's rotated AIR, NOT the memory reconciliation — the
/// same division as the narrow multi-domain cohort.
///
/// `before_nullifiers` is the note-spend grow-gate's BEFORE nullifier accumulator (a `NoteSpend` lead
/// routes through the wide note-spend producer, which requires it; `BridgeMint` rides the
/// transfer-shape producer — pass `None`). `before_cell`/`after_cell` supply the rotated block
/// witnesses. STAGED: a welded WIDE descriptor BESIDE the deployed wide registry; no VK bump, nothing
/// on the wire.
#[cfg(feature = "prover")]
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_multidomain_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &[u8; 32],
    commitments_root: &[u8; 32],
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    pre: &crate::umem::UProjection,
    ops: &[crate::umem::UmemOp],
    before_nullifiers: Option<&[BabyBear]>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use crate::umem::umem_cohort_multidomain_proving_inputs_from;
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem_multidomain: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        receipt_log,
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem_multidomain: rotated block witness: {e}"))
    };

    // Bridge the leg's MULTI-DOMAIN universal-memory touch into the width-`6 + #domains` cohort rows
    // + REAL boundary (fails closed on a single-domain leg — that uses the single-domain entry).
    let inputs = umem_cohort_multidomain_proving_inputs_from(pre, ops)
        .map_err(|e| format!("mint_welded_wide_umem_multidomain: umem multi-domain inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        &inputs.domains,
        before_nullifiers,
    )
}

/// **The shared single-effect state projection onto a cell — the anti-drift weld.**
///
/// Applies ONE kernel effect's STATE change to `cell`, mirroring exactly what the executor's
/// apply leg does (`turn::executor::apply`), but as a pure cell→cell projection with no ledger /
/// journal / permission-check side effects. Both sides of the rotated record-pin gate call THIS
/// function:
///
/// * the PRODUCER (`dregg_sdk::AgentCipherclerk::prove_sovereign_turn_rotated`) projects its
///   local before-cell to the after-cell whose `compute_authority_digest_felt` seeds the rotated
///   AFTER block's `B_RECORD_DIGEST` limb (the column the descriptor's last-row pin welds to
///   rotated PI 38), and
/// * the VERIFIER (`dregg_turn::executor::verify_and_commit_proof_rotated`) projects the trusted
///   before-cell it holds and anchors `dpis[38] = compute_authority_digest_felt(post_cell)`.
///
/// If the two diverged the anchored PI 38 would not equal the prover's honest after-limb and an
/// HONEST proof would be rejected; routing both through this one function is the guarantee they
/// move together. A forged after-state (a permissions value the effect did NOT produce) makes the
/// verifier's anchored PI 38 disagree with the proof's bound after-limb ⇒ `verify_vm_descriptor2`
/// UNSAT ⇒ reject (the genuine forcing gate the Lean `rotateV3WithRecordPin` keystone names).
///
/// `cell_id` is the effect's target cell: an effect whose target is not `cell_id` is a NO-OP on
/// this cell (matching the producer/verifier per-cell projection — the rotated sovereign proof is
/// over a single cell's transition). Only the variants whose rotated record-pin descriptor is live
/// are projected; everything else is a no-op (the digest does not move, which is correct for the
/// effects that do not touch this cell's authority residue).
///
/// SetPermissions semantics MIRROR `apply_set_permissions` (`c.permissions = new_permissions`).
///
/// `block_height` is the federation height the executor applies the effect at — it is load-bearing
/// for ONE arm only (`CellSeal` writes `sealed_at = block_height` into the lifecycle, which
/// `lifecycle_felt` folds). Every other arm ignores it. Both sides MUST pass the SAME height (the
/// verifier passes `self.block_height`; the producer passes the height it proves against) or an
/// honest seal proof's lifecycle felt would not equal the verifier's anchor.
pub fn apply_effect_to_cell(
    cell: &mut Cell,
    cell_id: &dregg_cell::CellId,
    effect: &Effect,
    block_height: u64,
) {
    match effect {
        // The setPermissions BEACHHEAD (record-digest limb 24): set the cell's permissions to the
        // effect's new value — byte-identical to the executor's `apply_set_permissions`. This moves
        // `compute_authority_digest_felt` (permissions are folded into the v9 authority residue).
        Effect::SetPermissions {
            cell: target,
            new_permissions,
        } if target == cell_id => {
            cell.permissions = new_permissions.clone();
        }
        // setVK (record-digest limb 24): mirror `apply_set_verification_key`
        // (`c.verification_key = new_vk.cloned()`). The executor first rejects a VK whose declared
        // `hash != blake3(data)` — that rejection happens at the apply leg BEFORE this projection is
        // reached on the verifier side, so a turn that reaches the anchor carries an integrity-valid
        // VK; we install it verbatim. `compute_authority_digest_felt` folds `vk.hash` (commitment.rs
        // §"Verification key"), so a genuine setVK MOVES the r23 authority residue.
        Effect::SetVerificationKey {
            cell: target,
            new_vk,
        } if target == cell_id => {
            cell.verification_key = new_vk.clone();
        }
        // refusal (record-digest limb 24): mirror `apply_refusal`'s STATE writes — bump the nonce
        // and write the audit commitment into the protocol-reserved EXT `fields_root` key
        // (`REFUSAL_AUDIT_EXT_KEY >= STATE_SLOTS`). `compute_authority_digest_felt` FOLDS
        // `fields_root`, so a genuine refusal MOVES the r23 authority residue and the `refusalV3`
        // record-pin BITES (the verifier anchors PI 38 to `compute_authority_digest_felt(post_cell)`).
        Effect::Refusal {
            cell: target,
            offered_action_commitment,
            refusal_reason,
            ..
        } if target == cell_id => {
            let _ = cell.state.increment_nonce();
            let mut h = blake3::Hasher::new_derive_key("dregg-refusal-audit-v1");
            h.update(offered_action_commitment);
            match refusal_reason {
                crate::action::RefusalReason::Declined => h.update(&[0u8]),
                crate::action::RefusalReason::NoAuthority => h.update(&[1u8]),
                crate::action::RefusalReason::WindowExpired => h.update(&[2u8]),
                crate::action::RefusalReason::Custom { reason_hash } => {
                    h.update(&[3u8]);
                    h.update(reason_hash)
                }
            };
            let audit = *h.finalize().as_bytes();
            cell.state
                .set_field_ext(dregg_cell::state::REFUSAL_AUDIT_EXT_KEY, audit);
        }
        // receiptArchive (lifecycle limb 29 — see routing note below): mirror `apply_receipt_archive`'s
        // STATE write — `c.archive(checkpoint)`, which moves the lifecycle to `Archived`. The executor's
        // pre-checks (cell_id / height / live-head binding) gate the apply leg BEFORE the anchor; here
        // we replay the lifecycle transition only. NOTE: `archive` writes the LIFECYCLE, which
        // `lifecycle_felt` (limb 29) folds — NOT the r23 authority residue. The current
        // `record_pin_offset` routes receiptArchive to `B_RECORD_DIGEST`, which this write does NOT
        // move; the genuine forced limb is `B_LIFECYCLE`.
        Effect::ReceiptArchive { checkpoint, .. } if checkpoint.cell_id == *cell_id => {
            let _ = cell.archive(checkpoint);
        }
        // cellSeal (lifecycle limb 29): mirror `apply_cell_seal` (`c.seal(reason, block_height)`),
        // which moves the lifecycle to `Sealed { reason_hash, sealed_at: block_height }`. The
        // `sealed_at` is the load-bearing `block_height` dependence; `lifecycle_felt` folds both
        // `reason_hash` and `sealed_at`, so a genuine seal MOVES limb 29.
        Effect::CellSeal { target, reason } if target == cell_id => {
            let _ = cell.seal(*reason, block_height);
        }
        // cellUnseal (lifecycle limb 29): mirror `apply_cell_unseal` (`c.unseal()` → `Live`). Moves
        // limb 29 from `Sealed` back to `Live`.
        Effect::CellUnseal { target } if target == cell_id => {
            let _ = cell.unseal();
        }
        // cellDestroy (lifecycle limb 29, death-cert reflected): mirror `apply_cell_destroy`
        // (`c.destroy(certificate)` → `Destroyed { death_certificate_hash, destroyed_at }`).
        // `lifecycle_felt` folds the `death_certificate_hash`, so the death certificate is reflected
        // in the forced limb.
        Effect::CellDestroy {
            target,
            certificate,
        } if target == cell_id => {
            let _ = cell.destroy(certificate);
        }
        // makeSovereign (record-digest limb 24 via the folded MODE byte): mirror the deployed
        // `apply_make_sovereign` (`ledger.make_sovereign` moves the cell from the hosted leaf set to a
        // sovereign registration). The CELL-LOCAL projection of that promotion is `cell.mode =
        // Sovereign` — the mode byte `compute_authority_digest_felt` FOLDS (commitment.rs §"Mode",
        // `Hosted=0/Sovereign=1`). The deployed `makeSovereignVmDescriptor2R24` welds the AFTER r23
        // authority-digest limb (`B_RECORD_DIGEST`, folding the flipped mode) to PI 46, and the verifier
        // anchors `compute_authority_digest_felt(post_cell)`. A frozen-mode AFTER block (a cell the
        // promotion did NOT advance) makes the anchored PI 46 disagree with the proof's bound limb ⇒
        // UNSAT. Both the producer (`cipherclerk::prove_sovereign_turn_rotated`'s after-cell) and this
        // weld route the SAME mode flip, so an HONEST promotion's after-digest equals the anchor.
        Effect::MakeSovereign { cell: target } if target == cell_id => {
            cell.mode = dregg_cell::CellMode::Sovereign;
        }
        _ => {}
    }
}

/// The cell-based lifecycle forced-limb felt: `lifecycle_felt(&cell.lifecycle)`. This is the value
/// the verifier anchors PI 38 to for the LIFECYCLE record-pin family (cellSeal/cellUnseal/
/// cellDestroy — `record_pin_offset` ⇒ `B_LIFECYCLE`, limb 29). A thin re-projection of the
/// existing `lifecycle_felt` onto the post-cell so the verifier need not reach into `cell.lifecycle`
/// itself (keeping the anchor's call shape uniform with the record-digest family's
/// `compute_authority_digest_felt(&post_cell)`).
pub fn lifecycle_felt_cell(cell: &Cell) -> BabyBear {
    lifecycle_felt(&cell.lifecycle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;

    fn cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        Cell::with_balance(pk, [0u8; 32], balance)
    }

    #[test]
    fn pre_limb_count_is_37_at_r24() {
        // 1 cells_root + 24 registers + 4 (cap/nullifier/commitments/heap) + 3 (lifecycle/epoch/
        // committed_height) + 5 (disc + perms + vk + mode + fields_root, the WAVE-2/3 flag-days).
        assert_eq!(NUM_PRE_LIMBS, 37);
    }

    /// THE iroot NON-OMISSION TOOTH (Lean `mroot_injective`): tamper / truncate / extend /
    /// reorder of the receipt log each MOVE the root.
    #[test]
    fn iroot_binds_the_whole_log() {
        let log = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
        let base = iroot(&log);
        // tamper a leaf
        let mut tampered = log.clone();
        tampered[1] = [9u8; 32];
        assert_ne!(base, iroot(&tampered), "tampered leaf must move the root");
        // truncate
        assert_ne!(base, iroot(&log[..2]), "truncation must move the root");
        // extend
        let mut extended = log.clone();
        extended.push([4u8; 32]);
        assert_ne!(base, iroot(&extended), "extension must move the root");
        // reorder
        let reordered = vec![log[1], log[0], log[2]];
        assert_ne!(base, iroot(&reordered), "reorder must move the root");
        // the empty log is the zero root
        assert_eq!(iroot(&[]), BabyBear::ZERO);
    }

    /// `cells_root` is a function of the SET of present cells, not the insertion order.
    #[test]
    fn cells_root_is_set_valued() {
        let (a, b) = (cell(1, 10), cell(2, 20));
        let mut l1 = Ledger::new();
        l1.insert_cell(a.clone()).unwrap();
        l1.insert_cell(b.clone()).unwrap();
        let mut l2 = Ledger::new();
        l2.insert_cell(b).unwrap();
        l2.insert_cell(a).unwrap();
        assert_eq!(
            cells_root(&l1),
            cells_root(&l2),
            "cells_root must be insertion-order independent"
        );
        // a different cell set yields a different root
        let mut l3 = Ledger::new();
        l3.insert_cell(cell(1, 10)).unwrap();
        assert_ne!(cells_root(&l1), cells_root(&l3));
        // the empty ledger is the empty-tree sentinel root
        assert_eq!(cells_root(&Ledger::new()), empty_heap_root());
    }

    /// The chained `wire_commit` binds every pre-iroot limb and the iroot: moving any limb
    /// (here the commitments_root limb at offset 27, and the heap_root at 28) or the iroot moves
    /// the commitment.
    #[test]
    fn wire_commit_binds_limbs_and_iroot() {
        let limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS)
            .map(|i| BabyBear::new(300 + i as u32))
            .collect();
        let c = wire_commit(&limbs, BabyBear::new(7));
        let mut moved = limbs.clone();
        moved[27] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved, BabyBear::new(7)),
            "commitments_root limb (27) is bound"
        );
        let mut moved_heap = limbs.clone();
        moved_heap[28] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved_heap, BabyBear::new(7)),
            "heap_root limb (28) is bound"
        );
        let mut moved_disc = limbs.clone();
        moved_disc[32] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved_disc, BabyBear::new(7)),
            "lifecycle_disc limb (32) is bound"
        );
        let mut moved_perms = limbs.clone();
        moved_perms[33] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved_perms, BabyBear::new(7)),
            "perms_digest limb (33) is bound"
        );
        let mut moved_vk = limbs.clone();
        moved_vk[34] = BabyBear::new(999);
        assert_ne!(
            c,
            wire_commit(&moved_vk, BabyBear::new(7)),
            "vk_digest limb (34) is bound"
        );
        assert_ne!(c, wire_commit(&limbs, BabyBear::new(8)), "iroot is bound");
    }

    /// THE FORCED-LIMB MOVEMENT MAP — the load-bearing fact for whether each record-pin effect's
    /// verifier anchor can BITE. `apply_effect_to_cell` mirrors the executor apply; for each effect
    /// we assert whether the forced limb (record-digest = `compute_authority_digest_felt`, lifecycle
    /// = `lifecycle_felt_cell`) genuinely moves between before and honest-after. Anchored effects
    /// REQUIRE movement (a non-moving forced limb is a published-value pin, not a forcing gate).
    #[test]
    fn forced_limb_movement_map() {
        use dregg_cell::lifecycle::{ArchivalAttestation, DeathCertificate, DeathReason};
        let base = Cell::with_balance([3u8; 32], [0u8; 32], 100);
        let id = base.id();
        let rd = |c: &Cell| dregg_cell::commitment::compute_authority_digest_felt(c);
        let lf = |c: &Cell| lifecycle_felt_cell(c);

        // setVK → record-digest: MOVES (anchored — the anchor bites).
        {
            let mut a = base.clone();
            #[allow(deprecated)]
            let vk = dregg_cell::VerificationKey::new(vec![1, 2, 3]);
            apply_effect_to_cell(
                &mut a,
                &id,
                &Effect::SetVerificationKey {
                    cell: id,
                    new_vk: Some(vk),
                },
                0,
            );
            assert_ne!(
                rd(&base),
                rd(&a),
                "setVK MUST move the record digest (anchored)"
            );
        }
        // refusal → record-digest: MOVES (anchored — the anchor bites). The deployed `apply_refusal`
        // writes the audit into the EXT `fields_root` (`REFUSAL_AUDIT_EXT_KEY`), which
        // `compute_authority_digest_felt` FOLDS, so the r23 record digest advances on a genuine refusal.
        // The user `fields[0..15]` block is UNTOUCHED (refusal is purely a non-action attestation).
        {
            let mut a = base.clone();
            apply_effect_to_cell(
                &mut a,
                &id,
                &Effect::Refusal {
                    cell: id,
                    offered_action_commitment: [7u8; 32],
                    refusal_reason: crate::action::RefusalReason::Declined,
                    proof_witness_index: 0,
                },
                0,
            );
            assert_eq!(
                base.state.fields[4], a.state.fields[4],
                "refusal must NOT touch the user-addressable fields[4] (the audit lands in fields_root)"
            );
            assert_ne!(
                rd(&base),
                rd(&a),
                "refusal MUST move the record digest (the audit lands in fields_root, which the r23 \
                 authority residue folds) — the record-pin anchor BITES"
            );
        }
        // receiptArchive → lifecycle: MOVES (the executor writes the LIFECYCLE `Archived`, which
        // `lifecycle_felt` (limb 29) folds; the record-pin is now routed to `B_LIFECYCLE` to match).
        {
            let mut a = base.clone();
            let att = ArchivalAttestation {
                cell_id: id,
                archive_start_height: 0,
                archive_end_height: 5,
                archive_blob_hash: [1u8; 32],
                archive_terminal_commitment: [2u8; 32],
                archive_terminal_receipt_hash: [3u8; 32],
            };
            apply_effect_to_cell(
                &mut a,
                &id,
                &Effect::ReceiptArchive {
                    prefix_end_height: 5,
                    checkpoint: att,
                },
                0,
            );
            assert_eq!(
                rd(&base),
                rd(&a),
                "receiptArchive does NOT move the record digest"
            );
            assert_ne!(
                lf(&base),
                lf(&a),
                "receiptArchive moves the LIFECYCLE (the genuine forced limb)"
            );
        }
        // cellSeal → lifecycle: MOVES (the lifecycle forced limb genuinely separates Live/Sealed).
        {
            let mut a = base.clone();
            apply_effect_to_cell(
                &mut a,
                &id,
                &Effect::CellSeal {
                    target: id,
                    reason: [9u8; 32],
                },
                42,
            );
            assert_ne!(lf(&base), lf(&a), "cellSeal MUST move the lifecycle felt");
        }
        // cellUnseal → lifecycle: MOVES (Sealed → Live).
        {
            let mut sealed = base.clone();
            sealed.seal([9u8; 32], 42).unwrap();
            let mut a = sealed.clone();
            apply_effect_to_cell(&mut a, &id, &Effect::CellUnseal { target: id }, 0);
            assert_ne!(
                lf(&sealed),
                lf(&a),
                "cellUnseal MUST move the lifecycle felt"
            );
        }
        // cellDestroy → lifecycle: MOVES, and the death certificate is REFLECTED (distinct certs ⇒
        // distinct lifecycle felt, since `lifecycle_felt` folds `death_certificate_hash`).
        {
            let cert = DeathCertificate {
                cell_id: id,
                last_receipt_hash: [4u8; 32],
                final_state_commitment: [5u8; 32],
                destroyed_at_height: 9,
                reason: DeathReason::Voluntary,
            };
            let cert2 = DeathCertificate {
                reason: DeathReason::Forced,
                ..cert.clone()
            };
            let mut a = base.clone();
            let mut a2 = base.clone();
            apply_effect_to_cell(
                &mut a,
                &id,
                &Effect::CellDestroy {
                    target: id,
                    certificate: cert,
                },
                0,
            );
            apply_effect_to_cell(
                &mut a2,
                &id,
                &Effect::CellDestroy {
                    target: id,
                    certificate: cert2,
                },
                0,
            );
            assert_ne!(
                lf(&base),
                lf(&a),
                "cellDestroy MUST move the lifecycle felt"
            );
            assert_ne!(
                lf(&a),
                lf(&a2),
                "cellDestroy reflects the death certificate (distinct certs distinct felt)"
            );
        }
    }

    /// **THE FAITHFUL 8-FELT COLLISION-DISTINGUISHING TOOTH (Phase B-ROTATION), producer side.**
    /// Two cell-states differing ONLY in a high position (one byte of the AUTHORITY DIGEST limb,
    /// i.e. a permissions / VK flip folded into r23) produce 8-felt commitments differing in ≥ 1
    /// felt — the binding a 1-felt (~31-bit) commit cannot promise. The producer twin equals the
    /// cell twin equals the circuit primitive (the three-way differential).
    #[test]
    #[cfg(feature = "prover")]
    fn faithful_8felt_commit_distinguishes_authority_near_collision() {
        use dregg_cell::commitment::{
            V9RotationContext, compute_canonical_state_commitment_v9_felt8,
        };
        let mut ledger = Ledger::new();
        let base = Cell::with_balance([3u8; 32], [0u8; 32], 100);
        ledger.insert_cell(base.clone()).unwrap();
        let ctx = V9RotationContext {
            cells_root: cells_root(&ledger),
            nullifier_root: [0u8; 32],
            commitments_root: [0u8; 32],
            iroot: BabyBear::new(7),
        };
        // a permission flip — folded into the authority-digest limb (r23), a HIGH limb.
        let mut flipped = base.clone();
        flipped.permissions.set_state = dregg_cell::permissions::AuthRequired::Impossible;
        assert_ne!(
            base.permissions.set_state, flipped.permissions.set_state,
            "the near-collision must be a genuine authority difference"
        );

        let c_base = compute_canonical_state_commitment_v9_felt8(&base, &ctx);
        let c_flip = compute_canonical_state_commitment_v9_felt8(&flipped, &ctx);
        assert_ne!(
            c_base, c_flip,
            "an authority flip must move the 8-felt commitment"
        );
        assert!(
            (0..8).any(|i| c_base[i] != c_flip[i]),
            "≥ 1 of the 8 committed felts must differ"
        );

        // POST-FLIP three-way differential: the cell twin (`_felt8`, repointed to the CHIP chain
        // under `prover`) == the deployed circuit primitive `wire_commit_8_chip` (the byte-twin of the
        // published wide carrier). The plain `wire_commit_8` DIVERGES (no arity-tag seeding) — that is
        // why the flip repointed to the chip chain; the executor anchors against THIS.
        let pre = dregg_cell::commitment::compute_rotated_pre_limbs(&base, &ctx);
        assert_eq!(
            dregg_circuit::poseidon2::wire_commit_8_chip(&pre, ctx.iroot),
            c_base,
            "cell 8-felt twin must equal the deployed chip-faithful circuit primitive"
        );
    }

    /// THE INTERMEDIATE-CARRIER TOOTH (producer side): an EARLY-limb difference (the cap_root limb,
    /// folded mid-chain) still moves the published 8-felt commit — the carrier is 8-wide throughout.
    #[test]
    fn faithful_8felt_commit_intermediate_carrier() {
        let limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS)
            .map(|i| BabyBear::new(7 * i as u32 + 1))
            .collect();
        let base = wire_commit_8(&limbs, BabyBear::new(5));
        // limb 1 (r0/balance_lo) is folded in the FIRST head site — deep before the final squeeze.
        let mut early = limbs.clone();
        early[1] += BabyBear::new(1);
        assert_ne!(
            base,
            wire_commit_8(&early, BabyBear::new(5)),
            "early mid-chain limb is bound"
        );
    }

    /// Distinct lifecycle states yield distinct limbs (the anti-omission tooth).
    #[test]
    fn lifecycle_felt_separates_states() {
        let live = lifecycle_felt(&CellLifecycle::Live);
        let destroyed = lifecycle_felt(&CellLifecycle::Destroyed {
            death_certificate_hash: [5u8; 32],
            destroyed_at: 42,
        });
        assert_ne!(live, destroyed, "Live and Destroyed must commit distinctly");
    }
}
