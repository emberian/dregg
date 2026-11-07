//! # `rotation_witness` — the per-turn ROTATION producers (the deferred long pole).
//!
//! `.docs-history-noclaude/ROTATION-CUTOVER.md` §5 items 3-5 name three witness columns of the rotated
//! state block that no v1 column carries, and that no producer existed for: `cells_root`
//! (the turn-level boundary view over present cells), `iroot` (the root over the
//! receipt log — whole-history non-omission, Lean
//! `Dregg2.Lightclient.ReceiptChain8.rchain8_binds_or_collides` /
//! `metatheory/Dregg2/Lightclient/ReceiptChain8.lean`), and the `lifecycle` / `epoch` scalar limbs.
//!
//! ⚠ That citation read `mroot_injective` / `Dregg2/Lightclient/MMR.lean` until 2026-08-01, and both
//! halves were false: the theorem had been DELETED on 2026-07-28 as pigeonhole-false, and `iroot` is
//! a left-leaning chain, not the MMR's bagged peak forest. See [`iroot8`].
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
//! * The `iroot` is a left-leaning Poseidon2 fold over the per-position receipt leaves — the Rust
//!   twin of Lean `ReceiptChain8.rchain8`, whose `rchain8_binds_or_collides` makes
//!   tamper/truncate/extend/reorder all move at **2^123.63**, unconditionally (no `Compress8CR`,
//!   no `Poseidon2SpongeCR` — both refuted at deployed parameters). ⚠ This note used to cite
//!   `mroot_injective` (`MMR.lean:313`) and to call the fold an MMR; the theorem was deleted
//!   2026-07-28 and the fold is not an MMR. All eight lanes reach the anchor: lane 0 at
//!   `B_IROOT` (absorbed last), lanes 1..7 as the pre-limbs `ROTATED_IROOT_COMPLETION` (the
//!   iroot-widening flag day, 187 -> 196). Until then only lane 0 did, and a lane-0 collision
//!   (2^15.45, found in 64,147 evaluations) gave two receipt logs one signed anchor.
//! * `cells_root` is the sorted-Poseidon2 boundary root over the present cells' existence
//!   leaves (`dregg_circuit::heap_root` — the SAME tree the heap domain commits to), the
//!   `boundary_root_derived` analogue at the turn level (`UNIVERSAL-MEMORY.md`).
//! * The per-cell scalar limbs (balance/nonce/fields/cap_root/lifecycle/epoch/height)
//!   read a SINGLE cell's `RecordKernelState` — the rotated per-effect descriptor is a
//!   per-cell shape (the v1 state block is one cell's before/after). The turn-level
//!   `cells_root` and `iroot` are the same for every effect row of the turn.

use crate::action::Effect;
use dregg_cell::{Cell, Ledger, lifecycle::CellLifecycle};
pub use dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS;
// ⚑ The absorption-order limb-group constants (`AUTHORITY_DIGEST_GROUP`, `CAP_ROOT_GROUP`, the
// carrier octet bases, `ROTATED_FIELD_LANE_COL`, `PUBKEY_NONET_LANE_COL`, …) are NO LONGER
// imported here. `produce` used to fill all 187 limbs itself from those constants, beside a
// byte-identical copy in `cell::commitment::compute_rotated_pre_limbs`; it now delegates to
// `produce_in_ctx`, which IS that function. One limb fill, one index table, nothing to drift.
use dregg_circuit::effect_vm::split_u64;
use dregg_circuit::exact_nullifier_aafi::{
    ExactLinkedDomains, ExactTaggedKey, exact_linked_append_root8, exact_root_faithful8,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const NUM_REGISTERS: usize = 24;

/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap_root · nullifier_root ·
/// commitments_root · heap_root · lifecycle · epoch · committed_height · lifecycle_disc ·
/// perms_digest · vk_digest · mode · fields_root · revoked_root). Matches Lean
/// `preLimbsAt_length = 178`, after the REVOKED-ROOT flag-day widening of the base region (37→38):
/// `revoked_root` is the new base limb 37, so every limb index ≥ 37 shifts +1 (completion 38..=88,
/// carrier 89..=112, fields 113..=168). The tail 169..=177 is the clean-alignment region: the
/// `cells_root` completion lanes 169..=175 (FILLED HERE on every turn since wound #23 — kept off
/// `revoked_root`'s 82..=88 group; the createCell/factory/spawn trace generator overwrites the whole
/// group with the in-circuit accounts tree) + pads 176..=177, body `[4..177]` = 174 = 58×3 (clean).
/// The present-cell-set exact tagged-linked-leaf domain triple: `FLI2`/`FLN2`/`FLE2` (`L` for
/// LEDGER — the set of present cells IS the ledger's key set).
///
/// Distinct from all four sibling accumulators — `FNI2`/`FNN2`/`FNE2` (nullifiers),
/// `FCI2`/`FCN2`/`FCE2` (commitments), `FRI2`/`FRN2`/`FRE2` (revocations), `FSI2`/`FSN2`/`FSE2`
/// (shielded notes) — so no tree's root, opening, or EMPTY root can be replayed as another's.
///
/// This triple REPLACES the `(collection_id, key)` addressing the cells tree used to ride: the
/// retired `const CELLS_COLLECTION: u32 = 0` was the first input to `heap_addr(coll, key)`, and
/// with the domain now carried by the sponge tag there is no collection felt left to name.
pub const EXACT_CELLS_LINKED_DOMAINS: ExactLinkedDomains = ExactLinkedDomains {
    leaf: 0x464c_4932,  // `FLI2`
    node: 0x464c_4e32,  // `FLN2`
    empty: 0x464c_4532, // `FLE2`
};

/// The existence value every present-cell leaf carries. The cells tree states PRESENCE and
/// nothing else — the cell's contents are committed by its own rotated block, not here — so the
/// value slot is the constant existence bit, exactly as it was under the retired heap fold.
const CELL_PRESENT_VALUE: u64 = 1;

/// One turn's rotated state-block witness for a single cell's before/after RecordKernelState.
///
/// `pre_limbs` is the `NUM_PRE_LIMBS`-limb absorption vector in the Lean-pinned order; `iroot` is the
/// MMR root absorbed LAST. `state_commit = wireCommitR(pre_limbs, iroot)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotationWitness {
    /// The `NUM_PRE_LIMBS` pre-iroot limbs, in absorption order.
    pub pre_limbs: Vec<BabyBear>,
    /// Lane 0 of the receipt-log root, the value absorbed LAST at `B_IROOT`. Lanes 1..7 are
    /// inside `pre_limbs` (`ROTATED_IROOT_COMPLETION`).
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
    ///
    /// ⚑ "Genuine asset class" is ~2^30.87 classes wide, not 2^256: the fold maps
    /// 32 bytes onto ONE felt, so two DISTINCT currencies collide after a 2^15.67
    /// grind and their conservation sums silently merge. The executor refuses a
    /// turn whose committed ids collide
    /// (`executor::atomic::refuse_colliding_asset_classes`); a light client
    /// reading only this felt cannot. See
    /// `dregg_circuit::block_conservation::fold_token_id_to_asset`.
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
        // Migrated keeps a richer payload (to + attestation + height) and is distinct from
        // the light-client movers this gate forces — so it folds through the SINGLE
        // canonical definition `dregg_circuit::poseidon2::lifecycle_migrated_felt` rather
        // than a second hand-written sponge here. That composition is FAITHFUL (16×u16
        // limbs, nothing reduces): `attestation` is a caller-chosen 32-byte blob and this
        // limb is its only binding on the v9 anchor, so the `bytes32_to_8_limbs` lanes it
        // used to ride — where `v` and `v + p` are one addition apart and identical —
        // were the whole of it.
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => dregg_circuit::poseidon2::lifecycle_migrated_felt(
            to.as_bytes(),
            attestation,
            *migrated_at,
        ),
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

/// The faithful 8-felt root of the EMPTY nullifier accumulator — the exact tagged-linked-leaf
/// (`FNI2`) root over the lone `BOT(value=0, next=TOP)` sentinel leaf. THE value a producer
/// passes for `nullifier_root` when no live accumulator root is threaded (a turn with no
/// note-spend).
///
/// Derived by CONSTRUCTING a fresh `NullifierSet` rather than re-deriving the fold, so the empty
/// default and a live-advanced root cannot drift apart: this IS the empty accumulator's `root8`,
/// not a second computation of it.
#[inline]
pub fn empty_nullifier_root_8() -> dregg_circuit::Faithful8 {
    dregg_cell::nullifier_set::NullifierSet::new().root8()
}

/// The faithful 8-felt root of the EMPTY commitments accumulator — the exact tagged-linked-leaf
/// (`FCI2`) root over the lone `BOT(value=0, next=TOP)` sentinel leaf. THE value a producer
/// passes for `commitments_root` when no live accumulator root is threaded (a turn with no
/// note-create).
///
/// Derived by CONSTRUCTING a fresh `CommitmentSet`, for the same reason as the spend-side
/// sibling above. It is DOMAIN-SEPARATED from that sibling: even the two EMPTY roots differ, so a
/// create-side opening cannot be replayed as a spend-side one.
#[inline]
pub fn empty_commitments_root_8() -> dregg_circuit::Faithful8 {
    dregg_cell::commitment_set::CommitmentSet::new().root8()
}

/// The faithful 8-felt root of the EMPTY credential-revocation accumulator — the exact
/// tagged-linked-leaf (`FRI2`) root over the lone `BOT(value=0, next=TOP)` sentinel leaf. THE
/// value a producer passes for `revoked_root` when no live accumulator root is threaded (a turn
/// that revokes nothing — the common case; the registry is grow-only and starts empty).
///
/// Derived by CONSTRUCTING a fresh `RevokedSet`, so the empty default and a live-advanced root
/// cannot drift apart. This empty default is the canonical "nothing revoked" root a light client
/// verifies against — it is COMMITTED (not wire-supplied), so a node cannot substitute a stale
/// root to hide a revocation (hole #139).
#[inline]
pub fn empty_revoked_root_8() -> dregg_circuit::Faithful8 {
    dregg_cell::revoked_set::RevokedSet::new().root8()
}

/// **THE `cells_root` PRODUCER** — the turn-level boundary view over the present cells,
/// as a FAITHFUL 8-felt root.
///
/// The exact tagged-linked-leaf (`FLI2 ‖ addr17 ‖ value4 ‖ next17`) append-at-free-index root at
/// depth 16, arity 4, eight BabyBear lanes — one existence leaf per present cell, keyed by the
/// cell id's SIXTEEN little-endian `u16` limbs. Structurally identical to its four sibling
/// accumulators (`nullifier_root`/`commitments_root`/`revoked_root`/the shielded set), which is
/// the point: the cells tree was the last member of that group still keyed by a felt fold.
///
/// The ids are sorted by their canonical `ExactTaggedKey` before the fold, so the physical slot
/// order IS the key order and the root is a function of the SET of present cells — never
/// `Ledger`'s `HashMap` iteration order, which is not even stable across nodes. The empty ledger
/// yields the domain's empty-tree root (`exact_linked_append_root8(EXACT_CELLS_LINKED_DOMAINS,
/// &[])`), distinct from every sibling's empty root by the `FLI2`/`FLN2`/`FLE2` tags.
///
/// ## ⚑ WHAT THIS REPLACED: a $0 permanent consensus halt (closed 2026-08-01)
///
/// Until this commit the leaf ADDRESS was `heap_addr(CELLS_COLLECTION, hash_bytes(id))` — ONE
/// BabyBear felt, ~30.9 bits, per 32-byte `CellId`. Since 2026-07-28
/// `heap_root::assert_addr_unique` **panics** (release-active, correctly) rather than silently
/// deduping a repeated address, because a dedup makes a cell's REMOVAL invisible to the anchor.
/// Fail-closed was right; shipping it over an attacker-collidable key is what turned a silent
/// double-spend into a **liveness kill**:
///
/// * `CellId::derive_raw` is `blake3::derive_key("dregg-cell-id-v1", public_key ‖ token_id)` over
///   two attacker-chosen 32-byte arrays, so candidate ids are ground **entirely offline** — no
///   chain interaction, no signature, no proof.
/// * `Effect::CreateCell` validates only `balance == 0` (`executor/apply.rs`); `token_id` is used
///   raw with no registry, no allowlist, no possession check on `public_key`, and no rate limit.
///   `token_id` alone is therefore a free 32-byte grinding domain.
/// * So ~2^15.5 offline folds and **two ordinary cell creations** put two cells on one address.
///   `cells_root` is on the unconditional per-turn anchor path (`state_commit::consensus_ctx`),
///   the panic is classified `FatalIntegrity`, and the finality executor stops permanently with
///   the block unacknowledged — deterministically, on every node, across restarts.
///
/// ⚠ The repair is NOT to restore the dedup. It is to make the collision unreachable.
///
/// ## Why SIXTEEN `u16` LIMBS and not a wider hash — a key needs INJECTIVITY, not collision
/// resistance
///
/// These are different jobs with different numbers and the two do not transfer:
///
/// * A **hash node** needs collision resistance, priced by the birthday bound over its image.
///   Eight BabyBear lanes give `8·log₂ p = 247.26` bits of image and `2^123.63` collision — the
///   figure `57105f387` bought for the membership tree, and the figure this root's EIGHT LANES
///   still carry. Correct for a node.
/// * A **key/encoding** needs injectivity: distinct ids must not share a leaf AT ALL, at any
///   root width. No collision bound achieves that; only an injection does. And no 8-lane
///   encoding of 32 bytes exists — `P^8 = 2^247.26 < 2^256` is pigeonhole, proved in Lean as
///   `Dregg2.Circuit.MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8` (*no* function,
///   not *no known* function) with `FieldLanes9.nine_lanes_is_the_minimum` beside it.
///
/// The sixteen-`u16` codec (`exact_nullifier_aafi::raw_to_u16_le`) is `65536^16 = 2^256` **on the
/// nose** — `card_key16` / `u16_limbs_admit_a_bijection` in that same Lean file — so nothing
/// reduces, nothing folds, and the encoding step loses exactly zero bits. Two distinct `CellId`s
/// cannot share a leaf, so `ExactAafiError::Duplicate` is now unreachable by construction: it
/// requires two byte-identical ids, which `Ledger`'s `HashMap<CellId, _>` cannot hold. The
/// `.expect` below is therefore a statement about the container, not a surviving grind target.
///
/// ⚑ SUBSTRATE: this is a producer, not an AIR. Nothing in any circuit recomputes this key —
/// the rotated trace generator OVERWRITES the whole cells group with its own in-circuit accounts
/// tree (`trace_rotated.rs`, `insert_witness_aafi`), which production always feeds
/// `before_accounts = &[]`, and no verifier opens `cells_root`
/// (`executor/proof_verify.rs`: the anchor is taken from trusted storage, not reconstructed).
/// So NO VK rotates and NO descriptor is re-emitted. The wide object being registered here was
/// already Lean-proved and already on disk — `MapOpWideKeyPigeonhole` records that "the kind-D
/// residual is REGISTRATION of an object on disk, not authoring a wider one." This is that
/// registration. Law #1 is untouched: no Rust-authored constraint exists on this path.
///
/// ⚠ FLAG DAY: every `pre_state_hash`/`post_state_hash` moves. `CANONICAL_STATE_SCHEMA_EPOCH`
/// 19 → 20; a store written under ≤19 REFUSES to load and re-genesises.
///
/// ## The width history, both halves (wound #23,
/// `docs/WOUND-felt-width-boundaries-2026-07-19.md`)
///
/// This root is limb 0 of the rotated block ‖ completion lanes 169..=175, i.e. a COMPONENT of the
/// deployed consensus anchor (`state_commit::consensus_state_commitment` →
/// `pre_state_hash`/`post_state_hash` on every receipt, which the executor signature signs and
/// the federation receipt QC aggregates over). Both halves of its width are now closed, and they
/// were separate defects:
///
/// * **The ROOT** was `compute_heap_root_entries -> BabyBear`: a 1-felt (~31-bit) fold riding as
///   a bare limb inside the faithful 8-felt chain. Two different present-cell SETS colliding on
///   that one felt gave ONE signed anchor for two different ledgers. Closed by wound #23 to a
///   `node8` fold, and the eight lanes survive verbatim here — `exact_node_digest_in` is a
///   `hash_many_8`, so every intermediate is 8 felts and the root keeps `2^123.63`.
/// * **The KEY** was `heap_addr(CELLS_COLLECTION, hash_bytes(id))` — one felt per 32-byte
///   `CellId`, so two ids whose folds collided produced literally the SAME leaf at any root
///   width. Wound #23 explicitly did NOT reach it, and after `assert_addr_unique` began refusing
///   such a pair it became the halt described above. That is the class closed here, by an
///   injection rather than by a wider hash.
pub fn cells_root(ledger: &Ledger) -> dregg_circuit::Faithful8 {
    // Sorted by the canonical tagged key, so the physical slot order IS the key order and the
    // root is a pure function of the SET. `Ledger` is a `HashMap`, whose iteration order is not
    // stable within a process, let alone across nodes — an unsorted fold here would be a
    // consensus split, not a nondeterminism nit.
    let mut ids: Vec<[u8; 32]> = ledger.iter().map(|(id, _)| *id.as_bytes()).collect();
    ids.sort_unstable_by_key(|raw| ExactTaggedKey::from_raw(*raw));

    let records: Vec<([u8; 32], u64)> = ids
        .into_iter()
        .map(|raw| (raw, CELL_PRESENT_VALUE))
        .collect();

    let lanes = exact_linked_append_root8(EXACT_CELLS_LINKED_DOMAINS, &records).expect(
        "the sixteen-u16 cell-id key is INJECTIVE (2^256 on the nose), so a Duplicate here would \
         require two byte-identical CellIds — which `Ledger`'s HashMap<CellId, Cell> cannot hold \
         — and the ledger is bounded by the 4^16 tree capacity",
    );
    exact_root_faithful8(lanes)
}

/// **THE `iroot` PRODUCER** — the receipt-log root, as a FAITHFUL 8-felt digest.
///
/// Delegates to the SINGLE definition, [`dregg_circuit::poseidon2::receipt_chain_root_8`], whose
/// byte-twin is the Lean keystone `Dregg2.Lightclient.ReceiptChain8.RChain8Scheme.rchain8`
/// (`metatheory/Dregg2/Lightclient/ReceiptChain8.lean`). There is one fold body, in the crate that
/// owns the chip primitives, and no second copy here to drift.
///
/// `rchain8_binds_or_collides` proves — with NO hypothesis, in particular no `Compress8CR` and no
/// `Poseidon2SpongeCR`, both of which are refuted at deployed parameters — that two receipt logs
/// with equal roots are EQUAL, or a TOTAL extractor names a genuine collision of the deployed chip.
/// So tamper / truncate / extend / reorder each move this root, at **2^123.63** (birthday over
/// `p^8`, `8 · log₂ p = 247.26` bits; the second-preimage figure ~2^247.3 is not the governing one).
///
/// ## ⚑ WHAT THIS REPLACED, AND WHAT THE HEADER SAID WHILE IT STOOD
///
/// This module's header cited `mroot_injective` TWICE (at the module doc and at the "honest boundary
/// notes") as the reason this root "makes tamper/truncate/extend/reorder all move". Both citations
/// were false, in two independent ways, and they are corrected above:
///
/// * **`mroot_injective` did not exist.** It was DELETED on 2026-07-28 (`ed616d24c`) as
///   pigeonhole-false — `MMR.lean` §3¼ shows ONE sponge collision at two singleton preimages refutes
///   its exact CONCLUSION, not merely its premise. Its honest successor `mroot_binds_or_collides`
///   carries a residual `MMR.lean`'s own header prices at **~2^15.5 queries: a break, not a bound**.
/// * **This was never an MMR.** `Lightclient.MMR` is a peak forest bagged youngest-outward
///   (`mroot = bag (peaksOf L)`, a binary carry). This is a flat left-leaning chain. No theorem
///   about one was ever a theorem about the other, whatever the name said. The genuine MMR
///   realization is `dregg-query/src/mmr.rs` (BLAKE3, 32-byte digests) — a different consumer,
///   which is NOT narrow, and whose own two `mroot_injective` citations are the same stale class.
///
/// The retired fold was zero-seeded with a ONE-felt running root over ONE-felt leaves, so it had two
/// independent ~31-bit waists. A real colliding pair was found by deterministic search in **71,133
/// evaluations / 0.86 s** and built into two well-formed 7-entry receipt logs that the retired fold
/// accepts as one history (`turn/tests/iroot_wide_old_admits_new_rejects.rs`).
pub fn iroot8(receipt_hashes: &[[u8; 32]]) -> dregg_circuit::Faithful8 {
    dregg_circuit::poseidon2::receipt_chain_root_8(receipt_hashes)
}

/// The receipt root of the EMPTY log, at all eight lanes — the value `state_commit::consensus_ctx`
/// pins on the classical executor path, where the anchor deliberately does not bind the receipt log
/// (the current turn's receipt hash is computed FROM this commitment, so it cannot be inside it;
/// `previous_receipt_hash` chains the history instead). It is the domain-separated arity-0 chip
/// image, DERIVED from the fold rather than restated, so it aliases no other zero sentinel.
#[inline]
pub fn empty_iroot_8() -> dregg_circuit::Faithful8 {
    iroot8(&[])
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
pub fn wire_commit_8(pre_limbs: &[BabyBear], iroot: BabyBear) -> dregg_circuit::Faithful8 {
    assert_eq!(
        pre_limbs.len(),
        NUM_PRE_LIMBS,
        "wire_commit_8: {NUM_PRE_LIMBS} pre-iroot limbs at R={NUM_REGISTERS}"
    );
    dregg_circuit::Faithful8::from_wire_commit(pre_limbs, iroot)
}

/// **THE CONTEXT-TAKING WITNESS PRODUCER** — the rotation witness for `cell` under an
/// EXPLICIT [`V9RotationContext`](dregg_cell::commitment::V9RotationContext), rather than under
/// one this function assembles from loose parts.
///
/// ⚑ THIS IS THE ALIGNMENT SURFACE. `state_commit::consensus_ctx` builds the context the
/// receipt's `pre_state_hash`/`post_state_hash` — the value the executor signs and the committee
/// attests — commit under. [`produce`] builds a DIFFERENT one from whatever its caller happened
/// to have in hand, and the resulting divergence is why
/// `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs` exists. A producer that
/// takes the context instead of assembling it can be handed the executor's own, and then the
/// proof's published 8-felt commit IS the receipt's anchor — one commitment per turn, and
/// `verify_full_turn_bound`'s two endpoint `CommitmentMismatch` teeth stop comparing `x != x`.
///
/// It is deliberately the SAME body as the cell-side twin: the limbs come from
/// [`dregg_cell::commitment::compute_rotated_pre_limbs`], so there is ONE limb-fill in the tree
/// rather than two that agree until they do not. [`produce`] now delegates here, and
/// `the_witness_and_the_anchor_are_one_body_under_one_context` in this module's tests is the
/// standing check.
///
/// ⚠ That citation read `the_two_producers_are_one_body` until 2026-08-07 — a test name with no
/// `fn` anywhere in the workspace. A `test(~…)` selector for a name that outlived its referent is
/// **silent** under nextest (`AGENTS.md`), so a filter aimed at this check would have run zero
/// tests and exited 0.
pub fn produce_in_ctx(
    cell: &Cell,
    ctx: &dregg_cell::commitment::V9RotationContext,
) -> RotationWitness {
    let pre_limbs = dregg_cell::commitment::compute_rotated_pre_limbs(cell, ctx);
    let state_commit = wire_commit(&pre_limbs, ctx.iroot.limbs()[0]);
    // The per-cell asset class (the fold of the cell's committed ASSET — its currency, not its
    // name salt) the light-client conservation partition keys on — the SAME fold the executor's
    // collector uses (`atomic::asset_class_for_cell`), so the proof-bound class agrees with the
    // ledger class.
    let asset_class =
        dregg_circuit::block_conservation::fold_token_id_to_asset(cell.asset().as_bytes());
    RotationWitness {
        pre_limbs,
        iroot: ctx.iroot.limbs()[0],
        state_commit,
        asset_class,
    }
}

/// The full witness producer for one cell's before/after state in a real turn.
///
/// `cell` is the per-cell `RecordKernelState` (after-state for the AFTER block; supply the
/// before-cell for the BEFORE block), `ledger` is the after-ledger (for `cells_root`),
/// `nullifier_root` / `heap_root` are the cell's committed map roots, and
/// `receipt_hashes` is the turn's receipt log (for `iroot`). `r11..r23` are witness-free
/// in this turn (no app data) → zero; a real app's hot scalars would fill them.
///
/// ⚠ **THE CONTEXT THIS ASSEMBLES IS NOT THE CONSENSUS CONTEXT**, and every caller in the tree
/// assembles a different one — measured in
/// `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`. Prefer
/// [`produce_in_ctx`] and hand it `state_commit::consensus_ctx`'s output; this entry is the
/// loose-parts form kept for producers that genuinely hold no context (the ledgerless sovereign
/// cipherclerk).
pub fn produce(
    cell: &Cell,
    ledger: &Ledger,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    revoked_root: &dregg_circuit::Faithful8,
    receipt_hashes: &[[u8; 32]],
    material: &dregg_cell::commitment::RotationCarrierMaterial,
) -> RotationWitness {
    produce_in_ctx(
        cell,
        &dregg_cell::commitment::V9RotationContext {
            cells_root: cells_root(ledger),
            nullifier_root: *nullifier_root,
            commitments_root: *commitments_root,
            revoked_root: *revoked_root,
            iroot: iroot8(receipt_hashes),
            material: *material,
        },
    )
}

/// **THE SOVEREIGN PRODUCER'S TURN CONTEXT — the ONE object, and the only way to name it.**
///
/// Every rotated sovereign turn commits under a [`V9RotationContext`](dregg_cell::commitment::V9RotationContext)
/// whose six fields have exactly THREE free parameters: the turn-context ledger (`cells_root`), the
/// receipt log (`iroot`), and the carrier material. The other three — `nullifier_root`,
/// `commitments_root`, `revoked_root` — are the empty-accumulator roots of the three live
/// accumulators, and a sovereign producer has no parameter to thread anything else through.
///
/// This type is that fact made unrepresentable-in-the-other-direction. It has ONE private field,
/// no public constructor that names a root, and no accessor that hands back a mutable or
/// spreadable `V9RotationContext` — so a holder **cannot** write
/// `V9RotationContext { revoked_root: <anything else>, ..ctx }`. Every operation a fixture or a
/// producer wants is a method, and each one reads the same three roots.
///
/// # ⚑ Why the type and not just a builder function
///
/// The wound this closes was measured three times by hand (`c45814b9f`, `a750130ed`, and the
/// `debug_assert` in `cipherclerk`): `dregg_circuit::heap_root::empty_heap_root_8()` was the empty
/// root of all three accumulators until `b20a2c50a` (2026-07-31) rebuilt them as exact
/// tagged-linked-leaf trees, and ~100 hand-written occurrences of the sentinel survived across the
/// fixtures. Nineteen of them were live defects: the fixture registered an OLD_COMMIT under the
/// sentinel while the producer beside it published `empty_revoked_root_8()`, and
/// `verify_and_commit_proof_rotated` — which binds the proof's OLD_COMMIT PIs to
/// `bytes32_to_felt8(stored)` — refused every honest turn.
///
/// A free function returning a bare `V9RotationContext` would have fixed those nineteen and left
/// the twentieth expressible in one token of struct-update syntax. The type does not offer it.
///
/// # ⚠ What this does NOT close, stated plainly
///
/// `V9RotationContext`'s fields are `pub`, and ~50 sites across the tree legitimately construct one
/// by hand (`state_commit::consensus_ctx` with the executor's LIVE roots, the note-spend anchors,
/// circuit fixtures pinning arbitrary roots to exercise a limb). A fixture that never obtains a
/// `SovereignTurnCtx` can still hand-write a disagreeing context and call
/// `compute_canonical_state_commitment_v9_8` directly. Making those fields private would require an
/// all-args constructor for those ~50 sites — which takes the three roots as parameters and so
/// reintroduces the identical hazard under a different name. **So: disagreement is unrepresentable
/// FOR A HOLDER OF THIS TYPE, and merely inconvenient for a fixture that declines to hold one.**
/// The binding is what makes the sovereign path have one body; it is not a whole-tree quantifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SovereignTurnCtx {
    /// PRIVATE ON PURPOSE — see the type doc. Exposing this (even by `&`) would restore
    /// `V9RotationContext { revoked_root: …, ..*ctx.as_v9() }`, which is the whole drift.
    inner: dregg_cell::commitment::V9RotationContext,
}

impl SovereignTurnCtx {
    /// The context for a sovereign turn whose `cells_root` is folded over `ctx_ledger` and whose
    /// `iroot` is folded over `receipt_hashes`. The three accumulator roots are the LIVE empty
    /// roots — [`empty_nullifier_root_8`] / [`empty_commitments_root_8`] / [`empty_revoked_root_8`]
    /// — because a sovereign turn threads no accumulator frontier (the ledgerless cipherclerk holds
    /// none, and `state_commit.rs`'s table records that there is no parameter for it).
    pub fn new(
        ctx_ledger: &Ledger,
        receipt_hashes: &[[u8; 32]],
        material: dregg_cell::commitment::RotationCarrierMaterial,
    ) -> Self {
        Self {
            inner: dregg_cell::commitment::V9RotationContext {
                cells_root: cells_root(ctx_ledger),
                nullifier_root: empty_nullifier_root_8(),
                commitments_root: empty_commitments_root_8(),
                revoked_root: empty_revoked_root_8(),
                iroot: iroot8(receipt_hashes),
                material,
            },
        }
    }

    /// The context for the single-cell turn-context ledger the sovereign producers build — a fresh
    /// `Ledger` holding exactly `cell`. This is `prove_sovereign_turn_rotated`'s own `ctx_ledger`,
    /// so a fixture that registers `cell`'s OLD_COMMIT calls THIS and cannot assemble a different
    /// ledger by accident.
    pub fn for_cell(
        cell: &Cell,
        receipt_hashes: &[[u8; 32]],
        material: dregg_cell::commitment::RotationCarrierMaterial,
    ) -> Self {
        let mut ctx_ledger = Ledger::new();
        let _ = ctx_ledger.insert_cell(cell.clone());
        Self::new(&ctx_ledger, receipt_hashes, material)
    }

    /// The same context with a different carrier material — the ONE field a producer legitimately
    /// varies between the BEFORE block (`Default`) and a factory turn's AFTER block (the installed
    /// child VK). The roots and the ledger/receipt folds are carried over untouched, so this cannot
    /// be used to move an accumulator root.
    pub fn with_material(self, material: dregg_cell::commitment::RotationCarrierMaterial) -> Self {
        Self {
            inner: dregg_cell::commitment::V9RotationContext {
                material,
                ..self.inner
            },
        }
    }

    /// The `iroot` this context absorbs LAST — the value a caller needs to rebuild a
    /// `RotatedBlockWitness` beside the witness itself.
    pub fn iroot(&self) -> dregg_circuit::Faithful8 {
        self.inner.iroot
    }

    /// The rotated witness for `cell` under this context — [`produce_in_ctx`], with no context to
    /// get wrong.
    pub fn witness(&self, cell: &Cell) -> RotationWitness {
        produce_in_ctx(cell, &self.inner)
    }

    /// The [`NUM_PRE_LIMBS`]-long absorption vector for `cell` under this context
    /// (`dregg_cell::commitment::compute_rotated_pre_limbs`) — deliberately not a re-typed literal.
    pub fn pre_limbs(&self, cell: &Cell) -> Vec<BabyBear> {
        dregg_cell::commitment::compute_rotated_pre_limbs(cell, &self.inner)
    }

    /// The 1-felt `wireCommitR` twin — the value the rotated trace's row-0 `B_STATE_COMMIT` carrier
    /// carries.
    pub fn commitment_felt(&self, cell: &Cell) -> BabyBear {
        dregg_cell::commitment::compute_canonical_state_commitment_v9_felt(cell, &self.inner)
    }

    /// The FAITHFUL 8-felt chip commitment — the object the wide proof's 16 commit PIs publish and
    /// the executor anchors against.
    pub fn commitment_felt8(&self, cell: &Cell) -> dregg_circuit::Faithful8 {
        dregg_cell::commitment::compute_canonical_state_commitment_v9_felt8(cell, &self.inner)
    }

    /// The 32-byte ledger-slot encoding of [`Self::commitment_felt8`] — **the value a fixture
    /// registers with `Ledger::register_sovereign_cell`**, and the value the executor reads back
    /// via `bytes32_to_felt8` as the proof's 8 BEFORE commit PIs.
    pub fn commitment_8(&self, cell: &Cell) -> [u8; 32] {
        dregg_cell::commitment::compute_canonical_state_commitment_v9_8(cell, &self.inner)
    }
}

/// **THE ONE CONTEXT BUILDER** — [`SovereignTurnCtx::new`] as a free function, the shape the
/// `a750130ed` lane named as the durable fix for the revoked-root drift. Call it from the producer
/// AND from every fixture that reconstructs what the producer publishes.
pub fn sovereign_turn_ctx(
    ctx_ledger: &Ledger,
    receipt_hashes: &[[u8; 32]],
    material: dregg_cell::commitment::RotationCarrierMaterial,
) -> SovereignTurnCtx {
    SovereignTurnCtx::new(ctx_ledger, receipt_hashes, material)
}

/// **THE VALUE A FIXTURE REGISTERS.** The 8-felt sovereign commitment of `cell` under the producer's
/// own single-cell context and `receipt_hashes` — i.e. exactly the OLD_COMMIT
/// `AgentCipherclerk::prove_sovereign_turn_rotated` publishes for its before-state.
///
/// This is the whole of what the seventeen repaired `revoked_root` fixture sites were doing by hand.
/// It takes NO root argument, so the drift it replaces has no place to live: registering a
/// commitment over an accumulator no producer commits now requires declining to call this at all.
///
/// ⚠ It is DERIVED, never read off the proof. Registering `turn`'s own published pre-state
/// commitment would make the executor's `stored == proof's OLD_COMMIT` check tautological — the
/// fixture must reach the same value independently, which is what "one body, two callers" buys.
pub fn sovereign_registration_commitment(cell: &Cell, receipt_hashes: &[[u8; 32]]) -> [u8; 32] {
    SovereignTurnCtx::for_cell(cell, receipt_hashes, Default::default()).commitment_8(cell)
}

/// **THE PRODUCER-SIDE MEMBERSHIP-TEETH FILL** — the honest `(sender_leaf, authorized_root)`
/// values the committed transfer row's teeth columns carry, derived from the BEFORE cell the leg
/// mints from (the recipe twin of the SDK attach lane's `retain_sender_membership`, which pins
/// the SAME pair for the fold's membership bundle):
///
/// * `sender_leaf` = [`dregg_commit::typed::compress_member`] over the cell's owner key — the
///   canonical chip-native membership compress (the in-AIR keystone's leaf domain). The generic
///   recipe's actor IS the cell owner (the leg is minted from the cell's own turn).
/// * `authorized_root` = the root felt read from the cell's `fields[set_root_index]` slot in the
///   executor verifier's canonical form (`membership_verifier::root_felt_from_slot` — the felt's
///   4-byte little-endian low bytes), where `set_root_index` is the slot the cell's program
///   declares via `SenderAuthorized { AuthorizedSet::PublicRoot { .. } }`.
///
/// A cell whose program declares NO such caveat fills the ZERO pair — the committed row's teeth
/// columns are producer-filled claim carriers (the in-AIR compress/fields-read welds are the
/// named `MembershipAuthRootEdge` seams), and the zero form is the no-caveat sentinel: the fold's
/// membership arm only binds these PIs when a membership bundle is attached, and a bundle claim
/// never equals the zero pair for a real member.
///
/// Un-gated, and `pub` since PR3 of the turn-prover extraction: the executor's rotated verifier
/// (`verify_one_cohort_run`) is the TRUSTED twin — it reconstructs the SAME pair from the trusted
/// before-cell to anchor the two published teeth PIs, so a proof whose bound teeth columns
/// disagree is UNSAT (executor-derived, never prover-supplied). The PRODUCER side now lives in
/// `dregg_turn_prover::rotation_witness`, so both sides must read the SAME derivation; `pub` is
/// what keeps that ONE definition rather than a mirrored twin across the crate boundary. Nothing
/// private is exposed — it is a pure function of a public [`Cell`] returning two felts.
pub fn sender_membership_teeth(before_cell: &Cell) -> (BabyBear, BabyBear) {
    use dregg_cell::program::AuthorizedSet;
    use dregg_cell::{CellProgram, StateConstraint};

    let scan = |cs: &[StateConstraint]| {
        cs.iter().find_map(|c| match c {
            StateConstraint::SenderAuthorized {
                set: AuthorizedSet::PublicRoot { set_root_index },
            } => Some(*set_root_index),
            _ => None,
        })
    };
    let slot_index = match &before_cell.program {
        CellProgram::Predicate(cs) => scan(cs),
        CellProgram::Cases(cases) => cases.iter().find_map(|case| scan(&case.constraints)),
        _ => None,
    };
    match slot_index.and_then(|i| before_cell.state.fields.get(i as usize)) {
        Some(slot) => (
            // ⚠ LANE 0 OF THE 8-FELT LEAF, DELIBERATELY. `compress_member` returns the full
            // eight-lane `node8` digest since the membership `node8` cutover, and the membership
            // STARK binds all eight. These two TEETH columns are a different, narrower surface:
            // the in-AIR weld that anchors them (`CarrierOctetGates.lean`'s
            // `withMembershipPubkeyCompress` / `pubkeyCompress1Spec`) is stated at
            // `A(pubkey8 ‖ 0⁸)[0]`, so lane 0 is exactly the value that gate forces and this
            // projection keeps the two sides bit-identical. It is NOT a re-narrowing of the tree:
            // the teeth are claim carriers whose PIs (50/51) are still unpinned, and the fold's
            // membership arm is fail-closed on every deployed leg. Widening the teeth to eight
            // lanes is the SEPARATE `MembershipAuthRootEdge` work, not this cutover.
            dregg_commit::typed::compress_member(before_cell.public_key())[0],
            // The verifier's `root_digest_from_slot` reads eight canonical 4-byte little-endian
            // limbs from the slot; limb 0 is lane 0 of the 8-felt root — the matching projection.
            BabyBear::new(u32::from_le_bytes([slot[0], slot[1], slot[2], slot[3]])),
        ),
        None => (BabyBear::ZERO, BabyBear::ZERO),
    }
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
        // ── The VALUE / FIELD / NONCE welds (absorbed from the sovereign producer, 2026-07-26) ──
        // These three used to live as HAND-WRITTEN arms inside
        // `sdk::cipherclerk::prove_sovereign_turn_rotated`'s step-2 after-cell derivation, beside
        // eight arms that already delegated here. Two lists over the same semantics: the single-leg
        // producer had all eleven, while the MULTI-COHORT producer
        // (`prove_sovereign_cohort_chain`) called ONLY this weld plus its own duplicate `Transfer`
        // — so a heterogeneous sovereign turn carrying a `SetField` or `IncrementNonce` built its
        // `full_after_cell` without that write, and BOTH the final leg's after-block witness (hence
        // the committed NEW commitment — the proof-carrying path does ZERO state manipulation, so
        // the 8-felt commit IS the state) and the SDK's own advanced local state came from that
        // short state. Both producers now route every effect through this one function.
        //
        // balance (limbs 1 `r0` lo / 3 `r2` hi): mirrors `apply_transfer`'s debit/credit as a
        // cell-local projection. `from == to == cell_id` nets to zero, exactly as the producer's
        // arm did. `saturating_*` matches the producer byte-for-byte (a saturating projection is
        // what the v9 commitment binds; the executor's own over/underflow refusal happens at the
        // apply leg BEFORE a turn reaches a rotated anchor).
        Effect::Transfer { from, to, amount } => {
            if from == cell_id {
                cell.state
                    .set_balance(cell.state.balance().saturating_sub(*amount as i64));
            }
            if to == cell_id {
                cell.state
                    .set_balance(cell.state.balance().saturating_add(*amount as i64));
            }
        }
        // fields (limbs 4..=11 lane-0 ‖ the 56 completion lanes, and limb 36 `fields_root` for an
        // EXT key): mirrors `apply_set_field`'s state write. `set_field_ext` routes a key below
        // `STATE_SLOTS` to the octet and an overflow key into `fields_map` (recomputing
        // `fields_root`), which is what `produce` reads for both limb groups.
        Effect::SetField {
            cell: target,
            index,
            value,
        } if target == cell_id => {
            cell.state.set_field_ext(*index, *value);
        }
        // nonce (limb 2 `r1`): mirrors `apply_increment_nonce`.
        Effect::IncrementNonce { cell: target } if target == cell_id => {
            let _ = cell.state.increment_nonce();
        }
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
            let audit =
                crate::action::refusal_audit_commitment(offered_action_commitment, refusal_reason);
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

/// How [`apply_effect_to_cell`] relates to the executor's apply leg for ONE effect against ONE cell.
///
/// The weld's contract is that `apply_effect_to_cell(before, e)` equals the cell state
/// `turn::executor::apply`'s leg for `e` leaves behind, restricted to the fields
/// [`produce`] reads into `pre_limbs`. This enum is the CHECKED statement of where that contract
/// holds — see [`weld_coverage`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WeldCoverage {
    /// The weld projects this effect's write onto `cell_id`. `apply_effect_to_cell` moves the
    /// cell exactly as the executor's apply leg does.
    Projected,
    /// The executor's apply leg writes NO field of `cell_id` that [`produce`] reads, so the weld's
    /// no-op is the CORRECT projection (the effect's real target is a different cell, a
    /// ledger-level accumulator the rotated witness carries as a separate root parameter, the
    /// journal, or the apply leg refuses the effect outright).
    NoCellStateChange,
    /// The executor's apply leg DOES write a field of `cell_id` that [`produce`] reads, and the
    /// weld does not project it. A producer that derived an AFTER block from this weld would bind
    /// a state transition in which the write never happened — and on the proof-carrying sovereign
    /// path the 8-felt commit IS the state (`executor::execute` does zero state manipulation for a
    /// turn carrying an `execution_proof`), so the committed cell would silently lose the write.
    /// The payload names the field and the limb it lands in.
    UnprojectedMover(&'static str),
}

/// **The weld's coverage ledger — the ONE list the sovereign producers refuse from.**
///
/// A `match` over EVERY `Effect` variant with **no `_ =>` arm**: adding a kernel verb does not
/// compile until it is classified here. The classification is grounded, per variant, against the
/// live weld by `turn/tests/sovereign_after_cell_weld_ledger.rs` (which runs the weld and diffs the
/// rotated `pre_limbs`), so narrowing a weld arm — or landing one for a declared
/// [`WeldCoverage::UnprojectedMover`] — reds that test by name.
///
/// `cell_id` is load-bearing: the same verb is a mover for one endpoint and a no-op for the other
/// (`GrantCapability` writes the GRANTEE's `capabilities`, never the granter's; `Introduce` writes
/// the RECIPIENT's). The deployed projector `convert_effects_to_vm` mints a VM row for BOTH
/// endpoints, which is exactly why this must be decided per cell and not per verb.
///
/// The [`WeldCoverage::UnprojectedMover`] rows are the residual the sovereign producers
/// (`sdk::cipherclerk::prove_sovereign_turn_rotated` / `prove_sovereign_cohort_chain`) FAIL CLOSED
/// on: refusing to mint is the only response that neither binds a false transition nor moves the
/// proof bytes of a turn that already committed. Landing a weld arm for one of them changes the
/// AFTER commit an honest turn publishes, which is a witness-migration decision, not a projection
/// fix — see the module note on `apply_effect_to_cell`.
///
/// # Reachability of the ten movers (measured, not reasoned)
///
/// `sdk/tests/wide_completeness_ledger.rs::provability_scoreboard_deployed_wide_path` drives every
/// effect through the deployed wide producer and prints a PROVABLE / UNPROVABLE board. Cross-reading
/// it against these ten:
///
/// * **Reachable — the wound was live**: `Burn`, `Introduce`, `RefreshDelegation`,
///   `ExerciseViaCapability` all prove on the deployed wide path, so before this gate each minted a
///   verifying proof whose AFTER block was byte-identical to its BEFORE block for the field its apply
///   leg writes. `Burn` is the sharpest: the projector mints a DEBITING
///   `VmEffect::Transfer { direction: 1 }` row, so the row and the AFTER block disagreed outright.
/// * **Already fails closed downstream (the gate makes it EARLY and NAMED, not newly safe)**:
///   `GrantCapability`, `RevokeCapability`, `AttenuateCapability` and `RevokeDelegation` carry an
///   in-circuit cap-tree / revoked-tree `map_op` write for which the bare wide route threads no
///   witness, so they die inside the prover ("no `CapWriteWideWitness`" / "no witness heap with
///   root8 …"). Their real route is the separate cap-open weld.
/// * **Dropped before the wide route, but reachable in a MIXED turn**: `SetProgram` is one of the
///   five verbs the projector mints no row for, so a lone `SetProgram` turn fails at descriptor
///   resolution — while `[SetPermissions, SetProgram]` projects to a single `[SetPermissions]`
///   cohort, proves, and commits with the program swap in `effects_hash` but in no row and in no
///   after-cell. `RotatePqIdentity` is refused by name by the CHECKED projector.
pub fn weld_coverage(effect: &Effect, cell_id: &dregg_cell::CellId) -> WeldCoverage {
    use WeldCoverage::{NoCellStateChange, Projected, UnprojectedMover};
    // A verb whose target is a DIFFERENT cell is a no-op on this one by construction — the rotated
    // sovereign proof is over a single cell's transition. Each arm below therefore decides against
    // its own endpoint test, and falls to `NoCellStateChange` when this cell is not that endpoint.
    match effect {
        // ── Projected: the weld moves this cell exactly as the apply leg does ────────────────────
        Effect::Transfer { from, to, .. } => {
            if from == cell_id || to == cell_id {
                Projected
            } else {
                NoCellStateChange
            }
        }
        Effect::SetField { cell, .. } => guard(cell == cell_id, Projected),
        Effect::IncrementNonce { cell } => guard(cell == cell_id, Projected),
        Effect::SetPermissions { cell, .. } => guard(cell == cell_id, Projected),
        Effect::SetVerificationKey { cell, .. } => guard(cell == cell_id, Projected),
        Effect::Refusal { cell, .. } => guard(cell == cell_id, Projected),
        Effect::CellSeal { target, .. } => guard(target == cell_id, Projected),
        Effect::CellUnseal { target } => guard(target == cell_id, Projected),
        Effect::CellDestroy { target, .. } => guard(target == cell_id, Projected),
        Effect::ReceiptArchive { checkpoint, .. } => {
            guard(checkpoint.cell_id == *cell_id, Projected)
        }
        Effect::MakeSovereign { cell } => guard(cell == cell_id, Projected),

        // ── UnprojectedMover: the apply leg writes a committed field the weld does not ───────────
        // `capabilities.grant_ref_provenanced` on the GRANTEE (`apply_grant_capability`): pushes a
        // cap ref + bumps `next_slot`, moving `compute_canonical_capability_root_8` (limb 25 ‖
        // 52..=58). The granter is read-only, so a `from == cell_id` grant is a genuine no-op here.
        Effect::GrantCapability { to, .. } => guard(
            to == cell_id,
            UnprojectedMover(
                "GrantCapability writes the grantee's `capabilities` (cap-root limb 25 ‖ 52..=58)",
            ),
        ),
        // `capabilities.revoke(slot)` (`apply_revoke_capability`): removes the ref and tombstones
        // the slot — cap-root limb 25 ‖ 52..=58.
        Effect::RevokeCapability { cell, .. } => guard(
            cell == cell_id,
            UnprojectedMover(
                "RevokeCapability removes a cap ref + tombstones the slot (cap-root limb 25 ‖ 52..=58)",
            ),
        ),
        // `capabilities.attenuate_in_place` (`apply_attenuate_capability`, which ENFORCES
        // `cell == actor`): narrows the slot's permissions / allowed effects / expiry in place —
        // cap-root limb 25 ‖ 52..=58.
        Effect::AttenuateCapability { cell, .. } => guard(
            cell == cell_id,
            UnprojectedMover(
                "AttenuateCapability narrows a cap slot in place (cap-root limb 25 ‖ 52..=58)",
            ),
        ),
        // `child_mut.delegation = Some(DelegatedRef::new(..))` (`apply_refresh_delegation`, which
        // ENFORCES `child == action_target`): the `delegation` leaves are folded by
        // `compute_authority_digest_8` — limbs 12..=18 + 24.
        Effect::RefreshDelegation { child, .. } => guard(
            child == cell_id,
            UnprojectedMover(
                "RefreshDelegation rewrites the child's `delegation` (authority digest limbs 12..=18, 24)",
            ),
        ),
        // `parent_mut.state.bump_delegation_epoch()` (`apply_revoke_delegation`) on the ACTING
        // parent — `epoch_felt` is limb 30. (The child's `delegation = None` moves the CHILD's
        // authority digest, so a sovereign cell that IS the child is a mover too.)
        Effect::RevokeDelegation { child } => {
            if child == cell_id {
                UnprojectedMover(
                    "RevokeDelegation clears the child's `delegation` (authority digest limbs 12..=18, 24)",
                )
            } else {
                // The acting parent's epoch bump is not addressable from the effect payload (the
                // effect names only the child), so a parent-side revoke cannot be decided here by
                // cell id. It is refused unconditionally: `bump_delegation_epoch` moves limb 30.
                UnprojectedMover(
                    "RevokeDelegation bumps the acting parent's `delegation_epoch` (limb 30)",
                )
            }
        }
        // `cm.state.debit_balance(amount)` (`apply_burn`; a self-burn where `actor == target` is the
        // permissionless case) — balance limbs 1 / 3. The deployed projector already mints a
        // DEBITING `VmEffect::Transfer { direction: 1 }` row for it, so the row and the AFTER block
        // disagree about the balance.
        Effect::Burn { target, .. } => guard(
            target == cell_id,
            UnprojectedMover("Burn debits `state.balance` (limbs 1 lo / 3 hi)"),
        ),
        // `recipient_cell.capabilities.grant_provenanced` (`apply_introduce`) — cap-root limb 25 ‖
        // 52..=58 on the RECIPIENT. The introducer and target are read-only.
        Effect::Introduce { recipient, .. } => guard(
            recipient == cell_id,
            UnprojectedMover(
                "Introduce grants into the recipient's `capabilities` (cap-root limb 25 ‖ 52..=58)",
            ),
        ),
        // `c.program = program.clone()` (`apply_set_program`) — `program` is folded by
        // `compute_authority_digest_8` (limbs 12..=18, 24). SetProgram is ALSO one of the five
        // variants the deployed projector mints no VM row for, so such a turn is doubly invisible:
        // no row and no after-cell move.
        Effect::SetProgram { cell, .. } => guard(
            cell == cell_id,
            UnprojectedMover(
                "SetProgram rewrites `cell.program` (authority digest limbs 12..=18, 24)",
            ),
        ),
        // `apply_exercise_via_capability` recurses into `inner_effects` with `action_target`
        // re-pointed at the capability's target, so the exercise's real writes are the INNER
        // effects' — none of which the weld or the projector sees (the exercise mints ONE row). An
        // exercise wrapping a `SetPermissions` would bind a frozen authority digest.
        Effect::ExerciseViaCapability { inner_effects, .. } => guard(
            !inner_effects.is_empty(),
            UnprojectedMover(
                "ExerciseViaCapability applies its `inner_effects`, which are neither projected to \
                 VM rows nor welded onto the after-cell",
            ),
        ),
        // `target.set_pq_identity(..)` (`apply_rotate_pq_identity`) — `pq_identity` is folded by
        // `compute_authority_digest_8` (limbs 12..=18, 24). Already refused earlier by the CHECKED
        // projector (no AIR row for the PQ identity plane); classified honestly here so a future
        // descriptor landing cannot quietly reach a frozen after-cell.
        Effect::RotatePqIdentity { cell, .. } => guard(
            cell == cell_id,
            UnprojectedMover(
                "RotatePqIdentity rewrites `cell.pq_identity` (authority digest limbs 12..=18, 24)",
            ),
        ),

        // ── NoCellStateChange: the apply leg writes no committed field of THIS cell ──────────────
        // Journal only (`journal.record_event_emitted`); the receipt/journal stream reaches `iroot`,
        // which the rotated witness carries as its own argument, not a `pre_limb`.
        Effect::EmitEvent { .. } => NoCellStateChange,
        // BIRTHS. The actor is read-only (`birth_asset` reads `parent.asset()`); every write lands
        // on the NEW cell, and the cell-ID set growth is the in-circuit accounts grow-gate's job
        // (limb 0 ‖ 169..=175), which the dedicated wide producers force — not an off-cell projection.
        Effect::CreateCell { .. }
        | Effect::CreateCellFromFactory { .. }
        | Effect::SpawnWithDelegation { .. }
        | Effect::CreateHybridCell { .. } => NoCellStateChange,
        // LEDGER-LEVEL ACCUMULATORS carried as separate rotated roots, never cell fields:
        // `note_nullifiers` → the `nullifier_root` argument (limb 26 ‖ 68..=74); `note_commitments`
        // → `commitments_root` (limb 27 ‖ 75..=81); `bridged_nullifiers` is its own set and feeds no
        // rotated limb; the reactive registry / `reactive_nullifiers` likewise.
        Effect::NoteSpend { .. }
        | Effect::NoteCreate { .. }
        | Effect::ShieldedTransfer { .. }
        // Shield moves the note-nullifier and shielded accumulator roots (rotated
        // separately), never a committed field of the acting cell.
        | Effect::Shield { .. }
        // Deshield moves the shielded accumulator's nullifier root and the cleartext
        // commitments root (rotated separately), never a committed field of the
        // acting cell.
        | Effect::Deshield { .. }
        | Effect::BridgeMint { .. }
        | Effect::Promise { .. }
        | Effect::Notify { .. }
        | Effect::React { .. } => NoCellStateChange,
        // `apply_mint` REJECTS `actor == target || actor == well`, so no write to the acting cell is
        // reachable: the well is debited and a THIRD cell credited.
        Effect::Mint { .. } => NoCellStateChange,
        // Apply legs that always error, so no state write exists to project: `apply_pipelined_send`
        // returns `PreconditionFailed` unconditionally, and `Custom` returns
        // `CustomEffectRequiresProofCarryingTurn` (its state movement rides the BOUND sub-proof's
        // own transition, which `enforce_custom_proof_state_binding` ties to this turn's endpoints).
        Effect::PipelinedSend { .. } | Effect::Custom { .. } => NoCellStateChange,
    }
}

/// `weld_coverage`'s endpoint test: `verdict` when this cell IS the effect's endpoint, else the
/// no-op that a different-cell target makes correct.
fn guard(is_endpoint: bool, verdict: WeldCoverage) -> WeldCoverage {
    if is_endpoint {
        verdict
    } else {
        WeldCoverage::NoCellStateChange
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

    /// ⚑ **THE WITNESS PRODUCER AND THE CONSENSUS ANCHOR ARE ONE BODY, UNDER ONE CONTEXT.**
    ///
    /// `produce` used to carry its own ~170-line copy of the absorption-order fill, byte-identical
    /// to `cell::commitment::compute_rotated_pre_limbs` "by construction" — which is to say by
    /// comment. It now DELEGATES to [`produce_in_ctx`], which IS that twin; the copy is DELETED,
    /// not `#[cfg(test)]`-parked (a cfg-test twin is the thing that hides drift, not the thing
    /// that finds it). The one-shot limb-for-limb differential that authorised the deletion ran
    /// green on 2026-08-07 before the copy went.
    ///
    /// What stands here instead is the equation the ALIGNMENT needs, and it needs no copy:
    ///
    /// 1. `produce(loose parts…) == produce_in_ctx(cell, ctx(loose parts…))` — so "hand the prover
    ///    the executor's `V9RotationContext`" is a ONE-ARGUMENT change rather than a rewrite;
    /// 2. the witness's 1-felt `wireCommitR` twin — `RotationWitness::state_commit`, the value the
    ///    rotated trace's row-0 `B_STATE_COMMIT` carrier carries — IS
    ///    `cell::commitment::compute_canonical_state_commitment_v9_felt(cell, ctx)`; and
    /// 3. the witness's limbs, chip-chained, ARE
    ///    `state_commit::cell_state_commitment(cell, ctx)` — the value the receipt carries, the
    ///    executor signs and the committee attests. There is one commitment function; what the two
    ///    sides disagree about is only WHICH CONTEXT, which is the whole of
    ///    `tests/receipt_state_commit_is_not_the_proof_state_commit.rs`.
    ///
    /// ⚑ LEG (2) WAS MISSING AND THAT IS WHY THREE `circuit/tests/effect_vm_rotation_flip.rs`
    /// teeth had to find the last drift instead. This tie checked leg (1) and leg (3) — the CHIP
    /// chain — and never the 1-felt twin, which is precisely the object those three differentials
    /// (`G3`, `G4`, `§4.2`) compare against the trace. The measured drift was a CONTEXT drift:
    /// `produce` was handed `empty_revoked_root_8()` while the cell-side context beside it was
    /// hand-written `heap_root::empty_heap_root_8()`, the same value until `b20a2c50a` rebuilt
    /// `RevokedSet` as an exact tagged-linked-leaf (`FRI2`) tree.
    ///
    /// ⚑ AND THE TIE IS NOW RED-PROVABLE WITHOUT A MUTATION. The body takes the cell-side
    /// `revoked_root` as a parameter, so
    /// [`the_tie_goes_red_when_the_cell_side_context_drifts`] re-runs it with exactly the stale
    /// sentinel that caused the drift and REQUIRES the panic. No `if false &&` scaffold, no window
    /// in a shared tree, and the demonstration cannot rot: if the two roots ever became equal
    /// again the `should_panic` test goes red, which is the honest verdict either way.
    fn the_witness_and_the_anchor_are_one_body(cell_side_revoked_root: dregg_circuit::Faithful8) {
        let c = cell(0x5A, 4242);
        let mut ledger = Ledger::new();
        ledger.insert_cell(c.clone()).unwrap();
        ledger.insert_cell(cell(0x77, 9)).unwrap();

        let nullifier_root = empty_nullifier_root_8();
        let commitments_root = empty_commitments_root_8();
        let revoked_root = empty_revoked_root_8();
        // NON-default material, so the carrier octets are exercised rather than left zero (the
        // shape a factory turn's AFTER block carries).
        let material = dregg_cell::commitment::RotationCarrierMaterial {
            child_vk: Some([0xC1; 32]),
            contract_hash: Some([0xD2; 32]),
        };
        let receipt_hashes = [[0x11u8; 32], [0x22u8; 32]];

        let w = produce(
            &c,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &revoked_root,
            &receipt_hashes,
            &material,
        );
        assert_eq!(
            w.pre_limbs.len(),
            NUM_PRE_LIMBS,
            "the delegated fill must still be the full absorption vector"
        );

        // (1) — the producer's OWN context, so this leg is about `produce` vs `produce_in_ctx` and
        // nothing else.
        let producer_ctx = dregg_cell::commitment::V9RotationContext {
            cells_root: cells_root(&ledger),
            nullifier_root,
            commitments_root,
            revoked_root,
            iroot: iroot8(&receipt_hashes),
            material,
        };
        assert_eq!(
            w,
            produce_in_ctx(&c, &producer_ctx),
            "produce ≡ produce_in_ctx ∘ ctx"
        );

        // The CELL-SIDE context — identical to the producer's on the honest call, and the one
        // knob the red-proof turns.
        let ctx = dregg_cell::commitment::V9RotationContext {
            revoked_root: cell_side_revoked_root,
            ..producer_ctx
        };

        // (2) — THE 1-FELT TWIN. `RotationWitness::state_commit` is `wire_commit(pre_limbs, iroot)`
        // and the cell side is `v9_wire_commit` over `compute_rotated_pre_limbs`: the same chain,
        // and this is the object the rotated trace publishes on `B_STATE_COMMIT`. If this equality
        // is not asserted HERE it is only asserted three crates away, inside proving tests that
        // take minutes, which is how the last drift stayed hidden.
        assert_eq!(
            w.state_commit,
            dregg_cell::commitment::compute_canonical_state_commitment_v9_felt(&c, &ctx),
            "the witness's 1-felt wireCommitR twin and the cell-side rotated commitment are ONE \
             value under ONE context — this is the felt the rotated trace carries on B_STATE_COMMIT"
        );

        // (3) — the SAME limbs the consensus anchor commits, under the SAME context. The anchor is
        // the CHIP chain (`from_wire_commit_chip`), a different chain over the same limbs, so this
        // leg compares through the anchor's own function.
        assert_eq!(
            dregg_circuit::Faithful8::from_wire_commit_chip(&w.pre_limbs, w.iroot).to_bytes32(),
            crate::state_commit::cell_state_commitment(&c, &ctx),
            "the witness producer and the consensus anchor must be one commitment function; only \
             the CONTEXT is allowed to differ between the proof and the receipt"
        );
    }

    #[test]
    fn the_witness_and_the_anchor_are_one_body_under_one_context() {
        the_witness_and_the_anchor_are_one_body(empty_revoked_root_8());
    }

    /// ⚑ **THE RED-PROOF OF THE TIE ABOVE, AS A TEST RATHER THAN AS A PROMISE.**
    ///
    /// Re-runs the tie with the cell side holding `dregg_circuit::heap_root::empty_heap_root_8()`
    /// — the retired `CanonicalHeapTree8` empty root — where the producer holds
    /// [`empty_revoked_root_8`]. That is not a hypothetical: it is the exact pair of literals that
    /// sat on the two sides of `circuit/tests/effect_vm_rotation_flip.rs`'s G3/G4/§4.2
    /// differentials, and the drift they produced survived because this tie handed BOTH sides the
    /// same value and never compared the 1-felt twin at all.
    ///
    /// `expected` pins leg (2) specifically, so a version of this file that deleted the 1-felt
    /// assertion and kept only the chip leg would fail this test rather than pass it.
    #[test]
    #[should_panic(expected = "the witness's 1-felt wireCommitR twin")]
    fn the_tie_goes_red_when_the_cell_side_context_drifts() {
        the_witness_and_the_anchor_are_one_body(dregg_circuit::heap_root::empty_heap_root_8());
    }

    /// The retired heap sentinel is NOT the empty root of any live accumulator, and the three live
    /// empty roots are pairwise distinct.
    ///
    /// `dregg_circuit::heap_root::empty_heap_root_8()` USED to be what
    /// `empty_nullifier_root_8` / `empty_commitments_root_8` / `empty_revoked_root_8` returned. It
    /// is now the empty root of a tree none of them is, and it still appears as a stand-in for all
    /// three in fixtures across `circuit/tests`, `sdk/tests`, `perf` and `tests/src`. Where both
    /// sides of a comparison use the same stand-in nothing is visible; where one side is a real
    /// producer default, the commitment silently moves. This names the trap so a reader meets it
    /// before a differential does — and it goes red the day any of these four converge, which
    /// would make those fixtures accidentally correct rather than correct.
    #[test]
    fn the_retired_heap_sentinel_is_no_accumulator_empty_root() {
        let heap = dregg_circuit::heap_root::empty_heap_root_8();
        let nul = empty_nullifier_root_8();
        let com = empty_commitments_root_8();
        let rev = empty_revoked_root_8();
        for (name, live) in [("nullifier", nul), ("commitments", com), ("revoked", rev)] {
            assert_ne!(
                heap, live,
                "heap_root::empty_heap_root_8() is NOT the empty {name} root — a fixture that \
                 substitutes it commits a different accumulator than the producer does"
            );
        }
        assert_ne!(nul, com, "FNI2 / FCI2 are domain-separated even when empty");
        assert_ne!(nul, rev, "FNI2 / FRI2 are domain-separated even when empty");
        assert_ne!(com, rev, "FCI2 / FRI2 are domain-separated even when empty");
    }

    /// ⚑ **THE SHARED BINDING COMMITS THE LIVE ACCUMULATOR ROOTS, AND NAMES NONE OF THEM.**
    ///
    /// [`SovereignTurnCtx`] is the ONE body both `cipherclerk::prove_sovereign_turn_rotated` and
    /// every fixture that registers its OLD_COMMIT read. Its three accumulator roots are not
    /// parameters — this pins WHICH roots that body chose, so the nullifier/commitments cutover
    /// (the sovereign producer used to publish `heap_root::empty_heap_root_8()` in limbs 26/27 while
    /// `node::turn_proving` already published the live empty roots) cannot be silently walked back.
    ///
    /// It compares against the ACCUMULATORS, not against remembered constants: `NullifierSet::new()
    /// .root8()` and friends are the definitions, so this goes red the day a set's empty root moves
    /// AND the binding fails to move with it — which is the only interesting direction.
    #[test]
    fn the_sovereign_binding_commits_the_live_empty_accumulator_roots() {
        let c = cell(0x11, 77);
        let ctx = SovereignTurnCtx::for_cell(&c, &[[0xABu8; 32]], Default::default());
        // The three roots are the LIVE empty accumulators…
        let pre = ctx.pre_limbs(&c);
        for (name, root, group) in [
            (
                "nullifier",
                empty_nullifier_root_8(),
                dregg_circuit::effect_vm::layout_generated::NULLIFIER_ROOT_GROUP,
            ),
            (
                "commitments",
                empty_commitments_root_8(),
                dregg_circuit::effect_vm::layout_generated::COMMITMENTS_ROOT_GROUP,
            ),
            (
                "revoked",
                empty_revoked_root_8(),
                dregg_circuit::effect_vm::layout_generated::REVOKED_ROOT_GROUP,
            ),
        ] {
            let carried: Vec<BabyBear> = group.iter().map(|&i| pre[i]).collect();
            assert_eq!(
                carried,
                root.limbs().to_vec(),
                "the sovereign binding must commit the LIVE empty {name} root in its limb group"
            );
            assert_ne!(
                carried,
                dregg_circuit::heap_root::empty_heap_root_8()
                    .limbs()
                    .to_vec(),
                "…and never the retired heap sentinel (the {name} slot)"
            );
        }
    }

    /// The registration helper and the witness producer are ONE value under ONE context: what a
    /// fixture registers with `register_sovereign_cell` is exactly the chip 8-felt commit the
    /// producer's BEFORE block publishes on the 16 wide commit PIs.
    ///
    /// This is the equation the executor's OLD_COMMIT tooth compares
    /// (`verify_and_commit_proof_rotated` binds the proof's BEFORE PIs to
    /// `bytes32_to_felt8(stored)`), asserted here at the ONE place both sides are in scope.
    #[test]
    fn the_registration_commitment_is_the_producers_before_block() {
        let c = cell(0x2C, 512);
        let receipts = [[0x01u8; 32], [0x02u8; 32]];
        let ctx = SovereignTurnCtx::for_cell(&c, &receipts, Default::default());
        let w = ctx.witness(&c);

        assert_eq!(
            sovereign_registration_commitment(&c, &receipts),
            dregg_circuit::Faithful8::from_wire_commit_chip(&w.pre_limbs, w.iroot).to_bytes32(),
            "the value a fixture registers IS the producer's published BEFORE 8-felt commit"
        );
        // …and the same body reached through the loose-parts producer, so the binding is not a
        // second limb fill: `produce` with the binding's own roots must land on the same witness.
        let mut ctx_ledger = Ledger::new();
        ctx_ledger.insert_cell(c.clone()).unwrap();
        assert_eq!(
            w,
            produce(
                &c,
                &ctx_ledger,
                &empty_nullifier_root_8(),
                &empty_commitments_root_8(),
                &empty_revoked_root_8(),
                &receipts,
                &Default::default(),
            ),
            "SovereignTurnCtx::witness ≡ produce under the binding's roots"
        );
    }

    #[test]
    fn pre_limb_count_is_187_at_r24() {
        // 1 cells_root + 24 registers + 4 (cap/nullifier/commitments/heap) + 3 (lifecycle/epoch/
        // committed_height) + 6 (disc + perms + vk + mode + fields_root + revoked_root, the
        // WAVE-2/3 + REVOKED-ROOT flag-days; revoked_root = base limb 37)
        // + 51 accumulator-8-felt completion limbs (38..88, lanes 1..7, incl. revoked 82..88)
        // + 24 v12 carrier-material octets (89..112: child_vk8·contract_hash8·pubkey8, ZERO until gate-welded)
        // + 56 v13 fields[0..7] completion lanes 1..7 (113..168)
        // + 7 circuit-only cells_root completion lanes (169..175, ZERO in producer)
        // + 8 NINE-LANE fields[0..7] lane-8 columns (176..183 — the two former pads plus the
        //   flag-day extent bump; `RotatedLayout.fieldLaneCol slot 8 = 176 + slot`)
        // + 3 KEY-NONET ninth lanes (184..186 = `ROTATED_OCTET_NINTH_LANES`: child_vk, contract_hash,
        //   pubkey). `canonical_32_to_felts_8` packs 32 bytes into 8 lanes at 8+8+8+6 bits and DROPS
        //   bits 6-7 of bytes 3,7,…,31 — bit 7 of byte 31 is the Ed25519 sign bit, so A and −A pack
        //   to one byte-identical octet at cost zero and the attacker holds the private half of the
        //   negation. `KeyLanes9` closes it and each of the three octets needs a ninth column.
        //   ⚑ AND IT GREW BY THREE, NOT ONE: `B_SPAN := n + 3 + (n−4)/3` is Nat floor division while
        //   the real chain rounds up, so they agree only at n ≡ 1 (mod 3); 185 is one carrier column
        //   short and 186 fails `bodyAligned`. 187 is the next legal extent.
        //   → body [4..186] = 183 = 61×3 (clean 3-grouping; `B_NUM_CHAIN = 62 = 1 + (187−4)/3`).
        //
        // ⚠ THIS LITERAL IS RE-TYPED ON PURPOSE (`trace_rotated.rs:3214`): re-deriving the geometry
        // by hand each flag day IS the review. Do NOT relax it to `== NUM_PRE_LIMBS`, which would
        // compare the constant against its own definition and check nothing.
        // Stale since 2026-08-01 (`76c3f7b9b` moved the emission 184 → 187 and this crate's three
        // hand-written literals were not carried across); repaired 2026-08-06.
        assert_eq!(NUM_PRE_LIMBS, 187);
    }

    /// THE iroot NON-OMISSION TOOTH (Lean `ReceiptChain8.rchain8_binds_or_collides`): tamper /
    /// truncate / extend / reorder of the receipt log each MOVE the root.
    ///
    /// ⚠ This doc cited `mroot_injective` until 2026-08-01 — a theorem deleted 2026-07-28 as
    /// pigeonhole-false, about a different (MMR) fold. Note also what this test does NOT establish:
    /// it exercises four hand-picked mutations, which is a smoke check, not a bound. The bound is
    /// the Lean theorem; the REFUTATION of the retired 1-felt shape (a real collision, found by
    /// deterministic search, admitted as one history all the way to the signed anchor) is
    /// `tests/iroot_wide_old_admits_new_rejects.rs`.
    #[test]
    fn iroot_binds_the_whole_log() {
        let log = vec![[1u8; 32], [2u8; 32], [3u8; 32]];
        let base = iroot8(&log);
        // tamper a leaf
        let mut tampered = log.clone();
        tampered[1] = [9u8; 32];
        assert_ne!(base, iroot8(&tampered), "tampered leaf must move the root");
        // truncate
        assert_ne!(base, iroot8(&log[..2]), "truncation must move the root");
        // extend
        let mut extended = log.clone();
        extended.push([4u8; 32]);
        assert_ne!(base, iroot8(&extended), "extension must move the root");
        // reorder
        let reordered = vec![log[1], log[0], log[2]];
        assert_ne!(base, iroot8(&reordered), "reorder must move the root");
        // ⚑ FLAG DAY: the empty log is NO LONGER the zero root. It is the domain-separated arity-0
        // chip image, like every sibling accumulator's empty root — a bare zero sentinel aliases
        // them all, and it is also what made the Lean collision extractor non-total
        // (`0 = chipAbsorb8 (…)` names no colliding preimage pair). `state_commit::consensus_ctx`
        // moved with it.
        assert_ne!(
            iroot8(&[]).limbs(),
            [BabyBear::ZERO; 8],
            "the empty receipt root is not a zero sentinel"
        );
        assert_eq!(
            iroot8(&[]),
            empty_iroot_8(),
            "…and the constant is derived, not restated"
        );
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
        // The empty ledger is the FLI2 accumulator's own empty-tree root, at full 8-felt width.
        // ⚠ NOT `heap_root::empty_heap_root_8()`: since the 2026-08-01 key widening the cells tree
        // is not a heap tree at all, and asserting the heap sentinel here would silently re-pin the
        // retired shape.
        assert_eq!(
            cells_root(&Ledger::new()),
            exact_root_faithful8(
                exact_linked_append_root8(EXACT_CELLS_LINKED_DOMAINS, &[]).unwrap()
            )
        );
        assert_ne!(
            cells_root(&Ledger::new()),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "anti-vacuity: the retired heap sentinel must NOT be what the empty ledger commits"
        );
        // wound #23: the root is a genuine 8-felt octet, not a lane-0 squeeze wearing a wide
        // coat. A different cell set must move MORE than lane 0 (a lane-0-only difference would
        // be exactly the ~31-bit component the widening exists to retire).
        assert!(
            cells_root(&l1).limbs()[1..]
                .iter()
                .zip(cells_root(&l3).limbs()[1..].iter())
                .any(|(a, b)| a != b),
            "cells_root must differ in the COMPLETION lanes, not only lane 0"
        );
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
    fn faithful_8felt_commit_distinguishes_authority_near_collision() {
        use dregg_cell::commitment::{
            V9RotationContext, compute_canonical_state_commitment_v9_felt8,
        };
        let mut ledger = Ledger::new();
        let base = Cell::with_balance([3u8; 32], [0u8; 32], 100);
        ledger.insert_cell(base.clone()).unwrap();
        let ctx = V9RotationContext {
            cells_root: cells_root(&ledger),
            nullifier_root: empty_nullifier_root_8(),
            commitments_root: empty_commitments_root_8(),
            revoked_root: empty_revoked_root_8(),
            iroot: iroot8(&[[7u8; 32]]),
            material: Default::default(),
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

        // POST-FLIP three-way differential: the cell twin (`_felt8`, repointed to the CHIP chain)
        // == the deployed circuit primitive `wire_commit_8_chip` (the byte-twin of the
        // published wide carrier). The plain `wire_commit_8` DIVERGES (no arity-tag seeding) — that is
        // why the flip repointed to the chip chain; the executor anchors against THIS.
        let pre = dregg_cell::commitment::compute_rotated_pre_limbs(&base, &ctx);
        assert_eq!(
            dregg_circuit::poseidon2::wire_commit_8_chip(&pre, ctx.iroot.limbs()[0]),
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
