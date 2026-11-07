//! The `Effect` enum: one variant per effect type the AIR proves.
//!
//! Each variant carries the witness data the trace generator needs to
//! emit the corresponding selector-gated row. Per-variant column
//! semantics live in `super::param`; per-variant AIR constraints live in
//! `super::air`.

use crate::field::BabyBear;

/// **Phase B** witness for an [`Effect::AttenuateCapability`]: the structured
/// held + granted capability leaves and the sorted-tree Merkle path that
/// authenticates the held leaf against the actor's `cap_root` and recomputes the
/// narrowed `cap_root`. Built from the actor's [`crate::cap_root::CanonicalCapTree`]
/// via [`crate::cap_root::CanonicalCapTree::attenuation_witness`].
///
/// The held and granted leaves share `slot_hash` / `target` / `breadstuff` (the
/// slot is fixed across an attenuation; only the rights narrow), so one sibling
/// path authenticates both the old and the recomputed root.
///
/// **Phase B2:** the SAME witness shape carries the GrantCapability granter-side
/// delegation row (`Effect::GrantCapability::phase_b`): `held` is the granter's
/// authenticated c-list leaf and `granted` is the leaf installed in the
/// RECIPIENT's c-list — so for grant the granted leaf's `slot_hash` (the
/// recipient's new slot) and `breadstuff` may DIFFER from held's, while
/// `target` is always shared (the delegated cap points at the same target).
/// The AIR keeps the attenuate same-slot/same-breadstuff law via explicit
/// equality gates fired only on Attenuate rows.
#[derive(Clone, Debug, PartialEq)]
pub struct AttenuateWitness {
    /// The HELD (pre-attenuation) leaf — the real committed rights, authenticated
    /// against the old `cap_root` by [`Self::siblings`] / [`Self::directions`].
    pub held: crate::cap_root::CapLeaf,
    /// The GRANTED (post-attenuation, narrowed) leaf.
    pub granted: crate::cap_root::CapLeaf,
    /// Sibling digests along the leaf→root path (bottom-up, len `CAP_TREE_DEPTH`).
    /// Native 8-felt (Phase H-CAP-8): each sibling is a full `cap_node8` digest.
    pub siblings: Vec<[BabyBear; crate::cap_root::CAP_DIGEST_W]>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
    /// The held tier ordinal (None=0…Custom=5) — the lattice ordinal distinct
    /// from the leaf's `auth_tag` felt (which for `Custom` absorbs the vk_hash).
    pub held_tier: u8,
    /// The granted tier ordinal.
    pub granted_tier: u8,
    /// The RAW held expiry HEIGHT (`None` = no bound) — the integer the
    /// monotone-expiry GTE gate range-checks. Bound in-circuit to the held
    /// leaf's encoded-expiry felt via the `encode_expiry` fold site. Must be the
    /// genuine height behind `held.expiry`; heights are assumed `< 2^30` (the
    /// in-circuit range-check bound), as for balances.
    pub held_expiry_height: Option<u64>,
    /// The RAW granted expiry HEIGHT (`None` = no bound).
    pub granted_expiry_height: Option<u64>,
}

/// The Phase-B (cap-crown) witness for a graduated `RevokeCapability` row: the
/// HELD leaf the revoke removes, authenticated against the actor's
/// `old_cap_root` by a membership path. Revoke needs NO narrowed-leaf / rights
/// witness (unlike [`AttenuateWitness`]) — the post `cap_root` is the genuine
/// sorted-tree DELETION of the slot (the ZERO/padding leaf folded up the SAME
/// sibling path), so only the held leaf + its path are witnessed.
#[derive(Clone, Debug, PartialEq)]
pub struct RevokeWitness {
    /// The HELD (revoked) leaf — the real committed cap, authenticated against
    /// the old `cap_root` by [`Self::siblings`] / [`Self::directions`].
    pub held: crate::cap_root::CapLeaf,
    /// Sibling digests along the leaf→root path (bottom-up, len `CAP_TREE_DEPTH`).
    /// Native 8-felt (Phase H-CAP-8): each sibling is a full `cap_node8` digest.
    pub siblings: Vec<[BabyBear; crate::cap_root::CAP_DIGEST_W]>,
    /// Direction bits along the path (0 = current is left child, 1 = right).
    pub directions: Vec<u8>,
}

/// An effect to be proven in the VM.
#[derive(Clone, Debug, PartialEq)]
pub enum Effect {
    /// No operation (used for padding).
    NoOp,
    /// Transfer balance.
    Transfer {
        amount: u64,
        /// 0 = incoming (credit), 1 = outgoing (debit).
        direction: u32,
    },
    /// Set a custom field value.
    SetField { field_idx: u32, value: BabyBear },
    /// **The single-tick grain turn** (initiative 10, `grain-session/SINGLE-TICK-DESCRIPTOR.md`):
    /// ONE executor turn on the grain worker cell as ONE row. Slots 3..=7 take `values[j - 3]`
    /// (lane 0 of each written 32-byte value; the high lanes ride the rotated after block and are
    /// published by the member's completion pins), the balance is debited by `fee` (the executor's
    /// Phase-1 `turn.fee`), and the nonce ticks ONCE. Slots 0..=2, the cap root and the reserved
    /// column are untouched. Proven by `grainTurnVmDescriptor2R24` (selector [`sel::GRAIN_TURN`]).
    ///
    /// [`sel::GRAIN_TURN`]: crate::effect_vm::columns::sel::GRAIN_TURN
    GrainTurn { values: [BabyBear; 5], fee: u64 },
    /// Grant a capability — the cross-cell delegation. ONE selector, TWO row
    /// roles (params[1] `GRANT_DIRECTION`, mirroring `Transfer.direction`):
    ///
    /// * **direction 0 — recipient install (legacy).** The row covers the
    ///   RECIPIENT cell (`apply_grant_capability` lands the new entry in the
    ///   `to` cell's c-list); `cap_entry` is the entry digest and the AIR's
    ///   cap_root advance uses limb[0] (`params[0]`):
    ///   `new_cap_root == hash_2_to_1(old_cap_root, cap_entry[0])`.
    ///   32-byte widening (effect-vm-hash-widen lane, 2026-05-28): all 8 limbs
    ///   bind via `compute_effects_hash` → `PI[EFFECTS_HASH]`.
    ///
    /// * **direction 1 — granter-side delegation row (cap Phase B2, `phase_b:
    ///   Some`).** The row covers the GRANTER cell, whose
    ///   `state_before.cap_root` IS the tree holding the delegated-from cap, so
    ///   the held rights are membership-AUTHENTICATED in-circuit (same
    ///   machinery as `AttenuateCapability`). The granter's own tree is
    ///   unchanged by delegating (the install lands in the recipient's tree),
    ///   so the row's cap_root PASSES THROUGH. The AIR pins `cap_entry[0]` to
    ///   the GRANTED CapLeaf's 7-field Poseidon2 digest recomputed in-circuit
    ///   from its actual rights fields (slot/target/auth/mask/expiry/
    ///   breadstuff — not an opaque digest) and enforces the three non-amp
    ///   order gates (submask + AuthRequired lattice + expiry-monotone) on
    ///   (granted vs held).
    GrantCapability {
        cap_entry: [BabyBear; 8],
        /// **Phase B2** granter-side non-amp witness (the same shape as the
        /// Attenuate witness — held + granted leaves, the held membership
        /// path in the GRANTER's tree, tier ordinals, raw expiry heights).
        /// `Some` ⇒ the row is the direction-1 delegation row; the granted
        /// leaf carries its OWN `slot_hash` (the recipient's new slot) and
        /// `breadstuff`, while `target` must equal the held cap's target
        /// (enforced structurally — one shared TARGET column hashes into both
        /// leaves). `None` ⇒ the legacy direction-0 recipient-install row.
        /// Excluded from the 8-limb `compute_effects_hash` binding except for
        /// the direction felt + held slot_hash absorbed for witnessed rows.
        phase_b: Option<Box<AttenuateWitness>>,
    },
    /// Revoke a capability (mix the revoked slot's hash into the c-list Merkle root).
    /// Like `GrantCapability`, the AIR constraint enforces
    /// `new_cap_root == hash_2_to_1(old_cap_root, slot_hash[0])` so a malicious
    /// prover cannot make up an arbitrary new root.
    ///
    /// 32-byte widening: `slot_hash` is the full 32-byte slot hash projected
    /// into 8 BabyBear limbs (see [`Effect::GrantCapability`]). The cap_root
    /// advance uses limb[0]; all 8 limbs bind via effects_hash.
    ///
    /// GRADUATED (cap-crown): with `phase_b = Some(_)` the row carries the
    /// [`RevokeWitness`] that authenticates the revoked leaf against
    /// `old_cap_root` (membership-open) and forces `new_cap_root` to be the
    /// genuine sorted-tree slot DELETION (the ZERO/padding leaf folded up the
    /// same path). `None` is the pre-graduation pinned-digest form
    /// (`new_cap_root == H2(old_cap_root, slot_hash)`).
    RevokeCapability {
        slot_hash: [BabyBear; 8],
        /// The cap-crown membership + zero-fold witness. Boxed (large), excluded
        /// from `effects_hash` binding except for the slot_hash[0] already bound.
        phase_b: Option<Box<RevokeWitness>>,
    },
    /// EmitEvent: stateless side-effect. Mirrors the runtime `Event` canonical
    /// encoding (topic ‖ data): `topic_hash` is the 32-byte BLAKE3 of the topic
    /// symbol, projected into 8 BabyBear felts (4 bytes per felt), and
    /// `payload_hash` is the 32-byte BLAKE3 of the concatenated `Vec<FieldElement>`
    /// data, projected the same way. Both contribute to `effects_hash`
    /// (binding the prover to the exact (topic, payload) bytes the executor
    /// observed), and the AIR additionally pins the low 4 felts of each into
    /// row params via a selector-gated PI-equality constraint (see
    /// `EMIT_EVENT_TOPIC_HASH` / `EMIT_EVENT_PAYLOAD_HASH` PI slots). The AIR
    /// constraint enforces full state passthrough — no balance, field, or
    /// cap_root change. Nonce increments by 1 like any non-NoOp effect.
    ///
    /// Soundness note: the per-row PI-equality constraint forces all
    /// emit-event rows in one proof to share the same (topic, payload) hashes.
    /// Multi-emit-distinct-hashes per proof is out of current scope; the
    /// off-AIR verifier's PI-match loop reads `EMIT_EVENT_COUNT` and refuses
    /// to derive multi-hash PI from the runtime turn (forcing the executor
    /// to split the turn into separate proofs if needed).
    EmitEvent {
        /// 32-byte BLAKE3 of the event topic symbol, projected into 8 BabyBear
        /// felts via 4-bytes-per-felt little-endian packing. Position 0 carries
        /// the low 4 bytes; position 7 the high 4 bytes.
        topic_hash: [BabyBear; 8],
        /// 32-byte BLAKE3 of the concatenated event data fields, same packing.
        payload_hash: [BabyBear; 8],
    },
    /// SetPermissions: update a cell's permission table. Permissions live
    /// outside the VM's tracked state, so the AIR enforces full state
    /// passthrough (balance / fields / cap_root unchanged) and the
    /// `permissions_hash` parameter binds the new permissions into
    /// effects_hash so the prover commits to the specific update.
    ///
    /// 32-byte widening: `permissions_hash` is the full 32-byte hash projected
    /// into 8 BabyBear limbs (see [`Effect::GrantCapability`]); the AIR anchors
    /// limb[0] into `params[0]` and all 8 limbs bind via effects_hash.
    SetPermissions { permissions_hash: [BabyBear; 8] },
    /// SetVerificationKey: update a cell's verification key (Option<VK>).
    /// Same shape as SetPermissions: VK lives off-trace, the AIR enforces
    /// state passthrough and `vk_hash` binds the new VK into effects_hash.
    /// `vk_hash == [0; 8]` represents "set to None" (revoke the VK).
    ///
    /// 32-byte widening: `vk_hash` is the full 32-byte hash projected into 8
    /// BabyBear limbs (see [`Effect::GrantCapability`]).
    SetVerificationKey { vk_hash: [BabyBear; 8] },
    /// RefreshDelegation: re-arm a SPECIFIC child cell's delegation snapshot
    /// from its parent (self-refresh — the child IS the actor). State
    /// passthrough; `child_hash` binds the refreshed child cell and
    /// `snapshot_value` binds the new snapshot commitment into effects_hash, so
    /// a light client knows WHICH delegation was re-armed and to WHAT value (the
    /// DELEG-tree UPDATE-at-key the cap-write wrapper proves). The genuine move
    /// is non-amplifying (`granted = held` shape; the value is the parent's
    /// fresh c-list commitment).
    ///
    /// 32-byte widening: both are full 32-byte hashes projected into 8 BabyBear
    /// limbs (see [`Effect::GrantCapability`]); the AIR anchors `child_hash[0]`
    /// into `params[0]`, and all 16 limbs bind via `compute_effects_hash`.
    RefreshDelegation {
        child_hash: [BabyBear; 8],
        snapshot_value: [BabyBear; 8],
    },
    /// IncrementNonce: explicit runtime nonce bump. The nonce transition is
    /// the global non-NoOp row invariant; this selector binds that the row is
    /// specifically an IncrementNonce effect rather than padding or another
    /// passthrough sibling.
    IncrementNonce,
    /// RevokeDelegation: invalidate a child cell's delegation. State
    /// passthrough; `child_hash` binds the target cell into effects_hash.
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    RevokeDelegation { child_hash: [BabyBear; 8] },
    /// CreateCell: actor records the creation of a new cell. Passthrough.
    /// `create_hash` = BLAKE3(pk ‖ token_id ‖ balance).
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    CreateCell { create_hash: [BabyBear; 8] },
    /// SpawnWithDelegation: actor records spawning a child cell.
    /// `spawn_hash` = BLAKE3(child_pk ‖ child_token_id ‖ max_staleness).
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    SpawnWithDelegation { spawn_hash: [BabyBear; 8] },
    /// ExerciseViaCapability: actor records exercise of a c-list cap on a
    /// target cell. From the actor's perspective the actor's own state
    /// doesn't change; `exercise_hash` = BLAKE3(cap_slot ‖ inner_effects_hash).
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    ExerciseViaCapability { exercise_hash: [BabyBear; 8] },
    /// Introduce: 3-party introduction. Passthrough from the introducer's
    /// POV; `intro_hash` = BLAKE3(introducer ‖ recipient ‖ target ‖ perm).
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    Introduce { intro_hash: [BabyBear; 8] },
    /// PipelinedSend: dispatch a future action against an EventualRef.
    /// Passthrough; `send_hash` = BLAKE3(target.source_turn ‖ target.output_slot ‖ action.hash()).
    ///
    /// 32-byte widening: full 32-byte hash → 8 BabyBear limbs (see
    /// [`Effect::GrantCapability`]); AIR anchors limb[0] into `params[0]`.
    PipelinedSend { send_hash: [BabyBear; 8] },
    /// BridgeMint: actor mints `value_lo` from a portable proof. Balance
    /// credit (mirrors NoteSpend). `mint_hash` binds (nullifier, root,
    /// dest_federation, asset_type).
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `value_full` carries
    /// the full u64 (see `CreateEscrow` (retired) above for rationale).
    BridgeMint {
        value_lo: BabyBear,
        mint_hash: BabyBear,
        /// Full u64 value (30-bit-trunc fix).
        value_full: u64,
    },
    /// Mint: the DEDICATED cap-gated SUPPLY-CREATION verb (SUPPLY-MODEL.md
    /// Stage 2b — the circuit image of the turn-layer `Effect::Mint`). Balance
    /// credit at `param1` (`value_lo`), exactly mirroring `BridgeMint`'s proven
    /// body, but fired on the DEDICATED `sel::MINT` selector column so a
    /// supply-mint proves + self-verifies under its OWN selector rather than
    /// riding `BridgeMint`'s slot. Routes to `supplyMintVmDescriptor2R24`
    /// (`EffectVmEmitRotationV3.supplyMintV3`); the selector-gate forgery tooth
    /// bites a `[Mint, foreign]` trace under that descriptor exactly as it does
    /// for the bridge-mint member.
    Mint {
        value_lo: BabyBear,
        mint_hash: BabyBear,
        /// Full u64 value (mirrors `BridgeMint.value_full`).
        value_full: u64,
    },
    /// Spend a note (reveal nullifier, credit balance).
    NoteSpend { nullifier: BabyBear, value: u64 },
    /// Create a note (create commitment, debit balance).
    NoteCreate { commitment: BabyBear, value: u64 },
    /// Custom cell program dispatch.
    ///
    /// State flows through normally (continuity enforced by the Effect VM).
    /// Domain-specific constraints are proven in a separate proof identified by
    /// `custom_proof_commitment`. The Effect VM AIR does not verify the external
    /// sub-proof with a row-local gate; instead the rotated Custom descriptor
    /// PUBLISHES `custom_proof_commitment` / `custom_program_vk_hash` as public
    /// inputs (Lean `EffectVmEmitRotationV3.customPiExposure`), and the per-turn
    /// FOLD connects those PIs to the custom sub-proof leaf (the `custom_proof_bind`
    /// recursion / `EngineBinding` carrier) — so a pure light client verifying the
    /// aggregate witnesses the binding. The remaining wire step is connecting the
    /// custom leaf's 4-felt PI-commitment to these PI slots in the joint-turn fold.
    Custom {
        /// VK hash identifying the custom program.
        ///
        /// **PI layout v2** (`pi::VK_PI_LAYOUT_VERSION == 2`): widened from
        /// 4 BabyBear felts (~16 bytes; 80-bit registry binding) to 8 felts
        /// (~32 bytes; ~248-bit registry binding) so that two custom programs
        /// whose 32-byte VKs collide only in the upper 16 bytes dispatch to
        /// distinct handlers. Pre-v2 callers zero-padded the upper 16 bytes,
        /// silently allowing such collisions to alias.
        program_vk_hash: [BabyBear; 8],
        /// Commitment to the external custom program proof's public inputs.
        ///
        /// **FLAG-DAY ROTATION (proof-bridge blocker #2): 4 → 8 felts.** The full
        /// 8-felt `WideHash` squeeze (~124-bit birthday collision resistance,
        /// `custom_proof_pi_commitment`) — limbs 0..4 ride the Custom row's param
        /// columns (cols 72..76), limbs 4..8 the member-local commit-teeth
        /// columns; all 8 are published as descriptor PIs the per-turn fold
        /// binds. Old 4-felt artifacts are refused at the versioned admission
        /// boundary, never silently widened.
        proof_commitment: [BabyBear; 8],
    },
    /// MakeSovereign: transition cell mode from managed (0) to sovereign (1).
    /// State constraint: mode_flag changes from 0 to 1. Balance/fields preserved.
    MakeSovereign,
    /// CreateCellFromFactory: record factory VK hash + provenance.
    /// Uses aux columns for factory_vk and child_vk_derived.
    CreateCellFromFactory {
        /// Factory VK hash.
        factory_vk: BabyBear,
        /// Derived child VK hash (provenance record).
        child_vk_derived: BabyBear,
    },
    /// Burn: explicit, non-conservation reduction of the cell's balance.
    /// Unlike `Transfer { direction: 1 }`, no destination credit happens —
    /// the supply is provably reduced and the row is distinguishable from
    /// a Transfer at the algebraic level (selector + dedicated
    /// `was_burn_flag == 1` constraint).
    ///
    /// Relationship to `effect_action_air::SCHEMA_BURN`:
    ///   The two coexist as complementary attestations. `SCHEMA_BURN`
    ///   carries a per-`Effect::Burn` binding proof with the snapshot-
    ///   aware algebraic invariant `old_balance - new_balance == amount`
    ///   (executor-injected via `effect_binding_proofs`). This
    ///   `VmEffect::Burn` lives inside the cell's whole-turn Effect-VM
    ///   trace and attests "this Burn occupied row X in the cell's
    ///   effect sequence, distinct from any Transfer / NoteCreate".
    ///   The two layers cover different gaps; the SCHEMA_BURN remains
    ///   the canonical place for the balance-subtraction algebraic
    ///   binding.
    ///
    /// 30-bit-trunc note: `amount_lo` carries the low 30 bits for the
    /// balance-debit constraint (BabyBear can hold values < 2^31);
    /// `amount_full` carries the full u64 for `compute_effects_hash`
    /// binding via 4×16-bit limbs (matches the BridgeMint/BridgeLock
    /// shape).
    Burn {
        /// Hash of the target cell whose balance is reduced. Full 32-byte hash
        /// projected into 8 BabyBear limbs (the same shape `CellDestroy` /
        /// `CellSeal` / `Refusal` already carry); the trace anchors limb[0] into
        /// params[0] and all 8 limbs bind via `compute_effects_hash`.
        ///
        /// Was ONE felt (`fold_bytes32_to_bb`) until the felt-width #25 repair.
        /// The narrow form was the LAST 1-felt `target_hash` in this enum, and
        /// its fold is `𝔽_p`-LINEAR in the limb vector — a directly-chosen
        /// 32-byte preimage collides in O(1) (one linear solve), and a
        /// `CellId::derive_raw` preimage in ~2^31. Nothing in the DEPLOYED
        /// circuit reads params[0] on a burn row (`burnVmDescriptor2R24`
        /// references col 68 zero times), so this widening changes no in-circuit
        /// binding — it removes a pre-priced liability from the one carrier the
        /// target does reach: `effects_hash`.
        target_hash: [BabyBear; 8],
        /// Burn amount, low 30 bits (for the balance-debit constraint).
        amount_lo: BabyBear,
        /// Full u64 amount (binds via the 4×16-bit-limb path in
        /// `compute_effects_hash`).
        amount_full: u64,
    },
    /// CellDestroy: permanently retire a cell. Lifecycle lives off-trace,
    /// but the AIR binds the `target_hash` and the `death_certificate_hash`
    /// into params (and through them into effects_hash) so a verifier
    /// replaying the trace can distinguish a CellDestroy from a generic
    /// SetPermissions row.
    ///
    /// State passthrough: balance, fields, and cap_root all unchanged;
    /// nonce ticks like any non-NoOp effect.
    CellDestroy {
        /// Hash of the cell being destroyed. Full 32-byte hash projected into
        /// 8 BabyBear limbs (see `CreateSealPair` (retired)); the AIR anchors
        /// limb[0] into params[0].
        target_hash: [BabyBear; 8],
        /// `DeathCertificate::certificate_hash()`, full 32 bytes projected into
        /// 8 BabyBear limbs. AIR anchors limb[0] into params[1].
        death_certificate_hash: [BabyBear; 8],
    },
    /// AttenuateCapability: monotonically narrow an existing c-list cap.
    /// Distinct from RevokeCapability: revoke removes a slot from the
    /// c-list root by hashing `slot_hash` in; attenuate REPLACES the
    /// slot's existing entry with a strictly narrower commitment. The
    /// AIR's cap_root advance encodes BOTH the slot identity and the
    /// new narrower entry, so a `RevokeCapability` proof cannot pass as
    /// an `AttenuateCapability` proof.
    ///
    /// State: balance / fields unchanged; cap_root advances to
    /// `hash_2_to_1(old_cap_root, hash_2_to_1(cap_slot_hash, narrower_commitment))`.
    AttenuateCapability {
        /// Hash of the c-list slot being narrowed. Full 32 bytes projected into
        /// 8 BabyBear limbs (see `CreateSealPair` (retired)). The AIR's cap_root
        /// advance uses limb[0] (params[0]); all 8 limbs bind via effects_hash.
        cap_slot_hash: [BabyBear; 8],
        /// Commitment to the new (narrower) permissions / facet / expiry.
        /// Full 32 bytes projected into 8 BabyBear limbs; AIR uses limb[0]
        /// (params[1]) in the cap_root advance.
        narrower_commitment: [BabyBear; 8],
        /// **Phase B** in-circuit non-amplification witness. When present, the
        /// trace generator emits the GENUINE sorted-tree leaf-update (the
        /// `cap_root` advances from the held leaf's authenticated position to the
        /// narrowed leaf, recomputed over the real Merkle path) and fills the
        /// AIR's non-amp gate witness (membership-open + submask + AuthRequired
        /// lattice + expiry). When `None` (legacy callers), the row keeps the
        /// pre-Phase-B opaque 2-of-2 cap-root fold and does NOT satisfy the
        /// Phase-B gates — only a witnessed Attenuate turn is provable through
        /// the audited p3 path. Boxed to keep the enum small; excluded from
        /// `compute_effects_hash` (the public binding is still the two 8-limb
        /// commitments).
        phase_b: Option<Box<super::AttenuateWitness>>,
    },
    /// CellSeal: transition a cell lifecycle to `Sealed`. The AIR enforces
    /// state passthrough (balance/fields/cap_root unchanged; only the
    /// lifecycle off-trace changes). `target_hash` binds the specific cell;
    /// `reason_hash` commits to the sealing rationale so a seal without a
    /// declared reason cannot satisfy the AIR. Both params fold into
    /// `effects_hash` (domain tag 49) so the proof distinguishes a
    /// `CellSeal` from any generic `SetPermissions` row.
    ///
    /// Distinct from `Effect::Seal { field_idx }` (which sets a
    /// sealed-field bit in the cell's in-trace `reserved` mask): this
    /// variant records the lifecycle-level seal of the whole cell.
    CellSeal {
        /// Hash of the cell being sealed. Full 32 bytes projected into 8
        /// BabyBear limbs (see `CreateSealPair` (retired)); AIR anchors limb[0]
        /// into params[0].
        target: [BabyBear; 8],
        /// BLAKE3 of the sealing reason (cleartext lives off-chain). Full 32
        /// bytes projected into 8 BabyBear limbs; AIR anchors limb[0] into
        /// params[1].
        reason_hash: [BabyBear; 8],
    },
    /// CellUnseal: reverse a cell seal (lifecycle `Sealed` → `Live`).
    /// State passthrough. `target_hash` binds the cell being unsealed;
    /// the absence of a `reason_hash` param (vs. `CellSeal`) is itself
    /// algebraically distinguishing — a `CellSeal` row has two non-zero
    /// params whereas a `CellUnseal` row has only one. Domain tag 50.
    CellUnseal {
        /// Hash of the cell being unsealed. Full 32 bytes projected into 8
        /// BabyBear limbs (see `CreateSealPair` (retired)); AIR anchors limb[0]
        /// into params[0] and mirrors it into aux[0].
        target: [BabyBear; 8],
    },
    /// ReceiptArchive: record that the cell's receipt-chain prefix through
    /// `archive_end_height` is summarized by a checkpoint. Lifecycle
    /// transitions to `Archived` off-trace; AIR enforces state passthrough
    /// and binds `archive_end_height` (as a BabyBear-truncated u64) plus
    /// `terminal_receipt_hash` into `effects_hash` (domain tag 51).
    ///
    /// Two params make this algebraically distinct from any single-hash
    /// passthrough (e.g. `SetPermissions`): a `SetPermissions` row only
    /// carries one non-zero param.
    ReceiptArchive {
        /// Hash of the cell targeted by the archive. Full 32 bytes projected
        /// into 8 BabyBear limbs (see `CreateSealPair` (retired)); AIR anchors
        /// limb[0] into params[0].
        target: [BabyBear; 8],
        /// `archive_end_height` low-30-bits truncation (enough for u32
        /// block heights; full u64 encoded separately through the
        /// `compute_effects_hash` limb path if needed). The AIR binds
        /// this value directly into params[1] and thence into effects_hash.
        /// This is a scalar height, NOT a 32-byte hash, so it stays a single
        /// `BabyBear`.
        archive_end_height: BabyBear,
        /// BLAKE3 of the receipt at `archive_end_height`. The live
        /// chain's `previous_receipt_hash` at height+1 must equal this. Full 32
        /// bytes projected into 8 BabyBear limbs; AIR anchors limb[0] into
        /// params[2].
        terminal_receipt_hash: [BabyBear; 8],
    },
    /// Refusal: evidence-of-absence. The prover commits that they did
    /// NOT perform `offered_action_commitment` within the declared window.
    /// State passthrough for the target cell (nonce ticks, audit slot
    /// records the refusal off-trace). Both `target_hash` and `reason_hash`
    /// bind into `effects_hash` (domain tag 52), making a `Refusal` row
    /// algebraically distinct from any other 2-param passthrough because
    /// the selector gate is unique.
    ///
    /// `reason_hash` encodes the `RefusalReason` discriminant (Declined=0,
    /// NoAuthority=1, WindowExpired=2, Custom=3) as a BabyBear scalar,
    /// XOR-mixed with the low 29 bits of `offered_action_commitment[0..4]`
    /// so the proof binds to a specific commitment + reason pair without
    /// exposing the full 32-byte commitment in params.
    Refusal {
        /// Hash of the cell issuing the refusal. Full 32 bytes projected into
        /// 8 BabyBear limbs (see `CreateSealPair` (retired)); AIR anchors
        /// limb[0] into params[0].
        target: [BabyBear; 8],
        /// Reason-encoded binding: `discriminant ^ offered_action_commitment`,
        /// full 32 bytes projected into 8 BabyBear limbs. AIR anchors limb[0]
        /// into params[1]; all 8 limbs bind via effects_hash, so the proof now
        /// commits to the full 256-bit (reason, commitment) pair rather than a
        /// 4-byte equivalence class.
        reason_hash: [BabyBear; 8],
    },
}
