//! Column layout constants for the Effect VM AIR trace.
//!
//! Defines `EFFECT_VM_WIDTH`, the per-effect-class column block bases,
//! and four sub-modules that name each column by purpose:
//! - `sel` — one boolean column per effect type (NUM_EFFECTS = 46).
//! - `state` — 14 columns describing cell state at row enter/exit.
//! - `param` — 8 effect-typed parameter columns.
//! - `aux_off` — NUM_AUX auxiliary witness columns.

/// Total trace width.
/// Layout: 46 selectors + 14 state_before + 8 params + 14 state_after + 23 aux = 105.
/// (aux[8..10] = state commitment intermediates;
///  aux[11] = cumulative custom-effect count (sum-check, Stage 1);
///  aux[12..20] = old_reserved bit-decomposition for sealing honesty (Stage 2);
///  aux[20] = mode_flag bit;
///  aux[21] = ResizeQueue delta sign (Stage 2: 0=grow, 1=shrink);
///  aux[22] = ResizeQueue |delta| magnitude (Stage 2))
///
/// Stage 7 / P1.C aux semantics for CapTP variants (within aux[0..1, 6..7]):
///   NB: aux[2..5] are reserved on row 0 for delta_mag / delta_sign /
///   effects_hash_4[0..1] boundary writes (see line ~4471). Per-effect
///   Merkle witnesses must avoid those slots on row 0; we use
///   aux[6..7] which are exclusive per-row selector-gated.
///
///   ExportSturdyRef row:
///     aux[0] = derived swiss number (existing).
///   EnlivenRef row (was tautological; now bound to swiss_table_root):
///     aux[0] = root  (= state_after.fields[4]).
///     aux[1] = leaf = hash_2_to_1(swiss, hash_2_to_1(cell_id, perms)).
///     aux[6] = Merkle sibling, pinned to state_before.fields[4]
///              (old swiss_table_root) — append-only chain.
///     aux[7] = chosen = hash_2_to_1(leaf, sibling).
///     AIR constrains aux[7] == aux[0] == state_after.fields[4]
///     AND aux[6] == state_before.fields[4].
///     (committed swiss_table_root mirror; full state_commitment
///     binds via PI).
///   DropRef row (holder_federation now bound to refcount_table_root):
///     aux[0] = inverse(refcount_param)  (refcount > 0 witness; existing).
///     aux[1] = leaf = hash_2_to_1(cell_id, holder_federation).
///     aux[6] = Merkle sibling, pinned to state_before.fields[3]
///              (old refcount_table_root) — append-only chain.
///     aux[7] = chosen = hash_2_to_1(leaf, sibling).
///     AIR constrains aux[7] == state_after.fields[3]
///     AND aux[6] == state_before.fields[3].
///     (committed refcount_table_root mirror).
///   ValidateHandoff row (was tautological; now bound to PI
///     APPROVED_HANDOFFS_BASE position 0):
///     aux[0] = leaf = hash_2_to_1(cert_hash,
///              hash_2_to_1(recipient_pk, introducer_pk)).
///     aux[1] = Merkle sibling (prover-supplied).
///     aux[6] = chosen = hash_2_to_1(leaf, sibling).
///     AIR constrains aux[6] == approved_set_root (PARAM) and
///     PARAM == PI[APPROVED_HANDOFFS_BASE]  (executor PI-match).
///     Consume-on-use lives at the executor (it rotates the
///     federation's approved-handoffs root after a successful
///     ValidateHandoff; replays present a non-membership witness to
///     the next AIR proof).
/// Total trace width.
/// Stage 2: 105 (46 selectors + 14 state_before + 8 params + 14 state_after + 23 aux).
/// Sovereign-witness teeth: 110 (+ 5 sovereign-witness aux cols).
/// Near-miss aliasing closure (#100 follow-up): 113 (+ 3 selectors for Burn,
/// CellDestroy, AttenuateCapability — see those variants on `Effect`).
/// AIR-impl lane (#119): 117 (+ 4 selectors for CellSeal, CellUnseal,
/// ReceiptArchive, Refusal).
/// IncrementNonce lane: 118 (+ 1 selector for explicit nonce-only turns).
/// γ.2 federation+owner binding (#131/#132): 126 (+ 8 aux cols:
/// 4 FEDERATION_ID + 4 OWNER_CELL_ID, row-0-pinned to the matching PI slots).
pub const EFFECT_VM_WIDTH: usize = 126;

/// Number of effect types (selectors).
pub const NUM_EFFECTS: usize = 54;

/// Selector column indices.
pub mod sel {
    pub const NOOP: usize = 0;
    pub const TRANSFER: usize = 1;
    pub const SET_FIELD: usize = 2;
    pub const GRANT_CAP: usize = 3;
    pub const NOTE_SPEND: usize = 4;
    pub const NOTE_CREATE: usize = 5;
    pub const CREATE_OBLIGATION: usize = 6;
    pub const FULFILL_OBLIGATION: usize = 7;
    /// Custom cell program dispatch: state flows normally, but domain-specific
    /// constraints are proven externally. The Effect VM binds to the external
    /// proof via `custom_proof_commitment` in the params.
    pub const CUSTOM: usize = 8;
    /// Slash an expired obligation: transfer locked stake to beneficiary.
    pub const SLASH_OBLIGATION: usize = 9;
    /// Seal: lock a field against mutation via sealed_field_mask.
    pub const SEAL: usize = 10;
    /// Unseal: unlock a sealed field (requires brand matching).
    pub const UNSEAL: usize = 11;
    /// MakeSovereign: transition cell mode_flag from 0 to 1.
    pub const MAKE_SOVEREIGN: usize = 12;
    /// CreateCellFromFactory: record factory VK hash + provenance.
    pub const CREATE_CELL_FROM_FACTORY: usize = 13;
    /// ExportSturdyRef: export a cell as a sturdy reference (creates swiss entry).
    pub const EXPORT_STURDY_REF: usize = 14;
    /// EnlivenRef: enliven a sturdy ref (validate swiss, create routing).
    pub const ENLIVEN_REF: usize = 15;
    /// DropRef: drop a remote reference (GC decrement).
    pub const DROP_REF: usize = 16;
    /// ValidateHandoff: validate a handoff certificate (check cert hash membership).
    pub const VALIDATE_HANDOFF: usize = 17;
    /// AllocateQueue: create a new MerkleQueue (storage Phase 2).
    pub const ALLOCATE_QUEUE: usize = 18;
    /// EnqueueMessage: append a message to a queue (storage Phase 2).
    pub const ENQUEUE_MESSAGE: usize = 19;
    /// DequeueMessage: advance queue head, reveal message (storage Phase 2).
    pub const DEQUEUE_MESSAGE: usize = 20;
    /// ResizeQueue: change queue capacity (storage Phase 2).
    pub const RESIZE_QUEUE: usize = 21;
    /// AtomicQueueTx: prove an atomic cross-queue transaction (storage Phase 3).
    pub const ATOMIC_QUEUE_TX: usize = 22;
    /// PipelineStep: prove a pipeline step correctly routed a message (storage Phase 3).
    pub const PIPELINE_STEP: usize = 23;
    /// RevokeCapability: remove a capability slot from the c-list Merkle root.
    /// Mirrors GRANT_CAP but binds the slot's hash instead of a new cap_entry.
    pub const REVOKE_CAPABILITY: usize = 24;
    /// EmitEvent: stateless side-effect; commits an event hash to effects_hash
    /// but does not modify any state column (balance, fields, cap_root all
    /// pass through unchanged; nonce increments like any non-NoOp effect).
    pub const EMIT_EVENT: usize = 25;
    /// SetPermissions: update the cell's permission table. The VM doesn't
    /// model permissions in its state columns (they live in the cell's
    /// off-trace manifest), so the AIR enforces state-passthrough and binds
    /// a hash of the new permissions into effects_hash.
    pub const SET_PERMISSIONS: usize = 26;
    /// SetVerificationKey: update the cell's circuit/predicate VK. Like
    /// SET_PERMISSIONS, the VK lives outside the VM trace, so the AIR
    /// enforces full state passthrough and the new VK hash is bound into
    /// effects_hash.
    pub const SET_VERIFICATION_KEY: usize = 27;
    /// CreateSealPair: register a new sealer/unsealer brand pair. State
    /// passthrough; pair_hash binds (sealer_holder, unsealer_holder) into
    /// effects_hash.
    pub const CREATE_SEAL_PAIR: usize = 28;
    /// RefreshDelegation: bump the cell's delegation epoch. No VM state
    /// columns track the epoch directly, so this is a passthrough variant
    /// (the epoch lives off-trace); the selector alone records the intent.
    pub const REFRESH_DELEGATION: usize = 29;
    /// RevokeDelegation: invalidate a child cell's delegation snapshot.
    /// State passthrough; child_hash binds the target into effects_hash.
    pub const REVOKE_DELEGATION: usize = 30;
    /// CreateCell: actor creates a new cell. The actor's own state doesn't
    /// change (CreateCell rejects non-zero initial balance via executor
    /// check). Passthrough; create_hash binds (pk, token_id, balance).
    pub const CREATE_CELL: usize = 31;
    /// SpawnWithDelegation: actor spawns a child with a delegation snapshot.
    /// Actor's state passthrough; spawn_hash binds (child_pk, child_token_id,
    /// max_staleness) into effects_hash.
    pub const SPAWN_WITH_DELEGATION: usize = 32;
    /// BridgeCancel: cancel a pending bridge by its nullifier. Local state
    /// passthrough (the bridge state lives off-trace); cancel_hash binds the
    /// nullifier into effects_hash.
    pub const BRIDGE_CANCEL: usize = 33;
    /// ExerciseViaCapability: invoke a cap from the actor's c-list. The
    /// inner_effects act on the TARGET cell, not the actor; from the actor's
    /// perspective this is a passthrough that records (cap_slot,
    /// hash(inner_effects)).
    pub const EXERCISE_VIA_CAPABILITY: usize = 34;
    /// Introduce: 3-party introduction; introducer's state doesn't change.
    /// Passthrough from the introducer's POV (recipient c-list updates are
    /// projected separately when this turn is replayed against the
    /// recipient cell).
    pub const INTRODUCE: usize = 35;
    /// PipelinedSend: dispatch a future action against an EventualRef. The
    /// dispatching cell's state doesn't change (the dispatch is deferred);
    /// passthrough with hash(target ‖ action_hash).
    pub const PIPELINED_SEND: usize = 36;
    /// CreateEscrow: actor locks `amount` from balance into an escrow.
    /// Balance debit (mirror NoteCreate's constraint shape).
    pub const CREATE_ESCROW: usize = 37;
    /// BridgeLock: actor locks `value` from balance into a cross-federation
    /// bridge. Balance debit.
    pub const BRIDGE_LOCK: usize = 38;
    /// CreateCommittedEscrow: actor opens a privacy-preserving escrow
    /// (value hidden in Pedersen commitment). Passthrough — the AIR can't
    /// verify the debit amount without opening the commitment, which
    /// requires its own range proof outside the Effect VM scope.
    pub const CREATE_COMMITTED_ESCROW: usize = 39;
    /// BridgeMint: actor mints tokens carried by a portable proof from
    /// another federation. Balance credit (mirror NoteSpend).
    pub const BRIDGE_MINT: usize = 40;
    /// BridgeFinalize: actor records finalization of a pending bridge.
    /// Outcome depends on whether the bridge was a mint or lock; balance
    /// resolution is the executor's responsibility. Passthrough with
    /// finalize_hash binding the nullifier + receipt.
    pub const BRIDGE_FINALIZE: usize = 41;
    /// ReleaseEscrow: actor records release of an escrow to a recipient.
    /// The recipient's balance change depends on escrow_id lookup; this
    /// AIR variant is passthrough with escrow_id binding (executor verifies
    /// the actual transfer).
    pub const RELEASE_ESCROW: usize = 42;
    /// RefundEscrow: actor records refund of an escrow back to creator.
    /// Passthrough with escrow_id binding.
    pub const REFUND_ESCROW: usize = 43;
    /// ReleaseCommittedEscrow: same as RELEASE_ESCROW but for the
    /// committed-value variant.
    pub const RELEASE_COMMITTED_ESCROW: usize = 44;
    /// RefundCommittedEscrow: same as REFUND_ESCROW but committed variant.
    pub const REFUND_COMMITTED_ESCROW: usize = 45;
    /// Burn: explicit, non-conservation balance reduction. Distinct from
    /// `TRANSFER` with `direction == 1` (no destination credit) and from
    /// `NOTE_CREATE` (no commitment hidden in the row). The AIR pins
    /// `was_burn_flag == 1` and binds the target via params[0].
    pub const BURN: usize = 46;
    /// CellDestroy: permanently retire a cell. Lifecycle lives off-trace
    /// but the AIR binds both `target_hash` (params[0]) and
    /// `death_certificate_hash` (params[1]) into effects_hash, distinct
    /// from any SetPermissions alias.
    pub const CELL_DESTROY: usize = 47;
    /// AttenuateCapability: narrow an existing c-list slot's commitment.
    /// Distinct from REVOKE_CAPABILITY: revoke folds a `slot_hash` into
    /// cap_root in a single step; attenuate folds a 2-of-2 leaf
    /// `hash_2_to_1(cap_slot_hash, narrower_commitment)` into cap_root.
    pub const ATTENUATE_CAPABILITY: usize = 48;
    /// CellSeal: transition a cell lifecycle to `Sealed`. State passthrough;
    /// `target_hash` (params[0]) and `reason_hash` (params[1]) bind the
    /// cell and rationale into effects_hash (domain tag 49). A
    /// `SetPermissions` row has only one non-zero param and a different
    /// selector, so the two cannot alias algebraically.
    pub const CELL_SEAL: usize = 49;
    /// CellUnseal: reverse a cell seal (`Sealed` → `Live`). State passthrough;
    /// `target_hash` (params[0]) binds the cell (domain tag 50). One param
    /// vs. CellSeal's two makes the two variants algebraically distinct even
    /// if a prover tries to alias by zeroing params[1].
    pub const CELL_UNSEAL: usize = 50;
    /// ReceiptArchive: summarize the cell's receipt-chain prefix. State
    /// passthrough; `target_hash` (params[0]), `archive_end_height`
    /// (params[1]), and `terminal_receipt_hash` (params[2]) all fold into
    /// effects_hash (domain tag 51). Three params make this algebraically
    /// distinct from any 1- or 2-param passthrough sibling.
    pub const RECEIPT_ARCHIVE: usize = 51;
    /// Refusal: evidence-of-absence. State passthrough; `target_hash`
    /// (params[0]) and `reason_hash` (params[1]) bind the refusing cell and
    /// commitment+reason discriminant into effects_hash (domain tag 52).
    /// Distinct from CellSeal by selector alone; distinct from CellDestroy
    /// by the absence of a `cert_hash` requirement in the AIR constraint.
    pub const REFUSAL: usize = 52;
    /// IncrementNonce: explicit runtime nonce bump. State passthrough except
    /// for the global nonce tick; selector alone binds intent.
    pub const INCREMENT_NONCE: usize = 53;

    // ---- Stage 7-γ.2 Phase 1.5 (planned): bilateral role selectors ----
    //
    // The PI-only Phase 1 binding (`STAGE-7-GAMMA-2-PI-DESIGN.md` §2-§4) is
    // already enforced by the off-AIR verifier loop (see
    // `turn::executor::TurnExecutor::verify_bilateral_bundle`). Phase 1.5
    // lifts the bilateral binding INTO the AIR by adding:
    //
    //   * 3 new selectors for Introduce role routing:
    //       INTRO_AS_INTRODUCER = 46
    //       INTRO_AS_RECIPIENT  = 47
    //       INTRO_AS_TARGET     = 48
    //     (replacing today's single INTRODUCE row that passes through
    //     `intro_hash` without role differentiation — see line 274).
    //
    //   * Per-row Poseidon2 absorb columns for transfer_id / grant_id /
    //     intro_id recomputation. Estimated ~46 new aux columns growing
    //     `EFFECT_VM_WIDTH` from 105 to ~151 (`STAGE-7-GAMMA-2-PI-DESIGN.md`
    //     §6.4).
    //
    //   * Boundary constraint pinning the last row's accumulator state to
    //     PI[OUTGOING_TRANSFER_ROOT_BASE..+4] etc. — the same shape as
    //     today's `CUSTOM_COUNT_ACC → CUSTOM_EFFECT_COUNT` sum-check.
    //
    // Phase 1 (this commit) delivers: PI surface + executor projection +
    // off-AIR verifier algorithm. The AIR widening is deferred until the
    // verifier-side algorithm has soaked in production.
}

/// State column offsets (relative to state start).
pub mod state {
    pub const BALANCE_LO: usize = 0;
    pub const BALANCE_HI: usize = 1;
    pub const NONCE: usize = 2;
    pub const FIELD_BASE: usize = 3; // fields[0..8] at offsets 3..11
    pub const CAP_ROOT: usize = 11;
    pub const STATE_COMMIT: usize = 12;
    pub const RESERVED: usize = 13;
    pub const SIZE: usize = 14;
}

/// Absolute column indices for state_before.
pub const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // selector count after IncrementNonce
/// Absolute column indices for state_after.
pub const STATE_AFTER_BASE: usize = STATE_BEFORE_BASE + state::SIZE + NUM_PARAMS; // 53 + 14 + 8 = 75
/// Effect parameter base column.
pub const PARAM_BASE: usize = STATE_BEFORE_BASE + state::SIZE; // 53 + 14 = 67
/// Number of parameter columns.
pub const NUM_PARAMS: usize = 8;
/// Auxiliary witness base column.
pub const AUX_BASE: usize = STATE_AFTER_BASE + state::SIZE; // 44 + 14 = 58
/// Number of auxiliary columns.
/// Stage 1: 12 (8 effect-aux + 3 state intermediates + 1 custom-count acc).
/// Stage 2: 23 (+ 8 reserved bits + 1 mode flag + 2 ResizeQueue sign/mag).
/// Sovereign-witness teeth: 28 (+ 4 WITNESS_KEY_COMMIT + 1 WITNESS_SEQUENCE).
/// γ.2 federation+owner binding (#131/#132): 36 (+ 4 FEDERATION_ID + 4 OWNER_CELL_ID).
pub const NUM_AUX: usize = 36;

/// Auxiliary column offsets for state commitment tree intermediates.
pub mod aux_off {
    /// Intermediate 1: hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    pub const STATE_INTER1: usize = 8;
    /// Intermediate 2: hash_4_to_1(field[1], field[2], field[3], field[4])
    pub const STATE_INTER2: usize = 9;
    /// Intermediate 3: hash_4_to_1(field[5], field[6], field[7], cap_root)
    pub const STATE_INTER3: usize = 10;
    /// Stage 1: cumulative count of `s_custom == 1` rows up to and including
    /// this row. Boundary-pinned at last row to `PI[CUSTOM_EFFECT_COUNT]`
    /// (sum-check, per `DESIGN-max-custom-effects.md` §6 step 3).
    pub const CUSTOM_COUNT_ACC: usize = 11;
    /// Stage 2: 2^field_idx witness for Seal/Unseal rows. Constrained by the
    /// Lagrange polynomial over {0..7} to lie in {1, 2, 4, 8, 16, 32, 64, 128}
    /// and to equal the value implied by SEAL_FIELD_IDX / UNSEAL_FIELD_IDX.
    /// Used to express `new_reserved == old_reserved ± 2^field_idx` for
    /// Seal/Unseal mask updates.
    pub const SEAL_POW2_IDX: usize = 7;
    /// Stage 2 (sealing honesty): bit-decomposition of `old_reserved`.
    /// `old_reserved == Σ_{i=0..7} bi * 2^i + mode * 256`, with each bi
    /// and mode boolean. Combined with a Lagrange-basis selection on
    /// `field_idx`, this yields an algebraically bound `bit_at_idx` that
    /// the SetField constraint can check against — closing the
    /// AUDIT[stage2-setfield-sealed-witness] hole.
    pub const RESERVED_BIT_0: usize = 12;
    pub const RESERVED_BIT_1: usize = 13;
    pub const RESERVED_BIT_2: usize = 14;
    pub const RESERVED_BIT_3: usize = 15;
    pub const RESERVED_BIT_4: usize = 16;
    pub const RESERVED_BIT_5: usize = 17;
    pub const RESERVED_BIT_6: usize = 18;
    pub const RESERVED_BIT_7: usize = 19;
    pub const RESERVED_MODE: usize = 20;
    /// Stage 2 (ResizeQueue honesty): sign bit for the capacity delta.
    /// 0 = grow (new_capacity > old_capacity), 1 = shrink. Constrained
    /// boolean. Combined with RESIZE_DELTA_MAG, this gives algebraic
    /// `new_capacity - old_capacity == delta_mag * (1 - 2*sign)`.
    pub const RESIZE_DELTA_SIGN: usize = 21;
    /// Stage 2: |new_capacity - old_capacity| magnitude.
    pub const RESIZE_DELTA_MAG: usize = 22;

    // ---- Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    /// 4-felt Poseidon2 hash of the sovereign witness's owning pubkey,
    /// row-0-pinned to PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4].
    /// Zero sentinel on every row for non-sovereign proofs. The boundary
    /// constraint binds row 0; later rows are free (the gate is at row 0
    /// only — the witness identity is a property of the turn, not of
    /// individual effects).
    pub const WITNESS_KEY_COMMIT_0: usize = 23;
    pub const WITNESS_KEY_COMMIT_1: usize = 24;
    pub const WITNESS_KEY_COMMIT_2: usize = 25;
    pub const WITNESS_KEY_COMMIT_3: usize = 26;
    /// Per-cell monotonic sequence counter, row-0-pinned to
    /// PI[SOVEREIGN_WITNESS_SEQUENCE]. Zero sentinel for non-sovereign proofs.
    pub const WITNESS_SEQUENCE: usize = 27;

    // ---- γ.2 follow-up (#131/#132): per-cell federation + owner binding ----
    /// 4-felt Poseidon2 compression of the 32-byte federation id this proof
    /// was minted under. Row-0-pinned to PI[FEDERATION_ID_BASE..+4]. Every
    /// row carries the same value (it is a property of the turn's federation,
    /// not of individual effects); the boundary constraint binds row 0.
    /// A proof minted under federation A cannot satisfy the row-0 binding
    /// when checked against federation B's reconstructed PI.
    pub const FEDERATION_ID_0: usize = 28;
    pub const FEDERATION_ID_1: usize = 29;
    pub const FEDERATION_ID_2: usize = 30;
    pub const FEDERATION_ID_3: usize = 31;
    /// 4-felt Poseidon2 compression of the 32-byte owner cell id whose state
    /// transition this proof attests. Row-0-pinned to PI[OWNER_CELL_ID_BASE..+4].
    /// Binds the proof to a specific owner cell so a proof for owner cell X
    /// cannot be substituted for owner cell Y.
    pub const OWNER_CELL_ID_0: usize = 32;
    pub const OWNER_CELL_ID_1: usize = 33;
    pub const OWNER_CELL_ID_2: usize = 34;
    pub const OWNER_CELL_ID_3: usize = 35;
}

/// Effect parameter meanings per effect type.
///
/// Transfer:
///   param0 = amount
///   param1 = direction (0=incoming, 1=outgoing)
///
/// SetField:
///   param0 = field_index (0..7)
///   param1 = new_value
///
/// GrantCapability:
///   param0 = capability_entry (hash of new capability)
///
/// NoteSpend:
///   param0 = nullifier
///   param1 = value_lo
///   param2 = value_hi
///
/// NoteCreate:
///   param0 = commitment
///   param1 = value_lo
///   param2 = value_hi
///
/// CreateObligation:
///   param0 = stake_amount_lo
///   param1 = stake_amount_hi
///   param2 = obligation_id (hash of terms)
///   param3 = beneficiary_hash
///
/// FulfillObligation:
///   param0 = obligation_id (hash identifying the obligation)
///   param1 = stake_return_lo (amount returned to obligor)
///   param2 = stake_return_hi
///
/// Custom (CellProgram dispatch):
///   param0..param3 = custom_program_vk_hash (4 BabyBear elements identifying the program)
///   param4..param7 = custom_proof_commitment (4 BabyBear elements = hash of external proof)
pub mod param {
    pub const AMOUNT: usize = 0;
    pub const DIRECTION: usize = 1;
    pub const FIELD_INDEX: usize = 0;
    pub const NEW_VALUE: usize = 1;
    pub const CAP_ENTRY: usize = 0;
    pub const NULLIFIER: usize = 0;
    pub const NOTE_VALUE_LO: usize = 1;
    pub const NOTE_VALUE_HI: usize = 2;
    pub const NOTE_COMMITMENT: usize = 0;
    // Obligation params.
    pub const OBLIGATION_STAKE_LO: usize = 0;
    pub const OBLIGATION_STAKE_HI: usize = 1;
    pub const OBLIGATION_ID: usize = 2;
    pub const OBLIGATION_BENEFICIARY: usize = 3;
    pub const FULFILL_OBLIGATION_ID: usize = 0;
    pub const FULFILL_RETURN_LO: usize = 1;
    pub const FULFILL_RETURN_HI: usize = 2;
    // SlashObligation params.
    pub const SLASH_OBLIGATION_ID: usize = 0;
    pub const SLASH_STAKE_LO: usize = 1;
    pub const SLASH_STAKE_HI: usize = 2;
    pub const SLASH_BENEFICIARY: usize = 3;
    // Seal params.
    pub const SEAL_FIELD_IDX: usize = 0;
    // Unseal params.
    pub const UNSEAL_FIELD_IDX: usize = 0;
    pub const UNSEAL_BRAND: usize = 1;
    // MakeSovereign params: no balance params (mode flag only).
    // CreateCellFromFactory params.
    pub const FACTORY_VK_HASH: usize = 0;
    pub const CHILD_VK_DERIVED: usize = 1;
    // Custom cell program dispatch params.
    /// VK hash identifying the custom program (4 elements = 4*30 = 120 bits).
    pub const CUSTOM_VK_HASH_BASE: usize = 0;
    /// Custom proof commitment (hash of the external proof, 4 elements).
    pub const CUSTOM_PROOF_COMMIT_BASE: usize = 4;
    // ExportSturdyRef params.
    /// Cell ID being exported.
    pub const EXPORT_CELL_ID: usize = 0;
    /// Permissions mask for the sturdy ref.
    pub const EXPORT_PERMISSIONS: usize = 1;
    /// Random seed for swiss number derivation.
    pub const EXPORT_RANDOM_SEED: usize = 2;
    /// Export counter (monotonic, pre-increment value).
    pub const EXPORT_COUNTER: usize = 3;
    // EnlivenRef params.
    /// Swiss number to look up.
    pub const ENLIVEN_SWISS: usize = 0;
    /// Presenter ID (who is enlivening).
    pub const ENLIVEN_PRESENTER: usize = 1;
    /// Expected cell_id (from swiss table lookup, verified via aux).
    pub const ENLIVEN_CELL_ID: usize = 2;
    /// Expected permissions (from swiss table lookup).
    pub const ENLIVEN_PERMISSIONS: usize = 3;
    // DropRef params.
    /// Cell ID whose reference is being dropped.
    pub const DROP_CELL_ID: usize = 0;
    /// Federation hash of the holder dropping the ref.
    pub const DROP_HOLDER_FED: usize = 1;
    /// Current refcount (pre-decrement).
    pub const DROP_REFCOUNT: usize = 2;
    // ValidateHandoff params.
    /// Certificate hash.
    pub const HANDOFF_CERT_HASH: usize = 0;
    /// Recipient public key hash.
    pub const HANDOFF_RECIPIENT_PK: usize = 1;
    /// Introducer public key hash.
    pub const HANDOFF_INTRODUCER_PK: usize = 2;
    /// Known-good certificate set root (Merkle root of approved certs).
    pub const HANDOFF_APPROVED_SET_ROOT: usize = 3;
    // AllocateQueue params.
    /// Queue capacity (number of slots).
    pub const QUEUE_CAPACITY: usize = 0;
    /// Owner quota ID (for balance check).
    pub const QUEUE_OWNER_QUOTA: usize = 1;
    /// Cost per slot (used for quota balance check).
    pub const QUEUE_COST_PER_SLOT: usize = 2;
    // EnqueueMessage params.
    /// Message hash being enqueued.
    pub const ENQUEUE_MSG_HASH: usize = 0;
    /// Deposit amount paid by sender.
    pub const ENQUEUE_DEPOSIT: usize = 1;
    /// Sender ID.
    pub const ENQUEUE_SENDER: usize = 2;
    /// Current queue length (pre-enqueue, for capacity check).
    pub const ENQUEUE_QUEUE_LEN: usize = 3;
    /// Queue program VK hash as a BabyBear field element.
    /// ZERO if the queue has no attached program (permissionless enqueue).
    /// Non-zero activates program validation hash constraint in aux[2].
    pub const ENQUEUE_PROGRAM_VK: usize = 4;
    // DequeueMessage params.
    /// Expected message hash at head of queue.
    pub const DEQUEUE_EXPECTED_HASH: usize = 0;
    /// Deposit refund amount returned to dequeuer.
    pub const DEQUEUE_DEPOSIT_REFUND: usize = 1;
    // ResizeQueue params.
    /// New capacity for the queue.
    pub const RESIZE_NEW_CAPACITY: usize = 0;
    /// Queue ID (identifies which queue to resize).
    pub const RESIZE_QUEUE_ID: usize = 1;
    /// Cost per slot (for balance check on growing).
    pub const RESIZE_COST_PER_SLOT: usize = 2;
    /// Old capacity (pre-resize, for delta computation).
    pub const RESIZE_OLD_CAPACITY: usize = 3;
    // AtomicQueueTx params.
    /// Number of operations in the transaction.
    pub const ATOMIC_TX_OP_COUNT: usize = 0;
    /// Hash of all operations (binds to specific ops).
    pub const ATOMIC_TX_HASH: usize = 1;
    /// Combined old roots of all queues touched.
    pub const ATOMIC_TX_COMBINED_OLD_ROOT: usize = 2;
    /// Combined new roots after atomic execution.
    pub const ATOMIC_TX_COMBINED_NEW_ROOT: usize = 3;
    /// Net deposit paid across all sub-operations in the atomic tx.
    /// This is the sum of deposits paid by enqueue ops minus refunds from dequeue ops.
    /// Allows the circuit to prove the correct balance delta for atomic transactions.
    pub const ATOMIC_TX_NET_DEPOSIT: usize = 4;
    // Burn params (near-miss aliasing closure, #100 follow-up).
    /// Hash of the target cell whose balance is reduced.
    pub const BURN_TARGET: usize = 0;
    /// Burn amount (low 30 bits). Constraints subtract from balance_lo.
    pub const BURN_AMOUNT_LO: usize = 1;
    /// Disclosure flag — constrained to 1 on any Burn row so that a
    /// verifier replaying the trace cannot confuse this with a
    /// Transfer-direction-1 row.
    pub const BURN_WAS_BURN_FLAG: usize = 2;
    // CellDestroy params (near-miss aliasing closure).
    /// Hash of the cell being destroyed.
    pub const CELL_DESTROY_TARGET: usize = 0;
    /// `DeathCertificate::certificate_hash()` truncated into a BabyBear.
    pub const CELL_DESTROY_CERT_HASH: usize = 1;
    // AttenuateCapability params (near-miss aliasing closure).
    /// Hash of the c-list slot being narrowed.
    pub const ATTN_CAP_SLOT_HASH: usize = 0;
    /// Commitment to the new (narrower) permissions / facet / expiry.
    pub const ATTN_NARROWER_COMMITMENT: usize = 1;
    // PipelineStep params.
    /// Pipeline identity hash (content-addressed from stage descriptions).
    pub const PIPELINE_ID: usize = 0;
    /// Source queue root before step.
    pub const PIPELINE_SOURCE_OLD_ROOT: usize = 1;
    /// Source queue root after step (message dequeued).
    pub const PIPELINE_SOURCE_NEW_ROOT: usize = 2;
    /// Sink queue root after step (message enqueued).
    pub const PIPELINE_SINK_NEW_ROOT: usize = 3;
    /// Message hash (what was routed).
    pub const PIPELINE_MESSAGE_HASH: usize = 4;

    // CellSeal params (AIR-impl lane #119, selector 49).
    /// Hash of the cell being sealed.
    pub const CELL_SEAL_TARGET: usize = 0;
    /// BLAKE3 of the sealing reason (cleartext off-chain).
    pub const CELL_SEAL_REASON_HASH: usize = 1;

    // CellUnseal params (AIR-impl lane #119, selector 50).
    /// Hash of the cell being unsealed.
    pub const CELL_UNSEAL_TARGET: usize = 0;

    // ReceiptArchive params (AIR-impl lane #119, selector 51).
    /// Hash of the cell being archived.
    pub const RECEIPT_ARCHIVE_TARGET: usize = 0;
    /// `archive_end_height` as BabyBear (low-30-bit truncation of the u64).
    pub const RECEIPT_ARCHIVE_END_HEIGHT: usize = 1;
    /// BLAKE3 of the terminal receipt at `archive_end_height`.
    pub const RECEIPT_ARCHIVE_TERMINAL_HASH: usize = 2;

    // Refusal params (AIR-impl lane #119, selector 52).
    /// Hash of the cell issuing the refusal.
    pub const REFUSAL_TARGET: usize = 0;
    /// Reason-encoded binding: `discriminant ^ trunc(offered_action_commitment)`.
    pub const REFUSAL_REASON_HASH: usize = 1;
}
