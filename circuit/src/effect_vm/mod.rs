//! Effect VM AIR: Multi-row DSL circuit proving arbitrary sequences of effects
//! (turns) in a single STARK proof.
//!
//! Inspired by o1vm (RISC-V execution trace proving), but for pyana Effects instead
//! of CPU instructions. Each trace row represents one effect execution step.
//!
//! # Instruction Set (Effect Types)
//!
//! - NoOp (0): Padding effect; all constraints trivially satisfied.
//! - Transfer (1): Balance transfer with direction (in/out).
//! - SetField (2): Update a custom field slot.
//! - GrantCapability (3): Add capability to c-list (capability_root update).
//! - NoteSpend (4): Spend a note (nullifier reveal, balance credit).
//! - NoteCreate (5): Create a note (commitment creation, balance debit).
//! - CreateObligation (6): Lock stake from balance as a bonded obligation.
//! - FulfillObligation (7): Return locked stake on successful fulfillment.
//! - Custom (8): CellProgram dispatch — state flows unchanged, domain constraints
//!   proven externally. Params carry program VK hash + proof commitment.
//! - SlashObligation (9): Slash an expired obligation.
//! - Seal (10): Lock a field against mutation.
//! - Unseal (11): Unlock a sealed field.
//! - MakeSovereign (12): Transition cell from managed to sovereign.
//! - CreateCellFromFactory (13): Record factory provenance.
//! - ExportSturdyRef (14): Export cell as sturdy ref (CapTP).
//! - EnlivenRef (15): Enliven a sturdy ref (CapTP).
//! - DropRef (16): Drop a remote reference / GC decrement (CapTP).
//! - ValidateHandoff (17): Validate a handoff certificate (CapTP).
//! - AllocateQueue (18): Create a new MerkleQueue (storage Phase 2).
//! - EnqueueMessage (19): Append message to queue (storage Phase 2).
//! - DequeueMessage (20): Advance queue head, reveal message (storage Phase 2).
//! - ResizeQueue (21): Change queue capacity (storage Phase 2).
//! - AtomicQueueTx (22): Prove atomic cross-queue transaction (storage Phase 3).
//! - PipelineStep (23): Prove pipeline step correctly routed a message (storage Phase 3).
//!
//! # Trace Layout (one row per effect)
//!
//! ```text
//! | selector[24] | state_before[14] | effect_params[8] | state_after[14] | aux[11] |
//! ```
//!
//! Total width: 71 columns
//!
//! ## Column Breakdown
//!
//! Selectors (cols 0..9): Exactly one active per row.
//!   - sel_noop, sel_transfer, sel_setfield, sel_grantcap, sel_notespend, sel_notecreate,
//!     sel_create_obligation, sel_fulfill_obligation, sel_custom
//!
//! State Before (cols 9..23):
//!   - balance_lo, balance_hi (u64 as two BabyBear limbs, 30+34 bits)
//!   - nonce
//!   - field_values[0..7] (8 custom fields)
//!   - capability_root
//!   - state_commitment (running Poseidon2 hash of full state)
//!   - reserved
//!
//! Effect Params (cols 23..31):
//!   - param0..param7 (meaning depends on effect type)
//!
//! State After (cols 31..45):
//!   - Same layout as state_before
//!
//! Aux (cols 50..61):
//!   - Auxiliary witness values (intermediate hashes, commitment tree nodes)
//!   - aux[8..10]: state commitment tree intermediates (hash_4_to_1 outputs)
//!
//! # Constraints
//!
//! 1. Selector exclusivity: sum(selectors) == 1, each selector is boolean.
//! 2. Per-effect constraints (gated by selector):
//!    - Transfer: new_balance = old_balance +/- amount
//!    - SetField: one field updated, others unchanged
//!    - GrantCap: capability_root = hash(old_root, new_entry)
//!    - NoteSpend: nullifier valid, balance increases
//!    - NoteCreate: commitment valid, balance decreases
//!    - CreateObligation: balance decreases by stake_amount
//!    - FulfillObligation: balance increases by stake_return
//!    - Custom: state unchanged (domain constraints proven externally)
//! 3. Transition constraints (row-to-row continuity):
//!    - next_row.state_before == this_row.state_after
//!    - next_row.nonce == this_row.nonce + 1 (or same for NoOp padding)
//! 4. Boundary constraints:
//!    - First row: state_before matches old_commitment (public input)
//!    - Last non-padding row: state_after matches new_commitment
//!    - Conservation: net balance delta == public input
//!
//! # Public Inputs
//!
//! Base layout (`pi::BASE_COUNT` felts, Stage 7-γ.2 Phase 1 widening):
//!
//! ```text
//!   [ 0.. 4]  OLD_COMMIT[4]                   cell pre-state commitment (Poseidon2)
//!   [ 4.. 8]  NEW_COMMIT[4]                   cell post-state commitment (Poseidon2)
//!   [ 8..12]  EFFECTS_HASH[4]                 Poseidon2 over per-cell projected effects
//!   [12]      INIT_BAL_LO                     row 0 balance low limb
//!   [13]      INIT_BAL_HI                     row 0 balance high limb
//!   [14]      FINAL_BAL_LO                    last row balance low limb
//!   [15]      FINAL_BAL_HI                    last row balance high limb
//!   [16]      NET_DELTA_MAG                   |Δbalance|
//!   [17]      NET_DELTA_SIGN                  0 = +, 1 = −
//!   [18]      CURRENT_BLOCK_HEIGHT            federation block height
//!   [19]      MAX_CUSTOM_EFFECTS              per-cell manifest cap
//!   [20]      CUSTOM_EFFECT_COUNT             Σ sel_custom in trace
//!   [21..25]  APPROVED_HANDOFFS[4]            CapTP federation-scoped Merkle root
//!   [25..29]  TURN_HASH[4]                    Poseidon2 of Turn::hash() (7-γ.0a)
//!   [29..33]  EFFECTS_HASH_GLOBAL[4]          Poseidon2 over canonical-DFS call_forest effects (7-γ.0a)
//!   [33]      ACTOR_NONCE                     outer Turn::nonce (7-γ.0a; closes W-1 nonce gap)
//!   [34..38]  PREVIOUS_RECEIPT_HASH[4]        Poseidon2 of previous_receipt_hash (7-γ.0a)
//!   [38..45]  bilateral counts (7-γ.2): outbound_transfer, inbound_transfer,
//!                                       outbound_grant, inbound_grant,
//!                                       intro_introducer, intro_recipient, intro_target
//!   [45..49]  OUTGOING_TRANSFER_ROOT[4]       (7-γ.2)
//!   [49..53]  INCOMING_TRANSFER_ROOT[4]       (7-γ.2)
//!   [53..57]  OUTGOING_GRANT_ROOT[4]          (7-γ.2)
//!   [57..61]  INCOMING_GRANT_ROOT[4]          (7-γ.2)
//!   [61..65]  INTRO_AS_INTRODUCER_ROOT[4]     (7-γ.2)
//!   [65..69]  INTRO_AS_RECIPIENT_ROOT[4]      (7-γ.2)
//!   [69..73]  INTRO_AS_TARGET_ROOT[4]         (7-γ.2)
//!   [73]      IS_AGENT_CELL                   (7-γ.2; 1 iff this proof is the actor's)
//!   ... (sovereign-witness teeth, value-limbs, slot-caveat / cross-effect /
//!        witness-index manifests; see `pi::BASE_COUNT` for the precise tail
//!        layout) ...
//!   [168]     UNILATERAL_ATTESTATIONS_COUNT   (7-γ.2 unilateral; number of self-attestations this turn)
//!   [169..173] UNILATERAL_ATTESTATIONS_ROOT[4] (7-γ.2 unilateral; Merkle/Poseidon2 accumulator over (kind, data) tuples)
//!   [173..]   CUSTOM_PROOFS                   per-custom-effect (vk_hash[4], proof_commit[4])
//! ```
//!
//! The four 7-γ.0a additions (TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//! PREVIOUS_RECEIPT_HASH) are *shared across all per-cell proofs of one
//! turn*. The verifier's cross-proof PI matching loop
//! (`verify_proof_carrying_turn_bundle` in `turn::executor`) enforces
//! equality across the N proofs; per-proof binding to the canonical
//! Turn::hash / call_forest is the executor's responsibility for now and
//! becomes algebraic at Stage 7-γ.1.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1, hash_many};
use crate::stark::{BoundaryConstraint, StarkAir};

// ============================================================================
// Column layout constants
// ============================================================================

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
pub const EFFECT_VM_WIDTH: usize = 110;

/// Number of effect types (selectors).
pub const NUM_EFFECTS: usize = 46;

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
pub const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // 22
/// Absolute column indices for state_after.
pub const STATE_AFTER_BASE: usize = STATE_BEFORE_BASE + state::SIZE + NUM_PARAMS; // 22 + 14 + 8 = 44
/// Effect parameter base column.
pub const PARAM_BASE: usize = STATE_BEFORE_BASE + state::SIZE; // 22 + 14 = 36
/// Number of parameter columns.
pub const NUM_PARAMS: usize = 8;
/// Auxiliary witness base column.
pub const AUX_BASE: usize = STATE_AFTER_BASE + state::SIZE; // 44 + 14 = 58
/// Number of auxiliary columns.
/// Stage 1: 12 (8 effect-aux + 3 state intermediates + 1 custom-count acc).
/// Stage 2: 23 (+ 8 reserved bits + 1 mode flag + 2 ResizeQueue sign/mag).
/// Sovereign-witness teeth: 28 (+ 4 WITNESS_KEY_COMMIT + 1 WITNESS_SEQUENCE).
pub const NUM_AUX: usize = 28;

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
}

/// Public input layout.
///
/// Stage 1 widening (`EFFECT-VM-SHAPE-A.md`): commitments grow from 1 felt
/// (~31-bit binding) to 4 felts (~124-bit binding), via the typed
/// `Commitment4<T>` framework (`pyana_commit::typed`). Position 0 of each
/// 4-tuple corresponds to the in-trace `state::STATE_COMMIT` continuity
/// column; positions 1..3 are bound to the canonical cell state by the
/// executor's PI matching loop (it recomputes all 4 deterministically from
/// the stored canonical bytes via `pyana_commit::typed::canonical_32_to_felts_4`).
///
/// AUDIT[stage1-trace-widen]: For Stage 1, the trace `state::STATE_COMMIT`
/// remains a 1-column continuity hash (Constraint Group 4 unchanged). The
/// extra 3 PI elements get their security from the executor PI matching
/// loop. Stage 2 (`EFFECT-VM-SHAPE-A.md` Phase 1) widens the trace column.
pub mod pi {
    // ---- Commitments (Stage 1 widened to 4 felts each, ~124-bit) ----
    /// Old state commitment, 4-felt Poseidon2 form.
    pub const OLD_COMMIT_BASE: usize = 0;
    pub const OLD_COMMIT_LEN: usize = 4;
    /// New state commitment, 4-felt Poseidon2 form.
    pub const NEW_COMMIT_BASE: usize = 4;
    pub const NEW_COMMIT_LEN: usize = 4;
    /// Effects-tree hash, 4-felt Poseidon2 form. Promotes the prior 2-felt
    /// (lo+synthetic-hi) form to 4 felts; synthetic-hi is dropped.
    pub const EFFECTS_HASH_BASE: usize = 8;
    pub const EFFECTS_HASH_LEN: usize = 4;

    // ---- Backwards-compatible aliases (position 0 only) ----
    /// Legacy alias: position 0 of OLD_COMMIT_BASE (single-felt continuity binding).
    pub const OLD_COMMIT: usize = OLD_COMMIT_BASE;
    /// Legacy alias: position 0 of NEW_COMMIT_BASE.
    pub const NEW_COMMIT: usize = NEW_COMMIT_BASE;
    /// Legacy alias: position 0 of EFFECTS_HASH_BASE.
    pub const EFFECTS_HASH_LO: usize = EFFECTS_HASH_BASE;
    /// Legacy alias: position 1 of EFFECTS_HASH_BASE. AUDIT[stage1-effects-hash]:
    /// callers reading this should switch to absorbing all 4 elements via the
    /// EFFECTS_HASH_LEN range; the prior synthetic-hi binding is replaced by
    /// independent Poseidon2 squeezes.
    pub const EFFECTS_HASH_HI: usize = EFFECTS_HASH_BASE + 1;

    // ---- Per-cell balance limbs (P0-1 net_delta binding) ----
    /// Initial balance low limb (30 bits) — pinned to row 0 state_before.
    pub const INIT_BAL_LO: usize = 12;
    /// Initial balance high limb — pinned to row 0 state_before.
    pub const INIT_BAL_HI: usize = 13;
    /// Final balance low limb — pinned to last row state_after.
    pub const FINAL_BAL_LO: usize = 14;
    /// Final balance high limb — pinned to last row state_after.
    pub const FINAL_BAL_HI: usize = 15;

    // ---- Net balance delta (P0-1 binding) ----
    pub const NET_DELTA_MAG: usize = 16;
    pub const NET_DELTA_SIGN: usize = 17;

    // ---- Stage 1 additions (per EFFECT-VM-SHAPE-A.md G, E, F) ----
    /// Federation block height supplied by the verifier. Used by effects
    /// that take a timeout (escrow refund, bridge cancel) — those land in
    /// later stages; the PI slot exists now so they have it.
    pub const CURRENT_BLOCK_HEIGHT: usize = 18;
    /// Per-cell maximum custom effects (from cell program manifest).
    /// Verifier supplies from `cell.program.max_custom_effects`.
    pub const MAX_CUSTOM_EFFECTS: usize = 19;
    /// Number of custom effects in this turn (0 if none). The AIR enforces
    /// `Σ s_custom == PI[CUSTOM_EFFECT_COUNT]` (sum-check, soundness
    /// prerequisite per `DESIGN-max-custom-effects.md` §7 threat 3).
    pub const CUSTOM_EFFECT_COUNT: usize = 20;

    // ---- CapTP federation-state root (Stage 1 prep; populated in Stage 7) ----
    /// Federation-scoped approved-handoffs Merkle root, 4-felt Poseidon2 form.
    /// Initial value: empty-tree sentinel (Commitment4::empty()).
    pub const APPROVED_HANDOFFS_BASE: usize = 21;
    pub const APPROVED_HANDOFFS_LEN: usize = 4;

    // ---- Stage 7-γ.0a additions: turn-level identity bindings ----
    //
    // These four fields are *shared across all per-cell proofs of one turn*.
    // Each per-cell proof carries the same values; the verifier's
    // cross-proof PI matching loop (`verify_proof_carrying_turn_bundle`)
    // enforces equality across the N proofs. Per-proof binding to the
    // canonical Turn::hash and call_forest projection is executor-trusted
    // for γ.0; γ.1 elevates the effects_hash_global -> Σ effects_local
    // merge to an aggregation micro-AIR.
    //
    /// Poseidon2 of the canonical `Turn::hash()` (v3, post-Stage-7-α.1).
    /// All per-cell proofs of one turn share this value; the verifier
    /// rejects bundles whose per-cell proofs disagree.
    pub const TURN_HASH_BASE: usize = 25;
    pub const TURN_HASH_LEN: usize = 4;
    /// Poseidon2 over the canonical-DFS-order traversal of the whole
    /// `call_forest`'s effects (not per-cell). Closes P2 (projection
    /// totality) at γ.1; for γ.0 it's a shared PI the executor verifies
    /// against the turn's recomputed value.
    pub const EFFECTS_HASH_GLOBAL_BASE: usize = 29;
    pub const EFFECTS_HASH_GLOBAL_LEN: usize = 4;
    /// Outer `Turn::nonce`, promoted to PI. Closes the differential-test
    /// gap from task #49 (AIR previously did not witness the agent's
    /// outer nonce bump). The verifier's PI-match loop rejects bundles
    /// whose per-cell proofs disagree on the actor nonce, and the
    /// executor checks PI[ACTOR_NONCE] == turn.nonce.
    pub const ACTOR_NONCE: usize = 33;
    /// Poseidon2 of `previous_receipt_hash` (32 bytes -> 4 felts) when
    /// present, or the zero sentinel when absent. Binds each per-cell
    /// proof to a specific receipt-chain position.
    pub const PREVIOUS_RECEIPT_HASH_BASE: usize = 34;
    pub const PREVIOUS_RECEIPT_HASH_LEN: usize = 4;

    // ---- Stage 7-γ.2 Phase 1: bilateral cross-cell algebraic binding ----
    //
    // These slots project each per-cell proof's bilateral-effect participation
    // (Transfer, GrantCapability, Introduce) into shared PI fields that the
    // off-AIR verifier reconstructs from the turn's call_forest + ACTOR_NONCE.
    // The verifier rejects any per-cell PI that doesn't match the
    // schedule-derived expectation, closing the executor-trust gap for cross-
    // cell agreement (EXECUTOR-HONESTY-AUDIT.md T1, T3, T15 multi-cell tails).
    //
    // All bilateral fields default to the zero sentinel
    // (`Commitment4::empty()` for the 4-felt roots; 0 for the scalar counts)
    // when this cell has no bilateral effects of that kind. The verifier
    // short-circuits matching against sentinel entries.
    //
    // Sub-stage status:
    //   γ.2.0  PI surface + sentinels                  ✅ (this commit)
    //   γ.2.1  AIR aux columns + boundary binding      pending (TODO[γ.2.1])
    //   γ.2.2  Verifier cross-cell match loop          ✅ (this commit)
    //   γ.2.3  IS_AGENT_CELL gate                      ✅ (this commit)

    /// Count of Transfer rows in this cell's projection where direction == 1
    /// (outflow). The verifier's expected-schedule reconstruction must agree.
    pub const OUTBOUND_TRANSFER_COUNT: usize = 38;
    /// Count of Transfer rows where direction == 0 (inflow).
    pub const INBOUND_TRANSFER_COUNT: usize = 39;
    /// Count of GrantCapability rows where this cell is the grantor.
    pub const OUTBOUND_GRANT_COUNT: usize = 40;
    /// Count of GrantCapability rows where this cell is the grantee.
    pub const INBOUND_GRANT_COUNT: usize = 41;
    /// Count of Introduce rows where this cell is the introducer.
    pub const INTRO_AS_INTRODUCER_COUNT: usize = 42;
    /// Count of Introduce rows where this cell is the recipient.
    pub const INTRO_AS_RECIPIENT_COUNT: usize = 43;
    /// Count of Introduce rows where this cell is the target.
    pub const INTRO_AS_TARGET_COUNT: usize = 44;

    /// 4-felt Poseidon2 accumulator over all outbound bilateral transfer_ids
    /// in this turn, absorbed in trace-row-index order. Each step folds
    /// `(transfer_id_4, peer_cell_id_4)` into the running state. Domain
    /// separator distinguishes from inbound + grant + introduce roots.
    /// Sentinel: `[BabyBear::ZERO; 4]` when count == 0.
    pub const OUTGOING_TRANSFER_ROOT_BASE: usize = 45;
    pub const OUTGOING_TRANSFER_ROOT_LEN: usize = 4;
    /// Mirror of OUTGOING_TRANSFER_ROOT for the inbound side.
    pub const INCOMING_TRANSFER_ROOT_BASE: usize = 49;
    pub const INCOMING_TRANSFER_ROOT_LEN: usize = 4;

    /// 4-felt accumulator over outbound grant_ids (this cell as grantor).
    pub const OUTGOING_GRANT_ROOT_BASE: usize = 53;
    pub const OUTGOING_GRANT_ROOT_LEN: usize = 4;
    /// 4-felt accumulator over inbound grant_ids (this cell as grantee).
    pub const INCOMING_GRANT_ROOT_BASE: usize = 57;
    pub const INCOMING_GRANT_ROOT_LEN: usize = 4;

    /// 4-felt accumulator over intro_ids where this cell is the introducer.
    pub const INTRO_AS_INTRODUCER_ROOT_BASE: usize = 61;
    pub const INTRO_AS_INTRODUCER_ROOT_LEN: usize = 4;
    /// 4-felt accumulator over intro_ids where this cell is the recipient.
    pub const INTRO_AS_RECIPIENT_ROOT_BASE: usize = 65;
    pub const INTRO_AS_RECIPIENT_ROOT_LEN: usize = 4;
    /// 4-felt accumulator over intro_ids where this cell is the target.
    pub const INTRO_AS_TARGET_ROOT_BASE: usize = 69;
    pub const INTRO_AS_TARGET_ROOT_LEN: usize = 4;

    /// Single-felt boolean: 1 iff this per-cell proof was the actor's
    /// (signer's) cell for the turn. Exactly one proof in a bundle must
    /// carry IS_AGENT_CELL == 1; all others must be 0. The agent-cell
    /// proof's row-0 NONCE column is pinned to PI[ACTOR_NONCE] (γ.0a
    /// constraint), and non-agent cells are exempt from that pin. The
    /// verifier enforces the exactly-one-agent rule across the bundle.
    pub const IS_AGENT_CELL: usize = 73;

    // ---- Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    //
    // Phase 1: bind the witness's signing identity + replay counter to the
    // AIR at row 0 via gated boundary constraints. When IS_SOVEREIGN_CELL
    // == 1, the prover and verifier must agree on
    //   PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4] == Poseidon2(owner_pubkey)
    //   PI[SOVEREIGN_WITNESS_SEQUENCE]            == witness.sequence
    // When IS_SOVEREIGN_CELL == 0 (hosted-cell proofs), the prover writes
    // the zero sentinel into both PI slots and the in-trace aux columns,
    // and the boundary holds trivially (the columns and PI both zero).
    // The verifier sets the PI sentinel when not sovereign.
    //
    // Phase 2 (Option B per design §3.2): an additional proof-commitment
    // pair binds an inner transition_proof. The off-AIR verifier reads
    // SOVEREIGN_TRANSITION_PROOF_VK_HASH + SOVEREIGN_TRANSITION_PROOF_COMMITMENT
    // and recursively verifies the inner STARK via Lane Golden-Edge's
    // generalized recursive verifier.
    /// 4-felt Poseidon2 hash of the sovereign cell's owning pubkey (the
    /// key that signed the witness). Zero sentinel when IS_SOVEREIGN_CELL == 0.
    pub const SOVEREIGN_WITNESS_KEY_COMMIT_BASE: usize = 74;
    pub const SOVEREIGN_WITNESS_KEY_COMMIT_LEN: usize = 4;
    /// Per-cell monotonic sequence counter from the witness. Zero sentinel
    /// when IS_SOVEREIGN_CELL == 0. Replay protection via the verifier's
    /// chain-walk (each turn's PI[SOVEREIGN_WITNESS_SEQUENCE] must equal
    /// the federation's last-known + 1, enforced at executor injection
    /// time).
    pub const SOVEREIGN_WITNESS_SEQUENCE: usize = 78;
    /// Single-felt boolean: 1 iff this per-cell proof attests to a
    /// sovereign-witnessed effect. 0 for hosted cells. Drives the gating
    /// for SOVEREIGN_WITNESS_KEY_COMMIT / SOVEREIGN_WITNESS_SEQUENCE.
    pub const IS_SOVEREIGN_CELL: usize = 79;
    /// 4-felt VK hash of the AIR under which the inner transition_proof
    /// was produced (typically the Effect VM AIR — see design §3.2). Zero
    /// sentinel when no transition_proof was supplied or IS_SOVEREIGN_CELL
    /// == 0. Bound only when HAS_TRANSITION_PROOF == 1.
    pub const SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE: usize = 80;
    pub const SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN: usize = 4;
    /// 4-felt Poseidon2 hash of the inner transition_proof bytes (after
    /// canonical serialization). Zero sentinel when no proof was supplied.
    pub const SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE: usize = 84;
    pub const SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN: usize = 4;
    /// Single-felt boolean: 1 iff a STARK transition_proof was supplied
    /// alongside the witness AND IS_SOVEREIGN_CELL == 1.
    pub const HAS_TRANSITION_PROOF: usize = 88;

    // ---- 30-bit value-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5) ----
    //
    // Three effects (BridgeMint, BridgeLock, CreateEscrow) project a u64
    // `value` into a single BabyBear via `value & ((1 << 30) - 1)`. Above
    // 2^30, the high 34 bits are unrecoverable from the proof: a malicious
    // prover could re-mint / re-lock / escrow with arbitrary high-bit
    // collisions.
    //
    // Fix: bind the full u64 into the PI via four 16-bit limbs (positive,
    // each < 2^16, summing as v_l + v_ml*2^16 + v_mh*2^32 + v_h*2^48 == value).
    // The executor populates the limbs from the runtime u64; the verifier
    // PI-matching loop catches any disagreement. The existing per-row
    // value_lo param is preserved for backwards-compatibility and is
    // tied to the lo+mid_lo+mid_hi via boundary at row 0 (the
    // 30-bit-limb form is now demonstrably one *shadow* of the full
    // four-limb form).
    //
    // Each effect gets a 4-element PI slot; populated only when that
    // effect appears in the trace. When absent, the slot is the zero
    // sentinel.
    /// 4-limb (16-bit each) decomposition of `BridgeMint.value`. Limbs are
    /// little-endian: limbs[0] is the low 16 bits, limbs[3] is the high 16.
    pub const BRIDGE_MINT_VALUE_LIMBS_BASE: usize = 89;
    pub const BRIDGE_MINT_VALUE_LIMBS_LEN: usize = 4;
    /// 4-limb decomposition of `BridgeLock.value`.
    pub const BRIDGE_LOCK_VALUE_LIMBS_BASE: usize = 93;
    pub const BRIDGE_LOCK_VALUE_LIMBS_LEN: usize = 4;
    /// 4-limb decomposition of `CreateEscrow.amount`.
    pub const CREATE_ESCROW_AMOUNT_LIMBS_BASE: usize = 97;
    pub const CREATE_ESCROW_AMOUNT_LIMBS_LEN: usize = 4;

    // ---- Custom proof commitments ----
    /// For each custom effect i (0..custom_count):
    ///   PI[CUSTOM_PROOFS_BASE + i*8 + 0..4] = custom_program_vk_hash (4 elements)
    ///   PI[CUSTOM_PROOFS_BASE + i*8 + 4..8] = custom_proof_commitment (4 elements)
    ///
    /// Note: CUSTOM_PROOFS_BASE is computed from BASE_COUNT so that adding
    /// new γ.2 PI fields shifts the custom-proof entries automatically. All
    /// callers compute from `BASE_COUNT` rather than the literal constant.
    pub const CUSTOM_PROOFS_BASE: usize = BASE_COUNT;
    /// Base public inputs (without custom proof data).
    ///
    /// Layout (post sovereign-witness teeth + unilateral binding; BASE_COUNT 173):
    ///   0..21   pre-γ.0a slots (commitments, balances, block height, etc.)
    ///   21..25  APPROVED_HANDOFFS[4]
    ///   25..29  TURN_HASH[4]                       (γ.0a)
    ///   29..33  EFFECTS_HASH_GLOBAL[4]             (γ.0a)
    ///   33      ACTOR_NONCE                        (γ.0a)
    ///   34..38  PREVIOUS_RECEIPT_HASH[4]           (γ.0a)
    ///   38..45  bilateral counts (transfer/grant/intro per direction/role) (γ.2)
    ///   45..49  OUTGOING_TRANSFER_ROOT[4]          (γ.2)
    ///   49..53  INCOMING_TRANSFER_ROOT[4]          (γ.2)
    ///   53..57  OUTGOING_GRANT_ROOT[4]             (γ.2)
    ///   57..61  INCOMING_GRANT_ROOT[4]             (γ.2)
    ///   61..65  INTRO_AS_INTRODUCER_ROOT[4]        (γ.2)
    ///   65..69  INTRO_AS_RECIPIENT_ROOT[4]         (γ.2)
    ///   69..73  INTRO_AS_TARGET_ROOT[4]            (γ.2)
    ///   73      IS_AGENT_CELL                      (γ.2)
    ///   74..78  SOVEREIGN_WITNESS_KEY_COMMIT[4]    (sovereign teeth)
    ///   78      SOVEREIGN_WITNESS_SEQUENCE         (sovereign teeth)
    ///   79      IS_SOVEREIGN_CELL                  (sovereign teeth)
    ///   80..84  SOVEREIGN_TRANSITION_PROOF_VK_HASH[4]    (sovereign teeth Phase 2)
    ///   84..88  SOVEREIGN_TRANSITION_PROOF_COMMITMENT[4] (sovereign teeth Phase 2)
    ///   88      HAS_TRANSITION_PROOF               (sovereign teeth Phase 2)
    ///   89..93  BRIDGE_MINT_VALUE_LIMBS[4]          (30-bit-trunc fix)
    ///   93..97  BRIDGE_LOCK_VALUE_LIMBS[4]          (30-bit-trunc fix)
    ///   97..101 CREATE_ESCROW_AMOUNT_LIMBS[4]       (30-bit-trunc fix)
    ///   101     SLOT_CAVEAT_COUNT                   (Cav-Codex Block 3)
    ///   102..126 SLOT_CAVEAT_MANIFEST[24]            (Cav-Codex Block 3)
    ///   126     CROSS_EFFECT_DEPS_COUNT             (Proof-to-Action §3.3)
    ///   127..151 CROSS_EFFECT_DEPS_MANIFEST[24]     (Proof-to-Action §3.3)
    ///   151     WITNESS_INDEX_MAP_COUNT             (Proof-to-Action §3.2)
    ///   152..168 WITNESS_INDEX_MAP[16]              (Proof-to-Action §3.2)
    ///   168     UNILATERAL_ATTESTATIONS_COUNT       (γ.2 unilateral)
    ///   169..173 UNILATERAL_ATTESTATIONS_ROOT[4]    (γ.2 unilateral)
    ///
    /// ---- Slot-caveat manifest (Cav-Codex Block 3) ----
    ///
    /// Per `SLOT-CAVEATS-DESIGN.md` §4: AIR enforcement of slot caveats
    /// is opt-in per variant. Block 3 lands the *manifest surface*: a
    /// single PI section that carries the cell-program's declared
    /// `StateConstraint` set so that
    ///   (a) the verifier can re-evaluate the same caveats against the
    ///       state_before/state_after columns this AIR already binds,
    ///       and
    ///   (b) a future row-bound AIR gadget can pin specific
    ///       (state_before.fields[i], state_after.fields[i]) columns to
    ///       the manifest entries.
    ///
    /// The manifest is fixed-size — up to `MAX_SLOT_CAVEATS` entries of
    /// `SLOT_CAVEAT_ENTRY_SIZE` felts each, prefixed by a single-felt
    /// count. Unused entries are zero-padded. Each entry is a 6-felt
    /// tuple: `[type_tag, slot_index, p0, p1, p2, p3]`. Variants with
    /// fewer than 4 numeric parameters leave trailing felts at zero;
    /// variants whose parameters don't fit (e.g. `AllowedTransitions`
    /// with a variable-length transition list) carry a 32B→4-felt
    /// commitment in `(p0, p1, p2, p3)`.
    ///
    /// Type tags (kept in sync with `pyana_cell::program::StateConstraint`):
    pub const SLOT_CAVEAT_COUNT: usize = 101;
    /// Maximum number of slot caveats bindable through the PI manifest.
    /// Cells declaring more than this fall back to executor-only
    /// enforcement (the AIR cannot bind them).
    pub const MAX_SLOT_CAVEATS: usize = 4;
    /// Felts per slot-caveat entry: [type_tag, slot_index, p0, p1, p2, p3].
    pub const SLOT_CAVEAT_ENTRY_SIZE: usize = 6;
    /// Base of the manifest array. Entry `i` lives at
    /// `SLOT_CAVEAT_MANIFEST_BASE + i * SLOT_CAVEAT_ENTRY_SIZE`.
    pub const SLOT_CAVEAT_MANIFEST_BASE: usize = 102;

    // Type tags for the manifest (numerically distinct from any
    // existing PI sentinel and from zero — zero means "no caveat").
    pub const SLOT_CAVEAT_TAG_FIELD_EQUALS: u32 = 1;
    pub const SLOT_CAVEAT_TAG_FIELD_GTE: u32 = 2;
    pub const SLOT_CAVEAT_TAG_FIELD_LTE: u32 = 3;
    pub const SLOT_CAVEAT_TAG_WRITE_ONCE: u32 = 4;
    pub const SLOT_CAVEAT_TAG_IMMUTABLE: u32 = 5;
    pub const SLOT_CAVEAT_TAG_MONOTONIC: u32 = 6;
    pub const SLOT_CAVEAT_TAG_STRICT_MONOTONIC: u32 = 7;
    pub const SLOT_CAVEAT_TAG_FIELD_DELTA: u32 = 8;
    pub const SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE: u32 = 9;
    pub const SLOT_CAVEAT_TAG_TEMPORAL_GATE: u32 = 10;
    pub const SLOT_CAVEAT_TAG_SENDER_AUTHORIZED: u32 = 11;
    pub const SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS: u32 = 12;

    // ---- Cross-effect within-turn chain pinning (Proof-to-Action Binding §3.3) ----
    //
    // Per `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.3: when two effects in
    // the same turn chain (e.g., `SpendNote` produces a nullifier that
    // a later `BridgeMint` consumes in the same turn), the AIR needs to
    // witness that the producer's output equals the consumer's input.
    // Without this, a malicious executor could route the consumer to a
    // different value than what the producer actually produced.
    //
    // The manifest is fixed-size — up to `MAX_CROSS_EFFECT_DEPS` entries
    // of `CROSS_EFFECT_DEP_ENTRY_SIZE` felts each, prefixed by a
    // single-felt count. Each entry is a 6-felt tuple:
    //   [producer_index, consumer_index, field_tag, vc0, vc1, vc2]
    // where:
    //   - producer_index, consumer_index: u32-as-BabyBear indices into
    //     the canonical DFS-traversal order of the call_forest;
    //   - field_tag: discriminator for the named field (nullifier=1,
    //     note_commitment=2, escrow_id=3, destination=4, note_tree_root=5);
    //   - vc0..vc2: 3 of the 8 limbs of the chained 32-byte value
    //     commitment, providing ~93-bit binding strength (one
    //     commitment cell can pack 32 bytes only with 8 limbs; the
    //     fixed manifest entry size of 6 felts holds the first 3 limbs;
    //     callers that need stronger binding should additionally
    //     submit an `EffectBindingProof` schema entry which carries the
    //     full 8 limbs).
    //
    // The verifier-side off-AIR check (`TurnExecutor::verify_effect_binding_proofs`)
    // enforces the full 32-byte algebraic match; the AIR slot here is the
    // shared-PI surface that future row-bound enforcement (Stage 7-γ.3)
    // will tie to specific trace rows of the producer/consumer effects.
    pub const CROSS_EFFECT_DEPS_COUNT: usize =
        SLOT_CAVEAT_MANIFEST_BASE + MAX_SLOT_CAVEATS * SLOT_CAVEAT_ENTRY_SIZE; // 126
    pub const MAX_CROSS_EFFECT_DEPS: usize = 4;
    pub const CROSS_EFFECT_DEP_ENTRY_SIZE: usize = 6;
    pub const CROSS_EFFECT_DEPS_BASE: usize = CROSS_EFFECT_DEPS_COUNT + 1; // 127

    /// Field-name tags for cross-effect dependencies. Kept in sync with
    /// `pyana_turn::binding_proof::EffectDependency::field_name` string
    /// match in `TurnExecutor::extract_named_field_32b`.
    pub const CROSS_EFFECT_FIELD_TAG_NULLIFIER: u32 = 1;
    pub const CROSS_EFFECT_FIELD_TAG_NOTE_COMMITMENT: u32 = 2;
    pub const CROSS_EFFECT_FIELD_TAG_ESCROW_ID: u32 = 3;
    pub const CROSS_EFFECT_FIELD_TAG_DESTINATION: u32 = 4;
    pub const CROSS_EFFECT_FIELD_TAG_NOTE_TREE_ROOT: u32 = 5;

    // ---- Witness-blob → Effect indexing (Proof-to-Action Binding §3.2) ----
    //
    // Per `PROOF-TO-ACTION-BINDING-SWEEP.md` §3.2: the runtime `Action`
    // carries `witness_blobs: Vec<WitnessBlob>` and witness-attached
    // predicates reference blobs by `proof_witness_index`. The Effect VM
    // currently does not bind which witness blob feeds which effect: a
    // malicious executor could shuffle blobs so that an effect needing
    // witness K reads bytes meant for effect L.
    //
    // Fix: a per-effect `witness_blob_index` manifest. Each entry is a
    // 2-felt tuple:
    //   [effect_index, witness_index]
    // both as u32-as-BabyBear. Unused entries are zero-padded; the
    // count prefix tells the verifier how many entries are live.
    //
    // The off-AIR verifier checks well-formedness (bounds, no-dupes); a
    // future per-effect AIR slot binds the witness blob's BLAKE3 hash to
    // the effect's row-0 columns for full algebraic enforcement.
    pub const WITNESS_INDEX_MAP_COUNT: usize =
        CROSS_EFFECT_DEPS_BASE + MAX_CROSS_EFFECT_DEPS * CROSS_EFFECT_DEP_ENTRY_SIZE; // 127 + 24 = 151
    pub const MAX_WITNESS_INDEX_ENTRIES: usize = 8;
    pub const WITNESS_INDEX_ENTRY_SIZE: usize = 2;
    pub const WITNESS_INDEX_MAP_BASE: usize = WITNESS_INDEX_MAP_COUNT + 1; // 152

    // ---- Stage 7-γ.2 unilateral binding (1-arity sibling of bilateral) ----
    //
    // Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.5: γ.2 binds pairs (Transfer,
    // Grant) and triples (Introduce) but has no 1-arity sibling. *Unilateral*
    // attestations are the dual — a single cell self-attests to a property
    // over its own transitions (state, nonce bump, sovereign-witness signing)
    // *without a counterparty*. They compose with `peer_exchange`'s
    // federation-bypass primitive: a peer state transition can carry one
    // unilateral attestation, and the receiver verifies it against the
    // sender's cell-id-derived canonical encoding.
    //
    // PI shape (append-only after `WITNESS_INDEX_MAP`):
    //   - `UNILATERAL_ATTESTATIONS_COUNT` (1 felt): number of unilateral
    //     attestations this turn produced for this cell.
    //   - `UNILATERAL_ATTESTATIONS_ROOT_BASE` (4 felts): Merkle/Poseidon2
    //     accumulator over the `(attestation_kind, attestation_data)` tuples,
    //     order-preserving DFS. The future AIR boundary constraint pins the
    //     in-trace `unilateral_root` aux column to this PI slot — same shape
    //     as the bilateral roots (γ.2.1 work). Today the off-AIR verifier
    //     recomputes the expected accumulator from the bundle's declared
    //     attestation list and rejects any mismatch.
    //
    // Sentinel: `[BabyBear::ZERO; 4]` when count == 0. Distinct salt per
    // attestation kind ensures `SelfStateTransition` cannot be confused with
    // `SelfNonceBump` even at colliding data.
    pub const UNILATERAL_ATTESTATIONS_COUNT: usize =
        WITNESS_INDEX_MAP_BASE + MAX_WITNESS_INDEX_ENTRIES * WITNESS_INDEX_ENTRY_SIZE; // 168
    pub const UNILATERAL_ATTESTATIONS_ROOT_BASE: usize = UNILATERAL_ATTESTATIONS_COUNT + 1; // 169
    pub const UNILATERAL_ATTESTATIONS_ROOT_LEN: usize = 4;

    /// Maximum unilateral attestations the off-AIR verifier walks per turn.
    /// The accumulator size is independent of this cap (4-felt root); the
    /// cap is a guardrail on the schedule reconstruction.
    pub const MAX_UNILATERAL_ATTESTATIONS: usize = 8;

    // Type tags for `UnilateralAttestationKind` — kept in sync with
    // `pyana_turn::bilateral_schedule::UnilateralAttestationKind`. Zero is
    // the "no attestation" sentinel (count == 0 → all data zero).
    pub const UNILATERAL_ATTESTATION_KIND_SELF_STATE_TRANSITION: u32 = 1;
    pub const UNILATERAL_ATTESTATION_KIND_SELF_NONCE_BUMP: u32 = 2;
    pub const UNILATERAL_ATTESTATION_KIND_SOVEREIGN_WITNESS: u32 = 3;
    /// `Custom { kind_tag }` flattens to the high half of u32 space: bit 31
    /// would put us out of canonical BabyBear, so kind_tag is masked to 30
    /// bits and OR'd with this discriminant.
    pub const UNILATERAL_ATTESTATION_KIND_CUSTOM_BASE: u32 = 0x4000_0000;

    pub const BASE_COUNT: usize =
        UNILATERAL_ATTESTATIONS_ROOT_BASE + UNILATERAL_ATTESTATIONS_ROOT_LEN; // 173
    /// Elements per custom effect entry in PI (4 vk_hash + 4 proof_commit).
    pub const CUSTOM_ENTRY_SIZE: usize = 8;

    // ---- Hard cap on declared max_custom_effects ----
    /// Hard ceiling: a cell declaring more than this is refused at registration
    /// time. Per `DESIGN-max-custom-effects.md` §5, bounds worst-case verifier
    /// child-proof work to ~3.2s/turn at 50ms/proof.
    pub const MAX_CUSTOM_EFFECTS_HARD_CAP: u8 = 64;
    /// Soft cap: the recommended workspace ceiling. Cells declaring up to this
    /// are uncontroversial; cells declaring 17..64 should justify the choice.
    pub const MAX_CUSTOM_EFFECTS_SOFT_CAP: u8 = 16;
    /// Default value for cells that don't declare a per-cell max. Matches the
    /// pre-Stage-1 workspace constant.
    pub const MAX_CUSTOM_EFFECTS_DEFAULT: u8 = 4;

    // AUDIT[stage1-pi-only-bound]: PI[OLD_COMMIT_BASE+1..+4],
    // PI[NEW_COMMIT_BASE+1..+4], PI[EFFECTS_HASH_BASE+1..+4], and the entire
    // PI[APPROVED_HANDOFFS_BASE..+4] are bound only by the executor's PI
    // matching loop (deterministic recomputation from cell/federation
    // state), not by per-row AIR constraints. Stage 2 may add aux columns
    // to anchor positions 1..3 of state-commit forms inside the trace.
}

// ============================================================================
// Effect enum for witness generation
// ============================================================================

/// An effect to be proven in the VM.
#[derive(Clone, Debug)]
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
    /// Grant a capability (add entry to c-list Merkle root).
    GrantCapability { cap_entry: BabyBear },
    /// Revoke a capability (mix the revoked slot's hash into the c-list Merkle root).
    /// Like `GrantCapability`, the AIR constraint enforces
    /// `new_cap_root == hash_2_to_1(old_cap_root, slot_hash)` so a malicious
    /// prover cannot make up an arbitrary new root.
    RevokeCapability { slot_hash: BabyBear },
    /// EmitEvent: stateless side-effect. The `event_hash` parameter contributes
    /// to `effects_hash` (binding the prover to which event was emitted), but
    /// the AIR constraint enforces full state passthrough — no balance,
    /// field, or cap_root change. Nonce increments by 1 like any non-NoOp effect.
    EmitEvent { event_hash: BabyBear },
    /// SetPermissions: update a cell's permission table. Permissions live
    /// outside the VM's tracked state, so the AIR enforces full state
    /// passthrough (balance / fields / cap_root unchanged) and the
    /// `permissions_hash` parameter binds the new permissions into
    /// effects_hash so the prover commits to the specific update.
    SetPermissions { permissions_hash: BabyBear },
    /// SetVerificationKey: update a cell's verification key (Option<VK>).
    /// Same shape as SetPermissions: VK lives off-trace, the AIR enforces
    /// state passthrough and `vk_hash` binds the new VK into effects_hash.
    /// `vk_hash == 0` represents "set to None" (revoke the VK).
    SetVerificationKey { vk_hash: BabyBear },
    /// CreateSealPair: register a new sealer/unsealer brand pair. Same
    /// passthrough shape; `pair_hash` is BLAKE3(sealer_holder ‖ unsealer_holder).
    CreateSealPair { pair_hash: BabyBear },
    /// RefreshDelegation: bump the delegation epoch. No params (the cell's
    /// epoch lives off-trace); selector alone records the intent. State
    /// passthrough.
    RefreshDelegation,
    /// RevokeDelegation: invalidate a child cell's delegation. State
    /// passthrough; `child_hash` binds the target cell into effects_hash.
    RevokeDelegation { child_hash: BabyBear },
    /// CreateCell: actor records the creation of a new cell. Passthrough.
    /// `create_hash` = BLAKE3(pk ‖ token_id ‖ balance) truncated to BabyBear.
    CreateCell { create_hash: BabyBear },
    /// SpawnWithDelegation: actor records spawning a child cell.
    /// `spawn_hash` = BLAKE3(child_pk ‖ child_token_id ‖ max_staleness).
    SpawnWithDelegation { spawn_hash: BabyBear },
    /// BridgeCancel: actor records the cancellation of a pending bridge.
    /// `nullifier_hash` binds the cancelled bridge into effects_hash.
    BridgeCancel { nullifier_hash: BabyBear },
    /// ExerciseViaCapability: actor records exercise of a c-list cap on a
    /// target cell. From the actor's perspective the actor's own state
    /// doesn't change; `exercise_hash` = BLAKE3(cap_slot ‖ inner_effects_hash).
    ExerciseViaCapability { exercise_hash: BabyBear },
    /// Introduce: 3-party introduction. Passthrough from the introducer's
    /// POV; `intro_hash` = BLAKE3(introducer ‖ recipient ‖ target ‖ perm).
    Introduce { intro_hash: BabyBear },
    /// PipelinedSend: dispatch a future action against an EventualRef.
    /// Passthrough; `send_hash` = BLAKE3(target.source_turn ‖ target.output_slot ‖ action.hash()).
    PipelinedSend { send_hash: BabyBear },
    /// CreateEscrow: actor's balance debits by `amount_lo`. Mirrors NoteCreate.
    /// `escrow_hash` = BLAKE3(recipient ‖ condition) binds the escrow target.
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `amount_full` carries
    /// the full u64 amount; `amount_lo` retains its 30-bit-truncated form for
    /// backwards-compatible AIR constraint use (balance arithmetic uses
    /// `amount_lo` because the per-row balance limbs are 30+34-bit BabyBear).
    /// The trace generator pins `amount_full`'s 4×16-bit limb decomposition
    /// into `PI[CREATE_ESCROW_AMOUNT_LIMBS_BASE..+4]`; the verifier rejects
    /// any disagreement.
    CreateEscrow {
        amount_lo: BabyBear,
        escrow_hash: BabyBear,
        /// Full u64 amount (30-bit-trunc fix). Zero when this effect is
        /// absent from the trace. Multiple emissions sum (wrap-add).
        amount_full: u64,
    },
    /// BridgeLock: actor's balance debits by `value_lo`. Mirrors NoteCreate.
    /// `lock_hash` = BLAKE3(nullifier ‖ destination ‖ asset_type) binds the lock.
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `value_full` carries
    /// the full u64 (see [`Effect::CreateEscrow`] above for rationale).
    BridgeLock {
        value_lo: BabyBear,
        lock_hash: BabyBear,
        /// Full u64 value (30-bit-trunc fix).
        value_full: u64,
    },
    /// CreateCommittedEscrow: passthrough; the locked amount is hidden in a
    /// Pedersen commitment that's verified outside this AIR.
    /// `commit_hash` = BLAKE3(creator_commit ‖ value_commit ‖ recipient_commit ‖ condition_commit).
    CreateCommittedEscrow { commit_hash: BabyBear },
    /// BridgeMint: actor mints `value_lo` from a portable proof. Balance
    /// credit (mirrors NoteSpend). `mint_hash` binds (nullifier, root,
    /// dest_federation, asset_type).
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `value_full` carries
    /// the full u64 (see [`Effect::CreateEscrow`] above for rationale).
    BridgeMint {
        value_lo: BabyBear,
        mint_hash: BabyBear,
        /// Full u64 value (30-bit-trunc fix).
        value_full: u64,
    },
    /// BridgeFinalize: actor finalizes a pending bridge. Passthrough.
    /// `finalize_hash` = BLAKE3(nullifier ‖ receipt_bytes).
    BridgeFinalize { finalize_hash: BabyBear },
    /// ReleaseEscrow: passthrough; amount resolution requires escrow_id
    /// lookup in the ledger (out of AIR scope). `escrow_id_hash` binds
    /// which escrow was released.
    ReleaseEscrow { escrow_id_hash: BabyBear },
    /// RefundEscrow: passthrough; same shape as ReleaseEscrow.
    RefundEscrow { escrow_id_hash: BabyBear },
    /// ReleaseCommittedEscrow: passthrough; same shape, but
    /// `commit_hash` also binds the claim_auth + recipient.
    ReleaseCommittedEscrow { commit_hash: BabyBear },
    /// RefundCommittedEscrow: passthrough; same shape, binds claim_auth +
    /// creator.
    RefundCommittedEscrow { commit_hash: BabyBear },
    /// Spend a note (reveal nullifier, credit balance).
    NoteSpend { nullifier: BabyBear, value: u64 },
    /// Create a note (create commitment, debit balance).
    NoteCreate { commitment: BabyBear, value: u64 },
    /// Create a bonded obligation (locks stake from balance).
    /// Balance decreases by stake_amount. The obligation_id binds the terms.
    CreateObligation {
        /// Amount to lock.
        stake_amount: u64,
        /// Hash identifying the obligation terms (beneficiary, condition, deadline).
        obligation_id: BabyBear,
        /// Hash of the beneficiary cell.
        beneficiary_hash: BabyBear,
    },
    /// Fulfill an obligation (returns stake to obligor's balance).
    /// Balance increases by the returned stake amount.
    FulfillObligation {
        /// Hash identifying the obligation being fulfilled.
        obligation_id: BabyBear,
        /// Amount returned to obligor on fulfillment.
        stake_return: u64,
    },
    /// Custom cell program dispatch.
    ///
    /// State flows through normally (continuity enforced by the Effect VM).
    /// Domain-specific constraints are proven in a separate proof identified by
    /// `custom_proof_commitment`. The verifier checks that the external proof is
    /// valid and that its hash matches this commitment.
    Custom {
        /// VK hash identifying the custom program (4 BabyBear elements packed into a hash).
        program_vk_hash: [BabyBear; 4],
        /// Hash of the external custom program proof (4 BabyBear elements).
        proof_commitment: [BabyBear; 4],
    },
    /// Slash an expired obligation: transfer locked stake to beneficiary.
    /// Balance of beneficiary increases by stake_amount.
    SlashObligation {
        /// Hash identifying the obligation to slash.
        obligation_id: BabyBear,
        /// Amount slashed to beneficiary.
        stake_amount: u64,
        /// Hash of the beneficiary (for cap_root update).
        beneficiary_hash: BabyBear,
    },
    /// Seal: lock a field against mutation.
    /// Sets sealed_field_mask |= (1 << field_idx) in the reserved state slot.
    Seal {
        /// Index of field to seal (0..7).
        field_idx: u32,
    },
    /// Unseal: unlock a sealed field (requires brand matching via aux).
    /// Clears sealed_field_mask &= ~(1 << field_idx).
    Unseal {
        /// Index of field to unseal.
        field_idx: u32,
        /// Brand hash proving authority to unseal.
        brand: BabyBear,
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
    /// ExportSturdyRef: export a cell as a sturdy reference.
    /// Proves: swiss_number = Hash(cell_id || random_seed || export_counter).
    /// State transition: export_counter increments (tracked in field[7] by convention).
    ExportSturdyRef {
        /// Cell ID being exported.
        cell_id: BabyBear,
        /// Permissions mask.
        permissions: BabyBear,
        /// Random seed for swiss derivation.
        random_seed: BabyBear,
        /// Export counter (pre-increment value, stored in field[7]).
        export_counter: u32,
    },
    /// EnlivenRef: enliven a sturdy ref (validate swiss exists in table).
    /// Proves: swiss_number is a known swiss entry (via committed hash check).
    /// State transition: use_count increments (tracked in field[6] by convention).
    EnlivenRef {
        /// Swiss number to validate.
        swiss_number: BabyBear,
        /// Presenter ID.
        presenter_id: BabyBear,
        /// Expected cell_id from the swiss table entry.
        expected_cell_id: BabyBear,
        /// Expected permissions from the swiss table entry.
        expected_permissions: BabyBear,
    },
    /// DropRef: drop a remote reference (GC decrement).
    /// Proves: refcount > 0.
    /// State transition: refcount decrements (tracked in field[5] by convention).
    DropRef {
        /// Cell ID being released.
        cell_id: BabyBear,
        /// Federation hash of the holder.
        holder_federation: BabyBear,
        /// Current refcount (must be > 0).
        current_refcount: u32,
    },
    /// ValidateHandoff: validate a handoff certificate.
    /// Proves: certificate_hash is in the approved set (Merkle membership).
    /// Instead of in-circuit Ed25519, we prove set membership of the cert hash.
    /// State transition: routing entry created (cap_root updated).
    ValidateHandoff {
        /// Hash of the handoff certificate.
        certificate_hash: BabyBear,
        /// Recipient public key hash.
        recipient_pk: BabyBear,
        /// Introducer public key hash.
        introducer_pk: BabyBear,
        /// Merkle root of approved certificates set.
        approved_set_root: BabyBear,
    },
    /// AllocateQueue: create a new MerkleQueue (storage Phase 2).
    /// Proves: quota has sufficient balance for capacity * cost_per_slot.
    /// State transition: field[8] = queue_root set to empty_queue_hash,
    ///   field[9] = queue_capacity set. Balance debited by allocation cost.
    /// (field indices are logical; mapped to fields[0..7] + cap_root slot.)
    /// For the circuit, we use: cap_root stores empty_queue_hash (queue_root),
    /// and the capacity is stored in the reserved field's lower bits.
    /// Simplified: field[4] = queue_root (Poseidon2 empty hash), balance debited.
    AllocateQueue {
        /// Number of slots in the new queue.
        capacity: u32,
        /// Owner quota ID (for provenance).
        owner_quota_id: BabyBear,
        /// Cost per slot in computrons.
        cost_per_slot: u32,
    },
    /// EnqueueMessage: append a message hash to a queue.
    /// Proves: deposit >= min_deposit, queue is not full (queue_len < capacity).
    /// State transition: queue_root changes via hash chain (old_root -> new_root).
    /// If the queue has an attached program, the program validation hash is bound
    /// to the proof via aux[2].
    EnqueueMessage {
        /// Hash of the message being enqueued.
        message_hash: BabyBear,
        /// Deposit amount paid by sender.
        deposit_amount: u32,
        /// Sender ID.
        sender_id: BabyBear,
        /// Current queue length (pre-enqueue, must be < capacity for not-full check).
        queue_len: u32,
        /// Queue program VK hash as a BabyBear field element.
        /// ZERO if the queue has no attached program (backward compatible).
        /// Non-zero activates the program validation constraint.
        program_vk: BabyBear,
    },
    /// DequeueMessage: advance queue head, reveal expected message.
    /// Proves: message_hash matches head of queue (hash equality via aux).
    /// State transition: queue_root advances (head removed via hash chain).
    DequeueMessage {
        /// Expected message hash at head of queue.
        expected_message_hash: BabyBear,
        /// Deposit refund returned on dequeue.
        deposit_refund: u32,
    },
    /// ResizeQueue: change queue capacity.
    /// Proves: if growing, quota has balance for delta * cost_per_slot.
    /// State transition: capacity field updated, balance debited if growing.
    ResizeQueue {
        /// New capacity.
        new_capacity: u32,
        /// Queue ID.
        queue_id: BabyBear,
        /// Cost per slot (for balance check on grow).
        cost_per_slot: u32,
        /// Old capacity (for delta computation).
        old_capacity: u32,
    },
    /// AtomicQueueTx: prove an atomic cross-queue transaction.
    /// Proves: combined old roots -> combined new roots transition is valid,
    /// bound to a specific set of operations via tx_hash.
    /// State transition: field[4] transitions from combined_old_root to combined_new_root
    /// (proves ALL queues transitioned atomically; if ANY op fails, proof is invalid).
    /// Balance transition: balance changes by net_deposit (sum of deposits paid minus refunds).
    AtomicQueueTx {
        /// Number of operations in the transaction.
        op_count: u32,
        /// Hash of all operations (binds to specific ops).
        tx_hash: BabyBear,
        /// Combined old roots of all queues touched.
        combined_old_root: BabyBear,
        /// Combined new roots after atomic execution.
        combined_new_root: BabyBear,
        /// Net deposit paid across all sub-operations (deposits - refunds).
        /// Positive means balance decreases (net payment out).
        net_deposit: u32,
    },
    /// PipelineStep: prove a pipeline step correctly routed a message.
    /// Proves: message M was dequeued from source S and enqueued to sink K,
    /// per pipeline P. The proof covers a single routing step.
    /// State transition: field[4] (source root) transitions from source_old_root
    /// to source_new_root; aux[0] stores sink_new_root for external verification.
    PipelineStep {
        /// Pipeline identity hash (content-addressed from stage descriptions).
        pipeline_id: BabyBear,
        /// Source queue root before step.
        source_old_root: BabyBear,
        /// Source queue root after step (message dequeued).
        source_new_root: BabyBear,
        /// Sink queue root after step (message enqueued).
        sink_new_root: BabyBear,
        /// Message hash (what was routed).
        message_hash: BabyBear,
    },
}

/// Cell state that flows between rows.
#[derive(Clone, Debug)]
pub struct CellState {
    /// Balance as u64 (split into lo/hi for BabyBear encoding).
    pub balance: u64,
    /// Monotonic nonce.
    pub nonce: u32,
    /// 8 custom field values.
    pub fields: [BabyBear; 8],
    /// Capability list Merkle root.
    pub capability_root: BabyBear,
    /// Running state commitment.
    pub state_commitment: BabyBear,
    /// Sealed field mask: bit i set means field i is sealed against mutation.
    pub sealed_field_mask: u32,
    /// Mode flag: 0 = managed, 1 = sovereign.
    pub mode_flag: u32,
}

impl CellState {
    /// Create a new cell state with default values.
    pub fn new(balance: u64, nonce: u32) -> Self {
        let fields = [BabyBear::ZERO; 8];
        let capability_root = BabyBear::ZERO;
        // Initial state commitment is hash of all state elements.
        let state_commitment = Self::compute_commitment(balance, nonce, &fields, capability_root);
        Self {
            balance,
            nonce,
            fields,
            capability_root,
            state_commitment,
            sealed_field_mask: 0,
            mode_flag: 0,
        }
    }

    /// Compute the state commitment from all state components using a
    /// constrainable tree of hash_4_to_1 calls.
    ///
    /// Tree structure:
    ///   inter1 = hash_4_to_1(balance_lo, balance_hi, nonce, field[0])
    ///   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
    ///   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
    ///   commitment = hash_4_to_1(inter1, inter2, inter3, ZERO)
    ///
    /// The fourth input to the root hash is ZERO (reserved for future use).
    /// This structure is directly constrainable because each hash_4_to_1 can be
    /// verified by the evaluator at each trace row.
    pub fn compute_commitment(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> BabyBear {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO])
    }

    /// Stage 1: compute the 4-felt state commitment for the public input layout.
    ///
    /// Position 0 matches [`compute_commitment`] exactly (the in-trace
    /// continuity column). Positions 1..3 are 3 additional independent
    /// Poseidon2 compressions of the same intermediates with different
    /// "salt" felts. The result is bound at row-0 / last-row boundaries
    /// (position 0 in-trace; positions 1..3 via PI matching against the
    /// executor's independently-computed canonical form).
    ///
    /// AUDIT[stage1-pi-only-bound]: positions 1..3 are constrained only by
    /// the executor's PI-matching loop (see `turn/src/executor.rs::verify_proof_carrying_turn`)
    /// — they bind the proof to the verifier's view of cell state but not
    /// to the trace. Stage 2 may add aux columns to extend the in-trace
    /// continuity binding to all 4 felts.
    pub fn compute_commitment_4(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> [BabyBear; 4] {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        [
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ONE]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::new(2)]),
            hash_4_to_1(&[inter1, inter2, inter3, BabyBear::new(3)]),
        ]
    }

    /// Compute the three intermediate hashes for the state commitment tree.
    /// Returns (inter1, inter2, inter3) which are needed as witness values.
    pub fn compute_commitment_intermediates(
        balance: u64,
        nonce: u32,
        fields: &[BabyBear; 8],
        capability_root: BabyBear,
    ) -> (BabyBear, BabyBear, BabyBear) {
        let (lo, hi) = split_u64(balance);
        let inter1 = hash_4_to_1(&[lo, hi, BabyBear::new(nonce), fields[0]]);
        let inter2 = hash_4_to_1(&[fields[1], fields[2], fields[3], fields[4]]);
        let inter3 = hash_4_to_1(&[fields[5], fields[6], fields[7], capability_root]);
        (inter1, inter2, inter3)
    }

    /// Recompute and update the state commitment.
    pub fn refresh_commitment(&mut self) {
        self.state_commitment =
            Self::compute_commitment(self.balance, self.nonce, &self.fields, self.capability_root);
    }

    /// Encode state into trace columns (14 elements).
    fn to_trace_cols(&self) -> Vec<BabyBear> {
        let (lo, hi) = split_u64(self.balance);
        let mut cols = Vec::with_capacity(state::SIZE);
        cols.push(lo); // balance_lo
        cols.push(hi); // balance_hi
        cols.push(BabyBear::new(self.nonce)); // nonce
        cols.extend_from_slice(&self.fields); // field_values[0..8]
        cols.push(self.capability_root); // cap_root
        cols.push(self.state_commitment); // state_commit
        cols.push(BabyBear::new(
            self.sealed_field_mask | (self.mode_flag << 8),
        )); // reserved: sealed_mask | mode_flag
        assert_eq!(cols.len(), state::SIZE);
        cols
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Split a u64 into two BabyBear elements: (lo = lower 30 bits, hi = upper 34 bits).
/// Both values fit in BabyBear (< 2^31).
pub fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32; // upper 34 bits (fits in u32 since val < 2^64)
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
#[allow(dead_code)]
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// Stage 2 (sealing honesty): bit-decompose `reserved = sealed_mask | (mode << 8)`
/// into 8 boolean mask bits + 1 boolean mode bit, and write them into the
/// row's reserved-bit aux slots. The AIR's per-row unconditional decomposition
/// constraint verifies the witness against `state_before.RESERVED`.
pub(super) fn fill_reserved_bits(row: &mut [BabyBear], sealed_mask: u32, mode_flag: u32) {
    row[AUX_BASE + aux_off::RESERVED_BIT_0] = BabyBear::new((sealed_mask >> 0) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_1] = BabyBear::new((sealed_mask >> 1) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_2] = BabyBear::new((sealed_mask >> 2) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_3] = BabyBear::new((sealed_mask >> 3) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_4] = BabyBear::new((sealed_mask >> 4) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_5] = BabyBear::new((sealed_mask >> 5) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_6] = BabyBear::new((sealed_mask >> 6) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_7] = BabyBear::new((sealed_mask >> 7) & 1);
    row[AUX_BASE + aux_off::RESERVED_MODE] = BabyBear::new(mode_flag & 1);
}

/// Compute the effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrantCapability { cap_entry } => {
                hasher_inputs.push(BabyBear::new(3));
                hasher_inputs.push(*cap_entry);
            }
            Effect::RevokeCapability { slot_hash } => {
                hasher_inputs.push(BabyBear::new(24));
                hasher_inputs.push(*slot_hash);
            }
            Effect::EmitEvent { event_hash } => {
                hasher_inputs.push(BabyBear::new(25));
                hasher_inputs.push(*event_hash);
            }
            Effect::SetPermissions { permissions_hash } => {
                hasher_inputs.push(BabyBear::new(26));
                hasher_inputs.push(*permissions_hash);
            }
            Effect::SetVerificationKey { vk_hash } => {
                hasher_inputs.push(BabyBear::new(27));
                hasher_inputs.push(*vk_hash);
            }
            Effect::CreateSealPair { pair_hash } => {
                hasher_inputs.push(BabyBear::new(28));
                hasher_inputs.push(*pair_hash);
            }
            Effect::RefreshDelegation => {
                hasher_inputs.push(BabyBear::new(29));
            }
            Effect::RevokeDelegation { child_hash } => {
                hasher_inputs.push(BabyBear::new(30));
                hasher_inputs.push(*child_hash);
            }
            Effect::CreateCell { create_hash } => {
                hasher_inputs.push(BabyBear::new(31));
                hasher_inputs.push(*create_hash);
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                hasher_inputs.push(BabyBear::new(32));
                hasher_inputs.push(*spawn_hash);
            }
            Effect::BridgeCancel { nullifier_hash } => {
                hasher_inputs.push(BabyBear::new(33));
                hasher_inputs.push(*nullifier_hash);
            }
            Effect::ExerciseViaCapability { exercise_hash } => {
                hasher_inputs.push(BabyBear::new(34));
                hasher_inputs.push(*exercise_hash);
            }
            Effect::Introduce { intro_hash } => {
                hasher_inputs.push(BabyBear::new(35));
                hasher_inputs.push(*intro_hash);
            }
            Effect::PipelinedSend { send_hash } => {
                hasher_inputs.push(BabyBear::new(36));
                hasher_inputs.push(*send_hash);
            }
            Effect::CreateEscrow {
                amount_lo,
                escrow_hash,
                amount_full,
            } => {
                hasher_inputs.push(BabyBear::new(37));
                hasher_inputs.push(*amount_lo);
                hasher_inputs.push(*escrow_hash);
                // 30-bit-trunc fix: absorb the four 16-bit limbs so the
                // effects hash binds to the full u64, not the truncated
                // value_lo.
                let limbs = u64_to_4_limbs_16(*amount_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::BridgeLock {
                value_lo,
                lock_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(38));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*lock_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::CreateCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(39));
                hasher_inputs.push(*commit_hash);
            }
            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(40));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::BridgeFinalize { finalize_hash } => {
                hasher_inputs.push(BabyBear::new(41));
                hasher_inputs.push(*finalize_hash);
            }
            Effect::ReleaseEscrow { escrow_id_hash } => {
                hasher_inputs.push(BabyBear::new(42));
                hasher_inputs.push(*escrow_id_hash);
            }
            Effect::RefundEscrow { escrow_id_hash } => {
                hasher_inputs.push(BabyBear::new(43));
                hasher_inputs.push(*escrow_id_hash);
            }
            Effect::ReleaseCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(44));
                hasher_inputs.push(*commit_hash);
            }
            Effect::RefundCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(45));
                hasher_inputs.push(*commit_hash);
            }
            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::CreateObligation {
                stake_amount,
                obligation_id,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(6));
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*obligation_id);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::FulfillObligation {
                obligation_id,
                stake_return,
            } => {
                hasher_inputs.push(BabyBear::new(7));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_return);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(8));
                hasher_inputs.extend_from_slice(program_vk_hash);
                hasher_inputs.extend_from_slice(proof_commitment);
            }
            Effect::SlashObligation {
                obligation_id,
                stake_amount,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(9));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::Seal { field_idx } => {
                hasher_inputs.push(BabyBear::new(10));
                hasher_inputs.push(BabyBear::new(*field_idx));
            }
            Effect::Unseal { field_idx, brand } => {
                hasher_inputs.push(BabyBear::new(11));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*brand);
            }
            Effect::MakeSovereign => {
                hasher_inputs.push(BabyBear::new(12));
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                hasher_inputs.push(BabyBear::new(13));
                hasher_inputs.push(*factory_vk);
                hasher_inputs.push(*child_vk_derived);
            }
            Effect::ExportSturdyRef {
                cell_id,
                permissions,
                random_seed,
                export_counter,
            } => {
                hasher_inputs.push(BabyBear::new(14));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*permissions);
                hasher_inputs.push(*random_seed);
                hasher_inputs.push(BabyBear::new(*export_counter));
            }
            Effect::EnlivenRef {
                swiss_number,
                presenter_id,
                expected_cell_id,
                expected_permissions,
            } => {
                hasher_inputs.push(BabyBear::new(15));
                hasher_inputs.push(*swiss_number);
                hasher_inputs.push(*presenter_id);
                hasher_inputs.push(*expected_cell_id);
                hasher_inputs.push(*expected_permissions);
            }
            Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount,
            } => {
                hasher_inputs.push(BabyBear::new(16));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*holder_federation);
                hasher_inputs.push(BabyBear::new(*current_refcount));
            }
            Effect::ValidateHandoff {
                certificate_hash,
                recipient_pk,
                introducer_pk,
                approved_set_root,
            } => {
                hasher_inputs.push(BabyBear::new(17));
                hasher_inputs.push(*certificate_hash);
                hasher_inputs.push(*recipient_pk);
                hasher_inputs.push(*introducer_pk);
                hasher_inputs.push(*approved_set_root);
            }
            Effect::AllocateQueue {
                capacity,
                owner_quota_id,
                cost_per_slot,
            } => {
                hasher_inputs.push(BabyBear::new(18));
                hasher_inputs.push(BabyBear::new(*capacity));
                hasher_inputs.push(*owner_quota_id);
                hasher_inputs.push(BabyBear::new(*cost_per_slot));
            }
            Effect::EnqueueMessage {
                message_hash,
                deposit_amount,
                sender_id,
                queue_len,
                program_vk,
            } => {
                hasher_inputs.push(BabyBear::new(19));
                hasher_inputs.push(*message_hash);
                hasher_inputs.push(BabyBear::new(*deposit_amount));
                hasher_inputs.push(*sender_id);
                hasher_inputs.push(BabyBear::new(*queue_len));
                hasher_inputs.push(*program_vk);
            }
            Effect::DequeueMessage {
                expected_message_hash,
                deposit_refund,
            } => {
                hasher_inputs.push(BabyBear::new(20));
                hasher_inputs.push(*expected_message_hash);
                hasher_inputs.push(BabyBear::new(*deposit_refund));
            }
            Effect::ResizeQueue {
                new_capacity,
                queue_id,
                cost_per_slot,
                old_capacity,
            } => {
                hasher_inputs.push(BabyBear::new(21));
                hasher_inputs.push(BabyBear::new(*new_capacity));
                hasher_inputs.push(*queue_id);
                hasher_inputs.push(BabyBear::new(*cost_per_slot));
                hasher_inputs.push(BabyBear::new(*old_capacity));
            }
            Effect::AtomicQueueTx {
                op_count,
                tx_hash,
                combined_old_root,
                combined_new_root,
                net_deposit,
            } => {
                hasher_inputs.push(BabyBear::new(22));
                hasher_inputs.push(BabyBear::new(*op_count));
                hasher_inputs.push(*tx_hash);
                hasher_inputs.push(*combined_old_root);
                hasher_inputs.push(*combined_new_root);
                hasher_inputs.push(BabyBear::new(*net_deposit));
            }
            Effect::PipelineStep {
                pipeline_id,
                source_old_root,
                source_new_root,
                sink_new_root,
                message_hash,
            } => {
                hasher_inputs.push(BabyBear::new(23));
                hasher_inputs.push(*pipeline_id);
                hasher_inputs.push(*source_old_root);
                hasher_inputs.push(*source_new_root);
                hasher_inputs.push(*sink_new_root);
                hasher_inputs.push(*message_hash);
            }
        }
    }
    let h = hash_many(&hasher_inputs);
    // Split into two elements for wider coverage (legacy 2-felt form).
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

/// Stage 1: 4-felt effects hash for the widened PI layout.
///
/// Position 0 matches [`compute_effects_hash`] (the legacy `EFFECTS_HASH_LO`);
/// positions 1..3 are 3 additional independent Poseidon2 compressions.
/// Drops the synthetic `EFFECTS_HASH_HI = hash_2_to_1(h, 0xEFFEC7)` binding
/// in favor of 4 independent squeezes, giving ~124-bit collision resistance.
pub fn compute_effects_hash_4(effects: &[Effect]) -> [BabyBear; 4] {
    let (h, _h_legacy_hi) = compute_effects_hash(effects);
    // Independent squeezes via hash_4_to_1 with distinct salts.
    [
        h,
        hash_4_to_1(&[h, BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(3), BabyBear::ZERO, BabyBear::ZERO]),
    ]
}


// ============================================================================
// AIR Implementation
// ============================================================================

mod air;
pub use air::{EffectVmAir, AIR_DESCRIPTOR};


// ============================================================================
// Witness Generation
// ============================================================================

mod trace;
pub use trace::{
    encode_net_delta, extract_custom_proof_commitments, extract_net_delta,
    extract_slot_caveat_manifest, generate_effect_vm_trace, generate_effect_vm_trace_ext,
    u64_from_4_limbs_16, u64_to_4_limbs_16, EffectVmContext, SlotCaveatEntry,
};


// ============================================================================
// Verifier-side validation
// ============================================================================

mod verify;
pub use verify::{
    verify_balance_limb_pis, verify_balance_limb_ranges, verify_slot_caveat_manifest,
    verify_state_integrity,
};



#[cfg(test)]
mod tests;
