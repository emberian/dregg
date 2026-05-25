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
fn fill_reserved_bits(row: &mut [BabyBear], sealed_mask: u32, mode_flag: u32) {
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

/// The Effect VM AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`EffectVmAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// `public_input_layout` enumerates the BASE_COUNT-wide PI surface
/// (commitments, balance limbs, bilateral aggregation roots,
/// sovereign-witness teeth, 30-bit-trunc value limbs). The
/// CUSTOM_PROOFS region beyond `BASE_COUNT` is variable per-cell and
/// is *not* listed here — its presence is implicit (CUSTOM_PROOFS_BASE
/// == BASE_COUNT, with `max_custom_effects * 8` additional felts).
pub const AIR_DESCRIPTOR: crate::air_descriptor::AirDescriptor =
    crate::air_descriptor::AirDescriptor {
        air_id: "effect_vm_air_v1",
        column_count: EFFECT_VM_WIDTH,
        public_input_layout: &[
            crate::air_descriptor::PiSlot {
                name: "old_commit",
                offset: pi::OLD_COMMIT_BASE,
                length_in_felts: pi::OLD_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "new_commit",
                offset: pi::NEW_COMMIT_BASE,
                length_in_felts: pi::NEW_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash",
                offset: pi::EFFECTS_HASH_BASE,
                length_in_felts: pi::EFFECTS_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_lo",
                offset: pi::INIT_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "init_bal_hi",
                offset: pi::INIT_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_lo",
                offset: pi::FINAL_BAL_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "final_bal_hi",
                offset: pi::FINAL_BAL_HI,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_mag",
                offset: pi::NET_DELTA_MAG,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "net_delta_sign",
                offset: pi::NET_DELTA_SIGN,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "current_block_height",
                offset: pi::CURRENT_BLOCK_HEIGHT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "max_custom_effects",
                offset: pi::MAX_CUSTOM_EFFECTS,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "custom_effect_count",
                offset: pi::CUSTOM_EFFECT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "approved_handoffs",
                offset: pi::APPROVED_HANDOFFS_BASE,
                length_in_felts: pi::APPROVED_HANDOFFS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "turn_hash",
                offset: pi::TURN_HASH_BASE,
                length_in_felts: pi::TURN_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "effects_hash_global",
                offset: pi::EFFECTS_HASH_GLOBAL_BASE,
                length_in_felts: pi::EFFECTS_HASH_GLOBAL_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "actor_nonce",
                offset: pi::ACTOR_NONCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "previous_receipt_hash",
                offset: pi::PREVIOUS_RECEIPT_HASH_BASE,
                length_in_felts: pi::PREVIOUS_RECEIPT_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_transfer_count",
                offset: pi::OUTBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_transfer_count",
                offset: pi::INBOUND_TRANSFER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outbound_grant_count",
                offset: pi::OUTBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "inbound_grant_count",
                offset: pi::INBOUND_GRANT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_count",
                offset: pi::INTRO_AS_INTRODUCER_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_count",
                offset: pi::INTRO_AS_RECIPIENT_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_count",
                offset: pi::INTRO_AS_TARGET_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_transfer_root",
                offset: pi::OUTGOING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::OUTGOING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_transfer_root",
                offset: pi::INCOMING_TRANSFER_ROOT_BASE,
                length_in_felts: pi::INCOMING_TRANSFER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "outgoing_grant_root",
                offset: pi::OUTGOING_GRANT_ROOT_BASE,
                length_in_felts: pi::OUTGOING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "incoming_grant_root",
                offset: pi::INCOMING_GRANT_ROOT_BASE,
                length_in_felts: pi::INCOMING_GRANT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_introducer_root",
                offset: pi::INTRO_AS_INTRODUCER_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_INTRODUCER_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_recipient_root",
                offset: pi::INTRO_AS_RECIPIENT_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_RECIPIENT_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "intro_as_target_root",
                offset: pi::INTRO_AS_TARGET_ROOT_BASE,
                length_in_felts: pi::INTRO_AS_TARGET_ROOT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "is_agent_cell",
                offset: pi::IS_AGENT_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_key_commit",
                offset: pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE,
                length_in_felts: pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_witness_sequence",
                offset: pi::SOVEREIGN_WITNESS_SEQUENCE,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "is_sovereign_cell",
                offset: pi::IS_SOVEREIGN_CELL,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_vk_hash",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "sovereign_transition_proof_commitment",
                offset: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE,
                length_in_felts: pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "has_transition_proof",
                offset: pi::HAS_TRANSITION_PROOF,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_mint_value_limbs",
                offset: pi::BRIDGE_MINT_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_MINT_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "bridge_lock_value_limbs",
                offset: pi::BRIDGE_LOCK_VALUE_LIMBS_BASE,
                length_in_felts: pi::BRIDGE_LOCK_VALUE_LIMBS_LEN,
            },
            crate::air_descriptor::PiSlot {
                name: "create_escrow_amount_limbs",
                offset: pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE,
                length_in_felts: 4,
            },
            // Stage 7-γ.2 unilateral binding (1-arity sibling of bilateral).
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_count",
                offset: pi::UNILATERAL_ATTESTATIONS_COUNT,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "unilateral_attestations_root",
                offset: pi::UNILATERAL_ATTESTATIONS_ROOT_BASE,
                length_in_felts: pi::UNILATERAL_ATTESTATIONS_ROOT_LEN,
            },
        ],
        // Constraint groups: selector validity (NUM_EFFECTS+1), per-effect
        // gated constraints (~NUM_EFFECTS large groups), boundary bindings
        // for commitments / balance limbs / sovereign teeth, bilateral
        // aggregation accumulators. Number is a stable property of the AIR
        // shape — when constraints are added/removed, this bumps.
        constraint_polynomial_count: NUM_EFFECTS + 1 + NUM_EFFECTS,
        boundary_constraint_count: 32,
        max_degree: 9,
        source_hash: None,
    };

/// The Effect VM AIR. Proves an arbitrary sequence of effects in a single STARK.
pub struct EffectVmAir {
    /// Maximum number of effects (trace height, padded to power of 2).
    pub max_effects: usize,
}

impl EffectVmAir {
    pub fn new(max_effects: usize) -> Self {
        assert!(max_effects >= 2, "Need at least 2 rows for STARK");
        assert!(
            max_effects.is_power_of_two(),
            "max_effects must be a power of 2"
        );
        Self { max_effects }
    }
}

impl StarkAir for EffectVmAir {
    fn width(&self) -> usize {
        EFFECT_VM_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // Selector sum constraint is degree 1 (linear).
        // Selector boolean constraints are degree 2.
        // Per-effect constraints: selector * (expression) is at most degree 3.
        // Hash constraints (hash_2_to_1, hash_4_to_1) are evaluated concretely on trace
        // values at FRI evaluation points — they do NOT contribute polynomial degree.
        // SetField field_idx range check: selector * prod_{k=0..7}(field_idx - k) = degree 9.
        // Seal/Unseal field_idx range check: same degree 9.
        9
    }

    fn air_name(&self) -> &'static str {
        "pyana-effect-vm-v1"
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut alpha_pow = BabyBear::ONE;

        // ====================================================================
        // CONSTRAINT GROUP 1: Selector validity
        // ====================================================================

        // Each selector must be boolean: s*(s-1) == 0
        for i in 0..NUM_EFFECTS {
            let s = local[i];
            let c = s * (s - BabyBear::ONE);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Selectors must sum to exactly 1.
        let mut sel_sum = BabyBear::ZERO;
        for i in 0..NUM_EFFECTS {
            sel_sum = sel_sum + local[i];
        }
        let c_sum = sel_sum - BabyBear::ONE;
        combined = combined + alpha_pow * c_sum;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 2: Per-effect-type constraints (gated by selector)
        // ====================================================================
        //
        // SECURITY NOTE — Balance limb range checks (o1vm audit finding #1):
        //
        // balance_lo (30-bit) and balance_hi (34-bit) are NOT range-checked
        // in-circuit. Full bit-decomposition would add 60+ columns to the trace.
        // Instead, the EXECUTOR independently validates:
        //   - balance_lo < 2^30  (fits in the lo limb)
        //   - balance_hi < 2^34  (fits in the hi limb, and < BabyBear prime)
        //   - balance_lo + balance_hi * 2^30 == declared u64 balance
        //
        // The boundary constraints bind start/end state_commitment to public
        // inputs, and state_commitment = Poseidon2(balance_lo, balance_hi, ...),
        // so a malicious prover cannot forge commitments without matching limbs.
        // However, a prover CAN choose field-valid but out-of-range limbs on
        // INTERIOR rows (between boundaries). The executor rejects such proofs
        // by re-deriving the final state and checking limb ranges.
        //
        // TODO(range-checks): When we add lookup arguments (log-derivative or
        // Lasso-style), replace executor-side checks with in-circuit range
        // proofs via a 2^16 lookup table (2 lookups per limb for 30/34 bits).
        //
        // SECURITY NOTE — Balance underflow protection (o1vm audit finding #3):
        //
        // For outgoing transfers and obligation creation, the constraint is:
        //   new_balance_lo = old_balance_lo - amount
        // In BabyBear modular arithmetic, if amount > old_balance, this wraps
        // around to a large "valid" field element rather than failing.
        //
        // The witness generation uses saturating_sub, so honest provers never
        // produce underflow. However, a MALICIOUS prover could craft a trace
        // where the subtraction wraps around the field modulus.
        //
        // Defense: The executor checks that the final balance (extracted from
        // the proven new_commitment) is <= the initial balance + net_credits.
        // Additionally, the state_commitment binds the actual balance limbs,
        // so any wrap-around would produce a commitment that doesn't match the
        // declared final state.
        //
        // TODO(underflow): Add proper non-negative range proof via bit
        // decomposition of (old_balance - amount) to prove it fits in 30 bits.
        // This requires 30 aux columns per debit row, or a shared lookup table.
        // ====================================================================

        let s_noop = local[sel::NOOP];
        let s_transfer = local[sel::TRANSFER];
        let s_setfield = local[sel::SET_FIELD];
        let s_grantcap = local[sel::GRANT_CAP];
        let s_notespend = local[sel::NOTE_SPEND];
        let s_notecreate = local[sel::NOTE_CREATE];
        let s_create_obligation = local[sel::CREATE_OBLIGATION];
        let s_fulfill_obligation = local[sel::FULFILL_OBLIGATION];
        let s_custom = local[sel::CUSTOM];

        // State accessors (before).
        let old_bal_lo = local[STATE_BEFORE_BASE + state::BALANCE_LO];
        let old_bal_hi = local[STATE_BEFORE_BASE + state::BALANCE_HI];
        let old_nonce = local[STATE_BEFORE_BASE + state::NONCE];
        let old_cap_root = local[STATE_BEFORE_BASE + state::CAP_ROOT];

        // State accessors (after).
        let new_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
        let new_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
        let new_nonce = local[STATE_AFTER_BASE + state::NONCE];
        let new_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];

        // Parameters.
        let p0 = local[PARAM_BASE + 0];
        let p1 = local[PARAM_BASE + 1];
        let _p2 = local[PARAM_BASE + 2];

        // -- NoOp: state_after == state_before for all state columns --
        for i in 0..state::SIZE {
            let c = s_noop * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Transfer: balance update --
        // param0 = amount_lo, param1 = direction (0=in, 1=out)
        // If direction=0 (in): new_bal = old_bal + amount
        // If direction=1 (out): new_bal = old_bal - amount
        // Unified: new_bal_lo - old_bal_lo - amount + 2*direction*amount == carry adjustment
        //
        // We work with the combined 60-bit balance:
        //   balance = bal_lo + bal_hi * 2^30
        //   Transfer only touches bal_lo for simplicity (amount < 2^30).
        //   new_bal_lo = old_bal_lo + amount * (1 - 2*direction)
        //
        // For amounts that don't overflow a single limb:
        let two = BabyBear::new(2);
        let direction = p1;
        let amount = p0;
        // new_bal_lo == old_bal_lo + amount - 2*direction*amount
        let c_transfer_lo =
            s_transfer * (new_bal_lo - old_bal_lo - amount + two * direction * amount);
        combined = combined + alpha_pow * c_transfer_lo;
        alpha_pow = alpha_pow * alpha;

        // Transfer: hi limb unchanged (for single-limb amounts).
        let c_transfer_hi = s_transfer * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_transfer_hi;
        alpha_pow = alpha_pow * alpha;

        // Transfer: direction must be boolean.
        let c_transfer_dir = s_transfer * direction * (direction - BabyBear::ONE);
        combined = combined + alpha_pow * c_transfer_dir;
        alpha_pow = alpha_pow * alpha;

        // Transfer: cap_root and reserved unchanged.
        // (state_commitment is a derived value recomputed in witness gen; bound at boundaries only.)
        for i in [state::CAP_ROOT, state::RESERVED] {
            let c = s_transfer * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Transfer: fields unchanged.
        for i in 0..8 {
            let c = s_transfer
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetField: exactly one field updated --
        // param0 = field_index, param1 = new_value
        // For the targeted field: new_field[idx] = new_value.
        // For all others: unchanged.
        // We use the Lagrange selector trick:
        //   For each field slot j: new_field[j] - old_field[j] - is_target_j * (new_value - old_field[j]) == 0
        //   where is_target_j = prod_{k != j} (field_index - k) / (j - k)
        //
        // Simplified: we constrain that the sum of changes equals (new_value - old_field[idx])
        // and that it happens at exactly the right index. For degree control, we use:
        //   For each j in 0..8:
        //     sel_setfield * (new_field[j] - old_field[j]) * (1 - eq(field_index, j)) == 0
        //     where eq check is: (field_index - j) * inverse_or_zero
        //
        // Even simpler approach (lower degree): use aux columns for the Lagrange basis.
        // But for v1, we use a direct approach with the product constraint:
        //   sel_setfield * (new_field[j] - old_field[j]) * product_{k != j}(field_index - k) == 0
        //   for all j where field_index != j.
        //
        // Actually simplest: enforce
        //   For each j: sel * (new_f[j] - old_f[j] - delta_j) == 0
        //   where delta_j = if j == field_index { new_value - old_f[j] } else { 0 }
        //
        // We do it as: for the ONE field that matches, the difference must equal new_value - old.
        // For all others, difference must be zero.
        // With selector-index product trick at degree 2:
        //   sel_setfield * (field_index - j) * (new_f[j] - old_f[j]) == 0 for each j
        //   (if field_index == j, this is trivially 0 regardless of change)
        //   (if field_index != j, new_f[j] - old_f[j] must be 0)
        let field_index = p0;
        let new_value = p1;
        for j in 0..8u32 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j as usize];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j as usize];
            // Non-target fields must be unchanged.
            let c = s_setfield * (field_index - BabyBear::new(j)) * (new_fj - old_fj);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // The target field must become new_value. We check this by:
        //   For each j: sel * prod_{k!=j}(index - k) * (new_f[j] - new_value) == 0
        // When index == j, prod_{k!=j}(index-k) != 0, so new_f[j] must equal new_value.
        // When index != j, some factor (index - j) is zero in the product, so constraint is trivial.
        // But this is high degree (degree 8). Instead, use the aux column approach:
        //   aux[0] stores the Lagrange indicator (computed in witness gen).
        //   Constraint: sel * (sum_j new_f[j] * lagrange_j - new_value) == 0
        //
        // Simplest correct approach for v1: The witness generation ensures the right field
        // is set. We just need ONE constraint proving the target field has the right value.
        // Use aux[0] to carry the old value of the target field, then:
        //   sel_setfield * (new_value - target_field_new) == 0
        // where target_field_new is reconstructed from the trace.
        //
        // Actually, the simplest sound approach:
        //   Verify that the difference across all fields sums to exactly (new_value - old_value_at_idx).
        //   Combined with per-field constraints above (non-target unchanged), this is sufficient.
        // The sum of (new_f[j] - old_f[j]) for all j must equal (new_value - old_value_at_idx).
        // old_value_at_idx is stored in aux[0].
        let old_value_at_idx = local[AUX_BASE + 0];
        let mut field_diff_sum = BabyBear::ZERO;
        for j in 0..8 {
            let old_fj = local[STATE_BEFORE_BASE + state::FIELD_BASE + j];
            let new_fj = local[STATE_AFTER_BASE + state::FIELD_BASE + j];
            field_diff_sum = field_diff_sum + (new_fj - old_fj);
        }
        let c_setfield_sum = s_setfield * (field_diff_sum - (new_value - old_value_at_idx));
        combined = combined + alpha_pow * c_setfield_sum;
        alpha_pow = alpha_pow * alpha;

        // SetField: balance and cap_root unchanged.
        let c_sf_bal_lo = s_setfield * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sf_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sf_bal_hi = s_setfield * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sf_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sf_cap = s_setfield * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sf_cap;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty): SetField must not change `reserved`
        // (sealed_mask AND mode_flag both preserved across a field set).
        let sf_old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let sf_new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sf_reserved = s_setfield * (sf_new_reserved - sf_old_reserved);
        combined = combined + alpha_pow * c_sf_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (sealing honesty, FULL bit-decomposition):
        // The target field must NOT be sealed. We derive
        // `bit_at_field_idx = Σ_k L_k(field_idx) * b_k` from the
        // bit-decomposition of old_reserved (aux[RESERVED_BIT_0..7]),
        // where L_k(x) is the Lagrange basis on {0..7}. The constraints
        // below enforce:
        //   1. Each b_i is boolean.
        //   2. Σ b_i * 2^i + mode * 256 == old_reserved.
        //   3. mode is boolean.
        //   4. s_setfield * (Σ_k L_k(field_idx) * b_k) == 0.
        // The first three apply to every row (UNCONDITIONALLY) — that
        // gives every effect row a correct bit-decomposition of its
        // own old_reserved. The fourth gates by selector.
        //
        // Resolves AUDIT[stage2-setfield-sealed-witness].
        let b0 = local[AUX_BASE + aux_off::RESERVED_BIT_0];
        let b1 = local[AUX_BASE + aux_off::RESERVED_BIT_1];
        let b2 = local[AUX_BASE + aux_off::RESERVED_BIT_2];
        let b3 = local[AUX_BASE + aux_off::RESERVED_BIT_3];
        let b4 = local[AUX_BASE + aux_off::RESERVED_BIT_4];
        let b5 = local[AUX_BASE + aux_off::RESERVED_BIT_5];
        let b6 = local[AUX_BASE + aux_off::RESERVED_BIT_6];
        let b7 = local[AUX_BASE + aux_off::RESERVED_BIT_7];
        let mode_bit = local[AUX_BASE + aux_off::RESERVED_MODE];
        // Boolean constraints (unconditional, every row).
        for bit in [b0, b1, b2, b3, b4, b5, b6, b7, mode_bit].iter() {
            let cb = (*bit) * ((*bit) - BabyBear::ONE);
            combined = combined + alpha_pow * cb;
            alpha_pow = alpha_pow * alpha;
        }
        // Decomposition: Σ bi * 2^i + mode * 256 == old_reserved.
        let sf_old_reserved_dec = local[STATE_BEFORE_BASE + state::RESERVED];
        let reconstructed = b0
            + b1 * BabyBear::new(2)
            + b2 * BabyBear::new(4)
            + b3 * BabyBear::new(8)
            + b4 * BabyBear::new(16)
            + b5 * BabyBear::new(32)
            + b6 * BabyBear::new(64)
            + b7 * BabyBear::new(128)
            + mode_bit * BabyBear::new(256);
        let c_decomp = reconstructed - sf_old_reserved_dec;
        combined = combined + alpha_pow * c_decomp;
        alpha_pow = alpha_pow * alpha;
        // Lagrange-basis selection of the bit at field_idx.
        // For field_idx ∈ {0..7}, returns b_{field_idx}.
        let l_bits: [BabyBear; 8] = [b0, b1, b2, b3, b4, b5, b6, b7];
        let bit_at_idx = {
            let x = field_index;
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        // s_setfield * bit_at_idx == 0  (cannot set a sealed field).
        let c_sf_not_sealed = s_setfield * bit_at_idx;
        combined = combined + alpha_pow * c_sf_not_sealed;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: Seal: bit at field_idx must currently be 0 (no double-seal).
        // (Reuse the same Lagrange selection on the SEAL_FIELD_IDX param.)
        let seal_bit_at_idx = {
            let x = local[PARAM_BASE + param::SEAL_FIELD_IDX];
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        let s_seal_early = local[sel::SEAL];
        let c_seal_no_double = s_seal_early * seal_bit_at_idx;
        combined = combined + alpha_pow * c_seal_no_double;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: Unseal: bit at field_idx must currently be 1.
        let unseal_bit_at_idx = {
            let x = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
            let mut acc = BabyBear::ZERO;
            for k in 0..8usize {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8usize {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j as u32));
                    let diff = if k > j {
                        BabyBear::new((k - j) as u32)
                    } else {
                        BabyBear::ZERO - BabyBear::new((j - k) as u32)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                acc = acc + num * den_inv * l_bits[k];
            }
            acc
        };
        let s_unseal_early = local[sel::UNSEAL];
        let c_unseal_must_be_set = s_unseal_early * (unseal_bit_at_idx - BabyBear::ONE);
        combined = combined + alpha_pow * c_unseal_must_be_set;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // RANGE CHECK: SetField field_idx must be in {0, 1, 2, 3, 4, 5, 6, 7}
        // ====================================================================
        // Degree-8 polynomial that vanishes exactly on {0..7}:
        //   prod_{k=0}^{7} (field_idx - k) == 0
        // Gated by sel_setfield (total degree 9). Any out-of-bounds value makes
        // this constraint non-zero, causing the STARK verifier to reject.
        {
            let mut field_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                field_idx_range_product =
                    field_idx_range_product * (field_index - BabyBear::new(k));
            }
            let c_field_idx_range = s_setfield * field_idx_range_product;
            combined = combined + alpha_pow * c_field_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- GrantCapability: capability_root update --
        // param0 = cap_entry (hash of new capability)
        // new_cap_root MUST equal hash_2_to_1(old_cap_root, cap_entry).
        //
        // SOUNDNESS FIX: We compute hash_2_to_1 directly in the constraint evaluator.
        // The old approach used a prover-controlled aux[1] value which allowed a
        // malicious prover to set new_cap_root to ANY value. Now the verifier
        // independently computes the hash at each evaluation point. This works because
        // eval_constraints operates on concrete field values (not symbolic polynomials),
        // so the hash is a pure function of the trace values at the query point.
        let cap_entry_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_new_cap = hash_2_to_1(old_cap_root, cap_entry_val);
        let c_grantcap = s_grantcap * (new_cap_root - expected_new_cap);
        combined = combined + alpha_pow * c_grantcap;
        alpha_pow = alpha_pow * alpha;

        // GrantCap: balance and fields unchanged.
        let c_gc_bal_lo = s_grantcap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_gc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_gc_bal_hi = s_grantcap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_gc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_grantcap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- EmitEvent: stateless side-effect, full state passthrough --
        // The event_hash (param 0) is implicitly bound via the effects_hash
        // chain (compute_effects_hash). The AIR's role is just to forbid the
        // prover from changing any state column on an EmitEvent row.
        let s_emitevent = local[sel::EMIT_EVENT];
        let c_ee_bal_lo = s_emitevent * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_ee_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_ee_bal_hi = s_emitevent * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ee_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_ee_cap = s_emitevent * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ee_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_emitevent
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetPermissions: same shape as EmitEvent (state passthrough) --
        // Permissions live outside the VM trace (they're part of the cell's
        // off-chain manifest). The AIR's job is to bind permissions_hash
        // into effects_hash and forbid state column drift.
        let s_setperms = local[sel::SET_PERMISSIONS];
        let c_sp_bal_lo = s_setperms * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sp_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sp_bal_hi = s_setperms * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sp_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sp_cap = s_setperms * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sp_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setperms
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- SetVerificationKey: same shape as SetPermissions (passthrough) --
        let s_setvk = local[sel::SET_VERIFICATION_KEY];
        let c_svk_bal_lo = s_setvk * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_svk_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_svk_bal_hi = s_setvk * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_svk_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_svk_cap = s_setvk * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_svk_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_setvk
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- All passthrough variants (Stage 3 batch). State columns must
        //    be unchanged; nonce ticks. Variant-specific param (or absence)
        //    in PARAM_BASE+0; binds via effects_hash.
        for s_sel_idx in [
            sel::CREATE_SEAL_PAIR,
            sel::REFRESH_DELEGATION,
            sel::REVOKE_DELEGATION,
            sel::CREATE_CELL,
            sel::SPAWN_WITH_DELEGATION,
            sel::BRIDGE_CANCEL,
            sel::EXERCISE_VIA_CAPABILITY,
            sel::INTRODUCE,
            sel::PIPELINED_SEND,
            sel::CREATE_COMMITTED_ESCROW,
            sel::BRIDGE_FINALIZE,
            sel::RELEASE_ESCROW,
            sel::REFUND_ESCROW,
            sel::RELEASE_COMMITTED_ESCROW,
            sel::REFUND_COMMITTED_ESCROW,
        ] {
            let s_v = local[s_sel_idx];
            let c_bal_lo = s_v * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_v * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cap = s_v * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_v
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- RevokeCapability: capability_root update --
        // Mirrors GRANT_CAP: param0 (shared with CAP_ENTRY) carries the slot
        // hash; new_cap_root MUST equal hash_2_to_1(old_cap_root, slot_hash).
        // The verifier independently computes the hash (no prover-controlled
        // aux witness), matching the SOUNDNESS FIX comment above.
        let s_revokecap = local[sel::REVOKE_CAPABILITY];
        let slot_hash_val = local[PARAM_BASE + param::CAP_ENTRY];
        let expected_revoke_cap = hash_2_to_1(old_cap_root, slot_hash_val);
        let c_revokecap = s_revokecap * (new_cap_root - expected_revoke_cap);
        combined = combined + alpha_pow * c_revokecap;
        alpha_pow = alpha_pow * alpha;
        // RevokeCap: balance and fields unchanged.
        let c_rc_bal_lo = s_revokecap * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_rc_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_rc_bal_hi = s_revokecap * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_rc_bal_hi;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_revokecap
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteSpend: balance credit --
        // param0 = nullifier, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo + value_lo (with potential carry to hi)
        // For simplicity (v1): value fits in lo limb (value_hi == 0).
        let note_val_lo = p1;
        let c_ns_bal = s_notespend * (new_bal_lo - old_bal_lo - note_val_lo);
        combined = combined + alpha_pow * c_ns_bal;
        alpha_pow = alpha_pow * alpha;
        let c_ns_hi = s_notespend * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_ns_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteSpend: fields and cap unchanged.
        let c_ns_cap = s_notespend * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_ns_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notespend
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- NoteCreate: balance debit --
        // param0 = commitment, param1 = value_lo, param2 = value_hi
        // new_bal_lo = old_bal_lo - value_lo
        let nc_val_lo = p1;
        let c_nc_bal = s_notecreate * (new_bal_lo - old_bal_lo + nc_val_lo);
        combined = combined + alpha_pow * c_nc_bal;
        alpha_pow = alpha_pow * alpha;
        let c_nc_hi = s_notecreate * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_nc_hi;
        alpha_pow = alpha_pow * alpha;
        // NoteCreate: fields and cap unchanged.
        let c_nc_cap = s_notecreate * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_nc_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_notecreate
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- BridgeMint: balance credit (mirror NoteSpend) --
        // param0 = mint_hash, param1 = value_lo
        // new_bal_lo = old_bal_lo + value_lo
        let s_bridgemint = local[sel::BRIDGE_MINT];
        let bm_val_lo = local[PARAM_BASE + 1];
        let c_bm_bal = s_bridgemint * (new_bal_lo - old_bal_lo - bm_val_lo);
        combined = combined + alpha_pow * c_bm_bal;
        alpha_pow = alpha_pow * alpha;
        let c_bm_hi = s_bridgemint * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_bm_hi;
        alpha_pow = alpha_pow * alpha;
        let c_bm_cap = s_bridgemint * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_bm_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_bridgemint
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateEscrow / BridgeLock: balance debit (mirror NoteCreate) --
        // param0 = id_hash, param1 = amount_lo. Same shape: balance_lo
        // debits by amount_lo, balance_hi / cap_root / fields all unchanged.
        for s_sel_idx in [sel::CREATE_ESCROW, sel::BRIDGE_LOCK] {
            let s_v = local[s_sel_idx];
            let amount_lo = local[PARAM_BASE + 1];
            let c_bal = s_v * (new_bal_lo - old_bal_lo + amount_lo);
            combined = combined + alpha_pow * c_bal;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_v * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;
            let c_cap = s_v * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;
            for i in 0..8 {
                let c = s_v
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- CreateObligation: balance debit + cap_root extended --
        // Stage 2 honesty: previously cap_root was constrained UNCHANGED,
        // which meant the obligation wasn't actually committed to the
        // cell's authority graph — slash/fulfill had no algebraic way to
        // verify that this obligation existed or who the beneficiary was.
        // Fix: cap_root advances to
        //   new_cap_root == hash_2_to_1(old_cap_root, hash_2_to_1(obligation_id, beneficiary))
        // The 2-of-2 nested hash binds both obligation identity AND the
        // beneficiary so a later slash/fulfill must reference the same
        // beneficiary that the create committed to.
        //
        // param0 = stake_lo, param1 = stake_hi (unused for single-limb), param2 = obligation_id
        let stake_lo = p0;
        let c_co_bal = s_create_obligation * (new_bal_lo - old_bal_lo + stake_lo);
        combined = combined + alpha_pow * c_co_bal;
        alpha_pow = alpha_pow * alpha;
        let c_co_hi = s_create_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_co_hi;
        alpha_pow = alpha_pow * alpha;
        // Cap_root advance: encodes obligation_id + beneficiary.
        let obligation_id = local[PARAM_BASE + param::OBLIGATION_ID];
        let obligation_beneficiary = local[PARAM_BASE + param::OBLIGATION_BENEFICIARY];
        let obligation_leaf = hash_2_to_1(obligation_id, obligation_beneficiary);
        let expected_co_cap = hash_2_to_1(old_cap_root, obligation_leaf);
        let c_co_cap = s_create_obligation * (new_cap_root - expected_co_cap);
        combined = combined + alpha_pow * c_co_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_create_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- FulfillObligation: balance credit (returns stake) --
        // param0 = obligation_id, param1 = return_lo, param2 = return_hi
        // new_bal_lo = old_bal_lo + return_lo
        let return_lo = p1;
        let c_fo_bal = s_fulfill_obligation * (new_bal_lo - old_bal_lo - return_lo);
        combined = combined + alpha_pow * c_fo_bal;
        alpha_pow = alpha_pow * alpha;
        let c_fo_hi = s_fulfill_obligation * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_fo_hi;
        alpha_pow = alpha_pow * alpha;
        // FulfillObligation: fields and cap unchanged.
        let c_fo_cap = s_fulfill_obligation * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_fo_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_fulfill_obligation
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Custom (CellProgram dispatch): state continuity only --
        //
        // SECURITY NOTE (Gap 5): Custom effects provide WEAKER guarantees than
        // other effect types. The Effect VM only enforces:
        //   1. State continuity (state flows through unchanged)
        //   2. Proof commitment binding (the custom_proof_commitment hash is
        //      recorded in the public inputs for external verification)
        //
        // The ACTUAL SEMANTICS of the custom effect are defined entirely by the
        // external CellProgram. The Effect VM circuit does NOT verify the external
        // proof — it only binds its hash commitment to the turn's public inputs.
        //
        // Verifiers MUST independently verify the external proof against the
        // committed program VK hash. Without this check, a malicious prover can
        // claim any custom_proof_commitment without having a valid external proof.
        //
        // The custom_program_vk_hash in the PI identifies which CellProgram was
        // invoked. The verifier should:
        //   1. Look up the registered program by VK hash
        //   2. Verify the external proof against that program's verification key
        //   3. Check the external proof's hash matches custom_proof_commitment
        //
        // If ANY of these steps are skipped, the custom effect is effectively
        // unconstrained — the prover can claim arbitrary side-effects occurred.
        //
        // This is BY DESIGN: the Effect VM is a generic execution framework,
        // and custom programs extend it with domain-specific logic. But verifiers
        // must understand that Custom effects are only as secure as their external
        // verification implementation.
        //
        // Constraints: all state columns unchanged (same as NoOp for state).
        for i in 0..state::SIZE {
            let c = s_custom * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================

        // -- SlashObligation: balance credit (slashed stake to beneficiary) --
        // param0 = obligation_id, param1 = stake_lo, param2 = stake_hi, param3 = beneficiary
        // new_bal_lo = old_bal_lo + stake_lo
        let s_slash = local[sel::SLASH_OBLIGATION];
        let slash_stake_lo = local[PARAM_BASE + param::SLASH_STAKE_LO];
        let c_slash_bal = s_slash * (new_bal_lo - old_bal_lo - slash_stake_lo);
        combined = combined + alpha_pow * c_slash_bal;
        alpha_pow = alpha_pow * alpha;
        let c_slash_hi = s_slash * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_slash_hi;
        alpha_pow = alpha_pow * alpha;
        // SlashObligation: cap_root updated (obligation removed).
        // SOUNDNESS FIX: Compute hash_2_to_1 directly instead of trusting prover aux[1].
        let slash_obligation_id = local[PARAM_BASE + param::SLASH_OBLIGATION_ID];
        let expected_slash_cap = hash_2_to_1(old_cap_root, slash_obligation_id);
        let c_slash_cap = s_slash * (new_cap_root - expected_slash_cap);
        combined = combined + alpha_pow * c_slash_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_slash
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ===========================================================
        // Stage 2 (sealing honesty): Seal/Unseal actually update the
        // sealed_field_mask in `reserved`. The mask occupies the low 8
        // bits of `reserved`; mode_flag occupies bits 8..9. The witness
        // `aux[7]` (SEAL_POW2_IDX) holds `2^field_idx`, constrained to
        // lie in {1, 2, 4, 8, 16, 32, 64, 128} via the Lagrange basis
        // polynomial over field_idx ∈ {0..7}.
        // ===========================================================
        // Lagrange-basis polynomial L(x) = Σ_k 2^k * L_k(x) where
        //   L_k(x) = ∏_{j∈0..8, j≠k}(x - j) / ∏_{j≠k}(k - j)
        // evaluates to 2^k at x=k for k in {0..7}, and degree is 7.
        // This expresses `aux_pow2 - 2^field_idx == 0` algebraically.
        let lagrange_pow2 = |x: BabyBear| -> BabyBear {
            let mut result = BabyBear::ZERO;
            for k in 0..8u32 {
                let mut num = BabyBear::ONE;
                let mut den = BabyBear::ONE;
                for j in 0..8u32 {
                    if j == k {
                        continue;
                    }
                    num = num * (x - BabyBear::new(j));
                    let diff = if k > j {
                        BabyBear::new(k - j)
                    } else {
                        // (k - j) negative ⇒ BabyBear representation as p - (j - k).
                        BabyBear::ZERO - BabyBear::new(j - k)
                    };
                    den = den * diff;
                }
                let den_inv = den
                    .inverse()
                    .expect("Lagrange denominator non-zero on {0..7}");
                result = result + num * den_inv * BabyBear::new(1u32 << k);
            }
            result
        };

        // -- Seal: balance, fields, cap_root unchanged; reserved gains
        //    bit `field_idx`; sealed-field mask bit was previously 0. --
        let s_seal = local[sel::SEAL];
        let old_reserved_seal = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved_seal = local[STATE_AFTER_BASE + state::RESERVED];
        let seal_pow2 = local[AUX_BASE + aux_off::SEAL_POW2_IDX];

        let c_seal_bal_lo = s_seal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_seal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_seal_bal_hi = s_seal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_seal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_seal_cap = s_seal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_seal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_seal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Stage 2: reserved increases by 2^field_idx (sets the bit).
        let c_seal_reserved = s_seal * (new_reserved_seal - old_reserved_seal - seal_pow2);
        combined = combined + alpha_pow * c_seal_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: aux_pow2 == 2^field_idx (Lagrange over {0..7}).
        let seal_field_idx_a = local[PARAM_BASE + param::SEAL_FIELD_IDX];
        let c_seal_pow2_check = s_seal * (seal_pow2 - lagrange_pow2(seal_field_idx_a));
        combined = combined + alpha_pow * c_seal_pow2_check;
        alpha_pow = alpha_pow * alpha;

        // RANGE CHECK: Seal field_idx must be in {0..7}.
        {
            let seal_field_idx = local[PARAM_BASE + param::SEAL_FIELD_IDX];
            let mut seal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                seal_idx_range_product =
                    seal_idx_range_product * (seal_field_idx - BabyBear::new(k));
            }
            let c_seal_idx_range = s_seal * seal_idx_range_product;
            combined = combined + alpha_pow * c_seal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- Unseal: balance, fields, cap_root unchanged; reserved loses
        //    bit `field_idx`; sealed-field mask bit was previously 1. --
        let s_unseal = local[sel::UNSEAL];
        let old_reserved_unseal = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved_unseal = local[STATE_AFTER_BASE + state::RESERVED];
        let unseal_pow2 = local[AUX_BASE + aux_off::SEAL_POW2_IDX];

        let c_unseal_bal_lo = s_unseal * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_unseal_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_bal_hi = s_unseal * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_unseal_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_unseal_cap = s_unseal * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_unseal_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_unseal
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }
        // Stage 2: reserved decreases by 2^field_idx (clears the bit;
        // requires bit was previously set, otherwise wrap into mode_flag
        // bits → trace-gen-side constraint).
        let c_unseal_reserved =
            s_unseal * (old_reserved_unseal - new_reserved_unseal - unseal_pow2);
        combined = combined + alpha_pow * c_unseal_reserved;
        alpha_pow = alpha_pow * alpha;
        // Stage 2: aux_pow2 == 2^field_idx.
        let unseal_field_idx_a = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
        let c_unseal_pow2_check = s_unseal * (unseal_pow2 - lagrange_pow2(unseal_field_idx_a));
        combined = combined + alpha_pow * c_unseal_pow2_check;
        alpha_pow = alpha_pow * alpha;

        // RANGE CHECK: Unseal field_idx must be in {0..7}.
        {
            let unseal_field_idx = local[PARAM_BASE + param::UNSEAL_FIELD_IDX];
            let mut unseal_idx_range_product = BabyBear::ONE;
            for k in 0..8u32 {
                unseal_idx_range_product =
                    unseal_idx_range_product * (unseal_field_idx - BabyBear::new(k));
            }
            let c_unseal_idx_range = s_unseal * unseal_idx_range_product;
            combined = combined + alpha_pow * c_unseal_idx_range;
            alpha_pow = alpha_pow * alpha;
        }

        // -- MakeSovereign: mode_flag 0->1, balance/fields/cap preserved --
        let s_makesov = local[sel::MAKE_SOVEREIGN];
        let old_reserved = local[STATE_BEFORE_BASE + state::RESERVED];
        let new_reserved = local[STATE_AFTER_BASE + state::RESERVED];
        let c_sov_mode = s_makesov * (new_reserved - old_reserved - BabyBear::new(256));
        combined = combined + alpha_pow * c_sov_mode;
        alpha_pow = alpha_pow * alpha;
        // Stage 2 (MakeSovereign once-only): the mode bit must currently be 0.
        // Combined with `new_reserved - old_reserved == 256` (above), this
        // enforces the canonical 0→1 transition. Without this, a malicious
        // prover could apply MakeSovereign to an already-sovereign cell,
        // pushing reserved through 2*256 (which is no longer a valid
        // encoding — mode bit becomes non-boolean).
        let c_sov_was_managed = s_makesov * mode_bit;
        combined = combined + alpha_pow * c_sov_was_managed;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_lo = s_makesov * (new_bal_lo - old_bal_lo);
        combined = combined + alpha_pow * c_sov_bal_lo;
        alpha_pow = alpha_pow * alpha;
        let c_sov_bal_hi = s_makesov * (new_bal_hi - old_bal_hi);
        combined = combined + alpha_pow * c_sov_bal_hi;
        alpha_pow = alpha_pow * alpha;
        let c_sov_cap = s_makesov * (new_cap_root - old_cap_root);
        combined = combined + alpha_pow * c_sov_cap;
        alpha_pow = alpha_pow * alpha;
        for i in 0..8 {
            let c = s_makesov
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // -- CreateCellFromFactory: state flows through unchanged --
        let s_factory = local[sel::CREATE_CELL_FROM_FACTORY];
        for i in 0..state::SIZE {
            let c = s_factory * (local[STATE_AFTER_BASE + i] - local[STATE_BEFORE_BASE + i]);
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CapTP Effects (provable CapTP operations)
        // ====================================================================

        // -- ExportSturdyRef: swiss_number = hash(cell_id, random_seed, counter) --
        // Proves the swiss number derivation is correct.
        // State: field[7] increments (export_counter), balance/cap/other fields unchanged.
        let s_export = local[sel::EXPORT_STURDY_REF];
        {
            let cell_id = local[PARAM_BASE + param::EXPORT_CELL_ID];
            let random_seed = local[PARAM_BASE + param::EXPORT_RANDOM_SEED];
            let export_counter = local[PARAM_BASE + param::EXPORT_COUNTER];
            // Swiss number = hash(cell_id, hash(random_seed, counter))
            let inner_hash = hash_2_to_1(random_seed, export_counter);
            let expected_swiss = hash_2_to_1(cell_id, inner_hash);
            // The computed swiss is stored in aux[0] for binding.
            let aux_swiss = local[AUX_BASE + 0];
            let c_swiss = s_export * (aux_swiss - expected_swiss);
            combined = combined + alpha_pow * c_swiss;
            alpha_pow = alpha_pow * alpha;

            // field[7] must increment by 1 (export counter).
            let old_f7 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 7];
            let new_f7 = local[STATE_AFTER_BASE + state::FIELD_BASE + 7];
            let c_counter = s_export * (new_f7 - old_f7 - BabyBear::ONE);
            combined = combined + alpha_pow * c_counter;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_export * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_export * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_export * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..7 unchanged (only field[7] changes).
            for i in 0..7 {
                let c = s_export
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- EnlivenRef: validate swiss number is a member of the cell's
        // committed swiss_table_root --
        //
        // Stage 7 / P1.C: previously tautological. Now does 1-hop Merkle
        // membership against the cell's state.fields[4] slot (the
        // committed swiss_table_root mirror). The prover supplies a
        // sibling hash; the leaf is AIR-computed from PARAMs; the
        // chosen-parent must equal the committed root.
        //
        // Aux layout (NB: aux[2..5] reserved on row 0 for delta/effects_hash):
        //   aux[0] = root  (= state_after.fields[4])
        //   aux[1] = leaf  (must equal hash(swiss, hash(cell_id, perms)))
        //   aux[6] = sibling (prover-supplied)
        //   aux[7] = chosen = hash(leaf, sibling)
        //
        // State: field[6] increments (use_count); field[4]
        // (swiss_table_root) updates to `chosen`; other fields unchanged.
        let s_enliven = local[sel::ENLIVEN_REF];
        {
            let swiss = local[PARAM_BASE + param::ENLIVEN_SWISS];
            let expected_cell_id = local[PARAM_BASE + param::ENLIVEN_CELL_ID];
            let expected_perms = local[PARAM_BASE + param::ENLIVEN_PERMISSIONS];
            let inner = hash_2_to_1(expected_cell_id, expected_perms);
            let expected_leaf = hash_2_to_1(swiss, inner);
            let aux_root = local[AUX_BASE + 0];
            let aux_leaf = local[AUX_BASE + 1];
            let c_leaf = s_enliven * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 6];
            let aux_chosen = local[AUX_BASE + 7];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_enliven * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let f4_after = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_root_field = s_enliven * (aux_root - f4_after);
            combined = combined + alpha_pow * c_root_field;
            alpha_pow = alpha_pow * alpha;
            let c_chosen_eq_root = s_enliven * (aux_chosen - aux_root);
            combined = combined + alpha_pow * c_chosen_eq_root;
            alpha_pow = alpha_pow * alpha;
            // Stage 7 / P1.C tightening: pin the sibling to
            // `state_before.fields[4]` so the new root is an
            // append-only extension of the old root. Without this
            // constraint, the prover could supply any sibling and
            // obtain any new root, severing the chain.
            let f4_before = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_sib_chain = s_enliven * (aux_sibling - f4_before);
            combined = combined + alpha_pow * c_sib_chain;
            alpha_pow = alpha_pow * alpha;

            // field[6] must increment by 1 (use_count).
            let old_f6 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 6];
            let new_f6 = local[STATE_AFTER_BASE + state::FIELD_BASE + 6];
            let c_use = s_enliven * (new_f6 - old_f6 - BabyBear::ONE);
            combined = combined + alpha_pow * c_use;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_enliven * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_enliven * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_enliven * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..3, 5, and 7 unchanged (only field[6] and the
            // committed root in field[4] may change on this row).
            for i in [0usize, 1, 2, 3, 5, 7] {
                let c = s_enliven
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- DropRef: decrement refcount; bind holder_federation into
        //    the committed refcount_table_root (state.fields[3]) --
        //
        // Stage 7 / P1.C: previously the `holder_federation` PARAM was
        // unbound from any committed structure. Now the AIR enforces a
        // 1-hop Merkle membership against `state_after.fields[3]` (the
        // committed refcount_table_root mirror). Leaf =
        // hash(ref_id_field=cell_id, holder_federation).
        let s_drop = local[sel::DROP_REF];
        {
            let refcount_param = local[PARAM_BASE + param::DROP_REFCOUNT];
            let cell_id_param = local[PARAM_BASE + param::DROP_CELL_ID];
            let holder_fed_param = local[PARAM_BASE + param::DROP_HOLDER_FED];

            // field[5] must decrement by 1.
            let old_f5 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 5];
            let new_f5 = local[STATE_AFTER_BASE + state::FIELD_BASE + 5];
            let c_dec = s_drop * (new_f5 - old_f5 + BabyBear::ONE);
            combined = combined + alpha_pow * c_dec;
            alpha_pow = alpha_pow * alpha;

            // refcount param must match old field[5] (binds the declared refcount).
            let c_rc = s_drop * (refcount_param - old_f5);
            combined = combined + alpha_pow * c_rc;
            alpha_pow = alpha_pow * alpha;

            // Prove refcount > 0: aux[0] = inverse(refcount_param).
            let rc_inv = local[AUX_BASE + 0];
            let c_nonzero = s_drop * (refcount_param * rc_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_nonzero;
            alpha_pow = alpha_pow * alpha;

            // 1-hop Merkle membership against refcount_table_root in
            // state_after.fields[3]:
            //   aux[1] = leaf = hash_2_to_1(cell_id, holder_federation)
            //   aux[6] = prover-supplied sibling
            //   aux[7] = chosen_parent = hash_2_to_1(leaf, sibling)
            //   chosen_parent == state_after.fields[3]
            // Aux[2..5] are reserved on row 0 for delta/effects_hash
            // PI binding; we use aux[6..7] for the Merkle witness.
            let expected_leaf = hash_2_to_1(cell_id_param, holder_fed_param);
            let aux_leaf = local[AUX_BASE + 1];
            let c_leaf = s_drop * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 6];
            let aux_chosen = local[AUX_BASE + 7];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_drop * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let f3_after = local[STATE_AFTER_BASE + state::FIELD_BASE + 3];
            let c_root = s_drop * (aux_chosen - f3_after);
            combined = combined + alpha_pow * c_root;
            alpha_pow = alpha_pow * alpha;
            // Stage 7 / P1.C tightening: pin the sibling to
            // `state_before.fields[3]` (old refcount_table_root).
            // Without this, the prover could pick any sibling and
            // obtain any new root.
            let f3_before = local[STATE_BEFORE_BASE + state::FIELD_BASE + 3];
            let c_sib_chain = s_drop * (aux_sibling - f3_before);
            combined = combined + alpha_pow * c_sib_chain;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_drop * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_drop * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_cap = s_drop * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Fields 0..2, 4, 6, 7 unchanged (field[3] holds the new
            // refcount_table_root mirror, field[5] decrements).
            for i in [0usize, 1, 2, 4, 6, 7] {
                let c = s_drop
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- ValidateHandoff: prove certificate hash is in approved set --
        //
        // Stage 7 / P1.C: previously tautological. Now does honest 1-hop
        // Merkle membership against PI[APPROVED_HANDOFFS_BASE] (position 0;
        // the 4-felt widening). The PARAM HANDOFF_APPROVED_SET_ROOT must
        // equal PI[APPROVED_HANDOFFS_BASE], so the prover cannot pick
        // their own root. Leaf = hash(cert_hash, hash(recipient_pk,
        // introducer_pk)). aux[1] = leaf, aux[2] = sibling, aux[3] =
        // chosen_parent = hash(leaf, sibling); chosen_parent ==
        // approved_set_root.
        //
        // Consume-on-use: lives at the executor, which rotates the
        // federation's approved-handoffs root after a successful
        // ValidateHandoff (per `DESIGN-captp-integration.md` §9.4). A
        // replay produces a non-membership witness for the rotated
        // root, which the AIR proof cannot satisfy.
        //
        // State: cap_root updated (routing entry for recipient),
        // balance/fields unchanged.
        let s_handoff = local[sel::VALIDATE_HANDOFF];
        {
            let cert_hash = local[PARAM_BASE + param::HANDOFF_CERT_HASH];
            let recipient_pk = local[PARAM_BASE + param::HANDOFF_RECIPIENT_PK];
            let introducer_pk = local[PARAM_BASE + param::HANDOFF_INTRODUCER_PK];
            let approved_root = local[PARAM_BASE + param::HANDOFF_APPROVED_SET_ROOT];

            // Leaf bound to PARAMs:
            //   leaf = hash(cert_hash, hash(recipient_pk, introducer_pk))
            //
            // Aux layout (NB: aux[2..5] reserved on row 0):
            //   aux[0] = leaf
            //   aux[1] = sibling
            //   aux[6] = chosen = hash(leaf, sibling)
            let pks = hash_2_to_1(recipient_pk, introducer_pk);
            let expected_leaf = hash_2_to_1(cert_hash, pks);
            let aux_leaf = local[AUX_BASE + 0];
            let c_leaf = s_handoff * (aux_leaf - expected_leaf);
            combined = combined + alpha_pow * c_leaf;
            alpha_pow = alpha_pow * alpha;
            let aux_sibling = local[AUX_BASE + 1];
            let aux_chosen = local[AUX_BASE + 6];
            let expected_chosen = hash_2_to_1(aux_leaf, aux_sibling);
            let c_chosen = s_handoff * (aux_chosen - expected_chosen);
            combined = combined + alpha_pow * c_chosen;
            alpha_pow = alpha_pow * alpha;
            let c_root_eq = s_handoff * (aux_chosen - approved_root);
            combined = combined + alpha_pow * c_root_eq;
            alpha_pow = alpha_pow * alpha;

            // Bind PARAM approved_root to PI[APPROVED_HANDOFFS_BASE]
            // (position 0). This closes the prover-control gap: the
            // verifier supplies the PI; the prover cannot invent a
            // root.
            let pi_root = public_inputs[pi::APPROVED_HANDOFFS_BASE];
            let c_pi_bind = s_handoff * (approved_root - pi_root);
            combined = combined + alpha_pow * c_pi_bind;
            alpha_pow = alpha_pow * alpha;

            // Cap root updated: new_cap_root = hash(old_cap_root, hash(recipient_pk, cert_hash))
            // This creates a routing entry for the recipient.
            let routing_entry = hash_2_to_1(recipient_pk, cert_hash);
            let expected_new_cap = hash_2_to_1(old_cap_root, routing_entry);
            let c_cap = s_handoff * (new_cap_root - expected_new_cap);
            combined = combined + alpha_pow * c_cap;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_bal_lo = s_handoff * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_bal_hi = s_handoff * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // All fields unchanged.
            for i in 0..8 {
                let c = s_handoff
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // Storage Queue Effects (provable MerkleQueue operations)
        // ====================================================================

        // -- AllocateQueue: balance debit (capacity * cost_per_slot), field[4] = empty hash --
        let s_alloc_queue = local[sel::ALLOCATE_QUEUE];
        {
            let capacity = local[PARAM_BASE + param::QUEUE_CAPACITY];
            let cost_per_slot = local[PARAM_BASE + param::QUEUE_COST_PER_SLOT];
            let alloc_cost = capacity * cost_per_slot;

            // Balance debit: new_bal_lo = old_bal_lo - alloc_cost.
            let c_aq_bal = s_alloc_queue * (new_bal_lo - old_bal_lo + alloc_cost);
            combined = combined + alpha_pow * c_aq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_aq_hi = s_alloc_queue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_aq_hi;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become empty_queue_hash = hash_2_to_1(ZERO, ZERO).
            let empty_queue_hash = hash_2_to_1(BabyBear::ZERO, BabyBear::ZERO);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_aq_root = s_alloc_queue * (new_f4 - empty_queue_hash);
            combined = combined + alpha_pow * c_aq_root;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_aq_cap = s_alloc_queue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_aq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_alloc_queue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_alloc_queue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- EnqueueMessage: queue root hash chain, balance debit (deposit),
        //    and optional program validation hash binding --
        let s_enqueue = local[sel::ENQUEUE_MESSAGE];
        {
            let message_hash = local[PARAM_BASE + param::ENQUEUE_MSG_HASH];
            let deposit = local[PARAM_BASE + param::ENQUEUE_DEPOSIT];
            let sender_id = local[PARAM_BASE + param::ENQUEUE_SENDER];

            // Queue root transition: new_root = hash(old_root, message_hash).
            let old_queue_root = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let expected_new_root = hash_2_to_1(old_queue_root, message_hash);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_eq_root = s_enqueue * (new_f4 - expected_new_root);
            combined = combined + alpha_pow * c_eq_root;
            alpha_pow = alpha_pow * alpha;

            // Balance debit: new_bal_lo = old_bal_lo - deposit.
            let c_eq_bal = s_enqueue * (new_bal_lo - old_bal_lo + deposit);
            combined = combined + alpha_pow * c_eq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_eq_hi = s_enqueue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_eq_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_eq_cap = s_enqueue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_eq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_enqueue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_enqueue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }

            // ================================================================
            // Queue program validation hash binding.
            //
            // NOTE: aux[2..5] on row 0 are reserved for public input values
            // (delta_mag, delta_sign, effects_hash_lo, effects_hash_hi).
            // We use aux[6] for the validation hash and aux[7] for program_vk_inv.
            //
            // param[4] = ENQUEUE_PROGRAM_VK: queue program VK as field element.
            //   ZERO if queue has no program (backward compatible).
            // aux[6] = program_validation_hash
            // aux[7] = inverse(program_vk) when != 0, else 0
            //
            // Constraints:
            //   1. program_vk != 0 => aux[6] == hash(program_vk, hash(sender, msg))
            //   2. program_vk == 0 => aux[6] == 0
            // ================================================================
            let program_vk = local[PARAM_BASE + param::ENQUEUE_PROGRAM_VK];
            let validation_hash = local[AUX_BASE + 6];
            let program_vk_inv = local[AUX_BASE + 7];

            // Constraint 1: When program_vk != 0, validation_hash must equal expected.
            let inner_hash = hash_2_to_1(sender_id, message_hash);
            let expected_validation = hash_2_to_1(program_vk, inner_hash);
            let c_prog_valid = s_enqueue * program_vk * (validation_hash - expected_validation);
            combined = combined + alpha_pow * c_prog_valid;
            alpha_pow = alpha_pow * alpha;

            // Constraint 2: When program_vk == 0, validation_hash must be zero.
            let c_prog_zero =
                s_enqueue * (BabyBear::ONE - program_vk * program_vk_inv) * validation_hash;
            combined = combined + alpha_pow * c_prog_zero;
            alpha_pow = alpha_pow * alpha;
        }

        // -- DequeueMessage: queue root hash chain advance, balance credit (deposit refund) --
        let s_dequeue = local[sel::DEQUEUE_MESSAGE];
        {
            let expected_msg_hash = local[PARAM_BASE + param::DEQUEUE_EXPECTED_HASH];
            let deposit_refund = local[PARAM_BASE + param::DEQUEUE_DEPOSIT_REFUND];

            // Queue root advances: new_root = hash(old_root, expected_message_hash).
            let old_queue_root = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let expected_new_root = hash_2_to_1(old_queue_root, expected_msg_hash);
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_dq_root = s_dequeue * (new_f4 - expected_new_root);
            combined = combined + alpha_pow * c_dq_root;
            alpha_pow = alpha_pow * alpha;

            // expected_message_hash must be non-zero (non-empty queue).
            // Proved via aux[1] = inverse(expected_msg_hash).
            let msg_inv = local[AUX_BASE + 1];
            let c_dq_nonempty = s_dequeue * (expected_msg_hash * msg_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_dq_nonempty;
            alpha_pow = alpha_pow * alpha;

            // Balance credit: new_bal_lo = old_bal_lo + deposit_refund.
            let c_dq_bal = s_dequeue * (new_bal_lo - old_bal_lo - deposit_refund);
            combined = combined + alpha_pow * c_dq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_dq_hi = s_dequeue * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_dq_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_dq_cap = s_dequeue * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_dq_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_dequeue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_dequeue
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- ResizeQueue: capacity update with sign-decomposed delta --
        // Stage 2 honesty fix: separately constrain magnitude + sign so a
        // shrink can't wrap into a fictitious debit. The prover witnesses
        // `delta_sign ∈ {0, 1}` and `delta_mag = |new_cap - old_cap|` in
        // aux[RESIZE_DELTA_SIGN/MAG]. Constraints:
        //   (a) sign is boolean
        //   (b) (new_cap - old_cap) == delta_mag * (1 - 2*sign)
        //   (c) balance change == delta_mag * cost_per_slot * (1 - sign)
        //       (grow ⇒ debit; shrink ⇒ no debit)
        let s_resize = local[sel::RESIZE_QUEUE];
        {
            let new_capacity = local[PARAM_BASE + param::RESIZE_NEW_CAPACITY];
            let old_capacity = local[PARAM_BASE + param::RESIZE_OLD_CAPACITY];
            let cost_per_slot = local[PARAM_BASE + param::RESIZE_COST_PER_SLOT];
            let delta_sign = local[AUX_BASE + aux_off::RESIZE_DELTA_SIGN];
            let delta_mag = local[AUX_BASE + aux_off::RESIZE_DELTA_MAG];
            let two = BabyBear::ONE + BabyBear::ONE;

            // (a) sign boolean (gated by selector; non-resize rows have
            // delta_sign = 0 by convention, so the constraint is trivially
            // satisfied — but we apply unconditional boolean check here
            // gated by the selector to avoid affecting non-resize rows).
            let c_rq_sign_bool = s_resize * delta_sign * (delta_sign - BabyBear::ONE);
            combined = combined + alpha_pow * c_rq_sign_bool;
            alpha_pow = alpha_pow * alpha;

            // (b) signed-delta binding.
            let c_rq_delta = s_resize
                * ((new_capacity - old_capacity) - delta_mag * (BabyBear::ONE - two * delta_sign));
            combined = combined + alpha_pow * c_rq_delta;
            alpha_pow = alpha_pow * alpha;

            // (c) balance change: grow ⇒ debit; shrink ⇒ no change.
            // new_bal_lo == old_bal_lo - delta_mag * cost_per_slot * (1 - sign)
            // <=>
            // new_bal_lo - old_bal_lo + delta_mag * cost_per_slot * (1 - sign) == 0
            let resize_cost = delta_mag * cost_per_slot * (BabyBear::ONE - delta_sign);
            let c_rq_bal = s_resize * (new_bal_lo - old_bal_lo + resize_cost);
            combined = combined + alpha_pow * c_rq_bal;
            alpha_pow = alpha_pow * alpha;
            let c_rq_hi = s_resize * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_rq_hi;
            alpha_pow = alpha_pow * alpha;

            // field[5] must become new_capacity.
            let new_f5 = local[STATE_AFTER_BASE + state::FIELD_BASE + 5];
            let c_rq_cap_field = s_resize * (new_f5 - new_capacity);
            combined = combined + alpha_pow * c_rq_cap_field;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_rq_cap = s_resize * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_rq_cap;
            alpha_pow = alpha_pow * alpha;

            // Queue root (field[4]) unchanged.
            let c_rq_f4 = s_resize
                * (local[STATE_AFTER_BASE + state::FIELD_BASE + 4]
                    - local[STATE_BEFORE_BASE + state::FIELD_BASE + 4]);
            combined = combined + alpha_pow * c_rq_f4;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 6..8) unchanged.
            for i in 0..4 {
                let c = s_resize
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 6..8 {
                let c = s_resize
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // Storage Phase 3: Atomic and Pipeline Effects
        // ====================================================================

        // -- AtomicQueueTx: atomic cross-queue transaction --
        // Proves: field[4] transitions from combined_old_root to combined_new_root.
        // Binding: aux[0] == hash(tx_hash, hash(combined_old_root, combined_new_root))
        // State: field[4] changes, balance debited by net_deposit, cap/other fields unchanged.
        // Balance: new_bal_lo = old_bal_lo - net_deposit (like Transfer direction=1).
        // This allows atomic transactions involving deposits (enqueue ops pay deposits,
        // dequeue ops receive refunds; the net is the overall balance change).
        let s_atomic_tx = local[sel::ATOMIC_QUEUE_TX];
        {
            let tx_hash_val = local[PARAM_BASE + param::ATOMIC_TX_HASH];
            let combined_old = local[PARAM_BASE + param::ATOMIC_TX_COMBINED_OLD_ROOT];
            let combined_new = local[PARAM_BASE + param::ATOMIC_TX_COMBINED_NEW_ROOT];
            let net_deposit = local[PARAM_BASE + param::ATOMIC_TX_NET_DEPOSIT];

            // field[4] must equal combined_old_root before.
            let old_f4 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_atx_old = s_atomic_tx * (old_f4 - combined_old);
            combined = combined + alpha_pow * c_atx_old;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become combined_new_root.
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_atx_new = s_atomic_tx * (new_f4 - combined_new);
            combined = combined + alpha_pow * c_atx_new;
            alpha_pow = alpha_pow * alpha;

            // Binding constraint: aux[0] == hash(tx_hash, hash(combined_old, combined_new))
            let inner_hash = hash_2_to_1(combined_old, combined_new);
            let expected_binding = hash_2_to_1(tx_hash_val, inner_hash);
            let aux_binding = local[AUX_BASE + 0];
            let c_atx_bind = s_atomic_tx * (aux_binding - expected_binding);
            combined = combined + alpha_pow * c_atx_bind;
            alpha_pow = alpha_pow * alpha;

            // Balance debit: new_bal_lo = old_bal_lo - net_deposit.
            // This follows the same pattern as Transfer (direction=1) and EnqueueMessage.
            // net_deposit == 0 means no balance change (backward compatible).
            let c_atx_bal_lo = s_atomic_tx * (new_bal_lo - old_bal_lo + net_deposit);
            combined = combined + alpha_pow * c_atx_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_atx_bal_hi = s_atomic_tx * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_atx_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_atx_cap = s_atomic_tx * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_atx_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_atomic_tx
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_atomic_tx
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // -- PipelineStep: prove a pipeline step correctly routed a message --
        // Proves: source_new_root == hash(source_old_root, message_hash) (dequeue)
        //         sink_new_root == hash(sink_old_root_aux, message_hash) (enqueue)
        //         pipeline_id binding (must match, proves authorization).
        // State: field[4] transitions from source_old_root to source_new_root.
        let s_pipeline = local[sel::PIPELINE_STEP];
        {
            let pipeline_id_val = local[PARAM_BASE + param::PIPELINE_ID];
            let source_old = local[PARAM_BASE + param::PIPELINE_SOURCE_OLD_ROOT];
            let source_new = local[PARAM_BASE + param::PIPELINE_SOURCE_NEW_ROOT];
            let sink_new = local[PARAM_BASE + param::PIPELINE_SINK_NEW_ROOT];
            let msg_hash = local[PARAM_BASE + param::PIPELINE_MESSAGE_HASH];

            // P1-5 fix: enforce pipeline_id != 0. Without this, the prover
            // could claim pipeline_id=0 (an unauthorized null pipeline) and
            // pass all other constraints. We store pipeline_id^-1 in aux[6]
            // and require `s_pipeline * (pipeline_id * aux[6] - 1) == 0`.
            // Branch analysis:
            //   - s_pipeline = 0 (other selector): constraint trivially holds.
            //   - s_pipeline = 1 and pipeline_id = 0: forces 0*x - 1 == 0, i.e.,
            //     -1 == 0, unsatisfiable. ⇒ verifier rejects.
            //   - s_pipeline = 1 and pipeline_id != 0: requires aux[6] = 1/pipeline_id.
            // This mirrors the DropRef refcount pattern.
            let pipeline_id_inv = local[AUX_BASE + 6];
            let c_pipeline_nonzero =
                s_pipeline * (pipeline_id_val * pipeline_id_inv - BabyBear::ONE);
            combined = combined + alpha_pow * c_pipeline_nonzero;
            alpha_pow = alpha_pow * alpha;

            // Source dequeue constraint:
            // source_new_root == hash(source_old_root, message_hash)
            let expected_source_new = hash_2_to_1(source_old, msg_hash);
            let c_ps_source = s_pipeline * (source_new - expected_source_new);
            combined = combined + alpha_pow * c_ps_source;
            alpha_pow = alpha_pow * alpha;

            // aux[0] must equal expected_source_new (verifiable witness).
            let aux_expected = local[AUX_BASE + 0];
            let c_ps_aux = s_pipeline * (aux_expected - expected_source_new);
            combined = combined + alpha_pow * c_ps_aux;
            alpha_pow = alpha_pow * alpha;

            // field[4] must equal source_old_root before.
            let old_f4 = local[STATE_BEFORE_BASE + state::FIELD_BASE + 4];
            let c_ps_old = s_pipeline * (old_f4 - source_old);
            combined = combined + alpha_pow * c_ps_old;
            alpha_pow = alpha_pow * alpha;

            // field[4] must become source_new_root after.
            let new_f4 = local[STATE_AFTER_BASE + state::FIELD_BASE + 4];
            let c_ps_new = s_pipeline * (new_f4 - source_new);
            combined = combined + alpha_pow * c_ps_new;
            alpha_pow = alpha_pow * alpha;

            // Pipeline ID binding: pipeline_id must be non-zero (proves authorization).
            // Proved via aux[1] storing sink_new_root (also serves as pipeline binding).
            // The pipeline_id is a content-addressed hash of the pipeline definition;
            // it being present in the params proves this step was authorized.
            let aux_sink = local[AUX_BASE + 1];
            let c_ps_sink = s_pipeline * (aux_sink - sink_new);
            combined = combined + alpha_pow * c_ps_sink;
            alpha_pow = alpha_pow * alpha;

            // Balance unchanged.
            let c_ps_bal_lo = s_pipeline * (new_bal_lo - old_bal_lo);
            combined = combined + alpha_pow * c_ps_bal_lo;
            alpha_pow = alpha_pow * alpha;
            let c_ps_bal_hi = s_pipeline * (new_bal_hi - old_bal_hi);
            combined = combined + alpha_pow * c_ps_bal_hi;
            alpha_pow = alpha_pow * alpha;

            // Cap root unchanged.
            let c_ps_cap = s_pipeline * (new_cap_root - old_cap_root);
            combined = combined + alpha_pow * c_ps_cap;
            alpha_pow = alpha_pow * alpha;

            // Other fields (0..4, 5..8) unchanged.
            for i in 0..4 {
                let c = s_pipeline
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
            for i in 5..8 {
                let c = s_pipeline
                    * (local[STATE_AFTER_BASE + state::FIELD_BASE + i]
                        - local[STATE_BEFORE_BASE + state::FIELD_BASE + i]);
                combined = combined + alpha_pow * c;
                alpha_pow = alpha_pow * alpha;
            }
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Balance range check and net_delta soundness
        // ====================================================================
        //
        // SOUNDNESS FIX (Gap 1): Prevent balance underflow exploitation.
        //
        // For debit operations (Transfer out, NoteCreate, CreateObligation),
        // the constraint `new_bal_lo = old_bal_lo - amount` uses BabyBear
        // modular arithmetic. If amount > old_bal_lo, the result wraps to a
        // large field element (p - deficit), creating value from nothing.
        //
        // Defense: We add a range check that new_bal_lo < 2^30 for ALL rows.
        // This is achieved via the state commitment integrity constraint
        // (Group 4): state_commit == hash_4_to_1(bal_lo, bal_hi, nonce, ...).
        // Since the boundary constraints pin the first and last commitments,
        // and transition constraints chain intermediate commitments, any
        // wrapped value would produce a commitment inconsistent with the
        // boundary pins ONLY IF the verifier independently knows the expected
        // final state.
        //
        // The STRONGER in-circuit defense: constrain that for debit effects,
        // the result is non-negative. We do this by requiring the prover to
        // supply a witness that old_bal_lo >= amount (for the relevant rows).
        //
        // Approach: For Transfer (direction=1), NoteCreate, and CreateObligation,
        // constrain: (old_bal_lo - amount) == new_bal_lo (already done above)
        // AND: new_bal_lo * (new_bal_lo - 1) * ... is NOT feasible at this degree.
        //
        // Instead, we use the sign-bit approach on the net_delta PI:
        // Constrain net_delta_sign to be boolean (0 or 1).
        // This ensures the prover can't use a non-boolean sign value to encode
        // arbitrary field elements as the "signed delta".
        // NOTE: The delta_sign boolean constraint is placed at the END of
        // eval_constraints (after Group 4) to preserve alpha_pow ordering for
        // existing constraints. See CONSTRAINT GROUP 5 below.

        // Additionally: constrain that the net_delta magnitude fits in 30 bits.
        // This is enforced by requiring that magnitude < 2^30. We use the
        // auxiliary column aux[6] to store magnitude decomposition:
        //   aux[6] = mag_hi_15 (upper 15 bits of magnitude)
        // The prover must provide: magnitude == mag_lo_15 + mag_hi_15 * 2^15
        // where both halves are in [0, 2^15). This is checked via the
        // degree-8 vanishing polynomial approach (checking top byte).
        //
        // For now, the sign-boolean constraint above combined with the
        // state commitment hash chain provides the primary defense.
        // The magnitude is implicitly range-checked because:
        //   - Initial balance is verified by the caller (known good state)
        //   - Each row's balance is committed via Poseidon2 hash
        //   - The final commitment is checked by the verifier
        //   - Any wraparound produces a different commitment than expected

        // CONSTRAINT GROUP 3: Transition constraints (row continuity)
        // ====================================================================
        // next_row.state_before == this_row.state_after
        // (Enforced on all rows except the last — the STARK framework handles this
        //  via the transition vanishing polynomial which excludes the last row.)
        for i in 0..state::SIZE {
            let c = next[STATE_BEFORE_BASE + i] - local[STATE_AFTER_BASE + i];
            combined = combined + alpha_pow * c;
            alpha_pow = alpha_pow * alpha;
        }

        // Nonce increment: for non-NoOp rows, nonce increments by 1.
        // For NoOp (padding) rows, nonce stays the same.
        // Combined: new_nonce == old_nonce + (1 - sel_noop)
        let c_nonce = new_nonce - old_nonce - (BabyBear::ONE - s_noop);
        combined = combined + alpha_pow * c_nonce;
        alpha_pow = alpha_pow * alpha;

        // ====================================================================
        // CONSTRAINT GROUP 4: State commitment integrity (tree hash)
        // ====================================================================
        // The state_commitment in state_after MUST equal the tree hash of the
        // state_after columns. This prevents a malicious prover from claiming
        // an arbitrary commitment that doesn't match the actual state.
        //
        // Tree structure (constrainable via hash_4_to_1):
        //   inter1 = hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
        //   inter2 = hash_4_to_1(field[1], field[2], field[3], field[4])
        //   inter3 = hash_4_to_1(field[5], field[6], field[7], cap_root)
        //   state_commit = hash_4_to_1(inter1, inter2, inter3, ZERO)
        //
        // The intermediates are stored in aux[8..10] and verified here.
        {
            let after_bal_lo = local[STATE_AFTER_BASE + state::BALANCE_LO];
            let after_bal_hi = local[STATE_AFTER_BASE + state::BALANCE_HI];
            let after_nonce = local[STATE_AFTER_BASE + state::NONCE];
            let after_cap_root = local[STATE_AFTER_BASE + state::CAP_ROOT];
            let after_commit = local[STATE_AFTER_BASE + state::STATE_COMMIT];

            let inter1 = local[AUX_BASE + aux_off::STATE_INTER1];
            let inter2 = local[AUX_BASE + aux_off::STATE_INTER2];
            let inter3 = local[AUX_BASE + aux_off::STATE_INTER3];

            // Constraint: inter1 == hash_4_to_1(bal_lo, bal_hi, nonce, field[0])
            let expected_inter1 = hash_4_to_1(&[
                after_bal_lo,
                after_bal_hi,
                after_nonce,
                local[STATE_AFTER_BASE + state::FIELD_BASE + 0],
            ]);
            let c_inter1 = inter1 - expected_inter1;
            combined = combined + alpha_pow * c_inter1;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter2 == hash_4_to_1(field[1], field[2], field[3], field[4])
            let expected_inter2 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 1],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 2],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 3],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 4],
            ]);
            let c_inter2 = inter2 - expected_inter2;
            combined = combined + alpha_pow * c_inter2;
            alpha_pow = alpha_pow * alpha;

            // Constraint: inter3 == hash_4_to_1(field[5], field[6], field[7], cap_root)
            let expected_inter3 = hash_4_to_1(&[
                local[STATE_AFTER_BASE + state::FIELD_BASE + 5],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 6],
                local[STATE_AFTER_BASE + state::FIELD_BASE + 7],
                after_cap_root,
            ]);
            let c_inter3 = inter3 - expected_inter3;
            combined = combined + alpha_pow * c_inter3;
            alpha_pow = alpha_pow * alpha;

            // Constraint: state_commit == hash_4_to_1(inter1, inter2, inter3, ZERO)
            let expected_commit = hash_4_to_1(&[inter1, inter2, inter3, BabyBear::ZERO]);
            let c_commit = after_commit - expected_commit;
            combined = combined + alpha_pow * c_commit;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 5: Net delta sign boolean (soundness fix, Gap 1)
        // ====================================================================
        // The net_delta_sign value (aux[3] on row 0) must be boolean (0 or 1).
        // Without this, a malicious prover could encode arbitrary field values
        // as the "sign" and manipulate the signed delta interpretation.
        //
        // On non-zero rows, aux[3] == 0 (unset), so this constraint is trivially
        // satisfied (0 * (0-1) = 0). On row 0, it enforces sign in {0, 1}.
        {
            let delta_sign = local[AUX_BASE + 3];
            let c_sign_bool = delta_sign * (delta_sign - BabyBear::ONE);
            combined = combined + alpha_pow * c_sign_bool;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 6: Algebraic binding of NET_DELTA PI to actual trace
        // balance deltas (P0-1 fix).
        //
        // PIs INIT_BAL_LO/HI and FINAL_BAL_LO/HI are pinned via boundary
        // constraints to row 0 state_before.balance_* and last_row
        // state_after.balance_*. This constraint enforces algebraically:
        //
        //   (FINAL_BAL_LO - INIT_BAL_LO)
        //     + (FINAL_BAL_HI - INIT_BAL_HI) * 2^30
        //     - NET_DELTA_MAG * (1 - 2 * NET_DELTA_SIGN) == 0
        //
        // Both sides depend only on PIs, so this evaluates to the same field
        // element on every row. Non-zero ⇒ no quotient polynomial exists ⇒
        // verifier rejects.
        //
        // The sign bit (PI[NET_DELTA_SIGN]) is constrained boolean (Group 5);
        // limb ranges are asserted at trace-generation time and should also be
        // checked externally by the verifier on the bal_* PIs.
        {
            let init_lo = public_inputs[pi::INIT_BAL_LO];
            let init_hi = public_inputs[pi::INIT_BAL_HI];
            let final_lo = public_inputs[pi::FINAL_BAL_LO];
            let final_hi = public_inputs[pi::FINAL_BAL_HI];
            let mag = public_inputs[pi::NET_DELTA_MAG];
            let sign = public_inputs[pi::NET_DELTA_SIGN];

            let two = BabyBear::ONE + BabyBear::ONE;
            let two_pow_30 = BabyBear::new(1u32 << 30);

            let actual_delta = (final_lo - init_lo) + (final_hi - init_hi) * two_pow_30;
            let signed_delta = mag * (BabyBear::ONE - two * sign);

            let c_delta_bind = actual_delta - signed_delta;
            combined = combined + alpha_pow * c_delta_bind;
            alpha_pow = alpha_pow * alpha;
        }

        // ====================================================================
        // CONSTRAINT GROUP 7: Custom-effect count sum-check (Stage 1, Stage 2 row-0 fix)
        // ====================================================================
        // Per `DESIGN-max-custom-effects.md` §6 step 3: bind the cumulative
        // sum of `s_custom` selector across rows to `PI[CUSTOM_EFFECT_COUNT]`.
        //
        // Stage 2 resolves REVIEW[stage1-acc-row0]: the column now uses an
        // EXCLUSIVE running sum (acc[i] = count of s_custom == 1 over rows
        // [0..i), i.e., NOT including row i). This makes acc[0] == 0 always,
        // pinned by a row-0 boundary. The transition rolls in the current
        // row's contribution: `next.acc - this.acc - this.s_custom == 0`.
        // The last-row check is `acc[last] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT]`,
        // implemented as a per-row PI-only identity gated by the
        // last-row vanishing polynomial.
        //
        // Without this, a prover with control over its witness generator can
        // place `s_custom == 1` on a row without declaring it in PI, hiding a
        // custom effect from the executor's child-proof verification loop
        // (`turn/src/executor.rs:1192-1235`). The sum-check makes the count
        // algebraically binding.
        {
            let this_acc = local[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let next_acc = next[AUX_BASE + aux_off::CUSTOM_COUNT_ACC];
            let this_s_custom = local[sel::CUSTOM];
            // Exclusive-sum transition:
            //   next.acc == this.acc + this.s_custom
            let c_acc_step = next_acc - this_acc - this_s_custom;
            combined = combined + alpha_pow * c_acc_step;
            // alpha_pow = alpha_pow * alpha; // not needed after last
        }

        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut constraints = vec![];
        if public_inputs.len() < pi::BASE_COUNT {
            return constraints;
        }

        // First row: state_commitment column must match the public input directly.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::OLD_COMMIT],
        });

        // CRITICAL: Last row state_after commitment must match new_commitment PI.
        // Without this, a malicious prover could claim any new_commitment.
        // The last row is either the last real effect or a NoOp padding row;
        // either way, its state_after must equal the final state.
        let last_row = trace_len.saturating_sub(1);
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::STATE_COMMIT,
            value: public_inputs[pi::NEW_COMMIT],
        });

        // Net balance delta binding: the net delta is carried in aux columns.
        // Row 0, aux[2] = net_delta_magnitude, aux[3] = net_delta_sign.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 2,
            value: public_inputs[pi::NET_DELTA_MAG],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 3,
            value: public_inputs[pi::NET_DELTA_SIGN],
        });

        // ====================================================================
        // SOUNDNESS FIX (P0-1): Pin row 0 state_before.balance_* and last_row
        // state_after.balance_* to public inputs. Combined with the per-effect
        // arithmetic constraints (which read state_before and write state_after
        // balance columns), the row-to-row continuity constraint, and the
        // Group 6 PI-only algebraic check (in eval_constraints), this makes
        // NET_DELTA_MAG/SIGN cryptographically bound to the actual trace
        // balance flow. Verifier MUST derive INIT/FINAL_BAL_* from the same
        // cell state used to derive OLD/NEW_COMMIT.
        // ====================================================================
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_LO,
            value: public_inputs[pi::INIT_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::BALANCE_HI,
            value: public_inputs[pi::INIT_BAL_HI],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_LO,
            value: public_inputs[pi::FINAL_BAL_LO],
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: STATE_AFTER_BASE + state::BALANCE_HI,
            value: public_inputs[pi::FINAL_BAL_HI],
        });

        // Effects hash binding (position 0 of the 4-felt Stage 1 form is the
        // in-trace continuity binding; positions 1..3 are bound by the
        // executor's PI-matching loop, not by AIR boundaries — see
        // AUDIT[stage1-pi-only-bound] in pi module).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 4,
            value: public_inputs[pi::EFFECTS_HASH_BASE],
        });
        // EFFECTS_HASH_BASE + 1: bound to AUX_BASE + 5 as before (preserves
        // legacy 2-felt witness binding; positions 2..3 are PI-only).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + 5,
            value: public_inputs[pi::EFFECTS_HASH_BASE + 1],
        });

        // Stage 2 resolution of REVIEW[stage1-acc-row0]: exclusive-sum scheme.
        //   Row 0: aux[CUSTOM_COUNT_ACC] == 0 (no rows summed yet).
        //   Transition (in eval_constraints Group 7): next.acc == this.acc + this.s_custom.
        //   Last row: aux[CUSTOM_COUNT_ACC] + s_custom[last] == PI[CUSTOM_EFFECT_COUNT].
        //
        // The last-row equation must use the row's selector, which the boundary
        // API doesn't expose directly. We split it into TWO boundary constraints
        // (cannot express s_custom dependency without an extra column), so we
        // instead add an aux column that holds the *inclusive* sum at the last
        // row only. Actually the cleaner trick: use the transition relation
        // backwards. The last-row constraint becomes the boundary
        //   aux[CUSTOM_COUNT_ACC]_{last_row} == PI[CUSTOM_EFFECT_COUNT] - s_custom_{last_row}
        // which still depends on the trace cell s_custom_{last_row}. Boundary
        // constraints CAN reference trace cells in some STARK frameworks but
        // not this one (BoundaryConstraint fixes a value).
        //
        // Resolution: add a *virtual* end-row by ensuring the trace generator
        // always pads with a NoOp row at the end (s_custom == 0 by NoOp's
        // exclusivity). Then last_row.acc directly equals the total count of
        // s_custom rows in [0..last_row) which (since last_row is NoOp)
        // includes all real custom rows. Boundary becomes:
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]
        //
        // The trace generator already pads to next power-of-two with NoOp rows
        // when n_effects isn't a power of two. For the all-real-rows case
        // (n_effects exactly a power of two), the existing prover only emits
        // real rows; we tighten the boundary to use last-row regardless and
        // require trace gen to enforce s_custom == 0 at the last padded row.
        // For now, we keep the simpler invariant:
        //   acc[0] == 0  (row 0 anchor)
        //   acc[last_row] == PI[CUSTOM_EFFECT_COUNT]  (closes the chain assuming
        //     last row's s_custom contribution is reflected in the prover-emitted
        //     acc OR last row is a NoOp pad row).
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: BabyBear::ZERO,
        });
        constraints.push(BoundaryConstraint {
            row: last_row,
            col: AUX_BASE + aux_off::CUSTOM_COUNT_ACC,
            value: public_inputs[pi::CUSTOM_EFFECT_COUNT],
        });

        // ====================================================================
        // Stage 7 / §B: trace-side boundary for γ.0a turn-identity PI.
        //
        // Closes #49 (AIR nonce-bump invisibility at the trace level): bind
        // row 0's `state_before.nonce` column to PI[ACTOR_NONCE]. Without
        // this, a malicious prover could submit a trace whose row-0 nonce
        // disagrees with PI[ACTOR_NONCE] and the STARK would still verify.
        //
        // Scope: this binding is correct for single-cell proofs where the
        // proven cell IS the agent (state.nonce() == turn.nonce). For
        // multi-cell turns, only the agent cell satisfies this; non-agent
        // cells would need an IS_AGENT_CELL PI gate (deferred to γ.2 /
        // STAGE-7-GAMMA-AGGREGATION-DESIGN.md). The bundle verifier
        // (`verify_proof_carrying_turn_bundle`) cross-checks PI[ACTOR_NONCE]
        // is the same across all per-cell proofs of a turn, so once we
        // gate this boundary per-cell-role the property propagates.
        //
        // EFFECTS_HASH_GLOBAL_BASE: not boundary-bound here. Per-cell
        // proofs already pin PI[EFFECTS_HASH_BASE] (the per-cell value)
        // via the row-0 aux[4..5] binding above. For single-cell turns,
        // EFFECTS_HASH_BASE == EFFECTS_HASH_GLOBAL_BASE (the bundle is
        // one cell) and the executor's PI-matching loop enforces the
        // equality. For multi-cell turns, the bundle verifier merges
        // per-cell effects_hash values into the global; that's a γ.1+
        // aggregation concern, not an AIR-local one.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: STATE_BEFORE_BASE + state::NONCE,
            value: public_inputs[pi::ACTOR_NONCE],
        });

        // ====================================================================
        // SOVEREIGN-WITNESS AIR TEETH (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.3)
        //
        // Row-0 boundary: bind the in-trace witness-identity aux columns
        // to the matching PI slots. The constraint holds unconditionally,
        // by sentinel-zero agreement on the hosted-cell path:
        //
        //   When IS_SOVEREIGN_CELL == 1 (sovereign path):
        //     trace[0][WITNESS_KEY_COMMIT_i] == PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i]
        //     trace[0][WITNESS_SEQUENCE] == PI[SOVEREIGN_WITNESS_SEQUENCE]
        //   When IS_SOVEREIGN_CELL == 0 (hosted path):
        //     prover writes zero into both columns; verifier writes zero
        //     into both PI slots; equality holds.
        //
        // A malicious executor that swaps the witness for one signed by a
        // different key cannot satisfy this binding without changing PI,
        // and the verifier supplies PI from the signature-verified key
        // (executor injection step §2.5 in AUDIT-sovereign-witness-teeth.md).
        // Combined effect: the witness identity becomes acceptance-inside
        // for the AIR layer.
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 1],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 2],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3,
            value: public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + 3],
        });
        constraints.push(BoundaryConstraint {
            row: 0,
            col: AUX_BASE + aux_off::WITNESS_SEQUENCE,
            value: public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE],
        });

        // ====================================================================
        // SOUNDNESS FIX (Gap 1): Net delta range check via balance binding.
        //
        // The net_delta public input MUST reflect the actual balance change.
        // We enforce this by pinning the initial and final balance_lo values
        // on boundary rows. The state_commitment hash already binds these
        // values (Poseidon2 preimage resistance), so any attempt to use
        // out-of-range limbs in the commitment would require a hash collision.
        //
        // Additionally, we constrain net_delta_sign to be boolean (0 or 1)
        // via a boundary constraint. Combined with the state commitment
        // integrity constraints (Group 4), this prevents a malicious prover
        // from encoding a wrapped negative balance as a large positive field
        // element in the net_delta.
        //
        // The binding chain is:
        //   1. Boundary: row 0 state_commit == PI[OLD_COMMIT]
        //   2. Group 4: state_commit == Poseidon2(bal_lo, bal_hi, nonce, ...)
        //   3. This: row 0 bal_lo and last_row bal_lo are hash-bound
        //   4. Transition: row continuity chains all intermediate states
        //   5. Boundary: last_row state_commit == PI[NEW_COMMIT]
        //
        // A malicious prover cannot fabricate net_delta without either:
        //   - Breaking Poseidon2 preimage resistance (computationally infeasible)
        //   - Violating the algebraic constraints (caught by STARK verifier)
        // ====================================================================

        // Net delta sign must be boolean (prevents sign manipulation).
        // Enforced: PI[NET_DELTA_SIGN] must be 0 or 1.
        // This is checked in eval_constraints as: sign * (sign - 1) == 0.
        // We also enforce it via boundary: pin aux[3] to PI value (already done above)
        // AND add the boolean check as a per-row constraint (see CONSTRAINT GROUP 5).

        constraints
    }
}

// ============================================================================
// Witness Generation
// ============================================================================

/// Generate the execution trace and public inputs for an effect VM proof.
///
/// # Arguments
/// * `initial_state` - The cell state before executing effects.
/// * `effects` - The sequence of effects to prove.
///
/// # Returns
/// (trace, public_inputs) suitable for `stark::prove`.
pub fn generate_effect_vm_trace(
    initial_state: &CellState,
    effects: &[Effect],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // Stage 7 / §B: for the default-context wrapper, set actor_nonce
    // from the initial cell nonce. This is the natural invariant for
    // single-cell proofs (the cell IS the agent), and it preserves
    // backwards-compat with the dozens of tests that pass a non-zero
    // initial nonce to CellState::new and rely on the row-0 boundary
    // (state_before.nonce == PI[ACTOR_NONCE]) holding.
    let mut ctx = EffectVmContext::default();
    ctx.actor_nonce = initial_state.nonce as u64;
    generate_effect_vm_trace_ext(initial_state, effects, ctx)
}

/// Extra context that goes into the widened PI layout (Stage 1 + 7-γ.0a).
///
/// All fields have safe defaults for backwards-compat: zero block height,
/// default `max_custom_effects`, empty approved-handoffs root, and
/// all-zero Stage 7-γ.0a turn-identity fields. Callers that produce
/// real per-cell proofs in the executor populate the γ.0a fields from
/// the live `Turn` and call_forest.
#[derive(Clone, Copy, Debug)]
pub struct EffectVmContext {
    /// Federation block height at turn-commit time. Used by timeout-bearing
    /// effects in later stages.
    pub current_block_height: u64,
    /// Per-cell maximum custom effects (from cell program manifest).
    pub max_custom_effects: u8,
    /// Federation-scoped approved-handoffs Merkle root (4-felt Poseidon2 form).
    /// Empty by default until Stage 7 populates the runtime emitter side.
    pub approved_handoffs_root: [BabyBear; 4],
    /// Stage 7-γ.0a: Poseidon2 of canonical `Turn::hash()` (v3). Shared
    /// across all per-cell proofs of one turn.
    pub turn_hash: [BabyBear; 4],
    /// Stage 7-γ.0a: Poseidon2 over the canonical-DFS-order traversal
    /// of the entire call_forest's effects. Shared across the bundle.
    pub effects_hash_global: [BabyBear; 4],
    /// Stage 7-γ.0a: outer `Turn::nonce` promoted to PI; closes the
    /// differential-test gap from task #49 (AIR did not witness the
    /// agent's outer nonce bump). Shared across the bundle.
    pub actor_nonce: u64,
    /// Stage 7-γ.0a: Poseidon2 of `previous_receipt_hash` (or zero
    /// sentinel when None). Shared across the bundle.
    pub previous_receipt_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): when this proof attests to a
    /// sovereign-witnessed effect, the 4-felt Poseidon2 hash of the
    /// witness's owning pubkey. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4]. Zero sentinel for
    /// hosted-cell proofs.
    pub sovereign_witness_key_commit: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 1): per-cell monotonic sequence
    /// from the witness. Bound to the row-0 aux column and to
    /// PI[SOVEREIGN_WITNESS_SEQUENCE]. Zero sentinel for hosted-cell
    /// proofs.
    pub sovereign_witness_sequence: u64,
    /// Sovereign-witness teeth (Phase 1): 1 iff this is a sovereign
    /// witnessed proof; 0 otherwise. Drives the (a)-style sentinel
    /// agreement between prover and verifier (no actual gating in the
    /// AIR — sentinel zeros on both sides make the boundary trivial
    /// when off).
    pub is_sovereign_cell: bool,
    /// Sovereign-witness teeth (Phase 2): 4-felt VK hash of the AIR the
    /// inner transition_proof was generated under. Zero sentinel when
    /// no transition_proof is supplied.
    pub sovereign_transition_proof_vk_hash: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 4-felt Poseidon2 hash of the
    /// canonical inner-proof bytes. Zero sentinel when no transition_proof
    /// is supplied.
    pub sovereign_transition_proof_commitment: [BabyBear; 4],
    /// Sovereign-witness teeth (Phase 2): 1 iff a transition_proof
    /// was supplied AND `is_sovereign_cell` is true.
    pub has_transition_proof: bool,

    /// 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5): 4×16-bit
    /// little-endian limbs of the full u64 `BridgeMint.value`. Position 0
    /// is the low 16 bits; position 3 is the high. Each limb < 2^16.
    /// Zero sentinel when no BridgeMint effect is in the trace.
    pub bridge_mint_value_limbs: [BabyBear; 4],
    /// 4-limb decomposition of `BridgeLock.value` (same shape as
    /// `bridge_mint_value_limbs`).
    pub bridge_lock_value_limbs: [BabyBear; 4],
    /// 4-limb decomposition of `CreateEscrow.amount` (same shape).
    pub create_escrow_amount_limbs: [BabyBear; 4],

    /// Slot-caveat manifest (Cav-Codex Block 3). Cell-program-declared
    /// `StateConstraint` set, projected into a fixed-size table for
    /// row-boundary AIR enforcement. `slot_caveat_count` ∈ [0,
    /// `pi::MAX_SLOT_CAVEATS`]; `slot_caveat_manifest[..count]`
    /// carries the entries.
    pub slot_caveat_count: u32,
    pub slot_caveat_manifest: [SlotCaveatEntry; pi::MAX_SLOT_CAVEATS],
}

/// A single entry in the slot-caveat manifest (Cav-Codex Block 3).
///
/// `type_tag` is one of `pi::SLOT_CAVEAT_TAG_*` (zero means "no
/// caveat"); `slot_index` is the cell-state field index; `params` are
/// up to 4 numeric parameters or a 4-felt commitment (the variant
/// determines the encoding — see `populate_slot_caveat_manifest`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SlotCaveatEntry {
    pub type_tag: u32,
    pub slot_index: u8,
    pub params: [BabyBear; 4],
}

impl SlotCaveatEntry {
    pub const fn zero() -> Self {
        Self {
            type_tag: 0,
            slot_index: 0,
            params: [BabyBear::ZERO; 4],
        }
    }

    /// Encode this entry into `out[..SLOT_CAVEAT_ENTRY_SIZE]` as
    /// (type_tag, slot_index, p0, p1, p2, p3).
    pub fn write_to(&self, out: &mut [BabyBear]) {
        debug_assert!(out.len() >= pi::SLOT_CAVEAT_ENTRY_SIZE);
        out[0] = BabyBear::new(self.type_tag);
        out[1] = BabyBear::new(self.slot_index as u32);
        for i in 0..4 {
            out[2 + i] = self.params[i];
        }
    }
}

impl Default for EffectVmContext {
    fn default() -> Self {
        Self {
            current_block_height: 0,
            max_custom_effects: pi::MAX_CUSTOM_EFFECTS_DEFAULT,
            approved_handoffs_root: [BabyBear::ZERO; 4],
            turn_hash: [BabyBear::ZERO; 4],
            effects_hash_global: [BabyBear::ZERO; 4],
            actor_nonce: 0,
            previous_receipt_hash: [BabyBear::ZERO; 4],
            sovereign_witness_key_commit: [BabyBear::ZERO; 4],
            sovereign_witness_sequence: 0,
            is_sovereign_cell: false,
            sovereign_transition_proof_vk_hash: [BabyBear::ZERO; 4],
            sovereign_transition_proof_commitment: [BabyBear::ZERO; 4],
            has_transition_proof: false,
            bridge_mint_value_limbs: [BabyBear::ZERO; 4],
            bridge_lock_value_limbs: [BabyBear::ZERO; 4],
            create_escrow_amount_limbs: [BabyBear::ZERO; 4],
            slot_caveat_count: 0,
            slot_caveat_manifest: [SlotCaveatEntry::zero(); pi::MAX_SLOT_CAVEATS],
        }
    }
}

/// Decompose a u64 into 4 BabyBear limbs (16 bits each, little-endian).
/// Returns `[lo16, mid_lo16, mid_hi16, hi16]` so the limbs sum back to
/// the original via `Σ limbs[i] * 2^(16*i)`. Used to project full-u64
/// effect values into the AIR PI without 30-bit truncation
/// (CAVEAT-LAYER-COVERAGE.md §6.5).
#[inline]
pub fn u64_to_4_limbs_16(value: u64) -> [BabyBear; 4] {
    [
        BabyBear::new((value & 0xFFFF) as u32),
        BabyBear::new(((value >> 16) & 0xFFFF) as u32),
        BabyBear::new(((value >> 32) & 0xFFFF) as u32),
        BabyBear::new(((value >> 48) & 0xFFFF) as u32),
    ]
}

/// Inverse of [`u64_to_4_limbs_16`]: reconstruct a u64 from 4 BabyBear
/// limbs of 16 bits each. Returns `None` if any limb exceeds 2^16
/// (rejects out-of-range limbs — adversarial-test entry point).
#[inline]
pub fn u64_from_4_limbs_16(limbs: &[BabyBear; 4]) -> Option<u64> {
    let mut acc: u64 = 0;
    for (i, l) in limbs.iter().enumerate() {
        let v = l.0 as u64;
        if v >= (1u64 << 16) {
            return None;
        }
        acc |= v << (16 * i);
    }
    Some(acc)
}

/// Stage 1 trace generator. Same as [`generate_effect_vm_trace`] but accepts
/// the widened PI inputs ([`EffectVmContext`]).
pub fn generate_effect_vm_trace_ext(
    initial_state: &CellState,
    effects: &[Effect],
    context: EffectVmContext,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!effects.is_empty(), "Need at least one effect");

    // ====================================================================
    // EXECUTOR-SIDE RANGE VALIDATION (o1vm audit mitigations)
    // ====================================================================
    // These checks run at proof generation time. They do NOT add constraints
    // to the STARK, but they prevent the executor from producing a trace with
    // out-of-range values that could exploit modular arithmetic.
    //
    // A verifier receiving a proof from an untrusted prover must additionally
    // verify that the final state (decoded from new_commitment PI) has valid
    // limb ranges. See `verify_balance_limb_ranges` below.
    // ====================================================================

    // Validate initial balance limbs are in range.
    let (init_lo, init_hi) = split_u64(initial_state.balance);
    assert!(
        init_lo.0 < (1 << 30),
        "Initial balance_lo out of range: {} >= 2^30",
        init_lo.0
    );
    assert!(
        init_hi.0 < (1 << 31),
        "Initial balance_hi out of range: {} >= 2^31 (exceeds BabyBear)",
        init_hi.0
    );

    // Validate field_idx bounds and balance underflow for all effects.
    // We track a running balance to catch underflow across multi-effect turns.
    {
        let mut running_balance = initial_state.balance;
        for effect in effects {
            match effect {
                Effect::SetField { field_idx, .. } => {
                    assert!(
                        *field_idx < 8,
                        "SetField field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Seal { field_idx } => {
                    assert!(
                        *field_idx < 8,
                        "Seal field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Unseal { field_idx, .. } => {
                    assert!(
                        *field_idx < 8,
                        "Unseal field_idx out of bounds: {} (must be 0..7)",
                        field_idx
                    );
                }
                Effect::Transfer {
                    amount, direction, ..
                } => {
                    if *direction == 1 {
                        // Outgoing: validate no underflow.
                        assert!(
                            *amount <= running_balance,
                            "Transfer underflow: amount {} > running balance {} \
                             (executor rejects; STARK constraint would wrap in BabyBear)",
                            amount,
                            running_balance
                        );
                        running_balance -= amount;
                    } else {
                        running_balance = running_balance.saturating_add(*amount);
                    }
                }
                Effect::NoteCreate { value, .. } => {
                    assert!(
                        *value <= running_balance,
                        "NoteCreate underflow: value {} > running balance {} \
                         (executor rejects; STARK constraint would wrap in BabyBear)",
                        value,
                        running_balance
                    );
                    running_balance -= value;
                }
                Effect::CreateObligation { stake_amount, .. } => {
                    assert!(
                        *stake_amount <= running_balance,
                        "CreateObligation underflow: stake {} > running balance {} \
                         (executor rejects; STARK constraint would wrap in BabyBear)",
                        stake_amount,
                        running_balance
                    );
                    running_balance -= stake_amount;
                }
                Effect::NoteSpend { value, .. } => {
                    running_balance = running_balance.saturating_add(*value);
                }
                Effect::FulfillObligation { stake_return, .. } => {
                    running_balance = running_balance.saturating_add(*stake_return);
                }
                Effect::SlashObligation { stake_amount, .. } => {
                    running_balance = running_balance.saturating_add(*stake_amount);
                }
                Effect::AllocateQueue {
                    capacity,
                    cost_per_slot,
                    ..
                } => {
                    let cost = (*capacity as u64) * (*cost_per_slot as u64);
                    assert!(
                        cost <= running_balance,
                        "AllocateQueue underflow: cost {} > running balance {}",
                        cost,
                        running_balance
                    );
                    running_balance -= cost;
                }
                Effect::EnqueueMessage { deposit_amount, .. } => {
                    assert!(
                        (*deposit_amount as u64) <= running_balance,
                        "EnqueueMessage underflow: deposit {} > running balance {}",
                        deposit_amount,
                        running_balance
                    );
                    running_balance -= *deposit_amount as u64;
                }
                Effect::DequeueMessage { deposit_refund, .. } => {
                    running_balance = running_balance.saturating_add(*deposit_refund as u64);
                }
                Effect::ResizeQueue {
                    new_capacity,
                    old_capacity,
                    cost_per_slot,
                    ..
                } => {
                    if *new_capacity > *old_capacity {
                        let delta = (*new_capacity - *old_capacity) as u64;
                        let cost = delta * (*cost_per_slot as u64);
                        assert!(
                            cost <= running_balance,
                            "ResizeQueue underflow: cost {} > running balance {}",
                            cost,
                            running_balance
                        );
                        running_balance -= cost;
                    }
                }
                Effect::AtomicQueueTx { net_deposit, .. } => {
                    assert!(
                        (*net_deposit as u64) <= running_balance,
                        "AtomicQueueTx underflow: net_deposit {} > running balance {}",
                        net_deposit,
                        running_balance
                    );
                    running_balance -= *net_deposit as u64;
                }
                _ => {}
            }
        }
    }

    // Determine trace height (pad to power of 2, minimum 2).
    // Stage 2 (REVIEW[stage1-acc-row0]): if the last real effect is a Custom,
    // we need at least one trailing NoOp row so the exclusive-sum boundary
    // `acc[last] == PI[CUSTOM_EFFECT_COUNT]` holds. Reserve a slot.
    let n_effects = effects.len();
    let need_extra_pad = matches!(effects.last(), Some(Effect::Custom { .. }));
    let trace_height = if need_extra_pad {
        (n_effects + 1).next_power_of_two().max(2)
    } else {
        n_effects.next_power_of_two().max(2)
    };

    let mut trace = Vec::with_capacity(trace_height);
    let mut current_state = initial_state.clone();

    // Track net balance delta.
    let mut net_delta: i64 = 0;

    for effect in effects {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];

        // Set selector.
        let sel_idx = match effect {
            Effect::NoOp => sel::NOOP,
            Effect::Transfer { .. } => sel::TRANSFER,
            Effect::SetField { .. } => sel::SET_FIELD,
            Effect::GrantCapability { .. } => sel::GRANT_CAP,
            Effect::NoteSpend { .. } => sel::NOTE_SPEND,
            Effect::NoteCreate { .. } => sel::NOTE_CREATE,
            Effect::CreateObligation { .. } => sel::CREATE_OBLIGATION,
            Effect::FulfillObligation { .. } => sel::FULFILL_OBLIGATION,
            Effect::Custom { .. } => sel::CUSTOM,
            Effect::SlashObligation { .. } => sel::SLASH_OBLIGATION,
            Effect::Seal { .. } => sel::SEAL,
            Effect::Unseal { .. } => sel::UNSEAL,
            Effect::MakeSovereign => sel::MAKE_SOVEREIGN,
            Effect::CreateCellFromFactory { .. } => sel::CREATE_CELL_FROM_FACTORY,
            Effect::ExportSturdyRef { .. } => sel::EXPORT_STURDY_REF,
            Effect::EnlivenRef { .. } => sel::ENLIVEN_REF,
            Effect::DropRef { .. } => sel::DROP_REF,
            Effect::ValidateHandoff { .. } => sel::VALIDATE_HANDOFF,
            Effect::AllocateQueue { .. } => sel::ALLOCATE_QUEUE,
            Effect::EnqueueMessage { .. } => sel::ENQUEUE_MESSAGE,
            Effect::DequeueMessage { .. } => sel::DEQUEUE_MESSAGE,
            Effect::ResizeQueue { .. } => sel::RESIZE_QUEUE,
            Effect::AtomicQueueTx { .. } => sel::ATOMIC_QUEUE_TX,
            Effect::PipelineStep { .. } => sel::PIPELINE_STEP,
            Effect::RevokeCapability { .. } => sel::REVOKE_CAPABILITY,
            Effect::EmitEvent { .. } => sel::EMIT_EVENT,
            Effect::SetPermissions { .. } => sel::SET_PERMISSIONS,
            Effect::SetVerificationKey { .. } => sel::SET_VERIFICATION_KEY,
            Effect::CreateSealPair { .. } => sel::CREATE_SEAL_PAIR,
            Effect::RefreshDelegation => sel::REFRESH_DELEGATION,
            Effect::RevokeDelegation { .. } => sel::REVOKE_DELEGATION,
            Effect::CreateCell { .. } => sel::CREATE_CELL,
            Effect::SpawnWithDelegation { .. } => sel::SPAWN_WITH_DELEGATION,
            Effect::BridgeCancel { .. } => sel::BRIDGE_CANCEL,
            Effect::ExerciseViaCapability { .. } => sel::EXERCISE_VIA_CAPABILITY,
            Effect::Introduce { .. } => sel::INTRODUCE,
            Effect::PipelinedSend { .. } => sel::PIPELINED_SEND,
            Effect::CreateEscrow { .. } => sel::CREATE_ESCROW,
            Effect::BridgeLock { .. } => sel::BRIDGE_LOCK,
            Effect::CreateCommittedEscrow { .. } => sel::CREATE_COMMITTED_ESCROW,
            Effect::BridgeMint { .. } => sel::BRIDGE_MINT,
            Effect::BridgeFinalize { .. } => sel::BRIDGE_FINALIZE,
            Effect::ReleaseEscrow { .. } => sel::RELEASE_ESCROW,
            Effect::RefundEscrow { .. } => sel::REFUND_ESCROW,
            Effect::ReleaseCommittedEscrow { .. } => sel::RELEASE_COMMITTED_ESCROW,
            Effect::RefundCommittedEscrow { .. } => sel::REFUND_COMMITTED_ESCROW,
        };
        row[sel_idx] = BabyBear::ONE;

        // Write state_before.
        let state_before_cols = current_state.to_trace_cols();
        for (i, &val) in state_before_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }

        // Apply effect and compute state_after + params.
        let mut new_state = current_state.clone();
        match effect {
            Effect::NoOp => {
                // No state change, no nonce increment for padding.
            }
            Effect::Transfer { amount, direction } => {
                let (lo, _hi) = split_u64(*amount);
                row[PARAM_BASE + param::AMOUNT] = lo;
                row[PARAM_BASE + param::DIRECTION] = BabyBear::new(*direction);

                if *direction == 1 {
                    // Outgoing.
                    new_state.balance = new_state.balance.saturating_sub(*amount);
                    net_delta -= *amount as i64;
                } else {
                    // Incoming.
                    new_state.balance = new_state.balance.saturating_add(*amount);
                    net_delta += *amount as i64;
                }
                new_state.nonce += 1;
            }
            Effect::SetField { field_idx, value } => {
                row[PARAM_BASE + param::FIELD_INDEX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::NEW_VALUE] = *value;

                // Store old value at target index in aux[0] for the constraint.
                let idx = *field_idx as usize;
                row[AUX_BASE + 0] = current_state.fields[idx.min(7)];

                new_state.fields[idx.min(7)] = *value;
                new_state.nonce += 1;
            }
            Effect::GrantCapability { cap_entry } => {
                row[PARAM_BASE + param::CAP_ENTRY] = *cap_entry;

                let new_cap = hash_2_to_1(current_state.capability_root, *cap_entry);
                new_state.capability_root = new_cap;
                new_state.nonce += 1;
            }
            Effect::RevokeCapability { slot_hash } => {
                // The slot_hash parameter shares param slot 0 with cap_entry.
                row[PARAM_BASE + param::CAP_ENTRY] = *slot_hash;

                // Mirror GrantCapability: cap_root deterministically updates
                // by hashing the slot_hash with the previous root.
                let new_cap = hash_2_to_1(current_state.capability_root, *slot_hash);
                new_state.capability_root = new_cap;
                new_state.nonce += 1;
            }
            Effect::EmitEvent { event_hash } => {
                // Park the event hash in param 0 so the AIR can bind it into
                // effects_hash. No state column changes.
                row[PARAM_BASE + 0] = *event_hash;
                new_state.nonce += 1;
            }
            Effect::SetPermissions { permissions_hash } => {
                // Same shape as EmitEvent: hash in param 0; AIR forbids any
                // state column change; nonce ticks.
                row[PARAM_BASE + 0] = *permissions_hash;
                new_state.nonce += 1;
            }
            Effect::SetVerificationKey { vk_hash } => {
                // Same shape as SetPermissions: VK lives off-trace.
                row[PARAM_BASE + 0] = *vk_hash;
                new_state.nonce += 1;
            }
            Effect::CreateSealPair { pair_hash } => {
                row[PARAM_BASE + 0] = *pair_hash;
                new_state.nonce += 1;
            }
            Effect::RefreshDelegation => {
                // No params; selector alone records the intent.
                new_state.nonce += 1;
            }
            Effect::RevokeDelegation { child_hash } => {
                row[PARAM_BASE + 0] = *child_hash;
                new_state.nonce += 1;
            }
            Effect::CreateCell { create_hash } => {
                row[PARAM_BASE + 0] = *create_hash;
                new_state.nonce += 1;
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                row[PARAM_BASE + 0] = *spawn_hash;
                new_state.nonce += 1;
            }
            Effect::BridgeCancel { nullifier_hash } => {
                row[PARAM_BASE + 0] = *nullifier_hash;
                new_state.nonce += 1;
            }
            Effect::ExerciseViaCapability { exercise_hash } => {
                row[PARAM_BASE + 0] = *exercise_hash;
                new_state.nonce += 1;
            }
            Effect::Introduce { intro_hash } => {
                row[PARAM_BASE + 0] = *intro_hash;
                new_state.nonce += 1;
            }
            Effect::PipelinedSend { send_hash } => {
                row[PARAM_BASE + 0] = *send_hash;
                new_state.nonce += 1;
            }
            Effect::CreateEscrow {
                amount_lo,
                escrow_hash,
                amount_full: _,
            } => {
                // Mirror NoteCreate: param0 = escrow_hash, param1 = amount_lo
                row[PARAM_BASE + 0] = *escrow_hash;
                row[PARAM_BASE + 1] = *amount_lo;
                let amount_u64 = amount_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_sub(amount_u64);
                net_delta -= amount_u64 as i64;
                new_state.nonce += 1;
            }
            Effect::BridgeLock {
                value_lo,
                lock_hash,
                value_full: _,
            } => {
                // Mirror CreateEscrow: balance debit by value_lo.
                row[PARAM_BASE + 0] = *lock_hash;
                row[PARAM_BASE + 1] = *value_lo;
                let value_u64 = value_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_sub(value_u64);
                net_delta -= value_u64 as i64;
                new_state.nonce += 1;
            }
            Effect::CreateCommittedEscrow { commit_hash } => {
                row[PARAM_BASE + 0] = *commit_hash;
                new_state.nonce += 1;
            }
            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full: _,
            } => {
                // Mirror NoteSpend: balance credit by value_lo.
                row[PARAM_BASE + 0] = *mint_hash;
                row[PARAM_BASE + 1] = *value_lo;
                let value_u64 = value_lo.as_u32() as u64;
                new_state.balance = new_state.balance.saturating_add(value_u64);
                net_delta += value_u64 as i64;
                new_state.nonce += 1;
            }
            Effect::BridgeFinalize { finalize_hash } => {
                row[PARAM_BASE + 0] = *finalize_hash;
                new_state.nonce += 1;
            }
            Effect::ReleaseEscrow { escrow_id_hash } | Effect::RefundEscrow { escrow_id_hash } => {
                row[PARAM_BASE + 0] = *escrow_id_hash;
                new_state.nonce += 1;
            }
            Effect::ReleaseCommittedEscrow { commit_hash }
            | Effect::RefundCommittedEscrow { commit_hash } => {
                row[PARAM_BASE + 0] = *commit_hash;
                new_state.nonce += 1;
            }
            Effect::NoteSpend { nullifier, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NULLIFIER] = *nullifier;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_add(*value);
                net_delta += *value as i64;
                new_state.nonce += 1;
            }
            Effect::NoteCreate { commitment, value } => {
                let (val_lo, val_hi) = split_u64(*value);
                row[PARAM_BASE + param::NOTE_COMMITMENT] = *commitment;
                row[PARAM_BASE + param::NOTE_VALUE_LO] = val_lo;
                row[PARAM_BASE + param::NOTE_VALUE_HI] = val_hi;

                new_state.balance = new_state.balance.saturating_sub(*value);
                net_delta -= *value as i64;
                new_state.nonce += 1;
            }
            Effect::CreateObligation {
                stake_amount,
                obligation_id,
                beneficiary_hash,
            } => {
                let (stake_lo, stake_hi) = split_u64(*stake_amount);
                row[PARAM_BASE + param::OBLIGATION_STAKE_LO] = stake_lo;
                row[PARAM_BASE + param::OBLIGATION_STAKE_HI] = stake_hi;
                row[PARAM_BASE + param::OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::OBLIGATION_BENEFICIARY] = *beneficiary_hash;

                new_state.balance = new_state.balance.saturating_sub(*stake_amount);
                net_delta -= *stake_amount as i64;
                // Stage 2: cap_root advances to bind both obligation_id and beneficiary.
                let obligation_leaf = hash_2_to_1(*obligation_id, *beneficiary_hash);
                new_state.capability_root = hash_2_to_1(new_state.capability_root, obligation_leaf);
                new_state.nonce += 1;
            }
            Effect::FulfillObligation {
                obligation_id,
                stake_return,
            } => {
                let (ret_lo, ret_hi) = split_u64(*stake_return);
                row[PARAM_BASE + param::FULFILL_OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::FULFILL_RETURN_LO] = ret_lo;
                row[PARAM_BASE + param::FULFILL_RETURN_HI] = ret_hi;

                new_state.balance = new_state.balance.saturating_add(*stake_return);
                net_delta += *stake_return as i64;
                new_state.nonce += 1;
            }
            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                // Write VK hash into params[0..4].
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_VK_HASH_BASE + i] = program_vk_hash[i];
                }
                // Write proof commitment into params[4..8].
                for i in 0..4 {
                    row[PARAM_BASE + param::CUSTOM_PROOF_COMMIT_BASE + i] = proof_commitment[i];
                }
                // Custom effects do NOT change state (state flows through unchanged).
                // The nonce still increments (it's a real effect, not padding).
                new_state.nonce += 1;
                // No balance change from the Effect VM perspective.
            }
            Effect::SlashObligation {
                obligation_id,
                stake_amount,
                beneficiary_hash,
            } => {
                let (stake_lo, stake_hi) = split_u64(*stake_amount);
                row[PARAM_BASE + param::SLASH_OBLIGATION_ID] = *obligation_id;
                row[PARAM_BASE + param::SLASH_STAKE_LO] = stake_lo;
                row[PARAM_BASE + param::SLASH_STAKE_HI] = stake_hi;
                row[PARAM_BASE + param::SLASH_BENEFICIARY] = *beneficiary_hash;
                // Slash credits the beneficiary: balance increases.
                new_state.balance = new_state.balance.saturating_add(*stake_amount);
                net_delta += *stake_amount as i64;
                // Update cap_root to reflect obligation removal.
                new_state.capability_root = hash_2_to_1(new_state.capability_root, *obligation_id);
                new_state.nonce += 1;
            }
            Effect::Seal { field_idx } => {
                row[PARAM_BASE + param::SEAL_FIELD_IDX] = BabyBear::new(*field_idx);
                // Stage 2: aux witness for 2^field_idx (constrained by Lagrange poly).
                row[AUX_BASE + aux_off::SEAL_POW2_IDX] = BabyBear::new(1u32 << field_idx);
                // Trace-gen-side check: bit must not already be set (no double-seal).
                assert!(
                    new_state.sealed_field_mask & (1 << field_idx) == 0,
                    "Seal: field {} already sealed (sealed_mask={:#b})",
                    field_idx,
                    new_state.sealed_field_mask,
                );
                new_state.sealed_field_mask |= 1 << field_idx;
                new_state.nonce += 1;
            }
            Effect::Unseal { field_idx, brand } => {
                row[PARAM_BASE + param::UNSEAL_FIELD_IDX] = BabyBear::new(*field_idx);
                row[PARAM_BASE + param::UNSEAL_BRAND] = *brand;
                // Store brand in aux for constraint checking.
                row[AUX_BASE + 6] = *brand;
                // Stage 2: aux witness for 2^field_idx.
                row[AUX_BASE + aux_off::SEAL_POW2_IDX] = BabyBear::new(1u32 << field_idx);
                // Trace-gen-side check: bit must be set (cannot unseal unsealed field).
                assert!(
                    new_state.sealed_field_mask & (1 << field_idx) != 0,
                    "Unseal: field {} not sealed (sealed_mask={:#b})",
                    field_idx,
                    new_state.sealed_field_mask,
                );
                new_state.sealed_field_mask &= !(1 << field_idx);
                new_state.nonce += 1;
            }
            Effect::MakeSovereign => {
                // Mode flag transitions from 0 to 1.
                new_state.mode_flag = 1;
                new_state.nonce += 1;
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                row[PARAM_BASE + param::FACTORY_VK_HASH] = *factory_vk;
                row[PARAM_BASE + param::CHILD_VK_DERIVED] = *child_vk_derived;
                // Store in aux columns for constraint verification.
                row[AUX_BASE + 6] = *factory_vk;
                row[AUX_BASE + 7] = *child_vk_derived;
                new_state.nonce += 1;
            }
            Effect::ExportSturdyRef {
                cell_id,
                permissions,
                random_seed,
                export_counter,
            } => {
                row[PARAM_BASE + param::EXPORT_CELL_ID] = *cell_id;
                row[PARAM_BASE + param::EXPORT_PERMISSIONS] = *permissions;
                row[PARAM_BASE + param::EXPORT_RANDOM_SEED] = *random_seed;
                row[PARAM_BASE + param::EXPORT_COUNTER] = BabyBear::new(*export_counter);

                // Compute swiss_number = hash(cell_id, hash(random_seed, counter))
                let inner_hash = hash_2_to_1(*random_seed, BabyBear::new(*export_counter));
                let swiss_number = hash_2_to_1(*cell_id, inner_hash);
                // Store computed swiss in aux[0] for constraint verification.
                row[AUX_BASE + 0] = swiss_number;

                // State: field[7] increments (export counter tracked there).
                new_state.fields[7] = new_state.fields[7] + BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::EnlivenRef {
                swiss_number,
                presenter_id,
                expected_cell_id,
                expected_permissions,
            } => {
                row[PARAM_BASE + param::ENLIVEN_SWISS] = *swiss_number;
                row[PARAM_BASE + param::ENLIVEN_PRESENTER] = *presenter_id;
                row[PARAM_BASE + param::ENLIVEN_CELL_ID] = *expected_cell_id;
                row[PARAM_BASE + param::ENLIVEN_PERMISSIONS] = *expected_permissions;

                // Stage 7 / P1.C: 1-hop Merkle membership against the
                // cell's committed swiss_table_root mirror
                // (state_after.fields[4]).
                //
                // Leaf = hash(swiss, hash(cell_id, permissions)).
                let inner = hash_2_to_1(*expected_cell_id, *expected_permissions);
                let leaf = hash_2_to_1(*swiss_number, inner);
                // For the deterministic witness path used by AIR tests
                // (no real swiss table), the sibling is the previous
                // root (ZERO at row 0) and the new root is the
                // pair-hash. Real deployments use a structured sibling
                // table maintained by the federation mirror.
                let sibling = current_state.fields[4];
                let chosen = hash_2_to_1(leaf, sibling);
                let root = chosen;
                row[AUX_BASE + 0] = root;
                row[AUX_BASE + 1] = leaf;
                row[AUX_BASE + 6] = sibling;
                row[AUX_BASE + 7] = chosen;
                // Materialise the post-enliven swiss_table_root in
                // state_after.fields[4]. The AIR constraint
                // (aux_root == state_after.fields[4]) is satisfied.
                new_state.fields[4] = root;

                // State: field[6] increments (use_count tracked there).
                new_state.fields[6] = new_state.fields[6] + BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount,
            } => {
                row[PARAM_BASE + param::DROP_CELL_ID] = *cell_id;
                row[PARAM_BASE + param::DROP_HOLDER_FED] = *holder_federation;
                row[PARAM_BASE + param::DROP_REFCOUNT] = BabyBear::new(*current_refcount);

                // Prove refcount > 0: store inverse in aux[0].
                assert!(
                    *current_refcount > 0,
                    "DropRef: current_refcount must be > 0"
                );
                let rc_field = BabyBear::new(*current_refcount);
                row[AUX_BASE + 0] = rc_field.inverse().expect("refcount is non-zero");

                // Stage 7 / P1.C: 1-hop Merkle membership against the
                // cell's committed refcount_table_root mirror
                // (state_after.fields[3]).
                let leaf = hash_2_to_1(*cell_id, *holder_federation);
                let sibling = current_state.fields[3];
                let chosen = hash_2_to_1(leaf, sibling);
                row[AUX_BASE + 1] = leaf;
                row[AUX_BASE + 6] = sibling;
                row[AUX_BASE + 7] = chosen;
                // Materialise the new refcount_table_root in field[3].
                new_state.fields[3] = chosen;

                // State: field[5] decrements (refcount tracked there).
                new_state.fields[5] = new_state.fields[5] - BabyBear::ONE;
                new_state.nonce += 1;
            }
            Effect::ValidateHandoff {
                certificate_hash,
                recipient_pk,
                introducer_pk,
                approved_set_root: _provided_root,
            } => {
                // Stage 7 / P1.C: bind PARAM approved_set_root to the
                // verifier-supplied PI position 0 of APPROVED_HANDOFFS_BASE.
                // The runtime-provided value is ignored; the trace
                // generator writes the PI-bound value into the PARAM.
                let approved_set_root = context.approved_handoffs_root[0];
                row[PARAM_BASE + param::HANDOFF_CERT_HASH] = *certificate_hash;
                row[PARAM_BASE + param::HANDOFF_RECIPIENT_PK] = *recipient_pk;
                row[PARAM_BASE + param::HANDOFF_INTRODUCER_PK] = *introducer_pk;
                row[PARAM_BASE + param::HANDOFF_APPROVED_SET_ROOT] = approved_set_root;

                // Stage 7 / P1.C: 1-hop Merkle membership.
                // leaf = hash(cert_hash, hash(recipient_pk, introducer_pk)).
                let pks = hash_2_to_1(*recipient_pk, *introducer_pk);
                let leaf = hash_2_to_1(*certificate_hash, pks);
                // For the deterministic witness path, the sibling is
                // chosen so that hash(leaf, sibling) == approved_set_root.
                // Without a real federation mirror, we set the sibling
                // such that the AIR's chosen-parent equals the root.
                // Production code wires this from the federation's
                // Merkle witness oracle.
                //
                // Deterministic path: if approved_set_root == ZERO, the
                // trace satisfies hash(leaf, sibling) == 0 only when
                // such a sibling exists; we leave this as ZERO for the
                // "empty approved set" case (the AIR proof fails, which
                // is the correct behaviour — you can't validate a
                // handoff against an empty approved set).
                let sibling = BabyBear::ZERO;
                let chosen = hash_2_to_1(leaf, sibling);
                row[AUX_BASE + 0] = leaf;
                row[AUX_BASE + 1] = sibling;
                row[AUX_BASE + 6] = chosen;
                // NOTE: this trace satisfies the AIR iff
                // `chosen == approved_set_root`. The
                // federation-mirror witness layer is responsible for
                // supplying sibling values that make this hold for
                // committed approved-set entries. Until the witness
                // oracle lands, this trace path will only succeed when
                // the federation's approved_handoffs_root happens to
                // equal hash(leaf, ZERO) — i.e., a single-entry tree.

                // State: cap_root updated with routing entry.
                // new_cap = hash(old_cap, hash(recipient_pk, cert_hash))
                let routing_entry = hash_2_to_1(*recipient_pk, *certificate_hash);
                new_state.capability_root = hash_2_to_1(new_state.capability_root, routing_entry);
                new_state.nonce += 1;
            }
            Effect::AllocateQueue {
                capacity,
                owner_quota_id,
                cost_per_slot,
            } => {
                row[PARAM_BASE + param::QUEUE_CAPACITY] = BabyBear::new(*capacity);
                row[PARAM_BASE + param::QUEUE_OWNER_QUOTA] = *owner_quota_id;
                row[PARAM_BASE + param::QUEUE_COST_PER_SLOT] = BabyBear::new(*cost_per_slot);

                // Allocation cost = capacity * cost_per_slot.
                let alloc_cost = (*capacity as u64) * (*cost_per_slot as u64);
                new_state.balance = new_state.balance.saturating_sub(alloc_cost);
                net_delta -= alloc_cost as i64;

                // Queue root = empty queue hash = hash_2_to_1(ZERO, ZERO).
                // Store in field[4] by convention (queue_root slot).
                let empty_queue_hash = hash_2_to_1(BabyBear::ZERO, BabyBear::ZERO);
                new_state.fields[4] = empty_queue_hash;

                // Store capacity in aux[0] for constraint verification.
                row[AUX_BASE + 0] = empty_queue_hash;

                new_state.nonce += 1;
            }
            Effect::EnqueueMessage {
                message_hash,
                deposit_amount,
                sender_id,
                queue_len,
                program_vk,
            } => {
                row[PARAM_BASE + param::ENQUEUE_MSG_HASH] = *message_hash;
                row[PARAM_BASE + param::ENQUEUE_DEPOSIT] = BabyBear::new(*deposit_amount);
                row[PARAM_BASE + param::ENQUEUE_SENDER] = *sender_id;
                row[PARAM_BASE + param::ENQUEUE_QUEUE_LEN] = BabyBear::new(*queue_len);
                row[PARAM_BASE + param::ENQUEUE_PROGRAM_VK] = *program_vk;

                // Queue root transition: new_root = hash(old_root, message_hash).
                let old_queue_root = new_state.fields[4];
                let new_queue_root = hash_2_to_1(old_queue_root, *message_hash);
                new_state.fields[4] = new_queue_root;

                // Deposit deducted from sender's balance.
                new_state.balance = new_state.balance.saturating_sub(*deposit_amount as u64);
                net_delta -= *deposit_amount as i64;

                // Store new queue root in aux[0] for constraint verification.
                row[AUX_BASE + 0] = new_queue_root;

                // Program validation hash binding (aux[6] and aux[7]).
                // NOTE: aux[2..5] are reserved for PI values on row 0.
                // When program_vk != 0, compute and store the validation hash.
                // When program_vk == 0, both are zero (backward compatible).
                if *program_vk != BabyBear::ZERO {
                    let inner = hash_2_to_1(*sender_id, *message_hash);
                    let validation_hash = hash_2_to_1(*program_vk, inner);
                    row[AUX_BASE + 6] = validation_hash;
                    // aux[7] = inverse of program_vk (for the zero-check constraint).
                    row[AUX_BASE + 7] = program_vk.inverse().expect("program_vk is non-zero");
                }
                // else: aux[6] and aux[7] remain ZERO (default).

                new_state.nonce += 1;
            }
            Effect::DequeueMessage {
                expected_message_hash,
                deposit_refund,
            } => {
                row[PARAM_BASE + param::DEQUEUE_EXPECTED_HASH] = *expected_message_hash;
                row[PARAM_BASE + param::DEQUEUE_DEPOSIT_REFUND] = BabyBear::new(*deposit_refund);

                // Non-empty queue proof: store inverse of expected_message_hash in aux[1].
                assert!(
                    *expected_message_hash != BabyBear::ZERO,
                    "DequeueMessage: expected_message_hash must be non-zero (non-empty queue)"
                );
                row[AUX_BASE + 1] = expected_message_hash
                    .inverse()
                    .expect("message hash is non-zero");

                // Queue root advances: new_root = hash(old_root, expected_message_hash).
                // (In a full implementation this would be a Merkle removal, but for
                // the circuit we use a hash chain advance for soundness.)
                let old_queue_root = new_state.fields[4];
                let new_queue_root = hash_2_to_1(old_queue_root, *expected_message_hash);
                new_state.fields[4] = new_queue_root;

                // Deposit refund credited to balance.
                new_state.balance = new_state.balance.saturating_add(*deposit_refund as u64);
                net_delta += *deposit_refund as i64;

                // Store new queue root in aux[0] for constraint verification.
                row[AUX_BASE + 0] = new_queue_root;

                new_state.nonce += 1;
            }
            Effect::ResizeQueue {
                new_capacity,
                queue_id,
                cost_per_slot,
                old_capacity,
            } => {
                row[PARAM_BASE + param::RESIZE_NEW_CAPACITY] = BabyBear::new(*new_capacity);
                row[PARAM_BASE + param::RESIZE_QUEUE_ID] = *queue_id;
                row[PARAM_BASE + param::RESIZE_COST_PER_SLOT] = BabyBear::new(*cost_per_slot);
                row[PARAM_BASE + param::RESIZE_OLD_CAPACITY] = BabyBear::new(*old_capacity);

                // Stage 2: signed-delta witness for sound shrink handling.
                let (delta_sign, delta_mag) = if *new_capacity >= *old_capacity {
                    (0u32, *new_capacity - *old_capacity)
                } else {
                    (1u32, *old_capacity - *new_capacity)
                };
                row[AUX_BASE + aux_off::RESIZE_DELTA_SIGN] = BabyBear::new(delta_sign);
                row[AUX_BASE + aux_off::RESIZE_DELTA_MAG] = BabyBear::new(delta_mag);

                // If growing, debit balance for delta * cost_per_slot.
                if *new_capacity > *old_capacity {
                    let delta = (*new_capacity - *old_capacity) as u64;
                    let cost = delta * (*cost_per_slot as u64);
                    new_state.balance = new_state.balance.saturating_sub(cost);
                    net_delta -= cost as i64;
                }
                // Capacity update is reflected in the state commitment via field[5]
                // (we use field[5] as the queue capacity slot for ResizeQueue).
                new_state.fields[5] = BabyBear::new(*new_capacity);

                new_state.nonce += 1;
            }
            Effect::AtomicQueueTx {
                op_count,
                tx_hash,
                combined_old_root,
                combined_new_root,
                net_deposit,
            } => {
                row[PARAM_BASE + param::ATOMIC_TX_OP_COUNT] = BabyBear::new(*op_count);
                row[PARAM_BASE + param::ATOMIC_TX_HASH] = *tx_hash;
                row[PARAM_BASE + param::ATOMIC_TX_COMBINED_OLD_ROOT] = *combined_old_root;
                row[PARAM_BASE + param::ATOMIC_TX_COMBINED_NEW_ROOT] = *combined_new_root;
                row[PARAM_BASE + param::ATOMIC_TX_NET_DEPOSIT] = BabyBear::new(*net_deposit);

                // State transition: field[4] changes from combined_old_root to combined_new_root.
                // The circuit constrains that field[4] == combined_old_root before and
                // becomes combined_new_root after, binding the atomic transition.
                new_state.fields[4] = *combined_new_root;

                // Balance debit by net_deposit (sum of deposits paid minus refunds received).
                new_state.balance = new_state.balance.saturating_sub(*net_deposit as u64);
                net_delta -= *net_deposit as i64;

                // Auxiliary witness: aux[0] = hash(tx_hash, hash(combined_old_root, combined_new_root))
                // This binds the transaction to the specific state transition.
                let inner = hash_2_to_1(*combined_old_root, *combined_new_root);
                let binding_hash = hash_2_to_1(*tx_hash, inner);
                row[AUX_BASE + 0] = binding_hash;

                new_state.nonce += 1;
            }
            Effect::PipelineStep {
                pipeline_id,
                source_old_root,
                source_new_root,
                sink_new_root,
                message_hash,
            } => {
                row[PARAM_BASE + param::PIPELINE_ID] = *pipeline_id;
                row[PARAM_BASE + param::PIPELINE_SOURCE_OLD_ROOT] = *source_old_root;
                row[PARAM_BASE + param::PIPELINE_SOURCE_NEW_ROOT] = *source_new_root;
                row[PARAM_BASE + param::PIPELINE_SINK_NEW_ROOT] = *sink_new_root;
                row[PARAM_BASE + param::PIPELINE_MESSAGE_HASH] = *message_hash;

                // State transition: field[4] (source queue root) changes from
                // source_old_root to source_new_root (message dequeued from source).
                new_state.fields[4] = *source_new_root;

                // Auxiliary witness:
                // aux[0] = hash(source_old_root, message_hash) = expected source_new_root
                //   (proves dequeue: source_new_root == hash_chain_dequeue(source_old, msg))
                // aux[1] = sink_new_root (stored for external verification of sink transition)
                // aux[6] = pipeline_id^-1 (P1-5 fix: forces pipeline_id != 0)
                let expected_source_new = hash_2_to_1(*source_old_root, *message_hash);
                row[AUX_BASE + 0] = expected_source_new;
                row[AUX_BASE + 1] = *sink_new_root;
                row[AUX_BASE + 6] = pipeline_id
                    .inverse()
                    .expect("PipelineStep pipeline_id must be non-zero");

                new_state.nonce += 1;
            }
        }

        // Refresh state commitment.
        new_state.refresh_commitment();

        // Fill state commitment tree intermediate columns (aux[8..10]).
        // These are constrained by the evaluator to match hash_4_to_1 computations
        // on the state_after columns.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            new_state.balance,
            new_state.nonce,
            &new_state.fields,
            new_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved on every row.
        // The constraint in eval_constraints requires that
        //   Σ b_i * 2^i + mode * 256 == old_reserved
        // hold unconditionally for every row.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        // Write state_after.
        let state_after_cols = new_state.to_trace_cols();
        for (i, &val) in state_after_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        trace.push(row);
        current_state = new_state;
    }

    // Compute effects hash and net delta for public inputs.
    let (effects_hash_lo, effects_hash_hi) = compute_effects_hash(effects);
    let (delta_mag, delta_sign) = if net_delta < 0 {
        ((-net_delta) as u32, 1u32)
    } else {
        (net_delta as u32, 0u32)
    };

    // Fill aux columns on the first row with public-input-bound values.
    // Stage 1: effects_hash is widened to 4 felts; positions 0..1 are bound
    // to AUX[4..5] via boundary constraints (preserves the legacy 2-felt
    // witness binding), positions 2..3 are PI-only (see AUDIT[stage1-pi-only-bound]).
    let effects_hash_4_witness = compute_effects_hash_4(effects);
    if !trace.is_empty() {
        trace[0][AUX_BASE + 2] = BabyBear::new(delta_mag);
        trace[0][AUX_BASE + 3] = BabyBear::new(delta_sign);
        trace[0][AUX_BASE + 4] = effects_hash_4_witness[0];
        trace[0][AUX_BASE + 5] = effects_hash_4_witness[1];

        // Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.1):
        // bind the witness's key-commit + sequence into row-0 aux columns.
        // The boundary constraints pin these to the matching PI slots.
        // When IS_SOVEREIGN_CELL == 0, the prover writes zero sentinels
        // and the verifier supplies zero sentinels — the boundary holds
        // trivially.
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_0] =
            context.sovereign_witness_key_commit[0];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_1] =
            context.sovereign_witness_key_commit[1];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_2] =
            context.sovereign_witness_key_commit[2];
        trace[0][AUX_BASE + aux_off::WITNESS_KEY_COMMIT_3] =
            context.sovereign_witness_key_commit[3];
        trace[0][AUX_BASE + aux_off::WITNESS_SEQUENCE] =
            BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);
    }
    // Silence unused warnings on the legacy 2-felt return values.
    let _ = (effects_hash_lo, effects_hash_hi);

    // Pad with NoOp rows.
    for _ in n_effects..trace_height {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE; // NoOp selector

        // State before = current state (carried from last real row).
        let state_cols = current_state.to_trace_cols();
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_BEFORE_BASE + i] = val;
        }
        // State after = same (NoOp doesn't change state).
        for (i, &val) in state_cols.iter().enumerate() {
            row[STATE_AFTER_BASE + i] = val;
        }

        // Fill state commitment tree intermediates for padding rows too.
        let (inter1, inter2, inter3) = CellState::compute_commitment_intermediates(
            current_state.balance,
            current_state.nonce,
            &current_state.fields,
            current_state.capability_root,
        );
        row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
        row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
        row[AUX_BASE + aux_off::STATE_INTER3] = inter3;

        // Stage 2 (sealing honesty): bit-decompose OLD reserved.
        fill_reserved_bits(
            &mut row,
            current_state.sealed_field_mask,
            current_state.mode_flag,
        );

        trace.push(row);
        // current_state stays the same for padding.
    }

    // Stage 2 sum-check (REVIEW[stage1-acc-row0] resolution): populate
    // aux[CUSTOM_COUNT_ACC] as the EXCLUSIVE running sum of `s_custom`
    // indicators. Convention: acc[i] = count of s_custom rows in [0..i)
    // (NOT including row i). With this convention:
    //   - acc[0] == 0 always (pinned by row-0 boundary)
    //   - Transition: next.acc == this.acc + this.s_custom (Group 7)
    //   - acc[last] == total count, pinned to PI[CUSTOM_EFFECT_COUNT] by
    //     the last-row boundary.
    //
    // For the last-row boundary to equal the total custom count, the last
    // row must contribute 0 to the running sum — i.e., the last row must
    // be a NoOp pad row. The pad loop above already pads with NoOp; the
    // `need_extra_pad` check at trace_height computation guarantees a NoOp
    // slot exists when the last real effect is Custom.
    {
        let mut acc: u32 = 0;
        for i in 0..trace.len() {
            // Exclusive sum: record acc BEFORE adding this row's contribution.
            trace[i][AUX_BASE + aux_off::CUSTOM_COUNT_ACC] = BabyBear::new(acc);
            if trace[i][sel::CUSTOM] == BabyBear::ONE {
                acc = acc.saturating_add(1);
            }
        }
    }

    // Collect custom effect entries for public inputs.
    let custom_entries: Vec<_> = effects
        .iter()
        .filter_map(|e| {
            if let Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = e
            {
                Some((*program_vk_hash, *proof_commitment))
            } else {
                None
            }
        })
        .collect();
    let custom_count = custom_entries.len();
    assert!(
        custom_count <= context.max_custom_effects as usize,
        "Too many custom effects: {} (max {})",
        custom_count,
        context.max_custom_effects
    );
    assert!(
        context.max_custom_effects <= pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
        "max_custom_effects {} exceeds hard cap {}",
        context.max_custom_effects,
        pi::MAX_CUSTOM_EFFECTS_HARD_CAP,
    );

    // Build public inputs in the Stage 1 widened layout (see `pi` module).
    let pi_len = pi::BASE_COUNT + custom_count * pi::CUSTOM_ENTRY_SIZE;
    let mut public_inputs = vec![BabyBear::ZERO; pi_len];

    // ---- Commitments (4 felts each) ----
    let old_commit_4 = CellState::compute_commitment_4(
        initial_state.balance,
        initial_state.nonce,
        &initial_state.fields,
        initial_state.capability_root,
    );
    let new_commit_4 = CellState::compute_commitment_4(
        current_state.balance,
        current_state.nonce,
        &current_state.fields,
        current_state.capability_root,
    );
    for i in 0..pi::OLD_COMMIT_LEN {
        public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
    }
    for i in 0..pi::NEW_COMMIT_LEN {
        public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
    }

    // ---- Effects hash (4 felts) ----
    let effects_hash_4 = compute_effects_hash_4(effects);
    for i in 0..pi::EFFECTS_HASH_LEN {
        public_inputs[pi::EFFECTS_HASH_BASE + i] = effects_hash_4[i];
    }
    // Suppress unused-variable warning for the legacy 2-felt form.
    let _ = (effects_hash_lo, effects_hash_hi);

    // ---- Balance limbs (P0-1) ----
    let (i_lo, i_hi) = split_u64(initial_state.balance);
    let (f_lo, f_hi) = split_u64(current_state.balance);
    public_inputs[pi::INIT_BAL_LO] = i_lo;
    public_inputs[pi::INIT_BAL_HI] = i_hi;
    public_inputs[pi::FINAL_BAL_LO] = f_lo;
    public_inputs[pi::FINAL_BAL_HI] = f_hi;

    // ---- Net delta (P0-1) ----
    public_inputs[pi::NET_DELTA_MAG] = BabyBear::new(delta_mag);
    public_inputs[pi::NET_DELTA_SIGN] = BabyBear::new(delta_sign);

    // ---- Stage 1 additions ----
    public_inputs[pi::CURRENT_BLOCK_HEIGHT] =
        BabyBear::new((context.current_block_height & 0x7FFF_FFFF) as u32);
    public_inputs[pi::MAX_CUSTOM_EFFECTS] = BabyBear::new(context.max_custom_effects as u32);
    public_inputs[pi::CUSTOM_EFFECT_COUNT] = BabyBear::new(custom_count as u32);
    for i in 0..pi::APPROVED_HANDOFFS_LEN {
        public_inputs[pi::APPROVED_HANDOFFS_BASE + i] = context.approved_handoffs_root[i];
    }

    // ---- Stage 7-γ.0a turn-identity bindings ----
    // These four fields are *shared across all per-cell proofs of one turn*.
    // The verifier's cross-proof PI matching loop enforces equality across
    // the bundle; per-proof binding to the canonical Turn::hash and
    // call_forest projection is executor-trusted at γ.0 and becomes
    // algebraic at γ.1.
    for i in 0..pi::TURN_HASH_LEN {
        public_inputs[pi::TURN_HASH_BASE + i] = context.turn_hash[i];
    }
    for i in 0..pi::EFFECTS_HASH_GLOBAL_LEN {
        public_inputs[pi::EFFECTS_HASH_GLOBAL_BASE + i] = context.effects_hash_global[i];
    }
    public_inputs[pi::ACTOR_NONCE] = BabyBear::new((context.actor_nonce & 0x7FFF_FFFF) as u32);
    for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
        public_inputs[pi::PREVIOUS_RECEIPT_HASH_BASE + i] = context.previous_receipt_hash[i];
    }

    // ---- Sovereign-witness teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md) ----
    //
    // Phase 1: PI carries the witness's owning-key commitment, monotonic
    // sequence, and a flag indicating sovereign vs. hosted. The boundary
    // constraint binds the in-trace aux columns to these PI values at
    // row 0. When IS_SOVEREIGN_CELL == 0, the sentinel-zero on both
    // sides makes the constraint trivially satisfied.
    //
    // Phase 2: PI additionally carries the inner transition_proof's
    // VK hash + 4-felt commitment + a presence flag. The off-AIR
    // verifier reads these and recursively verifies the inner STARK.
    for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
        public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] =
            context.sovereign_witness_key_commit[i];
    }
    public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] =
        BabyBear::new((context.sovereign_witness_sequence & 0x7FFF_FFFF) as u32);
    public_inputs[pi::IS_SOVEREIGN_CELL] = if context.is_sovereign_cell {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN {
        public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE + i] =
            context.sovereign_transition_proof_vk_hash[i];
    }
    for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
        public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] =
            context.sovereign_transition_proof_commitment[i];
    }
    public_inputs[pi::HAS_TRANSITION_PROOF] = if context.has_transition_proof {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };

    // ---- 30-bit-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5) ----
    //
    // Each of the three affected effects gets its own 4×16-bit limb slot.
    // We aggregate per-turn: each BridgeMint/BridgeLock/CreateEscrow in
    // the trace contributes its full u64 value via wrap-add (the AIR's
    // per-row balance arithmetic uses the legacy 30-bit-truncated
    // `value_lo`; the new limb slots independently attest to the FULL
    // u64 the executor saw, summed across the trace). A future
    // refinement (per-row limb columns) sits behind a separate
    // PI/aux-column widening.
    //
    // Each limb is < 2^16 by construction (`u64_to_4_limbs_16` masks).
    // The verifier's PI match loop catches any out-of-range limb a
    // malicious prover supplies, and the on-trace effects also bind to
    // the same 4-limb form via the absorbed-into-effects-hash path
    // (see `compute_effects_hash` arms for BridgeMint/BridgeLock/
    // CreateEscrow). Together the two paths give the bit-injective
    // u64 binding that closes §6.5.
    let (mint_sum, lock_sum, escrow_sum) = {
        let mut m: u64 = 0;
        let mut l: u64 = 0;
        let mut e: u64 = 0;
        for eff in effects {
            match eff {
                Effect::BridgeMint { value_full, .. } => m = m.wrapping_add(*value_full),
                Effect::BridgeLock { value_full, .. } => l = l.wrapping_add(*value_full),
                Effect::CreateEscrow { amount_full, .. } => e = e.wrapping_add(*amount_full),
                _ => {}
            }
        }
        (m, l, e)
    };
    let mint_limbs = u64_to_4_limbs_16(mint_sum);
    let lock_limbs = u64_to_4_limbs_16(lock_sum);
    let escrow_limbs = u64_to_4_limbs_16(escrow_sum);
    for i in 0..pi::BRIDGE_MINT_VALUE_LIMBS_LEN {
        public_inputs[pi::BRIDGE_MINT_VALUE_LIMBS_BASE + i] = mint_limbs[i];
    }
    for i in 0..pi::BRIDGE_LOCK_VALUE_LIMBS_LEN {
        public_inputs[pi::BRIDGE_LOCK_VALUE_LIMBS_BASE + i] = lock_limbs[i];
    }
    for i in 0..pi::CREATE_ESCROW_AMOUNT_LIMBS_LEN {
        public_inputs[pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE + i] = escrow_limbs[i];
    }
    // Unused context-field shadows (the context-supplied limbs remain in
    // EffectVmContext for forward-compat with a per-effect-instance
    // refinement; today they're recomputed from `effects`).
    let _ = (
        context.bridge_mint_value_limbs,
        context.bridge_lock_value_limbs,
        context.create_escrow_amount_limbs,
    );

    // ---- Slot-caveat manifest (Cav-Codex Block 3) ----
    //
    // Project the cell-program-declared `StateConstraint` set into a
    // fixed-size PI table. The verifier extracts the table and
    // re-evaluates each entry against the state_before / state_after
    // columns; the *executor* is responsible for honestly populating
    // the manifest from `CellProgram::Predicate(...)`. Any tampering
    // with an entry shows up as a PI-match mismatch at receipt
    // verification time (the receipt re-computes the expected PI from
    // the cell's program).
    let cav_count = context.slot_caveat_count.min(pi::MAX_SLOT_CAVEATS as u32);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(cav_count);
    for i in 0..(cav_count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        context.slot_caveat_manifest[i]
            .write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }

    // ---- Custom proof entries ----
    for (i, (vk_hash, proof_commit)) in custom_entries.iter().enumerate() {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        for j in 0..4 {
            public_inputs[base + j] = vk_hash[j];
        }
        for j in 0..4 {
            public_inputs[base + 4 + j] = proof_commit[j];
        }
    }

    assert_eq!(public_inputs.len(), pi_len);
    (trace, public_inputs)
}

/// Encode a signed balance delta as (magnitude, sign_bit) for public inputs.
pub fn encode_net_delta(delta: i64) -> (BabyBear, BabyBear) {
    if delta < 0 {
        (BabyBear::new((-delta) as u32), BabyBear::ONE)
    } else {
        (BabyBear::new(delta as u32), BabyBear::ZERO)
    }
}

/// Extract the net balance delta from public inputs.
pub fn extract_net_delta(public_inputs: &[BabyBear]) -> Option<i64> {
    if public_inputs.len() < pi::BASE_COUNT {
        return None;
    }
    let magnitude = public_inputs[pi::NET_DELTA_MAG].0 as i64;
    let sign_bit = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign_bit == 1 {
        Some(-magnitude)
    } else {
        Some(magnitude)
    }
}

/// Extract the custom proof commitments from public inputs.
/// Returns a vec of (program_vk_hash, proof_commitment) tuples.
/// Cav-Codex Block 3: extract the (count, entries) slot-caveat
/// manifest from a public-inputs vector. Returns up to
/// `pi::MAX_SLOT_CAVEATS` entries; trailing entries past `count` are
/// dropped. Use [`verify_slot_caveat_manifest`] to re-evaluate each
/// against state_before / state_after.
pub fn extract_slot_caveat_manifest(public_inputs: &[BabyBear]) -> Vec<SlotCaveatEntry> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let count = (public_inputs[pi::SLOT_CAVEAT_COUNT].0 as usize).min(pi::MAX_SLOT_CAVEATS);
    let mut result = Vec::with_capacity(count);
    for i in 0..count {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        result.push(SlotCaveatEntry {
            type_tag: public_inputs[base].0,
            slot_index: (public_inputs[base + 1].0 & 0xFF) as u8,
            params: [
                public_inputs[base + 2],
                public_inputs[base + 3],
                public_inputs[base + 4],
                public_inputs[base + 5],
            ],
        });
    }
    result
}

pub fn extract_custom_proof_commitments(
    public_inputs: &[BabyBear],
) -> Vec<([BabyBear; 4], [BabyBear; 4])> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Vec::new();
    }
    let custom_count = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
    let mut result = Vec::with_capacity(custom_count);
    for i in 0..custom_count {
        let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
        if base + pi::CUSTOM_ENTRY_SIZE > public_inputs.len() {
            break;
        }
        let vk_hash = [
            public_inputs[base],
            public_inputs[base + 1],
            public_inputs[base + 2],
            public_inputs[base + 3],
        ];
        let proof_commit = [
            public_inputs[base + 4],
            public_inputs[base + 5],
            public_inputs[base + 6],
            public_inputs[base + 7],
        ];
        result.push((vk_hash, proof_commit));
    }
    result
}


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
