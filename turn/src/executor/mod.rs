//! TurnExecutor: applies a turn to a ledger with full atomicity.
//!
//! # Trust Model
//!
//! This module operates at the **EXECUTOR-TRUSTED** trust level.
//!
//! - **Soundness**: Correct state transitions are guaranteed IF all federation members
//!   execute the same turns in the same order and reach consensus on the resulting state.
//!   A compromised executor can produce incorrect state that other honest members will
//!   reject during replication.
//! - **Assumptions**: At least 2f+1 honest federation members (BFT assumption). The
//!   executor correctly implements the turn semantics, precondition checks, and effect
//!   application. External parties trust the federation as a whole.
//! - **Verifiable by**: Other federation members via state replication. External parties
//!   trust the federation's attested root (not individually verifiable without re-execution).
//!
//! ## Trust-Critical Functions
//!
//! The following functions are trust-critical and are annotated individually:
//! - `execute()` — atomically applies a turn; if compromised, state diverges from consensus
//! - `verify_authorization()` — gates all state mutations; bypass = unauthorized writes
//! - `apply_effect()` — mutates ledger state; incorrect application = balance corruption
//! - `verify_and_commit_proof()` — bridges trustless (STARK) to executor; bypass = forged sovereign state
//! - `check_preconditions()` — temporal and state guards; bypass = expired/invalid actions succeed
//!
//! ## Path to Trustless
//!
//! Phase 3 (proof-carrying sovereign turns) already moves sovereign cells to the
//! trustless level: the executor merely verifies a STARK proof and updates a commitment.
//! The remaining executor-trusted path (Phase 2: classical call-forest execution) will
//! transition to trustless once the Effect VM circuit covers all effect types, allowing
//! every turn to carry a proof.
//!
//! The executor walks the call forest depth-first, checking preconditions,
//! verifying authorization, applying effects, and metering computrons at each step.
//! If any action fails, ALL effects are rolled back via journal replay (atomicity guarantee).

use std::collections::HashMap;
use std::sync::Mutex;

#[allow(unused_imports)]
use tracing::info;

use dregg_cell::{
    AuthRequired, BulletproofRangeProof, Cell, CellId, CellStateDelta, Ledger, LedgerDelta,
    RevocationChannelSet, ValueCommitment, ValueCommitmentBytes,
    note::NoteError,
    note_bridge::{BridgedNullifierSet, PendingBridgeSet},
    nullifier_set::NullifierSet,
    preconditions::EvalContext,
    predicate::{InputRef, PredicateInput, WitnessedPredicateError, WitnessedPredicateKind},
    state::STATE_SLOTS,
};
use dregg_types::AttestedRoot;
use ed25519_dalek::{Signature, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::action::{Action, Authorization, DelegationMode, Effect, Event};
use crate::budget_gate::BudgetGate;
use crate::error::TurnError;
use crate::escrow::{
    CommittedEscrow, EscrowClaimAuth, EscrowCondition, EscrowRecord, verify_escrow_claim,
};
use crate::forest::CallTree;
use crate::journal::{JournalEntry, LedgerJournal};
use crate::routing::RoutingDirective;
use crate::turn::{EmittedEvent, Turn, TurnReceipt, TurnResult};

use dregg_dsl_runtime::ProgramRegistry;

/// Whether a single `Effect` is a `Burn`, recursing into
/// `ExerciseViaCapability::inner_effects`. Powers `was_burn` disclosure.
fn effect_is_burn(e: &Effect) -> bool {
    match e {
        Effect::Burn { .. } => true,
        Effect::ExerciseViaCapability { inner_effects, .. } => {
            inner_effects.iter().any(effect_is_burn)
        }
        _ => false,
    }
}

/// Recursive: does any action in this tree carry an `Effect::Burn`?
fn tree_has_burn_effect(t: &crate::forest::CallTree) -> bool {
    if t.action.effects.iter().any(effect_is_burn) {
        return true;
    }
    t.children.iter().any(tree_has_burn_effect)
}

/// Human-readable name of a `WitnessedPredicateKind` for diagnostic
/// error messages (used by `TurnError::AuthModeNotRegistered`).
fn predicate_kind_name(kind: WitnessedPredicateKind) -> String {
    match kind {
        WitnessedPredicateKind::Dfa => "Dfa".into(),
        WitnessedPredicateKind::Temporal => "Temporal".into(),
        WitnessedPredicateKind::MerkleMembership => "MerkleMembership".into(),
        WitnessedPredicateKind::NonMembership => "NonMembership".into(),
        WitnessedPredicateKind::BlindedSet => "BlindedSet".into(),
        WitnessedPredicateKind::BridgePredicate => "BridgePredicate".into(),
        WitnessedPredicateKind::PedersenEquality => "PedersenEquality".into(),
        WitnessedPredicateKind::Custom { .. } => "Custom".into(),
    }
}

/// 32-byte vk_hash for `WitnessedPredicateKind::Custom { vk_hash }`;
/// zeroed for built-in kinds (the built-in identity is in the name).
fn predicate_kind_vk_hash(kind: WitnessedPredicateKind) -> [u8; 32] {
    match kind {
        WitnessedPredicateKind::Custom { vk_hash } => vk_hash,
        _ => [0u8; 32],
    }
}

/// Estimate the metering cost of a single [`Authorization`] variant.
///
/// Recurses into [`Authorization::OneOf`]'s candidates and returns the
/// maximum cost (pessimistic upper bound so a malicious chooser can't
/// sneak a cheaper-than-actual candidate through the meter).
fn estimate_authorization_cost(auth: &Authorization, costs: &ComputronCosts) -> u64 {
    match auth {
        Authorization::Signature(_, _) => costs.signature_verify,
        Authorization::Proof { .. } => costs.proof_verify,
        Authorization::Breadstuff(_) => costs.signature_verify / 2,
        Authorization::Bearer(_) => costs.signature_verify,
        Authorization::Unchecked => 0,
        Authorization::CapTpDelivered { .. } => costs.signature_verify.saturating_mul(2),
        Authorization::Custom { .. } => costs.proof_verify,
        Authorization::OneOf { candidates, .. } => candidates
            .iter()
            .map(|c| estimate_authorization_cost(c, costs))
            .max()
            .unwrap_or(0),
    }
}

/// Cav-Codex Block 3: project a cell-program's declared
/// `StateConstraint` list into the Effect-VM slot-caveat manifest
/// (the (count, entries[]) PI surface that
/// `dregg_circuit::effect_vm::verify_slot_caveat_manifest` will
/// re-evaluate).
///
/// Returns `(count, manifest)` where `count <= MAX_SLOT_CAVEATS` and
/// `manifest[..count]` carries one entry per binding-eligible
/// constraint. Constraints whose AIR teeth aren't yet implemented
/// (Custom, Witnessed, BoundDelta, FieldGteHeight, FieldLteHeight,
/// FieldDeltaInRange, RateLimit, RateLimitBySum, BoundedBy,
/// PreimageGate, MonotonicSequence-on-32B-state, AnyOf,
/// SumEqualsAcross, SumEquals, CapabilityUniqueness, TemporalPredicate)
/// are skipped at projection time; they still evaluate
/// executor-side, but the proof carries no manifest entry that
/// binds them — see `SLOT-CAVEATS-DESIGN.md` §4 ("AIR enforcement is
/// strong-soundness opt-in").
pub fn project_slot_caveat_manifest(
    constraints: &[dregg_cell::StateConstraint],
) -> (
    u32,
    [dregg_circuit::effect_vm::SlotCaveatEntry; dregg_circuit::effect_vm::pi::MAX_SLOT_CAVEATS],
) {
    use dregg_circuit::effect_vm::SlotCaveatEntry;
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::field::BabyBear;

    let mut entries = [SlotCaveatEntry::zero(); pi::MAX_SLOT_CAVEATS];
    let mut count: usize = 0;

    /// Project a 32-byte field-element to a BabyBear via the
    /// low-4-bytes path used everywhere else by the Effect VM's
    /// state column truncation.
    fn fe_to_bb(fe: &[u8; 32]) -> BabyBear {
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&fe[0..4]);
        BabyBear::new(u32::from_le_bytes(buf))
    }

    for c in constraints {
        if count >= pi::MAX_SLOT_CAVEATS {
            break;
        }
        let entry = match c {
            dregg_cell::StateConstraint::Immutable { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::WriteOnce { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::FieldDelta { index, delta } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
                slot_index: *index,
                params: [
                    fe_to_bb(delta),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::MonotonicSequence { seq_index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
                slot_index: *seq_index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::FieldEquals { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_EQUALS,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::FieldGte { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_GTE,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::FieldLte { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_LTE,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::Monotonic { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::StrictMonotonic { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::TemporalGate {
                not_before,
                not_after,
            } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
                // TemporalGate is cell-scoped, not slot-scoped — store
                // slot_index = 0 sentinel; the verifier never reads it.
                slot_index: 0,
                params: [
                    BabyBear::new((not_before.unwrap_or(0) & 0x7FFF_FFFF) as u32),
                    BabyBear::new((not_after.unwrap_or(0) & 0x7FFF_FFFF) as u32),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::SenderAuthorized { set } => {
                let slot_index = match set {
                    dregg_cell::program::AuthorizedSet::PublicRoot { set_root_index } => {
                        *set_root_index
                    }
                    dregg_cell::program::AuthorizedSet::BlindedSet { .. } => 0,
                    // CredentialSet dispatches via the BlindedSet verifier
                    // off-chain (see AuthorizedSet::credential_set_commitment).
                    // No public-slot root to index — use 0 as the
                    // "no-slot" sentinel like BlindedSet.
                    dregg_cell::program::AuthorizedSet::CredentialSet { .. } => 0,
                };
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_SENDER_AUTHORIZED,
                    slot_index,
                    params: [BabyBear::ZERO; 4],
                })
            }
            dregg_cell::StateConstraint::AllowedTransitions { slot_index, .. } => {
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
                    slot_index: *slot_index,
                    params: [BabyBear::ZERO; 4],
                })
            }
            // Deferred — no AIR teeth in Block 3 first wave.
            dregg_cell::StateConstraint::SumEquals { .. }
            | dregg_cell::StateConstraint::FieldLteField { .. }
            | dregg_cell::StateConstraint::BoundedBy { .. }
            | dregg_cell::StateConstraint::FieldDeltaInRange { .. }
            | dregg_cell::StateConstraint::FieldGteHeight { .. }
            | dregg_cell::StateConstraint::FieldLteHeight { .. }
            | dregg_cell::StateConstraint::SumEqualsAcross { .. }
            | dregg_cell::StateConstraint::CapabilityUniqueness { .. }
            | dregg_cell::StateConstraint::RateLimit { .. }
            | dregg_cell::StateConstraint::RateLimitBySum { .. }
            | dregg_cell::StateConstraint::PreimageGate { .. }
            | dregg_cell::StateConstraint::TemporalPredicate { .. }
            | dregg_cell::StateConstraint::BoundDelta { .. }
            | dregg_cell::StateConstraint::AnyOf { .. }
            | dregg_cell::StateConstraint::Witnessed { .. }
            // `Renounced` is the categorical dual of SenderAuthorized
            // (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2). No AIR projection
            // in Block-3 first wave; the witness side is checked by the
            // `WitnessedPredicateRegistry` NonMembership verifier.
            | dregg_cell::StateConstraint::Renounced { .. }
            | dregg_cell::StateConstraint::Custom { .. } => None,
        };
        if let Some(e) = entry {
            entries[count] = e;
            count += 1;
        }
    }
    (count as u32, entries)
}

/// Whether note effects in a turn use Pedersen value commitments or cleartext values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NoteCommitmentMode {
    /// No note effects present in the turn.
    Empty,
    /// All note effects use cleartext values (legacy path).
    Cleartext,
    /// All note effects carry Pedersen value commitments (committed path).
    Committed,
    /// Some notes have commitments, some don't -- invalid (rejected).
    Mixed,
}

/// A record of an active obligation tracked by the executor for balance enforcement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ObligationRecord {
    /// The obligor (who locked the stake).
    pub obligor: CellId,
    /// The beneficiary (who receives stake on slash).
    pub beneficiary: CellId,
    /// Federation height deadline.
    pub deadline_height: u64,
    /// Numeric stake amount locked from the obligor's balance.
    pub stake_amount: u64,
    /// Whether this obligation has been resolved (fulfilled or slashed).
    pub resolved: bool,
}

/// Trait for verifying ZK proofs. Implementations provide circuit-specific verification.
///
/// The executor is fail-closed: if no ProofVerifier is configured and a cell requires
/// proof authorization, the action is rejected.
pub trait ProofVerifier: Send + Sync {
    /// Verify a proof against public inputs and a verification key.
    ///
    /// Returns true if the proof is valid for the given public inputs and verification key.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool;
}

mod costs;
pub use costs::ComputronCosts;

// =============================================================================
// Cell Migration Two-Phase Commit
// =============================================================================

mod migration;
pub use migration::{CellMigrationManager, MigrationCancelReason, MigrationError, MigrationState};

/// The turn executor: applies turns to a ledger atomically.
mod effect_vm_bridge;
use effect_vm_bridge::convert_turn_effects_to_vm;
pub struct TurnExecutor {
    /// Cost configuration for computron metering.
    pub costs: ComputronCosts,
    /// Program registry for custom cell programs (smart contract runtime).
    /// When a sovereign cell has a `verification_key_hash` set, the executor
    /// looks up the deployed program here and verifies proofs against it.
    /// Falls back to `EffectVmAir` if no program is found.
    pub program_registry: ProgramRegistry,
    /// Current timestamp for precondition evaluation.
    pub current_timestamp: i64,
    /// Current block height for precondition evaluation.
    pub block_height: u64,
    /// Optional ZK proof verifier. If None and a cell requires proof auth, the action is rejected.
    pub proof_verifier: Option<Box<dyn ProofVerifier>>,
    /// Optional budget gate (Stingray bounded counter).
    /// When present, the executor checks the silo's local budget slice before executing
    /// each turn. If the slice cannot cover the turn fee, the turn is rejected with
    /// `TurnError::BudgetExhausted`. On turn failure, the debit is refunded (fast unlock).
    ///
    /// Designed for single-silo-single-thread execution, but uses `Mutex` for interior
    /// mutability to remain sound under concurrent access (future-proofing for async
    /// execution or parallel turn processing).
    pub budget_gate: Option<Mutex<BudgetGate>>,
    /// Trusted federation roots for cross-federation note bridging.
    /// When a BridgeMint effect is processed, the portable proof's source root
    /// must be in this set. Empty = no cross-federation bridges accepted.
    pub trusted_federation_roots: Vec<AttestedRoot>,
    /// This federation's identity (genesis root hash or configured ID).
    /// Prevents cross-federation double-spend via destination binding.
    pub local_federation_id: [u8; 32],
    /// Bridged nullifier set: tracks nullifiers from OTHER federations that have
    /// been bridged into this one. Prevents the same note from being bridged twice.
    pub bridged_nullifiers: Mutex<BridgedNullifierSet>,
    /// Production note-spend nullifier set: tracks every nullifier published by a
    /// successful `Effect::NoteSpend` in this federation. Append-only with
    /// double-spend rejection (`NullifierSet::insert` errors on re-insert).
    /// Rolled back via `JournalEntry::NoteNullifierInserted` if the turn fails
    /// after the insert.
    ///
    /// This is the production-side complement to `bridged_nullifiers` (which
    /// tracks *inbound* cross-federation bridges) — `note_nullifiers` tracks
    /// *local* spends. Together they form the permanent ledger gate that
    /// `Checkpoint::nullifier_set_root` commits to.
    pub note_nullifiers: Mutex<NullifierSet>,
    /// Pending bridges: notes locked for cross-federation transfer (two-phase protocol).
    /// Tracks notes that are committed-to-burn but not yet permanently spent.
    pub pending_bridges: Mutex<PendingBridgeSet>,
    /// Phased bridge receipt log (Stage 9 P3.D / DESIGN-receipts.md §5).
    ///
    /// Records monotone phase advancements per `bridge_id` for the four-phase
    /// envelope protocol. Independent of `pending_bridges` (which is keyed on
    /// `nullifier`, predates the full envelope format, and only tracks the
    /// source-side state machine). On `BridgeFinalize`, the executor admits a
    /// synthetic `Witnessed → Finalized` envelope pair so a future Refund for
    /// the same bridge_id is rejected as non-monotone.
    pub bridge_phase_log: Mutex<dregg_cell::note_bridge::BridgePhaseLog>,
    /// Trusted Ed25519 public keys for destination federation receipt verification.
    /// Used during BridgeFinalize to validate that the receipt was signed by a
    /// legitimate destination federation.
    pub trusted_destination_keys: Vec<[u8; 32]>,
    /// Block proposer cell (receives 50% of fees). If None, fees are 100% burned.
    pub proposer_cell: Option<CellId>,
    /// Federation treasury cell (receives 30% of fees). If None, that share is burned.
    pub treasury_cell: Option<CellId>,
    /// Maximum lifetime (in blocks) for capabilities introduced via three-party
    /// introduction. After `current_height + max_introduction_lifetime`, the routing
    /// directive expires and the introduced capability becomes stale.
    /// Default: 1000 blocks.
    pub max_introduction_lifetime: u64,
    /// Optional revocation channel set. When present, capability exercises and
    /// delegation access checks verify that gated capabilities haven't been revoked
    /// via their associated channel.
    pub revocation_channels: Option<RevocationChannelSet>,
    /// Active obligation records, keyed by obligation ID.
    /// Tracks locked stakes so that FulfillObligation and SlashObligation can
    /// enforce balance movement (return to obligor or transfer to beneficiary).
    pub obligations: Mutex<HashMap<[u8; 32], ObligationRecord>>,
    /// Active escrow records, keyed by escrow ID.
    /// Tracks locked funds for conditional settlement (release to recipient or refund to creator).
    pub escrows: Mutex<HashMap<[u8; 32], EscrowRecord>>,
    /// Active committed (privacy-preserving) escrow records, keyed by escrow ID.
    /// Tracks committed escrows where parties and amounts are hidden behind commitments.
    pub committed_escrows: Mutex<HashMap<[u8; 32], CommittedEscrow>>,
    /// Executor-internal side-table mapping committed escrow IDs to their locked amounts.
    /// This is needed for balance settlement (release/refund) since the committed escrow
    /// record intentionally does not store the cleartext amount. Only the executor knows
    /// this mapping; it is NOT exposed to observers.
    pub committed_escrow_amounts: Mutex<HashMap<[u8; 32], u64>>,
    /// Cell migration manager: tracks cells that are being migrated to other federations.
    /// Uses a two-phase commit protocol with timeout-based cancellation to prevent
    /// cells from being lost during network partitions.
    pub cell_migrations: Mutex<CellMigrationManager>,
    /// Factory registry: deployed factory descriptors and per-epoch creation counts.
    /// When a `CreateCellFromFactory` effect is processed, the factory's constraints
    /// are validated and budget is checked/recorded.
    /// Uses `RefCell` for interior mutability: `apply_effect` takes `&self` but
    /// factory validation needs `&mut` for recording budget usage.
    pub factory_registry: std::cell::RefCell<dregg_cell::FactoryRegistry>,
    /// Optional epoch minter for computron supply management.
    ///
    /// When configured, the executor calls `maybe_mint()` at each block to
    /// check for epoch boundaries and credit the treasury with newly minted
    /// computrons. This prevents the deflationary death spiral where all
    /// computrons are eventually burned.
    ///
    /// Uses `RefCell` for interior mutability since minting is called from
    /// within the execute path which takes `&self`.
    pub epoch_minter: Option<std::cell::RefCell<crate::economics::EpochMinter>>,
    /// Queue program registry: maps queue IDs to their attached validation programs.
    /// When an `EnqueueMessage` effect targets a queue with a registered program,
    /// the executor validates the enqueue against the program's constraints before
    /// accepting the effect. The validation result hash is bound to the STARK proof.
    pub queue_program_registry: crate::queue_programs::QueueProgramRegistry,
    /// Per-agent last receipt hash (P0-3 fix).
    ///
    /// On every successful turn commit, the agent's entry is set to the
    /// resulting receipt's `receipt_hash()`. Subsequent turns from the same
    /// agent must set `turn.previous_receipt_hash` to this value or be
    /// rejected with `TurnError::ReceiptChainMismatch`. An entry with no
    /// value means the agent has no committed turns and must submit with
    /// `previous_receipt_hash: None` (a "genesis" turn for that agent).
    ///
    /// Off-chain `verify::verify_receipt_chain` already enforces this when it
    /// has access to the full chain. This field enforces the same property
    /// AT WRITE TIME, removing the cipherclerk's ability to silently break the
    /// chain by submitting every turn as if it were genesis.
    pub last_receipt_hash: Mutex<HashMap<CellId, [u8; 32]>>,
    /// Optional X25519 keypair used to decrypt `EncryptedTurn` submissions.
    ///
    /// When set, callers may submit privacy-preserving `EncryptedTurn`
    /// envelopes via `execute_encrypted_turn`; the executor performs DH with
    /// its static secret and the sender's ephemeral public key, derives the
    /// ChaCha20-Poly1305 key, decrypts the turn body, and dispatches to the
    /// standard `execute` path. Without this key, `execute_encrypted_turn`
    /// rejects with `NoDecryptionKey` — i.e. the executor does not support
    /// the privacy path.
    ///
    /// The tuple is `(secret, public)` so callers don't need to recompute the
    /// public key on every decrypt. Senders bind their ciphertext to the
    /// `public` half via X25519 DH; the `secret` half is the long-term
    /// unsealer.
    pub turn_decryption_keypair: Option<([u8; 32], [u8; 32])>,
    /// Optional 32-byte Ed25519 signing key seed used to populate
    /// `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// When set, the executor signs each receipt's `receipt_hash()` and
    /// embeds the 64-byte signature in `receipt.executor_signature`. This is
    /// R-4 of `EFFECT-VM-SHAPE-A.md`: previously the field existed but was
    /// never populated, so the federation-exit path could not actually
    /// authenticate receipts as having come from a known executor.
    ///
    /// `None` reproduces the legacy behavior (receipts ship with
    /// `executor_signature = None`); existing chain-verification code
    /// (`verify_receipt_chain_with_keys`) treats absent signatures as a
    /// best-effort property, so the field is opt-in.
    pub executor_signing_key: Option<[u8; 32]>,
    /// Witnessed-predicate registry (Cav-Codex Block 2 + Block 3.5).
    ///
    /// Slot-caveat variants that need verifier dispatch
    /// (`StateConstraint::Witnessed`, `TemporalPredicate`,
    /// `SenderAuthorized { BlindedSet }`, `Custom`), `Preconditions::witnessed`
    /// clauses, and `CapabilityCaveat::Witnessed` exercise sites all
    /// route through this registry to verify proof bytes from the
    /// action's `witness_blobs`.
    ///
    /// Block 3.5: defaults to
    /// [`dregg_cell::WitnessedPredicateRegistry::default_builtins`] on
    /// every `TurnExecutor` constructor, so the dispatch path is
    /// always live and programs that declare `Witnessed { wp }` always
    /// evaluate. Hosts that want to swap in real (non-stub) verifiers
    /// call `set_witnessed_registry` with a registry pre-populated by
    /// `dregg_circuit::witnessed_predicate::default_registry()` (or
    /// register kinds piecemeal). `None` is *legal* — it disables
    /// dispatch and reverts to the legacy sentinel surface — but
    /// nothing inside `turn` constructs an executor that way anymore.
    pub witnessed_registry: Option<dregg_cell::WitnessedPredicateRegistry>,
    /// Optional custom-effect verifier registry, parallel structure to
    /// [`dregg_cell::WitnessedPredicateRegistry`] but keyed on the
    /// `Effect::Custom` vk_hash. The proof-carrying turn path consults
    /// this registry **before** falling back to the program registry,
    /// so app-side custom effects (whose canonical bytes are not
    /// `CellProgram`s) can be dispatched through a unified surface
    /// (per `VK-AS-RE-EXECUTION-RECIPE.md` §2.4).
    ///
    /// Absent: the executor uses the existing program-registry path
    /// (legacy DSL-authored cells).
    pub custom_effect_registry: Option<dregg_cell::CustomEffectRegistry>,
}

impl TurnExecutor {
    /// Create a new executor with the given cost configuration.
    pub fn new(costs: ComputronCosts) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: None,
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            bridge_phase_log: Mutex::new(dregg_cell::note_bridge::BridgePhaseLog::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            witnessed_registry: Some(dregg_cell::WitnessedPredicateRegistry::default_builtins()),
            custom_effect_registry: None,
        }
    }

    /// Create a new executor with a budget gate (Stingray bounded counter).
    ///
    /// When a budget gate is set, the executor checks the silo's local budget
    /// slice before executing each turn. If the slice cannot cover the turn fee,
    /// the turn is rejected with `TurnError::BudgetExhausted`.
    pub fn with_budget_gate(costs: ComputronCosts, gate: BudgetGate) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: None,
            budget_gate: Some(Mutex::new(gate)),
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            bridge_phase_log: Mutex::new(dregg_cell::note_bridge::BridgePhaseLog::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            witnessed_registry: Some(dregg_cell::WitnessedPredicateRegistry::default_builtins()),
            custom_effect_registry: None,
        }
    }

    /// Create a new executor with a proof verifier.
    pub fn with_proof_verifier(costs: ComputronCosts, verifier: Box<dyn ProofVerifier>) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            proof_verifier: Some(verifier),
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            pending_bridges: Mutex::new(PendingBridgeSet::new()),
            bridge_phase_log: Mutex::new(dregg_cell::note_bridge::BridgePhaseLog::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            obligations: Mutex::new(HashMap::new()),
            escrows: Mutex::new(HashMap::new()),
            committed_escrows: Mutex::new(HashMap::new()),
            committed_escrow_amounts: Mutex::new(HashMap::new()),
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            queue_program_registry: crate::queue_programs::QueueProgramRegistry::new(),
            last_receipt_hash: Mutex::new(HashMap::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            witnessed_registry: Some(dregg_cell::WitnessedPredicateRegistry::default_builtins()),
            custom_effect_registry: None,
        }
    }

    /// Set the budget gate.
    pub fn set_budget_gate(&mut self, gate: BudgetGate) {
        self.budget_gate = Some(Mutex::new(gate));
    }

    /// Set the proof verifier.
    pub fn set_proof_verifier(&mut self, verifier: Box<dyn ProofVerifier>) {
        self.proof_verifier = Some(verifier);
    }

    /// Equip the executor with an Ed25519 signing key (32-byte seed) used to
    /// populate `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// This is R-4 of `EFFECT-VM-SHAPE-A.md`. Until this builder is invoked,
    /// receipts ship with `executor_signature: None` (the legacy behavior);
    /// once set, every receipt produced by this executor — both the proof-
    /// carrying fast path and the standard execution path — is signed with
    /// the given key over the receipt's canonical `receipt_hash()`.
    ///
    /// Verification: `turn::verify::verify_receipt_chain_with_keys` walks the
    /// chain and accepts a receipt only if its `executor_signature` (when
    /// present) verifies against one of the caller-supplied executor public
    /// keys.
    pub fn with_executor_signing_key(mut self, signing_key_seed: [u8; 32]) -> Self {
        self.executor_signing_key = Some(signing_key_seed);
        self
    }

    /// Set the executor signing key after construction.
    pub fn set_executor_signing_key(&mut self, signing_key_seed: [u8; 32]) {
        self.executor_signing_key = Some(signing_key_seed);
    }

    /// Equip the executor with an X25519 keypair so it can decrypt
    /// `EncryptedTurn` submissions.
    ///
    /// `secret` is the 32-byte X25519 static secret (the unsealer);
    /// the public key is derived from it. After this call, callers may
    /// invoke `execute_encrypted_turn` and pass `EncryptedTurn` envelopes
    /// that bind to `public`. Without this key, the executor cannot
    /// participate in the privacy path.
    pub fn with_turn_decryption_secret(mut self, secret: [u8; 32]) -> Self {
        let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        self.turn_decryption_keypair = Some((secret, *public.as_bytes()));
        self
    }

    /// Set the X25519 turn-decryption secret after construction.
    pub fn set_turn_decryption_secret(&mut self, secret: [u8; 32]) {
        let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        self.turn_decryption_keypair = Some((secret, *public.as_bytes()));
    }

    /// Cav-Codex Block 2: equip the executor with a witnessed-predicate
    /// registry. Programs that declare `Witnessed` / `TemporalPredicate` /
    /// `Custom` / `SenderAuthorized { BlindedSet }` slot caveats will
    /// dispatch through this registry to verify proof bytes carried in
    /// the action's `witness_blobs`.
    pub fn with_witnessed_registry(
        mut self,
        registry: dregg_cell::WitnessedPredicateRegistry,
    ) -> Self {
        self.witnessed_registry = Some(registry);
        self
    }
    /// Set the witnessed-predicate registry after construction.
    pub fn set_witnessed_registry(&mut self, registry: dregg_cell::WitnessedPredicateRegistry) {
        self.witnessed_registry = Some(registry);
    }

    /// Set the [`Effect::Custom`] verifier registry after construction.
    ///
    /// When set, the proof-carrying turn path consults this registry
    /// **before** falling back to `program_registry`, so app-defined
    /// custom effects (whose canonical bytes are not `CellProgram`s)
    /// can be dispatched through a unified surface.
    pub fn set_custom_effect_registry(&mut self, registry: dregg_cell::CustomEffectRegistry) {
        self.custom_effect_registry = Some(registry);
    }

    /// Return the X25519 public key callers should encrypt to (if set).
    pub fn turn_decryption_public(&self) -> Option<[u8; 32]> {
        self.turn_decryption_keypair.map(|(_, pub_key)| pub_key)
    }

    /// Decrypt and execute an `EncryptedTurn` envelope.
    ///
    /// This is the production wiring for the privacy-preserving turn path
    /// (AUDIT-privacy.md §11.2: previously `EncryptedTurn` was exported but
    /// never consumed by the executor). Flow:
    ///
    /// 1. Verify the envelope's metadata (agent/conflict-set/turn-commitment
    ///    bindings via `EncryptedTurn::verify_metadata`).
    /// 2. Decrypt the ciphertext using the executor's static X25519 secret +
    ///    the sender's ephemeral public key. The decrypt path also re-checks
    ///    the turn commitment over the recovered plaintext.
    /// 3. Dispatch the recovered `Turn` to the standard `execute` path.
    ///
    /// The executor must have been configured with
    /// `with_turn_decryption_secret`; otherwise this returns a `Rejected`
    /// result.
    ///
    /// SECURITY: The agent in the recovered turn MUST match the envelope's
    /// claimed `agent` field. A mismatch is treated as a Byzantine submission
    /// and the turn is rejected. This binds the public-side fee/nonce
    /// preflight to the actual turn body.
    pub fn execute_encrypted_turn(
        &self,
        encrypted: &crate::encrypted::EncryptedTurn,
        ledger: &mut Ledger,
    ) -> TurnResult {
        // 1. Metadata consistency check (agent/conflict-set/turn-commitment
        //    bindings inside the validity proof's public inputs).
        if let Err(e) = encrypted.verify_metadata() {
            return TurnResult::Rejected {
                reason: TurnError::InvalidEffect {
                    reason: format!("encrypted turn metadata invalid: {:?}", e),
                },
                at_action: vec![],
            };
        }

        // 2. Decrypt with the executor's X25519 secret.
        let (secret, public) = match self.turn_decryption_keypair {
            Some(kp) => kp,
            None => {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: "executor has no turn_decryption_keypair configured; \
                                 EncryptedTurn cannot be processed"
                            .to_string(),
                    },
                    at_action: vec![],
                };
            }
        };
        let turn = match encrypted.decrypt_for_executor(&secret, &public) {
            Ok(t) => t,
            Err(e) => {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("encrypted turn decryption failed: {:?}", e),
                    },
                    at_action: vec![],
                };
            }
        };

        // 3. Agent binding: the decrypted turn's agent must equal the
        //    cleartext-side `agent` field. Otherwise the validity-proof's
        //    fee/nonce preflight was done against a different agent than
        //    the one the executor would now charge.
        if turn.agent != encrypted.agent {
            return TurnResult::Rejected {
                reason: TurnError::InvalidEffect {
                    reason: "encrypted turn agent mismatch: decrypted turn.agent != envelope.agent"
                        .to_string(),
                },
                at_action: vec![],
            };
        }

        // 4. Dispatch to the standard execution path. All the usual
        //    nullifier-set, ledger, and conservation gates apply.
        //
        // BOUNDARIES.md §5: flip the `was_encrypted` bit on the receipt
        // (cleartext-inside the executor; bound into `receipt_hash` and
        // the executor signature). External observers see only that
        // some receipt was produced via the privacy path — nothing about
        // the inner turn's content leaks through this flag.
        let result = self.execute(&turn, ledger);
        match result {
            TurnResult::Committed {
                ledger_delta,
                mut receipt,
                computrons_used,
            } => {
                receipt.was_encrypted = true;
                // Re-sign so the executor signature covers the new bit.
                // (The signature's canonical message doesn't currently include
                // `was_encrypted`, but `receipt_hash` does — and any downstream
                // verifier that recomputes `receipt_hash` would fail without
                // this resign step.)
                receipt.executor_signature = self.maybe_sign_receipt(&receipt);
                // Rebind the per-agent chain head to the post-flip hash.
                self.record_receipt_hash(receipt.agent, receipt.receipt_hash());
                TurnResult::Committed {
                    ledger_delta,
                    receipt,
                    computrons_used,
                }
            }
            other => other,
        }
    }

    /// **Canonical** encrypted-turn entry point (AUDIT-privacy.md §11.2):
    /// decrypt an `EncryptedTurn` with the supplied X25519 unsealer secret,
    /// recover the underlying `Turn`, apply it through the normal executor,
    /// and return the `TurnReceipt` (with `was_encrypted = true`).
    ///
    /// This is the production wiring node-level callers (HTTP / MCP) hit
    /// when forwarding an `EncryptedTurn` envelope. Unlike
    /// [`Self::execute_encrypted_turn`] (which mutates the executor's
    /// `turn_decryption_keypair`), this method accepts the sealer secret
    /// explicitly — useful when the secret is held in an HSM-style wrapper
    /// or when a single executor process serves multiple sealer pairs.
    ///
    /// The `sealer_secret` is the 32-byte X25519 static secret (`unsealer_secret`
    /// in `cell/src/seal.rs` terminology). The public key is recomputed from it
    /// so the decrypt path can verify the BLAKE3-key-derivation salt.
    ///
    /// # Errors
    ///
    /// Returns `TurnError::InvalidEffect { reason }` when:
    /// - the envelope's metadata fails self-consistency (`verify_metadata`),
    /// - decryption fails (wrong key / tampered ciphertext → Poly1305 MAC fail),
    /// - the decrypted `turn.agent` does not match `envelope.agent` (binding
    ///   the public-side fee/nonce preflight to the actual turn body), or
    /// - the inner turn was rejected by `execute` (insufficient fee, replayed
    ///   nullifier, broken receipt chain, etc.).
    pub fn apply_encrypted_turn(
        &self,
        encrypted: &crate::encrypted::EncryptedTurn,
        sealer_secret: &[u8; 32],
        ledger: &mut Ledger,
    ) -> Result<TurnReceipt, TurnError> {
        // 1. Metadata consistency.
        encrypted
            .verify_metadata()
            .map_err(|e| TurnError::InvalidEffect {
                reason: format!("encrypted turn metadata invalid: {:?}", e),
            })?;

        // 2. Recompute the public key from the secret and decrypt.
        let public = {
            let pk =
                x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(*sealer_secret));
            *pk.as_bytes()
        };
        let turn = encrypted
            .decrypt_for_executor(sealer_secret, &public)
            .map_err(|e| TurnError::InvalidEffect {
                reason: format!("encrypted turn decryption failed: {:?}", e),
            })?;

        // 3. Agent binding: the cleartext envelope.agent (used by the
        //    federation for fee/nonce preflight) must equal the inner
        //    turn.agent the executor would actually charge.
        if turn.agent != encrypted.agent {
            return Err(TurnError::InvalidEffect {
                reason: "encrypted turn agent mismatch: decrypted turn.agent != envelope.agent"
                    .to_string(),
            });
        }

        // 4. Apply through the standard execute path.
        match self.execute(&turn, ledger) {
            TurnResult::Committed { mut receipt, .. } => {
                receipt.was_encrypted = true;
                receipt.executor_signature = self.maybe_sign_receipt(&receipt);
                // Rebind the per-agent chain head to the post-flip hash so
                // the next turn's `previous_receipt_hash` check uses the
                // committed value.
                self.record_receipt_hash(receipt.agent, receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(reason),
            TurnResult::Expired => Err(TurnError::InvalidEffect {
                reason: "encrypted turn expired before application".to_string(),
            }),
            TurnResult::Pending => Err(TurnError::InvalidEffect {
                reason: "encrypted turn returned Pending (conditional encrypted turns \
                         are out of scope for apply_encrypted_turn)"
                    .to_string(),
            }),
        }
    }

    /// Sign `receipt.receipt_hash()` with the executor's signing key if one
    /// is configured, returning the 64-byte signature bytes for embedding in
    /// `receipt.executor_signature`. Returns `None` when no key is set —
    /// callers should leave `executor_signature` as `None` in that case.
    fn maybe_sign_receipt(&self, receipt: &TurnReceipt) -> Option<Vec<u8>> {
        let seed = self.executor_signing_key.as_ref()?;
        let sk = ed25519_dalek::SigningKey::from_bytes(seed);
        // Stage 9 R-4: sign the canonical narrow message
        // (`executor-receipt-sig-v1:` || turn_hash || pre_state || post_state ||
        // timestamp), not the broader `receipt_hash()`. This keeps the
        // executor's claim recoverable by downstream verifiers that do not yet
        // understand the v2 receipt's auxiliary fields (routing directives,
        // derivation records, emitted events, finality). See
        // `TurnReceipt::canonical_executor_signed_message`.
        let msg = receipt.canonical_executor_signed_message();
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg);
        Some(sig.to_bytes().to_vec())
    }

    /// Set the current timestamp (used for expiration and precondition checks).
    ///
    /// P2-2: rejects backwards timestamp updates. The executor's clock must be
    /// monotonically non-decreasing; a stuck/backward clock allows expired
    /// turns to succeed and breaks `valid_until` enforcement. Backward-stepping
    /// `ts` values are silently ignored (no-op).
    pub fn set_timestamp(&mut self, ts: i64) {
        if ts >= self.current_timestamp {
            self.current_timestamp = ts;
        }
        // else: silently ignore (do not allow time to go backwards).
    }

    /// Get the per-agent last-known receipt hash, if any (P0-3 fix).
    ///
    /// Used by callers that need to construct a turn with the correct
    /// `previous_receipt_hash` value. Returns `None` if the agent has no
    /// committed turns on this executor.
    pub fn get_last_receipt_hash(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied()
    }

    /// Seed the receipt-chain head for an agent (for state recovery / loading).
    ///
    /// Use this when an executor is started against a ledger that already has
    /// history (e.g. after restart) so the receipt-chain check reflects the
    /// actual prior state. Without seeding, the first turn from an agent with
    /// pre-existing history would be rejected as `ReceiptChainMismatch`.
    pub fn set_last_receipt_hash(&self, agent: CellId, hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, hash);
    }

    /// Clear the per-agent receipt-chain head (for tests and resets).
    pub fn reset_receipt_chain(&self) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
    }

    /// Check whether a cell is frozen for migration (P0-4 fix).
    ///
    /// Returns `Err(TurnError::CellFrozen { cell })` if the cell is in
    /// `MigrationState::Frozen` or `AwaitingReceipt`; `Ok(())` otherwise.
    /// Called near the top of every turn-execution path that mutates state.
    fn check_not_frozen(&self, cell: &CellId) -> Result<(), TurnError> {
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(cell)
        {
            Err(TurnError::CellFrozen { cell: *cell })
        } else {
            Ok(())
        }
    }

    /// Verify the agent's `previous_receipt_hash` matches the executor's
    /// stored head for that agent (P0-3 fix).
    fn check_previous_receipt_hash(
        &self,
        agent: &CellId,
        claimed: Option<[u8; 32]>,
    ) -> Result<(), TurnError> {
        let stored = self
            .last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied();
        if stored == claimed {
            Ok(())
        } else {
            Err(TurnError::ReceiptChainMismatch {
                expected: stored,
                got: claimed,
            })
        }
    }

    /// Record a receipt as the new chain-head for the agent.
    fn record_receipt_hash(&self, agent: CellId, receipt_hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, receipt_hash);
    }

    /// Set the current block height (used for network preconditions).
    pub fn set_block_height(&mut self, height: u64) {
        self.block_height = height;
    }

    /// Set the block proposer cell (receives 50% of fees).
    ///
    /// When set, 50% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the proposer share is burned instead.
    pub fn set_proposer_cell(&mut self, cell_id: CellId) {
        self.proposer_cell = Some(cell_id);
    }

    /// Set the federation treasury cell (receives 30% of fees).
    ///
    /// When set, 30% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the treasury share is burned instead.
    pub fn set_treasury_cell(&mut self, cell_id: CellId) {
        self.treasury_cell = Some(cell_id);
    }

    /// Configure epoch-based computron minting to prevent deflationary deadlock.
    ///
    /// When set, the executor will mint new computrons to the treasury cell at
    /// epoch boundaries. Call [`apply_epoch_minting`](Self::apply_epoch_minting)
    /// at each block to trigger minting when appropriate.
    ///
    /// # Arguments
    ///
    /// * `minter` - The configured epoch minter with policy parameters.
    pub fn set_epoch_minter(&mut self, minter: crate::economics::EpochMinter) {
        self.epoch_minter = Some(std::cell::RefCell::new(minter));
    }

    /// Apply epoch-based minting if the current block height crosses an epoch boundary.
    ///
    /// Call this once per block (typically at block start, before processing turns).
    /// Returns `Some(MintResult)` if computrons were minted, `None` otherwise.
    ///
    /// This prevents the deflationary death spiral: since 20% of every fee is
    /// burned and no new supply is created, the system would eventually run out
    /// of computrons. Epoch minting provides controlled issuance to the treasury,
    /// which distributes via governance (staking rewards, grants, fee subsidies).
    pub fn apply_epoch_minting(
        &self,
        ledger: &mut dregg_cell::Ledger,
    ) -> Option<crate::economics::MintResult> {
        let minter_cell = self.epoch_minter.as_ref()?;
        let mut minter = minter_cell.borrow_mut();
        minter.maybe_mint(ledger, self.block_height)
    }

    /// Execute a conditional turn by first resolving its condition.
    ///
    /// This checks:
    /// 1. Whether the timeout has been exceeded (returns `TurnResult::Expired`)
    /// 2. Whether the proof satisfies the condition
    /// 3. If satisfied, executes the underlying turn normally
    ///
    /// No fee is charged if the turn expires or the condition is not met.
    pub fn execute_conditional(
        &self,
        conditional: &crate::conditional::ConditionalTurn,
        proof: &crate::conditional::ConditionProof,
        current_height: u64,
        trusted_roots: &[crate::conditional::TrustedRoot],
        max_root_age: u64,
        used_proof_hashes: &mut std::collections::HashSet<[u8; 32]>,
        ledger: &mut Ledger,
    ) -> TurnResult {
        // Check timeout.
        if current_height > conditional.timeout_height {
            return TurnResult::Expired;
        }

        // Resolve condition.
        match crate::conditional::resolve_condition(
            &conditional.condition,
            proof,
            current_height,
            conditional.timeout_height,
            trusted_roots,
            max_root_age,
            used_proof_hashes,
            &self.trusted_destination_keys,
        ) {
            crate::conditional::ConditionalResult::Resolved => {
                let result = self.execute(&conditional.turn, ledger);
                // On successful execution, refund the conditional deposit to the agent.
                if let TurnResult::Committed { .. } = &result {
                    if conditional.deposit_amount > 0 {
                        if let Some(cell) = ledger.get_mut(&conditional.turn.agent) {
                            cell.state
                                .set_balance(cell.state.balance() + conditional.deposit_amount);
                        }
                    }
                }
                result
            }
            crate::conditional::ConditionalResult::Expired => TurnResult::Expired,
            crate::conditional::ConditionalResult::Pending => TurnResult::Pending,
            crate::conditional::ConditionalResult::InvalidProof(e) => TurnResult::Rejected {
                reason: TurnError::ConditionNotMet(e),
                at_action: vec![],
            },
        }
    }

    /// Set the trusted federation roots for cross-federation note bridging.
    ///
    /// Only portable note proofs whose source_root matches one of these roots
    /// will be accepted. Call this to configure which remote federations this
    /// executor trusts for bridge mints.
    pub fn set_trusted_federation_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.trusted_federation_roots = roots;
    }

    /// Add a single trusted federation root.
    pub fn add_trusted_federation_root(&mut self, root: AttestedRoot) {
        self.trusted_federation_roots.push(root);
    }

    /// Set the local federation identity for cross-federation bridge verification.
    pub fn set_local_federation_id(&mut self, id: [u8; 32]) {
        self.local_federation_id = id;
    }

    /// Set the trusted destination federation keys for bridge receipt verification.
    ///
    /// These Ed25519 public keys are used during BridgeFinalize to verify that a
    /// receipt was signed by a legitimate destination federation.
    pub fn set_trusted_destination_keys(&mut self, keys: Vec<[u8; 32]>) {
        self.trusted_destination_keys = keys;
    }

    // ─── Unified Lace Aliases ──────────────────────────────────────────────
    //
    // In the unified blocklace model, a "federation" is a reference group (GroupId).
    // These aliases provide forward-compatible naming.

    /// Alias for [`set_trusted_federation_roots`](Self::set_trusted_federation_roots).
    /// In the unified lace model, "federation roots" are "group roots".
    pub fn set_trusted_group_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.set_trusted_federation_roots(roots);
    }

    /// Alias for [`add_trusted_federation_root`](Self::add_trusted_federation_root).
    pub fn add_trusted_group_root(&mut self, root: AttestedRoot) {
        self.add_trusted_federation_root(root);
    }

    /// Alias for [`set_local_federation_id`](Self::set_local_federation_id).
    /// In the unified lace model, the "local federation ID" is the local group ID.
    pub fn set_local_group_id(&mut self, id: [u8; 32]) {
        self.set_local_federation_id(id);
    }

    /// Add a single trusted destination federation key.
    pub fn add_trusted_destination_key(&mut self, key: [u8; 32]) {
        self.trusted_destination_keys.push(key);
    }

    /// Set the revocation channel set for capability exercise checks.
    ///
    /// When present, the executor verifies that capabilities used via
    /// `ExerciseViaCapability` and delegation access checks are not gated
    /// by a tripped revocation channel.
    pub fn set_revocation_channels(&mut self, channels: RevocationChannelSet) {
        self.revocation_channels = Some(channels);
    }

    /// Set the program registry for custom cell program verification.
    ///
    /// When a sovereign cell has a `verification_key_hash` in its registration,
    /// proof-carrying turns are verified against the deployed program instead of
    /// the default `EffectVmAir`.
    pub fn set_program_registry(&mut self, registry: ProgramRegistry) {
        self.program_registry = registry;
    }

    /// Get a mutable reference to the program registry (for deploying programs).
    pub fn program_registry_mut(&mut self) -> &mut ProgramRegistry {
        &mut self.program_registry
    }

    /// Set the queue program registry for enqueue validation.
    ///
    /// When an `EnqueueMessage` effect targets a queue with a registered program,
    /// the executor validates the enqueue against the program's constraints before
    /// accepting the effect. Invalid enqueues are rejected.
    pub fn set_queue_program_registry(
        &mut self,
        registry: crate::queue_programs::QueueProgramRegistry,
    ) {
        self.queue_program_registry = registry;
    }

    /// Get a mutable reference to the queue program registry.
    pub fn queue_program_registry_mut(
        &mut self,
    ) -> &mut crate::queue_programs::QueueProgramRegistry {
        &mut self.queue_program_registry
    }

    /// Get a mutable reference to the factory registry (for deploying factories).
    pub fn factory_registry_mut(&mut self) -> std::cell::RefMut<'_, dregg_cell::FactoryRegistry> {
        self.factory_registry.borrow_mut()
    }

    /// Deploy a factory into the executor's registry.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        self.factory_registry.borrow_mut().deploy(descriptor)
    }
}

// ─── Decomposed Implementation Modules ──────────────────────────────────────

mod apply;
mod authorize;
mod execute;
mod execute_tree;
mod finalize;
mod proof_verify;

// ─── Pipeline Execution ──────────────────────────────────────────────────────

mod pipeline;
pub use pipeline::{
    ResolutionTable, execute_pipeline, execute_pipeline_result, resolve_eventual_ref,
    resolve_output_ref,
};

mod atomic;
pub use atomic::{
    AtomicProofEntry, AtomicSovereignTurn, AtomicTurnError, MixedAtomicResult, MixedAtomicTurn,
};
