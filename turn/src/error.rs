//! Error types for turn execution failures.
//!
//! TurnError covers all the ways a turn can fail: authorization issues,
//! precondition violations, resource limits, and structural problems.

use pyana_cell::{AuthRequired, CellId, ChannelId};
use serde::{Deserialize, Serialize};

/// All possible failure modes when executing a turn.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TurnError {
    /// The source cell doesn't have enough computrons for a transfer.
    InsufficientBalance {
        cell: CellId,
        required: u64,
        available: u64,
    },

    /// The provided authorization doesn't satisfy the cell's permission requirements.
    PermissionDenied {
        cell: CellId,
        action: String,
        required: AuthRequired,
    },

    /// A precondition check failed.
    PreconditionFailed { description: String },

    /// The authorization was structurally invalid (e.g., bad signature format).
    InvalidAuthorization { reason: String },

    /// The target cell doesn't exist in the ledger.
    CellNotFound { id: CellId },

    /// An action tried to act on a cell it has no capability to reach.
    CapabilityNotHeld { actor: CellId, target: CellId },

    /// The turn's nonce doesn't match the expected nonce for the agent cell.
    NonceReplay { expected: u64, got: u64 },

    /// The turn's valid_until timestamp has passed.
    Expired { valid_until: i64, now: i64 },

    /// The turn exceeded its computron budget.
    BudgetExceeded { limit: u64, used: u64 },

    /// A child action tried to use delegation but the parent disallowed it.
    DelegationDenied {
        parent: CellId,
        child_target: CellId,
    },

    /// State field index out of bounds.
    InvalidFieldIndex { cell: CellId, index: usize },

    /// A cell that was supposed to be created already exists.
    CellAlreadyExists { id: CellId },

    /// The call forest is empty (no actions to execute).
    EmptyForest,

    /// Transfer destination cell not found.
    TransferDestNotFound { id: CellId },

    /// Balance overflow on receiving cell.
    BalanceOverflow { cell: CellId },

    /// CreateCell was called with a non-zero initial balance.
    CreateCellNonZeroBalance { cell: CellId, balance: u64 },

    /// The sum of all balance_change deltas in the turn is not zero.
    /// This violates the conservation law: withdrawals must be matched by deposits.
    ExcessNotZero { excess: i64 },

    /// A balance_change would underflow the target cell's balance (withdrawal exceeds holdings).
    BalanceChangeUnderflow {
        cell: CellId,
        current: u64,
        delta: i64,
    },

    /// The cell's program rejected the state transition.
    ProgramViolation { cell: CellId, reason: String },

    /// Note conservation law violated: for a given asset type, the total value
    /// of spent notes does not equal the total value of created notes.
    NoteConservationViolation {
        asset_type: u64,
        inputs: u64,
        outputs: u64,
    },
    /// Three-party introduction denied.
    IntroductionDenied {
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        reason: String,
    },

    /// The silo's budget slice is exhausted (Stingray bounded counter).
    /// The turn was rejected before execution because the BudgetGate's
    /// local slice cannot cover the requested fee.
    BudgetExhausted {
        silo_id: u32,
        requested: u64,
        remaining: u64,
    },

    /// A conditional turn's condition was not satisfied by the presented proof.
    ConditionNotMet(String),

    /// The fee provided for a conditional turn is less than the required reservation deposit.
    /// Deposit = BASE_CONDITIONAL_DEPOSIT + PER_BLOCK_DEPOSIT * blocks_until_timeout.
    InsufficientConditionalDeposit { required: u64, provided: u64 },

    /// A BridgeMint effect failed verification (untrusted root, invalid proof,
    /// or double-bridge attempt).
    BridgeMintFailed { reason: String },

    /// A BridgeLock effect failed (note already locked, etc.).
    BridgeLockFailed { reason: String },

    /// A BridgeFinalize effect failed (invalid receipt, bridge not found, etc.).
    BridgeFinalizeFailed { reason: String },

    /// A BridgeCancel effect failed (timeout not reached, bridge not found, etc.).
    BridgeCancelFailed { reason: String },

    /// A delegated capability snapshot is stale (exceeded max_staleness).
    /// The delegation must be refreshed before it can be exercised.
    StaleDelegation {
        actor: CellId,
        source: CellId,
        refreshed_at: u64,
        max_staleness: u64,
        now: u64,
    },

    /// A delegated capability has been revoked via its revocation channel.
    /// The channel was tripped, meaning the capability is no longer valid.
    CapabilityRevoked {
        actor: CellId,
        channel_id: ChannelId,
        tripped_at: u64,
    },

    /// The capability slot counter overflowed (2^32 grants exhausted).
    CapabilitySlotOverflow { cell: CellId },

    /// An effect was structurally invalid (malformed data, null identifiers, etc.).
    InvalidEffect { reason: String },

    /// Committed (Pedersen) conservation check failed: the Schnorr proof over the
    /// excess commitment is invalid, indicating value is not conserved.
    CommittedConservationFailed { reason: String },

    /// A turn targets a sovereign cell but no witness was provided.
    SovereignWitnessRequired { cell: CellId },

    /// The sovereign cell witness commitment does not match the stored commitment.
    SovereignCommitmentMismatch {
        cell: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },

    /// A proof-carrying turn targets a cell that is not sovereign.
    ProofCarryingRequiresSovereign { cell: CellId },

    /// The execution proof bytes could not be deserialized into a valid STARK proof.
    InvalidExecutionProof(String),

    /// The effects hash in the proof's public inputs does not match the turn's actual effects.
    EffectsHashMismatch { expected: [u8; 32], got: [u8; 32] },

    /// The STARK proof verification failed.
    ProofVerificationFailed(String),

    /// The cell targeted by a proof-carrying turn has no stored sovereign commitment.
    SovereignNotRegistered { cell: CellId },

    /// A faceted capability was exercised with an effect type not permitted by its mask.
    ///
    /// In E-language terms, this is a facet violation: the capability holder tried to
    /// invoke a method not exposed by the faceted view of the target object.
    FacetViolation {
        actor: CellId,
        target: CellId,
        cap_slot: u32,
        attempted_effect: String,
        allowed_mask: u32,
    },

    /// A breadstuff (capability token) has expired.
    BreadstuffExpired {
        actor: CellId,
        target: CellId,
        expires_at: u64,
        current_height: u64,
    },

    /// A breadstuff (capability token) has been revoked via its revocation channel.
    BreadstuffRevoked {
        actor: CellId,
        target: CellId,
        channel_id: ChannelId,
    },

    /// A breadstuff (capability token) was exercised with an effect not permitted by its facet.
    BreadstuffFacetViolation {
        actor: CellId,
        target: CellId,
        attempted_effects_mask: u32,
        allowed_mask: u32,
    },

    /// A bearer capability was exercised with effects not permitted by its facet mask.
    BearerCapFacetViolation {
        target: CellId,
        attempted_effects_mask: u32,
        allowed_mask: u32,
    },

    /// A bearer capability's facet exceeds the delegator's facet (amplification).
    BearerCapFacetAmplification {
        target: CellId,
        delegator_mask: u32,
        bearer_mask: u32,
    },

    /// A bearer capability proof has expired.
    BearerCapExpired {
        target: CellId,
        expires_at: u64,
        current_height: u64,
    },

    /// A bearer capability's revocation channel has been tripped.
    BearerCapRevoked {
        target: CellId,
        channel_id: ChannelId,
    },

    /// A bearer capability's delegation proof is invalid (bad signature, bad STARK proof, etc.).
    BearerCapInvalidProof { target: CellId, reason: String },

    /// A bearer capability attempts to amplify permissions beyond what the delegator holds.
    BearerCapAmplification {
        target: CellId,
        delegator_permissions: AuthRequired,
        bearer_permissions: AuthRequired,
    },

    /// A bearer capability references a delegator who does not hold the required capability.
    BearerCapDelegatorLacksCapability { delegator: CellId, target: CellId },

    /// A custom proof commitment in the Effect VM's public inputs does not match
    /// the hash of the provided custom proof bytes.
    CustomProofCommitmentMismatch {
        index: usize,
        expected: [u8; 16],
        got: [u8; 16],
    },

    /// A custom program referenced by VK hash in a Custom effect is not deployed.
    CustomProgramNotFound { index: usize, vk_hash: [u8; 32] },

    /// A custom program's proof verification failed.
    CustomProgramVerificationFailed {
        index: usize,
        program_vk: [u8; 32],
        reason: String,
    },

    /// The cell is frozen for migration to another federation.
    ///
    /// Turns may not execute against cells in `MigrationState::Frozen` or
    /// `AwaitingReceipt`. Migrations are a two-phase protocol; while a cell is
    /// in a migrating state the source federation must not mutate it (otherwise
    /// the destination's snapshot diverges).
    CellFrozen { cell: CellId },

    /// The agent's `previous_receipt_hash` does not match the prior receipt
    /// the executor has on file for this agent. Either:
    /// - `expected: Some(h)`, `got: Some(other)` -- chain branch / replay
    /// - `expected: Some(h)`, `got: None` -- agent has a history but submitted
    ///   as if genesis
    /// - `expected: None`, `got: Some(_)` -- agent claims a prior receipt but
    ///   the executor has none on file
    ///
    /// This is the executor-side enforcement of "self-bound history" (the
    /// receipt-chain property documented on `TurnReceipt`). Prior to this
    /// check, the property was only enforced off-chain by verifiers in
    /// possession of the full chain.
    ReceiptChainMismatch {
        expected: Option<[u8; 32]>,
        got: Option<[u8; 32]>,
    },

    /// `Authorization::Custom` named a `WitnessedPredicateKind` (built-in
    /// discriminant or `Custom { vk_hash }`) that the executor's
    /// `WitnessedPredicateRegistry` does not have a verifier for.
    ///
    /// Per AUTHORIZATION-CUSTOM-DESIGN §2 step 3 ("Registry lookup …
    /// No silent fallback. The mode must be on the federation's
    /// allowlist") and §8.6 (T18 — verifier version drift): turns that
    /// reference an unregistered auth mode are rejected closed.
    AuthModeNotRegistered {
        /// Human-readable discriminant name for built-ins, or
        /// `"Custom"` for `WitnessedPredicateKind::Custom`.
        kind: String,
        /// 32-byte verifier-key hash, set for `Custom` kinds; zeroed for
        /// built-ins (the built-in identity is in `kind`).
        vk_hash: [u8; 32],
    },

    /// An action carries `Effect::Refusal { cell, .. }` alongside another
    /// state-mutating effect (`SetField`, `SetPermissions`,
    /// `SetVerificationKey`, `Transfer`, `GrantCapability`,
    /// `RevokeCapability`) on the *same* cell.
    ///
    /// `Refusal` is the categorical "evidence of non-action"
    /// (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3) — a structural
    /// attestation that the prover did NOT act. Co-occurring it with a
    /// real mutation on the same target collapses the semantics: was
    /// the action refused, or taken? The executor rejects the action
    /// closed rather than silently picking an order.
    ///
    /// Per task-1 of the 2026-05-25 lane-honesty sweep.
    RefusalConflictsWithMutation {
        /// The cell whose refusal collides with a co-occurring
        /// state-mutating effect.
        cell: CellId,
        /// Human-readable name of the conflicting effect for triage.
        conflicting_effect: &'static str,
    },
}

impl core::fmt::Display for TurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnError::InsufficientBalance {
                cell,
                required,
                available,
            } => {
                write!(
                    f,
                    "insufficient balance on cell {cell}: need {required}, have {available}"
                )
            }
            TurnError::PermissionDenied {
                cell,
                action,
                required,
            } => {
                write!(
                    f,
                    "permission denied on cell {cell} for action '{action}': requires {required:?}"
                )
            }
            TurnError::PreconditionFailed { description } => {
                write!(f, "precondition failed: {description}")
            }
            TurnError::InvalidAuthorization { reason } => {
                write!(f, "invalid authorization: {reason}")
            }
            TurnError::CellNotFound { id } => {
                write!(f, "cell not found: {id}")
            }
            TurnError::CapabilityNotHeld { actor, target } => {
                write!(f, "cell {actor} has no capability to reach cell {target}")
            }
            TurnError::NonceReplay { expected, got } => {
                write!(f, "nonce replay: expected {expected}, got {got}")
            }
            TurnError::Expired { valid_until, now } => {
                write!(f, "turn expired: valid_until={valid_until}, now={now}")
            }
            TurnError::BudgetExceeded { limit, used } => {
                write!(f, "computron budget exceeded: limit={limit}, used={used}")
            }
            TurnError::DelegationDenied {
                parent,
                child_target,
            } => {
                write!(
                    f,
                    "delegation denied: parent {parent} does not delegate to child targeting {child_target}"
                )
            }
            TurnError::InvalidFieldIndex { cell, index } => {
                write!(f, "invalid field index {index} for cell {cell}")
            }
            TurnError::CellAlreadyExists { id } => {
                write!(f, "cell already exists: {id}")
            }
            TurnError::EmptyForest => {
                write!(f, "call forest is empty")
            }
            TurnError::TransferDestNotFound { id } => {
                write!(f, "transfer destination not found: {id}")
            }
            TurnError::BalanceOverflow { cell } => {
                write!(f, "balance overflow on cell {cell}")
            }
            TurnError::CreateCellNonZeroBalance { cell, balance } => {
                write!(
                    f,
                    "CreateCell requires zero initial balance, got {balance} for cell {cell}"
                )
            }
            TurnError::ExcessNotZero { excess } => {
                write!(
                    f,
                    "excess not zero at turn end: {excess} (conservation law violated)"
                )
            }
            TurnError::BalanceChangeUnderflow {
                cell,
                current,
                delta,
            } => {
                write!(
                    f,
                    "balance_change underflow on cell {cell}: balance={current}, delta={delta}"
                )
            }
            TurnError::ProgramViolation { cell, reason } => {
                write!(f, "program violation on cell {cell}: {reason}")
            }
            TurnError::NoteConservationViolation {
                asset_type,
                inputs,
                outputs,
            } => {
                write!(
                    f,
                    "note conservation violated for asset {asset_type}: inputs={inputs}, outputs={outputs}"
                )
            }
            TurnError::IntroductionDenied {
                introducer,
                recipient,
                target,
                reason,
            } => {
                write!(
                    f,
                    "introduction denied: {introducer} cannot introduce {recipient} to {target}: {reason}"
                )
            }
            TurnError::BudgetExhausted {
                silo_id,
                requested,
                remaining,
            } => {
                write!(
                    f,
                    "budget exhausted on silo {silo_id}: requested {requested}, remaining {remaining}"
                )
            }
            TurnError::ConditionNotMet(reason) => {
                write!(f, "conditional turn condition not met: {reason}")
            }
            TurnError::InsufficientConditionalDeposit { required, provided } => {
                write!(
                    f,
                    "insufficient conditional deposit: required {required}, provided {provided}"
                )
            }
            TurnError::BridgeMintFailed { reason } => {
                write!(f, "bridge mint failed: {reason}")
            }
            TurnError::BridgeLockFailed { reason } => {
                write!(f, "bridge lock failed: {reason}")
            }
            TurnError::BridgeFinalizeFailed { reason } => {
                write!(f, "bridge finalize failed: {reason}")
            }
            TurnError::BridgeCancelFailed { reason } => {
                write!(f, "bridge cancel failed: {reason}")
            }
            TurnError::StaleDelegation {
                actor,
                source,
                refreshed_at,
                max_staleness,
                now,
            } => {
                write!(
                    f,
                    "stale delegation: actor {actor}'s delegation from {source} expired \
                     (refreshed_at={refreshed_at}, max_staleness={max_staleness}, now={now})"
                )
            }
            TurnError::CapabilityRevoked {
                actor,
                channel_id,
                tripped_at,
            } => {
                write!(
                    f,
                    "capability revoked: actor {actor}'s delegation revoked via channel \
                     {:02x}{:02x}... (tripped_at={tripped_at})",
                    channel_id[0], channel_id[1]
                )
            }
            TurnError::CapabilitySlotOverflow { cell } => {
                write!(
                    f,
                    "capability slot counter overflow on cell {cell} (2^32 grants exhausted)"
                )
            }
            TurnError::InvalidEffect { reason } => {
                write!(f, "invalid effect: {reason}")
            }
            TurnError::CommittedConservationFailed { reason } => {
                write!(f, "committed conservation failed: {reason}")
            }
            TurnError::SovereignWitnessRequired { cell } => {
                write!(
                    f,
                    "sovereign cell {cell} targeted but no witness provided in turn"
                )
            }
            TurnError::SovereignCommitmentMismatch {
                cell,
                expected,
                got,
            } => {
                write!(
                    f,
                    "sovereign commitment mismatch for cell {cell}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
            TurnError::ProofCarryingRequiresSovereign { cell } => {
                write!(f, "proof-carrying turn targets non-sovereign cell {cell}")
            }
            TurnError::InvalidExecutionProof(reason) => {
                write!(f, "invalid execution proof: {reason}")
            }
            TurnError::EffectsHashMismatch { expected, got } => {
                write!(
                    f,
                    "effects hash mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
            TurnError::ProofVerificationFailed(reason) => {
                write!(f, "execution proof verification failed: {reason}")
            }
            TurnError::SovereignNotRegistered { cell } => {
                write!(
                    f,
                    "sovereign cell {cell} not registered (no stored commitment)"
                )
            }
            TurnError::FacetViolation {
                actor,
                target,
                cap_slot,
                attempted_effect,
                allowed_mask,
            } => {
                write!(
                    f,
                    "facet violation: actor {actor} tried {attempted_effect} on target {target} \
                     via cap slot {cap_slot}, but capability mask 0x{allowed_mask:08x} does not permit it"
                )
            }
            TurnError::BreadstuffExpired {
                actor,
                target,
                expires_at,
                current_height,
            } => {
                write!(
                    f,
                    "breadstuff expired: actor {actor} -> target {target}, \
                     expires_at={expires_at}, current_height={current_height}"
                )
            }
            TurnError::BreadstuffRevoked {
                actor,
                target,
                channel_id,
            } => {
                write!(
                    f,
                    "breadstuff revoked: actor {actor} -> target {target}, \
                     channel {:02x}{:02x}...",
                    channel_id[0], channel_id[1]
                )
            }
            TurnError::BreadstuffFacetViolation {
                actor,
                target,
                attempted_effects_mask,
                allowed_mask,
            } => {
                write!(
                    f,
                    "breadstuff facet violation: actor {actor} -> target {target}, \
                     attempted 0x{attempted_effects_mask:08x} but allowed 0x{allowed_mask:08x}"
                )
            }
            TurnError::BearerCapFacetViolation {
                target,
                attempted_effects_mask,
                allowed_mask,
            } => {
                write!(
                    f,
                    "bearer cap facet violation: target {target}, \
                     attempted 0x{attempted_effects_mask:08x} but allowed 0x{allowed_mask:08x}"
                )
            }
            TurnError::BearerCapFacetAmplification {
                target,
                delegator_mask,
                bearer_mask,
            } => {
                write!(
                    f,
                    "bearer cap facet amplification: target {target}, \
                     bearer mask 0x{bearer_mask:08x} exceeds delegator mask 0x{delegator_mask:08x}"
                )
            }
            TurnError::BearerCapExpired {
                target,
                expires_at,
                current_height,
            } => {
                write!(
                    f,
                    "bearer cap expired: target {target}, expires_at={expires_at}, current_height={current_height}"
                )
            }
            TurnError::BearerCapRevoked { target, channel_id } => {
                write!(
                    f,
                    "bearer cap revoked: target {target}, channel {:02x}{:02x}...",
                    channel_id[0], channel_id[1]
                )
            }
            TurnError::BearerCapInvalidProof { target, reason } => {
                write!(f, "bearer cap invalid proof for target {target}: {reason}")
            }
            TurnError::BearerCapAmplification {
                target,
                delegator_permissions,
                bearer_permissions,
            } => {
                write!(
                    f,
                    "bearer cap amplification on target {target}: bearer has {bearer_permissions:?} \
                     but delegator only holds {delegator_permissions:?}"
                )
            }
            TurnError::BearerCapDelegatorLacksCapability { delegator, target } => {
                write!(
                    f,
                    "bearer cap delegator {delegator} does not hold capability to target {target}"
                )
            }
            TurnError::CustomProofCommitmentMismatch {
                index,
                expected,
                got,
            } => {
                write!(
                    f,
                    "custom proof commitment mismatch at index {index}: expected {expected:02x?}, got {got:02x?}"
                )
            }
            TurnError::CustomProgramNotFound { index, vk_hash } => {
                write!(
                    f,
                    "custom program not found at index {index}: vk_hash {:02x}{:02x}...",
                    vk_hash[0], vk_hash[1]
                )
            }
            TurnError::CustomProgramVerificationFailed {
                index,
                program_vk,
                reason,
            } => {
                write!(
                    f,
                    "custom program verification failed at index {index} (vk {:02x}{:02x}...): {reason}",
                    program_vk[0], program_vk[1]
                )
            }
            TurnError::CellFrozen { cell } => {
                write!(
                    f,
                    "cell {cell} is frozen for migration; no turns may execute against it"
                )
            }
            TurnError::AuthModeNotRegistered { kind, vk_hash } => {
                write!(
                    f,
                    "authorization mode not registered: kind={kind}, vk_hash={:02x}{:02x}...",
                    vk_hash[0], vk_hash[1]
                )
            }
            TurnError::ReceiptChainMismatch { expected, got } => {
                fn fmt_hash(o: &Option<[u8; 32]>) -> String {
                    match o {
                        Some(h) => format!("Some({:02x}{:02x}...)", h[0], h[1]),
                        None => "None".to_string(),
                    }
                }
                write!(
                    f,
                    "receipt chain mismatch: expected {}, got {}",
                    fmt_hash(expected),
                    fmt_hash(got)
                )
            }
            TurnError::RefusalConflictsWithMutation {
                cell,
                conflicting_effect,
            } => {
                write!(
                    f,
                    "Effect::Refusal on cell {cell} conflicts with co-occurring \
                     state-mutating effect '{conflicting_effect}' on the same cell: \
                     refusal is evidence-of-non-action and cannot coexist with a \
                     real mutation in the same action"
                )
            }
        }
    }
}

impl std::error::Error for TurnError {}
