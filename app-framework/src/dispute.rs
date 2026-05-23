//! Optimistic dispute/slashing framework for pyana apps.
//!
//! # Design Philosophy
//!
//! You cannot prove "I actually computed X" inside a STARK unless you run the entire
//! computation inside a zkVM. The correct pattern is **optimistic execution with
//! economic enforcement**:
//!
//! 1. Provider stakes (CreateObligation)
//! 2. Provider submits a **claim** (attestation of delivered metrics)
//! 3. Dispute window opens (N blocks)
//! 4. If unchallenged: stake returned + payment released
//! 5. If challenged: arbiter evaluates, slashes if fraudulent
//!
//! # Generalization
//!
//! This pattern applies to ANY app where one party claims to have done something:
//! - Compute-exchange: "I computed X FLOPS"
//! - Bounty-board: "I completed the task"
//! - Gallery: "I delivered the artwork"
//! - Lending: "My collateral is still sufficient" (can be challenged by liquidators)
//!
//! Apps implement the [`Disputable`] trait with their domain-specific claim and
//! evidence types, then get the full optimistic settlement lifecycle for free.
//!
//! # Arbiter Strategies
//!
//! Who decides disputes?
//! - **Federation consensus**: finalized blocks encode the resolution (constitution
//!   members vote).
//! - **Designated arbiter cell**: a pre-agreed third party.
//! - **Cryptographic**: if the dispute can be resolved by re-executing the computation
//!   in a zkVM (SP1), the proof IS the resolution.
//!
//! For compute-exchange: cryptographic (Option C) is ideal when feasible (the
//! computation IS re-executable). For subjective disputes (quality, SLA interpretation):
//! federation consensus or designated arbiter.
//!
//! # Prior Art
//!
//! The hellas protocol prototype (~/hellas/protoproto2) had this same flow:
//! PostJob -> ClaimJob -> CommitResult -> challenge period -> FinalizeJob, with
//! disputes left as a TODO (section 10.1 of HELLAS_DESIGN_BOOK.md). This module
//! implements that TODO as a reusable framework.

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

/// Serde helper for [u8; 64] (Ed25519 signature).
mod signature_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

// =============================================================================
// Core Types
// =============================================================================

/// Unique identifier for an optimistic settlement.
pub type SettlementId = [u8; 32];

/// Unique identifier for a dispute.
pub type DisputeId = [u8; 32];

/// The lifecycle state of an optimistic settlement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SettlementState {
    /// Claim submitted, dispute window is open.
    Pending {
        /// Block height when the claim was submitted.
        submitted_at: u64,
    },
    /// Someone challenged the claim during the dispute window.
    Disputed {
        /// The challenger's identity.
        challenger: CellId,
        /// Block height when the challenge was filed.
        challenged_at: u64,
    },
    /// Dispute window closed without challenge -- ready to finalize.
    Finalized,
    /// Dispute was resolved -- one party was slashed.
    Resolved {
        /// The winning party.
        winner: CellId,
        /// The slashed party (their stake goes to winner + pool).
        slashed: CellId,
    },
    /// Settlement was cancelled before the dispute window opened (e.g. mutual agreement).
    Cancelled,
}

/// An optimistic settlement tracks a claim through its dispute lifecycle.
///
/// Generic over `C` (the claim type) so different apps can encode their own
/// domain-specific delivery attestations.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OptimisticSettlement<C> {
    /// Unique identifier for this settlement.
    pub id: SettlementId,
    /// The obligation ID backing the provider's stake.
    pub obligation_id: [u8; 32],
    /// The claimant (usually the provider).
    pub claimant: CellId,
    /// The counterparty (usually the consumer).
    pub counterparty: CellId,
    /// The claim being made.
    pub claim: C,
    /// Block height when the dispute window closes.
    pub dispute_deadline: u64,
    /// Current lifecycle state.
    pub state: SettlementState,
    /// Amount at stake (slashed on fraud).
    pub stake_amount: u64,
    /// Payment amount released on finalization.
    pub payment_amount: u64,
}

/// A delivery claim: the provider's signed attestation of what was delivered.
///
/// This is the GENERIC claim envelope. Apps embed their domain-specific metrics
/// inside `metrics_payload`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DeliveryClaim {
    /// Domain-specific metrics payload (serialized by the app).
    pub metrics_payload: Vec<u8>,
    /// Provider's Ed25519 signature over `metrics_payload`.
    #[serde(with = "signature_serde")]
    pub signature: [u8; 64],
    /// Optional STARK proof as EVIDENCE (not enforcement).
    /// If present, this strengthens the claim but is NOT the sole
    /// mechanism of enforcement. The dispute system is.
    pub proof: Option<Vec<u8>>,
}

/// Compute-specific delivery metrics (used by compute-exchange).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComputeMetrics {
    /// Total FLOPS delivered.
    pub flops_delivered: u64,
    /// Duration of the computation in seconds.
    pub duration_seconds: u64,
    /// Quality score (0-10000 basis points).
    pub quality_bps: u32,
    /// Output hash (commitment to the result).
    pub output_hash: [u8; 32],
    /// Optional: hash of input data (for re-execution verification).
    pub input_hash: Option<[u8; 32]>,
}

// =============================================================================
// Dispute Evidence
// =============================================================================

/// Evidence submitted by a challenger to dispute a claim.
///
/// Different challenge types require different evidence. The arbiter evaluates
/// the evidence to determine if the claim is fraudulent.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DisputeEvidence {
    /// "I re-ran the computation and got a different result."
    ///
    /// The strongest form of challenge for deterministic computations.
    /// If the challenger can produce a zkVM proof of correct re-execution
    /// yielding a different output, the dispute is settled cryptographically.
    ReExecutionMismatch {
        /// Hash the claimant said they produced.
        claimed_output_hash: [u8; 32],
        /// Hash the challenger produced by re-execution.
        actual_output_hash: [u8; 32],
        /// Optional ZK proof of correct re-execution (e.g. SP1 proof).
        /// If present, this constitutes cryptographic proof of fraud.
        execution_proof: Option<Vec<u8>>,
    },
    /// "The provider's STARK proof doesn't verify."
    ///
    /// If the claim included an optional STARK proof and that proof fails
    /// verification, the claim is trivially fraudulent.
    ProofInvalid {
        /// Description of the verification error.
        verification_error: String,
    },
    /// "The claimed metrics are physically impossible."
    ///
    /// E.g., claiming 100 PFLOPS from a single A100 in 1 second.
    /// Arbiter checks hardware caps from the provider's registered capabilities.
    MetricsImpossible {
        /// Human-readable explanation.
        reason: String,
        /// Maximum physically possible FLOPS for the provider's hardware.
        max_possible_flops: u64,
    },
    /// "Provider went offline during the SLA window."
    ///
    /// Uptime violations are evidenced by listing block heights where the
    /// provider's heartbeat was missing.
    UptimeViolation {
        /// Block heights where the provider's heartbeat was absent.
        missed_heartbeat_blocks: Vec<u64>,
        /// Minimum uptime required (basis points, e.g. 9500 = 95%).
        required_uptime_bps: u32,
        /// Actual uptime achieved (basis points).
        actual_uptime_bps: u32,
    },
    /// "The output is malformed or violates the job specification."
    ///
    /// Generic challenge for when output exists but is wrong/incomplete.
    OutputInvalid {
        /// Hash of the invalid output.
        output_hash: [u8; 32],
        /// Description of why it's invalid.
        reason: String,
    },
    /// Custom app-specific evidence (serialized by the app).
    Custom {
        /// Evidence type tag for the app's arbiter to dispatch on.
        evidence_type: String,
        /// Serialized evidence payload.
        payload: Vec<u8>,
    },
}

/// A dispute record tracking the challenge and its resolution.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Dispute {
    /// Unique dispute identifier.
    pub id: DisputeId,
    /// The settlement being disputed.
    pub settlement_id: SettlementId,
    /// Who filed the challenge.
    pub challenger: CellId,
    /// The evidence submitted.
    pub evidence: DisputeEvidence,
    /// Amount the challenger staked (to prevent frivolous disputes).
    pub challenger_stake: u64,
    /// Block height when the dispute was filed.
    pub filed_at: u64,
    /// Current resolution state.
    pub resolution: DisputeResolution,
}

/// Resolution state of a dispute.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DisputeResolution {
    /// Pending arbiter evaluation.
    Pending,
    /// Resolved in favor of the claimant (challenger loses stake).
    ClaimantWins {
        /// Explanation of why the challenge was rejected.
        reason: String,
    },
    /// Resolved in favor of the challenger (claimant is slashed).
    ChallengerWins {
        /// Explanation of why the claim was found fraudulent.
        reason: String,
    },
    /// Resolved by cryptographic proof (no arbiter needed).
    CryptographicResolution {
        /// Whether the claimant was found fraudulent.
        claimant_fraudulent: bool,
        /// Hash of the proof that resolved the dispute.
        proof_hash: [u8; 32],
    },
}

// =============================================================================
// Arbiter Strategy
// =============================================================================

/// How disputes are resolved. Apps select a strategy when configuring
/// their optimistic settlement flow.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ArbiterStrategy {
    /// Federation consensus: constitution members vote on the dispute.
    /// Suitable for subjective disputes (quality, SLA interpretation).
    FederationConsensus {
        /// Minimum number of votes required for resolution.
        quorum: u32,
        /// Block deadline for voting (after which default resolution applies).
        voting_deadline_blocks: u64,
    },
    /// Designated arbiter cell: a pre-agreed third party resolves disputes.
    /// Suitable for bilateral relationships with a trusted mediator.
    DesignatedArbiter {
        /// The arbiter cell's identity.
        arbiter: CellId,
        /// Block deadline for the arbiter to respond.
        response_deadline_blocks: u64,
    },
    /// Cryptographic resolution: the dispute is resolved by re-executing
    /// the computation in a zkVM. The proof IS the resolution.
    /// Suitable for deterministic computations.
    Cryptographic {
        /// The computation specification hash (for re-execution).
        computation_hash: [u8; 32],
        /// Block deadline for the challenger to produce the re-execution proof.
        proof_deadline_blocks: u64,
    },
    /// Multi-tier: try cryptographic first, fall back to federation.
    /// This is the recommended strategy for compute-exchange.
    Tiered {
        /// First try cryptographic resolution.
        cryptographic_deadline_blocks: u64,
        /// Fall back to federation if cryptographic resolution fails/times out.
        federation_quorum: u32,
        federation_deadline_blocks: u64,
    },
}

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for the optimistic settlement system.
///
/// Apps provide this when initializing their dispute infrastructure.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DisputeConfig {
    /// How many blocks the dispute window stays open.
    pub dispute_window_blocks: u64,
    /// Minimum stake required from challengers (as percentage of claimant stake).
    /// Prevents frivolous challenges.
    pub challenger_stake_pct: u8,
    /// How the arbiter resolves disputes.
    pub arbiter_strategy: ArbiterStrategy,
    /// Slash distribution: percentage of slashed stake going to the winner
    /// (remainder goes to the protocol treasury / burn).
    pub winner_slash_pct: u8,
    /// Whether to require the optional STARK proof in claims.
    /// Even when false, proofs strengthen claims during disputes.
    pub require_proof_in_claim: bool,
}

impl Default for DisputeConfig {
    fn default() -> Self {
        Self {
            dispute_window_blocks: 100, // ~20 minutes at 12s blocks
            challenger_stake_pct: 10,   // Challenger must stake 10% of provider stake
            arbiter_strategy: ArbiterStrategy::Tiered {
                cryptographic_deadline_blocks: 200,
                federation_quorum: 3,
                federation_deadline_blocks: 500,
            },
            winner_slash_pct: 80, // 80% to winner, 20% to treasury
            require_proof_in_claim: false,
        }
    }
}

// =============================================================================
// The Disputable Trait
// =============================================================================

/// Trait for apps that use optimistic dispute settlement.
///
/// Implement this with your domain-specific `Claim` and `Evidence` types to get
/// the full optimistic settlement lifecycle. The framework handles:
/// - Dispute window management
/// - Challenger stake locking
/// - Arbiter dispatch
/// - Slash/release effect generation
///
/// # Example (compute-exchange)
///
/// ```ignore
/// impl Disputable for ComputeExchange {
///     type Claim = ComputeMetrics;
///     type Evidence = DisputeEvidence;
///
///     fn submit_claim(&mut self, claim: ComputeMetrics) -> SettlementId { ... }
///     fn challenge(&mut self, id: SettlementId, ev: DisputeEvidence) -> DisputeId { ... }
///     fn resolve(&mut self, id: DisputeId, resolution: DisputeResolution) { ... }
///     fn finalize_unchallenged(&mut self, id: SettlementId) { ... }
/// }
/// ```
pub trait Disputable {
    /// The domain-specific claim type (what the provider attests to).
    type Claim;
    /// The domain-specific evidence type (what the challenger provides).
    type Evidence;
    /// Error type for operations.
    type Error;

    /// Submit a delivery claim, opening the dispute window.
    ///
    /// Returns the settlement ID. State transitions to `Pending`.
    fn submit_claim(&mut self, claim: Self::Claim) -> Result<SettlementId, Self::Error>;

    /// Challenge a pending claim with evidence.
    ///
    /// The challenger must stake to prevent frivolous disputes.
    /// State transitions to `Disputed`.
    fn challenge(
        &mut self,
        settlement_id: SettlementId,
        challenger: CellId,
        evidence: Self::Evidence,
        challenger_stake: u64,
    ) -> Result<DisputeId, Self::Error>;

    /// Resolve a dispute (called by the arbiter or automatically via ZK proof).
    ///
    /// State transitions to `Resolved`.
    fn resolve(
        &mut self,
        dispute_id: DisputeId,
        resolution: DisputeResolution,
    ) -> Result<(), Self::Error>;

    /// Finalize a settlement whose dispute window has closed without challenge.
    ///
    /// State transitions to `Finalized`, triggering payment release and stake return.
    fn finalize_unchallenged(&mut self, settlement_id: SettlementId) -> Result<(), Self::Error>;
}

// =============================================================================
// Settlement Lifecycle Helpers
// =============================================================================

/// Errors from the optimistic settlement lifecycle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisputeError {
    /// The settlement was not found.
    SettlementNotFound,
    /// The settlement is not in the expected state for this operation.
    InvalidState {
        expected: &'static str,
        actual: String,
    },
    /// The dispute window has not yet closed (cannot finalize).
    DisputeWindowOpen { deadline: u64, current_height: u64 },
    /// The dispute window has already closed (cannot challenge).
    DisputeWindowClosed { deadline: u64, current_height: u64 },
    /// Challenger stake is insufficient.
    InsufficientChallengerStake { required: u64, provided: u64 },
    /// The dispute was not found.
    DisputeNotFound,
    /// The claim is missing a required proof.
    ProofRequired,
}

impl std::fmt::Display for DisputeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SettlementNotFound => write!(f, "settlement not found"),
            Self::InvalidState { expected, actual } => {
                write!(f, "invalid state: expected {expected}, got {actual}")
            }
            Self::DisputeWindowOpen {
                deadline,
                current_height,
            } => {
                write!(
                    f,
                    "dispute window still open: deadline {deadline}, current {current_height}"
                )
            }
            Self::DisputeWindowClosed {
                deadline,
                current_height,
            } => {
                write!(
                    f,
                    "dispute window closed: deadline {deadline}, current {current_height}"
                )
            }
            Self::InsufficientChallengerStake { required, provided } => {
                write!(
                    f,
                    "insufficient challenger stake: required {required}, provided {provided}"
                )
            }
            Self::DisputeNotFound => write!(f, "dispute not found"),
            Self::ProofRequired => write!(f, "proof required in claim but not provided"),
        }
    }
}

impl std::error::Error for DisputeError {}

// =============================================================================
// Effect Generation
// =============================================================================

/// Effects to emit when a settlement is finalized (no dispute).
///
/// These map to `pyana_turn::Effect` variants that the app's executor applies.
#[derive(Clone, Debug)]
pub struct FinalizationEffects {
    /// Release the claimant's stake (FulfillObligation).
    pub release_stake_obligation_id: [u8; 32],
    /// Release payment to the claimant (ReleaseEscrow).
    pub release_payment_escrow_id: [u8; 32],
}

/// Effects to emit when a dispute is resolved in favor of the challenger.
///
/// The claimant's stake is slashed and distributed.
#[derive(Clone, Debug)]
pub struct SlashEffects {
    /// Slash the claimant's obligation (SlashObligation).
    pub slash_obligation_id: [u8; 32],
    /// Amount going to the challenger.
    pub challenger_reward: u64,
    /// Amount going to the protocol treasury (burn/pool).
    pub treasury_amount: u64,
    /// Return the challenger's dispute stake.
    pub return_challenger_stake: u64,
    /// Refund the payment escrow back to the counterparty (consumer).
    pub refund_payment_escrow_id: [u8; 32],
}

/// Effects to emit when a dispute is resolved in favor of the claimant.
///
/// The challenger's stake is forfeit to the claimant.
#[derive(Clone, Debug)]
pub struct ChallengerSlashEffects {
    /// Slash the challenger's dispute stake to the claimant.
    pub challenger_stake_to_claimant: u64,
    /// Now finalize the settlement normally (claimant was honest).
    pub finalization: FinalizationEffects,
}

/// Compute the distribution of a slashed stake.
pub fn compute_slash_distribution(
    total_stake: u64,
    challenger_dispute_stake: u64,
    config: &DisputeConfig,
) -> SlashEffects {
    let winner_amount = (total_stake as u128 * config.winner_slash_pct as u128 / 100) as u64;
    let treasury_amount = total_stake.saturating_sub(winner_amount);

    SlashEffects {
        slash_obligation_id: [0u8; 32], // Caller fills this in
        challenger_reward: winner_amount,
        treasury_amount,
        return_challenger_stake: challenger_dispute_stake,
        refund_payment_escrow_id: [0u8; 32], // Caller fills this in
    }
}

/// Compute the minimum challenger stake required for a given settlement.
pub fn minimum_challenger_stake(provider_stake: u64, config: &DisputeConfig) -> u64 {
    (provider_stake as u128 * config.challenger_stake_pct as u128 / 100) as u64
}

// =============================================================================
// Settlement ID derivation
// =============================================================================

/// Derive a deterministic settlement ID from its parameters.
pub fn compute_settlement_id(
    obligation_id: &[u8; 32],
    claimant: &CellId,
    counterparty: &CellId,
    submitted_at: u64,
) -> SettlementId {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-dispute-settlement-id-v1");
    hasher.update(obligation_id);
    hasher.update(claimant.as_bytes());
    hasher.update(counterparty.as_bytes());
    hasher.update(&submitted_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Derive a deterministic dispute ID from its parameters.
pub fn compute_dispute_id(
    settlement_id: &SettlementId,
    challenger: &CellId,
    filed_at: u64,
) -> DisputeId {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-dispute-id-v1");
    hasher.update(settlement_id);
    hasher.update(challenger.as_bytes());
    hasher.update(&filed_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Validation Helpers
// =============================================================================

/// Check whether a settlement's dispute window has closed.
pub fn is_dispute_window_closed(deadline: u64, current_height: u64) -> bool {
    current_height >= deadline
}

/// Check whether a claim can still be challenged.
pub fn can_challenge(state: &SettlementState, deadline: u64, current_height: u64) -> bool {
    matches!(state, SettlementState::Pending { .. }) && current_height < deadline
}

/// Check whether a settlement can be finalized (window closed, no dispute).
pub fn can_finalize(state: &SettlementState, deadline: u64, current_height: u64) -> bool {
    matches!(state, SettlementState::Pending { .. }) && current_height >= deadline
}

/// Validate that a dispute evidence is structurally sound.
///
/// This does NOT evaluate the evidence -- that's the arbiter's job.
/// This just checks that required fields are present and non-empty.
pub fn validate_evidence_structure(evidence: &DisputeEvidence) -> Result<(), &'static str> {
    match evidence {
        DisputeEvidence::ReExecutionMismatch {
            claimed_output_hash,
            actual_output_hash,
            ..
        } => {
            if claimed_output_hash == actual_output_hash {
                return Err("re-execution mismatch: hashes are identical");
            }
            Ok(())
        }
        DisputeEvidence::ProofInvalid { verification_error } => {
            if verification_error.is_empty() {
                return Err("proof invalid: must provide verification error");
            }
            Ok(())
        }
        DisputeEvidence::MetricsImpossible {
            reason,
            max_possible_flops,
        } => {
            if reason.is_empty() {
                return Err("metrics impossible: must provide reason");
            }
            if *max_possible_flops == 0 {
                return Err("metrics impossible: max_possible_flops must be non-zero");
            }
            Ok(())
        }
        DisputeEvidence::UptimeViolation {
            missed_heartbeat_blocks,
            required_uptime_bps,
            actual_uptime_bps,
        } => {
            if missed_heartbeat_blocks.is_empty() {
                return Err("uptime violation: must list missed blocks");
            }
            if *actual_uptime_bps >= *required_uptime_bps {
                return Err("uptime violation: actual uptime meets requirement");
            }
            Ok(())
        }
        DisputeEvidence::OutputInvalid { reason, .. } => {
            if reason.is_empty() {
                return Err("output invalid: must provide reason");
            }
            Ok(())
        }
        DisputeEvidence::Custom {
            evidence_type,
            payload,
        } => {
            if evidence_type.is_empty() {
                return Err("custom evidence: must provide evidence_type tag");
            }
            if payload.is_empty() {
                return Err("custom evidence: payload must not be empty");
            }
            Ok(())
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell(id: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = id;
        CellId::from_bytes(bytes)
    }

    #[test]
    fn test_settlement_id_derivation() {
        let obligation_id = [1u8; 32];
        let claimant = test_cell(1);
        let counterparty = test_cell(2);

        let id1 = compute_settlement_id(&obligation_id, &claimant, &counterparty, 100);
        let id2 = compute_settlement_id(&obligation_id, &claimant, &counterparty, 100);
        assert_eq!(id1, id2, "deterministic derivation");

        let id3 = compute_settlement_id(&obligation_id, &claimant, &counterparty, 101);
        assert_ne!(id1, id3, "different submitted_at yields different ID");
    }

    #[test]
    fn test_dispute_window_logic() {
        let state = SettlementState::Pending { submitted_at: 50 };

        // Window open
        assert!(can_challenge(&state, 150, 100));
        assert!(!can_finalize(&state, 150, 100));

        // Window closed
        assert!(!can_challenge(&state, 150, 150));
        assert!(can_finalize(&state, 150, 150));
        assert!(!can_challenge(&state, 150, 200));
        assert!(can_finalize(&state, 150, 200));
    }

    #[test]
    fn test_slash_distribution() {
        let config = DisputeConfig {
            winner_slash_pct: 80,
            ..Default::default()
        };
        let effects = compute_slash_distribution(1000, 100, &config);
        assert_eq!(effects.challenger_reward, 800);
        assert_eq!(effects.treasury_amount, 200);
        assert_eq!(effects.return_challenger_stake, 100);
    }

    #[test]
    fn test_minimum_challenger_stake() {
        let config = DisputeConfig {
            challenger_stake_pct: 10,
            ..Default::default()
        };
        assert_eq!(minimum_challenger_stake(1000, &config), 100);
        assert_eq!(minimum_challenger_stake(500, &config), 50);
    }

    #[test]
    fn test_evidence_validation() {
        // Valid re-execution mismatch
        let ev = DisputeEvidence::ReExecutionMismatch {
            claimed_output_hash: [1u8; 32],
            actual_output_hash: [2u8; 32],
            execution_proof: None,
        };
        assert!(validate_evidence_structure(&ev).is_ok());

        // Invalid: same hashes
        let ev = DisputeEvidence::ReExecutionMismatch {
            claimed_output_hash: [1u8; 32],
            actual_output_hash: [1u8; 32],
            execution_proof: None,
        };
        assert!(validate_evidence_structure(&ev).is_err());

        // Invalid: empty reason
        let ev = DisputeEvidence::MetricsImpossible {
            reason: String::new(),
            max_possible_flops: 1000,
        };
        assert!(validate_evidence_structure(&ev).is_err());

        // Valid uptime violation
        let ev = DisputeEvidence::UptimeViolation {
            missed_heartbeat_blocks: vec![100, 101, 102],
            required_uptime_bps: 9500,
            actual_uptime_bps: 9000,
        };
        assert!(validate_evidence_structure(&ev).is_ok());
    }

    #[test]
    fn test_default_config() {
        let config = DisputeConfig::default();
        assert_eq!(config.dispute_window_blocks, 100);
        assert_eq!(config.challenger_stake_pct, 10);
        assert_eq!(config.winner_slash_pct, 80);
        assert!(!config.require_proof_in_claim);
        assert!(matches!(
            config.arbiter_strategy,
            ArbiterStrategy::Tiered { .. }
        ));
    }
}
