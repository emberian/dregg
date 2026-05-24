//! Atomic payment via conditional turns.
//!
//! The escrow model:
//! 1. Issuer creates a cell to hold the bounty reward.
//! 2. A conditional turn is created: "release to worker IFF completion proof arrives before deadline."
//! 3. If the deadline passes without proof: reward returns to issuer.
//! 4. On approval: the conditional turn resolves, transferring reward atomically.
//!
//! Payment flows are handled through the `EscrowManager` from `pyana-app-framework`,
//! which submits turns to the executor rather than producing self-attested receipts.
//!
//! Every helper here requires the caller to supply a `Box<dyn Authorizer>` so
//! that the underlying turn is properly authenticated. The previous
//! `Authorization::Unchecked` default was removed when the DSL audit flagged it
//! as a structural authentication gap (P0 #1). See
//! [`make_default_authorizer`] for the convenience constructor this app uses.

use pyana_app_framework::authorizer::{Authorizer, SignedAuthorizer};
use pyana_app_framework::escrow::{EscrowError, EscrowManager};
use pyana_app_framework::{CellId, EscrowCondition, PyanaEngine};

/// Error type for payment operations.
#[derive(Debug, Clone)]
pub enum PaymentError {
    /// The escrow cell could not be created.
    EscrowCreationFailed(String),
    /// The conditional turn could not be constructed.
    ConditionalTurnFailed(String),
    /// The reward release failed.
    ReleaseFailed(String),
    /// The refund back to issuer failed.
    RefundFailed(String),
}

impl std::fmt::Display for PaymentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EscrowCreationFailed(msg) => write!(f, "escrow creation failed: {msg}"),
            Self::ConditionalTurnFailed(msg) => write!(f, "conditional turn failed: {msg}"),
            Self::ReleaseFailed(msg) => write!(f, "release failed: {msg}"),
            Self::RefundFailed(msg) => write!(f, "refund failed: {msg}"),
        }
    }
}

impl std::error::Error for PaymentError {}

impl From<EscrowError> for PaymentError {
    fn from(e: EscrowError) -> Self {
        PaymentError::EscrowCreationFailed(e.to_string())
    }
}

/// An escrow holding a bounty reward until completion conditions are met.
#[derive(Clone, Debug)]
pub struct Escrow {
    /// The escrow identifier (derived deterministically from parameters).
    pub escrow_id: [u8; 32],
    /// The issuer's cell (for refund on timeout).
    pub issuer_cell: CellId,
    /// The worker's cell (for release on approval).
    pub worker_cell: CellId,
    /// The reward amount held.
    pub amount: u64,
    /// The deadline height for timeout/refund.
    pub timeout_height: u64,
}

/// Build the default `Authorizer` for the bounty-board service.
///
/// Reads `PYANA_BOUNTY_ESCROW_KEY` (32 hex bytes) and constructs a
/// [`SignedAuthorizer`] from it. If the env var is unset, a deterministic
/// dev-only key is used and a warning is logged. Production deployments MUST
/// set `PYANA_BOUNTY_ESCROW_KEY`.
pub fn make_default_authorizer() -> Box<dyn Authorizer> {
    let secret = match std::env::var("PYANA_BOUNTY_ESCROW_KEY") {
        Ok(hex) => match parse_hex_32(&hex) {
            Some(bytes) => bytes,
            None => {
                eprintln!(
                    "WARNING: PYANA_BOUNTY_ESCROW_KEY is not valid 32-byte hex; using dev key"
                );
                dev_key_bytes()
            }
        },
        Err(_) => {
            eprintln!(
                "WARNING: PYANA_BOUNTY_ESCROW_KEY not set; using deterministic dev key. \
                 DO NOT use this in production."
            );
            dev_key_bytes()
        }
    };
    Box::new(SignedAuthorizer::from_secret_bytes(secret))
}

fn dev_key_bytes() -> [u8; 32] {
    *blake3::hash(b"pyana-bounty-board-dev-escrow-key-v1").as_bytes()
}

fn parse_hex_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim().trim_start_matches("0x");
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

/// Create an escrow holding the bounty reward, submitting through the engine.
///
/// The reward is released via the `EscrowManager` when completion is approved.
/// If the deadline passes without completion, the reward returns to the issuer.
///
/// # Arguments
///
/// * `engine` - The pyana engine to submit turns through.
/// * `authorizer` - Authorizer used to sign the escrow-create turn.
/// * `issuer_cell` - The issuer's cell that funds the escrow.
/// * `worker_cell` - The worker's cell to receive the reward on release.
/// * `reward_amount` - Amount to escrow.
/// * `deadline_height` - Block height at which the escrow expires.
/// * `condition` - The condition that must be satisfied to release.
///
/// # Returns
///
/// An `Escrow` containing the escrow ID and metadata.
pub fn create_escrow(
    engine: &mut PyanaEngine,
    authorizer: Box<dyn Authorizer>,
    issuer_cell: CellId,
    worker_cell: CellId,
    reward_amount: u64,
    deadline_height: u64,
    condition: EscrowCondition,
) -> Result<Escrow, PaymentError> {
    let mut mgr = EscrowManager::new(engine, authorizer);

    let escrow_id = mgr
        .create_payment_escrow(
            issuer_cell,
            worker_cell,
            reward_amount,
            condition,
            deadline_height,
        )
        .map_err(|e| PaymentError::EscrowCreationFailed(e.to_string()))?;

    Ok(Escrow {
        escrow_id,
        issuer_cell,
        worker_cell,
        amount: reward_amount,
        timeout_height: deadline_height,
    })
}

/// Release the escrowed reward to the worker.
///
/// Called when the issuer approves a submission. The escrow is released through
/// the engine's executor with the provided completion proof.
///
/// # Arguments
///
/// * `engine` - The pyana engine to submit the release turn through.
/// * `authorizer` - Authorizer used to sign the release turn.
/// * `escrow` - The escrow to release.
/// * `completion_proof` - The proof that satisfies the escrow's condition.
///
/// # Returns
///
/// The escrow ID confirming the release, or an error.
pub fn release_reward(
    engine: &mut PyanaEngine,
    authorizer: Box<dyn Authorizer>,
    escrow: &Escrow,
    completion_proof: &[u8],
) -> Result<[u8; 32], PaymentError> {
    let mut mgr = EscrowManager::new(engine, authorizer);

    mgr.release_with_proof(escrow.escrow_id, completion_proof)
        .map_err(|e| PaymentError::ReleaseFailed(e.to_string()))?;

    Ok(escrow.escrow_id)
}

/// Refund the escrowed reward back to the issuer (timeout case).
///
/// Called when a bounty expires without completion. The escrow is refunded
/// through the engine's executor.
///
/// # Arguments
///
/// * `engine` - The pyana engine to submit the refund turn through.
/// * `authorizer` - Authorizer used to sign the refund turn.
/// * `escrow` - The escrow to refund.
/// * `current_height` - The current block height (must be past timeout).
///
/// # Returns
///
/// The escrow ID confirming the refund, or an error.
pub fn refund_escrow(
    engine: &mut PyanaEngine,
    authorizer: Box<dyn Authorizer>,
    escrow: &Escrow,
    current_height: u64,
) -> Result<[u8; 32], PaymentError> {
    let mut mgr = EscrowManager::new(engine, authorizer);

    mgr.refund_expired(escrow.escrow_id, current_height)
        .map_err(|e| PaymentError::RefundFailed(e.to_string()))?;

    Ok(escrow.escrow_id)
}
