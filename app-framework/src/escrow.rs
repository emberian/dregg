//! High-level escrow lifecycle helpers built on `pyana-turn` effects.
//!
//! Wraps the low-level `Effect::CreateEscrow`, `Effect::ReleaseEscrow`, and
//! `Effect::RefundEscrow` into a managed workflow that submits turns to a
//! `PyanaEngine`.
//!
//! # Authentication
//!
//! Every action this manager emits is authenticated through an
//! [`Authorizer`](crate::authorizer::Authorizer) that the caller supplies at
//! construction. Earlier versions of this module shipped every turn with
//! `Authorization::Unchecked`, which the DSL audit (P0 #1) flagged as a
//! structural authentication gap: any caller of `EscrowManager` was implicitly
//! submitting unsigned turns. The current shape forces the caller to make an
//! explicit choice (Ed25519 sign, capability token, bearer cap) and produces a
//! loud error if the authorizer rejects.

use pyana_cell::CellId;
use pyana_sdk::embed::PyanaEngine;
use pyana_turn::action::{Action, CommitmentMode, DelegationMode, Effect, Symbol, symbol};
use pyana_turn::escrow::EscrowCondition;
use pyana_turn::turn::Turn;
use pyana_turn::{CallForest, CallTree};

use crate::authorizer::{AuthContext, AuthError, Authorizer};

/// Errors from escrow lifecycle operations.
#[derive(Debug)]
pub enum EscrowError {
    /// Turn execution was rejected by the engine.
    TurnRejected(String),
    /// The escrow has already been resolved.
    AlreadyResolved,
    /// The escrow timeout has not yet passed (cannot refund).
    NotExpired {
        timeout_height: u64,
        current_height: u64,
    },
    /// The configured `Authorizer` declined to authorize the action.
    AuthorizationFailed(AuthError),
}

impl std::fmt::Display for EscrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TurnRejected(reason) => write!(f, "turn rejected: {reason}"),
            Self::AlreadyResolved => write!(f, "escrow already resolved"),
            Self::NotExpired {
                timeout_height,
                current_height,
            } => write!(
                f,
                "escrow not expired: timeout at height {timeout_height}, current {current_height}"
            ),
            Self::AuthorizationFailed(err) => write!(f, "authorization failed: {err}"),
        }
    }
}

impl std::error::Error for EscrowError {}

impl From<AuthError> for EscrowError {
    fn from(err: AuthError) -> Self {
        EscrowError::AuthorizationFailed(err)
    }
}

/// Manages escrow creation, release, and refund via a `PyanaEngine`.
///
/// # Example
///
/// ```ignore
/// use pyana_app_framework::escrow::EscrowManager;
/// use pyana_app_framework::authorizer::SignedAuthorizer;
/// use pyana_sdk::embed::{PyanaEngine, EngineConfig};
/// use pyana_turn::escrow::EscrowCondition;
///
/// let mut engine = PyanaEngine::new(EngineConfig::for_testing());
/// let authorizer = SignedAuthorizer::from_secret_bytes([7u8; 32]);
/// let mut mgr = EscrowManager::new(&mut engine, Box::new(authorizer));
///
/// let escrow_id = mgr.create_payment_escrow(
///     from_cell, to_cell, 1000,
///     EscrowCondition::ProofPresented { verification_key: [0u8; 32] },
///     100,
/// ).unwrap();
/// ```
pub struct EscrowManager<'a> {
    engine: &'a mut PyanaEngine,
    authorizer: Box<dyn Authorizer>,
}

/// The parts of an `Action` that this manager needs to fill in before asking
/// the authorizer to produce an `Authorization`. The `authorization` field of
/// `Action` is intentionally absent here — it is set by the authorizer at
/// `submit_action` time, never with a `Unchecked` placeholder.
struct UnauthorizedAction {
    target: CellId,
    method: Symbol,
    effects: Vec<Effect>,
}

impl<'a> EscrowManager<'a> {
    /// Create a new escrow manager wrapping an engine.
    ///
    /// The `authorizer` is used to authenticate every turn this manager emits.
    /// Callers must supply a real authorizer (typically a [`SignedAuthorizer`]
    /// wrapping the caller's Ed25519 key). There is no `Unchecked` default:
    /// the audit found that the previous default was an authentication gap.
    ///
    /// [`SignedAuthorizer`]: crate::authorizer::SignedAuthorizer
    pub fn new(engine: &'a mut PyanaEngine, authorizer: Box<dyn Authorizer>) -> Self {
        Self { engine, authorizer }
    }

    /// Build a fully-authorized `Action` from an `UnauthorizedAction` by running
    /// it through this manager's `Authorizer`.
    ///
    /// The authorizer is given a probe `Action` to inspect; the probe carries a
    /// zero-byte `Signature` placeholder solely so the `Authorization` enum has
    /// a value (the signing-message computation deliberately does not hash the
    /// `authorization` field — see `TurnExecutor::compute_signing_message`).
    /// `Authorization::Unchecked` is intentionally not used as a placeholder so
    /// that the framework's CI grep-guard against `Unchecked` in production
    /// code remains effective.
    fn authorize_action(
        &self,
        unsigned: UnauthorizedAction,
        nonce: u64,
    ) -> Result<Action, EscrowError> {
        let federation_id = self.engine.executor().local_federation_id;
        let placeholder_authorization =
            pyana_turn::action::Authorization::Signature([0u8; 32], [0u8; 32]);
        let probe = Action {
            target: unsigned.target,
            method: unsigned.method,
            args: vec![],
            authorization: placeholder_authorization,
            preconditions: Default::default(),
            effects: unsigned.effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };
        let ctx = AuthContext {
            action: &probe,
            federation_id,
            forest_position: 0,
            turn_nonce: nonce,
        };
        let authorization = self.authorizer.authorize(ctx)?;
        let mut action = probe;
        action.authorization = authorization;
        Ok(action)
    }

    /// Submit a single-action turn after authorizing its action.
    fn submit_unauthorized(
        &mut self,
        agent: CellId,
        nonce: u64,
        unsigned: UnauthorizedAction,
        memo: String,
    ) -> Result<(), EscrowError> {
        let action = self.authorize_action(unsigned, nonce)?;

        let turn = Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![CallTree::new(action)],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: Some(memo),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
        };

        self.engine
            .execute_turn(&turn)
            .map_err(|e| EscrowError::TurnRejected(e.to_string()))?;

        Ok(())
    }

    /// Create a payment escrow that locks `amount` from `from` for `to`.
    ///
    /// The escrow is released when `condition` is satisfied, or refundable
    /// after `timeout_height` blocks.
    ///
    /// Returns the escrow ID on success.
    pub fn create_payment_escrow(
        &mut self,
        from: CellId,
        to: CellId,
        amount: u64,
        condition: EscrowCondition,
        timeout: u64,
    ) -> Result<[u8; 32], EscrowError> {
        // Derive a deterministic escrow ID from parameters.
        let escrow_id = compute_escrow_id(&from, &to, amount, timeout);

        let unsigned = UnauthorizedAction {
            target: from,
            method: symbol("create_escrow"),
            effects: vec![Effect::CreateEscrow {
                cell: from,
                recipient: to,
                amount,
                condition,
                timeout_height: timeout,
                escrow_id,
            }],
        };

        let memo = format!("create escrow: {amount} locked until height {timeout}");
        self.submit_unauthorized(from, timeout, unsigned, memo)?;
        Ok(escrow_id)
    }

    /// Release an escrow by providing a proof that satisfies its condition.
    ///
    /// The escrowed amount transfers to the recipient.
    pub fn release_with_proof(
        &mut self,
        escrow_id: [u8; 32],
        proof: &[u8],
    ) -> Result<(), EscrowError> {
        // We use a sentinel agent for the release turn (the executor validates
        // the proof against the escrow condition, not the agent identity).
        let agent = CellId::from_bytes(escrow_id);

        let unsigned = UnauthorizedAction {
            target: agent,
            method: symbol("release_escrow"),
            effects: vec![Effect::ReleaseEscrow {
                escrow_id,
                proof: Some(proof.to_vec()),
            }],
        };

        self.submit_unauthorized(agent, 0, unsigned, "release escrow with proof".to_string())
    }

    /// Refund an escrow after its timeout height has passed.
    ///
    /// The escrowed amount returns to the original creator.
    pub fn refund_expired(
        &mut self,
        escrow_id: [u8; 32],
        current_height: u64,
    ) -> Result<(), EscrowError> {
        let agent = CellId::from_bytes(escrow_id);

        let unsigned = UnauthorizedAction {
            target: agent,
            method: symbol("refund_escrow"),
            effects: vec![Effect::RefundEscrow { escrow_id }],
        };

        let memo = format!("refund expired escrow at height {current_height}");
        self.submit_unauthorized(agent, current_height, unsigned, memo)
    }
}

/// Compute a deterministic escrow ID from its creation parameters.
fn compute_escrow_id(from: &CellId, to: &CellId, amount: u64, timeout: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-app-framework-escrow-id-v1");
    hasher.update(from.as_bytes());
    hasher.update(to.as_bytes());
    hasher.update(&amount.to_le_bytes());
    hasher.update(&timeout.to_le_bytes());
    *hasher.finalize().as_bytes()
}
