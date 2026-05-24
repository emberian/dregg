//! `Authorizer` abstraction for framework helpers.
//!
//! Framework helpers (`EscrowManager`, queue/inbox/blinded endpoints, ring trade
//! coordinators) historically constructed actions with `Authorization::Unchecked`,
//! shifting the authentication burden to the underlying cell permissions. The
//! DSL audit (P0 #1) flagged this as a security gap: any caller of e.g.
//! `EscrowManager` was implicitly submitting unsigned turns.
//!
//! This module introduces the `Authorizer` trait: framework helpers now take an
//! `Authorizer` at construction time, and call `authorizer.authorize(ctx)` to
//! obtain an `Authorization` for each action they emit. Concrete implementations
//! cover the common cases (Ed25519 signing key, capability token, bearer cap).
//!
//! A `RejectingAuthorizer` exists for adversarial testing — it always returns an
//! error, so a misconfigured helper that forgets to set a real authorizer fails
//! loudly rather than silently submitting unauthenticated turns.

use pyana_turn::action::{Action, Authorization, BearerCapProof};
use pyana_turn::executor::TurnExecutor;

/// Errors from authorizing an action.
#[derive(Debug, Clone)]
pub enum AuthError {
    /// Authorizer is intentionally configured to reject (used in tests).
    Rejected(String),
    /// Signing operation failed (key material invalid, etc.).
    SigningFailed(String),
    /// The action being authorized is incompatible with this authorizer
    /// (e.g. a proof authorizer asked to sign a `Partial` commitment action).
    Incompatible(String),
}

impl std::fmt::Display for AuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rejected(reason) => write!(f, "authorization rejected: {reason}"),
            Self::SigningFailed(reason) => write!(f, "signing failed: {reason}"),
            Self::Incompatible(reason) => write!(f, "authorizer incompatible: {reason}"),
        }
    }
}

impl std::error::Error for AuthError {}

/// Context provided to an `Authorizer` when producing an `Authorization`.
///
/// The authorizer needs to know the federation it's authorizing against (for
/// federation-bound signing), the action's position in its forest (for
/// `CommitmentMode::Partial`), and the turn nonce. A reference to the unsigned
/// action lets the authorizer inspect what it is signing.
#[derive(Debug, Clone)]
pub struct AuthContext<'a> {
    /// The action that needs an authorization. Its `authorization` field will
    /// be overwritten by the result of `authorize`.
    pub action: &'a Action,
    /// The local federation id (binds signatures to this federation, preventing
    /// cross-federation replay).
    pub federation_id: [u8; 32],
    /// The action's position in the call forest (root index). Used only for
    /// `CommitmentMode::Partial` signing.
    pub forest_position: usize,
    /// The turn nonce. Used only for `CommitmentMode::Partial` signing.
    pub turn_nonce: u64,
}

/// Produces an `Authorization` for an unsigned action.
///
/// Framework helpers (`EscrowManager` etc.) take an `Authorizer` at
/// construction. For each action they would have shipped with
/// `Authorization::Unchecked`, they now call `authorizer.authorize(ctx)?` and
/// embed the returned `Authorization` in the action.
pub trait Authorizer: Send + Sync {
    /// Authorize the given action. Returns the `Authorization` to embed in the
    /// action's `authorization` field, or an `AuthError` if the authorizer
    /// declines to authorize (rejected, key invalid, incompatible action, ...).
    fn authorize(&self, ctx: AuthContext<'_>) -> Result<Authorization, AuthError>;
}

// =============================================================================
// SignedAuthorizer — Ed25519 signing key
// =============================================================================

/// Authorizes actions by signing them with an Ed25519 key.
///
/// Uses the same signing-message scheme the executor expects
/// (`TurnExecutor::compute_signing_message` /
/// `compute_partial_signing_message`), so the resulting
/// `Authorization::Signature(r, s)` will verify against the target cell's
/// public key if the cell's `public_key` matches this authorizer's key.
pub struct SignedAuthorizer {
    signing_key: ed25519_dalek::SigningKey,
}

impl SignedAuthorizer {
    /// Construct from a 32-byte Ed25519 secret key.
    pub fn from_secret_bytes(secret: [u8; 32]) -> Self {
        Self {
            signing_key: ed25519_dalek::SigningKey::from_bytes(&secret),
        }
    }

    /// Construct from an existing `SigningKey`.
    pub fn new(signing_key: ed25519_dalek::SigningKey) -> Self {
        Self { signing_key }
    }

    /// Get the verifying (public) key for this authorizer.
    pub fn verifying_key(&self) -> ed25519_dalek::VerifyingKey {
        self.signing_key.verifying_key()
    }
}

impl Authorizer for SignedAuthorizer {
    fn authorize(&self, ctx: AuthContext<'_>) -> Result<Authorization, AuthError> {
        use ed25519_dalek::Signer;
        use pyana_turn::action::CommitmentMode;

        let message = match ctx.action.commitment_mode {
            CommitmentMode::Full => {
                TurnExecutor::compute_signing_message(ctx.action, &ctx.federation_id)
            }
            CommitmentMode::Partial => TurnExecutor::compute_partial_signing_message(
                ctx.action,
                ctx.forest_position,
                &ctx.federation_id,
                ctx.turn_nonce,
            ),
        };

        let sig = self.signing_key.sign(&message);
        let bytes = sig.to_bytes();
        let mut r = [0u8; 32];
        let mut s = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        s.copy_from_slice(&bytes[32..]);
        Ok(Authorization::Signature(r, s))
    }
}

// =============================================================================
// CapabilityAuthorizer — breadstuff capability token
// =============================================================================

/// Authorizes actions with a capability (breadstuff) token.
///
/// The token is a 32-byte hash that the executor checks against the actor's
/// c-list when validating the action.
pub struct CapabilityAuthorizer {
    token: [u8; 32],
}

impl CapabilityAuthorizer {
    pub fn new(token: [u8; 32]) -> Self {
        Self { token }
    }
}

impl Authorizer for CapabilityAuthorizer {
    fn authorize(&self, _ctx: AuthContext<'_>) -> Result<Authorization, AuthError> {
        Ok(Authorization::Breadstuff(self.token))
    }
}

// =============================================================================
// BearerAuthorizer — proof-carrying bearer capability
// =============================================================================

/// Authorizes actions by presenting a bearer-capability proof.
pub struct BearerAuthorizer {
    proof: BearerCapProof,
}

impl BearerAuthorizer {
    pub fn new(proof: BearerCapProof) -> Self {
        Self { proof }
    }
}

impl Authorizer for BearerAuthorizer {
    fn authorize(&self, _ctx: AuthContext<'_>) -> Result<Authorization, AuthError> {
        Ok(Authorization::Bearer(self.proof.clone()))
    }
}

// =============================================================================
// RejectingAuthorizer — for adversarial testing
// =============================================================================

/// An `Authorizer` that always rejects, used in tests to verify that
/// framework helpers actually call into the authorizer (and fail when the
/// authorizer refuses to authorize, rather than silently shipping unsigned
/// turns).
pub struct RejectingAuthorizer {
    reason: String,
}

impl RejectingAuthorizer {
    pub fn new(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
        }
    }
}

impl Default for RejectingAuthorizer {
    fn default() -> Self {
        Self::new("rejecting authorizer (test only)")
    }
}

impl Authorizer for RejectingAuthorizer {
    fn authorize(&self, _ctx: AuthContext<'_>) -> Result<Authorization, AuthError> {
        Err(AuthError::Rejected(self.reason.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_turn::action::{CommitmentMode, DelegationMode, symbol};
    use pyana_types::CellId;

    fn dummy_action() -> Action {
        // Use a zeroed Signature as a placeholder so this file does not
        // contain the literal token the no_unchecked.rs grep-guard scans for.
        Action {
            target: CellId::from_bytes([1u8; 32]),
            method: symbol("test"),
            args: vec![],
            authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
            preconditions: Default::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        }
    }

    #[test]
    fn signed_authorizer_produces_signature() {
        let auth = SignedAuthorizer::from_secret_bytes([7u8; 32]);
        let action = dummy_action();
        let ctx = AuthContext {
            action: &action,
            federation_id: [0u8; 32],
            forest_position: 0,
            turn_nonce: 0,
        };
        let result = auth.authorize(ctx).expect("signing should succeed");
        assert!(matches!(result, Authorization::Signature(_, _)));
    }

    #[test]
    fn capability_authorizer_produces_token() {
        let auth = CapabilityAuthorizer::new([9u8; 32]);
        let action = dummy_action();
        let ctx = AuthContext {
            action: &action,
            federation_id: [0u8; 32],
            forest_position: 0,
            turn_nonce: 0,
        };
        let result = auth.authorize(ctx).expect("cap should succeed");
        assert!(matches!(result, Authorization::Breadstuff(t) if t == [9u8; 32]));
    }

    #[test]
    fn rejecting_authorizer_always_errors() {
        let auth = RejectingAuthorizer::new("no");
        let action = dummy_action();
        let ctx = AuthContext {
            action: &action,
            federation_id: [0u8; 32],
            forest_position: 0,
            turn_nonce: 0,
        };
        let err = auth.authorize(ctx).expect_err("must reject");
        assert!(matches!(err, AuthError::Rejected(_)));
    }
}
