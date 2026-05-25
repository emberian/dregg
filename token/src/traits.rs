//! Core authorization token trait.
//!
//! [`AuthToken`] is the unified interface over both Macaroon and Biscuit tokens.
//! The rest of the auth system works with this trait — the token format is an
//! implementation detail selected at creation time.

use crate::error::TokenError;
use crate::format::TokenFormat;

/// Result of successful token verification.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct TokenClearance {
    /// Which policy or caveat set matched.
    pub matched_policy: Option<String>,

    /// The effective capabilities after verification.
    ///
    /// For macaroons: the set of cleared caveats.
    /// For biscuit: the matched allow policy index + any query results.
    pub capabilities: Vec<Capability>,

    /// Token format that was verified.
    pub format: TokenFormat,

    /// Absolute expiration timestamp (Unix seconds), if the token has one.
    ///
    /// Extracted from ValidityWindow caveats (macaroon) or time checks (biscuit).
    pub expires_at: Option<i64>,

    /// Subject / user ID the token is confined to, if any.
    ///
    /// Extracted from ConfineUser caveats (macaroon) or user() facts (biscuit).
    pub subject: Option<String>,
}

/// A single capability granted by a token.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Capability {
    /// Resource type (e.g., "app", "service", "secret", "feature").
    pub resource_type: String,
    /// Resource identifier (e.g., "my-app", "http", "oauth/github").
    pub resource_id: String,
    /// Actions permitted (e.g., "r", "rw", "rwcd", "*").
    pub actions: String,
}

impl TokenClearance {
    /// Convenience constructor for a single capability entry.
    pub fn cap(resource_type: &str, resource_id: &str, actions: &str) -> Capability {
        Capability {
            resource_type: resource_type.into(),
            resource_id: resource_id.into(),
            actions: actions.into(),
        }
    }
}

/// An authorization request — what the token is being asked to authorize.
///
/// This is the format-agnostic representation. Both Macaroon caveats and
/// Biscuit Datalog checks evaluate against this.
#[derive(Clone, Debug, Default)]
pub struct AuthRequest {
    /// Application identifier.
    pub app_id: Option<String>,
    /// Service name (e.g., "dns", "http", "auth", "secrets").
    pub service: Option<String>,
    /// Action being performed (e.g., "read", "write", "create", "delete", "control").
    pub action: Option<String>,
    /// Features required.
    pub features: Vec<String>,
    /// OAuth provider name.
    pub oauth_provider: Option<String>,
    /// OAuth scopes.
    pub oauth_scopes: Vec<String>,
    /// User ID.
    pub user_id: Option<String>,
    /// Current timestamp (Unix seconds). Auto-filled if None.
    pub now: Option<i64>,
    /// Current budget states for any budget caveats on this token.
    /// Maps budget_id to remaining units. Required when the token has Budget caveats.
    pub budget_states: std::collections::HashMap<String, u64>,
    /// Cost of this specific request (in budget units).
    /// Required when the token has Budget caveats.
    pub request_cost: Option<u64>,
    /// Revocation non-membership proofs: set of token IDs confirmed not-revoked.
    /// Required when the token has `Revocable` caveats; the bridge's authorize
    /// path (`bridge/src/authorize.rs`) checks each revocable id against this
    /// set.
    pub not_revoked: std::collections::HashSet<String>,
}

/// Restrictions to apply when attenuating a token.
///
/// Each field, if set, adds a restriction. Restrictions can only narrow
/// permissions, never expand them.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Attenuation {
    /// Lock to specific app(s) with action masks.
    /// Key: app ID, Value: action string (e.g., "r", "rw", "*").
    pub apps: Vec<(String, String)>,
    /// Lock to specific service(s) with action masks.
    pub services: Vec<(String, String)>,
    /// Lock to specific feature set.
    pub features: Vec<String>,
    /// Expiration (Unix timestamp seconds). Token invalid after this time.
    pub not_after: Option<i64>,
    /// Not-before (Unix timestamp seconds). Token invalid before this time.
    pub not_before: Option<i64>,
    /// Lock to specific user ID.
    pub confine_user: Option<String>,
    /// Lock to specific OAuth provider(s).
    pub oauth_providers: Vec<String>,
    /// Lock to specific OAuth scope(s).
    pub oauth_scopes: Vec<String>,
    /// Feature glob patterns: include/exclude for resource scoping.
    /// Include patterns match resources; exclude patterns (prefixed with `!`) deny.
    pub feature_globs: Option<FeatureGlobSpec>,
    /// Budget enrollment: (budget_id, budget_class, limit, optional window).
    pub budget: Option<BudgetSpec>,
    // SECURITY: raw_datalog field was removed to prevent Datalog injection attacks.
    // All attenuation MUST use structured caveats (apps, services, features, etc.).
}

/// Feature glob pattern specification for resource scoping.
///
/// Allows fine-grained file/resource access control using glob patterns.
/// Include patterns grant access; exclude patterns deny it.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct FeatureGlobSpec {
    /// Glob patterns to include (e.g., `src/components/**`).
    pub include: Vec<String>,
    /// Glob patterns to exclude (e.g., `src/components/secrets.ts`).
    pub exclude: Vec<String>,
}

/// Budget specification for token-scoped resource limits.
///
/// The budget caveat itself always passes locally — enforcement
/// happens at the budget counter service.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BudgetSpec {
    /// Budget identifier (e.g., `ci-bot-7:daily`).
    pub id: String,
    /// Parent budget identifier, if any.
    pub parent_id: Option<String>,
    /// Budget class (e.g., `api_calls`, `tokens`, `cost`, `bytes`).
    pub class: String,
    /// Maximum count/amount for the budget window.
    pub limit: u64,
    /// Optional time window (e.g., `1d`, `1h`, `30m`).
    pub window: Option<String>,
}

/// Verifies encoded tokens against an [`AuthRequest`].
///
/// Implementors hold key material (HMAC root keys, Ed25519 public keys) and
/// handle format detection + key resolution internally. The `tokenizer` crate
/// uses this to remain decoupled from the full `auth` crate.
pub trait TokenVerifier: Send + Sync {
    fn verify(&self, encoded: &str, request: &AuthRequest) -> Result<TokenClearance, TokenError>;
}

/// The core authorization token trait.
///
/// Both [`MacaroonToken`] and [`BiscuitToken`] implement this.
/// The auth service, sidecar, and guest API all work through this interface.
pub trait AuthToken: Send + Sync + std::fmt::Debug {
    /// The token format.
    fn format(&self) -> TokenFormat;

    /// Verify the token and authorize the given request.
    ///
    /// Returns the clearance (matched policy + capabilities) on success,
    /// or an error describing why authorization failed.
    fn verify(&self, request: &AuthRequest) -> Result<TokenClearance, TokenError>;

    /// Add restrictions to the token, returning a new (more restricted) token.
    ///
    /// This can only narrow permissions, never expand them.
    fn attenuate(&self, restrictions: &Attenuation) -> Result<Box<dyn AuthToken>, TokenError>;

    /// Encode the token to its wire format (binary).
    fn to_bytes(&self) -> Result<Vec<u8>, TokenError>;

    /// Encode the token to its prefixed string format.
    fn to_encoded(&self) -> Result<String, TokenError>;

    /// Whether this token can still be attenuated.
    ///
    /// Returns false for sealed biscuit tokens or tokens without the
    /// necessary key material for further chaining.
    fn is_attenuable(&self) -> bool;

    /// SEAL the token, preventing further attenuation.
    ///
    /// Not all formats support sealing — macaroons are inherently non-sealable
    /// (they don't need it since HMAC chain already prevents forgery).
    fn seal(&self) -> Result<Box<dyn AuthToken>, TokenError>;
}
