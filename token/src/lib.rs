//! Dregg Authorization Token Library
//!
//! Unified abstraction over two token formats:
//!
//! - **Macaroon** (feature `macaroon`): HMAC-SHA256 symmetric tokens.
//!   Fast (~0.5μs verify), requires root secret key. Best for internal
//!   service-to-service auth on hot paths.
//!
//! - **Biscuit** (feature `biscuit`): Ed25519/P-256 asymmetric tokens
//!   with Datalog authorization. Decentralized verification with just
//!   a public key. Best for distributed/delegated auth scenarios.
//!
//! Both implement [`AuthToken`] — the rest of the auth system
//! (OAuth, sidecar, RPC, guest API) works through this trait.
//!
//! # Token Format Detection
//!
//! Tokens are self-describing via prefix:
//! - `em2_` — Macaroon (Dregg Macaroon v2)
//! - `eb2_` — Biscuit (Dregg Biscuit v2)
//!
//! Use [`TokenFormat::detect`] to auto-detect from an encoded string.

pub mod action_set;
pub mod dregg;
pub mod error;
pub mod format;
#[cfg(feature = "rand-deps")]
pub mod revocation;
pub mod traits;

#[cfg(feature = "biscuit")]
pub mod biscuit_backend;

#[cfg(feature = "macaroon")]
pub mod dregg_caveats;

#[cfg(all(feature = "macaroon", feature = "rand-deps"))]
pub mod macaroon_backend;

#[cfg(feature = "macaroon")]
pub mod factset;

#[cfg(feature = "macaroon")]
pub mod datalog_verify;

// Re-export primary types.
pub use action_set::{ActionId, ActionSet};
pub use error::TokenError;
pub use format::TokenFormat;
#[cfg(feature = "rand-deps")]
#[allow(deprecated)]
pub use revocation::RevocationFilter;
#[cfg(feature = "rand-deps")]
pub use revocation::{
    AttestedRevocationRoot, NonMembershipProof, RevocationError, RevocationRegistry,
};
pub use traits::{
    Attenuation, AuthRequest, AuthToken, BudgetSpec, Capability, FeatureGlobSpec, TokenClearance,
    TokenVerifier,
};

#[cfg(feature = "biscuit")]
pub use biscuit_backend::BiscuitToken;

#[cfg(all(feature = "macaroon", feature = "rand-deps"))]
pub use macaroon_backend::MacaroonToken;

// Re-export underlying crate types for advanced usage.
#[cfg(feature = "biscuit")]
pub use biscuit_auth;

#[cfg(feature = "macaroon")]
pub use dregg_macaroon;

/// Decode a token from its prefixed string representation.
///
/// Auto-detects the format from the prefix and returns a boxed [`AuthToken`].
///
/// For **Biscuit** tokens, you must provide the root public key.
/// For **Macaroon** tokens, you must provide the root secret key.
///
/// Use the format-specific constructors for type-safe key handling.
#[cfg(feature = "rand-deps")]
pub fn decode_token(
    encoded: &str,
    #[cfg(feature = "biscuit")] biscuit_public_key: Option<biscuit_auth::PublicKey>,
    #[cfg(feature = "macaroon")] macaroon_root_key: Option<[u8; 32]>,
) -> Result<Box<dyn AuthToken>, TokenError> {
    let fmt = TokenFormat::detect(encoded)?;
    match fmt {
        #[cfg(feature = "biscuit")]
        TokenFormat::Biscuit => {
            let pk = biscuit_public_key
                .ok_or_else(|| TokenError::KeyError("biscuit public key required".into()))?;
            Ok(Box::new(BiscuitToken::from_encoded(encoded, pk)?))
        }
        #[cfg(feature = "macaroon")]
        TokenFormat::Macaroon => {
            let key = macaroon_root_key
                .ok_or_else(|| TokenError::KeyError("macaroon root key required".into()))?;
            Ok(Box::new(MacaroonToken::from_encoded(encoded, key)?))
        }
        #[allow(unreachable_patterns)]
        _ => Err(TokenError::UnsupportedFormat(format!(
            "{} support not compiled in",
            fmt
        ))),
    }
}
