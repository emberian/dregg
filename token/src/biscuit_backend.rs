//! Biscuit token backend.
//!
//! Wraps the `biscuit-auth` crate to implement [`AuthToken`].
//! Biscuit tokens use Ed25519 (or P-256) asymmetric signatures with Datalog
//! authorization policies. Verification requires only the root public key.

use base64::Engine;
use biscuit_auth::Biscuit;
use biscuit_auth::builder::{AuthorizerBuilder, BlockBuilder};

use crate::error::TokenError;
use crate::format::TokenFormat;
use crate::pyana;
use crate::traits::{Attenuation, AuthRequest, AuthToken, TokenClearance};

/// Extract a string value from a Biscuit Datalog term.
fn term_to_string(term: &biscuit_auth::builder::Term) -> Option<String> {
    match term {
        biscuit_auth::builder::Term::Str(s) => Some(s.clone()),
        biscuit_auth::builder::Term::Integer(n) => Some(n.to_string()),
        _ => None,
    }
}

/// A Biscuit-backed authorization token.
///
/// Wraps `biscuit_auth::Biscuit` with the Pyana-specific Datalog schema.
pub struct BiscuitToken {
    /// The inner biscuit token.
    inner: Biscuit,
    /// Root public key (needed for verification).
    root_public_key: biscuit_auth::PublicKey,
}

impl std::fmt::Debug for BiscuitToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BiscuitToken")
            .field("block_count", &self.inner.block_count())
            .finish()
    }
}

impl BiscuitToken {
    /// Create a new Biscuit token from the inner biscuit and root public key.
    pub fn new(inner: Biscuit, root_public_key: biscuit_auth::PublicKey) -> Self {
        Self {
            inner,
            root_public_key,
        }
    }

    /// Mint a new Biscuit token with the given authority Datalog code.
    pub fn mint(
        root_keypair: &biscuit_auth::KeyPair,
        authority_code: &str,
    ) -> Result<Self, TokenError> {
        let token = Biscuit::builder()
            .code(authority_code)
            .map_err(|e| TokenError::Datalog(e.to_string()))?
            .build(root_keypair)
            .map_err(|e| TokenError::Crypto(e.to_string()))?;
        Ok(Self {
            root_public_key: root_keypair.public(),
            inner: token,
        })
    }

    /// Mint a new Biscuit token for the Pyana runtime with structured parameters.
    pub fn mint_pyana(
        root_keypair: &biscuit_auth::KeyPair,
        org_id: Option<u64>,
        apps: &[(String, String)],
        services: &[(String, String)],
        features: &[String],
        oauth_providers: &[String],
        oauth_scopes: &[String],
        user_id: Option<&str>,
        machine_id: Option<&str>,
        commands: &[String],
    ) -> Result<Self, TokenError> {
        let code = pyana::authority_datalog(
            org_id,
            apps,
            services,
            features,
            oauth_providers,
            oauth_scopes,
            user_id,
            machine_id,
            commands,
        )?;
        Self::mint(root_keypair, &code)
    }

    /// Deserialize and verify a Biscuit token from bytes.
    pub fn from_bytes(
        data: &[u8],
        root_public_key: biscuit_auth::PublicKey,
    ) -> Result<Self, TokenError> {
        let inner = Biscuit::from(data, root_public_key)
            .map_err(|e| TokenError::VerificationFailed(e.to_string()))?;
        Ok(Self {
            inner,
            root_public_key,
        })
    }

    /// Deserialize and verify from the `eb2_` prefixed string format.
    pub fn from_encoded(
        encoded: &str,
        root_public_key: biscuit_auth::PublicKey,
    ) -> Result<Self, TokenError> {
        let stripped = encoded
            .strip_prefix(TokenFormat::Biscuit.prefix())
            .or_else(|| encoded.strip_prefix("biscuit:"))
            .unwrap_or(encoded);
        let bytes = base64::engine::general_purpose::URL_SAFE_NO_PAD
            .decode(stripped)
            .map_err(|e| TokenError::Encoding(e.to_string()))?;
        Self::from_bytes(&bytes, root_public_key)
    }

    /// Access the inner `biscuit_auth::Biscuit` for advanced operations.
    pub fn inner(&self) -> &Biscuit {
        &self.inner
    }

    /// Build an authorizer with the Pyana standard policies.
    pub fn build_authorizer(
        &self,
        request: &AuthRequest,
    ) -> Result<biscuit_auth::Authorizer, TokenError> {
        let authorizer_code = pyana::authorizer_datalog(request)?;
        AuthorizerBuilder::new()
            .code(authorizer_code)
            .map_err(|e| TokenError::Datalog(e.to_string()))?
            .build(&self.inner)
            .map_err(|e| TokenError::Datalog(e.to_string()))
    }
}

impl AuthToken for BiscuitToken {
    fn format(&self) -> TokenFormat {
        TokenFormat::Biscuit
    }

    fn verify(&self, request: &AuthRequest) -> Result<TokenClearance, TokenError> {
        let mut authorizer = self.build_authorizer(request)?;

        let policy_idx = authorizer
            .authorize()
            .map_err(|e| TokenError::Denied(e.to_string()))?;

        // Extract granted capabilities from the authorized Datalog world
        let mut capabilities = Vec::new();

        // Query for app grants
        if let Ok(facts) = authorizer
            .query::<_, biscuit_auth::builder::Fact, _>("data($id, $actions) <- app($id, $actions)")
        {
            for fact in &facts {
                if fact.predicate.terms.len() == 2 {
                    let id = term_to_string(&fact.predicate.terms[0]);
                    let actions = term_to_string(&fact.predicate.terms[1]);
                    if let (Some(id), Some(actions)) = (id, actions) {
                        capabilities.push(TokenClearance::cap("app", &id, &actions));
                    }
                }
            }
        }

        // Query for service grants
        if let Ok(facts) = authorizer.query::<_, biscuit_auth::builder::Fact, _>(
            "data($name, $actions) <- service($name, $actions)",
        ) {
            for fact in &facts {
                if fact.predicate.terms.len() == 2 {
                    let name = term_to_string(&fact.predicate.terms[0]);
                    let actions = term_to_string(&fact.predicate.terms[1]);
                    if let (Some(name), Some(actions)) = (name, actions) {
                        capabilities.push(TokenClearance::cap("service", &name, &actions));
                    }
                }
            }
        }

        // Query for feature grants
        if let Ok(facts) =
            authorizer.query::<_, biscuit_auth::builder::Fact, _>("data($name) <- feature($name)")
        {
            for fact in &facts {
                if let Some(name) = fact.predicate.terms.first().and_then(term_to_string) {
                    capabilities.push(TokenClearance::cap("feature", &name, "*"));
                }
            }
        }

        // Query for oauth_scope grants
        if let Ok(facts) = authorizer
            .query::<_, biscuit_auth::builder::Fact, _>("data($scope) <- oauth_scope($scope)")
        {
            for fact in &facts {
                if let Some(scope) = fact.predicate.terms.first().and_then(term_to_string) {
                    capabilities.push(TokenClearance::cap("oauth_scope", &scope, "*"));
                }
            }
        }

        // Query for oauth_provider grants
        if let Ok(facts) = authorizer.query::<_, biscuit_auth::builder::Fact, _>(
            "data($provider) <- oauth_provider($provider)",
        ) {
            for fact in &facts {
                if let Some(provider) = fact.predicate.terms.first().and_then(term_to_string) {
                    capabilities.push(TokenClearance::cap("oauth_provider", &provider, "*"));
                }
            }
        }

        // Extract subject (user fact)
        let subject = authorizer
            .query::<_, biscuit_auth::builder::Fact, _>("data($uid) <- user($uid)")
            .ok()
            .and_then(|facts| facts.into_iter().next())
            .and_then(|f| f.predicate.terms.first().and_then(term_to_string));

        Ok(TokenClearance {
            matched_policy: Some(format!("policy_{}", policy_idx)),
            capabilities,
            format: TokenFormat::Biscuit,
            expires_at: None, // Biscuit time checks are opaque (embedded in Datalog checks)
            subject,
        })
    }

    fn attenuate(&self, restrictions: &Attenuation) -> Result<Box<dyn AuthToken>, TokenError> {
        let code = pyana::attenuation_datalog(restrictions)?;
        if code.is_empty() {
            return Err(TokenError::Malformed(
                "no restrictions specified for attenuation".into(),
            ));
        }

        let block = BlockBuilder::new()
            .code(code)
            .map_err(|e| TokenError::Datalog(e.to_string()))?;
        let attenuated = self
            .inner
            .append(block)
            .map_err(|e| TokenError::Crypto(e.to_string()))?;

        Ok(Box::new(BiscuitToken {
            inner: attenuated,
            root_public_key: self.root_public_key,
        }))
    }

    fn to_bytes(&self) -> Result<Vec<u8>, TokenError> {
        self.inner
            .to_vec()
            .map_err(|e| TokenError::Encoding(e.to_string()))
    }

    fn to_encoded(&self) -> Result<String, TokenError> {
        let bytes = self.to_bytes()?;
        let b64 = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&bytes);
        Ok(format!("{}{}", TokenFormat::Biscuit.prefix(), b64))
    }

    fn is_attenuable(&self) -> bool {
        !self.inner.container().proof.is_sealed()
    }

    fn seal(&self) -> Result<Box<dyn AuthToken>, TokenError> {
        let sealed = self
            .inner
            .seal()
            .map_err(|e| TokenError::Crypto(e.to_string()))?;
        Ok(Box::new(BiscuitToken {
            inner: sealed,
            root_public_key: self.root_public_key,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_keypair() -> biscuit_auth::KeyPair {
        biscuit_auth::KeyPair::new()
    }

    #[test]
    fn test_mint_and_verify() {
        let kp = test_keypair();
        let token = BiscuitToken::mint_pyana(
            &kp,
            Some(1),
            &[("test-app".into(), "rwcd".into())],
            &[("http".into(), "rw".into())],
            &[],
            &[],
            &[],
            Some("user-1"),
            None,
            &[],
        )
        .unwrap();

        let request = AuthRequest {
            app_id: Some("test-app".into()),
            action: Some("r".into()),
            service: Some("http".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let clearance = token.verify(&request).unwrap();
        assert_eq!(clearance.format, TokenFormat::Biscuit);
    }

    #[test]
    fn test_encode_decode_roundtrip() {
        let kp = test_keypair();
        let token = BiscuitToken::mint(&kp, "app(\"my-app\", \"rw\");").unwrap();

        let encoded = token.to_encoded().unwrap();
        assert!(encoded.starts_with("eb2_"));

        let decoded = BiscuitToken::from_encoded(&encoded, kp.public()).unwrap();
        assert_eq!(decoded.inner.block_count(), token.inner.block_count());
    }

    #[test]
    fn test_attenuate_restricts() {
        let kp = test_keypair();
        let token = BiscuitToken::mint_pyana(
            &kp,
            None,
            &[("my-app".into(), "rwcd".into())],
            &[],
            &[],
            &[],
            &[],
            Some("user-1"),
            None,
            &[],
        )
        .unwrap();

        let restricted = token
            .attenuate(&Attenuation {
                apps: vec![("my-app".into(), "r".into())],
                confine_user: Some("user-1".into()),
                ..Default::default()
            })
            .unwrap();

        // Should still verify for read
        let req = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert!(restricted.verify(&req).is_ok());
    }

    #[test]
    fn test_seal_prevents_attenuation() {
        let kp = test_keypair();
        let token = BiscuitToken::mint(&kp, "app(\"x\", \"r\");").unwrap();
        let sealed = token.seal().unwrap();

        let result = sealed.attenuate(&Attenuation {
            apps: vec![("x".into(), "r".into())],
            ..Default::default()
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_bytes_roundtrip() {
        let kp = test_keypair();
        let token = BiscuitToken::mint(&kp, "app(\"x\", \"r\");").unwrap();
        let bytes = token.to_bytes().unwrap();
        let decoded = BiscuitToken::from_bytes(&bytes, kp.public()).unwrap();
        assert_eq!(decoded.inner.block_count(), token.inner.block_count());
    }

    #[test]
    fn test_wrong_key_fails() {
        let kp1 = test_keypair();
        let kp2 = test_keypair();
        let token = BiscuitToken::mint(&kp1, "app(\"x\", \"r\");").unwrap();
        let bytes = token.to_bytes().unwrap();
        assert!(BiscuitToken::from_bytes(&bytes, kp2.public()).is_err());
    }
}
