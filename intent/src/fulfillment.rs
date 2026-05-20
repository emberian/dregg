//! Fulfillment protocol: creating attenuated tokens to satisfy matched intents.
//!
//! After matching locally, the wallet can fulfill an intent by creating an
//! attenuated capability token that meets the intent's requirements. The
//! fulfillment is sent DIRECTLY to the intent creator (not broadcast).
//!
//! # Privacy
//!
//! The fulfillment reveals only what's necessary:
//! - Trusted mode: the attenuated token itself (minimal, but reveals the token)
//! - Selective mode: proof that specific requirements are met
//! - Private mode: STARK proof of capability satisfaction (reveals nothing extra)

use crate::{CommitmentId, Intent, Match, VerificationMode};
use crate::matcher::HeldCapability;

/// A completed fulfillment: an attenuated token + proof ready for delivery.
#[derive(Clone, Debug)]
pub struct Fulfillment {
    /// The intent being fulfilled.
    pub intent_id: [u8; 32],
    /// The match that triggered this fulfillment.
    pub matched: Match,
    /// The attenuated token data (format depends on mode).
    /// - Trusted: serialized attenuated token
    /// - Selective: partial token + selective disclosure proof
    /// - Private: only the STARK proof (no token revealed)
    pub token_data: Option<Vec<u8>>,
    /// Actions granted in the attenuated token (a subset of the original).
    pub granted_actions: Vec<String>,
    /// Resource scope of the attenuated token.
    pub granted_resource: String,
    /// Expiry of the attenuated token (may be shorter than the source token).
    pub expiry: Option<u64>,
    /// The fulfiller's anonymous commitment.
    pub fulfiller: CommitmentId,
}

/// Options for creating a fulfillment.
#[derive(Clone, Debug)]
pub struct FulfillOptions {
    /// Verification mode: how much to reveal.
    pub mode: VerificationMode,
    /// Maximum expiry for the attenuated token (caps the source token's expiry).
    pub max_expiry: Option<u64>,
    /// Restrict to only these actions (attenuation).
    pub restrict_actions: Option<Vec<String>>,
    /// Restrict to a narrower resource scope.
    pub restrict_resource: Option<String>,
}

impl Default for FulfillOptions {
    fn default() -> Self {
        Self {
            mode: VerificationMode::Trusted,
            max_expiry: None,
            restrict_actions: None,
            restrict_resource: None,
        }
    }
}

/// Create a fulfillment for a matched intent.
///
/// This:
/// 1. Attenuates the matching token to meet ONLY the intent's requirements
/// 2. Generates a proof of satisfaction (per the verification mode)
/// 3. Returns a Fulfillment ready for direct delivery to the intent creator
///
/// The key principle: MINIMUM DISCLOSURE. The attenuated token grants the
/// least privilege needed to satisfy the intent.
pub fn fulfill(
    intent: &Intent,
    matched: &Match,
    source_token: &HeldCapability,
    our_commitment: CommitmentId,
    options: &FulfillOptions,
) -> Fulfillment {
    // Determine the actions to grant (intersection of source + intent needs)
    let granted_actions = compute_granted_actions(source_token, intent, options);

    // Determine the resource scope (narrowest of source, intent, and options)
    let granted_resource = compute_granted_resource(source_token, intent, options);

    // Determine expiry (minimum of source, intent, and options)
    let expiry = compute_expiry(source_token, intent, options);

    // Generate token data based on mode
    let token_data = match options.mode {
        VerificationMode::Trusted => {
            // In trusted mode, produce a serialized attenuated token.
            // The real implementation would use MacaroonToken::attenuate() or similar.
            let token_repr = AttenuatedTokenRepr {
                actions: granted_actions.clone(),
                resource: granted_resource.clone(),
                expiry,
                intent_id: intent.id,
            };
            Some(serde_json::to_vec(&token_repr).unwrap_or_default())
        }
        VerificationMode::Selective => {
            // Selective: commit to the granted facts without revealing the full token
            let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-selective-v1");
            hasher.update(&intent.id);
            for action in &granted_actions {
                hasher.update(action.as_bytes());
            }
            hasher.update(granted_resource.as_bytes());
            if let Some(exp) = expiry {
                hasher.update(&exp.to_le_bytes());
            }
            Some(hasher.finalize().as_bytes().to_vec())
        }
        VerificationMode::Private => {
            // Private: only the STARK proof from the Match is used.
            // No additional token data is revealed.
            None
        }
    };

    Fulfillment {
        intent_id: intent.id,
        matched: matched.clone(),
        token_data,
        granted_actions,
        granted_resource,
        expiry,
        fulfiller: our_commitment,
    }
}

/// Compute the set of actions to grant in the attenuated token.
///
/// Takes the intersection of:
/// - What the source token grants
/// - What the intent requests
/// - Any additional restrictions from options
fn compute_granted_actions(
    source: &HeldCapability,
    intent: &Intent,
    options: &FulfillOptions,
) -> Vec<String> {
    // Start with the source token's actions
    let mut actions = source.actions.clone();

    // If options restrict actions, intersect
    if let Some(restricted) = &options.restrict_actions {
        actions.retain(|a| restricted.contains(a) || a == "*");
    }

    // If the intent specifies required actions, intersect with those
    let intent_actions: Vec<String> = intent
        .matcher
        .actions
        .iter()
        .filter_map(|p| p.action.clone())
        .collect();

    if !intent_actions.is_empty() {
        // If source has wildcard, grant exactly what's requested
        if actions.contains(&"*".to_string()) {
            actions = intent_actions;
        } else {
            // Otherwise intersect
            actions.retain(|a| intent_actions.contains(a));
        }
    }

    actions
}

/// Compute the resource scope for the attenuated token.
fn compute_granted_resource(
    source: &HeldCapability,
    intent: &Intent,
    options: &FulfillOptions,
) -> String {
    // If options restrict resource, use that
    if let Some(restricted) = &options.restrict_resource {
        return restricted.clone();
    }

    // If intent specifies a resource pattern, use that (if source covers it)
    if let Some(pattern) = &intent.matcher.resource_pattern {
        if source.resource == "*" || source.resource == *pattern {
            return pattern.clone();
        }
        // If source has a broader pattern that covers the intent's, use intent's (narrower)
        if source.resource.ends_with("/*") {
            let prefix = &source.resource[..source.resource.len() - 2];
            if pattern.starts_with(prefix) {
                return pattern.clone();
            }
        }
    }

    // Default to the source token's resource (don't widen)
    source.resource.clone()
}

/// Compute the expiry for the attenuated token.
fn compute_expiry(
    source: &HeldCapability,
    intent: &Intent,
    options: &FulfillOptions,
) -> Option<u64> {
    let mut expiry = source.expiry;

    // Cap at intent's expiry (no point granting longer than the intent lives)
    if intent.expiry < u64::MAX {
        expiry = Some(match expiry {
            Some(e) => e.min(intent.expiry),
            None => intent.expiry,
        });
    }

    // Cap at options max_expiry
    if let Some(max) = options.max_expiry {
        expiry = Some(match expiry {
            Some(e) => e.min(max),
            None => max,
        });
    }

    expiry
}

/// Internal representation for serializing an attenuated token in trusted mode.
#[derive(serde::Serialize, serde::Deserialize, Debug)]
struct AttenuatedTokenRepr {
    actions: Vec<String>,
    resource: String,
    expiry: Option<u64>,
    intent_id: [u8; 32],
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec, VerificationMode};

    fn source_token() -> HeldCapability {
        HeldCapability {
            token_id: "tok_source".into(),
            actions: vec!["read".into(), "write".into(), "delete".into()],
            resource: "documents/*".into(),
            app_id: Some("myapp".into()),
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: Some(10000),
            budget: None,
            sensitivity: crate::matcher::Sensitivity::Normal,
        }
    }

    fn test_intent(actions: Vec<&str>, resource_pattern: Option<&str>) -> Intent {
        let spec = MatchSpec {
            actions: actions
                .into_iter()
                .map(|a| ActionPattern {
                    action: Some(a.into()),
                    resource: None,
                })
                .collect(),
            constraints: vec![],
            min_budget: None,
            resource_pattern: resource_pattern.map(String::from),
        };
        Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            5000,
            None,
        )
    }

    #[test]
    fn test_fulfill_attenuates_actions() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let result = fulfill(&intent, &matched, &token, our_id, &FulfillOptions::default());

        // Should only grant "read", not "write" or "delete"
        assert_eq!(result.granted_actions, vec!["read".to_string()]);
    }

    #[test]
    fn test_fulfill_narrows_resource() {
        let intent = test_intent(vec!["read"], Some("documents/reports/*"));
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token(); // has "documents/*"
        let our_id = CommitmentId([0xBB; 32]);

        let result = fulfill(&intent, &matched, &token, our_id, &FulfillOptions::default());

        // Should narrow to the intent's requested pattern
        assert_eq!(result.granted_resource, "documents/reports/*");
    }

    #[test]
    fn test_fulfill_caps_expiry() {
        let intent = test_intent(vec!["read"], None); // intent expires at 5000
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token(); // token expires at 10000
        let our_id = CommitmentId([0xBB; 32]);

        let result = fulfill(&intent, &matched, &token, our_id, &FulfillOptions::default());

        // Expiry should be capped at intent's expiry (5000), not token's (10000)
        assert_eq!(result.expiry, Some(5000));
    }

    #[test]
    fn test_fulfill_options_restrict_further() {
        let intent = test_intent(vec!["read", "write"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            max_expiry: Some(3000),
            restrict_actions: Some(vec!["read".into()]),
            restrict_resource: Some("documents/public/*".into()),
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options);

        assert_eq!(result.granted_actions, vec!["read".to_string()]);
        assert_eq!(result.granted_resource, "documents/public/*");
        assert_eq!(result.expiry, Some(3000));
    }

    #[test]
    fn test_fulfill_trusted_produces_token_data() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let result = fulfill(&intent, &matched, &token, our_id, &FulfillOptions::default());
        assert!(result.token_data.is_some());

        // Should be valid JSON
        let data = result.token_data.unwrap();
        let parsed: AttenuatedTokenRepr = serde_json::from_slice(&data).unwrap();
        assert_eq!(parsed.actions, vec!["read"]);
        assert_eq!(parsed.intent_id, intent.id);
    }

    #[test]
    fn test_fulfill_private_no_token_data() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: Some(vec![0xDE, 0xAD]),
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let options = FulfillOptions {
            mode: VerificationMode::Private,
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options);

        // Private mode: no token data revealed
        assert!(result.token_data.is_none());
    }

    #[test]
    fn test_fulfill_wildcard_source_grants_only_requested() {
        let mut token = source_token();
        token.actions = vec!["*".into()]; // wildcard source

        let intent = test_intent(vec!["read", "execute"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let our_id = CommitmentId([0xBB; 32]);

        let result = fulfill(&intent, &matched, &token, our_id, &FulfillOptions::default());

        // Even though source is wildcard, only grant what's requested
        assert_eq!(
            result.granted_actions,
            vec!["read".to_string(), "execute".to_string()]
        );
    }
}
