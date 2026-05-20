//! Local matching engine.
//!
//! Evaluates whether held capability tokens can satisfy a broadcast intent.
//! Matching runs ENTIRELY locally (no network calls) and uses Datalog evaluation
//! to check constraints. The result is a [`Match`] that can optionally include
//! a STARK proof of satisfaction.
//!
//! # Privacy guarantee
//!
//! The matcher never reveals WHICH token matched, only THAT a match exists.
//! The proof (if generated) demonstrates knowledge of a valid token satisfying
//! the intent's MatchSpec without revealing the token itself.

use crate::{
    ActionPattern, CommitmentId, Constraint, Intent, IntentKind, Match, MatchSpec,
    VerificationMode,
};

/// Sensitivity level for a held capability.
///
/// Controls whether a capability can be automatically matched against incoming intents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sensitivity {
    /// Public capabilities: freely matchable by the engine.
    Public,
    /// Normal capabilities: matchable, but not against Query intents.
    Normal,
    /// Sensitive capabilities: NEVER matched automatically.
    /// Requires explicit user action to match against any intent.
    Sensitive,
}

/// A held capability token in the wallet's simplified representation.
///
/// This is the wallet-side view of a token -- enough information to evaluate
/// whether it satisfies a MatchSpec without needing the full serialized token.
#[derive(Clone, Debug)]
pub struct HeldCapability {
    /// Unique identifier for this token in the wallet.
    pub token_id: String,
    /// Actions this token grants (e.g., "read", "write").
    pub actions: Vec<String>,
    /// Resource this token applies to (e.g., "documents/*", "*").
    pub resource: String,
    /// App this token is scoped to, if any.
    pub app_id: Option<String>,
    /// Service this token is scoped to, if any.
    pub service: Option<String>,
    /// User this token is confined to, if any.
    pub user_id: Option<String>,
    /// Features this token grants.
    pub features: Vec<String>,
    /// OAuth provider, if relevant.
    pub oauth_provider: Option<String>,
    /// Expiry timestamp (Unix seconds), if any.
    pub expiry: Option<u64>,
    /// Remaining budget, if budgeted.
    pub budget: Option<u64>,
    /// Sensitivity level: controls automatic matching behavior.
    /// Sensitive capabilities are never matched against incoming intents without
    /// explicit user action.
    pub sensitivity: Sensitivity,
}

/// Result of attempting to match an intent against held capabilities.
#[derive(Clone, Debug)]
pub enum MatchResult {
    /// A match was found. Contains the matching token index and a Match struct.
    Matched {
        /// Index into the held_tokens slice that satisfied the intent.
        token_index: usize,
        /// The match result ready for fulfillment.
        matched: Match,
    },
    /// No held token satisfies this intent.
    NoMatch,
    /// The intent has expired.
    Expired,
    /// The intent kind is not matchable from our perspective.
    /// (e.g., we see an Offer but we're looking for Needs)
    WrongKind,
}

/// Attempt to match an intent against a set of held capability tokens.
///
/// This is the core matching function. It:
/// 1. Checks intent validity (not expired, correct kind)
/// 2. For each held token, evaluates whether it satisfies the MatchSpec
/// 3. Returns the first match found (or NoMatch)
///
/// All evaluation is LOCAL -- no network calls, no side effects.
pub fn match_intent(
    intent: &Intent,
    held_tokens: &[HeldCapability],
    our_commitment: CommitmentId,
    mode: VerificationMode,
    now: u64,
) -> MatchResult {
    // Check expiry
    if intent.is_expired(now) {
        return MatchResult::Expired;
    }

    // Only match against Need intents (we satisfy them).
    // For Offer intents, the matching direction is reversed (handled elsewhere).
    // Query intents NEVER trigger automatic matching -- they are a probing vector.
    // Queries require explicit user opt-in (handled via a separate API).
    if intent.kind == IntentKind::Offer || intent.kind == IntentKind::Query {
        return MatchResult::WrongKind;
    }

    // Try each held token (skip Sensitive tokens -- they require explicit user action)
    for (idx, token) in held_tokens.iter().enumerate() {
        if token.sensitivity == Sensitivity::Sensitive {
            continue;
        }
        if satisfies_spec(token, &intent.matcher, now) {
            let matched = Match {
                intent_id: intent.id,
                satisfier: our_commitment,
                proof: generate_proof(token, intent, mode),
                mode,
            };
            return MatchResult::Matched {
                token_index: idx,
                matched,
            };
        }
    }

    MatchResult::NoMatch
}

/// Check if a single held token satisfies a MatchSpec.
///
/// Evaluates:
/// 1. Action patterns (does the token grant the required actions?)
/// 2. Resource pattern (does the token's resource match the pattern?)
/// 3. Constraints (app, service, user, expiry, features, etc.)
/// 4. Budget requirements
pub fn satisfies_spec(token: &HeldCapability, spec: &MatchSpec, now: u64) -> bool {
    // Check action patterns
    if !spec.actions.is_empty() && !actions_match(token, &spec.actions) {
        return false;
    }

    // Check resource pattern
    if let Some(pattern) = &spec.resource_pattern {
        if !resource_matches(&token.resource, pattern) {
            return false;
        }
    }

    // Check constraints
    for constraint in &spec.constraints {
        if !constraint_satisfied(token, constraint, now) {
            return false;
        }
    }

    // Check budget
    if let Some(min_budget) = spec.min_budget {
        match token.budget {
            Some(b) if b >= min_budget => {}
            Some(_) => return false,
            // No budget info means unlimited -- satisfies any min_budget
            None => {}
        }
    }

    true
}

/// Check if a token's actions satisfy the required action patterns.
fn actions_match(token: &HeldCapability, patterns: &[ActionPattern]) -> bool {
    for pattern in patterns {
        // Check action match
        if let Some(required_action) = &pattern.action {
            // Wildcard resource on token means it matches anything
            if token.resource == "*" || pattern.resource.is_none() {
                // Just need the action
                if !token.actions.iter().any(|a| a == required_action || a == "*") {
                    return false;
                }
            } else {
                // Need both action AND resource match
                let resource_ok = pattern
                    .resource
                    .as_ref()
                    .is_none_or(|r| resource_matches(&token.resource, r));
                let action_ok = token.actions.iter().any(|a| a == required_action || a == "*");
                if !resource_ok || !action_ok {
                    return false;
                }
            }
        }
        // If action is None (wildcard), any token action satisfies it.
        // Just check resource if specified.
        if pattern.action.is_none() {
            if let Some(resource) = &pattern.resource {
                if !resource_matches(&token.resource, resource) {
                    return false;
                }
            }
        }
    }
    true
}

/// Check if a token's resource matches a pattern.
///
/// Supports:
/// - Exact match: "documents/readme.md" matches "documents/readme.md"
/// - Wildcard: "*" matches anything
/// - Prefix glob: "documents/*" matches "documents/readme.md"
fn resource_matches(token_resource: &str, pattern: &str) -> bool {
    if token_resource == "*" || pattern == "*" {
        return true;
    }
    if token_resource == pattern {
        return true;
    }
    // Glob matching via the globset crate
    if let Ok(glob) = globset::Glob::new(pattern) {
        let matcher = glob.compile_matcher();
        if matcher.is_match(token_resource) {
            return true;
        }
    }
    // Also check if token resource is a superset pattern that covers the request
    if token_resource.ends_with("/*") {
        let prefix = &token_resource[..token_resource.len() - 2];
        if pattern.starts_with(prefix) {
            return true;
        }
    }
    false
}

/// Check if a single constraint is satisfied by a token.
fn constraint_satisfied(token: &HeldCapability, constraint: &Constraint, now: u64) -> bool {
    match constraint {
        Constraint::AppId(app) => token.app_id.as_ref().is_some_and(|a| a == app),
        Constraint::Service(svc) => token.service.as_ref().is_some_and(|s| s == svc),
        Constraint::UserId(uid) => {
            // If token has no user constraint, it's valid for any user
            token.user_id.is_none() || token.user_id.as_ref().is_some_and(|u| u == uid)
        }
        Constraint::NotExpiredAt(ts) => {
            let check_time = *ts as u64;
            token.expiry.is_none_or(|exp| exp > check_time)
        }
        Constraint::Feature(feat) => token.features.contains(feat),
        Constraint::OAuthProvider(provider) => {
            token.oauth_provider.as_ref().is_some_and(|p| p == provider)
        }
        Constraint::Custom { predicate, value } => {
            // Custom constraints: extensible matching. For now, treat as
            // a feature-like check (the real implementation would evaluate
            // arbitrary Datalog predicates).
            let _ = (predicate, value, now);
            // Conservative: custom constraints don't match unless explicitly handled
            false
        }
    }
}

/// Generate a proof of match (optional, depends on VerificationMode).
///
/// - Trusted: no proof needed
/// - Selective: partial proof showing specific facts
/// - Private: full STARK proof of capability satisfaction
fn generate_proof(
    token: &HeldCapability,
    intent: &Intent,
    mode: VerificationMode,
) -> Option<Vec<u8>> {
    match mode {
        VerificationMode::Trusted => None,
        VerificationMode::Selective => {
            // In selective mode, we produce a proof that reveals:
            // - The token grants the required action(s)
            // - The token covers the required resource
            // Without revealing: token ID, full action set, delegation chain
            //
            // For now, produce a commitment to the match facts.
            let mut hasher = blake3::Hasher::new_derive_key("pyana-selective-match-v1");
            hasher.update(&intent.id);
            hasher.update(token.token_id.as_bytes());
            for action in &token.actions {
                hasher.update(action.as_bytes());
            }
            hasher.update(token.resource.as_bytes());
            Some(hasher.finalize().as_bytes().to_vec())
        }
        VerificationMode::Private => {
            // In private mode, we would generate a full STARK proof via
            // pyana-circuit's prove_authorization_stark. The proof demonstrates:
            // - There exists a token T in the wallet
            // - T's Datalog evaluation produces ALLOW for the intent's MatchSpec
            // - T is not expired
            // Without revealing T or anything else about the wallet contents.
            //
            // For now, produce a commitment (the real circuit integration comes
            // when the multi_step_air is wired up to this matcher).
            let mut hasher = blake3::Hasher::new_derive_key("pyana-private-match-v1");
            hasher.update(&intent.id);
            hasher.update(token.token_id.as_bytes());
            // Add randomness so the proof doesn't leak token identity across matches
            let mut rand_bytes = [0u8; 32];
            crate::getrandom(&mut rand_bytes);
            hasher.update(&rand_bytes);
            Some(hasher.finalize().as_bytes().to_vec())
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CommitmentId, Intent, IntentKind, MatchSpec};

    fn make_token(actions: &[&str], resource: &str) -> HeldCapability {
        HeldCapability {
            token_id: "tok_test".into(),
            actions: actions.iter().map(|s| s.to_string()).collect(),
            resource: resource.into(),
            app_id: None,
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: None,
            budget: None,
            sensitivity: Sensitivity::Normal,
        }
    }

    fn make_intent(actions: Vec<ActionPattern>, constraints: Vec<Constraint>) -> Intent {
        let spec = MatchSpec {
            actions,
            constraints,
            min_budget: None,
            resource_pattern: None,
        };
        Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX, // never expires for tests
            None,
        )
    }

    #[test]
    fn test_basic_action_match() {
        let token = make_token(&["read", "write"], "documents/*");
        let intent = make_intent(
            vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        assert!(matches!(result, MatchResult::Matched { .. }));
    }

    #[test]
    fn test_action_not_held() {
        let token = make_token(&["read"], "documents/*");
        let intent = make_intent(
            vec![ActionPattern {
                action: Some("delete".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        assert!(matches!(result, MatchResult::NoMatch));
    }

    #[test]
    fn test_wildcard_action_matches_anything() {
        let token = make_token(&["*"], "documents/*");
        let intent = make_intent(
            vec![ActionPattern {
                action: Some("delete".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        assert!(matches!(result, MatchResult::Matched { .. }));
    }

    #[test]
    fn test_resource_pattern_matching() {
        let token = make_token(&["read"], "documents/reports/*");
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: Some("documents/reports/*".into()),
        };
        assert!(satisfies_spec(&token, &spec, 100));

        let spec_miss = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: Some("secrets/*".into()),
        };
        assert!(!satisfies_spec(&token, &spec_miss, 100));
    }

    #[test]
    fn test_constraint_app_id() {
        let mut token = make_token(&["read"], "*");
        token.app_id = Some("my-app".into());

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::AppId("my-app".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));

        let spec_miss = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::AppId("other-app".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(!satisfies_spec(&token, &spec_miss, 100));
    }

    #[test]
    fn test_constraint_service() {
        let mut token = make_token(&["read", "write"], "*");
        token.service = Some("http".into());

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![Constraint::Service("http".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));
    }

    #[test]
    fn test_constraint_not_expired() {
        let mut token = make_token(&["read"], "*");
        token.expiry = Some(5000);

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::NotExpiredAt(3000)],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));

        let spec_expired = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::NotExpiredAt(6000)],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(!satisfies_spec(&token, &spec_expired, 100));
    }

    #[test]
    fn test_constraint_feature() {
        let mut token = make_token(&["read"], "*");
        token.features = vec!["gpu".into(), "ai".into()];

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::Feature("gpu".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));

        let spec_miss = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::Feature("quantum".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(!satisfies_spec(&token, &spec_miss, 100));
    }

    #[test]
    fn test_budget_constraint() {
        let mut token = make_token(&["execute"], "*");
        token.budget = Some(1000);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("execute".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(500),
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));

        let spec_too_much = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("execute".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(2000),
            resource_pattern: None,
        };
        assert!(!satisfies_spec(&token, &spec_too_much, 100));
    }

    #[test]
    fn test_expired_intent_does_not_match() {
        let token = make_token(&["read"], "*");
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            100, // expires at t=100
            None,
        );
        let our_id = CommitmentId([0xBB; 32]);
        // now=200, intent expired at 100
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 200);
        assert!(matches!(result, MatchResult::Expired));
    }

    #[test]
    fn test_offer_intent_returns_wrong_kind() {
        let token = make_token(&["read"], "*");
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Offer,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX,
            None,
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        assert!(matches!(result, MatchResult::WrongKind));
    }

    #[test]
    fn test_multiple_tokens_first_match_wins() {
        let token1 = make_token(&["read"], "docs/*");
        let token2 = make_token(&["read", "write"], "*");
        let intent = make_intent(
            vec![ActionPattern {
                action: Some("write".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(
            &intent,
            &[token1, token2],
            our_id,
            VerificationMode::Trusted,
            100,
        );
        match result {
            MatchResult::Matched { token_index, .. } => {
                assert_eq!(token_index, 1); // token2 is the first that matches "write"
            }
            _ => panic!("expected Matched"),
        }
    }

    #[test]
    fn test_selective_proof_is_generated() {
        let token = make_token(&["read"], "*");
        let intent = make_intent(
            vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(
            &intent,
            &[token],
            our_id,
            VerificationMode::Selective,
            100,
        );
        match result {
            MatchResult::Matched { matched, .. } => {
                assert!(matched.proof.is_some());
                assert_eq!(matched.proof.unwrap().len(), 32); // BLAKE3 output
            }
            _ => panic!("expected Matched"),
        }
    }

    #[test]
    fn test_user_id_unrestricted_token_matches_any_user() {
        let token = make_token(&["read"], "*");
        // token.user_id is None -- unrestricted

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::UserId("alice".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec, 100));
    }

    #[test]
    fn test_user_id_restricted_token_must_match() {
        let mut token = make_token(&["read"], "*");
        token.user_id = Some("alice".into());

        let spec_ok = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::UserId("alice".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(satisfies_spec(&token, &spec_ok, 100));

        let spec_wrong = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::UserId("bob".into())],
            min_budget: None,
            resource_pattern: None,
        };
        assert!(!satisfies_spec(&token, &spec_wrong, 100));
    }

    #[test]
    fn test_combined_constraints() {
        let mut token = make_token(&["read", "write"], "api/*");
        token.app_id = Some("dashboard".into());
        token.service = Some("http".into());
        token.features = vec!["v2".into()];
        token.expiry = Some(9999);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![
                Constraint::AppId("dashboard".into()),
                Constraint::Service("http".into()),
                Constraint::Feature("v2".into()),
                Constraint::NotExpiredAt(5000),
            ],
            min_budget: None,
            resource_pattern: Some("api/*".into()),
        };
        assert!(satisfies_spec(&token, &spec, 100));
    }

    #[test]
    fn test_query_intent_returns_wrong_kind() {
        let token = make_token(&["read"], "*");
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Query,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX,
            None,
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        assert!(matches!(result, MatchResult::WrongKind));
    }

    #[test]
    fn test_sensitive_token_never_auto_matched() {
        let mut token = make_token(&["read", "write", "admin"], "*");
        token.sensitivity = Sensitivity::Sensitive;

        let intent = make_intent(
            vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(&intent, &[token], our_id, VerificationMode::Trusted, 100);
        // Even though the token satisfies the spec, it's Sensitive so it's skipped
        assert!(matches!(result, MatchResult::NoMatch));
    }

    #[test]
    fn test_sensitive_token_skipped_but_normal_still_matches() {
        let mut sensitive_token = make_token(&["read", "admin"], "*");
        sensitive_token.sensitivity = Sensitivity::Sensitive;

        let normal_token = make_token(&["read"], "*");

        let intent = make_intent(
            vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            vec![],
        );
        let our_id = CommitmentId([0xBB; 32]);
        let result = match_intent(
            &intent,
            &[sensitive_token, normal_token],
            our_id,
            VerificationMode::Trusted,
            100,
        );
        match result {
            MatchResult::Matched { token_index, .. } => {
                // Should match the second (Normal) token, not the first (Sensitive)
                assert_eq!(token_index, 1);
            }
            _ => panic!("expected Matched"),
        }
    }
}
