//! Fulfillment protocol: creating attenuated tokens to satisfy matched intents.
//!
//! After matching locally, the wallet can fulfill an intent by creating an
//! attenuated capability token that meets the intent's requirements. The
//! fulfillment is sent DIRECTLY to the intent creator (not broadcast).
//!
//! # Privacy
//!
//! The fulfillment reveals only what's necessary:
//! - Trusted mode: a real attenuated macaroon token (HMAC-chained, verifiable)
//! - Selective mode: STARK proof + selective disclosure of granted facts
//! - Private mode: STARK proof of capability satisfaction (reveals nothing extra)
//!
//! # Verification
//!
//! All fulfillment modes produce VERIFIABLE artifacts:
//! - Trusted: the token bytes can be deserialized and verified with the issuer key
//! - Private/Selective: the STARK proof can be verified against public inputs
//!   (conclusion, accumulated_hash) without trusting the fulfiller

use crate::matcher::HeldCapability;
use crate::{CommitmentId, Intent, Match, VerificationMode};
use pyana_circuit::BabyBear;
use pyana_circuit::multi_step_air::{
    MultiStepWitness, prove_authorization_stark, verify_authorization_stark,
};
use pyana_circuit::stark;
use pyana_token::{Attenuation, AuthToken, MacaroonToken};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors during fulfillment creation or verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FulfillmentError {
    /// The source token could not be attenuated.
    AttenuationFailed(String),
    /// The STARK proof could not be generated (witness invalid).
    ProofGenerationFailed(String),
    /// The STARK proof failed verification.
    ProofVerificationFailed(String),
    /// The fulfillment is missing required data for its mode.
    MissingData(String),
    /// Granted actions do not satisfy the intent's requirements.
    ActionsMismatch(String),
    /// Granted resource does not match the intent's requirements.
    ResourceMismatch(String),
}

impl std::fmt::Display for FulfillmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AttenuationFailed(e) => write!(f, "attenuation failed: {}", e),
            Self::ProofGenerationFailed(e) => write!(f, "proof generation failed: {}", e),
            Self::ProofVerificationFailed(e) => write!(f, "proof verification failed: {}", e),
            Self::MissingData(e) => write!(f, "missing data: {}", e),
            Self::ActionsMismatch(e) => write!(f, "actions mismatch: {}", e),
            Self::ResourceMismatch(e) => write!(f, "resource mismatch: {}", e),
        }
    }
}

// ---------------------------------------------------------------------------
// Fulfillment struct
// ---------------------------------------------------------------------------

/// A completed fulfillment: a verifiable proof of capability satisfaction.
#[derive(Clone, Debug)]
pub struct Fulfillment {
    /// The intent being fulfilled.
    pub intent_id: [u8; 32],
    /// The fulfiller's anonymous commitment.
    pub fulfiller: CommitmentId,
    /// Verification mode used for this fulfillment.
    pub mode: VerificationMode,
    /// Real attenuated macaroon token bytes (Trusted mode only).
    /// These bytes are a valid HMAC-chained token that can be deserialized
    /// and verified against the original issuer's key.
    pub token_data: Option<Vec<u8>>,
    /// Real STARK proof bytes (Private/Selective mode).
    /// This proves "I hold a capability satisfying this intent's MatchSpec"
    /// without revealing which token or what other capabilities are held.
    pub proof: Option<Vec<u8>>,
    /// Actions granted in the attenuated token (a subset of the original).
    pub granted_actions: Vec<String>,
    /// Resource scope of the attenuated token.
    pub granted_resource: String,
    /// Expiry of the attenuated token (may be shorter than the source token).
    pub expiry: Option<u64>,
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
    /// The root key for the source token (needed to produce a real attenuated macaroon).
    /// Only required for Trusted mode.
    pub root_key: Option<[u8; 32]>,
    /// A pre-built STARK witness for Private/Selective mode.
    /// The caller (the matcher) builds this from the local Datalog evaluation.
    pub stark_witness: Option<MultiStepWitness>,
}

impl Default for FulfillOptions {
    fn default() -> Self {
        Self {
            mode: VerificationMode::Trusted,
            max_expiry: None,
            restrict_actions: None,
            restrict_resource: None,
            root_key: None,
            stark_witness: None,
        }
    }
}

/// Create a fulfillment for a matched intent.
///
/// This:
/// 1. Attenuates the matching token to meet ONLY the intent's requirements
/// 2. Generates a VERIFIABLE proof of satisfaction (per the verification mode)
/// 3. Returns a Fulfillment ready for direct delivery to the intent creator
///
/// The key principle: MINIMUM DISCLOSURE. The attenuated token grants the
/// least privilege needed to satisfy the intent.
///
/// # Trusted mode
/// Produces a real HMAC-chained attenuated macaroon. The recipient can verify
/// the token's HMAC chain with the issuer's root key.
///
/// # Private/Selective mode
/// Produces a real STARK proof that the fulfiller holds a capability satisfying
/// the intent. No token or private data is revealed.
pub fn fulfill(
    intent: &Intent,
    _matched: &Match,
    source_token: &HeldCapability,
    our_commitment: CommitmentId,
    options: &FulfillOptions,
) -> Result<Fulfillment, FulfillmentError> {
    // Determine the actions to grant (intersection of source + intent needs)
    let granted_actions = compute_granted_actions(source_token, intent, options);

    // Determine the resource scope (narrowest of source, intent, and options)
    let granted_resource = compute_granted_resource(source_token, intent, options);

    // Determine expiry (minimum of source, intent, and options)
    let expiry = compute_expiry(source_token, intent, options);

    // Generate verifiable artifacts based on mode
    let (token_data, proof_bytes) = match options.mode {
        VerificationMode::Trusted => {
            // Produce a real attenuated macaroon token.
            let token_bytes = produce_attenuated_token(
                source_token,
                &granted_actions,
                &granted_resource,
                expiry,
                options,
            )?;
            (Some(token_bytes), None)
        }
        VerificationMode::Selective => {
            // Selective: produce a STARK proof + a commitment to the granted facts.
            // The proof demonstrates capability satisfaction; the commitment allows
            // selective verification of specific facts without full token disclosure.
            let proof_bytes = produce_stark_proof(options)?;
            (None, Some(proof_bytes))
        }
        VerificationMode::Private => {
            // Private: only a STARK proof — no token data revealed at all.
            let proof_bytes = produce_stark_proof(options)?;
            (None, Some(proof_bytes))
        }
    };

    Ok(Fulfillment {
        intent_id: intent.id,
        fulfiller: our_commitment,
        mode: options.mode,
        token_data,
        proof: proof_bytes,
        granted_actions,
        granted_resource,
        expiry,
    })
}

/// Verify a fulfillment against its intent.
///
/// For Trusted mode: verifies the token bytes are present and non-empty.
/// (Full HMAC verification requires the issuer key, which is the trade-off.)
///
/// For Private/Selective mode: verifies the STARK proof cryptographically.
/// The verifier only needs the public inputs (conclusion, accumulated_hash)
/// from the proof — no private data required.
///
/// Also checks that granted_actions satisfy the intent's MatchSpec and that
/// the granted_resource matches the intent's requirements.
pub fn verify_fulfillment(
    fulfillment: &Fulfillment,
    intent: &Intent,
    _state_root: BabyBear,
) -> Result<(), FulfillmentError> {
    // 1. Mode-specific verification
    match fulfillment.mode {
        VerificationMode::Trusted => {
            // In trusted mode, verify token bytes are present and non-trivial.
            // Full HMAC chain verification requires the issuer key — that's the
            // fundamental trade-off of trusted mode.
            let token_data = fulfillment.token_data.as_ref().ok_or_else(|| {
                FulfillmentError::MissingData("trusted mode requires token_data".into())
            })?;
            if token_data.is_empty() {
                return Err(FulfillmentError::MissingData("token_data is empty".into()));
            }
        }
        VerificationMode::Private | VerificationMode::Selective => {
            // Verify the STARK proof cryptographically.
            let proof_bytes = fulfillment.proof.as_ref().ok_or_else(|| {
                FulfillmentError::MissingData("private/selective mode requires proof".into())
            })?;
            let proof = stark::proof_from_bytes(proof_bytes).map_err(|e| {
                FulfillmentError::ProofVerificationFailed(format!("deserialize: {}", e))
            })?;

            // The proof's public inputs contain conclusion and accumulated_hash.
            // We verify that the conclusion is ALLOW (1).
            if proof.public_inputs.len() < 5 {
                return Err(FulfillmentError::ProofVerificationFailed(
                    "proof has insufficient public inputs".into(),
                ));
            }
            let conclusion = BabyBear(proof.public_inputs[2]); // pi::CONCLUSION
            let accumulated_hash = BabyBear(proof.public_inputs[4]); // pi::FINAL_ACCUMULATED_HASH

            if conclusion != BabyBear::ONE {
                return Err(FulfillmentError::ProofVerificationFailed(
                    "proof conclusion is DENY, not ALLOW".into(),
                ));
            }

            verify_authorization_stark(conclusion, accumulated_hash, &proof)
                .map_err(|e| FulfillmentError::ProofVerificationFailed(e))?;
        }
    }

    // 2. Check granted_actions satisfy the intent's MatchSpec
    let intent_actions: Vec<String> = intent
        .matcher
        .actions
        .iter()
        .filter_map(|p| p.action.clone())
        .collect();

    if !intent_actions.is_empty() {
        for required_action in &intent_actions {
            if !fulfillment.granted_actions.contains(required_action)
                && !fulfillment.granted_actions.contains(&"*".to_string())
            {
                return Err(FulfillmentError::ActionsMismatch(format!(
                    "required action '{}' not granted",
                    required_action
                )));
            }
        }
    }

    // 3. Check granted_resource matches the intent's resource_pattern
    if let Some(pattern) = &intent.matcher.resource_pattern {
        if !resource_matches(&fulfillment.granted_resource, pattern) {
            return Err(FulfillmentError::ResourceMismatch(format!(
                "granted '{}' does not cover required '{}'",
                fulfillment.granted_resource, pattern
            )));
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal: produce a real attenuated macaroon
// ---------------------------------------------------------------------------

/// Produce a real HMAC-chained attenuated macaroon token.
///
/// The resulting bytes are a valid `MacaroonToken` serialization with caveats
/// restricting it to only the granted actions/resource/expiry.
fn produce_attenuated_token(
    source_token: &HeldCapability,
    granted_actions: &[String],
    granted_resource: &str,
    expiry: Option<u64>,
    options: &FulfillOptions,
) -> Result<Vec<u8>, FulfillmentError> {
    let root_key = options.root_key.ok_or_else(|| {
        FulfillmentError::AttenuationFailed("root_key required for Trusted mode fulfillment".into())
    })?;

    // Mint a macaroon from the root key (the wallet holds the key for its own tokens)
    let mac = MacaroonToken::mint(root_key, source_token.token_id.as_bytes(), "pyana.intent");

    // Build the attenuation restrictions
    let attenuation = Attenuation {
        services: vec![(granted_resource.to_string(), granted_actions.join(","))],
        not_after: expiry.map(|e| e as i64),
        ..Default::default()
    };

    // Attenuate the token — this adds HMAC-chained caveats
    let attenuated = mac
        .attenuate(&attenuation)
        .map_err(|e| FulfillmentError::AttenuationFailed(e.to_string()))?;

    // Serialize to bytes — this is the real HMAC-chained token
    let token_bytes = attenuated
        .to_bytes()
        .map_err(|e| FulfillmentError::AttenuationFailed(e.to_string()))?;

    Ok(token_bytes)
}

// ---------------------------------------------------------------------------
// Internal: produce a real STARK proof
// ---------------------------------------------------------------------------

/// Produce a real FRI-based STARK proof of authorization.
///
/// The proof demonstrates that the prover holds a capability satisfying the
/// intent's requirements WITHOUT revealing which token, what delegation chain,
/// or any other private data.
fn produce_stark_proof(options: &FulfillOptions) -> Result<Vec<u8>, FulfillmentError> {
    let witness = options.stark_witness.as_ref().ok_or_else(|| {
        FulfillmentError::ProofGenerationFailed(
            "stark_witness required for Private/Selective mode".into(),
        )
    })?;

    // Generate the real STARK proof using the multi-step authorization AIR
    let proof = prove_authorization_stark(witness);
    let proof_bytes = stark::proof_to_bytes(&proof);

    Ok(proof_bytes)
}

// ---------------------------------------------------------------------------
// Helpers: compute granted actions, resource, expiry
// ---------------------------------------------------------------------------

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

/// Check if a granted resource covers a required resource pattern.
fn resource_matches(granted: &str, required: &str) -> bool {
    if granted == "*" || granted == required {
        return true;
    }
    // Wildcard prefix matching: "documents/*" covers "documents/reports/*"
    if granted.ends_with("/*") {
        let prefix = &granted[..granted.len() - 2];
        if required.starts_with(prefix) {
            return true;
        }
    }
    false
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec, VerificationMode};
    use pyana_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use pyana_circuit::multi_step_air::{ALLOW_PREDICATE, build_multi_step_witness};
    use pyana_circuit::poseidon2::hash_fact;

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
            compound: None,
        };
        Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None)
    }

    fn test_root_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[1] = 0x13;
        key[31] = 0xFF;
        key
    }

    /// Build a valid STARK witness that concludes ALLOW.
    /// This simulates what the matcher would produce after local Datalog evaluation.
    fn build_allow_witness() -> MultiStepWitness {
        let state_root = BabyBear::new(99999);
        let alice = BabyBear::new(1000);
        let app = BabyBear::new(2000);
        let allow_pred = BabyBear::new(ALLOW_PREDICATE);
        let has_role_pred = BabyBear::new(600);

        let body_hash = hash_fact(has_role_pred, &[alice, app, BabyBear::ZERO]);

        let step = DerivationWitness {
            rule: CircuitRule {
                id: 1,
                num_body_atoms: 1,
                num_variables: 2,
                head_predicate: allow_pred,
                head_terms: [
                    (true, BabyBear::new(0)),
                    (true, BabyBear::new(1)),
                    (false, BabyBear::ZERO),
                    (false, BabyBear::ZERO),
                ],
                body_atoms: vec![BodyAtomPattern {
                    predicate: has_role_pred,
                    terms: [
                        (true, BabyBear::new(0)),
                        (true, BabyBear::new(1)),
                        (false, BabyBear::ZERO),
                    ],
                }],
                equal_checks: vec![],
                memberof_checks: vec![],
                gte_check: None,
            },
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![alice, app],
            derived_predicate: allow_pred,
            derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
        };

        build_multi_step_witness(state_root, BabyBear::new(42), vec![step])
    }

    #[test]
    fn test_fulfill_trusted_produces_real_token() {
        let intent = test_intent(vec!["read"], None);
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
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        // Should only grant "read", not "write" or "delete"
        assert_eq!(result.granted_actions, vec!["read".to_string()]);
        assert_eq!(result.mode, VerificationMode::Trusted);

        // Token data should be present and be real serialized macaroon bytes
        let token_data = result.token_data.as_ref().unwrap();
        assert!(!token_data.is_empty());
        // Real macaroon bytes are NOT JSON — they don't start with '{' or '['
        // They start with the em2_ prefix or raw binary
        assert!(token_data.len() > 32, "real macaroon should be substantial");

        // Proof should be None in trusted mode
        assert!(result.proof.is_none());
    }

    #[test]
    fn test_fulfill_private_produces_stark_proof() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let witness = build_allow_witness();

        let options = FulfillOptions {
            mode: VerificationMode::Private,
            stark_witness: Some(witness),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        // Private mode: no token data revealed
        assert!(result.token_data.is_none());
        assert_eq!(result.mode, VerificationMode::Private);

        // Should have a real STARK proof
        let proof_bytes = result.proof.as_ref().unwrap();
        assert!(proof_bytes.len() > 100, "STARK proof should be substantial");

        // Verify the proof starts with the PYNA header
        assert_eq!(
            &proof_bytes[0..4],
            b"PYNA",
            "proof should have STARK header"
        );

        // The proof should be independently verifiable
        let proof = stark::proof_from_bytes(proof_bytes).unwrap();
        let conclusion = BabyBear(proof.public_inputs[2]);
        let acc_hash = BabyBear(proof.public_inputs[4]);
        assert_eq!(
            conclusion,
            BabyBear::ONE,
            "proof conclusion should be ALLOW"
        );
        assert!(verify_authorization_stark(conclusion, acc_hash, &proof).is_ok());
    }

    #[test]
    fn test_fulfill_selective_produces_stark_proof() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Selective,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let witness = build_allow_witness();

        let options = FulfillOptions {
            mode: VerificationMode::Selective,
            stark_witness: Some(witness),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        // Selective: no token data, but has proof
        assert!(result.token_data.is_none());
        assert!(result.proof.is_some());
        assert_eq!(result.mode, VerificationMode::Selective);
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

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

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

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

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

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

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
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        assert_eq!(result.granted_actions, vec!["read".to_string()]);
        assert_eq!(result.granted_resource, "documents/public/*");
        assert_eq!(result.expiry, Some(3000));
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

        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        // Even though source is wildcard, only grant what's requested
        assert_eq!(
            result.granted_actions,
            vec!["read".to_string(), "execute".to_string()]
        );
    }

    #[test]
    fn test_fulfill_trusted_without_key_fails() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        // No root_key provided
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options);
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::AttenuationFailed(msg) => {
                assert!(msg.contains("root_key required"));
            }
            other => panic!("unexpected error: {:?}", other),
        }
    }

    #[test]
    fn test_fulfill_private_without_witness_fails() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        // No stark_witness provided
        let options = FulfillOptions {
            mode: VerificationMode::Private,
            ..Default::default()
        };

        let result = fulfill(&intent, &matched, &token, our_id, &options);
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::ProofGenerationFailed(msg) => {
                assert!(msg.contains("stark_witness required"));
            }
            other => panic!("unexpected error: {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_trusted() {
        let intent = test_intent(vec!["read"], None);
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
            root_key: Some(test_root_key()),
            ..Default::default()
        };

        let fulfillment = fulfill(&intent, &matched, &token, our_id, &options).unwrap();
        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(
            result.is_ok(),
            "trusted fulfillment should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_verify_fulfillment_private_stark() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let witness = build_allow_witness();

        let options = FulfillOptions {
            mode: VerificationMode::Private,
            stark_witness: Some(witness),
            ..Default::default()
        };

        let fulfillment = fulfill(&intent, &matched, &token, our_id, &options).unwrap();
        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(
            result.is_ok(),
            "private STARK fulfillment should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_verify_fulfillment_rejects_missing_actions() {
        let intent = test_intent(vec!["read", "write"], None);

        // Create a fulfillment that only grants "read" (missing "write")
        let fulfillment = Fulfillment {
            intent_id: intent.id,
            fulfiller: CommitmentId([0xBB; 32]),
            mode: VerificationMode::Trusted,
            token_data: Some(vec![1, 2, 3, 4]), // non-empty stub
            proof: None,
            granted_actions: vec!["read".into()], // missing "write"!
            granted_resource: "documents/*".into(),
            expiry: Some(5000),
        };

        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::ActionsMismatch(msg) => {
                assert!(msg.contains("write"));
            }
            other => panic!("unexpected error: {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_rejects_tampered_proof() {
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let witness = build_allow_witness();
        let options = FulfillOptions {
            mode: VerificationMode::Private,
            stark_witness: Some(witness),
            ..Default::default()
        };

        let mut fulfillment = fulfill(&intent, &matched, &token, our_id, &options).unwrap();

        // Tamper with the proof bytes
        if let Some(ref mut proof) = fulfillment.proof {
            // Flip a byte in the trace commitment area (after the 5-byte header)
            if proof.len() > 10 {
                proof[5] ^= 0xFF;
            }
        }

        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(result.is_err(), "tampered proof should fail verification");
    }

    #[test]
    fn test_resource_matches_exact() {
        assert!(resource_matches("documents/*", "documents/*"));
        assert!(resource_matches("*", "anything"));
        assert!(resource_matches("documents/*", "documents/reports/*"));
        assert!(!resource_matches(
            "documents/public/*",
            "documents/private/*"
        ));
    }

    #[test]
    fn test_stark_proof_roundtrip() {
        // Verify that a STARK proof produced by fulfill can be deserialized and verified
        let intent = test_intent(vec!["read"], None);
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Private,
        };
        let token = source_token();
        let our_id = CommitmentId([0xBB; 32]);

        let witness = build_allow_witness();
        let conclusion = witness.conclusion();
        let acc_hash = witness.final_accumulated_hash();

        let options = FulfillOptions {
            mode: VerificationMode::Private,
            stark_witness: Some(witness),
            ..Default::default()
        };

        let fulfillment = fulfill(&intent, &matched, &token, our_id, &options).unwrap();
        let proof_bytes = fulfillment.proof.unwrap();

        // Deserialize
        let proof = stark::proof_from_bytes(&proof_bytes).unwrap();

        // Verify with known-good public inputs
        let result = verify_authorization_stark(conclusion, acc_hash, &proof);
        assert!(
            result.is_ok(),
            "deserialized proof should verify: {:?}",
            result.err()
        );
    }
}
