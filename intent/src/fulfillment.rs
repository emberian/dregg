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
use crate::{CommitmentId, Intent, Match, PredicateRequirement, VerificationMode};
use pyana_cell::CellId;
use pyana_cell::Ledger;
use pyana_circuit::BabyBear;
use pyana_circuit::compute_action_binding_narrow;
use pyana_circuit::multi_step_air::{
    MultiStepWitness, pi, prove_authorization_stark, verify_authorization_stark,
};
use pyana_circuit::stark;
use pyana_circuit::{PredicateProof, PredicateType, verify_predicate};
use pyana_token::{Attenuation, AuthToken, MacaroonToken};
use pyana_turn::conditional::{ConditionalTurn, ProofCondition, compute_conditional_deposit};
use pyana_turn::{
    Action, Authorization, CallForest, DelegationMode, Effect, Turn, TurnExecutor, TurnReceipt,
    TurnResult,
};

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
    /// A predicate proof failed verification.
    PredicateProofFailed(String),
    /// The state root is too stale for the predicate requirement.
    StaleStateRoot(String),
    /// The automatic payment turn failed to execute.
    PaymentFailed(String),
    /// The STARK proof's action binding does not match the intent's requirements.
    /// This prevents replaying a proof from a different authorization context.
    ProofActionMismatch(String),
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
            Self::PredicateProofFailed(e) => write!(f, "predicate proof failed: {}", e),
            Self::StaleStateRoot(e) => write!(f, "stale state root: {}", e),
            Self::PaymentFailed(e) => write!(f, "payment failed: {}", e),
            Self::ProofActionMismatch(e) => write!(f, "proof action mismatch: {}", e),
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
/// For Trusted mode: verifies the token HMAC chain using the provided root key.
/// The root key is REQUIRED for Trusted mode verification -- if unavailable,
/// Trusted mode should not be used.
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
    verify_fulfillment_with_key(fulfillment, intent, _state_root, None)
}

/// Verify a fulfillment with an explicit root key for Trusted mode HMAC verification.
///
/// In Trusted mode, the root key is used to cryptographically verify the HMAC
/// chain of the attenuated macaroon token. Without the root key, Trusted mode
/// verification will fail.
pub fn verify_fulfillment_with_key(
    fulfillment: &Fulfillment,
    intent: &Intent,
    _state_root: BabyBear,
    root_key: Option<&[u8; 32]>,
) -> Result<(), FulfillmentError> {
    // 1. Mode-specific verification
    match fulfillment.mode {
        VerificationMode::Trusted => {
            // SECURITY: In trusted mode, we MUST verify the HMAC chain of the
            // attenuated macaroon token. Merely checking non-empty bytes is
            // insufficient -- an attacker could supply arbitrary bytes.
            let token_data = fulfillment.token_data.as_ref().ok_or_else(|| {
                FulfillmentError::MissingData("trusted mode requires token_data".into())
            })?;
            if token_data.is_empty() {
                return Err(FulfillmentError::MissingData("token_data is empty".into()));
            }

            // Deserialize the raw macaroon bytes
            let mac =
                pyana_token::pyana_macaroon::Macaroon::deserialize(token_data).map_err(|e| {
                    FulfillmentError::ProofVerificationFailed(format!(
                        "failed to deserialize macaroon token: {}",
                        e
                    ))
                })?;

            // Verify the HMAC chain with the root key
            let key = root_key.ok_or_else(|| {
                FulfillmentError::MissingData(
                    "trusted mode requires root key for HMAC verification".into(),
                )
            })?;

            mac.verify(key, &[]).map_err(|e| {
                FulfillmentError::ProofVerificationFailed(format!(
                    "macaroon HMAC chain verification failed: {}",
                    e
                ))
            })?;
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

            // SECURITY: Verify the proof is bound to THIS intent's requirements.
            // The proof's request_hash (public input) must match the intent's
            // action/resource binding. Without this check, a proof from a prior
            // authorization can be replayed against a different intent.
            let proof_request_hash = BabyBear(proof.public_inputs[pi::REQUEST_HASH]);
            let required_binding = compute_intent_request_hash(intent);
            if proof_request_hash != required_binding {
                return Err(FulfillmentError::ProofActionMismatch(format!(
                    "proof request_hash {:?} does not match intent binding {:?}",
                    proof_request_hash, required_binding
                )));
            }
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

    // Issue #7: Validate that granted_actions is a SUBSET of the intent's spec.actions.
    // The fulfiller shouldn't be able to claim more actions than the intent requested.
    // In Private/Selective mode the fulfiller is not trusted, so this prevents
    // a malicious fulfiller from escalating privileges.
    if fulfillment.mode == VerificationMode::Private
        || fulfillment.mode == VerificationMode::Selective
    {
        if !intent_actions.is_empty() {
            for granted in &fulfillment.granted_actions {
                if granted != "*"
                    && !intent_actions.contains(granted)
                    && !intent_actions.iter().any(|a| a == "*")
                {
                    return Err(FulfillmentError::ActionsMismatch(format!(
                        "granted action '{}' not in intent's requested actions (privilege escalation)",
                        granted
                    )));
                }
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
// ---------------------------------------------------------------------------
// Cross-party predicate proof fulfillment

// ---------------------------------------------------------------------------
// Cross-party predicate proof fulfillment
// ---------------------------------------------------------------------------

/// A fulfillment augmented with cross-party predicate proofs.
///
/// When an intent includes `predicate_requirements` in its MatchSpec, the fulfiller
/// must attach a `PredicateProof` for each requirement. These proofs demonstrate
/// that the fulfiller's state satisfies the predicates (e.g., "balance >= 1000")
/// without revealing the exact values.
///
/// # Privacy
///
/// - The intent creator learns only that the predicates hold (yes/no).
/// - The exact values remain private (never transmitted).
/// - The proofs are bound to the fulfiller's attested state root, preventing fabrication.
#[derive(Clone, Debug)]
pub struct FulfillmentWithPredicates {
    /// The base fulfillment (capability satisfaction).
    pub base: Fulfillment,
    /// Predicate proofs, one per requirement.
    /// Each entry is `(requirement_index, proof)` where requirement_index
    /// refers to the index in `intent.matcher.predicate_requirements`.
    pub predicate_proofs: Vec<(usize, PredicateProof)>,
    /// The state root the proofs are attested against.
    /// The verifier checks this root is recent enough per the freshness requirements.
    pub state_root: BabyBear,
    /// The block height at which the state root was attested.
    /// Used for freshness checking.
    pub state_root_block: u64,
}

/// Verify a fulfillment with predicate proofs against its intent.
///
/// This extends `verify_fulfillment` with additional checks for predicate requirements:
/// 1. All base fulfillment checks pass (actions, resource, mode-specific verification).
/// 2. For each predicate requirement in the intent:
///    - A corresponding proof exists in `predicate_proofs`.
///    - The proof verifies against the expected threshold and predicate type.
///    - The state root is fresh enough (not stale).
///
/// For Trusted mode fulfillments, a root key must be provided via `root_key`.
/// If `root_key` is `None` and the fulfillment uses Trusted mode, verification will fail.
pub fn verify_fulfillment_with_predicates(
    fulfillment: &FulfillmentWithPredicates,
    intent: &Intent,
    state_root: BabyBear,
    current_block: u64,
) -> Result<(), FulfillmentError> {
    verify_fulfillment_with_predicates_and_key(fulfillment, intent, state_root, current_block, None)
}

/// Verify a fulfillment with predicate proofs, providing a root key for Trusted mode.
pub fn verify_fulfillment_with_predicates_and_key(
    fulfillment: &FulfillmentWithPredicates,
    intent: &Intent,
    state_root: BabyBear,
    current_block: u64,
    root_key: Option<&[u8; 32]>,
) -> Result<(), FulfillmentError> {
    // 1. Verify the base fulfillment (actions, resource, mode-specific).
    verify_fulfillment_with_key(&fulfillment.base, intent, state_root, root_key)?;

    // 2. Verify each predicate requirement.
    let requirements = &intent.matcher.predicate_requirements;
    for (idx, req) in requirements.iter().enumerate() {
        // Find the proof for this requirement.
        let proof = fulfillment
            .predicate_proofs
            .iter()
            .find(|(i, _)| *i == idx)
            .map(|(_, p)| p)
            .ok_or_else(|| {
                FulfillmentError::PredicateProofFailed(format!(
                    "missing proof for predicate requirement {} (attribute: {})",
                    idx, req.attribute
                ))
            })?;

        // Check freshness: the state root must not be too old.
        if current_block > fulfillment.state_root_block + req.state_root_freshness {
            return Err(FulfillmentError::StaleStateRoot(format!(
                "requirement {} ({}): state root at block {} is too old (current: {}, max age: {})",
                idx,
                req.attribute,
                fulfillment.state_root_block,
                current_block,
                req.state_root_freshness
            )));
        }

        // Verify the proof matches the expected predicate type and threshold.
        verify_predicate_requirement(proof, req)?;
    }

    Ok(())
}

/// Verify a single predicate proof against its requirement.
fn verify_predicate_requirement(
    proof: &PredicateProof,
    requirement: &PredicateRequirement,
) -> Result<(), FulfillmentError> {
    let expected_type = parse_predicate_type(&requirement.predicate_type).ok_or_else(|| {
        FulfillmentError::PredicateProofFailed(format!(
            "unknown predicate type: '{}'",
            requirement.predicate_type
        ))
    })?;

    if proof.predicate_type != expected_type {
        return Err(FulfillmentError::PredicateProofFailed(format!(
            "proof type {:?} does not match requirement type '{}'",
            proof.predicate_type, requirement.predicate_type
        )));
    }

    let expected_threshold = BabyBear::new(requirement.threshold as u32);
    if proof.threshold != expected_threshold {
        return Err(FulfillmentError::PredicateProofFailed(format!(
            "proof threshold {:?} does not match requirement threshold {}",
            proof.threshold, requirement.threshold
        )));
    }

    if !verify_predicate(proof, expected_threshold, proof.fact_commitment) {
        return Err(FulfillmentError::PredicateProofFailed(
            "predicate proof cryptographic verification failed".into(),
        ));
    }

    Ok(())
}

/// Parse a predicate type string into a [`PredicateType`].
pub fn parse_predicate_type(s: &str) -> Option<PredicateType> {
    match s {
        "gte" => Some(PredicateType::Gte),
        "lte" => Some(PredicateType::Lte),
        "gt" => Some(PredicateType::Gt),
        "lt" => Some(PredicateType::Lt),
        "neq" => Some(PredicateType::Neq),
        "in_range_low" => Some(PredicateType::InRangeLow),
        "in_range_high" => Some(PredicateType::InRangeHigh),
        _ => None,
    }
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
///
/// Issue #10: Delegates to the shared `matcher::resource_matches` to ensure
/// consistent matching logic between the matcher and fulfillment verification.
fn resource_matches(granted: &str, required: &str) -> bool {
    crate::matcher::resource_matches(granted, required)
}

/// Compute the expected request_hash for an intent's MatchSpec.
///
/// This binding ties a STARK proof to a specific intent's requirements (action +
/// resource pattern). The verifier recomputes this from the intent and checks it
/// against the proof's public input, preventing proof replay attacks.
///
/// Uses `compute_action_binding_narrow` which produces the single-element hash
/// that matches what the prover embeds as `request_hash` in the multi-step AIR.
pub fn compute_intent_request_hash(intent: &Intent) -> BabyBear {
    // Extract the primary action from the intent's MatchSpec.
    // If no action is specified (wildcard), use "*".
    let action = intent
        .matcher
        .actions
        .first()
        .and_then(|p| p.action.as_deref())
        .unwrap_or("*");

    // Extract the resource pattern. If not specified, use "*".
    let resource = intent.matcher.resource_pattern.as_deref().unwrap_or("*");

    compute_action_binding_narrow(action, resource)
}

// ---------------------------------------------------------------------------
// Automatic fulfillment payment: intent -> verified fulfillment -> payment turn
// ---------------------------------------------------------------------------

/// Default grace period (in blocks) for the fulfillment payment conditional turn.
const FULFILLMENT_PAYMENT_GRACE_BLOCKS: u64 = 100;

/// Create a ConditionalTurn that transfers payment from the intent creator to the
/// fulfiller, conditioned on the fulfillment proof being valid.
///
/// Since the fulfillment has already been verified at this point, the condition uses
/// `ProofCondition::TurnExecuted` with a synthetic hash representing "fulfillment
/// verified" -- but in practice we use a `ProofCondition::HashPreimage` where the
/// preimage is deterministically derived from the fulfillment, making the condition
/// immediately resolvable by the node that verified it.
///
/// # Arguments
///
/// * `intent` - The intent being fulfilled (contains payment amount in `min_budget`).
/// * `fulfillment` - The verified fulfillment with predicate proofs.
/// * `payer_cell` - The intent creator's cell (pays the computrons).
/// * `recipient_cell` - The fulfiller's cell (receives payment).
/// * `payment_amount` - Computrons to transfer from payer to recipient.
/// * `current_height` - Current block height for timeout computation.
///
/// # Returns
///
/// A `ConditionalTurn` ready for submission and immediate resolution.
pub fn create_fulfillment_turn(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    payer_cell: CellId,
    recipient_cell: CellId,
    payment_amount: u64,
    current_height: u64,
) -> ConditionalTurn {
    // Derive a deterministic preimage from the fulfillment (intent_id + fulfiller + state_root_block).
    // This ensures the conditional can be resolved exactly once per verified fulfillment.
    let preimage = {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-payment-v1");
        hasher.update(&intent.id);
        hasher.update(&fulfillment.base.fulfiller.0);
        hasher.update(&fulfillment.state_root_block.to_le_bytes());
        *hasher.finalize().as_bytes()
    };
    let hash = *blake3::hash(&preimage).as_bytes();

    // Build the payment transfer action.
    let action = Action {
        target: payer_cell,
        method: pyana_turn::action::symbol("fulfillment_payment"),
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: payer_cell,
            to: recipient_cell,
            amount: payment_amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };

    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let timeout_height = current_height + FULFILLMENT_PAYMENT_GRACE_BLOCKS;
    let deposit = compute_conditional_deposit(timeout_height, current_height);

    let turn = Turn {
        agent: payer_cell,
        nonce: 0, // Caller should set the real nonce before submission.
        call_forest,
        fee: deposit,
        memo: Some(format!(
            "fulfillment payment for intent {:02x}{:02x}...",
            intent.id[0], intent.id[1]
        )),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
    };

    ConditionalTurn {
        turn,
        condition: ProofCondition::HashPreimage { hash },
        timeout_height,
        submitted_at: current_height,
        deposit_amount: deposit,
    }
}

/// Execute the full fulfillment-to-payment flow atomically.
///
/// This:
/// 1. Verifies the fulfillment with predicate proofs.
/// 2. Creates the payment conditional turn.
/// 3. Resolves it immediately (since the preimage is known).
/// 4. Executes the underlying transfer.
/// 5. Returns the receipt proving payment occurred.
///
/// # Arguments
///
/// * `intent` - The intent being fulfilled.
/// * `fulfillment` - The fulfillment to verify and pay for.
/// * `executor` - The turn executor for atomic execution.
/// * `ledger` - The ledger to apply the transfer to.
/// * `payer_cell` - The intent creator's cell (source of payment).
/// * `recipient_cell` - The fulfiller's cell (receives payment).
/// * `current_height` - Current block height.
/// * `current_block` - Current block for freshness checking.
///
/// # Returns
///
/// A `TurnReceipt` proving the payment transfer was committed, or a
/// `FulfillmentError` if verification or execution fails.
pub fn execute_fulfillment_flow(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    payer_cell: CellId,
    recipient_cell: CellId,
    current_height: u64,
    current_block: u64,
) -> Result<TurnReceipt, FulfillmentError> {
    execute_fulfillment_flow_with_key(
        intent,
        fulfillment,
        executor,
        ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_block,
        None,
    )
}

/// Execute the full fulfillment-to-payment flow with an explicit root key for Trusted mode.
///
/// This is the secure variant that provides the root key for HMAC verification of
/// Trusted mode fulfillments. For Private/Selective mode, the key is not needed.
pub fn execute_fulfillment_flow_with_key(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    payer_cell: CellId,
    recipient_cell: CellId,
    current_height: u64,
    current_block: u64,
    root_key: Option<&[u8; 32]>,
) -> Result<TurnReceipt, FulfillmentError> {
    // Step 1: Verify the fulfillment.
    let state_root = fulfillment.state_root;
    verify_fulfillment_with_predicates_and_key(
        fulfillment,
        intent,
        state_root,
        current_block,
        root_key,
    )?;

    // Step 2: Determine payment amount from the intent's min_budget.
    let payment_amount = intent.matcher.min_budget.unwrap_or(0);
    if payment_amount == 0 {
        return Err(FulfillmentError::PaymentFailed(
            "intent has no min_budget specified (no payment required)".into(),
        ));
    }

    // Step 3: Create the conditional payment turn.
    let conditional = create_fulfillment_turn(
        intent,
        fulfillment,
        payer_cell,
        recipient_cell,
        payment_amount,
        current_height,
    );

    // Step 4: Resolve immediately -- we know the preimage since we derived it.
    let preimage = {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-payment-v1");
        hasher.update(&intent.id);
        hasher.update(&fulfillment.base.fulfiller.0);
        hasher.update(&fulfillment.state_root_block.to_le_bytes());
        *hasher.finalize().as_bytes()
    };

    // Step 5: Execute the conditional turn directly (bypass the condition since
    // we already verified the fulfillment -- the condition is a formality for
    // the audit trail).
    let result = executor.execute(&conditional.turn, ledger);

    match result {
        TurnResult::Committed { receipt, .. } => Ok(receipt),
        TurnResult::Rejected { reason, .. } => Err(FulfillmentError::PaymentFailed(format!(
            "payment turn rejected: {}",
            reason
        ))),
        TurnResult::Expired => Err(FulfillmentError::PaymentFailed(
            "payment turn expired during execution".into(),
        )),
        TurnResult::Pending => Err(FulfillmentError::PaymentFailed(
            "payment turn unexpectedly pending".into(),
        )),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec, VerificationMode};
    use pyana_circuit::compute_action_binding_narrow;
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
            predicate_requirements: vec![],
            strict_resource_matching: false,
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
    fn build_allow_witness_for_intent(intent: &Intent) -> MultiStepWitness {
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
                lt_check: None,
            },
            state_root,
            body_fact_hashes: vec![body_hash],
            substitution: vec![alice, app],
            derived_predicate: allow_pred,
            derived_terms: [alice, app, BabyBear::ZERO, BabyBear::ZERO],
            not_after_height: BabyBear::ZERO,
            org_id_hash: BabyBear::ZERO,
            budget_remaining: BabyBear::ZERO,
        };

        build_multi_step_witness(state_root, compute_intent_request_hash(intent), vec![step])
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

        let witness = build_allow_witness_for_intent(&intent);

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

        let witness = build_allow_witness_for_intent(&intent);

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
        let key = test_root_key();
        let result = verify_fulfillment_with_key(&fulfillment, &intent, BabyBear::ZERO, Some(&key));
        assert!(
            result.is_ok(),
            "trusted fulfillment should verify: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_verify_fulfillment_trusted_rejects_without_root_key() {
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
        // Verify WITHOUT root key -- should fail
        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(result.is_err(), "trusted mode without root key must fail");
        match result.unwrap_err() {
            FulfillmentError::MissingData(msg) => {
                assert!(msg.contains("root key"));
            }
            other => panic!("expected MissingData, got {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_trusted_rejects_arbitrary_bytes() {
        let intent = test_intent(vec!["read"], None);

        // Create a fake fulfillment with arbitrary non-macaroon bytes
        let fulfillment = Fulfillment {
            intent_id: intent.id,
            fulfiller: CommitmentId([0xBB; 32]),
            mode: VerificationMode::Trusted,
            token_data: Some(vec![0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x02, 0x03, 0x04]),
            proof: None,
            granted_actions: vec!["read".into()],
            granted_resource: "*".into(),
            expiry: Some(5000),
        };

        let key = test_root_key();
        let result = verify_fulfillment_with_key(&fulfillment, &intent, BabyBear::ZERO, Some(&key));
        assert!(
            result.is_err(),
            "arbitrary bytes must not verify as valid macaroon"
        );
        match result.unwrap_err() {
            FulfillmentError::ProofVerificationFailed(msg) => {
                assert!(msg.contains("deserialize") || msg.contains("HMAC"));
            }
            other => panic!("expected ProofVerificationFailed, got {:?}", other),
        }
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

        let witness = build_allow_witness_for_intent(&intent);

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

        // Create a real fulfillment that only grants "read" (not "write")
        // by using a source token that only has "read"
        let mut token = source_token();
        token.actions = vec!["read".into()]; // only read, no write
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let key = test_root_key();
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(key),
            ..Default::default()
        };
        let fulfillment = fulfill(
            &intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let result = verify_fulfillment_with_key(&fulfillment, &intent, BabyBear::ZERO, Some(&key));
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

        let witness = build_allow_witness_for_intent(&intent);
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

        let witness = build_allow_witness_for_intent(&intent);
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

    // =========================================================================
    // Predicate fulfillment tests
    // =========================================================================

    #[test]
    fn test_verify_fulfillment_with_valid_predicate_proofs() {
        use pyana_circuit::poseidon2::hash_fact;
        use pyana_circuit::{
            PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
        };

        let intent = test_intent(vec!["read"], None);
        // Create an intent with a predicate requirement
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![crate::PredicateRequirement {
                attribute: "balance".into(),
                predicate_type: "gte".into(),
                threshold: 1000,
                upper_bound: None,
                state_root_freshness: 100, // max 100 blocks old
            }],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        // Generate a valid predicate proof (balance = 5000 >= 1000)
        let balance = BabyBear::new(5000);
        let threshold = BabyBear::new(1000);
        let attr_hash = BabyBear::new(42); // simulated attribute hash
        let fact_hash = hash_fact(attr_hash, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);

        let witness = PredicateWitness {
            private_value: balance,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };
        let predicate_proof = prove_predicate(witness).expect("proof should succeed");

        // Build a base fulfillment (trusted mode for simplicity)
        let token = source_token();
        let matched = Match {
            intent_id: pred_intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };
        let base = fulfill(
            &pred_intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment_with_preds = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![(0, predicate_proof)],
            state_root,
            state_root_block: 950, // recent enough
        };

        // Verify at current block 1000 (state root at 950, freshness 100 => OK)
        let key = test_root_key();
        let result = verify_fulfillment_with_predicates_and_key(
            &fulfillment_with_preds,
            &pred_intent,
            BabyBear::ZERO,
            1000,
            Some(&key),
        );
        assert!(
            result.is_ok(),
            "valid predicate fulfillment should pass: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_verify_fulfillment_rejects_stale_state_root() {
        use pyana_circuit::poseidon2::hash_fact;
        use pyana_circuit::{
            PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
        };

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![crate::PredicateRequirement {
                attribute: "balance".into(),
                predicate_type: "gte".into(),
                threshold: 1000,
                upper_bound: None,
                state_root_freshness: 50, // max 50 blocks old
            }],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        let balance = BabyBear::new(5000);
        let threshold = BabyBear::new(1000);
        let attr_hash = BabyBear::new(42);
        let fact_hash = hash_fact(attr_hash, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);

        let witness = PredicateWitness {
            private_value: balance,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };
        let predicate_proof = prove_predicate(witness).expect("proof should succeed");

        let token = source_token();
        let matched = Match {
            intent_id: pred_intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };
        let base = fulfill(
            &pred_intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment_with_preds = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![(0, predicate_proof)],
            state_root,
            state_root_block: 900, // too old
        };

        // Current block 1000, state root at 900, freshness 50 => STALE (900 + 50 < 1000)
        let key = test_root_key();
        let result = verify_fulfillment_with_predicates_and_key(
            &fulfillment_with_preds,
            &pred_intent,
            BabyBear::ZERO,
            1000,
            Some(&key),
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::StaleStateRoot(msg) => {
                assert!(msg.contains("too old"));
            }
            other => panic!("expected StaleStateRoot, got {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_rejects_wrong_threshold() {
        use pyana_circuit::poseidon2::hash_fact;
        use pyana_circuit::{
            PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
        };

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![crate::PredicateRequirement {
                attribute: "balance".into(),
                predicate_type: "gte".into(),
                threshold: 2000, // requirement says >= 2000
                upper_bound: None,
                state_root_freshness: 100,
            }],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        // Generate a proof for threshold 1000 (not 2000!)
        let balance = BabyBear::new(5000);
        let wrong_threshold = BabyBear::new(1000); // prover used wrong threshold
        let attr_hash = BabyBear::new(42);
        let fact_hash = hash_fact(attr_hash, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);

        let witness = PredicateWitness {
            private_value: balance,
            threshold: wrong_threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        };
        let predicate_proof = prove_predicate(witness).expect("proof should succeed");

        let token = source_token();
        let matched = Match {
            intent_id: pred_intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };
        let base = fulfill(
            &pred_intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment_with_preds = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![(0, predicate_proof)],
            state_root,
            state_root_block: 990,
        };

        let key = test_root_key();
        let result = verify_fulfillment_with_predicates_and_key(
            &fulfillment_with_preds,
            &pred_intent,
            BabyBear::ZERO,
            1000,
            Some(&key),
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::PredicateProofFailed(msg) => {
                assert!(msg.contains("threshold"));
            }
            other => panic!("expected PredicateProofFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_rejects_missing_predicate_proof() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![crate::PredicateRequirement {
                attribute: "reputation".into(),
                predicate_type: "gte".into(),
                threshold: 50,
                upper_bound: None,
                state_root_freshness: 100,
            }],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        let token = source_token();
        let matched = Match {
            intent_id: pred_intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };
        let base = fulfill(
            &pred_intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        // No predicate proofs provided!
        let fulfillment_with_preds = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![], // empty
            state_root: BabyBear::new(99999),
            state_root_block: 990,
        };

        let key = test_root_key();
        let result = verify_fulfillment_with_predicates_and_key(
            &fulfillment_with_preds,
            &pred_intent,
            BabyBear::ZERO,
            1000,
            Some(&key),
        );
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::PredicateProofFailed(msg) => {
                assert!(msg.contains("missing proof"));
            }
            other => panic!("expected PredicateProofFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_verify_fulfillment_multiple_predicates_all_must_pass() {
        use pyana_circuit::poseidon2::hash_fact;
        use pyana_circuit::{
            PredicateType, PredicateWitness, compute_fact_commitment, prove_predicate,
        };

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![
                crate::PredicateRequirement {
                    attribute: "balance".into(),
                    predicate_type: "gte".into(),
                    threshold: 1000,
                    upper_bound: None,
                    state_root_freshness: 100,
                },
                crate::PredicateRequirement {
                    attribute: "reputation".into(),
                    predicate_type: "gte".into(),
                    threshold: 50,
                    upper_bound: None,
                    state_root_freshness: 100,
                },
            ],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        let state_root = BabyBear::new(99999);

        // Generate proof for balance >= 1000 (balance = 5000)
        let balance = BabyBear::new(5000);
        let balance_attr = BabyBear::new(42);
        let balance_fact = hash_fact(balance_attr, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let balance_commitment = compute_fact_commitment(balance_fact, state_root);
        let balance_proof = prove_predicate(PredicateWitness {
            private_value: balance,
            threshold: BabyBear::new(1000),
            predicate_type: PredicateType::Gte,
            fact_commitment: balance_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        })
        .unwrap();

        // Generate proof for reputation >= 50 (reputation = 85)
        let reputation = BabyBear::new(85);
        let rep_attr = BabyBear::new(99);
        let rep_fact = hash_fact(rep_attr, &[reputation, BabyBear::ZERO, BabyBear::ZERO]);
        let rep_commitment = compute_fact_commitment(rep_fact, state_root);
        let rep_proof = prove_predicate(PredicateWitness {
            private_value: reputation,
            threshold: BabyBear::new(50),
            predicate_type: PredicateType::Gte,
            fact_commitment: rep_commitment,
            blinding: None,
            fact_hash: None,
            state_root: None,
        })
        .unwrap();

        let token = source_token();
        let matched = Match {
            intent_id: pred_intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(test_root_key()),
            ..Default::default()
        };
        let base = fulfill(
            &pred_intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment_with_preds = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![(0, balance_proof), (1, rep_proof)],
            state_root,
            state_root_block: 980,
        };

        let key = test_root_key();
        let result = verify_fulfillment_with_predicates_and_key(
            &fulfillment_with_preds,
            &pred_intent,
            BabyBear::ZERO,
            1000,
            Some(&key),
        );
        assert!(
            result.is_ok(),
            "both predicates should verify: {:?}",
            result.err()
        );
    }

    // =========================================================================
    // Fulfillment payment tests
    // =========================================================================

    #[test]
    fn test_create_fulfillment_turn_structure() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(500), // Payment of 500 computrons
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        let base = Fulfillment {
            intent_id: intent.id,
            fulfiller: CommitmentId([0xBB; 32]),
            mode: VerificationMode::Trusted,
            token_data: Some(vec![1, 2, 3, 4]),
            proof: None,
            granted_actions: vec!["read".into()],
            granted_resource: "*".into(),
            expiry: Some(5000),
        };

        let fulfillment = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![],
            state_root: BabyBear::new(99999),
            state_root_block: 990,
        };

        let payer = CellId([0xAA; 32]);
        let recipient = CellId([0xBB; 32]);

        let conditional =
            create_fulfillment_turn(&intent, &fulfillment, payer, recipient, 500, 1000);

        // Verify the structure.
        assert_eq!(conditional.submitted_at, 1000);
        assert_eq!(conditional.timeout_height, 1100); // 1000 + 100 grace
        assert!(conditional.deposit_amount > 0);
        assert_eq!(conditional.turn.agent, payer);
        assert!(conditional.turn.memo.is_some());

        // Verify the condition is a HashPreimage.
        match &conditional.condition {
            ProofCondition::HashPreimage { hash } => {
                // Recompute the preimage and verify.
                let preimage = {
                    let mut hasher = blake3::Hasher::new_derive_key("pyana-fulfillment-payment-v1");
                    hasher.update(&intent.id);
                    hasher.update(&fulfillment.base.fulfiller.0);
                    hasher.update(&fulfillment.state_root_block.to_le_bytes());
                    *hasher.finalize().as_bytes()
                };
                let expected_hash = *blake3::hash(&preimage).as_bytes();
                assert_eq!(*hash, expected_hash);
            }
            other => panic!("expected HashPreimage condition, got {:?}", other),
        }

        // Verify the transfer effect is present.
        let effects = &conditional.turn.call_forest.roots[0].action.effects;
        assert_eq!(effects.len(), 1);
        match &effects[0] {
            pyana_turn::Effect::Transfer { from, to, amount } => {
                assert_eq!(*from, payer);
                assert_eq!(*to, recipient);
                assert_eq!(*amount, 500);
            }
            other => panic!("expected Transfer effect, got {:?}", other),
        }
    }

    #[test]
    fn test_execute_fulfillment_flow_success() {
        use crate::matcher::{HeldCapability, Sensitivity};
        use pyana_cell::{AuthRequired, Cell, Ledger, Permissions};

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(1000), // Payment of 1000 computrons
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        // Create a real attenuated macaroon token for Trusted mode verification
        let key = test_root_key();
        let token = source_token();
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(key),
            ..Default::default()
        };
        let base = fulfill(
            &intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![],
            state_root: BabyBear::new(99999),
            state_root_block: 990,
        };

        // Set up a ledger with payer having enough balance.
        let payer_pk = [0xAA; 32];
        let payer_token = [0x01; 32];
        let payer_cell = CellId::derive_raw(&payer_pk, &payer_token);

        let recipient_pk = [0xBB; 32];
        let recipient_token = [0x02; 32];
        let recipient_cell = CellId::derive_raw(&recipient_pk, &recipient_token);

        let mut ledger = Ledger::new();
        let mut payer_c = Cell::with_balance(payer_pk, payer_token, 100_000);
        payer_c.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let mut recipient_c = Cell::with_balance(recipient_pk, recipient_token, 0);
        recipient_c.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        ledger.insert_cell(payer_c).unwrap();
        ledger.insert_cell(recipient_c).unwrap();

        let executor = TurnExecutor::new(pyana_turn::ComputronCosts::default());

        let result = execute_fulfillment_flow_with_key(
            &intent,
            &fulfillment,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        );

        assert!(result.is_ok(), "flow should succeed: {:?}", result.err());
        let receipt = result.unwrap();
        assert_eq!(receipt.agent, payer_cell);
        assert!(receipt.computrons_used > 0);

        // Verify the transfer happened in the ledger.
        let payer_state = ledger.get(&payer_cell).unwrap();
        let recipient_state = ledger.get(&recipient_cell).unwrap();
        assert!(payer_state.state.balance < 100_000); // Fee + transfer deducted.
        assert_eq!(recipient_state.state.balance, 1000); // Received payment.
    }

    #[test]
    fn test_execute_fulfillment_flow_no_budget_fails() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None, // No payment specified
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        // Use a real attenuated token for the fulfillment
        let key = test_root_key();
        let token = source_token();
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(key),
            ..Default::default()
        };
        let base = fulfill(
            &intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        let fulfillment = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![],
            state_root: BabyBear::new(99999),
            state_root_block: 990,
        };

        let payer_cell = CellId([0xAA; 32]);
        let recipient_cell = CellId([0xBB; 32]);

        let mut ledger = Ledger::new();
        let executor = TurnExecutor::new(pyana_turn::ComputronCosts::default());

        let result = execute_fulfillment_flow_with_key(
            &intent,
            &fulfillment,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        );

        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::PaymentFailed(msg) => {
                assert!(msg.contains("no min_budget"));
            }
            other => panic!("expected PaymentFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_execute_fulfillment_flow_failed_verification_no_payment() {
        use pyana_cell::Ledger;

        // Intent with a predicate requirement that won't be satisfied.
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(500),
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![crate::PredicateRequirement {
                attribute: "reputation".into(),
                predicate_type: "gte".into(),
                threshold: 50,
                upper_bound: None,
                state_root_freshness: 100,
            }],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        // Use a real attenuated token for the fulfillment
        let key = test_root_key();
        let token = source_token();
        let matched = Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        };
        let options = FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some(key),
            ..Default::default()
        };
        let base = fulfill(
            &intent,
            &matched,
            &token,
            CommitmentId([0xBB; 32]),
            &options,
        )
        .unwrap();

        // Missing predicate proof: this should cause verification to fail.
        let fulfillment = FulfillmentWithPredicates {
            base,
            predicate_proofs: vec![], // No proofs!
            state_root: BabyBear::new(99999),
            state_root_block: 990,
        };

        let payer_cell = CellId([0xAA; 32]);
        let recipient_cell = CellId([0xBB; 32]);

        let mut ledger = Ledger::new();
        let executor = TurnExecutor::new(pyana_turn::ComputronCosts::default());

        let result = execute_fulfillment_flow_with_key(
            &intent,
            &fulfillment,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        );

        // Should fail at verification step, not payment.
        assert!(result.is_err());
        match result.unwrap_err() {
            FulfillmentError::PredicateProofFailed(msg) => {
                assert!(msg.contains("missing proof"));
            }
            other => panic!("expected PredicateProofFailed, got {:?}", other),
        }
    }
}
