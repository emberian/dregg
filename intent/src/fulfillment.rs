//! Fulfillment protocol: creating attenuated tokens to satisfy matched intents.
//!
//! After matching locally, the cclerk can fulfill an intent by creating an
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
use dregg_cell::CellId;
use dregg_cell::Ledger;
use dregg_circuit::BabyBear;
use dregg_circuit::PredicateType;
use dregg_circuit::compute_action_binding_narrow;
use dregg_circuit::multi_step_witness::MultiStepWitness;
// The retired hand-STARK proof types (`PredicateProof`, `verify_predicate`,
// `prove_authorization_stark`, `verify_authorization_dsl`, the `stark` codec) are gone.
// Predicate fulfillment now rides the bridge's descriptor-backed `BridgePredicateProof`
// (only `Gte` has an emitted IR-v2 descriptor; every other operator fails closed at verify).
use dregg_bridge::present::{
    BridgePredicateProof, Predicate as BridgePredicate, verify_predicate_proof_third_party,
};
use dregg_token::{Attenuation, AuthToken, MacaroonToken};
use dregg_turn::conditional::{ConditionalTurn, ProofCondition, compute_conditional_deposit};
use dregg_turn::{
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
    /// The VERIFIED executor refused the payment leg (gate failure, liveness, FFI
    /// divergence, …). Fail-closed: a refusal here is final — there is NO fallback
    /// to the legacy Rust executor. **A genuine verdict on the payment.**
    VerifiedRefusal(String),
    /// ⚑ **The payment was NEVER JUDGED.** No verdict was reached: either this BINARY never
    /// installed the verified gate (a WIRING BUG, fixed in code by calling
    /// `dregg_exec_lean::register_distributed_gates()` at startup) or its Lean export could not run
    /// (fixed in the ENVIRONMENT). The ledger is untouched either way — but nothing here says the
    /// payment was bad.
    ///
    /// ⚠ **This used to arrive as [`Self::VerifiedRefusal`],** whose `Display` reads *"verified
    /// executor refused the payment"* — naming a refusal that never happened, on a payment nobody
    /// looked at. `execute_fulfillment_flow_verified*` is a PUBLIC library entry point, so every
    /// caller inherited the wrong sentence and had no typed way to tell the two apart.
    PaymentNeverJudged {
        /// Which absence — the two have opposite fixes.
        cause: crate::verified_settle::Unjudged,
        /// The operator-facing sentence naming the build/environment, never the payment.
        diagnosis: String,
    },
}

impl FulfillmentError {
    /// Classify a verified-settle failure as a VERDICT on the payment or an ABSENCE of the
    /// executor, at the point the error is produced.
    fn from_settle(e: crate::verified_settle::VerifiedSettleError) -> Self {
        use crate::verified_settle::{unjudged, unjudged_diagnosis};
        match unjudged_diagnosis(
            &e,
            "this binary (a host that fulfills must call \
             `dregg_exec_lean::register_distributed_gates()` at startup; `dregg-intent` is FFI-free \
             and cannot install it itself)",
        ) {
            Some(diagnosis) => Self::PaymentNeverJudged {
                cause: unjudged(&e).expect("a diagnosis implies a cause"),
                diagnosis,
            },
            None => Self::VerifiedRefusal(e.to_string()),
        }
    }
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
            Self::VerifiedRefusal(e) => write!(f, "verified executor refused the payment: {}", e),
            Self::PaymentNeverJudged { diagnosis, .. } => write!(f, "{diagnosis}"),
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

/// Build a genuinely-verifying Trusted-mode [`FulfillmentWithPredicates`] for the
/// **self-fulfillment** path: a node that accepts a submitted, payable intent and wants
/// to COMMIT it through the verified ledger immediately (the `POST /intents` inline
/// drain).
///
/// Unlike a stub `token_data`, this mints a REAL HMAC-chained attenuated macaroon under
/// `root_key` (via the same [`fulfill`] machinery a peer fulfiller uses), so the
/// downstream [`verify_fulfillment_with_predicates_and_key`] HMAC check genuinely passes —
/// the commit is verified, not laundered. The grant is attenuated to exactly the intent's
/// actions/resource (minimum disclosure); the `root_key` is the operator's intent root key
/// (the same key the recipient would verify the token against), so a self-fulfillment is a
/// real, verifiable capability grant + a real verified payment leg.
///
/// The returned value carries `predicate_proofs: vec![]`; the intent must therefore have no
/// `predicate_requirements` (the inline self-fulfill path is for the plain payable-intent
/// case — a node holding the predicate witnesses would use the full `fulfill` path). The
/// caller still drives the value leg through [`execute_fulfillment_flow_verified`].
pub fn build_self_fulfillment_trusted(
    intent: &Intent,
    fulfiller: CommitmentId,
    root_key: [u8; 32],
    state_root: BabyBear,
    state_root_block: u64,
) -> Result<FulfillmentWithPredicates, FulfillmentError> {
    // A synthetic source capability that covers the intent: wildcard actions + resource,
    // attenuated DOWN to exactly the intent's needs inside `fulfill`. The token id is bound
    // to the intent id so the minted macaroon is intent-specific.
    // A stable per-intent token id string (lowercase hex of the intent id), without
    // pulling a hex dependency.
    let token_id = intent
        .id
        .iter()
        .fold(String::with_capacity(64), |mut s, b| {
            use std::fmt::Write as _;
            let _ = write!(s, "{b:02x}");
            s
        });
    let source = crate::matcher::HeldCapability {
        token_id,
        actions: vec!["*".to_string()],
        resource: "*".to_string(),
        app_id: None,
        service: None,
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: Some(intent.expiry),
        budget: intent.matcher.min_budget,
        sensitivity: crate::matcher::Sensitivity::Public,
    };

    let matched = Match {
        intent_id: intent.id,
        satisfier: fulfiller,
        proof: None,
        mode: VerificationMode::Trusted,
    };

    let options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some(root_key),
        ..Default::default()
    };

    // Mint the real attenuated macaroon (HMAC-chained) bound to the intent's grant.
    let mut base = fulfill(intent, &matched, &source, fulfiller, &options)?;
    // The fulfiller commitment is the recipient cell; bind it explicitly.
    base.fulfiller = fulfiller;

    Ok(FulfillmentWithPredicates {
        base,
        predicate_proofs: vec![],
        state_root,
        state_root_block,
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
                dregg_token::dregg_macaroon::Macaroon::deserialize(token_data).map_err(|e| {
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
            // FAIL-CLOSED. The Private/Selective fulfillment proof was the hand-STARK
            // multi-step authorization proof (`prove_authorization_stark` +
            // `verify_authorization_dsl`, wire-encoded through the `stark` codec). That
            // engine was retired and NO descriptor replacement for the multi-step
            // authorization statement exists yet, so there is no way to cryptographically
            // verify such a proof. Rather than accept an unverifiable claim (fail-open),
            // reject: a Private/Selective fulfillment cannot be verified in this build.
            //
            // The `request_hash` replay binding this branch used to enforce
            // (`compute_intent_request_hash`) rode inside that same retired proof; it is
            // subsumed by this outright rejection.
            let _ = fulfillment.proof.as_ref().ok_or_else(|| {
                FulfillmentError::MissingData("private/selective mode requires proof".into())
            })?;
            return Err(FulfillmentError::ProofVerificationFailed(
                "private/selective fulfillment verification is unavailable: the multi-step \
                 authorization hand-STARK engine was retired and no descriptor replacement \
                 exists yet (fail-closed)"
                    .into(),
            ));
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
    if (fulfillment.mode == VerificationMode::Private
        || fulfillment.mode == VerificationMode::Selective)
        && !intent_actions.is_empty()
    {
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

    // 3. Check granted_resource matches the intent's resource_pattern
    if let Some(pattern) = &intent.matcher.resource_pattern
        && !resource_matches(&fulfillment.granted_resource, pattern)
    {
        return Err(FulfillmentError::ResourceMismatch(format!(
            "granted '{}' does not cover required '{}'",
            fulfillment.granted_resource, pattern
        )));
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
///
/// # Soundness: state-root binding (and the facts_root residual)
///
/// Each proof is now bound to the verifier's TRUSTED state root.
/// `verify_predicate_requirement` requires the proof to carry a `BridgeFactAttestation`
/// and routes through `verify_predicate_proof_third_party(proof, facts_root,
/// trusted_state_root)`, which pins the membership STARK to `trusted_state_root`. A proof
/// bound to a foreign/fabricated state root — or carrying no attestation at all — is REFUSED
/// (the cross-state forgery driven by
/// `test_verify_fulfillment_rejects_cross_state_predicate_forgery`).
///
/// RESIDUAL: the verify path threads the trusted `state_root` but not an independently-trusted
/// `facts_root`, so the `facts_root` fed to the attestation is the prover's own and that half is
/// vacuous. The STATE_ROOT binding is real; the FACTS_ROOT binding is not — closing it needs a
/// `facts_root` the verifier trusts (settled state / presentation public inputs) threaded in.
#[derive(Clone, Debug)]
pub struct FulfillmentWithPredicates {
    /// The base fulfillment (capability satisfaction).
    pub base: Fulfillment,
    /// Predicate proofs, one per requirement.
    /// Each entry is `(requirement_index, proof)` where requirement_index
    /// refers to the index in `intent.matcher.predicate_requirements`.
    ///
    /// The proof is the bridge's descriptor-backed [`BridgePredicateProof`]: only the
    /// `Gte` (`≥ threshold`) predicate has an emitted IR-v2 descriptor
    /// (`dregg-predicate-arith-ge::threshold-v1`); every other operator fails closed at
    /// verify (the retired hand-AIR predicate gadgets are gone).
    pub predicate_proofs: Vec<(usize, BridgePredicateProof)>,
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

        // Verify the proof matches the expected predicate type and threshold, and is bound to
        // the state root the VERIFIER trusts (the `state_root` parameter) — not the proof's own.
        verify_predicate_requirement(proof, req, state_root)?;
    }

    Ok(())
}

/// Verify a single predicate proof against its requirement, bound to the verifier's
/// TRUSTED `state_root`.
///
/// Migrated onto the bridge's descriptor-backed [`BridgePredicateProof`]: the proof's
/// declared predicate must match the requirement (operator + threshold), and the proof
/// must verify via [`verify_predicate_proof_third_party`] against a `BridgeFactAttestation`
/// pinned to `trusted_state_root`. Only `Gte` has an emitted IR-v2 descriptor; every other
/// operator fails closed inside the descriptor verify (never accepted against the wrong
/// comparison semantics), and a proof carrying NO attestation fails closed as well — there
/// is nothing to bind its commitment to the trusted state.
fn verify_predicate_requirement(
    proof: &BridgePredicateProof,
    requirement: &PredicateRequirement,
    trusted_state_root: BabyBear,
) -> Result<(), FulfillmentError> {
    // Ensure the requirement names a predicate type we understand (parity with the
    // legacy path's typed rejection of unknown types).
    let _expected_type = parse_predicate_type(&requirement.predicate_type).ok_or_else(|| {
        FulfillmentError::PredicateProofFailed(format!(
            "unknown predicate type: '{}'",
            requirement.predicate_type
        ))
    })?;

    // Map the requirement to the bridge predicate the proof must carry.
    let threshold = requirement.threshold as u32;
    let upper = requirement.upper_bound.unwrap_or(requirement.threshold) as u32;
    let expected_predicate = match requirement.predicate_type.as_str() {
        "gte" => BridgePredicate::Gte(threshold),
        "lte" => BridgePredicate::Lte(threshold),
        "gt" => BridgePredicate::Gt(threshold),
        "lt" => BridgePredicate::Lt(threshold),
        "neq" => BridgePredicate::Neq(threshold),
        "in_range" | "in_range_low" | "in_range_high" => BridgePredicate::InRange(threshold, upper),
        other => {
            return Err(FulfillmentError::PredicateProofFailed(format!(
                "unsupported predicate type '{}' for bridge predicate proof",
                other
            )));
        }
    };

    if proof.predicate != expected_predicate {
        return Err(FulfillmentError::PredicateProofFailed(format!(
            "proof predicate {:?} does not match requirement {:?}",
            proof.predicate, expected_predicate
        )));
    }

    // Cryptographically verify the predicate STARK, BOUND TO THE TRUSTED STATE ROOT.
    //
    // The former gate here was `verify_predicate_proof(proof, proof.fact_commitment)` — the
    // proof checked against its OWN commitment (`x == x`), which never touched the trusted
    // `state_root` threaded into `verify_fulfillment_with_predicates_and_key`. That accepted a
    // proof bound (via its blinded fact commitment) to a FOREIGN/fabricated state root — the
    // cross-state forgery driven by `test_verify_fulfillment_rejects_cross_state_predicate_forgery`.
    //
    // The sound source for the expected commitment is a `BridgeFactAttestation`: a STARK
    // (`dregg-attested-fact-membership::v1`) proving `fact_commitment` is the blinded image of a
    // `fact_hash` that is a member of `facts_root`, at a PINNED `state_root`.
    // `verify_predicate_proof_third_party` refuses a mismatch on BOTH roots by parameter and
    // re-checks them inside the membership STARK, so a proof whose attestation names a state root
    // other than the one the verifier trusts is REFUSED — the commitment fed to the predicate
    // descriptor exists only because it checked out against `trusted_state_root`.
    //
    // A proof with NO attestation fails closed: nothing binds its commitment to the trusted
    // state, so there is no `x == x` escape left.
    //
    // RESIDUAL (facts_root): the intent verify path threads the trusted `state_root` but NOT an
    // independently-trusted `facts_root`, so the `facts_root` argument is taken from the proof's
    // own attestation and that half of `verify_fact_attestation` is vacuous. The STATE_ROOT
    // binding is real (it refuses this falsifier's cross-state forgery); the FACTS_ROOT binding
    // is not — a prover may still attest membership under a tree OF ITS OWN choosing at the
    // trusted state root. Closing that residual requires threading a `facts_root` the verifier
    // independently trusts (from settled state / the presentation's public inputs) into
    // `verify_fulfillment_with_predicates_and_key` and passing it here instead of
    // `attestation.facts_root`.
    let Some(attestation) = proof.attestation.as_ref() else {
        return Err(FulfillmentError::PredicateProofFailed(
            "predicate proof carries no fact attestation; cannot bind its commitment to the \
             trusted state root (fail-closed)"
                .to_string(),
        ));
    };
    let facts_root = attestation.facts_root;
    if !verify_predicate_proof_third_party(proof, facts_root, trusted_state_root) {
        return Err(FulfillmentError::PredicateProofFailed(
            "predicate proof did not verify against the trusted state root (no descriptor for \
             this operator, the membership attestation did not check out under the trusted \
             state root, the attested commitment did not join the predicate proof, or the \
             predicate STARK did not verify)"
                .to_string(),
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

    // Mint a macaroon from the root key (the cclerk holds the key for its own tokens)
    let mac = MacaroonToken::mint(root_key, source_token.token_id.as_bytes(), "dregg.intent");

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
    // FAIL-CLOSED. The multi-step authorization proof was produced by the retired
    // hand-STARK engine (`prove_authorization_stark` + the `stark` codec). No descriptor
    // replacement for the multi-step authorization statement exists yet, so a
    // Private/Selective fulfillment proof cannot be produced. Report the failure rather
    // than emit an unverifiable placeholder blob (which the verifier now rejects anyway).
    let _ = options.stark_witness.as_ref().ok_or_else(|| {
        FulfillmentError::ProofGenerationFailed(
            "stark_witness required for Private/Selective mode".into(),
        )
    })?;

    Err(FulfillmentError::ProofGenerationFailed(
        "private/selective fulfillment proof generation is unavailable: the multi-step \
         authorization hand-STARK engine was retired and no descriptor replacement exists \
         yet (fail-closed)"
            .into(),
    ))
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

/// Validity horizon (wall-clock seconds) stamped onto turns this module constructs.
///
/// `Turn::valid_until` (`turn/src/turn.rs`) is compared against the executor's
/// `current_timestamp` — a wall-clock Unix timestamp, entirely separate from
/// `block_height` (`turn/src/executor/mod.rs`). Do NOT stamp `current_height` (this
/// module's block-height parameter) in here: as a "timestamp" it would already be far
/// in the past and expire the turn on arrival. Leaving `valid_until` as `None` is worse
/// than either: the executor's expiration check is `if let Some(valid_until) =
/// turn.valid_until { .. }` (`turn/src/executor/execute.rs:426`) — entirely SKIPPED on
/// `None`, so a turn built that way never expires, no matter how stale. Mirrors
/// `default_valid_until` in `node/src/api.rs` / `sdk/src/runtime.rs` (same rationale,
/// same fix, same 1-hour horizon); this crate has no dependency on either, hence its
/// own copy.
const FULFILLMENT_TURN_VALIDITY_HORIZON_SECS: i64 = 3600;

fn default_valid_until() -> Option<i64> {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    Some(now + FULFILLMENT_TURN_VALIDITY_HORIZON_SECS)
}

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
        let mut hasher = blake3::Hasher::new_derive_key("dregg-fulfillment-payment-v1");
        hasher.update(&intent.id);
        hasher.update(&fulfillment.base.fulfiller.0);
        hasher.update(&fulfillment.state_root_block.to_le_bytes());
        *hasher.finalize().as_bytes()
    };
    let hash = *blake3::hash(&preimage).as_bytes();

    // Build the payment transfer action.
    //
    // The action's authorization is `Breadstuff(hash)` — a capability-
    // token authorization whose token id is the same hash carried by
    // the `ProofCondition::HashPreimage` gate. Concretely: "whoever
    // presents the preimage that resolves this conditional has the
    // capability to dispatch this payment." The `ConditionalTurn`
    // resolver consults the preimage, the executor consults the
    // token id; both reduce to the same secret.
    //
    // Previously this used `Authorization::Unchecked`, which would
    // fail `SealedTurn::from_turn`'s debug_assert if the turn ever
    // flowed through the lowering tower. Using `Breadstuff(hash)`
    // keeps the action seal-compatible without altering the
    // conditional gating semantics.
    let action = Action {
        target: payer_cell,
        method: dregg_turn::action::symbol("fulfillment_payment"),
        args: Vec::new(),
        authorization: Authorization::Breadstuff(hash),
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: payer_cell,
            to: recipient_cell,
            amount: payment_amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
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
        // `valid_until: None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it with the module's shared
        // wall-clock horizon instead of `current_height` (a block height, not a timestamp).
        valid_until: default_valid_until(),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
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
    let _preimage = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-fulfillment-payment-v1");
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

// ---------------------------------------------------------------------------
// The VERIFIED fulfillment payment flow — the value move settles through the
// verified executor edge (`verified_settle`), NOT `dregg_turn::TurnExecutor`.
// ---------------------------------------------------------------------------

/// The computron column as a verified-ledger asset id.
///
/// The fulfillment payment moves COMPUTRONS — the cell record's scalar `balance` field. The
/// verified per-asset executor ([`crate::verified_settle`]) indexes balances by a 32-byte asset
/// column; the all-zero id names the computron column. This matches the Lean projection
/// (`Dregg2.Intent.RingFFI.projAsset`): the scalar `balance` IS the projected asset column the
/// verified export `dregg_record_kernel_step` runs over.
pub const COMPUTRON_ASSET: [u8; 32] = [0u8; 32];

/// Execute the fulfillment-to-payment flow with the VALUE MOVE settled by the VERIFIED executor.
///
/// Same contract as [`execute_fulfillment_flow`] (verify the fulfillment, then pay
/// `intent.matcher.min_budget` from `payer_cell` to `recipient_cell`), with ONE difference that
/// is the point: the payment leg does NOT run through the legacy `dregg_turn::TurnExecutor`. It
/// is folded through [`crate::verified_settle::settle_ring_verified`] — the verified per-asset
/// transition `recKExecAsset` (proved in `metatheory/Dregg2/Intent/Ring.lean`), which under the
/// default native build (Lean unconditional) is cross-checked leg-by-leg against the REAL Lean FFI export
/// `@[export] dregg_record_kernel_step` (the PROVED `Exec.recKExec`;
/// `RingFFI.ffi_export_realises_settleRing_leg`) and FAILS CLOSED on any divergence.
///
/// Fail-closed means fail-closed: a payment the verified executor refuses (underfunded payer,
/// non-distinct cells, a missing/dead cell, an FFI divergence) returns
/// [`FulfillmentError::VerifiedRefusal`] and the ledger is untouched. There is NO fallback to the
/// legacy executor.
///
/// Differences from the legacy flow a caller can observe (all REFUSALS, never silent changes):
/// * `payer_cell == recipient_cell` is refused (the verified distinctness gate).
/// * Both cells must already exist in the ledger (the verified liveness gate); the flow never
///   implicitly creates the recipient.
/// * No conditional-turn fee/deposit is charged and no fee distribution runs — the verified edge
///   moves EXACTLY the payment leg, conserving the computron column (`settleRing_conserves`).
///
/// The returned receipt binds the SAME canonical payment turn the legacy flow built
/// ([`create_fulfillment_turn`] — so `turn_hash` is unchanged across the rewire) plus the
/// executor's OWN consensus state anchor around the verified write-back.
///
/// # Why this takes an `executor` when it never calls `executor.execute`
///
/// `TurnReceipt::{pre,post}_state_hash` MUST be
/// [`dregg_turn::state_commit::consensus_state_commitment`] — the AIR-bound chip 8-felt anchor
/// (`state_commit.rs:146`: "`pre_state_hash` and `post_state_hash` MUST both come from this
/// function, or every consumer that compares them across receipts compares incomparable
/// values"). That anchor binds the executor's LIVE accumulator roots (nullifier / commitment /
/// revocation), which only a `TurnExecutor` holds — so the verified edge borrows one purely to
/// stamp the same value `TurnExecutor::execute` and
/// [`dregg_turn::lean_apply::produce_via_lean`] stamp. The value leg still settles through
/// [`crate::verified_settle`]; the executor is NOT consulted for the payment decision.
#[allow(clippy::too_many_arguments)]
pub fn execute_fulfillment_flow_verified(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    payer_cell: CellId,
    recipient_cell: CellId,
    current_height: u64,
    current_block: u64,
) -> Result<TurnReceipt, FulfillmentError> {
    execute_fulfillment_flow_verified_with_key(
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

/// [`execute_fulfillment_flow_verified`] with an explicit root key for Trusted-mode HMAC
/// verification (the secure variant, mirroring [`execute_fulfillment_flow_with_key`]).
#[allow(clippy::too_many_arguments)]
pub fn execute_fulfillment_flow_verified_with_key(
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
    use crate::verified_settle::{VerifiedLedger, VerifiedLeg, settle_ring_verified};

    // Step 1: Verify the fulfillment (identical to the legacy flow).
    let state_root = fulfillment.state_root;
    verify_fulfillment_with_predicates_and_key(
        fulfillment,
        intent,
        state_root,
        current_block,
        root_key,
    )?;

    // Step 2: Payment amount from the intent's min_budget.
    let payment_amount = intent.matcher.min_budget.unwrap_or(0);
    if payment_amount == 0 {
        return Err(FulfillmentError::PaymentFailed(
            "intent has no min_budget specified (no payment required)".into(),
        ));
    }

    // Step 3: Build the verified leg. Distinctness is checked on the REAL 32-byte cell ids
    // BEFORE projection — the projection below assigns synthetic indices, so two distinct
    // cells can never alias, and a true self-payment can never slip past the gate.
    if payer_cell == recipient_cell {
        return Err(FulfillmentError::VerifiedRefusal(
            "payer and recipient are the same cell (distinctness gate)".into(),
        ));
    }

    // Project the real ledger's computron column for the two touched cells onto the verified
    // per-asset ledger. Both cells must be LIVE (present) — the verified liveness gate; a
    // missing cell is a refusal, never an implicit create.
    let payer_balance = ledger
        .get(&payer_cell)
        .ok_or_else(|| {
            FulfillmentError::VerifiedRefusal(
                "payer cell not found in ledger (liveness gate)".into(),
            )
        })?
        .state
        .balance();
    let recipient_balance = ledger
        .get(&recipient_cell)
        .ok_or_else(|| {
            FulfillmentError::VerifiedRefusal(
                "recipient cell not found in ledger (liveness gate)".into(),
            )
        })?
        .state
        .balance();

    const PAYER: u8 = 0;
    const RECIPIENT: u8 = 1;
    let mut k0 = VerifiedLedger::new();
    k0.add_account(PAYER);
    k0.add_account(RECIPIENT);
    k0.set(PAYER, &COMPUTRON_ASSET, payer_balance as i128);
    k0.set(RECIPIENT, &COMPUTRON_ASSET, recipient_balance as i128);

    let leg = VerifiedLeg {
        from: PAYER,
        to: RECIPIENT,
        asset: COMPUTRON_ASSET,
        amount: payment_amount as i128,
    };

    // Step 4: Settle through the verified executor — fail-closed, NO fallback. Under the
    // default native build (Lean unconditional), the leg is additionally settled by the REAL
    // Lean FFI export `dregg_record_kernel_step` over this exact projection and cross-checked;
    // any divergence refuses the payment.
    let k1 = settle_ring_verified(&k0, &[leg]).map_err(FulfillmentError::from_settle)?;

    // Step 5: Write the VERIFIED post-balances back to the real ledger. Cell balances are
    // signed (i64) under the well model; the verified gate guarantees these ordinary
    // (non-well) cells stay non-negative, so the only failure here is the ℤ→i64 range
    // conversion (the Lean side is ℤ — overflow lives only at this conversion).
    let payer_post = i64::try_from(k1.get(PAYER, &COMPUTRON_ASSET)).map_err(|_| {
        FulfillmentError::VerifiedRefusal("verified payer post-balance out of i64 range".into())
    })?;
    let recipient_post = i64::try_from(k1.get(RECIPIENT, &COMPUTRON_ASSET)).map_err(|_| {
        FulfillmentError::VerifiedRefusal("verified recipient post-balance overflows i64".into())
    })?;

    // THE CONSENSUS ANCHOR, not `Ledger::root()`. `state_commit.rs:146` requires both stamps to
    // come from `consensus_state_commitment`; this edge stamped the trusted-Rust BLAKE3 ledger
    // root from 977e73b19 (2026-07-20) until 2026-07-29, so every receipt this flow produced
    // carried a value incomparable with every other receipt on the chain. The agent of this
    // receipt is `payer_cell` (see the `agent:` field below), so that is the cell the anchor
    // commits — exactly as `produce_via_lean` anchors on `turn.agent`.
    let pre_state_hash = executor.consensus_state_commitment(ledger, &payer_cell);
    ledger
        .update_with(&payer_cell, |c| c.state.set_balance(payer_post))
        .map_err(|e| {
            FulfillmentError::PaymentFailed(format!("ledger write-back (payer): {e:?}"))
        })?;
    ledger
        .update_with(&recipient_cell, |c| c.state.set_balance(recipient_post))
        .map_err(|e| {
            FulfillmentError::PaymentFailed(format!("ledger write-back (recipient): {e:?}"))
        })?;
    let post_state_hash = executor.consensus_state_commitment(ledger, &payer_cell);

    // Step 6: The audit-trail receipt over the SAME canonical payment turn the legacy flow
    // built, so the turn hash a fulfillment receipt carries is unchanged across the rewire.
    let conditional = create_fulfillment_turn(
        intent,
        fulfillment,
        payer_cell,
        recipient_cell,
        payment_amount,
        current_height,
    );
    let turn_hash = conditional.turn.hash();
    let forest_hash = conditional.turn.call_forest.compute_hash();
    let effects_hash = {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-verified-fulfillment-effects-v1");
        hasher.update(payer_cell.as_bytes());
        hasher.update(recipient_cell.as_bytes());
        hasher.update(&payment_amount.to_le_bytes());
        *hasher.finalize().as_bytes()
    };

    Ok(TurnReceipt {
        turn_hash,
        forest_hash,
        pre_state_hash,
        post_state_hash,
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0),
        effects_hash,
        computrons_used: 0,
        action_count: 1,
        agent: payer_cell,
        ..Default::default()
    })
}

/// Execute the fulfillment flow with anti-frontrunning enforcement.
///
/// This variant requires a `FulfillmentRegistry` and a `fulfiller_secret`.
/// Before proceeding with verification and payment, it checks that the fulfiller
/// registered a commitment for this intent BEFORE the reveal window elapsed.
///
/// This prevents a malicious observer from racing to submit their own fulfillment
/// after seeing a match in the gossip layer.
///
/// # Arguments
///
/// * `registry` - The commit-reveal fulfillment registry.
/// * `fulfiller_secret` - The secret used in the original commitment.
/// * `now` - Current timestamp (for window validation).
/// * All other arguments are the same as `execute_fulfillment_flow_with_key`.
///
/// # Errors
///
/// Returns `FulfillmentError::MissingData` if no commitment was registered (front-running
/// attempt), or if the reveal window checks fail.
pub fn execute_fulfillment_flow_with_commitment(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    payer_cell: CellId,
    recipient_cell: CellId,
    current_height: u64,
    current_block: u64,
    root_key: Option<&[u8; 32]>,
    registry: &mut crate::commit_reveal_fulfillment::FulfillmentRegistry,
    fulfiller_secret: &[u8; 32],
    now: u64,
) -> Result<TurnReceipt, FulfillmentError> {
    // Anti-frontrunning gate: validate that the fulfiller has a registered commitment.
    registry
        .validate_reveal(&intent.id, fulfiller_secret, now)
        .map_err(|e| FulfillmentError::MissingData(format!("commit-reveal check failed: {}", e)))?;

    // Proceed with the standard execution flow.
    let receipt = execute_fulfillment_flow_with_key(
        intent,
        fulfillment,
        executor,
        ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_block,
        root_key,
    )?;

    // Mark the intent as fulfilled in the registry (prevents double-fulfillment).
    registry.mark_fulfilled(intent.id);

    Ok(receipt)
}

// ============================================================================
// Committed payment fulfillment flow
// ============================================================================

/// A committed note input for the fulfillment flow.
///
/// The fulfiller provides these from their cipherclerk's owned notes.
#[derive(Clone, Debug)]
pub struct CommittedFulfillmentInput {
    /// The nullifier for this note.
    pub nullifier: dregg_cell::Nullifier,
    /// The Merkle root at the time of proof generation.
    pub merkle_root: [u8; 32],
    /// The plaintext value (known to the spender only).
    pub value: u64,
    /// The blinding factor from the commitment opening.
    pub blinding: curve25519_dalek::scalar::Scalar,
    /// Asset type identifier.
    pub asset_type: u64,
    /// Serialized STARK spending proof.
    pub spending_proof: Vec<u8>,
}

/// A committed note output for the fulfillment flow.
#[derive(Clone, Debug)]
pub struct CommittedFulfillmentOutput {
    /// The value to commit.
    pub value: u64,
    /// Asset type identifier.
    pub asset_type: u64,
    /// Recipient's public key.
    pub recipient: [u8; 32],
}

/// Execute a committed (privacy-preserving) fulfillment-to-payment flow.
///
/// This is the committed counterpart of [`execute_fulfillment_flow_with_key`]:
/// instead of building a cleartext transfer turn, it builds a turn where note
/// values are hidden behind Pedersen commitments. The conservation proof ensures
/// no inflation without revealing amounts.
///
/// # Flow
///
/// 1. Verifies the fulfillment (same as the cleartext path).
/// 2. Builds a committed payment turn using the provided note inputs/outputs.
/// 3. Executes the turn through the executor (which validates via the committed
///    conservation path).
/// 4. Returns the receipt proving the committed payment occurred.
///
/// # Arguments
///
/// * `intent` - The intent being fulfilled.
/// * `fulfillment` - The fulfillment to verify and pay for.
/// * `executor` - The turn executor.
/// * `ledger` - The ledger to apply effects to.
/// * `payer_cell` - The payer's cell ID.
/// * `inputs` - Committed note inputs (notes the payer is spending).
/// * `outputs` - Committed note outputs (notes being created for the fulfiller).
/// * `nonce` - Replay-protection nonce.
/// * `current_block` - Current block for freshness checking.
/// * `root_key` - Optional root key for Trusted mode verification.
pub fn execute_committed_fulfillment_flow(
    intent: &Intent,
    fulfillment: &FulfillmentWithPredicates,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    payer_cell: CellId,
    inputs: &[CommittedFulfillmentInput],
    outputs: &[CommittedFulfillmentOutput],
    nonce: u64,
    current_block: u64,
    root_key: Option<&[u8; 32]>,
) -> Result<TurnReceipt, FulfillmentError> {
    use curve25519_dalek::scalar::Scalar;
    use dregg_cell::note::NoteCommitment;
    use dregg_cell_crypto::{
        BulletproofRangeProof, ValueCommitment, prove_conservation_with_range,
    };
    use dregg_turn::action::{CommitmentMode, DelegationMode, symbol};

    // Step 1: Verify the fulfillment (same verification as cleartext path).
    let state_root = fulfillment.state_root;
    verify_fulfillment_with_predicates_and_key(
        fulfillment,
        intent,
        state_root,
        current_block,
        root_key,
    )?;

    // Step 2: Build the committed payment turn.
    if inputs.is_empty() {
        return Err(FulfillmentError::PaymentFailed(
            "committed fulfillment requires at least one input note".into(),
        ));
    }

    // Generate fresh output blindings.
    let output_blindings: Vec<Scalar> = outputs
        .iter()
        .map(|_| {
            let mut bytes = [0u8; 64];
            getrandom::fill(&mut bytes).expect("getrandom failed");
            Scalar::from_bytes_mod_order_wide(&bytes)
        })
        .collect();

    // Compute value commitments.
    // Use the default generator (not asset-specific) because the BulletproofRangeProof
    // implementation uses fixed PedersenGens. Asset type is enforced by spending proofs.
    let input_commitments: Vec<ValueCommitment> = inputs
        .iter()
        .map(|inp| ValueCommitment::commit(inp.value, &inp.blinding))
        .collect();

    let output_commitments: Vec<ValueCommitment> = outputs
        .iter()
        .zip(output_blindings.iter())
        .map(|(out, blinding)| ValueCommitment::commit(out.value, blinding))
        .collect();

    // Build NoteSpend effects.
    let mut all_effects: Vec<Effect> = inputs
        .iter()
        .zip(input_commitments.iter())
        .map(|(inp, vc)| Effect::NoteSpend {
            nullifier: inp.nullifier,
            note_tree_root: inp.merkle_root,
            value: inp.value,
            asset_type: inp.asset_type,
            spending_proof: inp.spending_proof.clone(),
            value_commitment: Some(vc.to_bytes().0),
        })
        .collect();

    // Build NoteCreate effects.
    for (out, (vc, blinding)) in outputs
        .iter()
        .zip(output_commitments.iter().zip(output_blindings.iter()))
    {
        let mut creation_nonce = [0u8; 32];
        getrandom::fill(&mut creation_nonce).expect("getrandom failed");
        let mut note_randomness = [0u8; 32];
        getrandom::fill(&mut note_randomness).expect("getrandom failed");

        // Compute note commitment.
        let note_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-committed-note v1");
            hasher.update(&out.recipient);
            hasher.update(&vc.to_bytes().0);
            hasher.update(&out.asset_type.to_le_bytes());
            hasher.update(&creation_nonce);
            hasher.update(&note_randomness);
            *hasher.finalize().as_bytes()
        };

        let range_proof = BulletproofRangeProof::prove_range(out.value, blinding);

        let mut encrypted_note = Vec::with_capacity(64);
        encrypted_note.extend_from_slice(&out.recipient);
        encrypted_note.extend_from_slice(&creation_nonce);

        all_effects.push(Effect::NoteCreate {
            commitment: NoteCommitment(note_commitment),
            value: out.value,
            asset_type: out.asset_type,
            encrypted_note,
            value_commitment: Some(vc.to_bytes().0),
            range_proof: Some(postcard::to_allocvec(&range_proof).unwrap_or_default()),
        });
    }

    // Build the action.
    //
    // Authorization is bound to the conservation proof — this action
    // executes only inside a turn whose `conservation_proof` field
    // verifies. The action's auth records the binding intent under
    // `bound_resource`; the turn-level conservation proof (built
    // below) is the actual cryptographic gate the executor checks
    // atomically with the per-action seal.
    //
    // Previously this used `Authorization::Unchecked`, which the seal
    // layer rejects in debug builds (audit §17). The new value passes
    // `SealedTurn::from_turn`'s invariant and makes the auth chain
    // auditable: the executor sees a `Proof` authorization whose
    // `bound_action` and `bound_resource` name exactly the intent +
    // payer being settled.
    let action = Action {
        target: payer_cell,
        method: symbol("committed_fulfillment_payment"),
        args: Vec::new(),
        authorization: Authorization::Proof {
            // Placeholder proof bytes — real conservation proof flows
            // through the turn-level `conservation_proof` field which
            // the executor checks atomically with the per-action seal.
            proof_bytes: Vec::new(),
            bound_action: "committed_fulfillment_payment".to_string(),
            bound_resource: format!(
                "intent:{:02x}{:02x}{:02x}{:02x}",
                intent.id[0], intent.id[1], intent.id[2], intent.id[3]
            ),
        },
        preconditions: Default::default(),
        effects: all_effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };

    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    // Build partial turn to get hash for binding the conservation proof.
    let partial_turn = Turn {
        agent: payer_cell,
        nonce,
        call_forest,
        fee: 0,
        memo: Some(format!(
            "committed fulfillment payment for intent {:02x}{:02x}...",
            intent.id[0], intent.id[1]
        )),
        // `valid_until: None` skips the executor's expiration check entirely
        // (`turn/src/executor/execute.rs:426`) — bound it with the module's shared
        // wall-clock horizon instead of `current_height` (a block height, not a timestamp).
        valid_until: default_valid_until(),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let turn_hash = partial_turn.hash();

    // Generate conservation proof.
    let sum_input_blindings = inputs
        .iter()
        .fold(Scalar::ZERO, |acc, inp| acc + inp.blinding);
    let sum_output_blindings = output_blindings.iter().fold(Scalar::ZERO, |acc, b| acc + b);
    let excess_blinding = sum_input_blindings - sum_output_blindings;

    let output_values: Vec<u64> = outputs.iter().map(|o| o.value).collect();
    let full_proof = prove_conservation_with_range(
        &input_commitments,
        &output_commitments,
        &output_values,
        &output_blindings,
        &excess_blinding,
        &turn_hash,
    );

    let proof_bytes = postcard::to_allocvec(&full_proof).map_err(|e| {
        FulfillmentError::PaymentFailed(format!("failed to serialize conservation proof: {e}"))
    })?;

    let turn = Turn {
        conservation_proof: Some(proof_bytes),
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
        ..partial_turn
    };

    // Step 3: Execute the turn.
    let result = executor.execute(&turn, ledger);

    match result {
        TurnResult::Committed { receipt, .. } => Ok(receipt),
        TurnResult::Rejected { reason, .. } => Err(FulfillmentError::PaymentFailed(format!(
            "committed payment turn rejected: {}",
            reason
        ))),
        TurnResult::Expired => Err(FulfillmentError::PaymentFailed(
            "committed payment turn expired during execution".into(),
        )),
        TurnResult::Pending => Err(FulfillmentError::PaymentFailed(
            "committed payment turn unexpectedly pending".into(),
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
    use dregg_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
    use dregg_circuit::multi_step_witness::{ALLOW_PREDICATE, build_multi_step_witness};
    use dregg_circuit::poseidon2::hash_fact;

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

    /// The fixed depth-2 co-path (`ATTESTED_DEPTH == 2`) the test facts sit under. In production
    /// the ISSUER builds the facts tree and the presentation attests its root; here it stands in
    /// for that — what is under test on the fulfillment path is the STATE-ROOT binding, not the
    /// tree build.
    fn test_attest_siblings() -> [[BabyBear; 3]; 2] {
        [
            [
                BabyBear::new(0xA1),
                BabyBear::new(0xA2),
                BabyBear::new(0xA3),
            ],
            [
                BabyBear::new(0xB1),
                BabyBear::new(0xB2),
                BabyBear::new(0xB3),
            ],
        ]
    }

    /// Build an ATTESTED `Gte` predicate proof BOUND to `state_root` — the third-party shape the
    /// fulfillment verifier now requires. The proof carries a `BridgeFactAttestation` whose
    /// membership STARK pins `state_root`, so verifying it against any OTHER trusted root refuses
    /// it (the cross-state binding). `predicate_sym` names the attribute fact; `value` is the
    /// private balance/score being proven `>= threshold`.
    fn attested_gte_proof(
        value: u32,
        predicate_sym: u32,
        threshold: u32,
        state_root: BabyBear,
    ) -> BridgePredicateProof {
        use dregg_bridge::present::{
            FactTerms, fresh_predicate_blinding, prove_predicate_for_fact_attested,
        };
        let binding = FactTerms {
            predicate_sym: BabyBear::new(predicate_sym),
            term1: BabyBear::ZERO,
            term2: BabyBear::ZERO,
        }
        .bind(state_root);
        prove_predicate_for_fact_attested(
            value,
            binding,
            fresh_predicate_blinding(),
            &BridgePredicate::Gte(threshold),
            &test_attest_siblings(),
        )
        .expect("attested gte predicate proof should be produced")
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
    fn test_fulfill_private_fails_closed_after_stark_retirement() {
        // The multi-step authorization hand-STARK engine was retired (no descriptor
        // replacement exists yet), so Private-mode fulfillment now FAILS CLOSED at proof
        // generation rather than emitting an unverifiable blob. This test pins that
        // fail-closed contract (was: `..._produces_stark_proof`).
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

        let result = fulfill(&intent, &matched, &token, our_id, &options);
        match result {
            Err(FulfillmentError::ProofGenerationFailed(msg)) => {
                assert!(
                    msg.contains("unavailable") && msg.contains("fail-closed"),
                    "expected the fail-closed retirement message, got: {msg}"
                );
            }
            other => panic!("private fulfillment must fail closed, got: {other:?}"),
        }
    }

    #[test]
    fn test_fulfill_selective_fails_closed_after_stark_retirement() {
        // Selective mode rides the same retired multi-step authorization proof → fail-closed.
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

        let result = fulfill(&intent, &matched, &token, our_id, &options);
        assert!(
            matches!(result, Err(FulfillmentError::ProofGenerationFailed(_))),
            "selective fulfillment must fail closed, got: {result:?}"
        );
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
    fn test_verify_fulfillment_private_fails_closed() {
        // A Private-mode fulfillment can no longer be produced (fail-closed at proof gen),
        // and even a hand-constructed one is rejected at verify: the multi-step
        // authorization statement has no descriptor verifier, so `verify_fulfillment`
        // fails closed rather than accept an unverifiable claim.
        let intent = test_intent(vec!["read"], None);

        // Hand-build a Private fulfillment carrying an arbitrary proof blob (fulfill itself
        // now fails closed, so we bypass it to exercise the verify-side fail-closed gate).
        let fulfillment = Fulfillment {
            intent_id: intent.id,
            fulfiller: CommitmentId([0xBB; 32]),
            mode: VerificationMode::Private,
            token_data: None,
            proof: Some(vec![0xADu8; 128]),
            granted_actions: vec!["read".into()],
            granted_resource: "*".into(),
            expiry: None,
        };
        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(
            matches!(result, Err(FulfillmentError::ProofVerificationFailed(_))),
            "private verify must fail closed after the hand-STARK retirement, got: {result:?}"
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
    fn test_verify_fulfillment_rejects_arbitrary_private_proof() {
        // With the hand-STARK engine retired, the Private verify path fails closed for
        // ANY supplied proof (no descriptor verifier exists for the multi-step
        // authorization statement). A tampered vs untampered blob is indistinguishable —
        // both are rejected — so we assert the blanket fail-closed rejection (was:
        // `..._rejects_tampered_proof`).
        let intent = test_intent(vec!["read"], None);
        let fulfillment = Fulfillment {
            intent_id: intent.id,
            fulfiller: CommitmentId([0xBB; 32]),
            mode: VerificationMode::Private,
            token_data: None,
            proof: Some(vec![0xADu8; 128]),
            granted_actions: vec!["read".into()],
            granted_resource: "*".into(),
            expiry: None,
        };
        let result = verify_fulfillment(&fulfillment, &intent, BabyBear::ZERO);
        assert!(
            matches!(result, Err(FulfillmentError::ProofVerificationFailed(_))),
            "any private proof must be rejected (fail-closed), got: {result:?}"
        );
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
    fn test_private_proof_generation_unavailable() {
        // The hand-STARK proof codec (`stark::proof_{to,from}_bytes`) and the multi-step
        // authorization prover were retired; a Private fulfillment proof can no longer be
        // produced. Pin that `produce_stark_proof` fails closed (was: a roundtrip test of
        // the removed codec).
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

        let result = fulfill(&intent, &matched, &token, our_id, &options);
        assert!(
            matches!(result, Err(FulfillmentError::ProofGenerationFailed(_))),
            "private proof generation must be unavailable (fail-closed), got: {result:?}"
        );
    }

    // =========================================================================
    // Predicate fulfillment tests
    // =========================================================================

    // BOTH POLES of the state-root binding on the fulfillment path, in one test.
    //
    // Formerly this test bound the proof to `state_root = 99999`, verified with a TRUSTED root of
    // `BabyBear::ZERO`, and asserted `is_ok()` — i.e. it asserted the forgery-accepting behavior
    // was CORRECT, green-lighting exactly the hole its `#[ignore]`d sibling documented. It now
    // drives:
    //   * the POSITIVE control — a genuine attested proof bound to the SAME trusted root VERIFIES
    //     (so the refusal below is real, not a test that refuses everything);
    //   * the FOREIGN pole — a proof bound to a foreign state root (99999) is REFUSED when the
    //     verifier trusts a different root (ZERO).
    #[test]
    fn test_verify_fulfillment_with_valid_predicate_proofs() {
        // Create an intent with a predicate requirement (`balance >= 1000`).
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

        let attr_sym = 42u32; // simulated attribute symbol
        let trusted_state_root = BabyBear::ZERO;
        let key = test_root_key();

        // A base fulfillment shared by both poles (its content is orthogonal to the predicate leg).
        let make_base = || {
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
            fulfill(
                &pred_intent,
                &matched,
                &token,
                CommitmentId([0xBB; 32]),
                &options,
            )
            .unwrap()
        };

        // ---- POSITIVE CONTROL: an attested proof bound to the SAME root the verifier trusts.
        let honest_proof = attested_gte_proof(5000, attr_sym, 1000, trusted_state_root);
        let honest = FulfillmentWithPredicates {
            base: make_base(),
            predicate_proofs: vec![(0, honest_proof)],
            state_root: trusted_state_root,
            state_root_block: 950, // recent enough
        };
        let ok = verify_fulfillment_with_predicates_and_key(
            &honest,
            &pred_intent,
            trusted_state_root,
            1000,
            Some(&key),
        );
        assert!(
            ok.is_ok(),
            "COMPLETENESS: a genuine attested predicate proof bound to the trusted state root must \
             VERIFY — without this the refusal below would prove nothing: {:?}",
            ok.err()
        );

        // ---- FOREIGN POLE: the SAME statement, but bound to a foreign state root (99999). The
        //      verifier trusts ZERO, so nothing ties this proof's commitment to the trusted state.
        let foreign_state_root = BabyBear::new(99999);
        let foreign_proof = attested_gte_proof(5000, attr_sym, 1000, foreign_state_root);
        let forged = FulfillmentWithPredicates {
            base: make_base(),
            predicate_proofs: vec![(0, foreign_proof)],
            state_root: foreign_state_root,
            state_root_block: 950,
        };
        let refused = verify_fulfillment_with_predicates_and_key(
            &forged,
            &pred_intent,
            trusted_state_root,
            1000,
            Some(&key),
        );
        assert!(
            refused.is_err(),
            "SOUNDNESS: a predicate proof bound to a FOREIGN state root (99999) must be REFUSED \
             when the verifier trusts a different root (ZERO)"
        );
    }

    // CROSS-STATE predicate FORGERY — the falsifier for the (now closed) hole on the fulfillment
    // path.
    //
    // `verify_fulfillment_with_predicates_and_key` receives the `state_root` the verifier TRUSTS
    // as a parameter. Formerly `verify_predicate_requirement` checked the proof with the BARE
    // `verify_predicate_proof(proof, proof.fact_commitment)` — against the proof's OWN commitment,
    // ignoring the trusted `state_root` — so a predicate proof bound (via its blinded fact
    // commitment) to a FOREIGN state root the verifier does not trust was ACCEPTED as though it
    // spoke about the trusted state. It is now bound: `verify_predicate_requirement` routes
    // through `verify_predicate_proof_third_party(proof, facts_root, trusted_state_root)`, which
    // pins the membership STARK to the trusted root.
    //
    // This drives THREE poles over ONE forged proof, so the refusal cannot pass vacuously:
    //   * NEUTERED CANARY — verify the forged proof against ITS OWN root (99999): ACCEPTED. This
    //     proves the proof is internally genuine, so what refuses it below is the ROOT MISMATCH,
    //     not a broken proof.
    //   * THE REAL GATE — verify against a DIFFERENT trusted root (12345): REFUSED.
    //   * FAIL-CLOSED — a proof with NO attestation, even bound to the trusted root, is REFUSED:
    //     nothing binds its commitment to the trusted state, so there is no `x == x` escape left.
    #[test]
    fn test_verify_fulfillment_rejects_cross_state_predicate_forgery() {
        use dregg_bridge::present::{
            FactTerms, fresh_predicate_blinding, prove_predicate_for_fact,
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
                state_root_freshness: 100,
            }],
            strict_resource_matching: false,
        };
        let pred_intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

        let key = test_root_key();
        let make_base = || {
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
            fulfill(
                &pred_intent,
                &matched,
                &token,
                CommitmentId([0xBB; 32]),
                &options,
            )
            .unwrap()
        };

        // A GENUINE `balance >= 1000` proof — but ATTESTED under a FOREIGN state root the verifier
        // does NOT trust (a different/fabricated account's state).
        let foreign_state_root = BabyBear::new(99999);
        let forged_proof = attested_gte_proof(5000, 42, 1000, foreign_state_root);
        let forged = FulfillmentWithPredicates {
            base: make_base(),
            predicate_proofs: vec![(0, forged_proof)],
            state_root: foreign_state_root,
            state_root_block: 950,
        };

        // ---- NEUTERED CANARY: verify against the forged proof's OWN root. ACCEPTED — so the
        //      refusal below is about the trusted-root mismatch, not a broken proof.
        let neutered = verify_fulfillment_with_predicates_and_key(
            &forged,
            &pred_intent,
            foreign_state_root, // the verifier is (wrongly) fed the prover's own root
            1000,
            Some(&key),
        );
        assert!(
            neutered.is_ok(),
            "CANARY: the forged proof must verify against its OWN state root, or this test is not \
             demonstrating a ROOT-MISMATCH refusal: {:?}",
            neutered.err()
        );

        // ---- THE REAL GATE: the verifier trusts a DIFFERENT state root (the real settled state).
        let trusted_state_root = BabyBear::new(12345);
        let refused = verify_fulfillment_with_predicates_and_key(
            &forged,
            &pred_intent,
            trusted_state_root,
            1000,
            Some(&key),
        );
        assert!(
            refused.is_err(),
            "SOUNDNESS: a predicate proof bound to a state root the verifier does NOT trust \
             (foreign 99999 vs trusted 12345) must be REJECTED — nothing ties the proof's \
             commitment to the trusted state."
        );

        // ---- FAIL-CLOSED: a proof carrying NO attestation, even bound to the trusted root, must
        //      be REFUSED. Nothing binds its commitment to the trusted state.
        let unattested = {
            let binding = FactTerms {
                predicate_sym: BabyBear::new(42),
                term1: BabyBear::ZERO,
                term2: BabyBear::ZERO,
            }
            .bind(trusted_state_root);
            prove_predicate_for_fact(
                5000,
                binding,
                fresh_predicate_blinding(),
                &BridgePredicate::Gte(1000),
            )
            .expect("gte predicate proof should be produced")
        };
        assert!(
            unattested.attestation.is_none(),
            "the trusted-state (re-derive) shape carries no attestation"
        );
        let no_attestation = FulfillmentWithPredicates {
            base: make_base(),
            predicate_proofs: vec![(0, unattested)],
            state_root: trusted_state_root,
            state_root_block: 950,
        };
        let refused_unattested = verify_fulfillment_with_predicates_and_key(
            &no_attestation,
            &pred_intent,
            trusted_state_root,
            1000,
            Some(&key),
        );
        assert!(
            refused_unattested.is_err(),
            "FAIL-CLOSED: a predicate proof with NO fact attestation must be REFUSED — nothing \
             binds its commitment to the trusted state, so the old x==x escape is gone"
        );
    }

    #[test]
    fn test_verify_fulfillment_rejects_stale_state_root() {
        use dregg_bridge::present::{FactTerms, prove_predicate_for_fact};
        use dregg_circuit::predicate_arith_witness::Blinding;

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

        // Real descriptor-backed Gte proof (balance 5000 >= 1000). The fact is named by its
        // TERMS (the value 5000 is `terms[0]`); `prove_predicate_for_fact` DERIVES the fact hash
        // and computes the blinded `fact_commitment` internally, and the proof carries it (plus
        // the blinding decommitment) for the verifier.
        let attr_sym = BabyBear::new(42);
        let state_root = BabyBear::new(99999);
        let fact = FactTerms {
            predicate_sym: attr_sym,
            term1: BabyBear::ZERO,
            term2: BabyBear::ZERO,
        }
        .bind(state_root);
        let predicate_proof = prove_predicate_for_fact(
            5000,
            fact,
            Blinding(BabyBear::new(0xB11D1)),
            &BridgePredicate::Gte(1000),
        )
        .expect("gte predicate proof should be produced");

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
        use dregg_bridge::present::{FactTerms, prove_predicate_for_fact};
        use dregg_circuit::predicate_arith_witness::Blinding;

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

        // Generate a proof for Gte(1000) — but the requirement demands Gte(2000). The bridge
        // proof carries its DECLARED predicate, and the verifier rejects the predicate
        // mismatch (the currency replacement for the retired hand-STARK `prove_predicate`).
        // The fact is named by its TERMS, not by an opaque `fact_hash`: the value (5000) is
        // `terms[0]` and the hash is DERIVED, so the value and the commitment cannot name
        // different facts. A REAL, non-zero blinding — the deployed (unlinkable) posture.
        let attr_sym = BabyBear::new(42); // simulated attribute symbol
        let state_root = BabyBear::new(99999);
        let fact = FactTerms {
            predicate_sym: attr_sym,
            term1: BabyBear::ZERO,
            term2: BabyBear::ZERO,
        }
        .bind(state_root);
        let predicate_proof = prove_predicate_for_fact(
            5000,
            fact,
            Blinding(BabyBear::new(0xB11D1)),
            &BridgePredicate::Gte(1000),
        )
        .expect("gte predicate proof should be produced");

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
                assert!(
                    msg.contains("does not match"),
                    "expected a predicate-mismatch rejection, got: {msg}"
                );
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

        // Both proofs are ATTESTED and bound to the SAME state root the verifier trusts. Each
        // presentation draws its OWN blinding (inside `attested_gte_proof`), so two facts shown at
        // once are not correlatable through a shared commitment factor.
        let state_root = BabyBear::ZERO;

        // Generate proof for balance >= 1000 (balance = 5000, the balance fact's value)
        let balance_proof = attested_gte_proof(5000, 42, 1000, state_root);

        // Generate proof for reputation >= 50 (reputation = 85, the reputation fact's value)
        let rep_proof = attested_gte_proof(85, 99, 50, state_root);

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
                    let mut hasher = blake3::Hasher::new_derive_key("dregg-fulfillment-payment-v1");
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
            dregg_turn::Effect::Transfer { from, to, amount } => {
                assert_eq!(*from, payer);
                assert_eq!(*to, recipient);
                assert_eq!(*amount, 500);
            }
            other => panic!("expected Transfer effect, got {:?}", other),
        }
    }

    #[test]
    fn test_execute_fulfillment_flow_success() {
        use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

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
        // ⚑ SAME TOKEN AS THE PAYER, and that is the whole point of the fixture.
        //
        // This read `[0x02; 32]`, so payer and recipient sat in DIFFERENT ASSET COLUMNS and the
        // fulfillment payment was a cross-asset Transfer — exactly the teleport `b1a370194` closed:
        // "a Transfer moves a SINGLE asset column (kernel `recTransferBal`); a value swap is two
        // same-asset transfers or a dedicated effect, never one cross-asset Transfer."
        //
        // The test was green only while that hole was open, and red since it was shut. A
        // fulfillment pays computrons for a service — both parties hold the same currency, and a
        // fixture where they do not was never modelling the flow it is named for.
        let recipient_token = payer_token;
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

        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::default());

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
        assert!(payer_state.state.balance() < 100_000); // Fee + transfer deducted.
        assert_eq!(recipient_state.state.balance(), 1000); // Received payment.
    }

    /// Shared setup for the VERIFIED flow tests: a Trusted-mode fulfillment for an intent
    /// with `min_budget = 1000`, plus payer/recipient cells in a fresh ledger.
    fn verified_flow_fixture(
        payer_balance: i64, // signed-wells (ac01f9b7b): cell balances are i64
    ) -> (
        Intent,
        FulfillmentWithPredicates,
        [u8; 32],
        dregg_cell::Ledger,
        CellId,
        CellId,
    ) {
        use dregg_cell::{Cell, Ledger};

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(1000),
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 5000, None);

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

        let payer_pk = [0xAA; 32];
        let payer_token = [0x01; 32];
        let payer_cell = CellId::derive_raw(&payer_pk, &payer_token);
        let recipient_pk = [0xBB; 32];
        // ⚑ SAME TOKEN AS THE PAYER, and that is the whole point of the fixture.
        //
        // This read `[0x02; 32]`, so payer and recipient sat in DIFFERENT ASSET COLUMNS and the
        // fulfillment payment was a cross-asset Transfer — exactly the teleport `b1a370194` closed:
        // "a Transfer moves a SINGLE asset column (kernel `recTransferBal`); a value swap is two
        // same-asset transfers or a dedicated effect, never one cross-asset Transfer."
        //
        // The test was green only while that hole was open, and red since it was shut. A
        // fulfillment pays computrons for a service — both parties hold the same currency, and a
        // fixture where they do not was never modelling the flow it is named for.
        let recipient_token = payer_token;
        let recipient_cell = CellId::derive_raw(&recipient_pk, &recipient_token);

        let mut ledger = Ledger::new();
        ledger
            .insert_cell(Cell::with_balance(payer_pk, payer_token, payer_balance))
            .unwrap();
        ledger
            .insert_cell(Cell::with_balance(recipient_pk, recipient_token, 0))
            .unwrap();

        (intent, fulfillment, key, ledger, payer_cell, recipient_cell)
    }

    /// A bare executor for the verified edge's ANCHOR context. The flow never executes a turn
    /// through it — it borrows the executor's live accumulator roots so the receipt's stamp is
    /// `state_commit::consensus_state_commitment` (see the fn's own docs).
    fn anchor_executor() -> TurnExecutor {
        TurnExecutor::new(dregg_turn::ComputronCosts::zero())
    }

    #[test]
    fn test_execute_fulfillment_flow_verified_success_moves_exactly_the_payment() {
        let (intent, fulfillment, key, mut ledger, payer_cell, recipient_cell) =
            verified_flow_fixture(100_000);
        let executor = anchor_executor();

        // BOTH the old (BLAKE3 whole-ledger) and the new (chip 8-felt) values of the pre-state,
        // so the assertions below can tell the fix from the bug.
        let pre_blake3 = ledger.root();
        let pre_anchor = executor.consensus_state_commitment(&ledger, &payer_cell);
        let receipt = execute_fulfillment_flow_verified_with_key(
            &intent,
            &fulfillment,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        )
        .expect("verified flow settles");

        // The verified edge moves EXACTLY the payment leg — no fee, no deposit, conserved.
        assert_eq!(ledger.get(&payer_cell).unwrap().state.balance(), 99_000);
        assert_eq!(ledger.get(&recipient_cell).unwrap().state.balance(), 1000);

        // ⚑ THE STAMP IS THE CONSENSUS ANCHOR. Until 2026-07-29 this edge wrote
        // `Ledger::root()` and this very test asserted it back, so the pair was green while
        // violating `turn/src/state_commit.rs:146`. The stamp is now the AIR-bound chip 8-felt
        // `consensus_state_commitment` — the same value `TurnExecutor::execute` and
        // `lean_apply::produce_via_lean` write.
        let post_anchor = executor.consensus_state_commitment(&ledger, &payer_cell);
        assert_eq!(receipt.agent, payer_cell);
        assert_eq!(receipt.pre_state_hash, pre_anchor);
        assert_eq!(receipt.post_state_hash, post_anchor);

        // ANTI-VACUITY: the new stamp must DIFFER from the old one, else the two assertions
        // above cannot distinguish the fix from the bug they replaced.
        let post_blake3 = ledger.root();
        assert_ne!(
            pre_anchor, pre_blake3,
            "the anchor must not be the BLAKE3 ledger root (else this test pins nothing)"
        );
        assert_ne!(
            post_anchor, post_blake3,
            "the anchor must not be the BLAKE3 ledger root (else this test pins nothing)"
        );
        assert_ne!(
            receipt.pre_state_hash, pre_blake3,
            "the receipt must NOT carry the old trusted-Rust BLAKE3 pre-state root"
        );
        assert_ne!(
            receipt.post_state_hash, post_blake3,
            "the receipt must NOT carry the old trusted-Rust BLAKE3 post-state root"
        );
        // The payment MOVED the anchor: a stamp that never changes verifies nothing.
        assert_ne!(
            receipt.pre_state_hash, receipt.post_state_hash,
            "the payment debits the payer, so the payer's anchor must move"
        );

        assert_ne!(receipt.turn_hash, [0u8; 32]);
        let expected_turn = create_fulfillment_turn(
            &intent,
            &fulfillment,
            payer_cell,
            recipient_cell,
            1000,
            1000,
        );
        assert_eq!(receipt.turn_hash, expected_turn.turn.hash());
    }

    /// **BOTH POLES of the receipt stamp**, in one process so an unrelated failure cannot read
    /// as the check: an HONEST fulfillment's `post_state_hash` VERIFIES through the real
    /// federation-exit verifier against the executor's own commitment, and the SAME receipt
    /// presented against a TAMPERED post-state is REFUSED with `StateChainBreak`.
    ///
    /// The tamper is on the object the anchor actually binds — the payer cell's balance — not a
    /// byte-flip of the receipt, so the refusal is the commitment doing its job.
    #[test]
    fn verified_fulfillment_stamp_verifies_honest_and_refuses_a_tampered_post_state() {
        use dregg_federation::verify_via_receipt_chain;

        let (intent, fulfillment, key, mut ledger, payer_cell, recipient_cell) =
            verified_flow_fixture(100_000);
        let executor = anchor_executor();

        let receipt = execute_fulfillment_flow_verified_with_key(
            &intent,
            &fulfillment,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        )
        .expect("verified flow settles");

        // ── POLE 1 (HONEST): the stamp verifies against the executor's own commitment.
        let honest_anchor = executor.consensus_state_commitment(&ledger, &payer_cell);
        assert_eq!(
            receipt.post_state_hash, honest_anchor,
            "an honest fulfillment's stamp IS the executor's consensus commitment"
        );
        verify_via_receipt_chain(std::slice::from_ref(&receipt), Some(honest_anchor))
            .expect("the honest chain head must bind the executor's own commitment");

        // ANTI-VACUITY for pole 1: the value asserted differs from the OLD (BLAKE3) stamp, so
        // a regression to `ledger.root()` fails here rather than sliding through.
        assert_ne!(
            honest_anchor,
            ledger.root(),
            "anchor and BLAKE3 ledger root must differ, else pole 1 proves nothing"
        );

        // ── POLE 2 (TAMPERED): inflate the payer's balance behind the receipt. The payer cell's
        // balance is inside the anchor's committed limbs, so the recomputed commitment MOVES and
        // the head-binding check REFUSES the chain.
        ledger
            .update_with(&payer_cell, |c| c.state.set_balance(9_999_999))
            .expect("tamper the payer balance");
        let tampered_anchor = executor.consensus_state_commitment(&ledger, &payer_cell);
        assert_ne!(
            tampered_anchor, honest_anchor,
            "the tamper must move the anchor, else pole 2 is vacuous"
        );
        let err = verify_via_receipt_chain(std::slice::from_ref(&receipt), Some(tampered_anchor))
            .expect_err("a receipt whose stamp does not bind the presented state must be REFUSED");
        assert!(
            matches!(err, dregg_turn::VerifyError::StateChainBreak { .. }),
            "expected StateChainBreak (the stamp does not bind the tampered state), got {err:?}"
        );

        // ── AND THE EXECUTOR'S LIVE ACCUMULATORS ARE GENUINELY READ, not a hardcoded empty
        // context: moving the nullifier accumulator moves the stamp a fresh run produces.
        let (intent2, fulfillment2, key2, mut ledger2, payer2, recipient2) =
            verified_flow_fixture(100_000);
        let executor2 = anchor_executor();
        executor2
            .note_nullifiers
            .lock()
            .unwrap()
            .insert(dregg_cell::note::Nullifier([0x5A; 32]), 1)
            .expect("seed the nullifier accumulator");
        let receipt2 = execute_fulfillment_flow_verified_with_key(
            &intent2,
            &fulfillment2,
            &executor2,
            &mut ledger2,
            payer2,
            recipient2,
            1000,
            1000,
            Some(&key2),
        )
        .expect("verified flow settles");
        assert_eq!(
            receipt2.post_state_hash,
            executor2.consensus_state_commitment(&ledger2, &payer2)
        );
        assert_ne!(
            receipt2.post_state_hash, receipt.post_state_hash,
            "the executor's LIVE nullifier root must be bound into the stamp — an equal value \
             here means the flow stamped a constant empty context, not this executor's state"
        );
    }

    #[test]
    fn test_execute_fulfillment_flow_verified_underfunded_refuses_untouched() {
        // Payer holds less than min_budget: the verified gate REFUSES and the ledger
        // is byte-identical (no partial debit, no fallback executor).
        let (intent, fulfillment, key, mut ledger, payer_cell, recipient_cell) =
            verified_flow_fixture(999);

        let pre_root = ledger.root();
        let result = execute_fulfillment_flow_verified_with_key(
            &intent,
            &fulfillment,
            &anchor_executor(),
            &mut ledger,
            payer_cell,
            recipient_cell,
            1000,
            1000,
            Some(&key),
        );
        assert!(
            matches!(result, Err(FulfillmentError::VerifiedRefusal(_))),
            "underfunded payment must be a VerifiedRefusal; got {result:?}"
        );
        assert_eq!(
            ledger.root(),
            pre_root,
            "refusal must leave the ledger untouched"
        );
        assert_eq!(ledger.get(&payer_cell).unwrap().state.balance(), 999);
        assert_eq!(ledger.get(&recipient_cell).unwrap().state.balance(), 0);
    }

    #[test]
    fn test_execute_fulfillment_flow_verified_missing_recipient_refuses() {
        // The verified liveness gate: a recipient cell absent from the ledger is a
        // refusal, never an implicit create (the legacy edge fell through here).
        let (intent, fulfillment, key, mut ledger, payer_cell, _recipient_cell) =
            verified_flow_fixture(100_000);
        let ghost = CellId::derive_raw(&[0xEE; 32], &[0xEE; 32]);

        let result = execute_fulfillment_flow_verified_with_key(
            &intent,
            &fulfillment,
            &anchor_executor(),
            &mut ledger,
            payer_cell,
            ghost,
            1000,
            1000,
            Some(&key),
        );
        assert!(
            matches!(result, Err(FulfillmentError::VerifiedRefusal(_))),
            "missing recipient must be a VerifiedRefusal; got {result:?}"
        );
        assert_eq!(ledger.get(&payer_cell).unwrap().state.balance(), 100_000);
    }

    #[test]
    fn test_execute_fulfillment_flow_verified_self_payment_refuses() {
        // The verified distinctness gate, checked on the REAL 32-byte cell ids.
        let (intent, fulfillment, key, mut ledger, payer_cell, _recipient_cell) =
            verified_flow_fixture(100_000);

        let result = execute_fulfillment_flow_verified_with_key(
            &intent,
            &fulfillment,
            &anchor_executor(),
            &mut ledger,
            payer_cell,
            payer_cell,
            1000,
            1000,
            Some(&key),
        );
        assert!(
            matches!(result, Err(FulfillmentError::VerifiedRefusal(_))),
            "self-payment must be a VerifiedRefusal; got {result:?}"
        );
        assert_eq!(ledger.get(&payer_cell).unwrap().state.balance(), 100_000);
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
        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::default());

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
        use dregg_cell::Ledger;

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
        let executor = TurnExecutor::new(dregg_turn::ComputronCosts::default());

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

    /// The sentinel must be `Some` — `None` here skips the executor's expiration check
    /// entirely (`turn/src/executor/execute.rs:426`), so a turn built that way never
    /// expires no matter how stale.
    #[test]
    fn default_valid_until_is_some() {
        assert!(
            default_valid_until().is_some(),
            "a None here means the fulfillment-payment turn never expires — see module docs \
             on default_valid_until"
        );
    }

    /// The stamped deadline must be a future WALL-CLOCK second count, not a block height —
    /// this module also has a `current_height` parameter nearby and it would be an easy
    /// mistake to stamp that instead (it would already be far in the past as a timestamp).
    #[test]
    fn default_valid_until_is_a_future_wall_clock_horizon_not_a_block_height() {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let stamped =
            default_valid_until().expect("must be Some, see default_valid_until_is_some");
        assert!(
            stamped > now,
            "stamped valid_until ({stamped}) must be strictly after now ({now})"
        );
        assert!(
            stamped <= now + FULFILLMENT_TURN_VALIDITY_HORIZON_SECS,
            "stamped valid_until ({stamped}) must not exceed the declared horizon (now={now} + \
             {FULFILLMENT_TURN_VALIDITY_HORIZON_SECS}s) — a block height here would be off by \
             many orders of magnitude in the wrong direction"
        );
    }

    /// Ratchet against the unbounded `valid_until` sentinel regrowing in a `Turn` literal
    /// this file builds. `include_str!` reads this file at COMPILE time, so this cannot go
    /// stale against what actually ships. This file is itself the one scanned, which is why
    /// the needle is assembled at runtime rather than written as one literal — a literal
    /// copy of it here would trivially match itself.
    #[test]
    fn no_fulfillment_turn_rebuilds_the_unbounded_valid_until_sentinel() {
        let src = include_str!("fulfillment.rs");
        let sentinel_field = "valid_until";
        let sentinel_value = "None";
        let needle = format!("{sentinel_field}: {sentinel_value},");
        assert!(
            !src.contains(&needle),
            "fulfillment.rs builds a Turn with `{sentinel_field}` bound to a bare \
             `{sentinel_value}` — this turn will NEVER expire (the executor's expiration \
             check is skipped entirely when this field is `{sentinel_value}`, \
             turn/src/executor/execute.rs:426). Use `default_valid_until()` instead, as \
             every other Turn literal in this file now does."
        );
    }
}
