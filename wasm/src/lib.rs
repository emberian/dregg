//! pyana-wasm: Interactive browser playground for pyana token primitives.
//!
//! Exposes token minting, attenuation, verification, STARK proof generation,
//! Merkle tree operations, and Datalog evaluation to JavaScript via wasm-bindgen.

use wasm_bindgen::prelude::*;
use serde::Serialize;

// Import the AuthToken trait to bring its methods into scope.
use pyana_token::AuthToken;

// ============================================================================
// Token operations (Macaroon backend)
// ============================================================================

/// Mint a new root macaroon token.
///
/// Returns JSON: { "token": "<em2_...>", "key_hex": "<hex>" }
#[wasm_bindgen]
pub fn mint_token(root_key: &[u8], location: &str) -> Result<JsValue, JsError> {
    if root_key.len() != 32 {
        return Err(JsError::new("root_key must be exactly 32 bytes"));
    }
    let mut key = [0u8; 32];
    key.copy_from_slice(root_key);

    let token = pyana_token::MacaroonToken::mint(key, b"playground-kid", location);
    let encoded = token.to_encoded().map_err(|e| JsError::new(&e.to_string()))?;

    #[derive(Serialize)]
    struct MintResult {
        token: String,
        location: String,
        format: String,
    }

    let result = MintResult {
        token: encoded,
        location: location.to_string(),
        format: "macaroon".to_string(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Generate a random 32-byte root key and return it as hex.
#[wasm_bindgen]
pub fn generate_root_key() -> Result<JsValue, JsError> {
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).map_err(|e| JsError::new(&e.to_string()))?;

    #[derive(Serialize)]
    struct KeyResult {
        key_hex: String,
        key_bytes: Vec<u8>,
    }

    let result = KeyResult {
        key_hex: hex_encode(&key),
        key_bytes: key.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Attenuate a macaroon token with service/action restrictions.
///
/// `actions` is a comma-separated list of action strings (e.g. "read,write").
/// `expires_secs` is seconds from now (0 means no expiry caveat).
///
/// Returns JSON: { "token": "<em2_...>", "caveats_added": N }
#[wasm_bindgen]
pub fn attenuate_token(
    token_str: &str,
    root_key: &[u8],
    service: &str,
    actions: &str,
    expires_secs: i64,
) -> Result<JsValue, JsError> {
    if root_key.len() != 32 {
        return Err(JsError::new("root_key must be exactly 32 bytes"));
    }
    let mut key = [0u8; 32];
    key.copy_from_slice(root_key);

    let token = pyana_token::MacaroonToken::from_encoded(token_str, key)
        .map_err(|e| JsError::new(&e.to_string()))?;

    let mut attenuation = pyana_token::Attenuation::default();
    if !service.is_empty() {
        attenuation.services = vec![(service.to_string(), actions.to_string())];
    }
    if expires_secs > 0 {
        // Set not-after to now + expires_secs
        let now = js_sys_now_secs();
        attenuation.not_after = Some(now + expires_secs);
    }

    let restricted: Box<dyn AuthToken> = token
        .attenuate(&attenuation)
        .map_err(|e| JsError::new(&e.to_string()))?;
    let encoded = restricted
        .to_encoded()
        .map_err(|e| JsError::new(&e.to_string()))?;

    #[derive(Serialize)]
    struct AttenuateResult {
        token: String,
        service: String,
        actions: String,
        expires_secs: i64,
    }

    let result = AttenuateResult {
        token: encoded,
        service: service.to_string(),
        actions: actions.to_string(),
        expires_secs,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a macaroon token against a request.
///
/// Returns JSON: { "allowed": bool, "policy": "...", "error": null | "..." }
#[wasm_bindgen]
pub fn verify_token(
    token_str: &str,
    root_key: &[u8],
    app_id: &str,
    action: &str,
) -> Result<JsValue, JsError> {
    if root_key.len() != 32 {
        return Err(JsError::new("root_key must be exactly 32 bytes"));
    }
    let mut key = [0u8; 32];
    key.copy_from_slice(root_key);

    let token = pyana_token::MacaroonToken::from_encoded(token_str, key)
        .map_err(|e| JsError::new(&e.to_string()))?;

    let mut request = pyana_token::AuthRequest::default();
    if !app_id.is_empty() {
        request.app_id = Some(app_id.to_string());
    }
    if !action.is_empty() {
        request.action = Some(action.to_string());
    }

    #[derive(Serialize)]
    struct VerifyResult {
        allowed: bool,
        policy: Option<String>,
        error: Option<String>,
    }

    let verification: Result<pyana_token::TokenClearance, pyana_token::TokenError> =
        token.verify(&request);

    match verification {
        Ok(clearance) => {
            let result = VerifyResult {
                allowed: true,
                policy: clearance.matched_policy,
                error: None,
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
        Err(e) => {
            let result = VerifyResult {
                allowed: false,
                policy: None,
                error: Some(e.to_string()),
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
    }
}

// ============================================================================
// STARK Proof operations
// ============================================================================

/// Generate a STARK proof for a Merkle membership claim.
///
/// `leaf_value` is a u32 field element, `depth` controls the Merkle tree depth (2-8).
///
/// Returns JSON with proof bytes, generation time, proof size, etc.
#[wasm_bindgen]
pub fn generate_stark_proof(leaf_value: u32, depth: u32) -> Result<JsValue, JsError> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{MerkleStarkAir, prove};

    let depth = depth.clamp(2, 8) as usize;

    let start = perf_now();

    // Build a Merkle membership trace:
    // Each row = [current_hash, sibling0, sibling1, sibling2, position, parent_hash]
    // The AIR checks: parent = current + sib0 + sib1 + sib2 + position
    let num_rows = depth.next_power_of_two().max(4);
    let leaf = BabyBear::new(leaf_value);

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(num_rows);
    let mut current = leaf;

    for level in 0..num_rows {
        let position = BabyBear::new((level % 4) as u32);
        // Deterministic siblings based on level
        let sib0 = BabyBear::new(100 + level as u32 * 7);
        let sib1 = BabyBear::new(200 + level as u32 * 13);
        let sib2 = BabyBear::new(300 + level as u32 * 17);
        let parent = current + sib0 + sib1 + sib2 + position;

        trace.push(vec![current, sib0, sib1, sib2, position, parent]);
        current = parent;
    }

    let public_inputs = vec![leaf, current]; // leaf and root
    let air = MerkleStarkAir;
    let proof = prove(&air, &trace, &public_inputs);

    let elapsed_ms = perf_now() - start;

    // Serialize the proof for size measurement
    let proof_bytes = serde_json::to_vec(&proof).unwrap_or_default();

    #[derive(Serialize)]
    struct ProofResult {
        proof_json: String,
        proof_size_bytes: usize,
        generation_time_ms: f64,
        trace_rows: usize,
        leaf_value: u32,
        root_value: u32,
        num_queries: usize,
        fri_layers: usize,
    }

    let result = ProofResult {
        proof_json: serde_json::to_string(&proof).unwrap_or_default(),
        proof_size_bytes: proof_bytes.len(),
        generation_time_ms: elapsed_ms,
        trace_rows: num_rows,
        leaf_value: leaf.0,
        root_value: current.0,
        num_queries: proof.query_proofs.len(),
        fri_layers: proof.fri_commitments.len(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a previously generated STARK proof.
///
/// Returns JSON: { "valid": bool, "error": null | "..." }
#[wasm_bindgen]
pub fn verify_stark_proof(proof_json: &str) -> Result<JsValue, JsError> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{MerkleStarkAir, StarkProof, verify};

    let start = perf_now();

    let proof: StarkProof =
        serde_json::from_str(proof_json).map_err(|e| JsError::new(&e.to_string()))?;

    let public_inputs: Vec<BabyBear> = proof.public_inputs.iter().map(|&v| BabyBear(v)).collect();
    let air = MerkleStarkAir;

    let result = verify(&air, &proof, &public_inputs);
    let elapsed_ms = perf_now() - start;

    #[derive(Serialize)]
    struct VerifyProofResult {
        valid: bool,
        error: Option<String>,
        verification_time_ms: f64,
    }

    let out = match result {
        Ok(()) => VerifyProofResult {
            valid: true,
            error: None,
            verification_time_ms: elapsed_ms,
        },
        Err(e) => VerifyProofResult {
            valid: false,
            error: Some(e),
            verification_time_ms: elapsed_ms,
        },
    };
    Ok(serde_wasm_bindgen::to_value(&out)?)
}

/// Tamper with a STARK proof by flipping bits in the first query's trace values.
///
/// Returns the tampered proof JSON.
#[wasm_bindgen]
pub fn tamper_stark_proof(proof_json: &str) -> Result<String, JsError> {
    use pyana_circuit::stark::StarkProof;

    let mut proof: StarkProof =
        serde_json::from_str(proof_json).map_err(|e| JsError::new(&e.to_string()))?;

    // Flip bits in the first query proof's trace values
    if let Some(query) = proof.query_proofs.first_mut() {
        if let Some(val) = query.trace_values.first_mut() {
            *val ^= 0xDEAD; // Corrupt the value
        }
    }

    serde_json::to_string(&proof).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Merkle Tree operations (4-ary, BLAKE3)
// ============================================================================

/// Compute a Merkle root from a list of leaf strings.
///
/// Returns JSON: { "root_hex": "...", "num_leaves": N, "tree_depth": D }
#[wasm_bindgen]
pub fn compute_merkle_root(leaves_json: &str) -> Result<JsValue, JsError> {
    use pyana_commit::{Fact, FactSet, FieldElement};

    let leaves: Vec<String> =
        serde_json::from_str(leaves_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut fs = FactSet::new();
    for leaf in &leaves {
        let fact = Fact::unary(
            FieldElement::from_symbol("leaf"),
            FieldElement::from_symbol(leaf),
        );
        fs.insert(fact);
    }

    let root = fs.root();

    #[derive(Serialize)]
    struct MerkleResult {
        root_hex: String,
        num_leaves: usize,
    }

    let result = MerkleResult {
        root_hex: hex_encode(&root),
        num_leaves: leaves.len(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Generate a Merkle membership proof for a specific leaf.
///
/// Returns JSON with the proof path and verification result.
#[wasm_bindgen]
pub fn merkle_membership_proof(leaves_json: &str, target_leaf: &str) -> Result<JsValue, JsError> {
    use pyana_commit::{Fact, FactSet, FieldElement};

    let leaves: Vec<String> =
        serde_json::from_str(leaves_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut fs = FactSet::new();
    for leaf in &leaves {
        let fact = Fact::unary(
            FieldElement::from_symbol("leaf"),
            FieldElement::from_symbol(leaf),
        );
        fs.insert(fact);
    }

    let root = fs.root();
    let target_fact = Fact::unary(
        FieldElement::from_symbol("leaf"),
        FieldElement::from_symbol(target_leaf),
    );

    #[derive(Serialize)]
    struct MembershipResult {
        root_hex: String,
        leaf: String,
        is_member: bool,
        proof_path_len: usize,
    }

    match fs.membership_proof(&target_fact) {
        Some(proof) => {
            let valid = FactSet::verify_membership(&root, &target_fact, &proof);
            let result = MembershipResult {
                root_hex: hex_encode(&root),
                leaf: target_leaf.to_string(),
                is_member: valid,
                proof_path_len: proof.siblings.len(),
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
        None => {
            let result = MembershipResult {
                root_hex: hex_encode(&root),
                leaf: target_leaf.to_string(),
                is_member: false,
                proof_path_len: 0,
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
    }
}

/// Generate a non-membership proof for a leaf NOT in the set.
#[wasm_bindgen]
pub fn merkle_non_membership_proof(
    leaves_json: &str,
    absent_leaf: &str,
) -> Result<JsValue, JsError> {
    use pyana_commit::{Fact, FactSet, FieldElement};

    let leaves: Vec<String> =
        serde_json::from_str(leaves_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut fs = FactSet::new();
    for leaf in &leaves {
        let fact = Fact::unary(
            FieldElement::from_symbol("leaf"),
            FieldElement::from_symbol(leaf),
        );
        fs.insert(fact);
    }

    let root = fs.root();
    let absent_fact = Fact::unary(
        FieldElement::from_symbol("leaf"),
        FieldElement::from_symbol(absent_leaf),
    );

    #[derive(Serialize)]
    struct NonMembershipResult {
        root_hex: String,
        leaf: String,
        proven_absent: bool,
    }

    match fs.non_membership_proof(&absent_fact) {
        Some(proof) => {
            let valid = FactSet::verify_non_membership(&root, &absent_fact, &proof);
            let result = NonMembershipResult {
                root_hex: hex_encode(&root),
                leaf: absent_leaf.to_string(),
                proven_absent: valid,
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
        None => {
            let result = NonMembershipResult {
                root_hex: hex_encode(&root),
                leaf: absent_leaf.to_string(),
                proven_absent: false,
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
    }
}

// ============================================================================
// Datalog Evaluator
// ============================================================================

/// Evaluate a Datalog authorization request against facts and rules.
///
/// `facts_json`: array of { "predicate": "name", "terms": ["const1", "const2"] }
/// `request_json`: { "app_id": "...", "action": "...", "service": "..." }
///
/// Returns the full derivation trace as JSON.
#[wasm_bindgen]
pub fn evaluate_datalog(facts_json: &str, request_json: &str) -> Result<JsValue, JsError> {
    use pyana_trace::{Evaluator, standard_policy};
    use pyana_trace::types::*;

    // Parse facts
    let raw_facts: Vec<RawFact> =
        serde_json::from_str(facts_json).map_err(|e| JsError::new(&e.to_string()))?;

    let facts: Vec<Fact> = raw_facts
        .into_iter()
        .map(|rf| {
            let pred = symbol_from_str(&rf.predicate);
            let terms: Vec<Term> = rf
                .terms
                .iter()
                .map(|t| {
                    if let Ok(n) = t.parse::<i64>() {
                        Term::Int(n)
                    } else {
                        Term::Const(symbol_from_str(t))
                    }
                })
                .collect();
            Fact::new(pred, terms)
        })
        .collect();

    // Parse request
    let raw_req: RawRequest =
        serde_json::from_str(request_json).map_err(|e| JsError::new(&e.to_string()))?;

    let request = AuthorizationRequest {
        app_id: raw_req.app_id.as_deref().map(symbol_from_str),
        service: raw_req.service.as_deref().map(symbol_from_str),
        action: raw_req.action.as_deref().map(symbol_from_str),
        features: raw_req
            .features
            .unwrap_or_default()
            .iter()
            .map(|s| symbol_from_str(s))
            .collect(),
        user_id: raw_req.user_id.as_deref().map(symbol_from_str),
        now: raw_req.now.unwrap_or(0),
    };

    // Use standard policy rules
    let rules = standard_policy();
    let evaluator = Evaluator::new(facts, rules);
    let trace = evaluator.evaluate(&request);

    #[derive(Serialize)]
    struct DatalogResult {
        conclusion: String,
        policy_rule_id: Option<u32>,
        num_derivation_steps: usize,
        steps: Vec<StepInfo>,
    }

    #[derive(Serialize)]
    struct StepInfo {
        rule_id: u32,
        derived_predicate_hex: String,
        num_bindings: usize,
    }

    let (conclusion_str, policy_id) = match &trace.conclusion {
        Conclusion::Allow { policy_rule_id } => ("allow".to_string(), Some(*policy_rule_id)),
        Conclusion::Deny => ("deny".to_string(), None),
    };

    let steps: Vec<StepInfo> = trace
        .steps
        .iter()
        .map(|s| StepInfo {
            rule_id: s.rule_id,
            derived_predicate_hex: hex_encode(&s.derived_fact.predicate),
            num_bindings: s.substitution.bindings.len(),
        })
        .collect();

    let result = DatalogResult {
        conclusion: conclusion_str,
        policy_rule_id: policy_id,
        num_derivation_steps: trace.steps.len(),
        steps,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Fold chain (attenuation visualization)
// ============================================================================

/// Create a token state, attenuate it, and return the fold chain info.
///
/// `facts_json`: array of strings like "predicate:term1:term2"
/// `remove_json`: array of strings (facts to remove in attenuation)
///
/// Returns JSON with old_root, new_root, verification status.
#[wasm_bindgen]
pub fn demonstrate_fold(facts_json: &str, remove_json: &str) -> Result<JsValue, JsError> {
    use pyana_commit::{Fact, FieldElement, FoldDeltaBuilder, TokenState};

    let fact_strs: Vec<String> =
        serde_json::from_str(facts_json).map_err(|e| JsError::new(&e.to_string()))?;
    let remove_strs: Vec<String> =
        serde_json::from_str(remove_json).map_err(|e| JsError::new(&e.to_string()))?;

    // Build initial state
    let mut state = TokenState::new();
    let mut all_facts: Vec<Fact> = Vec::new();

    for s in &fact_strs {
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() >= 2 {
            let fact = Fact::unary(
                FieldElement::from_symbol(parts[0]),
                FieldElement::from_symbol(parts[1]),
            );
            state.add_fact(fact);
            all_facts.push(fact);
        }
    }

    let old_root = state.root();

    // Build attenuation delta
    let mut builder = FoldDeltaBuilder::new(state.clone());
    let mut removed_count = 0;

    for s in &remove_strs {
        let parts: Vec<&str> = s.split(':').collect();
        if parts.len() >= 2 {
            let fact = Fact::unary(
                FieldElement::from_symbol(parts[0]),
                FieldElement::from_symbol(parts[1]),
            );
            builder = builder.remove_fact(fact);
            removed_count += 1;
        }
    }

    #[derive(Serialize)]
    struct FoldResult {
        old_root_hex: String,
        new_root_hex: String,
        verified: bool,
        total_facts: usize,
        removed_facts: usize,
        remaining_facts: usize,
    }

    match builder.build() {
        Some(delta) => {
            let verified = delta.apply_and_verify();
            let result = FoldResult {
                old_root_hex: hex_encode(&old_root),
                new_root_hex: hex_encode(&delta.new_root),
                verified,
                total_facts: all_facts.len(),
                removed_facts: removed_count,
                remaining_facts: all_facts.len() - removed_count,
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
        None => {
            let result = FoldResult {
                old_root_hex: hex_encode(&old_root),
                new_root_hex: hex_encode(&old_root),
                verified: false,
                total_facts: all_facts.len(),
                removed_facts: 0,
                remaining_facts: all_facts.len(),
            };
            Ok(serde_wasm_bindgen::to_value(&result)?)
        }
    }
}

// ============================================================================
// Helpers
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn perf_now() -> f64 {
    #[cfg(target_arch = "wasm32")]
    {
        web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(0.0)
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        0.0
    }
}

fn js_sys_now_secs() -> i64 {
    #[cfg(target_arch = "wasm32")]
    {
        (js_sys::Date::now() / 1000.0) as i64
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        0
    }
}

// ============================================================================
// Internal serde types for JSON input parsing
// ============================================================================

#[derive(serde::Deserialize)]
struct RawFact {
    predicate: String,
    terms: Vec<String>,
}

#[derive(serde::Deserialize)]
struct RawRequest {
    app_id: Option<String>,
    service: Option<String>,
    action: Option<String>,
    features: Option<Vec<String>>,
    user_id: Option<String>,
    now: Option<i64>,
}
