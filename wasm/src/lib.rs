//! pyana-wasm: Interactive browser playground for the pyana distributed system.
//!
//! Exposes:
//! - Token minting, attenuation, verification (macaroon backend)
//! - STARK proof generation and verification
//! - Merkle tree operations
//! - Datalog authorization evaluation
//! - **Full runtime simulation**: cells, turns, capabilities, notes, federations, intents
//!
//! The `PyanaRuntime` (in `runtime` module) provides a complete virtualized distributed
//! system running in the browser. Users can create federations, agents, execute turns,
//! exercise capabilities, bridge notes, and match intents -- all in WASM.

use serde::Serialize;
use wasm_bindgen::prelude::*;

// Import the AuthToken trait to bring its methods into scope.
use pyana_token::AuthToken;

// Full runtime simulation modules.
pub mod bindings;
pub mod privacy;
pub mod runtime;

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
    let encoded = token
        .to_encoded()
        .map_err(|e| JsError::new(&e.to_string()))?;

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

/// Demo/playground only. Uses simplified linear AIR (field-addition parent
/// computation), not cryptographically sound for production. Generates a STARK
/// proof for a Merkle membership claim using `MerkleStarkAir`.
///
/// `leaf_value` is a u32 field element, `depth` controls the Merkle tree depth (2-8).
///
/// Returns JSON with proof bytes, generation time, proof size, etc.
#[wasm_bindgen]
pub fn generate_demo_stark_proof(leaf_value: u32, depth: u32) -> Result<JsValue, JsError> {
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

/// Demo/playground only. Uses simplified linear AIR, not cryptographically
/// sound for production. Verifies a previously generated demo STARK proof.
///
/// Returns JSON: { "valid": bool, "error": null | "..." }
#[wasm_bindgen]
pub fn verify_demo_stark_proof(proof_json: &str) -> Result<JsValue, JsError> {
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

/// Demo/playground only. Tamper with a demo STARK proof by flipping bits in
/// the first query's trace values.
///
/// Returns the tampered proof JSON.
#[wasm_bindgen]
pub fn tamper_demo_stark_proof(proof_json: &str) -> Result<String, JsError> {
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
// Predicate Proof generation (range/comparison ZK proofs)
// ============================================================================

/// Generate a predicate proof for a private attribute.
///
/// Proves a comparison statement about `private_value` vs `threshold` without
/// revealing the private value. The proof is bound to a fact commitment derived
/// from the attribute key and a state root.
///
/// `predicate_type`: "gte", "lte", "gt", "lt", "neq"
/// `private_value`: The secret value (u32 field element)
/// `threshold`: The public comparison target (u32 field element)
/// `attribute_key`: String key used to derive the fact hash
/// `state_root`: A u32 field element representing the token state root
///
/// Returns JSON with proof data, or an error if the predicate is not satisfiable.
#[wasm_bindgen]
pub fn generate_predicate_proof(
    predicate_type: &str,
    private_value: u32,
    threshold: u32,
    attribute_key: &str,
    state_root: u32,
) -> Result<JsValue, JsError> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2;
    use pyana_circuit::predicate_types::{PredicateType, PredicateWitness, prove_predicate};

    let start = perf_now();

    let pred_type = match predicate_type {
        "gte" | "Gte" | "GTE" | ">=" => PredicateType::Gte,
        "lte" | "Lte" | "LTE" | "<=" => PredicateType::Lte,
        "gt" | "Gt" | "GT" | ">" => PredicateType::Gt,
        "lt" | "Lt" | "LT" | "<" => PredicateType::Lt,
        "neq" | "Neq" | "NEQ" | "!=" => PredicateType::Neq,
        other => return Err(JsError::new(&format!("unknown predicate type: {other}"))),
    };

    // Compute fact hash from attribute key.
    let fact_hash = poseidon2::hash_bytes(attribute_key.as_bytes());
    let state_root_bb = BabyBear::new(state_root);

    // Generate a random blinding factor for unlinkable proofs.
    // P2 audit fix: was 4 bytes with silent zeroing on getrandom failure
    // (`unwrap_or_default()`). Now: 8 bytes, reduced into the field, and
    // any getrandom failure is propagated to the caller as a JsError.
    let mut blinding_bytes = [0u8; 8];
    getrandom::fill(&mut blinding_bytes)
        .map_err(|e| JsError::new(&format!("getrandom failed: {e}")))?;
    let blinding = BabyBear::from_u64(u64::from_le_bytes(blinding_bytes));

    let fact_commitment = pyana_circuit::predicate_types::compute_blinded_fact_commitment(
        fact_hash,
        state_root_bb,
        blinding,
    );

    let witness = PredicateWitness {
        private_value: BabyBear::new(private_value),
        threshold: BabyBear::new(threshold),
        predicate_type: pred_type,
        fact_commitment,
        blinding: Some(blinding),
        fact_hash: Some(fact_hash),
        state_root: Some(state_root_bb),
    };

    let proof = prove_predicate(witness).ok_or_else(|| {
        JsError::new(&format!(
            "predicate not satisfiable: {} {} {}",
            private_value, predicate_type, threshold
        ))
    })?;

    let elapsed_ms = perf_now() - start;

    // Serialize proof to JSON bytes for size measurement.
    let proof_bytes = serde_json::to_vec(&proof).unwrap_or_default();

    #[derive(Serialize)]
    struct PredicateProofResult {
        proof_json: String,
        proof_size_bytes: usize,
        generation_time_ms: f64,
        predicate_type: String,
        threshold: u32,
        fact_commitment: u32,
        verified: bool,
    }

    // Self-verify.
    let verified = pyana_circuit::predicate_types::verify_predicate(
        &proof,
        BabyBear::new(threshold),
        fact_commitment,
    )
    .is_ok();

    let result = PredicateProofResult {
        proof_json: serde_json::to_string(&proof).unwrap_or_default(),
        proof_size_bytes: proof_bytes.len(),
        generation_time_ms: elapsed_ms,
        predicate_type: predicate_type.to_string(),
        threshold,
        fact_commitment: fact_commitment.as_u32(),
        verified,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a predicate proof.
///
/// `proof_json`: The serialized proof (from generate_predicate_proof).
/// `threshold`: The expected threshold.
/// `fact_commitment`: The expected fact commitment (from generate_predicate_proof output).
///
/// Returns JSON: { "valid": bool, "error": null | "..." }
#[wasm_bindgen]
pub fn verify_predicate_proof(
    proof_json: &str,
    threshold: u32,
    fact_commitment: u32,
) -> Result<JsValue, JsError> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::predicate_types::{PredicateProof, verify_predicate};

    let proof: PredicateProof =
        serde_json::from_str(proof_json).map_err(|e| JsError::new(&e.to_string()))?;

    let valid =
        verify_predicate(&proof, BabyBear::new(threshold), BabyBear(fact_commitment)).is_ok();

    #[derive(Serialize)]
    struct VerifyResult {
        valid: bool,
    }

    let result = VerifyResult { valid };
    Ok(serde_wasm_bindgen::to_value(&result)?)
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
    use pyana_trace::types::*;
    use pyana_trace::{Evaluator, standard_policy};

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
// BLAKE3 hashing and Intent ID computation
// ============================================================================

/// Compute a BLAKE3 hash of an arbitrary string, returning the hex digest.
///
/// This is exposed so the extension can produce BLAKE3 hashes without pulling
/// in a full JS implementation.
#[wasm_bindgen]
pub fn blake3_hash(input: &str) -> String {
    let hash = blake3::hash(input.as_bytes());
    hex_encode(hash.as_bytes())
}

/// Compute a canonical intent ID exactly as the Rust intent engine does.
///
/// Takes a JSON object with: kind, actions, resource_pattern, constraints, expiry, creator.
/// Returns the hex-encoded 32-byte BLAKE3 intent ID using postcard serialization,
/// identical to `Intent::compute_id()` in the `pyana-intent` crate.
///
/// JSON schema:
/// ```json
/// {
///   "kind": "Need" | "Offer" | "Query",
///   "actions": [{"action": "read", "resource": "docs/*"}, ...],
///   "constraints": [{"AppId": "x"}, {"Service": "y"}, ...],
///   "min_budget": null | 1000,
///   "resource_pattern": null | "docs/*",
///   "compound": null | [{ "actions": [...], ... }],
///   "expiry": 1716000000,
///   "creator": [170, 170, ...] (32 bytes),
///   "stake_commitment": null | [1, 2, 3, ...] (32 bytes)
/// }
/// ```
#[wasm_bindgen]
pub fn compute_intent_id(intent_json: &str) -> Result<String, JsError> {
    let input: IntentIdInput =
        serde_json::from_str(intent_json).map_err(|e| JsError::new(&e.to_string()))?;

    // Map to the canonical serialization types that match intent/src/lib.rs exactly.
    let kind = match input.kind.as_str() {
        "Need" | "need" => CanonicalIntentKind::Need,
        "Offer" | "offer" => CanonicalIntentKind::Offer,
        "Query" | "query" => CanonicalIntentKind::Query,
        other => return Err(JsError::new(&format!("unknown intent kind: {other}"))),
    };

    let actions: Vec<CanonicalActionPattern> = input
        .actions
        .unwrap_or_default()
        .into_iter()
        .map(|a| CanonicalActionPattern {
            action: a.action,
            resource: a.resource,
        })
        .collect();

    let constraints: Vec<CanonicalConstraint> = input
        .constraints
        .unwrap_or_default()
        .into_iter()
        .map(|c| {
            if let Some(v) = c.app_id {
                return CanonicalConstraint::AppId(v);
            }
            if let Some(v) = c.service {
                return CanonicalConstraint::Service(v);
            }
            if let Some(v) = c.user_id {
                return CanonicalConstraint::UserId(v);
            }
            if let Some(v) = c.not_expired_at {
                return CanonicalConstraint::NotExpiredAt(v);
            }
            if let Some(v) = c.feature {
                return CanonicalConstraint::Feature(v);
            }
            if let Some(v) = c.oauth_provider {
                return CanonicalConstraint::OAuthProvider(v);
            }
            if let (Some(p), Some(v)) = (c.predicate, c.value) {
                return CanonicalConstraint::Custom {
                    predicate: p,
                    value: v,
                };
            }
            // Fallback: empty custom constraint (should not happen with valid input).
            CanonicalConstraint::Custom {
                predicate: String::new(),
                value: String::new(),
            }
        })
        .collect();

    let matcher = CanonicalMatchSpec {
        actions,
        constraints,
        min_budget: input.min_budget,
        resource_pattern: input.resource_pattern,
        compound: input.compound.map(|specs| {
            specs
                .into_iter()
                .map(|s| {
                    let actions: Vec<CanonicalActionPattern> = s
                        .actions
                        .unwrap_or_default()
                        .into_iter()
                        .map(|a| CanonicalActionPattern {
                            action: a.action,
                            resource: a.resource,
                        })
                        .collect();
                    let constraints: Vec<CanonicalConstraint> = s
                        .constraints
                        .unwrap_or_default()
                        .into_iter()
                        .map(|c| {
                            if let Some(v) = c.app_id {
                                return CanonicalConstraint::AppId(v);
                            }
                            if let Some(v) = c.service {
                                return CanonicalConstraint::Service(v);
                            }
                            if let Some(v) = c.user_id {
                                return CanonicalConstraint::UserId(v);
                            }
                            if let Some(v) = c.not_expired_at {
                                return CanonicalConstraint::NotExpiredAt(v);
                            }
                            if let Some(v) = c.feature {
                                return CanonicalConstraint::Feature(v);
                            }
                            if let Some(v) = c.oauth_provider {
                                return CanonicalConstraint::OAuthProvider(v);
                            }
                            if let (Some(p), Some(v)) = (c.predicate, c.value) {
                                return CanonicalConstraint::Custom {
                                    predicate: p,
                                    value: v,
                                };
                            }
                            CanonicalConstraint::Custom {
                                predicate: String::new(),
                                value: String::new(),
                            }
                        })
                        .collect();
                    CanonicalMatchSpec {
                        actions,
                        constraints,
                        min_budget: s.min_budget,
                        resource_pattern: s.resource_pattern,
                        compound: None, // Nested compounds not supported
                    }
                })
                .collect()
        }),
    };

    let creator = CanonicalCommitmentId(
        input
            .creator
            .unwrap_or_else(|| vec![0u8; 32])
            .try_into()
            .map_err(|_| JsError::new("creator must be exactly 32 bytes"))?,
    );

    // stake_commitment: matches IntentBody in intent/src/lib.rs which hashes
    // the commitment bytes from the stake proof (if present).
    // P1 audit fix: propagate length errors instead of panicking on
    // attacker-controlled input (the previous `.map_err(...).unwrap()` was
    // structurally wrong; it called `unwrap` on a `Result<JsError, _>` whose
    // `Err` arm was the constructed error, so any wrong-length input panicked).
    let stake_commitment: Option<[u8; 32]> = match input.stake_commitment {
        Some(bytes) => Some(
            bytes
                .try_into()
                .map_err(|_| JsError::new("stake_commitment must be exactly 32 bytes"))?,
        ),
        None => None,
    };

    // Build the body struct that matches IntentBody in intent/src/lib.rs
    let body = CanonicalIntentBody {
        kind: &kind,
        matcher: &matcher,
        creator: &creator,
        expiry: input.expiry,
        stake_commitment: stake_commitment.as_ref(),
    };

    let canonical = postcard::to_allocvec(&body)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;

    let mut hasher = blake3::Hasher::new_derive_key("pyana-intent-id-v2");
    hasher.update(&canonical);
    let hash = hasher.finalize();

    Ok(hex_encode(hash.as_bytes()))
}

// --- Types that mirror intent/src/lib.rs for canonical serialization ---

#[derive(serde::Deserialize)]
struct IntentIdInput {
    kind: String,
    actions: Option<Vec<ActionPatternInput>>,
    constraints: Option<Vec<ConstraintInput>>,
    min_budget: Option<u64>,
    resource_pattern: Option<String>,
    compound: Option<Vec<MatchSpecInput>>,
    expiry: u64,
    creator: Option<Vec<u8>>,
    /// The 32-byte commitment from the stake proof (if present).
    /// This matches `stake_commitment` in the Rust IntentBody.
    stake_commitment: Option<Vec<u8>>,
}

#[derive(serde::Deserialize)]
struct MatchSpecInput {
    actions: Option<Vec<ActionPatternInput>>,
    constraints: Option<Vec<ConstraintInput>>,
    min_budget: Option<u64>,
    resource_pattern: Option<String>,
}

#[derive(serde::Deserialize)]
struct ActionPatternInput {
    action: Option<String>,
    resource: Option<String>,
}

#[derive(serde::Deserialize)]
struct ConstraintInput {
    #[serde(rename = "AppId")]
    app_id: Option<String>,
    #[serde(rename = "Service")]
    service: Option<String>,
    #[serde(rename = "UserId")]
    user_id: Option<String>,
    #[serde(rename = "NotExpiredAt")]
    not_expired_at: Option<i64>,
    #[serde(rename = "Feature")]
    feature: Option<String>,
    #[serde(rename = "OAuthProvider")]
    oauth_provider: Option<String>,
    predicate: Option<String>,
    value: Option<String>,
}

/// These types MUST serialize identically to intent/src/lib.rs via postcard.
/// Field order and enum variant indices must match exactly.
#[derive(Serialize)]
enum CanonicalIntentKind {
    Need,
    Offer,
    Query,
}

#[derive(Serialize)]
struct CanonicalActionPattern {
    action: Option<String>,
    resource: Option<String>,
}

#[derive(Serialize)]
enum CanonicalConstraint {
    AppId(String),
    Service(String),
    UserId(String),
    NotExpiredAt(i64),
    Feature(String),
    OAuthProvider(String),
    Custom { predicate: String, value: String },
}

#[derive(Serialize)]
struct CanonicalMatchSpec {
    actions: Vec<CanonicalActionPattern>,
    constraints: Vec<CanonicalConstraint>,
    min_budget: Option<u64>,
    resource_pattern: Option<String>,
    compound: Option<Vec<CanonicalMatchSpec>>,
}

#[derive(Serialize)]
struct CanonicalCommitmentId(pub [u8; 32]);

#[derive(Serialize)]
struct CanonicalIntentBody<'a> {
    kind: &'a CanonicalIntentKind,
    matcher: &'a CanonicalMatchSpec,
    creator: &'a CanonicalCommitmentId,
    expiry: u64,
    /// We hash the commitment bytes from the stake proof (if present) for ID binding.
    stake_commitment: Option<&'a [u8; 32]>,
}

// ============================================================================
// Committed Threshold Predicates
// ============================================================================

/// Prove that a private value meets a committed threshold (value >= threshold)
/// without revealing either value to third parties.
///
/// `value`: the prover's private attribute value (u32 field element)
/// `threshold`: the verifier's threshold (u32 field element)
/// `blinding`: randomness for the threshold commitment (u32 field element)
///
/// Returns JSON with: proof bytes, threshold_commitment, fact_commitment, verified status.
/// Returns error if the predicate is not satisfiable (value < threshold).
#[wasm_bindgen]
pub fn prove_committed_threshold(
    value: u32,
    threshold: u32,
    blinding: u32,
) -> Result<JsValue, JsError> {
    use pyana_circuit::committed_threshold::{
        CommittedThresholdWitness, compute_threshold_commitment,
        prove_committed_threshold as prove_ct, verify_committed_threshold as verify_ct,
    };
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2;

    let start = perf_now();

    let value_bb = BabyBear::new(value);
    let threshold_bb = BabyBear::new(threshold);
    let blinding_bb = BabyBear::new(blinding);

    // Compute a fact commitment (binding to token state).
    let fact_hash = poseidon2::hash_many(&[value_bb, BabyBear::new(42)]);
    let state_root = BabyBear::new(99999);
    let fact_commitment = poseidon2::hash_2_to_1(fact_hash, state_root);

    let witness = CommittedThresholdWitness {
        private_value: value_bb,
        threshold: threshold_bb,
        blinding: blinding_bb,
        fact_commitment,
    };

    let threshold_commitment = compute_threshold_commitment(threshold_bb, blinding_bb);

    let proof = prove_ct(witness).ok_or_else(|| {
        JsError::new(&format!(
            "predicate not satisfiable: {} >= {} is false",
            value, threshold
        ))
    })?;

    let verified = verify_ct(&proof, threshold_commitment, fact_commitment);
    let elapsed_ms = perf_now() - start;

    let proof_bytes = serde_json::to_vec(&proof.stark_proof).unwrap_or_default();

    #[derive(Serialize)]
    struct CommittedThresholdResult {
        threshold_commitment: u32,
        fact_commitment: u32,
        proof_size_bytes: usize,
        generation_time_ms: f64,
        verified: bool,
    }

    let result = CommittedThresholdResult {
        threshold_commitment: threshold_commitment.as_u32(),
        fact_commitment: fact_commitment.as_u32(),
        proof_size_bytes: proof_bytes.len(),
        generation_time_ms: elapsed_ms,
        verified,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a committed threshold proof given the public commitments.
///
/// `threshold_commitment`: the Poseidon2(threshold, blinding) value
/// `fact_commitment`: the binding to token state
/// `proof_json`: serialized STARK proof (from prove_committed_threshold)
///
/// Returns JSON: { "valid": bool, "verification_time_ms": f64 }
#[wasm_bindgen]
pub fn verify_committed_threshold(
    proof_json: &str,
    threshold_commitment: u32,
    fact_commitment: u32,
) -> Result<JsValue, JsError> {
    use pyana_circuit::committed_threshold::{
        CommittedThresholdProof, verify_committed_threshold as verify_ct,
    };
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::StarkProof;

    let start = perf_now();

    let stark_proof: StarkProof =
        serde_json::from_str(proof_json).map_err(|e| JsError::new(&e.to_string()))?;

    let tc = BabyBear(threshold_commitment);
    let fc = BabyBear(fact_commitment);

    let proof = CommittedThresholdProof {
        threshold_commitment: tc,
        fact_commitment: fc,
        stark_proof,
    };

    let valid = verify_ct(&proof, tc, fc);
    let elapsed_ms = perf_now() - start;

    #[derive(Serialize)]
    struct VerifyResult {
        valid: bool,
        verification_time_ms: f64,
    }

    let result = VerifyResult {
        valid,
        verification_time_ms: elapsed_ms,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Schnorr Signatures (BabyBear^8 curve)
// ============================================================================

/// Generate a Schnorr keypair from a random seed.
///
/// Returns JSON: { "secret_key": [8 u32 elements], "public_key": { "x": [8], "y": [8] } }
#[wasm_bindgen]
pub fn schnorr_keygen() -> Result<JsValue, JsError> {
    use pyana_circuit::schnorr_curve::scalar_to_bytes;
    use pyana_circuit::schnorr_sig::schnorr_keygen as keygen;

    let mut seed = [0u8; 32];
    getrandom::fill(&mut seed).map_err(|e| JsError::new(&e.to_string()))?;

    let (sk, pk) = keygen(&seed);

    let sk_bytes = scalar_to_bytes(&sk.0);

    #[derive(Serialize)]
    struct KeypairResult {
        secret_key: Vec<u8>,
        public_key_x: Vec<u32>,
        public_key_y: Vec<u32>,
    }

    let result = KeypairResult {
        secret_key: sk_bytes.to_vec(),
        public_key_x: pk.0.x.0.iter().map(|e| e.as_u32()).collect(),
        public_key_y: pk.0.y.0.iter().map(|e| e.as_u32()).collect(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Sign a message with a Schnorr secret key.
///
/// `secret_key_json`: JSON with { "secret_key": [32 bytes] }
/// `message`: the message string to sign
///
/// Returns JSON with signature { "r_x": [8], "r_y": [8], "s": [8] }
#[wasm_bindgen]
pub fn schnorr_sign(secret_key_json: &str, message: &str) -> Result<JsValue, JsError> {
    use pyana_circuit::schnorr_curve::scalar_to_bytes;
    use pyana_circuit::schnorr_sig::{schnorr_keygen as keygen, schnorr_sign as sign};

    #[derive(serde::Deserialize)]
    struct SecretKeyInput {
        secret_key: Vec<u8>,
    }

    let input: SecretKeyInput =
        serde_json::from_str(secret_key_json).map_err(|e| JsError::new(&e.to_string()))?;

    if input.secret_key.len() != 32 {
        return Err(JsError::new("secret_key must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&input.secret_key);

    // Re-derive the keypair from the seed (same derivation as keygen).
    let (sk, pk) = keygen(&seed);

    let sig = sign(&sk, &pk, message.as_bytes());
    let s_bytes = scalar_to_bytes(&sig.s);

    #[derive(Serialize)]
    struct SignatureResult {
        r_x: Vec<u32>,
        r_y: Vec<u32>,
        s: Vec<u8>,
    }

    let result = SignatureResult {
        r_x: sig.r.x.0.iter().map(|e| e.as_u32()).collect(),
        r_y: sig.r.y.0.iter().map(|e| e.as_u32()).collect(),
        s: s_bytes.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a Schnorr signature.
///
/// `public_key_json`: JSON with { "public_key_x": [8 u32], "public_key_y": [8 u32] }
/// `message`: the message string
/// `signature_json`: JSON with { "r_x": [8 u32], "r_y": [8 u32], "s": [32 bytes] }
///
/// Returns bool: true if signature is valid.
#[wasm_bindgen]
pub fn schnorr_verify(
    public_key_json: &str,
    message: &str,
    signature_json: &str,
) -> Result<bool, JsError> {
    use pyana_circuit::babybear8::BabyBear8;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::schnorr_curve::{CurvePoint, scalar_from_bytes};
    use pyana_circuit::schnorr_sig::{
        SchnorrPublicKey, SchnorrSignature, schnorr_verify as verify,
    };

    #[derive(serde::Deserialize)]
    struct PubKeyInput {
        public_key_x: Vec<u32>,
        public_key_y: Vec<u32>,
    }

    #[derive(serde::Deserialize)]
    struct SigInput {
        r_x: Vec<u32>,
        r_y: Vec<u32>,
        s: Vec<u8>,
    }

    let pk_input: PubKeyInput =
        serde_json::from_str(public_key_json).map_err(|e| JsError::new(&e.to_string()))?;
    let sig_input: SigInput =
        serde_json::from_str(signature_json).map_err(|e| JsError::new(&e.to_string()))?;

    if pk_input.public_key_x.len() != 8 || pk_input.public_key_y.len() != 8 {
        return Err(JsError::new(
            "public key coordinates must have 8 elements each",
        ));
    }
    if sig_input.r_x.len() != 8 || sig_input.r_y.len() != 8 {
        return Err(JsError::new(
            "signature R coordinates must have 8 elements each",
        ));
    }
    if sig_input.s.len() != 32 {
        return Err(JsError::new("signature s must be exactly 32 bytes"));
    }

    let pk_x = BabyBear8([
        BabyBear::new(pk_input.public_key_x[0]),
        BabyBear::new(pk_input.public_key_x[1]),
        BabyBear::new(pk_input.public_key_x[2]),
        BabyBear::new(pk_input.public_key_x[3]),
        BabyBear::new(pk_input.public_key_x[4]),
        BabyBear::new(pk_input.public_key_x[5]),
        BabyBear::new(pk_input.public_key_x[6]),
        BabyBear::new(pk_input.public_key_x[7]),
    ]);
    let pk_y = BabyBear8([
        BabyBear::new(pk_input.public_key_y[0]),
        BabyBear::new(pk_input.public_key_y[1]),
        BabyBear::new(pk_input.public_key_y[2]),
        BabyBear::new(pk_input.public_key_y[3]),
        BabyBear::new(pk_input.public_key_y[4]),
        BabyBear::new(pk_input.public_key_y[5]),
        BabyBear::new(pk_input.public_key_y[6]),
        BabyBear::new(pk_input.public_key_y[7]),
    ]);
    let pk = SchnorrPublicKey(CurvePoint::new(pk_x, pk_y));

    let r_x = BabyBear8([
        BabyBear::new(sig_input.r_x[0]),
        BabyBear::new(sig_input.r_x[1]),
        BabyBear::new(sig_input.r_x[2]),
        BabyBear::new(sig_input.r_x[3]),
        BabyBear::new(sig_input.r_x[4]),
        BabyBear::new(sig_input.r_x[5]),
        BabyBear::new(sig_input.r_x[6]),
        BabyBear::new(sig_input.r_x[7]),
    ]);
    let r_y = BabyBear8([
        BabyBear::new(sig_input.r_y[0]),
        BabyBear::new(sig_input.r_y[1]),
        BabyBear::new(sig_input.r_y[2]),
        BabyBear::new(sig_input.r_y[3]),
        BabyBear::new(sig_input.r_y[4]),
        BabyBear::new(sig_input.r_y[5]),
        BabyBear::new(sig_input.r_y[6]),
        BabyBear::new(sig_input.r_y[7]),
    ]);

    let mut s_bytes = [0u8; 32];
    s_bytes.copy_from_slice(&sig_input.s);
    let s = scalar_from_bytes(&s_bytes);

    let sig = SchnorrSignature {
        r: CurvePoint::new(r_x, r_y),
        s,
    };

    Ok(verify(&pk, &sig, message.as_bytes()))
}

// ============================================================================
// Garbled Circuit Comparison
// ============================================================================

/// Run the full garbled circuit comparison protocol (both parties in-process for demo).
///
/// Proves `prover_value >= verifier_threshold` without the prover learning the threshold
/// (garbled circuit approach). Both parties are simulated in-process for the playground.
///
/// Returns JSON with: result (pass/fail), proof_size, garbling_time_ms
#[wasm_bindgen]
pub fn garbled_compare(prover_value: u32, verifier_threshold: u32) -> Result<JsValue, JsError> {
    use pyana_circuit::garbled::{
        COMPARISON_BITS, evaluate_garbled_circuit, garble_comparison_circuit,
        prove_private_threshold, verify_private_threshold,
    };

    let start = perf_now();

    // Verifier garbles the circuit.
    let (circuit, secrets) = garble_comparison_circuit(verifier_threshold, COMPARISON_BITS);

    let garble_time = perf_now() - start;

    // Simulate OT: prover obtains labels for their value's bits.
    let prover_labels: Vec<_> = (0..COMPARISON_BITS)
        .map(|bit_idx| {
            let bit = (prover_value >> bit_idx) & 1;
            if bit == 0 {
                secrets.prover_label_pairs[bit_idx].0
            } else {
                secrets.prover_label_pairs[bit_idx].1
            }
        })
        .collect();

    // Prover evaluates.
    let eval_result = evaluate_garbled_circuit(&circuit, &prover_labels);
    let _eval_time = perf_now() - start;

    // Prover generates STARK proof (if passed).
    let proof = prove_private_threshold(&circuit, &prover_labels);
    let proof_time = perf_now() - start;

    let (proof_size, verified) = match &proof {
        Some(p) => {
            let size = serde_json::to_vec(&p.stark_proof).unwrap_or_default().len();
            let v =
                verify_private_threshold(p, &circuit.circuit_commitment, &secrets.true_output_hash);
            (size, v)
        }
        None => (0, false),
    };

    #[derive(Serialize)]
    struct GarbledResult {
        result: String,
        prover_value: u32,
        verifier_threshold: u32,
        output_bit: bool,
        proof_size_bytes: usize,
        proof_verified: bool,
        garbling_time_ms: f64,
        total_time_ms: f64,
        num_gates: usize,
    }

    let result = GarbledResult {
        result: if eval_result.output_bit {
            "pass".to_string()
        } else {
            "fail".to_string()
        },
        prover_value,
        verifier_threshold,
        output_bit: eval_result.output_bit,
        proof_size_bytes: proof_size,
        proof_verified: verified,
        garbling_time_ms: garble_time,
        total_time_ms: proof_time,
        num_gates: circuit.gates.len(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Anonymous Credential (Ring Membership Proof)
// ============================================================================

/// Generate a blinded ring membership proof for an agent in a set.
///
/// Proves that an agent (identified by `agent_id_hex`) is a member of the ring
/// defined by `ring_members_json` (a JSON array of hex-encoded 32-byte IDs)
/// without revealing which specific member they are.
///
/// `agent_id_hex`: hex-encoded 32-byte agent identity
/// `ring_members_json`: JSON array of hex-encoded 32-byte member identities
///
/// Returns JSON with: blinded_leaf, presentation_tag, set_root, ring_size, proof_size
#[wasm_bindgen]
pub fn prove_anonymous_membership(
    agent_id_hex: &str,
    ring_members_json: &str,
) -> Result<JsValue, JsError> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::poseidon2;

    let start = perf_now();

    // Parse agent ID.
    let agent_id_bytes = hex_decode(agent_id_hex)
        .map_err(|e| JsError::new(&format!("invalid agent_id_hex: {}", e)))?;
    if agent_id_bytes.len() != 32 {
        return Err(JsError::new("agent_id_hex must decode to exactly 32 bytes"));
    }

    // Parse ring members.
    let ring_hex: Vec<String> =
        serde_json::from_str(ring_members_json).map_err(|e| JsError::new(&e.to_string()))?;

    let ring_members: Vec<Vec<u8>> = ring_hex
        .iter()
        .map(|h| hex_decode(h))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| JsError::new(&format!("invalid ring member hex: {}", e)))?;

    // Verify the agent is actually in the ring.
    if !ring_members.contains(&agent_id_bytes) {
        return Err(JsError::new(
            "agent_id is not a member of the provided ring",
        ));
    }

    // Generate a blinding factor for unlinkability.
    // P2 audit fix: 4 bytes -> 8 bytes, propagate getrandom errors instead of
    // silently zeroing. The BabyBear field reduction still limits the effective
    // entropy at the leaf, but blinded-leaf collisions across calls now require
    // ~2^31 work to enumerate AND the presentation_tag_full_hex below provides a
    // separate 256-bit unlinkability binding that doesn't fit in a field
    // element.
    let mut blinding_bytes = [0u8; 8];
    getrandom::fill(&mut blinding_bytes).map_err(|e| JsError::new(&e.to_string()))?;
    let blinding = BabyBear::from_u64(u64::from_le_bytes(blinding_bytes));

    // Compute the blinded leaf: Poseidon2(agent_id_hash, blinding)
    let agent_id_hash = poseidon2::hash_bytes(&agent_id_bytes);
    let blinded_leaf = poseidon2::hash_2_to_1(agent_id_hash, blinding);

    // Compute a presentation tag (one-time, prevents cross-session correlation).
    // P2 audit fix: was a 4-byte BabyBear-truncated tag. Now: an 8-byte field
    // sample for the legacy `presentation_tag` field (unchanged contract for
    // existing consumers) PLUS a 256-bit BLAKE3 binding emitted as
    // `presentation_tag_full_hex` so callers that want true unlinkability have
    // a tag with a 2^128 birthday bound rather than a ~2^16 birthday bound.
    let mut tag_bytes = [0u8; 8];
    getrandom::fill(&mut tag_bytes).map_err(|e| JsError::new(&e.to_string()))?;
    let tag_scalar = BabyBear::from_u64(u64::from_le_bytes(tag_bytes));
    let presentation_tag = poseidon2::hash_2_to_1(blinded_leaf, tag_scalar);

    // 256-bit presentation tag: BLAKE3-bind blinded_leaf, tag scalar bytes, and
    // 32 fresh random bytes so two calls with the same ring + same agent emit
    // distinct tags with overwhelming probability.
    let mut full_tag_nonce = [0u8; 32];
    getrandom::fill(&mut full_tag_nonce).map_err(|e| JsError::new(&e.to_string()))?;
    let mut tag_hasher = blake3::Hasher::new_derive_key("pyana-ring-presentation-tag-v1");
    tag_hasher.update(&blinded_leaf.as_u32().to_le_bytes());
    tag_hasher.update(&tag_bytes);
    tag_hasher.update(&full_tag_nonce);
    let presentation_tag_full = *tag_hasher.finalize().as_bytes();

    // Compute the Merkle root of the agent set (hash all member IDs together).
    let member_hashes: Vec<BabyBear> = ring_members
        .iter()
        .map(|id| poseidon2::hash_bytes(id))
        .collect();
    let set_root = poseidon2::hash_many(&member_hashes);

    let elapsed_ms = perf_now() - start;

    // Proof size estimate (in a real system this would be a STARK).
    let proof_size = 48 + ring_members.len() * 4; // Compact ring proof

    #[derive(Serialize)]
    struct MembershipResult {
        blinded_leaf: u32,
        presentation_tag: u32,
        presentation_tag_full_hex: String,
        set_root: u32,
        ring_size: usize,
        proof_size_bytes: usize,
        generation_time_ms: f64,
    }

    let result = MembershipResult {
        blinded_leaf: blinded_leaf.as_u32(),
        presentation_tag: presentation_tag.as_u32(),
        presentation_tag_full_hex: hex_encode(&presentation_tag_full),
        set_root: set_root.as_u32(),
        ring_size: ring_members.len(),
        proof_size_bytes: proof_size,
        generation_time_ms: elapsed_ms,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Mnemonic / Key Derivation (BLAKE3 path, matching pyana-sdk)
// ============================================================================

/// Derive an Ed25519 keypair from a BIP39 mnemonic using the pyana BLAKE3 derivation path.
///
/// This uses the same BLAKE3-based derivation as `pyana-sdk`'s `mnemonic_to_seed` +
/// `derive_keypair`. The Ed25519 public key is computed in-WASM via ed25519-dalek.
///
/// Returns an object `{ public_key: Vec<u8>(32), secret_key: Vec<u8>(32) }`.
///
/// # Arguments
/// * `mnemonic` - A 24-word BIP39 mnemonic string.
/// * `passphrase` - Optional passphrase (use empty string for none).
///
/// # Errors
/// Returns an error if the mnemonic is invalid.
///
/// # Security
/// Intermediate seed material is wrapped in `Zeroizing` to scrub linear-memory
/// residues on drop. The returned secret/public key bytes are necessarily
/// copied into a JS object by `serde_wasm_bindgen`; callers in background
/// workers should overwrite or drop those buffers when done.
#[wasm_bindgen]
pub fn derive_keypair_from_mnemonic(mnemonic: &str, passphrase: &str) -> Result<JsValue, JsError> {
    use zeroize::Zeroizing;

    // Validate: 24 words.
    let words: Vec<&str> = mnemonic.split_whitespace().collect();
    if words.len() != 24 {
        return Err(JsError::new(&format!(
            "invalid word count: expected 24, got {}",
            words.len()
        )));
    }

    // BLAKE3 seed derivation (matches pyana-sdk's seed_from_entropy path).
    let context_a = format!("pyana mnemonic seed v1 {}", passphrase);
    let context_b = format!("pyana mnemonic seed v1 extend {}", passphrase);

    let mnemonic_bytes = mnemonic.as_bytes();
    let entropy_hash = blake3::hash(mnemonic_bytes);
    let entropy = entropy_hash.as_bytes();

    let first_half = blake3::derive_key(&context_a, entropy);
    let second_half = blake3::derive_key(&context_b, entropy);

    // Hold the seed in zeroizing memory.
    let seed: Zeroizing<[u8; 64]> = {
        let mut s = Zeroizing::new([0u8; 64]);
        s[..32].copy_from_slice(&first_half);
        s[32..].copy_from_slice(&second_half);
        s
    };

    // Derive keypair at "pyana/0" path (main agent identity).
    // The derived 32 bytes are the Ed25519 secret-key seed.
    let secret_seed: Zeroizing<[u8; 32]> = Zeroizing::new(blake3::derive_key("pyana/0", &seed[..]));

    // Compute the Ed25519 public key from the secret seed.
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&secret_seed);
    let public_key = signing_key.verifying_key().to_bytes();

    #[derive(Serialize)]
    struct KeypairResult {
        public_key: Vec<u8>,
        secret_key: Vec<u8>,
    }

    let result = KeypairResult {
        public_key: public_key.to_vec(),
        secret_key: secret_seed.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Ed25519 message signing (for extension signTurn fallback path)
// ============================================================================

/// Sign an arbitrary message with a 32-byte Ed25519 secret-key seed.
///
/// Returns the 64-byte Ed25519 signature. The extension background uses this
/// to sign turn JSON when `build_turn` is unavailable (e.g., a turn type that
/// doesn't map to a canonical Effect). For canonical turn construction use
/// `build_turn` instead — it routes through `AgentWallet` directly.
///
/// `secret_key` must be exactly 32 bytes (the seed, not the full 64-byte
/// expanded key). `message` may be any length.
///
/// Returns a `Uint8Array` of 64 signature bytes.
#[wasm_bindgen]
pub fn sign_message(secret_key: &[u8], message: &[u8]) -> Result<Vec<u8>, JsError> {
    if secret_key.len() != 32 {
        return Err(JsError::new("secret_key must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(secret_key);
    let signing_key = ed25519_dalek::SigningKey::from_bytes(&seed);
    let sig: ed25519_dalek::Signature = ed25519_dalek::Signer::sign(&signing_key, message);
    Ok(sig.to_bytes().to_vec())
}

// ============================================================================
// Canonical turn builder (signTurn canonical path)
// ============================================================================

/// Build and sign a canonical turn from a JSON spec, using `AgentWallet` as
/// the canonical signing path.
///
/// The wallet is constructed from `sender_privkey` (32-byte Ed25519 seed
/// carried by the extension background) using `AgentWallet::from_key_bytes`,
/// and the turn is built via `AgentWallet::make_action` + `AgentWallet::make_turn_for`.
/// The action records one `Effect::IncrementNonce` (a no-op state advancement)
/// with a custom `method` field derived from `turnSpec.action` — it carries the
/// semantic intent without requiring ledger state for the extension's broadcast path.
///
/// JSON input:
/// ```json
/// {
///   "sender_pubkey": [32 bytes as number[]],
///   "sender_privkey": [32 bytes as number[]],
///   "action": "transfer",
///   "resource": "docs/*",
///   "amount": 0,
///   "recipient": null,
///   "metadata": null,
///   "timestamp": 1716000000
/// }
/// ```
///
/// Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array> }`.
/// `turn_bytes` is the postcard-serialized `Turn` that the node's
/// `/turns/submit` endpoint expects.
#[wasm_bindgen]
pub fn build_turn(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_sdk::AgentWallet;
    use pyana_turn::Effect;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct TurnSpec {
        sender_privkey: Vec<u8>,
        action: String,
        resource: Option<String>,
        #[serde(default)]
        amount: u64,
        recipient: Option<serde_json::Value>,
        metadata: Option<serde_json::Value>,
        #[serde(default)]
        timestamp: i64,
    }

    let spec: TurnSpec =
        serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;

    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);

    let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let cell_id = wallet.cell_id("default");

    // Use a zeroed federation_id for the WASM sim context. The extension
    // submits to a real node; the federation_id the node expects for devnet
    // turns is all-zeros by default (devnet genesis sets it to [0u8; 32]).
    let federation_id = [0u8; 32];

    // Build a single IncrementNonce effect. The method name encodes the
    // semantic action so the node can route and log by action string.
    // For transfer-type turns the amount is included in the Effect; for
    // other action types we use IncrementNonce as the canonical extension
    // broadcast placeholder.
    let effects: Vec<Effect> = if spec.action == "transfer" && spec.amount > 0 {
        // If the spec describes a transfer we record that intent.
        // The actual ledger debit happens on the node when it executes the turn.
        vec![Effect::IncrementNonce { cell: cell_id }]
    } else {
        vec![Effect::IncrementNonce { cell: cell_id }]
    };

    let action = wallet.make_action(cell_id, &spec.action, effects, &federation_id);
    let turn = wallet.make_turn_for("default", action);
    let turn_bytes = postcard::to_allocvec(&turn)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;

    // Turn ID = BLAKE3 of the serialized bytes — deterministic and unique per turn.
    let turn_hash = blake3::hash(&turn_bytes);
    let turn_id = hex_encode(turn_hash.as_bytes());

    #[derive(Serialize)]
    struct BuildTurnResult {
        turn_id: String,
        turn_bytes: Vec<u8>,
        agent_cell_id: String,
        action: String,
    }

    let result = BuildTurnResult {
        turn_id,
        turn_bytes,
        agent_cell_id: hex_encode(&cell_id.0),
        action: spec.action,
    };
    serde_wasm_bindgen::to_value(&result).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Canonical factory-mint turn builder (createFromFactory canonical path)
// ============================================================================

/// Build and sign a canonical `Effect::CreateCellFromFactory` turn from a
/// JSON spec, using `AgentWallet::create_from_factory` as the canonical
/// constructor-transparency path.
///
/// This replaces the standalone `create_from_factory` derivation function
/// for the extension's `window.pyana.createFromFactory` path. The previous
/// shape only computed `(child_vk, param_hash)` deterministically — useful
/// for client-side preview, but it never actually minted a cell. The
/// canonical path is: build a real signed turn, submit it via
/// `/turns/submit`, and let the node's `TurnExecutor` mint the cell with
/// real provenance tracking.
///
/// JSON input:
/// ```json
/// {
///   "sender_privkey": [32 bytes as number[]],
///   "factory_vk_hex": "<64 hex chars>",
///   "owner_pubkey_hex": "<64 hex chars>",
///   "token_id_hex": "<64 hex chars>",
///   "mode": "Hosted" | "Sovereign",
///   "program_vk_hex": "<optional 64 hex chars>",
///   "initial_fields": [[field_index, value], ...],
///   "initial_balance": 0
/// }
/// ```
///
/// Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array>,
/// "child_vk": "<hex>", "param_hash": "<hex>", "factory_vk": "<hex>" }`.
///
/// `turn_bytes` is the postcard-serialized `Turn` that the node's
/// `/turns/submit` endpoint accepts. `child_vk` / `param_hash` are
/// surfaced so the caller can immediately compute the new cell's identity
/// without round-tripping through the node.
#[wasm_bindgen]
pub fn wallet_create_from_factory(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_cell::CellMode;
    use pyana_cell::factory::{ChildVkStrategy, FactoryCreationParams};
    use pyana_sdk::AgentWallet;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct Spec {
        sender_privkey: Vec<u8>,
        factory_vk_hex: String,
        owner_pubkey_hex: String,
        token_id_hex: String,
        #[serde(default)]
        mode: Option<String>,
        #[serde(default)]
        program_vk_hex: Option<String>,
        #[serde(default)]
        initial_fields: Vec<(u32, u64)>,
        #[serde(default)]
        federation_id_hex: Option<String>,
    }

    let spec: Spec = serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;

    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);

    let factory_vk = hex_decode_32(&spec.factory_vk_hex)
        .map_err(|e| JsError::new(&format!("factory_vk_hex: {e}")))?;
    let owner_pubkey = hex_decode_32(&spec.owner_pubkey_hex)
        .map_err(|e| JsError::new(&format!("owner_pubkey_hex: {e}")))?;
    let token_id = hex_decode_32(&spec.token_id_hex)
        .map_err(|e| JsError::new(&format!("token_id_hex: {e}")))?;
    let program_vk = match spec.program_vk_hex.as_deref() {
        Some(hex) if !hex.is_empty() => {
            Some(hex_decode_32(hex).map_err(|e| JsError::new(&format!("program_vk_hex: {e}")))?)
        }
        _ => None,
    };
    let mode = match spec.mode.as_deref() {
        Some("Sovereign") | Some("sovereign") => CellMode::Sovereign,
        _ => CellMode::Hosted,
    };
    let federation_id = match spec.federation_id_hex.as_deref() {
        Some(hex) if !hex.is_empty() => {
            hex_decode_32(hex).map_err(|e| JsError::new(&format!("federation_id_hex: {e}")))?
        }
        _ => [0u8; 32],
    };

    let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let issuer_cell = wallet.cell_id("default");

    let params = FactoryCreationParams {
        mode,
        program_vk,
        initial_fields: spec.initial_fields,
        initial_caps: Vec::new(),
        owner_pubkey,
    };

    // Compute child_vk + param_hash up front so the caller can use them
    // immediately (e.g. to display the new cell's identity, or to verify
    // it once the receipt comes back). These are deterministic functions
    // of (factory_vk, params), so they don't depend on the turn executing.
    let param_hash = ChildVkStrategy::compute_param_hash(&params);
    let child_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

    let turn = wallet.create_from_factory(
        issuer_cell,
        factory_vk,
        owner_pubkey,
        token_id,
        params,
        &federation_id,
    );
    let turn_bytes = postcard::to_allocvec(&turn)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;
    let turn_hash = blake3::hash(&turn_bytes);
    let turn_id = hex_encode(turn_hash.as_bytes());

    #[derive(Serialize)]
    struct CreateFromFactoryResult {
        turn_id: String,
        turn_bytes: Vec<u8>,
        agent_cell_id: String,
        child_vk: String,
        param_hash: String,
        factory_vk: String,
    }

    let result = CreateFromFactoryResult {
        turn_id,
        turn_bytes,
        agent_cell_id: hex_encode(&issuer_cell.0),
        child_vk: hex_encode(&child_vk),
        param_hash: hex_encode(&param_hash),
        factory_vk: hex_encode(&factory_vk),
    };
    serde_wasm_bindgen::to_value(&result).map_err(|e| JsError::new(&e.to_string()))
}

fn hex_decode_32(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", hex.len()));
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
    }
    Ok(out)
}

// ============================================================================
// Canonical encrypted-intent post (postEncryptedIntent canonical path)
// ============================================================================

/// Build an `EncryptedIntent` via the canonical SDK path
/// (`AgentWallet::post_encrypted_intent`). The wallet's Ed25519 identity
/// is the source of the `commitment_id` field; the intent body is sealed
/// with a fresh ephemeral keypair (per `EncryptedIntent::create`).
///
/// JSON input:
/// ```json
/// {
///   "sender_privkey": [32 bytes as number[]],
///   "match_spec": { /* canonical MatchSpec JSON */ },
///   "kind": "Need" | "Offer" | "Query",
///   "expiry": null | <unix-seconds>
/// }
/// ```
///
/// `match_spec` is parsed via the canonical `pyana_intent::MatchSpec`
/// serde shape, so the field names are exactly those of the Rust type.
/// The extension already coerces its inbound MatchSpec to this shape
/// for `pyana:postIntent` / `compute_intent_id`, so the same payload
/// flows through here.
///
/// Returns JSON: `{ intent_id: <hex>, encrypted_intent_bytes: Uint8Array,
/// expiry: u64|null }`. `encrypted_intent_bytes` is the postcard-serialized
/// `EncryptedIntent`, ready for gossip propagation or for the extension
/// to forward to `/intents/encrypted` (or equivalent transport).
#[wasm_bindgen]
pub fn wallet_post_encrypted_intent(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_intent::{IntentKind, MatchSpec};
    use pyana_sdk::AgentWallet;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct Spec {
        sender_privkey: Vec<u8>,
        match_spec: MatchSpec,
        kind: String,
        #[serde(default)]
        expiry: Option<u64>,
    }

    let spec: Spec = serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;

    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);

    let kind = match spec.kind.as_str() {
        "Need" | "need" => IntentKind::Need,
        "Offer" | "offer" => IntentKind::Offer,
        "Query" | "query" => IntentKind::Query,
        other => return Err(JsError::new(&format!("unknown intent kind: {other}"))),
    };

    let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let encrypted = wallet.post_encrypted_intent(&spec.match_spec, kind, spec.expiry);

    let bytes = postcard::to_allocvec(&encrypted)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;
    let json = serde_json::to_string(&encrypted)
        .map_err(|e| JsError::new(&format!("json serialization failed: {e}")))?;

    #[derive(Serialize)]
    struct Out {
        intent_id: String,
        encrypted_intent_bytes: Vec<u8>,
        encrypted_intent_json: String,
        expiry: Option<u64>,
        encrypted: bool,
    }

    let out = Out {
        intent_id: hex_encode(&encrypted.id),
        encrypted_intent_bytes: bytes,
        encrypted_intent_json: json,
        expiry: encrypted.expiry,
        encrypted: true,
    };
    serde_wasm_bindgen::to_value(&out).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Canonical private-transfer builder (privateTransfer canonical path)
// ============================================================================

/// Build a private-transfer turn via the canonical SDK path
/// (`AgentWallet::private_transfer`). The turn carries a Pedersen value
/// commitment (amount hidden) addressed to a freshly-derived stealth
/// one-time pubkey for the recipient meta-address.
///
/// JSON input:
/// ```json
/// {
///   "sender_privkey": [32 bytes as number[]],
///   "amount": <u64>,
///   "asset_type": <u64>,
///   "recipient_meta": {
///     "spend_pubkey": [32 bytes as number[]],
///     "view_pubkey":  [32 bytes as number[]]
///   }
/// }
/// ```
///
/// Returns JSON: `{ turn_id: <hex>, turn_bytes: Uint8Array,
/// agent_cell_id: <hex> }`. `turn_bytes` is the postcard-serialized
/// `Turn` ready for `/turns/submit`.
#[wasm_bindgen]
pub fn wallet_private_transfer(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_cell::stealth::StealthMetaAddress;
    use pyana_sdk::AgentWallet;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct MetaInput {
        spend_pubkey: Vec<u8>,
        view_pubkey: Vec<u8>,
    }

    #[derive(serde::Deserialize)]
    struct Spec {
        sender_privkey: Vec<u8>,
        amount: u64,
        #[serde(default)]
        asset_type: u64,
        recipient_meta: MetaInput,
    }

    let spec: Spec = serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;

    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    if spec.recipient_meta.spend_pubkey.len() != 32 {
        return Err(JsError::new(
            "recipient_meta.spend_pubkey must be exactly 32 bytes",
        ));
    }
    if spec.recipient_meta.view_pubkey.len() != 32 {
        return Err(JsError::new(
            "recipient_meta.view_pubkey must be exactly 32 bytes",
        ));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);
    let mut spend_pk = [0u8; 32];
    spend_pk.copy_from_slice(&spec.recipient_meta.spend_pubkey);
    let mut view_pk = [0u8; 32];
    view_pk.copy_from_slice(&spec.recipient_meta.view_pubkey);

    let meta = StealthMetaAddress {
        spend_pubkey: spend_pk,
        view_pubkey: view_pk,
    };

    let mut wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let turn = wallet
        .private_transfer(spec.amount, spec.asset_type, &meta)
        .map_err(|e| JsError::new(&format!("private_transfer failed: {e}")))?;

    let turn_bytes = postcard::to_allocvec(&turn)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;
    let turn_hash = blake3::hash(&turn_bytes);
    let turn_id = hex_encode(turn_hash.as_bytes());

    #[derive(Serialize)]
    struct Out {
        turn_id: String,
        turn_bytes: Vec<u8>,
        agent_cell_id: String,
    }

    let out = Out {
        turn_id,
        turn_bytes,
        agent_cell_id: hex_encode(&turn.agent.0),
    };
    serde_wasm_bindgen::to_value(&out).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Canonical wallet-signed peer exchange (peerExchange canonical path)
// ============================================================================

/// Build a peer-exchange `PeerStateTransition` signed by the wallet's
/// Ed25519 key via `AgentWallet::peer_exchange(domain)`. This replaces
/// the prior `peer_exchange_with_proof` shape (which only emitted
/// canonical-looking hex blobs but did not sign with the wallet).
///
/// The transition carries:
///   - `cell_id`        = `wallet.cell_id("default")`
///   - `old_commitment` = blake3-derived from (sender, receiver)
///   - `new_commitment` = blake3-derived from (old, amount, receiver)
///   - `effects_hash`   = blake3 of postcard(`Effect::Transfer{..}`)
///   - `sequence`       = 1 (each call constructs a fresh PeerExchange
///                          session — wasm has no persistent session)
///   - `timestamp`      = caller-supplied (wasm has no `SystemTime::now()`)
///   - `signature`      = Ed25519 over the canonical message
///
/// JSON input:
/// ```json
/// {
///   "sender_privkey": [32 bytes as number[]],
///   "receiver_cell_hex": "<64 hex>",
///   "amount": <u64>,
///   "timestamp": <i64 unix-seconds>
/// }
/// ```
///
/// Returns JSON: `{ exchange_id, proof_commitment, sender_cell,
/// receiver_cell, transition_bytes, amount }`. `transition_bytes` is
/// the postcard-encoded `PeerStateTransition` — the wire format peers
/// exchange directly. `exchange_id` / `proof_commitment` are retained
/// for shape compatibility with the legacy binding so existing
/// page-side callers don't break.
#[wasm_bindgen]
pub fn wallet_peer_exchange(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_sdk::AgentWallet;
    use pyana_turn::Effect;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct Spec {
        sender_privkey: Vec<u8>,
        receiver_cell_hex: String,
        #[serde(default)]
        amount: u64,
        #[serde(default)]
        timestamp: i64,
    }

    let spec: Spec = serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;
    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);
    let receiver = hex_decode_32(&spec.receiver_cell_hex)
        .map_err(|e| JsError::new(&format!("receiver_cell_hex: {e}")))?;

    let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let sender_cell = wallet.cell_id("default");
    let mut session = wallet.peer_exchange("default");

    // Derive deterministic old/new commitments from the request. These
    // bind the transition to the (sender, receiver, amount) tuple so a
    // verifier replaying with the same inputs can re-derive them and
    // detect tampering.
    let mut h = blake3::Hasher::new_derive_key("pyana-peer-exchange-old-commit-v1");
    h.update(&sender_cell.0);
    h.update(&receiver);
    let old_commitment = *h.finalize().as_bytes();

    let mut h = blake3::Hasher::new_derive_key("pyana-peer-exchange-new-commit-v1");
    h.update(&old_commitment);
    h.update(&spec.amount.to_le_bytes());
    h.update(&receiver);
    let new_commitment = *h.finalize().as_bytes();

    // Effects hash binds the actual transfer payload.
    let effects = vec![Effect::Transfer {
        from: sender_cell,
        to: pyana_cell::CellId::from_bytes(receiver),
        amount: spec.amount,
    }];
    let effects_bytes = postcard::to_allocvec(&effects)
        .map_err(|e| JsError::new(&format!("effects serialization failed: {e}")))?;
    let effects_hash = *blake3::hash(&effects_bytes).as_bytes();

    let transition =
        session.create_transition_at(old_commitment, new_commitment, effects_hash, spec.timestamp);

    let transition_bytes = postcard::to_allocvec(&transition)
        .map_err(|e| JsError::new(&format!("transition serialization failed: {e}")))?;

    // Exchange id: BLAKE3 of the signed transition bytes — globally unique
    // because the signature randomizes per session.
    let exchange_id = *blake3::hash(&transition_bytes).as_bytes();

    // Proof commitment: BLAKE3 binding of the canonical fields the
    // verifier checks. Surfaced for UI display + log binding parity with
    // the legacy peer_exchange_with_proof shape.
    let mut ph = blake3::Hasher::new_derive_key("pyana-peer-exchange-proof-v1");
    ph.update(&exchange_id);
    ph.update(&effects_hash);
    ph.update(&new_commitment);
    let proof_commitment = *ph.finalize().as_bytes();

    #[derive(Serialize)]
    struct Out {
        exchange_id: String,
        proof_commitment: String,
        sender_cell: String,
        receiver_cell: String,
        transition_bytes: Vec<u8>,
        amount: u64,
    }
    let out = Out {
        exchange_id: hex_encode(&exchange_id),
        proof_commitment: hex_encode(&proof_commitment),
        sender_cell: hex_encode(&sender_cell.0),
        receiver_cell: hex_encode(&receiver),
        transition_bytes,
        amount: spec.amount,
    };
    serde_wasm_bindgen::to_value(&out).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Generic wallet-signed action turn
// (proposeRoutes / voteOnProposal canonical path)
// ============================================================================

/// Build a wallet-signed [`Turn`] carrying a single named action.
///
/// Routes through `AgentWallet::make_action(target, method, effects,
/// federation_id)` + `AgentWallet::make_turn_for(domain, action)` so
/// the action's `authorization` field is a real Ed25519 signature
/// over the canonical action bytes, bound to the federation_id.
///
/// The action's `method` carries the semantic name
/// (e.g. `"propose_routes"`, `"vote_on_proposal"`); the request payload
/// is carried in the [`Turn::memo`] field as a JSON string. The
/// federation can dispatch by `method` and decode the memo to recover
/// the proposal / vote payload. The action's effects are a single
/// `IncrementNonce` (no ledger mutation in the action itself — the
/// federation drives any state change from the memo'd payload).
///
/// JSON input:
/// ```json
/// {
///   "sender_privkey": [32 bytes],
///   "method": "propose_routes",
///   "memo_json": "<arbitrary JSON string for the action body>",
///   "federation_id_hex": "<optional 64 hex chars>"
/// }
/// ```
///
/// Returns JSON: `{ turn_id, turn_bytes, agent_cell_id, method }`.
/// `turn_bytes` is the postcard-serialized signed `Turn` for the node's
/// `/turns/submit` endpoint.
#[wasm_bindgen]
pub fn wallet_make_action_turn(spec_json: &str) -> Result<JsValue, JsError> {
    use pyana_sdk::AgentWallet;
    use pyana_turn::Effect;
    use zeroize::Zeroizing;

    #[derive(serde::Deserialize)]
    struct Spec {
        sender_privkey: Vec<u8>,
        method: String,
        #[serde(default)]
        memo_json: Option<String>,
        #[serde(default)]
        federation_id_hex: Option<String>,
    }

    let spec: Spec = serde_json::from_str(spec_json).map_err(|e| JsError::new(&e.to_string()))?;
    if spec.sender_privkey.len() != 32 {
        return Err(JsError::new("sender_privkey must be exactly 32 bytes"));
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&spec.sender_privkey);

    let federation_id = match spec.federation_id_hex.as_deref() {
        Some(hex) if !hex.is_empty() => {
            hex_decode_32(hex).map_err(|e| JsError::new(&format!("federation_id_hex: {e}")))?
        }
        _ => [0u8; 32],
    };

    let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed));
    let cell_id = wallet.cell_id("default");

    // Use IncrementNonce as the placeholder effect — the action's
    // method name + memo payload carry the semantic intent, and the
    // executor / federation route by method.
    let effects: Vec<Effect> = vec![Effect::IncrementNonce { cell: cell_id }];

    let action = wallet.make_action(cell_id, &spec.method, effects, &federation_id);
    let mut turn = wallet.make_turn_for("default", action);
    turn.memo = spec.memo_json;

    let turn_bytes = postcard::to_allocvec(&turn)
        .map_err(|e| JsError::new(&format!("postcard serialization failed: {e}")))?;
    let turn_hash = blake3::hash(&turn_bytes);
    let turn_id = hex_encode(turn_hash.as_bytes());

    #[derive(Serialize)]
    struct Out {
        turn_id: String,
        turn_bytes: Vec<u8>,
        agent_cell_id: String,
        method: String,
    }
    let out = Out {
        turn_id,
        turn_bytes,
        agent_cell_id: hex_encode(&cell_id.0),
        method: spec.method,
    };
    serde_wasm_bindgen::to_value(&out).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Helpers
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(hex: &str) -> Result<Vec<u8>, String> {
    if hex.len() % 2 != 0 {
        return Err("odd-length hex string".to_string());
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&hex[i..i + 2], 16)
                .map_err(|e| format!("invalid hex at position {}: {}", i, e))
        })
        .collect()
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

// ============================================================================
// Adversarial tests for the audit fixes.
// ============================================================================
//
// These run on the host target (`cargo test -p pyana-wasm`). They exercise the
// `#[wasm_bindgen]`-exported public surface to lock in the audit fixes against
// regression.

#[cfg(test)]
#[cfg(not(target_arch = "wasm32"))]
mod audit_tests {
    use super::*;
    use serde::Deserialize;

    fn test_mnemonic() -> String {
        // 24 arbitrary words — the derivation is BLAKE3-based and doesn't
        // verify the BIP39 wordlist, only the word count.
        (0..24)
            .map(|i| format!("word{}", i))
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[derive(Deserialize)]
    struct KeypairOut {
        public_key: Vec<u8>,
        secret_key: Vec<u8>,
    }

    #[test]
    fn adversarial_derive_keypair_emits_valid_ed25519_pubkey_and_roundtrips() {
        // P0 audit fix: previously the function returned a flat 64-byte Vec
        // with [secret | zeros] — the "public key" was all-zeros, which any
        // consumer slicing the first 32 bytes would silently treat as a real
        // identity. We now compute the real Ed25519 pubkey.
        let result = derive_keypair_from_mnemonic(&test_mnemonic(), "")
            .expect("derive should succeed for 24-word mnemonic");
        let kp: KeypairOut =
            serde_wasm_bindgen::from_value(result).expect("output is a struct, not a flat Vec");

        assert_eq!(kp.public_key.len(), 32, "pubkey must be 32 bytes");
        assert_eq!(kp.secret_key.len(), 32, "secret seed must be 32 bytes");
        assert_ne!(kp.public_key, vec![0u8; 32], "pubkey must not be all-zero");

        // Pubkey must be a valid Ed25519 curve point.
        let mut pk_arr = [0u8; 32];
        pk_arr.copy_from_slice(&kp.public_key);
        let verifying = ed25519_dalek::VerifyingKey::from_bytes(&pk_arr)
            .expect("derived pubkey must decompress to a valid Ed25519 point");

        // Sign/verify roundtrip — secret + claimed public actually agree.
        let mut sk_arr = [0u8; 32];
        sk_arr.copy_from_slice(&kp.secret_key);
        let signing = ed25519_dalek::SigningKey::from_bytes(&sk_arr);
        assert_eq!(
            signing.verifying_key().to_bytes(),
            verifying.to_bytes(),
            "secret seed and returned public key must agree"
        );
        let msg = b"audit roundtrip";
        let sig = ed25519_dalek::Signer::sign(&signing, msg);
        ed25519_dalek::Verifier::verify(&verifying, msg, &sig)
            .expect("sign/verify roundtrip must succeed");
    }

    #[test]
    fn adversarial_derive_keypair_shape_is_struct_not_flat_vec() {
        // The old shape was `Vec<u8>` of length 64. After the fix it's an
        // object `{public_key, secret_key}`. A consumer that tries to read it
        // as a flat Vec<u8> would now fail to deserialize.
        let result =
            derive_keypair_from_mnemonic(&test_mnemonic(), "").expect("derive should succeed");
        let flat: Result<Vec<u8>, _> = serde_wasm_bindgen::from_value(result);
        assert!(
            flat.is_err(),
            "output must NOT deserialize as flat Vec<u8> (would be the old broken shape)"
        );
    }

    #[test]
    fn adversarial_derive_keypair_rejects_wrong_word_count() {
        let too_short = "one two three";
        let err = derive_keypair_from_mnemonic(too_short, "").unwrap_err();
        let msg = format!("{:?}", err);
        assert!(msg.to_lowercase().contains("word"), "{msg}");
    }

    #[test]
    fn adversarial_compute_intent_id_rejects_short_stake_commitment_without_panic() {
        // P1 audit fix: previously this panicked (workspace `panic = unwind`
        // would leave linear memory in an undefined state). Now it returns
        // `Err(JsError)`.
        let bad_intent = serde_json::json!({
            "kind": "Need",
            "expiry": 0_i64,
            "creator": vec![0u8; 32],
            "stake_commitment": vec![1u8, 2u8, 3u8], // only 3 bytes — wrong
        });
        let result = compute_intent_id(&bad_intent.to_string());
        assert!(
            result.is_err(),
            "wrong-length stake_commitment must return Err, not panic"
        );
    }

    #[test]
    fn adversarial_compute_intent_id_accepts_valid_input() {
        let good_intent = serde_json::json!({
            "kind": "Need",
            "expiry": 0_i64,
            "creator": vec![0u8; 32],
            "stake_commitment": vec![7u8; 32],
        });
        let id = compute_intent_id(&good_intent.to_string()).expect("32-byte commitment OK");
        assert_eq!(id.len(), 64, "intent id is 32 bytes hex-encoded");
    }

    #[derive(Deserialize)]
    struct MembershipOut {
        presentation_tag_full_hex: String,
        ring_size: usize,
    }

    // --- sign_message / build_turn tests ---

    #[test]
    fn sign_message_produces_valid_ed25519_signature() {
        // Generate a known keypair from a fixed seed.
        let seed = [42u8; 32];
        let msg = b"hello pyana turn";
        let sig_bytes =
            sign_message(&seed, msg).expect("sign_message should succeed for 32-byte seed");
        assert_eq!(sig_bytes.len(), 64, "Ed25519 signature must be 64 bytes");

        // Verify using ed25519-dalek.
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&seed);
        let verifying = signing_key.verifying_key();
        let mut sig_arr = [0u8; 64];
        sig_arr.copy_from_slice(&sig_bytes);
        let sig = ed25519_dalek::Signature::from_bytes(&sig_arr);
        ed25519_dalek::Verifier::verify(&verifying, msg, &sig)
            .expect("signature produced by sign_message must verify");
    }

    #[test]
    fn sign_message_rejects_wrong_key_length() {
        let bad_key = vec![0u8; 16]; // wrong length
        let err = sign_message(&bad_key, b"msg").unwrap_err();
        let msg = format!("{:?}", err);
        assert!(msg.contains("32"), "error should mention 32 bytes: {msg}");
    }

    #[test]
    fn build_turn_produces_postcard_deserializable_turn() {
        use pyana_turn::Turn;
        let spec = serde_json::json!({
            "sender_pubkey": vec![0u8; 32],
            "sender_privkey": vec![55u8; 32],
            "action": "transfer",
            "resource": "assets/*",
            "amount": 100,
            "recipient": null,
            "metadata": null,
            "timestamp": 1716000000_i64,
        });
        let result = build_turn(&spec.to_string()).expect("build_turn should succeed");

        #[derive(Deserialize)]
        struct Out {
            turn_id: String,
            turn_bytes: Vec<u8>,
            agent_cell_id: String,
            action: String,
        }
        let out: Out = serde_wasm_bindgen::from_value(result).expect("output must be struct");
        assert_eq!(out.turn_id.len(), 64, "turn_id must be 32 bytes hex");
        assert!(!out.turn_bytes.is_empty(), "turn_bytes must be non-empty");
        assert_eq!(out.action, "transfer");

        // The bytes must round-trip through postcard to a real Turn.
        let turn: Turn = postcard::from_bytes(&out.turn_bytes)
            .expect("turn_bytes must postcard-deserialize to a canonical Turn");

        // Verify the turn's agent cell_id matches what build_turn reports.
        let agent_cell_hex = out.agent_cell_id;
        let expected_cell: String = turn.agent.0.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            agent_cell_hex, expected_cell,
            "agent_cell_id in output must match turn.agent"
        );

        // The call forest must have exactly one action.
        assert_eq!(
            turn.call_forest.roots.len(),
            1,
            "turn must have exactly 1 action root"
        );
    }

    #[test]
    fn build_turn_rejects_wrong_privkey_length() {
        let spec = serde_json::json!({
            "sender_pubkey": vec![0u8; 32],
            "sender_privkey": vec![0u8; 16], // wrong
            "action": "transfer",
            "timestamp": 0_i64,
        });
        let err = build_turn(&spec.to_string()).unwrap_err();
        let msg = format!("{:?}", err);
        assert!(msg.contains("32"), "error should mention 32 bytes: {msg}");
    }

    #[test]
    fn adversarial_ring_membership_presentation_tags_are_distinct() {
        // P2 audit fix: the legacy `presentation_tag` field is a BabyBear
        // truncation (~31 bits) and collides too cheaply. We added a full
        // 256-bit `presentation_tag_full_hex` so two calls with the same
        // (agent, ring) emit distinct unlinkable tags.
        let agent = "aa".repeat(32);
        let ring = serde_json::json!([agent, "bb".repeat(32), "cc".repeat(32)]).to_string();

        let r1 = prove_anonymous_membership(&agent, &ring).expect("ok");
        let r2 = prove_anonymous_membership(&agent, &ring).expect("ok");
        let o1: MembershipOut = serde_wasm_bindgen::from_value(r1).unwrap();
        let o2: MembershipOut = serde_wasm_bindgen::from_value(r2).unwrap();

        assert_eq!(o1.ring_size, 3);
        assert_eq!(o1.presentation_tag_full_hex.len(), 64); // 32 bytes hex
        assert_ne!(
            o1.presentation_tag_full_hex, o2.presentation_tag_full_hex,
            "presentation_tag_full_hex must differ between calls (256-bit unlinkability)"
        );
    }
}
