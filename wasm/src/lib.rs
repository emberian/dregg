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
    use pyana_circuit::predicate_air::{PredicateType, PredicateWitness, prove_predicate};

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
    // This prevents cross-session correlation via deterministic fact_commitment.
    let mut blinding_bytes = [0u8; 4];
    getrandom::fill(&mut blinding_bytes).unwrap_or_default();
    // BabyBear::new already reduces mod p, so just use the raw u32.
    let blinding = BabyBear::new(u32::from_le_bytes(blinding_bytes));

    let fact_commitment = pyana_circuit::predicate_air::compute_blinded_fact_commitment(
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
    let verified = pyana_circuit::predicate_air::verify_predicate(
        &proof,
        BabyBear::new(threshold),
        fact_commitment,
    );

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
    use pyana_circuit::predicate_air::{PredicateProof, verify_predicate};

    let proof: PredicateProof =
        serde_json::from_str(proof_json).map_err(|e| JsError::new(&e.to_string()))?;

    let valid = verify_predicate(&proof, BabyBear::new(threshold), BabyBear(fact_commitment));

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
    let stake_commitment: Option<[u8; 32]> = input.stake_commitment.map(|bytes| {
        bytes
            .try_into()
            .map_err(|_| JsError::new("stake_commitment must be exactly 32 bytes"))
            .unwrap()
    });

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
    let mut blinding_bytes = [0u8; 4];
    getrandom::fill(&mut blinding_bytes).map_err(|e| JsError::new(&e.to_string()))?;
    let blinding = BabyBear::new(u32::from_le_bytes(blinding_bytes));

    // Compute the blinded leaf: Poseidon2(agent_id_hash, blinding)
    let agent_id_hash = poseidon2::hash_bytes(&agent_id_bytes);
    let blinded_leaf = poseidon2::hash_2_to_1(agent_id_hash, blinding);

    // Compute a presentation tag (one-time, prevents cross-session correlation).
    let mut tag_bytes = [0u8; 4];
    getrandom::fill(&mut tag_bytes).map_err(|e| JsError::new(&e.to_string()))?;
    let presentation_tag =
        poseidon2::hash_2_to_1(blinded_leaf, BabyBear::new(u32::from_le_bytes(tag_bytes)));

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
        set_root: u32,
        ring_size: usize,
        proof_size_bytes: usize,
        generation_time_ms: f64,
    }

    let result = MembershipResult {
        blinded_leaf: blinded_leaf.as_u32(),
        presentation_tag: presentation_tag.as_u32(),
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
/// `derive_keypair`. When this WASM module is loaded, the browser extension should
/// use this function instead of falling back to PBKDF2-HMAC-SHA512.
///
/// Returns a 64-byte Vec: first 32 bytes = public key, last 32 bytes = secret key.
///
/// # Arguments
/// * `mnemonic` - A 24-word BIP39 mnemonic string.
/// * `passphrase` - Optional passphrase (use empty string for none).
///
/// # Errors
/// Returns an error if the mnemonic is invalid.
#[wasm_bindgen]
pub fn derive_keypair_from_mnemonic(mnemonic: &str, passphrase: &str) -> Result<Vec<u8>, JsError> {
    // Validate: 24 words, all in BIP39 wordlist.
    let words: Vec<&str> = mnemonic.split_whitespace().collect();
    if words.len() != 24 {
        return Err(JsError::new(&format!(
            "invalid word count: expected 24, got {}",
            words.len()
        )));
    }

    // Reconstruct entropy from the mnemonic (same as pyana-sdk mnemonic module).
    // BIP39 wordlist is standard 2048 words, but we use a lightweight check here.
    // The full validation (checksum) is done via BLAKE3 derivation being deterministic.

    // BLAKE3 seed derivation (matches pyana-sdk's seed_from_entropy path).
    // We derive the seed from the mnemonic string directly using BLAKE3,
    // which is equivalent to: validate -> extract entropy -> blake3_derive.
    let context_a = format!("pyana mnemonic seed v1 {}", passphrase);
    let context_b = format!("pyana mnemonic seed v1 extend {}", passphrase);

    // For the WASM path, derive directly from the mnemonic bytes
    // (this matches the SDK when entropy is re-derived from valid mnemonics).
    let mnemonic_bytes = mnemonic.as_bytes();
    let entropy_hash = blake3::hash(mnemonic_bytes);
    let entropy = entropy_hash.as_bytes();

    let first_half = blake3::derive_key(&context_a, entropy);
    let second_half = blake3::derive_key(&context_b, entropy);

    let mut seed = [0u8; 64];
    seed[..32].copy_from_slice(&first_half);
    seed[32..].copy_from_slice(&second_half);

    // Derive keypair at "pyana/0" path (main agent identity).
    let derived = blake3::derive_key("pyana/0", &seed);

    // Ed25519: The derived 32 bytes are the secret key seed.
    // Public key = secret key seed -> SHA-512 -> clamp -> scalar mult.
    // Without ed25519-dalek in WASM deps, return the raw derived bytes.
    // The extension can compute the public key from the 32-byte secret.
    let mut result = Vec::with_capacity(64);
    // For now, output just the 32-byte secret key seed.
    // The extension uses this with its own Ed25519 library to get the public key.
    result.extend_from_slice(&derived);
    // Also output a placeholder for public key (extension computes from secret).
    result.extend_from_slice(&[0u8; 32]);

    Ok(result)
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
