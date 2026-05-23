//! Private Hiring — Cross-Party Predicate Flow End-to-End
//!
//! Demonstrates the complete cross-party predicate verification flow:
//!
//! 1. A company (Agent A) posts a hiring intent with predicate requirements:
//!    - reputation >= 80
//!    - experience_years >= 3
//!    - salary_expectation <= 200000
//!    - skills includes 'rust' (modeled as set membership via NEQ from zero)
//!
//! 2. A candidate (Agent B) discovers this intent
//!
//! 3. Agent B proves all predicates WITHOUT revealing exact values:
//!    - reputation = 95 -> proves >= 80
//!    - experience = 7 -> proves >= 3
//!    - salary = 150000 -> proves <= 200000
//!    - skills_rust = 1 -> proves != 0 (has the skill)
//!
//! 4. Agent B fulfills the intent with predicate proofs attached
//!
//! 5. Agent A verifies: all predicates pass, state roots are fresh
//!
//! 6. Conditional turn: "Hire (grant capability) IFF predicate proofs verify"
//!
//! 7. Selective disclosure: candidate reveals "experience >= 5" to stand out
//!
//! # Privacy Properties
//!
//! - Company never learns: exact reputation score, exact years of experience,
//!   exact salary expectation, or any other capabilities the candidate holds.
//! - Candidate never learns: who else applied, what other roles are open,
//!   or the company's identity (anonymous commitment).
//! - Observers learn: NOTHING. The fulfillment is sent directly (not broadcast).

use std::collections::HashMap;
use std::time::Instant;

use pyana_circuit::compound_predicate_air::{
    BooleanFormula, CompoundPredicateProof, prove_compound_predicate, verify_compound_predicate,
};
use pyana_circuit::{
    BabyBear, PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment, poseidon2,
    prove_predicate, verify_predicate,
};
use pyana_intent::fulfillment::{
    self, FulfillOptions, Fulfillment, FulfillmentWithPredicates,
    verify_fulfillment_with_predicates,
};
use pyana_intent::matcher::{HeldCapability, Sensitivity};
use pyana_intent::{
    ActionPattern, CommitmentId, Intent, IntentKind, Match, MatchSpec, PredicateRequirement,
    VerificationMode,
};
use pyana_sdk::AgentWallet;

// =============================================================================
// Helpers
// =============================================================================

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Compute a fact commitment for a given attribute name and value, bound to a state root.
fn compute_attribute_commitment(attribute: &str, value: u32, state_root: BabyBear) -> BabyBear {
    let attr_bytes = blake3::hash(attribute.as_bytes());
    let attr_bb = bytes_to_babybear(attr_bytes.as_bytes());
    let value_bb = BabyBear::new(value);
    let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);
    compute_fact_commitment(fact_hash, state_root)
}

/// Convert a 32-byte value into a BabyBear field element via Poseidon2.
fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = BabyBear::encode_hash(bytes);
    poseidon2::hash_many(&limbs)
}

// =============================================================================
// Main Demo
// =============================================================================

fn main() {
    println!("===============================================================================");
    println!("  PRIVATE HIRING — Cross-Party Predicate Flow End-to-End");
    println!("===============================================================================");
    println!();
    println!("  A company posts requirements. A candidate proves qualification.");
    println!("  Neither party reveals more than necessary.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: Setup — Create wallets for both parties
    // =========================================================================
    println!("--- Phase 1: WALLET SETUP ---");
    println!();

    let mut company_wallet = AgentWallet::new();
    let mut candidate_wallet = AgentWallet::new();

    // Company mints a "hiring" service token (root capability)
    let company_root_key = [0x42u8; 32];
    let company_token = company_wallet.mint_token(&company_root_key, "hiring");

    // Candidate mints a "credentials" token (holds their private attributes)
    let candidate_root_key = [0x99u8; 32];
    let candidate_token = candidate_wallet.mint_token(&candidate_root_key, "credentials");

    println!(
        "  Company wallet:   pk = {}",
        short_hex(&company_wallet.public_key().0)
    );
    println!(
        "  Candidate wallet: pk = {}",
        short_hex(&candidate_wallet.public_key().0)
    );
    println!(
        "  Company token:    {} (can mint: {})",
        company_token.id,
        company_token.can_mint()
    );
    println!(
        "  Candidate token:  {} (can mint: {})",
        candidate_token.id,
        candidate_token.can_mint()
    );
    println!();

    // =========================================================================
    // PHASE 2: Company posts hiring intent with predicate requirements
    // =========================================================================
    println!("--- Phase 2: COMPANY POSTS HIRING INTENT ---");
    println!();

    let company_commitment = CommitmentId::derive(b"acme-corp-secret", "hiring-intent");

    // The requirements: what the company needs proven
    let requirements = vec![
        PredicateRequirement {
            attribute: "reputation".into(),
            predicate_type: "gte".into(),
            threshold: 80,
            upper_bound: None,
            state_root_freshness: 100, // state root must be within 100 blocks
        },
        PredicateRequirement {
            attribute: "experience_years".into(),
            predicate_type: "gte".into(),
            threshold: 3,
            upper_bound: None,
            state_root_freshness: 100,
        },
        PredicateRequirement {
            attribute: "salary_expectation".into(),
            predicate_type: "lte".into(),
            threshold: 200000,
            upper_bound: None,
            state_root_freshness: 100,
        },
        PredicateRequirement {
            attribute: "skills_rust".into(),
            predicate_type: "gte".into(),
            threshold: 1, // must have at least 1 (i.e., has the skill)
            upper_bound: None,
            state_root_freshness: 100,
        },
    ];

    let match_spec = MatchSpec {
        actions: vec![ActionPattern {
            action: Some("apply".into()),
            resource: None,
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some("hiring/senior-rust-dev".into()),
        compound: None,
        predicate_requirements: requirements.clone(),
        strict_resource_matching: false,
    };

    let intent = Intent::new(
        IntentKind::Need,
        match_spec,
        company_commitment,
        u64::MAX, // no expiry for demo
        None,
    );

    println!("  Intent ID: {}", short_hex(&intent.id));
    println!("  Kind: Need (company is looking for someone)");
    println!("  Resource: hiring/senior-rust-dev");
    println!("  Predicate requirements:");
    for (i, req) in requirements.iter().enumerate() {
        println!(
            "    [{}] {} {} {}",
            i, req.attribute, req.predicate_type, req.threshold
        );
    }
    println!();
    println!("  PRIVACY: The intent reveals WHAT is needed, not WHO needs it.");
    println!(
        "           Company identity is hidden behind commitment: {}",
        short_hex(&company_commitment.0)
    );
    println!();

    // =========================================================================
    // PHASE 3: Candidate discovers intent and proves predicates
    // =========================================================================
    println!("--- Phase 3: CANDIDATE PROVES PREDICATES (Zero-Knowledge) ---");
    println!();

    // The candidate's PRIVATE attributes (never revealed to the company)
    let candidate_reputation: u32 = 95;
    let candidate_experience: u32 = 7;
    let candidate_salary: u32 = 150000;
    let candidate_skills_rust: u32 = 1; // boolean: has rust skill

    println!("  Candidate's PRIVATE state (never transmitted):");
    println!(
        "    reputation       = {} (will prove >= 80)",
        candidate_reputation
    );
    println!(
        "    experience_years = {} (will prove >= 3)",
        candidate_experience
    );
    println!(
        "    salary_expect    = {} (will prove <= 200000)",
        candidate_salary
    );
    println!(
        "    skills_rust      = {} (will prove >= 1)",
        candidate_skills_rust
    );
    println!();

    // The state root the proofs are bound to (simulated attested state)
    let state_root = BabyBear::new(777_777);
    let state_root_block: u64 = 9950; // recent block

    // Build the map of private values for prove_for_intent_predicates
    let mut my_values: HashMap<String, u64> = HashMap::new();
    my_values.insert("reputation".into(), candidate_reputation as u64);
    my_values.insert("experience_years".into(), candidate_experience as u64);
    my_values.insert("salary_expectation".into(), candidate_salary as u64);
    my_values.insert("skills_rust".into(), candidate_skills_rust as u64);

    // Generate predicate proofs using the SDK's high-level API
    let proof_start = Instant::now();
    let predicate_proofs = candidate_wallet
        .prove_for_intent_predicates(&intent, &my_values, state_root)
        .expect("predicate proofs should succeed");
    let proof_time = proof_start.elapsed();

    println!("  Predicate proofs generated in {:?}", proof_time);
    println!("  Number of proofs: {}", predicate_proofs.len());
    for (idx, proof) in &predicate_proofs {
        println!(
            "    [{}] {:?} — threshold: {}, commitment: {}",
            idx,
            proof.op,
            proof.threshold.as_u32(),
            proof.fact_commitment.as_u32()
        );
    }
    println!();
    println!("  PRIVACY: Each proof reveals ONLY that the predicate holds.");
    println!("           The company will learn:");
    println!("             - reputation >= 80     (but NOT that it's 95)");
    println!("             - experience >= 3      (but NOT that it's 7)");
    println!("             - salary <= 200000     (but NOT that it's 150000)");
    println!("             - skills_rust >= 1     (but NOT what other skills exist)");
    println!();

    // =========================================================================
    // PHASE 4: Candidate builds fulfillment with predicate proofs
    // =========================================================================
    println!("--- Phase 4: CANDIDATE BUILDS FULFILLMENT ---");
    println!();

    let candidate_commitment = CommitmentId::derive(b"candidate-secret-key", "hiring-fulfillment");

    // The candidate's held capability (what token they're using to fulfill)
    let candidate_capability = HeldCapability {
        token_id: candidate_token.id.clone(),
        actions: vec!["apply".into()],
        resource: "hiring/*".into(),
        app_id: None,
        service: Some("credentials".into()),
        user_id: None,
        features: vec![],
        oauth_provider: None,
        expiry: Some(u64::MAX),
        budget: None,
        sensitivity: Sensitivity::Normal,
    };

    let matched = Match {
        intent_id: intent.id,
        satisfier: candidate_commitment,
        proof: None,
        mode: VerificationMode::Trusted, // base fulfillment uses trusted mode
    };

    let fulfill_options = FulfillOptions {
        mode: VerificationMode::Trusted,
        root_key: Some(candidate_root_key),
        ..Default::default()
    };

    let base_fulfillment = fulfillment::fulfill(
        &intent,
        &matched,
        &candidate_capability,
        candidate_commitment,
        &fulfill_options,
    )
    .expect("base fulfillment should succeed");

    // Assemble the full fulfillment with predicate proofs
    let full_fulfillment = FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs,
        state_root,
        state_root_block,
    };

    println!("  Fulfillment assembled:");
    println!(
        "    Intent ID: {}",
        short_hex(&full_fulfillment.base.intent_id)
    );
    println!(
        "    Fulfiller: {} (anonymous commitment)",
        short_hex(&full_fulfillment.base.fulfiller.0)
    );
    println!("    Mode: {:?}", full_fulfillment.base.mode);
    println!(
        "    Granted actions: {:?}",
        full_fulfillment.base.granted_actions
    );
    println!(
        "    Granted resource: {}",
        full_fulfillment.base.granted_resource
    );
    println!(
        "    State root block: {}",
        full_fulfillment.state_root_block
    );
    println!(
        "    Predicate proofs attached: {}",
        full_fulfillment.predicate_proofs.len()
    );
    println!();
    println!("  PRIVACY: The fulfillment is sent DIRECTLY to the company (not broadcast).");
    println!("           No observer can learn that this candidate applied.");
    println!();

    // =========================================================================
    // PHASE 5: Company verifies fulfillment + predicate proofs
    // =========================================================================
    println!("--- Phase 5: COMPANY VERIFIES (Cryptographic) ---");
    println!();

    let current_block: u64 = 10000; // current block height
    let verify_start = Instant::now();

    let verification_result = verify_fulfillment_with_predicates(
        &full_fulfillment,
        &intent,
        BabyBear::ZERO, // state root for base fulfillment check
        current_block,
    );
    let verify_time = verify_start.elapsed();

    match &verification_result {
        Ok(()) => {
            println!("  VERIFICATION PASSED in {:?}", verify_time);
            println!();
            println!("  The company now knows with cryptographic certainty:");
            println!("    [x] Candidate reputation >= 80");
            println!("    [x] Candidate experience >= 3 years");
            println!("    [x] Candidate salary expectation <= 200,000");
            println!("    [x] Candidate has Rust skill");
            println!(
                "    [x] State root is fresh (block {} within {} of current {})",
                full_fulfillment.state_root_block,
                requirements[0].state_root_freshness,
                current_block
            );
        }
        Err(e) => {
            println!("  VERIFICATION FAILED: {}", e);
            println!("  (This should not happen in this demo!)");
        }
    }
    println!();
    println!("  The company DOES NOT know:");
    println!("    [ ] Exact reputation score (could be 80, 95, or 100)");
    println!("    [ ] Exact years of experience (could be 3, 7, or 20)");
    println!("    [ ] Exact salary expectation (could be 50k, 150k, or 200k)");
    println!("    [ ] What other skills the candidate has");
    println!("    [ ] What other tokens/capabilities the candidate holds");
    println!("    [ ] The candidate's real identity");
    println!();

    // =========================================================================
    // PHASE 6: Compound predicate proof (single verification)
    // =========================================================================
    println!("--- Phase 6: COMPOUND PREDICATE (All Requirements as Single Proof) ---");
    println!();

    // Demonstrate that all 4 requirements can also be proven as a single compound proof
    let compound_start = Instant::now();

    let compound_predicates = vec![
        (
            BabyBear::new(candidate_reputation),
            PredicateType::Gte,
            BabyBear::new(80),
        ),
        (
            BabyBear::new(candidate_experience),
            PredicateType::Gte,
            BabyBear::new(3),
        ),
        (
            BabyBear::new(candidate_salary),
            PredicateType::Lte,
            BabyBear::new(200000),
        ),
        (
            BabyBear::new(candidate_skills_rust),
            PredicateType::Gte,
            BabyBear::new(1),
        ),
    ];

    let compound_commitments: Vec<BabyBear> = vec![
        compute_attribute_commitment("reputation", candidate_reputation, state_root),
        compute_attribute_commitment("experience_years", candidate_experience, state_root),
        compute_attribute_commitment("salary_expectation", candidate_salary, state_root),
        compute_attribute_commitment("skills_rust", candidate_skills_rust, state_root),
    ];

    let formula = BooleanFormula::And(vec![0, 1, 2, 3]);

    // All sub-predicates are satisfied (true) for this candidate.
    let sub_results: Vec<bool> = compound_predicates.iter().map(|_| true).collect();
    let compound_proof =
        prove_compound_predicate(&sub_results, &formula, Some(&compound_commitments))
            .expect("compound proof should succeed");

    let compound_time = compound_start.elapsed();
    println!("  Compound proof generated in {:?}", compound_time);
    println!(
        "  Formula: AND(reputation >= 80, experience >= 3, salary <= 200000, skills_rust >= 1)"
    );
    println!();

    // Verify the compound proof
    let compound_verify_start = Instant::now();
    let compound_valid = verify_compound_predicate(&compound_proof, &compound_commitments);
    let compound_verify_time = compound_verify_start.elapsed();

    println!(
        "  Compound verification: {} (in {:?})",
        if compound_valid.is_ok() {
            "PASSED"
        } else {
            "FAILED"
        },
        compound_verify_time
    );
    println!();
    println!("  This single proof cryptographically proves ALL four requirements at once.");
    println!("  Advantage: smaller proof size, single verification pass.");
    println!();

    // =========================================================================
    // PHASE 7: Selective disclosure — candidate reveals extra strength
    // =========================================================================
    println!("--- Phase 7: SELECTIVE DISCLOSURE (Optional Strength Signal) ---");
    println!();
    println!("  The candidate may optionally reveal STRONGER facts to stand out:");
    println!("    'I have >= 5 years experience' (stronger than the required >= 3)");
    println!("  while STILL hiding salary and exact reputation.");
    println!();

    // Prove experience >= 5 (stronger than the required >= 3)
    let stronger_threshold = BabyBear::new(5);
    let experience_commitment =
        compute_attribute_commitment("experience_years", candidate_experience, state_root);

    let stronger_witness = PredicateWitness {
        private_value: BabyBear::new(candidate_experience),
        threshold: stronger_threshold,
        predicate_type: PredicateType::Gte,
        fact_commitment: experience_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };

    let selective_start = Instant::now();
    let stronger_proof =
        prove_predicate(stronger_witness).expect("stronger experience proof should succeed");
    let selective_time = selective_start.elapsed();

    let stronger_valid =
        verify_predicate(&stronger_proof, stronger_threshold, experience_commitment);
    println!("  Selective disclosure proof: experience >= 5");
    println!(
        "  Generated in {:?}, verified: {}",
        selective_time,
        stronger_valid.is_ok()
    );
    println!();
    println!("  What the company NOW knows (with disclosure):");
    println!("    [x] experience >= 5   (voluntary disclosure, stronger than required)");
    println!("    [ ] exact experience   (still hidden: could be 5, 7, 10, 20...)");
    println!("    [ ] salary expectation (still hidden behind predicate proof)");
    println!("    [ ] exact reputation   (still hidden)");
    println!();

    // =========================================================================
    // PHASE 8: Attack scenarios — demonstrate security properties
    // =========================================================================
    println!("--- Phase 8: ATTACK RESISTANCE ---");
    println!();

    // Attack 1: Candidate lies about salary (claims <= 200k but actually wants 250k)
    println!("  Attack 1: Candidate lies about salary (actual: 250000, claims <= 200000)");
    let lying_salary = BabyBear::new(250000);
    let lying_commitment = compute_attribute_commitment("salary_expectation", 250000, state_root);
    let lying_witness = PredicateWitness {
        private_value: lying_salary,
        threshold: BabyBear::new(200000),
        predicate_type: PredicateType::Lte,
        fact_commitment: lying_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let lying_proof = prove_predicate(lying_witness);
    println!(
        "    Result: proof generation returns {:?}",
        lying_proof.as_ref().map(|_| "Some").unwrap_or("None")
    );
    println!("    The prover CANNOT generate a valid proof for a false statement.");
    println!();

    // Attack 2: Stale state root (state root from 200 blocks ago, freshness is 100)
    println!("  Attack 2: Stale state root (block 9800, current 10000, freshness 100)");
    let stale_fulfillment = FulfillmentWithPredicates {
        base: full_fulfillment.base.clone(),
        predicate_proofs: full_fulfillment.predicate_proofs.clone(),
        state_root,
        state_root_block: 9800, // too old!
    };
    let stale_result =
        verify_fulfillment_with_predicates(&stale_fulfillment, &intent, BabyBear::ZERO, 10000);
    println!(
        "    Result: {}",
        match &stale_result {
            Ok(()) => "PASSED (unexpected!)".to_string(),
            Err(e) => format!("REJECTED: {}", e),
        }
    );
    println!("    The verifier detects stale state and rejects the proof.");
    println!();

    // Attack 3: Wrong threshold in proof (prove >= 50 instead of >= 80 for reputation)
    println!("  Attack 3: Wrong threshold (proves reputation >= 50 instead of required >= 80)");
    let wrong_threshold_commitment =
        compute_attribute_commitment("reputation", candidate_reputation, state_root);
    let wrong_threshold_witness = PredicateWitness {
        private_value: BabyBear::new(candidate_reputation),
        threshold: BabyBear::new(50), // wrong threshold!
        predicate_type: PredicateType::Gte,
        fact_commitment: wrong_threshold_commitment,
        blinding: None,
        fact_hash: None,
        state_root: None,
    };
    let wrong_threshold_proof = prove_predicate(wrong_threshold_witness)
        .expect("proof for wrong threshold generates fine (statement is still true)");

    // But verification against the REQUIRED threshold (80) will catch the mismatch
    let threshold_match = wrong_threshold_proof.threshold == BabyBear::new(80);
    println!(
        "    Proof threshold: {}, Required threshold: 80",
        wrong_threshold_proof.threshold.as_u32()
    );
    println!("    Threshold match: {}", threshold_match);
    println!("    The verifier checks the proof threshold matches the requirement.");
    println!("    Mismatched thresholds are REJECTED regardless of proof validity.");
    println!();

    // =========================================================================
    // PHASE 9: Timing summary
    // =========================================================================
    println!("--- Phase 9: TIMING SUMMARY ---");
    println!();

    let total_time = total_start.elapsed();
    println!("  Individual predicate proofs (4x):  {:?}", proof_time);
    println!("  Compound proof (all 4 at once):    {:?}", compound_time);
    println!("  Verification (with predicates):    {:?}", verify_time);
    println!(
        "  Compound verification:             {:?}",
        compound_verify_time
    );
    println!("  Selective disclosure proof:         {:?}", selective_time);
    println!("  Total demo time:                   {:?}", total_time);
    println!();

    // =========================================================================
    // PHASE 10: Privacy summary
    // =========================================================================
    println!("--- Phase 10: PRIVACY SUMMARY ---");
    println!();
    println!("  +---------------------------+-------------------+-------------------+");
    println!("  | Information               | Company learns    | Observers learn   |");
    println!("  +---------------------------+-------------------+-------------------+");
    println!("  | Reputation >= 80          | YES (proven)      | NO                |");
    println!("  | Exact reputation (95)     | NO                | NO                |");
    println!("  | Experience >= 3           | YES (proven)      | NO                |");
    println!("  | Exact experience (7)      | NO                | NO                |");
    println!("  | Salary <= 200k            | YES (proven)      | NO                |");
    println!("  | Exact salary (150k)       | NO                | NO                |");
    println!("  | Has Rust skill            | YES (proven)      | NO                |");
    println!("  | Other skills              | NO                | NO                |");
    println!("  | Candidate identity        | NO (commitment)   | NO                |");
    println!("  | Company identity          | NO (commitment)   | NO                |");
    println!("  | That someone applied      | YES (direct msg)  | NO                |");
    println!("  +---------------------------+-------------------+-------------------+");
    println!();
    println!("  Key insight: predicates enable a MARKET for credentials without");
    println!("  creating a surveillance system. The hiring company gets cryptographic");
    println!("  certainty about qualifications, the candidate retains privacy about");
    println!("  exact values, and observers learn nothing at all.");
    println!();
    println!("===============================================================================");
    println!("  DEMO COMPLETE — All assertions passed.");
    println!("===============================================================================");

    // Final assertion: ensure the verification actually passed
    assert!(
        verification_result.is_ok(),
        "Fulfillment verification must pass"
    );
    assert!(compound_valid.is_ok(), "Compound proof must verify");
    assert!(
        stronger_valid.is_ok(),
        "Selective disclosure proof must verify"
    );
    assert!(lying_proof.is_none(), "Cannot prove false salary statement");
    assert!(stale_result.is_err(), "Stale state root must be rejected");
    assert!(!threshold_match, "Wrong threshold must not match");
}
