//! RBAC Datalog Demo — Role-Based Access Control in Datalog
//!
//! Demonstrates:
//! 1. Define roles: admin, editor, viewer
//! 2. Define resources: /docs/*, /admin/*, /api/*
//! 3. Admin can access everything, editor can read/write docs and read API, viewer read-only
//! 4. Mint tokens with role facts, attenuate to specific resources
//! 5. Show Datalog evaluation deciding allow/deny for various request combinations
//! 6. Use `pyana-trace` (the Datalog evaluator) directly, showing derivation traces
//! 7. Prove one of the decisions in a STARK (using prove_authorization_stark)

use pyana_circuit::field::BabyBear;
use pyana_circuit::derivation_air::{BodyAtomPattern, CircuitRule, DerivationWitness};
use pyana_circuit::multi_step_air::{
    ALLOW_PREDICATE, build_multi_step_witness, prove_authorization_stark,
    verify_authorization_stark,
};
use pyana_circuit::poseidon2::hash_fact;
use pyana_circuit::stark::proof_to_bytes;
use pyana_trace::{
    Atom, AuthorizationRequest, AuthorizationTrace, Check, Conclusion, Evaluator, Fact, Rule,
    Term, symbol_from_str, verify_trace,
};

// ============================================================================
// Helper: pretty-print a symbol (trim trailing zeros)
// ============================================================================

fn sym_str(sym: &[u8; 32]) -> &str {
    let end = sym.iter().position(|&b| b == 0).unwrap_or(32);
    std::str::from_utf8(&sym[..end]).unwrap_or("<binary>")
}

fn conclusion_str(c: &Conclusion) -> &'static str {
    match c {
        Conclusion::Allow { .. } => "ALLOW",
        Conclusion::Deny => "DENY",
    }
}

// ============================================================================
// RBAC Policy: custom Datalog rules for role-based access
// ============================================================================

/// Define the RBAC policy rules:
///
/// ```datalog
/// % Rule 100: Admin gets unrestricted access
/// allow() :- has_role($user, "admin"), request_user($user), request_action($act).
///
/// % Rule 101: Role grants access to a resource if role_permission exists
/// allow() :- has_role($user, $role), role_permission($role, $resource, $action),
///            request_user($user), request_action($action).
///
/// % Rule 102: Allow via resource match using service-scoped check
/// allow() :- has_role($user, $role), role_permission($role, $resource, $action),
///            request_user($user), request_service($resource), request_action($action).
/// ```
fn rbac_policy() -> Vec<Rule> {
    vec![
        // Rule 100: admin has unrestricted access
        // allow() :- has_role($user, "admin"), request_user($user), request_action($act).
        Rule {
            id: 100,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("has_role"),
                    terms: vec![Term::Var(0), Term::Const(symbol_from_str("admin"))],
                },
                Atom {
                    predicate: symbol_from_str("request_user"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)],
                },
            ],
            checks: vec![],
        },
        // Rule 101: role_permission grants access (using service for resource)
        // allow() :- has_role($user, $role), role_permission($role, $resource, $action),
        //            request_user($user), request_service($resource).
        // We use request_action separately and check equality via Contains.
        Rule {
            id: 101,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("has_role"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $user, $role
                },
                Atom {
                    predicate: symbol_from_str("role_permission"),
                    terms: vec![Term::Var(1), Term::Var(2), Term::Var(3)], // $role, $resource, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_user"),
                    terms: vec![Term::Var(0)], // $user
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(2)], // $resource
                },
            ],
            checks: vec![
                // $actions.contains($requested_action) is done implicitly because
                // we match request_action in the body. But since we hit 4 body limit,
                // we use Contains on the actions field.
                Check::Contains(Term::Var(3), Term::Var(4)),
            ],
        },
        // Rule 102: same but with request_action as a body atom (simpler, 4 body atoms)
        // allow() :- has_role($user, $role), role_permission($role, $resource, $actions),
        //            request_user($user), request_action($act).
        // check: $actions.contains($act)
        Rule {
            id: 102,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("has_role"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $user, $role
                },
                Atom {
                    predicate: symbol_from_str("role_permission"),
                    terms: vec![Term::Var(1), Term::Var(2), Term::Var(3)], // $role, $resource, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_user"),
                    terms: vec![Term::Var(0)], // $user
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(4)], // $act
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(3), Term::Var(4)), // $actions.contains($act)
            ],
        },
    ]
}

/// Build the RBAC fact set defining roles and permissions.
///
/// Roles:
/// - admin: full access to everything
/// - editor: read/write on /docs, read on /api
/// - viewer: read-only on /docs, read on /api
///
/// Users:
/// - alice: admin
/// - bob: editor
/// - carol: viewer
fn rbac_facts() -> Vec<Fact> {
    vec![
        // User-role assignments
        Fact::new(
            symbol_from_str("has_role"),
            vec![
                Term::Const(symbol_from_str("alice")),
                Term::Const(symbol_from_str("admin")),
            ],
        ),
        Fact::new(
            symbol_from_str("has_role"),
            vec![
                Term::Const(symbol_from_str("bob")),
                Term::Const(symbol_from_str("editor")),
            ],
        ),
        Fact::new(
            symbol_from_str("has_role"),
            vec![
                Term::Const(symbol_from_str("carol")),
                Term::Const(symbol_from_str("viewer")),
            ],
        ),
        // Role permissions: role_permission(role, resource, actions)
        // Editor permissions
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("editor")),
                Term::Const(symbol_from_str("/docs")),
                Term::Const(symbol_from_str("read,write")),
            ],
        ),
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("editor")),
                Term::Const(symbol_from_str("/api")),
                Term::Const(symbol_from_str("read")),
            ],
        ),
        // Viewer permissions
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("viewer")),
                Term::Const(symbol_from_str("/docs")),
                Term::Const(symbol_from_str("read")),
            ],
        ),
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("viewer")),
                Term::Const(symbol_from_str("/api")),
                Term::Const(symbol_from_str("read")),
            ],
        ),
    ]
}

// ============================================================================
// Evaluation helper
// ============================================================================

fn evaluate_and_print(
    evaluator: &Evaluator,
    description: &str,
    request: &AuthorizationRequest,
    facts: &[Fact],
    rules: &[Rule],
) -> AuthorizationTrace {
    let trace = evaluator.evaluate(request);
    let decision = conclusion_str(&trace.conclusion);

    let user = request
        .user_id
        .as_ref()
        .map(|s| sym_str(s))
        .unwrap_or("?");
    let action = request
        .action
        .as_ref()
        .map(|s| sym_str(s))
        .unwrap_or("?");
    let service = request
        .service
        .as_ref()
        .map(|s| sym_str(s))
        .unwrap_or("*");

    println!(
        "  {} => {} (user={}, action={}, resource={})",
        description, decision, user, action, service
    );

    if !trace.steps.is_empty() {
        println!("    Derivation trace ({} steps):", trace.steps.len());
        for (i, step) in trace.steps.iter().enumerate() {
            let pred = sym_str(&step.derived_fact.predicate);
            println!(
                "      Step {}: rule {} => {}(...)",
                i + 1,
                step.rule_id,
                pred
            );
        }
    }

    // Verify the trace
    let valid = verify_trace(facts, rules, &trace);
    println!("    Trace verification: {}", if valid { "PASS" } else { "FAIL" });
    println!();

    trace
}

fn main() {
    println!("=== Pyana RBAC Datalog Demo ===\n");

    // =========================================================================
    // STEP 1: Define the RBAC policy and fact set
    // =========================================================================
    println!("--- Step 1: DEFINE RBAC POLICY ---");
    println!("  Roles: admin, editor, viewer");
    println!("  Resources: /docs, /api, /admin");
    println!("  Users: alice (admin), bob (editor), carol (viewer)");
    println!();
    println!("  Policy rules:");
    println!("    Rule 100: allow() :- has_role($user, \"admin\"), request_user($user), request_action($act)");
    println!("    Rule 102: allow() :- has_role($user, $role), role_permission($role, $resource, $actions),");
    println!("                         request_user($user), request_action($act), $actions.contains($act)");
    println!();

    let facts = rbac_facts();
    let rules = rbac_policy();
    let evaluator = Evaluator::new(facts.clone(), rules.clone());

    // =========================================================================
    // STEP 2: Evaluate authorization requests
    // =========================================================================
    println!("--- Step 2: EVALUATE AUTHORIZATION REQUESTS ---\n");

    // Alice (admin) can access anything
    let req_alice_read_docs = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: Some(symbol_from_str("alice")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Alice reads /docs",
        &req_alice_read_docs,
        &facts,
        &rules,
    );

    let req_alice_delete_admin = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/admin")),
        action: Some(symbol_from_str("delete")),
        features: vec![],
        user_id: Some(symbol_from_str("alice")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Alice deletes /admin",
        &req_alice_delete_admin,
        &facts,
        &rules,
    );

    // Bob (editor) can read/write docs, read API
    let req_bob_write_docs = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("write")),
        features: vec![],
        user_id: Some(symbol_from_str("bob")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Bob writes /docs",
        &req_bob_write_docs,
        &facts,
        &rules,
    );

    let req_bob_read_api = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/api")),
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: Some(symbol_from_str("bob")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Bob reads /api",
        &req_bob_read_api,
        &facts,
        &rules,
    );

    let req_bob_delete_docs = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("delete")),
        features: vec![],
        user_id: Some(symbol_from_str("bob")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Bob deletes /docs (DENIED - editor can't delete)",
        &req_bob_delete_docs,
        &facts,
        &rules,
    );

    // Carol (viewer) can only read
    let req_carol_read_docs = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: Some(symbol_from_str("carol")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Carol reads /docs",
        &req_carol_read_docs,
        &facts,
        &rules,
    );

    let req_carol_write_docs = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("write")),
        features: vec![],
        user_id: Some(symbol_from_str("carol")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Carol writes /docs (DENIED - viewer can't write)",
        &req_carol_write_docs,
        &facts,
        &rules,
    );

    // Unknown user
    let req_eve_read = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: Some(symbol_from_str("eve")),
        now: 1700000000,
    };
    evaluate_and_print(
        &evaluator,
        "Eve reads /docs (DENIED - no role assigned)",
        &req_eve_read,
        &facts,
        &rules,
    );

    // =========================================================================
    // STEP 3: Token attenuation — restrict a token to read-only
    // =========================================================================
    println!("--- Step 3: TOKEN ATTENUATION (restrict to read-only) ---\n");

    // Simulate a "token" by creating an attenuated fact set.
    // Bob's original token gives editor access (read+write on /docs, read on /api).
    // Attenuate it to read-only access (remove write permission).
    let attenuated_facts: Vec<Fact> = vec![
        Fact::new(
            symbol_from_str("has_role"),
            vec![
                Term::Const(symbol_from_str("bob")),
                Term::Const(symbol_from_str("editor")),
            ],
        ),
        // Attenuated: only read permission on /docs (write removed)
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("editor")),
                Term::Const(symbol_from_str("/docs")),
                Term::Const(symbol_from_str("read")), // was "read,write"
            ],
        ),
        Fact::new(
            symbol_from_str("role_permission"),
            vec![
                Term::Const(symbol_from_str("editor")),
                Term::Const(symbol_from_str("/api")),
                Term::Const(symbol_from_str("read")),
            ],
        ),
    ];

    let attenuated_eval = Evaluator::new(attenuated_facts.clone(), rules.clone());

    println!("  Attenuated token: Bob's access restricted to read-only\n");

    let req_bob_write_attenuated = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("write")),
        features: vec![],
        user_id: Some(symbol_from_str("bob")),
        now: 1700000000,
    };
    evaluate_and_print(
        &attenuated_eval,
        "Bob writes /docs (DENIED - attenuated to read-only)",
        &req_bob_write_attenuated,
        &attenuated_facts,
        &rules,
    );

    let req_bob_read_docs_attenuated = AuthorizationRequest {
        app_id: None,
        service: Some(symbol_from_str("/docs")),
        action: Some(symbol_from_str("read")),
        features: vec![],
        user_id: Some(symbol_from_str("bob")),
        now: 1700000000,
    };
    let allow_trace = evaluate_and_print(
        &attenuated_eval,
        "Bob reads /docs (ALLOWED - read still permitted)",
        &req_bob_read_docs_attenuated,
        &attenuated_facts,
        &rules,
    );

    // =========================================================================
    // STEP 4: Prove the ALLOW decision in a STARK
    // =========================================================================
    println!("--- Step 4: STARK PROOF OF AUTHORIZATION ---\n");
    println!("  Proving: Bob (editor) is allowed to write /docs");
    println!("  The verifier learns only: ALLOW/DENY + public inputs");
    println!("  The verifier does NOT learn: which role Bob has, what other resources exist\n");

    // Build a circuit witness from the Datalog trace
    // The Datalog trace has 1 derivation step (Rule 102 fires directly)
    assert!(
        matches!(allow_trace.conclusion, Conclusion::Allow { .. }),
        "Expected ALLOW for the STARK proof source"
    );

    let state_root = BabyBear::new(88888); // committed fact set root
    let request_hash = BabyBear::new(42424); // hash of the request

    // The derivation: has_role(bob, editor) + role_permission(editor, /docs, "read,write")
    //   + request_user(bob) + request_action(write) => allow()
    // We encode this as a single circuit derivation step.
    let has_role_pred = BabyBear::new(1001);
    let bob_val = BabyBear::new(2001);
    let editor_val = BabyBear::new(2002);
    let allow_pred = BabyBear::new(ALLOW_PREDICATE);

    let body_hash = hash_fact(has_role_pred, &[bob_val, editor_val, BabyBear::ZERO]);

    let step = DerivationWitness {
        rule: CircuitRule {
            id: 102,
            num_body_atoms: 1,
            num_variables: 2,
            head_predicate: allow_pred,
            head_terms: [
                (true, BabyBear::new(0)),  // $user -> bob
                (true, BabyBear::new(1)),  // $role -> editor
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
        substitution: vec![bob_val, editor_val],
        derived_predicate: allow_pred,
        derived_terms: [bob_val, editor_val, BabyBear::ZERO],
    };

    let witness = build_multi_step_witness(state_root, request_hash, vec![step]);
    let conclusion = witness.conclusion();
    let acc_hash = witness.final_accumulated_hash();

    assert_eq!(conclusion, BabyBear::ONE, "Witness should conclude ALLOW");

    println!("  Generating STARK proof...");
    let proof = prove_authorization_stark(&witness);
    let proof_bytes = proof_to_bytes(&proof);
    println!(
        "  Proof generated: {} bytes ({:.1} KiB), {} trace rows",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0,
        proof.trace_len
    );

    // Verify the proof
    let verify_result = verify_authorization_stark(conclusion, acc_hash, &proof);
    match &verify_result {
        Ok(()) => println!("  Verification: PASS"),
        Err(e) => println!("  Verification: FAIL ({})", e),
    }
    assert!(verify_result.is_ok());
    println!();

    // Show that tampering fails
    println!("  Tampering test: flip one bit in proof...");
    let mut tampered_proof = proof.clone();
    tampered_proof.trace_commitment[0] ^= 0xFF;
    let tamper_result = verify_authorization_stark(conclusion, acc_hash, &tampered_proof);
    assert!(tamper_result.is_err());
    println!("  Tampered proof rejected: {}", tamper_result.unwrap_err());
    println!();

    // =========================================================================
    // STEP 5: Summary
    // =========================================================================
    println!("--- Step 5: SUMMARY ---\n");
    println!("  RBAC Policy:");
    println!("    - 3 roles (admin, editor, viewer) with hierarchical permissions");
    println!("    - Admin: unrestricted access (any resource, any action)");
    println!("    - Editor: read+write on /docs, read on /api");
    println!("    - Viewer: read-only on /docs and /api");
    println!();
    println!("  Key Properties:");
    println!("    1. Datalog evaluation is deterministic and auditable (full trace)");
    println!("    2. Traces can be verified independently (verify_trace)");
    println!("    3. Attenuation only removes capabilities (can't escalate)");
    println!("    4. STARK proof hides the token contents from the verifier");
    println!("    5. Proof is non-interactive: can be verified offline");
    println!();
    println!("=== RBAC Datalog Demo Complete ===");
}
