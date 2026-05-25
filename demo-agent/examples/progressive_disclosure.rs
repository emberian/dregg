//! Progressive Disclosure Demo — Three Verification Modes on One Authorization
//!
//! Demonstrates:
//! 1. Create a token with multiple facts (role=admin via app, org=acme, clearance=top_secret, budget=1000)
//! 2. Evaluate with Datalog (proves the agent can access resource X)
//! 3. Present in Trusted mode: verifier sees everything (full trace)
//! 4. Present in Selective mode: reveal only role + org, hide clearance + budget
//! 5. Present in Fully Private mode: verifier sees only allow/deny + STARK proof
//! 6. For each mode, show exactly what the verifier learns and what remains hidden

use pyana_sdk::{AgentCipherclerk, AuthorizationPresentation, FactIndex, VerificationMode};
use pyana_sdk::{Attenuation, AuthRequest};
use pyana_trace::Conclusion;

fn main() {
    println!("=== Pyana Progressive Disclosure Demo ===\n");
    println!("This demo shows the SAME authorization evaluated three different ways,");
    println!("with progressively less information revealed to the verifier.\n");

    // =========================================================================
    // SETUP: Create an agent cclerk and mint a richly-attenuated token
    // =========================================================================
    println!("--- Setup: Token with Multiple Facts ---\n");

    let mut cclerk = AgentCipherclerk::new();
    let pubkey = cclerk.public_key();
    println!(
        "  Agent identity: {:02x}{:02x}{:02x}{:02x}...",
        pubkey.0[0], pubkey.0[1], pubkey.0[2], pubkey.0[3]
    );

    // Mint a root token for our organization's infrastructure service.
    let root_key: [u8; 32] = *blake3::hash(b"acme-corp-root-secret-key-2026!!").as_bytes();
    let root_token = cclerk.mint_token(&root_key, "infrastructure");
    println!("  Root token minted: service='infrastructure' (unrestricted)");

    // Attenuate with rich facts: app access, service access, features, user binding.
    // This simulates: "admin role on the 'deployments' app, read access to 'secrets' service,
    // with features 'top_secret_clearance' and 'budget_1000', confined to user 'agent-007'"
    let attenuated = cclerk
        .attenuate(
            &root_token,
            &Attenuation {
                apps: vec![("deployments".into(), "rwcd".into())], // admin role
                services: vec![("secrets".into(), "r".into())],    // read-only secrets
                features: vec!["top_secret_clearance".into(), "budget_1000".into()],
                confine_user: Some("agent-007".into()),
                not_after: Some(1800000000), // expires 2027
                ..Default::default()
            },
        )
        .expect("attenuation should succeed");

    println!("  Attenuated token created with:");
    println!("    - App: deployments (rwcd) -- represents admin role");
    println!("    - Service: secrets (r) -- read-only access");
    println!("    - Feature: top_secret_clearance");
    println!("    - Feature: budget_1000");
    println!("    - Confined to user: agent-007");
    println!("    - Expires: 2027");
    println!();

    // The authorization request: "Can this agent read from the deployments app?"
    let request = AuthRequest {
        app_id: Some("deployments".into()),
        action: Some("r".into()),
        user_id: Some("agent-007".into()),
        now: Some(1716000000), // May 2024 (well before expiry)
        ..Default::default()
    };

    println!("  Authorization request:");
    println!("    app_id: deployments");
    println!("    action: read");
    println!("    user_id: agent-007");
    println!("    time: 1716000000 (within validity window)");
    println!();

    // =========================================================================
    // MODE 1: TRUSTED — Full visibility, no proof needed
    // =========================================================================
    println!("=======================================================================");
    println!("  MODE 1: TRUSTED (Local Datalog Evaluation)");
    println!("=======================================================================\n");
    println!("  The verifier holds the root key and trusts the local evaluation.");
    println!("  Latency: ~8 microseconds. No cryptographic proof generated.\n");

    let trusted_result = cclerk.authorize(&attenuated, &request, VerificationMode::Trusted);

    match trusted_result {
        Ok(AuthorizationPresentation::Trusted { clearance, trace }) => {
            println!("  [RESULT: ALLOW]\n");
            println!("  What the verifier LEARNS (everything):");
            println!("  +---------------------------------------------------------+");
            println!("  | Full token clearance:                                    |");
            if let Some(ref policy) = clearance.matched_policy {
                println!("  |   Matched policy: {:<38} |", policy);
            }
            println!("  |   Capabilities:                                          |");
            for cap in &clearance.capabilities {
                println!(
                    "  |     {}:{} -> actions={}",
                    cap.resource_type, cap.resource_id, cap.actions
                );
            }
            if let Some(expires) = clearance.expires_at {
                println!("  |   Expires at: {:<43} |", expires);
            }
            if let Some(ref subject) = clearance.subject {
                println!("  |   Subject: {:<46} |", subject);
            }
            println!("  |                                                         |");
            println!("  | Full derivation trace:                                   |");
            println!("  |   Steps: {:<48} |", trace.steps.len());
            match &trace.conclusion {
                Conclusion::Allow { policy_rule_id } => {
                    println!(
                        "  |   Conclusion: ALLOW (rule {}){}",
                        policy_rule_id,
                        " ".repeat(28)
                    );
                }
                Conclusion::Deny => {
                    println!("  |   Conclusion: DENY                                      |");
                }
            }
            for (i, step) in trace.steps.iter().enumerate() {
                println!(
                    "  |   Step {}: rule={}, derived fact predicate bytes[0..4]={:02x}{:02x}{:02x}{:02x}",
                    i,
                    step.rule_id,
                    step.derived_fact.predicate[0],
                    step.derived_fact.predicate[1],
                    step.derived_fact.predicate[2],
                    step.derived_fact.predicate[3]
                );
            }
            println!("  +---------------------------------------------------------+");
            println!();
            println!("  What remains HIDDEN: Nothing. The verifier sees EVERYTHING.");
            println!("  The verifier knows: all capabilities, all rules used, all bindings.");
            println!();
        }
        Ok(_) => unreachable!("Trusted mode returns Trusted variant"),
        Err(e) => {
            println!("  [RESULT: DENIED] Error: {:?}\n", e);
            println!("  (Token authorization failed -- check attenuation and request match)");
            return;
        }
    }

    // =========================================================================
    // MODE 2: SELECTIVE DISCLOSURE — Reveal only chosen facts
    // =========================================================================
    println!("=======================================================================");
    println!("  MODE 2: SELECTIVE DISCLOSURE (STARK proof + chosen facts)");
    println!("=======================================================================\n");
    println!("  The verifier receives a STARK proof plus only the facts we choose");
    println!("  to reveal. We reveal the 'allow' derivation step (index 0) which shows");
    println!("  the app name and action match, but hide the user binding, clearance,");
    println!("  and budget features.");
    println!("  Latency: ~200ms (proof generation).\n");

    // Reveal only fact index 0 (the 'allow' derivation step that shows app+action).
    // Hide indices 1+ (user confinement, features, time checks, etc.)
    let selective_result = cclerk.authorize(
        &attenuated,
        &request,
        VerificationMode::SelectiveDisclosure {
            reveal: vec![FactIndex(0)],
        },
    );

    match selective_result {
        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
            ..
        }) => {
            println!(
                "  [RESULT: {}]\n",
                if conclusion { "ALLOW" } else { "DENY" }
            );
            println!("  What the verifier LEARNS (selective):");
            println!("  +---------------------------------------------------------+");
            println!(
                "  | Conclusion: {:<45} |",
                if conclusion { "ALLOW" } else { "DENY" }
            );
            println!(
                "  | STARK proof: {} bytes{}",
                proof.len(),
                " ".repeat(33usize.saturating_sub(proof.len().to_string().len()))
            );
            println!("  | Revealed facts ({}):", revealed_facts.len());
            for fact in &revealed_facts {
                // Show the predicate (first few bytes to identify it)
                let pred_str: String = fact
                    .predicate
                    .iter()
                    .take_while(|&&b| b != 0)
                    .map(|&b| b as char)
                    .collect();
                println!(
                    "  |   predicate='{}' ({} terms)",
                    if pred_str.is_empty() {
                        format!(
                            "{:02x}{:02x}{:02x}{:02x}...",
                            fact.predicate[0],
                            fact.predicate[1],
                            fact.predicate[2],
                            fact.predicate[3]
                        )
                    } else {
                        pred_str
                    },
                    fact.terms.len()
                );
            }
            println!("  +---------------------------------------------------------+");
            println!();
            println!("  What remains HIDDEN:");
            println!("    - User identity (agent-007) -- NOT revealed");
            println!("    - top_secret_clearance feature -- NOT revealed");
            println!("    - budget_1000 feature -- NOT revealed");
            println!("    - Expiration time -- NOT revealed");
            println!("    - Full capability set -- NOT revealed");
            println!("    - Number of attenuation steps -- NOT revealed");
            println!("    - Which specific Datalog rule fired -- hidden in proof");
            println!();
            println!("  The verifier can verify the STARK proof to confirm authorization");
            println!("  was genuinely derived, but cannot learn anything beyond the");
            println!("  revealed facts and the allow/deny conclusion.");
            println!();
        }
        Ok(_) => unreachable!("Selective mode returns Selective variant"),
        Err(e) => {
            println!("  [RESULT: ERROR] {:?}\n", e);
        }
    }

    // =========================================================================
    // MODE 3: FULLY PRIVATE — Only allow/deny + proof
    // =========================================================================
    println!("=======================================================================");
    println!("  MODE 3: FULLY PRIVATE (STARK proof, zero knowledge)");
    println!("=======================================================================\n");
    println!("  The verifier receives ONLY a single bit (allow/deny) and a STARK proof.");
    println!("  The proof proves: 'I hold a valid token chain issued by a trusted");
    println!("  federation member, which after Datalog evaluation authorizes this");
    println!("  specific request.' No facts, no capabilities, no identity revealed.");
    println!("  Latency: ~500ms (full multi-step derivation proof).\n");

    let private_result = cclerk.authorize(&attenuated, &request, VerificationMode::FullyPrivate);

    match private_result {
        Ok(AuthorizationPresentation::Private { proof, conclusion }) => {
            println!(
                "  [RESULT: {}]\n",
                if conclusion { "ALLOW" } else { "DENY" }
            );
            println!("  What the verifier LEARNS:");
            println!("  +---------------------------------------------------------+");
            println!(
                "  | Conclusion: {:<45} |",
                if conclusion { "ALLOW" } else { "DENY" }
            );
            println!(
                "  | STARK proof: {} bytes{}",
                proof.len(),
                " ".repeat(33usize.saturating_sub(proof.len().to_string().len()))
            );
            println!("  | (That's it. One bit of authorization + proof of validity.) |");
            println!("  +---------------------------------------------------------+");
            println!();
            println!("  What remains HIDDEN (everything else):");
            println!("    - Which app was authorized -- HIDDEN");
            println!("    - What actions are permitted -- HIDDEN");
            println!("    - Who the user is -- HIDDEN");
            println!("    - What features/clearance levels exist -- HIDDEN");
            println!("    - When the token expires -- HIDDEN");
            println!("    - How many attenuation steps in the chain -- HIDDEN");
            println!("    - Which issuer created the root token -- HIDDEN");
            println!("    - Which Datalog rules fired -- HIDDEN");
            println!("    - How many facts are in the token -- HIDDEN");
            println!();
            println!("  The verifier trusts ONLY the cryptographic proof. The STARK");
            println!("  guarantees that a valid token chain exists, was issued by a");
            println!("  federation member, and its Datalog evaluation concluded ALLOW");
            println!("  for the given request — without revealing ANY of the above.");
            println!();
        }
        Ok(_) => unreachable!("Private mode returns Private variant"),
        Err(e) => {
            println!("  [RESULT: ERROR] {:?}\n", e);
        }
    }

    // =========================================================================
    // SUMMARY: Comparison table
    // =========================================================================
    println!("=======================================================================");
    println!("  SUMMARY: What each mode reveals");
    println!("=======================================================================\n");
    println!("  Property              | Trusted | Selective | Private");
    println!("  ----------------------|---------|-----------|--------");
    println!("  Allow/Deny conclusion |   YES   |    YES    |   YES");
    println!("  STARK proof           |   NO    |    YES    |   YES");
    println!("  App name (deployments)|   YES   |  CHOSEN   |   NO");
    println!("  Action (read)         |   YES   |  CHOSEN   |   NO");
    println!("  User (agent-007)      |   YES   |    NO     |   NO");
    println!("  Clearance level       |   YES   |    NO     |   NO");
    println!("  Budget allocation     |   YES   |    NO     |   NO");
    println!("  Expiration time       |   YES   |    NO     |   NO");
    println!("  Full capability set   |   YES   |    NO     |   NO");
    println!("  Derivation trace      |   YES   |    NO     |   NO");
    println!("  Chain length          |   YES   |    NO     |   NO");
    println!("  Issuer identity       |   YES   |    NO     |   NO");
    println!();
    println!("  Use cases:");
    println!("    Trusted   -> Internal services (same trust domain, fastest)");
    println!("    Selective -> Cross-org APIs (show you have app access, hide user)");
    println!("    Private   -> Anonymous credentials (prove auth without identity)");
    println!();
    println!("=== Progressive Disclosure Demo Complete ===");
}
