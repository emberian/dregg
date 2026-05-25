//! Agent SDK demonstration: full lifecycle of token management, delegation,
//! turn execution, and proof generation.
//!
//! This example shows the core workflow an agent goes through:
//! 1. Create a cipherclerk (identity)
//! 2. Mint a root authorization token
//! 3. Attenuate it for a specific task
//! 4. Delegate to a sub-agent
//! 5. Sub-agent verifies its authorization
//! 6. Sub-agent executes a turn using the capability
//! 7. Print the full audit trail

use pyana_sdk::{AgentCipherclerk, AgentRuntime, Attenuation, AuthRequest, Effect};
use std::sync::{Arc, RwLock};

fn main() {
    println!("=== Pyana Agent SDK Demo ===\n");

    // -------------------------------------------------------------------------
    // Step 1: Create an agent cipherclerk with a fresh Ed25519 identity.
    // -------------------------------------------------------------------------
    let mut cclerk = AgentCipherclerk::new();
    println!("[1] Created agent cclerk");
    println!("    Public key: {}", cclerk.public_key());
    println!(
        "    Cell ID (compute domain): {}\n",
        cclerk.cell_id("compute")
    );

    // -------------------------------------------------------------------------
    // Step 2: Mint a root token for the "compute" service.
    // -------------------------------------------------------------------------
    let root_key: [u8; 32] = {
        let mut k = [0u8; 32];
        getrandom::fill(&mut k).unwrap();
        k
    };
    let root_token = cclerk.mint_token(&root_key, "compute");
    println!("[2] Minted root token");
    println!("    Label: {}", root_token.label());
    println!("    Service: {}", root_token.service());
    println!("    ID: {}\n", root_token.id());

    // Verify the root token works for any request (unrestricted).
    let unrestricted_request = AuthRequest {
        service: Some("compute".into()),
        action: Some("execute".into()),
        ..Default::default()
    };
    assert!(cclerk.verify_token(&root_token, &unrestricted_request));
    println!("    [OK] Root token verifies for unrestricted compute access\n");

    // -------------------------------------------------------------------------
    // Step 3: Attenuate the token for a specific task (app: monitoring, read-only).
    // -------------------------------------------------------------------------
    let app_restrictions = Attenuation {
        apps: vec![("monitoring".into(), "r".into())],
        ..Default::default()
    };

    let restricted_token = cclerk.attenuate(&root_token, &app_restrictions).unwrap();
    println!("[3] Attenuated token for monitoring read-only");
    println!("    Label: {}", restricted_token.label());
    println!("    ID: {}", restricted_token.id());

    // Verify the attenuated token (the HMAC chain is valid regardless of caveats;
    // semantic caveat checking may vary based on the request).
    let monitoring_request = AuthRequest {
        app_id: Some("monitoring".into()),
        action: Some("read".into()),
        ..Default::default()
    };
    let verified = cclerk.verify_token(&restricted_token, &monitoring_request);
    println!(
        "    Verification for app=monitoring, action=read: {}\n",
        verified
    );

    // -------------------------------------------------------------------------
    // Step 4: Delegate to a sub-agent with further restrictions.
    // -------------------------------------------------------------------------
    let sub_restrictions = Attenuation {
        apps: vec![("monitoring-sub".into(), "r".into())],
        ..Default::default()
    };

    let cclerk_arc = Arc::new(RwLock::new(cclerk));
    let runtime = AgentRuntime::new(cclerk_arc.clone(), "compute");
    println!("[4] Created agent runtime");
    println!("    Domain: {}", runtime.domain());
    println!("    Cell ID: {}", runtime.cell_id());
    println!("    Nonce: {}\n", runtime.nonce());

    let sub_agent = runtime
        .spawn_sub_agent(&sub_restrictions, &root_token)
        .unwrap();
    println!("    Spawned sub-agent");
    println!("    Sub-agent public key: {}", sub_agent.public_key());
    println!("    Sub-agent cell ID: {}", sub_agent.cell_id());
    println!("    Sub-agent token: {}\n", sub_agent.token().label());

    // -------------------------------------------------------------------------
    // Step 5: Sub-agent verifies its authorization.
    // -------------------------------------------------------------------------
    let sub_request = AuthRequest {
        app_id: Some("monitoring-sub".into()),
        action: Some("read".into()),
        ..Default::default()
    };
    let can_auth = sub_agent.can_authorize(&sub_request);
    println!("[5] Sub-agent authorization check");
    println!("    Request: app=monitoring-sub, action=read");
    println!("    Authorized: {}\n", can_auth);

    // -------------------------------------------------------------------------
    // Step 6: Sub-agent executes a turn (increment its own nonce).
    // -------------------------------------------------------------------------
    println!("[6] Sub-agent executing turn...");
    let effects = vec![Effect::IncrementNonce {
        cell: sub_agent.cell_id(),
    }];

    match sub_agent.execute(effects) {
        Ok(receipt) => {
            println!("    [OK] Turn committed!");
            println!("    Turn hash: {}", hex(&receipt.turn_hash));
            println!("    Pre-state: {}", hex(&receipt.pre_state_hash));
            println!("    Post-state: {}", hex(&receipt.post_state_hash));
            println!("    Computrons used: {}", receipt.computrons_used);
            println!("    Actions: {}\n", receipt.action_count);
        }
        Err(e) => {
            println!("    [ERR] Turn rejected: {e}\n");
        }
    }

    // -------------------------------------------------------------------------
    // Step 7: Parent agent also executes a turn.
    // -------------------------------------------------------------------------
    println!("[7] Parent agent executing turn...");
    let parent_effects = vec![Effect::IncrementNonce {
        cell: runtime.cell_id(),
    }];

    match runtime.execute(parent_effects) {
        Ok(receipt) => {
            println!("    [OK] Turn committed!");
            println!("    Turn hash: {}", hex(&receipt.turn_hash));
            println!("    Post-state: {}", hex(&receipt.post_state_hash));
            println!("    Computrons used: {}\n", receipt.computrons_used);
        }
        Err(e) => {
            println!("    [ERR] Turn rejected: {e}\n");
        }
    }

    // -------------------------------------------------------------------------
    // Audit Trail Summary
    // -------------------------------------------------------------------------
    println!("=== Audit Trail ===");
    println!(
        "  Parent agent: {}",
        cclerk_arc.read().unwrap().public_key()
    );
    println!("  Sub-agent:    {}", sub_agent.public_key());
    println!("  Domain:       {}", runtime.domain());
    println!("  Root token:   {}", root_token.id());
    println!(
        "  Delegated:    {} -> {}",
        root_token.id(),
        sub_agent.token().id()
    );
    println!("  Restrictions: apps=[monitoring:r], sub-apps=[monitoring-sub:r]");
    println!("  Turns executed: 2 (1 parent, 1 sub-agent)");
    println!("\n=== Demo Complete ===");
}

/// Format a 32-byte hash as short hex (first 8 bytes).
fn hex(bytes: &[u8; 32]) -> String {
    bytes[..8].iter().map(|b| format!("{b:02x}")).collect()
}
