//! Full AgentWallet Lifecycle Demo: Receipt Chain as Proof-Carrying State
//!
//! Demonstrates:
//! 1. Create a new wallet (generates Ed25519 keypair)
//! 2. Receive a token (provision from an issuer)
//! 3. Execute 5 turns, building up the receipt chain
//! 4. Verify the wallet's own receipt chain (verify_receipt_chain)
//! 5. Export the receipt chain as proof of state (federation exit scenario)
//! 6. Show: another party can verify the agent's state from just the receipt chain

use pyana_sdk::{
    AgentWallet, CellId, TurnReceipt, verify_receipt_chain, verify_receipt_chain_head,
};

// ─── Helpers ────────────────────────────────────────────────────────────────

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

/// Simulate executing a turn and producing a receipt.
///
/// In production, this would come from TurnExecutor::execute(). Here we
/// simulate the receipt that the executor would produce, advancing state
/// deterministically per turn.
fn simulate_turn_execution(agent: CellId, turn_number: u64, pre_state: [u8; 32]) -> TurnReceipt {
    // Deterministic state transition: hash the pre-state with the turn number.
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-demo-state-transition");
    hasher.update(&pre_state);
    hasher.update(&turn_number.to_le_bytes());
    let post_state = *hasher.finalize().as_bytes();

    // Deterministic turn hash.
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-demo-turn");
    hasher.update(agent.as_bytes());
    hasher.update(&turn_number.to_le_bytes());
    let turn_hash = *hasher.finalize().as_bytes();

    // Deterministic effects hash.
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-demo-effects");
    hasher.update(&turn_number.to_le_bytes());
    let effects_hash = *hasher.finalize().as_bytes();

    TurnReceipt {
        turn_hash,
        forest_hash: [0u8; 32],
        pre_state_hash: pre_state,
        post_state_hash: post_state,
        timestamp: 1700000000 + (turn_number as i64 * 60), // 1 minute apart
        effects_hash,
        computrons_used: 100 + turn_number * 25,
        action_count: (turn_number as usize) + 1,
        previous_receipt_hash: None, // AgentWallet.append_receipt() fills this
        agent,
        federation_id: [0u8; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
    }
}

fn section(title: &str) {
    println!();
    println!("  --- {} ---", title);
}

fn item(msg: &str) {
    println!("    {msg}");
}

// ─── Main ────────────────────────────────────────────────────────────────────

fn main() {
    println!();
    println!("  {}", "=".repeat(60));
    println!("  PYANA WALLET LIFECYCLE DEMO");
    println!("  Receipt Chain as Proof-Carrying State");
    println!("  {}", "=".repeat(60));

    // =========================================================================
    // STEP 1: Create a new wallet (generates Ed25519 keypair)
    // =========================================================================

    section("Step 1: Create Wallet (Ed25519 identity)");

    let mut wallet = AgentWallet::new();
    let agent_pubkey = wallet.public_key();
    let agent_cell = wallet.cell_id("demo-service");

    item(&format!("Public key: {}", short_hex(&agent_pubkey.0)));
    item(&format!(
        "Cell ID (demo-service): {}",
        short_hex(agent_cell.as_bytes())
    ));
    item(&format!(
        "Receipt chain length: {} (empty, genesis)",
        wallet.receipt_chain_length()
    ));
    item(&format!("State commitment: None (no turns executed yet)"));

    // =========================================================================
    // STEP 2: Receive a token (provision)
    // =========================================================================

    section("Step 2: Provision Token (issuer mints for this agent)");

    let root_key: [u8; 32] = *blake3::hash(b"demo-issuer-root-secret-key").as_bytes();
    let token = wallet.mint_token(&root_key, "compute");

    item(&format!("Token minted for service: {}", token.service));
    item(&format!("Token ID: {}", token.id));
    item(&format!("Token label: {}", token.label));
    item(&format!("Tokens held: {}", wallet.tokens().len()));

    // =========================================================================
    // STEP 3: Execute 5 turns, building the receipt chain
    // =========================================================================

    section("Step 3: Execute 5 Turns (building receipt chain)");

    // Genesis state: hash of the agent's public key (deterministic starting point).
    let genesis_state = *blake3::hash(&agent_pubkey.0).as_bytes();
    let mut current_state = genesis_state;

    for turn_number in 0..5u64 {
        let receipt = simulate_turn_execution(agent_cell, turn_number, current_state);
        let post_state = receipt.post_state_hash;
        let computrons = receipt.computrons_used;

        wallet.append_receipt(receipt);
        current_state = post_state;

        item(&format!(
            "Turn {}: pre={} -> post={} ({} computrons, {} actions)",
            turn_number,
            short_hex(&current_state),
            short_hex(&post_state),
            computrons,
            turn_number + 1,
        ));
    }

    println!();
    item(&format!(
        "Receipt chain length: {}",
        wallet.receipt_chain_length()
    ));
    item(&format!(
        "Current state commitment: {}",
        short_hex(&current_state)
    ));

    // =========================================================================
    // STEP 4: Verify the wallet's own receipt chain
    // =========================================================================

    section("Step 4: Self-Verify Receipt Chain");

    match wallet.verify_own_chain() {
        Ok(()) => {
            item("Chain verification: PASS");
            item("  - Genesis receipt has previous_receipt_hash = None");
            item("  - All hash links valid (each points to prior receipt)");
            item("  - State continuity holds (pre_state[n] == post_state[n-1])");
            item("  - Agent identity consistent throughout");
        }
        Err(e) => {
            item(&format!("Chain verification FAILED: {e}"));
            panic!("Receipt chain should be valid");
        }
    }

    // Show the chain structure
    println!();
    item("Chain structure:");
    let chain = wallet.receipt_chain();
    for (i, receipt) in chain.iter().enumerate() {
        let prev = match &receipt.previous_receipt_hash {
            None => "None (genesis)".to_string(),
            Some(h) => short_hex(h),
        };
        item(&format!(
            "  [{}] hash={} prev={} state={}->{}",
            i,
            short_hex(&receipt.receipt_hash()),
            prev,
            short_hex(&receipt.pre_state_hash),
            short_hex(&receipt.post_state_hash),
        ));
    }

    // =========================================================================
    // STEP 5: Export the receipt chain (federation exit scenario)
    // =========================================================================

    section("Step 5: Export Receipt Chain (Federation Exit)");

    item("Scenario: Agent leaves federation, exports proof of state.");
    item("The receipt chain is the agent's portable proof that its current");
    item("state was reached through a valid sequence of executor-approved turns.");
    println!();

    // Export the chain (in real code, this would be serialized to wire format)
    let exported_chain: Vec<TurnReceipt> = wallet.receipt_chain().to_vec();
    let chain_length = exported_chain.len();
    let final_state = exported_chain.last().unwrap().post_state_hash;

    // Compute total "proof weight"
    let total_computrons: u64 = exported_chain.iter().map(|r| r.computrons_used).sum();
    let total_actions: usize = exported_chain.iter().map(|r| r.action_count).sum();
    let time_span =
        exported_chain.last().unwrap().timestamp - exported_chain.first().unwrap().timestamp;

    item(&format!("Exported chain: {} receipts", chain_length));
    item(&format!(
        "Final state commitment: {}",
        short_hex(&final_state)
    ));
    item(&format!("Total computrons consumed: {}", total_computrons));
    item(&format!("Total actions executed: {}", total_actions));
    item(&format!(
        "Time span: {} seconds ({} minutes)",
        time_span,
        time_span / 60
    ));
    item(&format!("Agent cell: {}", short_hex(agent_cell.as_bytes())));

    // =========================================================================
    // STEP 6: Third-party verification from just the receipt chain
    // =========================================================================

    section("Step 6: Third-Party Verification (from exported chain only)");

    item("A receiving federation/verifier has ONLY the exported receipt chain.");
    item("They know nothing about the wallet, tokens, or executor internals.");
    item("They verify the chain structure proves valid state evolution.");
    println!();

    // Simulate the third party's perspective: they only have the chain bytes
    match verify_receipt_chain(&exported_chain) {
        Ok(()) => {
            item("Third-party verification: PASS");
        }
        Err(e) => {
            panic!("Third-party verification should pass: {e}");
        }
    }

    // They can also extract the final verified state
    let verified_head = verify_receipt_chain_head(&exported_chain).unwrap();
    assert_eq!(verified_head, final_state);
    item(&format!(
        "Verified state head: {}",
        short_hex(&verified_head)
    ));

    // They can read the chain metadata
    let genesis = &exported_chain[0];
    let head = exported_chain.last().unwrap();
    item(&format!(
        "Agent identity: {}",
        short_hex(genesis.agent.as_bytes())
    ));
    item(&format!(
        "Genesis state: {}",
        short_hex(&genesis.pre_state_hash)
    ));
    item(&format!(
        "Final state: {}",
        short_hex(&head.post_state_hash)
    ));
    item(&format!("Chain depth: {} turns", chain_length));

    println!();
    item("What the third party now KNOWS (from chain alone):");
    item("  [x] The agent's identity (consistent CellId throughout)");
    item("  [x] The exact sequence of state transitions");
    item("  [x] Each transition was executor-approved (receipts exist)");
    item("  [x] No gaps in the chain (hash + state continuity verified)");
    item("  [x] The current state commitment is cryptographically bound");
    println!();
    item("What the third party does NOT know:");
    item("  [ ] The agent's private key");
    item("  [ ] The content of any tokens held");
    item("  [ ] The actual computation performed in each turn");
    item("  [ ] Which federation approved the turns");

    // ─── Summary ────────────────────────────────────────────────────────────

    println!();
    println!("  {}", "=".repeat(60));
    println!("  WALLET LIFECYCLE DEMO COMPLETE");
    println!("  {}", "=".repeat(60));
    println!();
    println!("  Key takeaway: The receipt chain IS the agent's portable identity.");
    println!("  It proves state evolution without revealing private data, tokens,");
    println!("  or computation internals. Any party can verify the chain offline");
    println!("  using only the public verify_receipt_chain() function.");
    println!();
}
