//! Hello, receipt chain — the smallest agent-to-agent receipt-chain primitive.
//!
//! GitHub issue #3 asked for a minimal demonstration of the receipt-chain
//! primitive in isolation (the `two-ai-handoff` demo is the full production
//! reference; this is the "what does a dregg receipt actually look like" demo).
//!
//! It shows the whole loop with no moving parts beyond the SDK:
//!   1. create an agent (a fresh Ed25519 identity + its cell in a local ledger),
//!   2. submit ONE turn carrying a single `Effect::SetField`,
//!   3. get back a `TurnReceipt`, printed as JSON — this is the exact shape an
//!      external team should pin a dregg-compatible shim to,
//!   4. read the agent's receipt chain (one entry, whose `receipt_hash` is the
//!      tip and becomes the next turn's `previous_receipt_hash`).
//!
//! Run:
//!   cargo run -p dregg-sdk --example hello_receipt_chain

use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};

fn main() {
    // 1. Create an agent. `AgentRuntime` wraps the cipherclerk, a local in-memory
    //    ledger seeded with this agent's cell, and a `TurnExecutor`.
    let cclerk = AgentCipherclerk::new();
    let runtime = AgentRuntime::new_simple(cclerk, "hello");
    println!("agent cell id: {}", runtime.cell_id());

    // 2. Submit ONE turn with a single effect: set state slot 0.
    //    A cell has 8 state slots (indices 0..=7), each a 32-byte field element.
    //    Numeric values live in the low bytes (big-endian), so 42 -> last byte.
    let mut value = [0u8; 32];
    value[31] = 42;

    let receipt = runtime
        .execute(vec![Effect::SetField {
            cell: runtime.cell_id(),
            index: 0,
            value,
        }])
        .expect("a SetField turn on the agent's own cell should commit");

    // 3. The receipt. This struct (serialized here as JSON) is dregg's canonical
    //    proof-of-execution shape: turn/effects hashes, pre/post state roots, the
    //    agent cell id, federation id, and the chain link `previous_receipt_hash`.
    println!("\n--- TurnReceipt (JSON) ---");
    println!("{}", serde_json::to_string_pretty(&receipt).unwrap());

    // 4. The receipt chain. After one turn it holds exactly one entry. Each
    //    entry's `receipt_hash()` is the tip; the next turn's
    //    `previous_receipt_hash` points back to it, forming the hash chain.
    let cclerk = runtime.cipherclerk().read().unwrap();
    let chain = cclerk.receipt_chain();
    println!("\n--- Receipt chain (len {}) ---", chain.len());
    for (i, r) in chain.iter().enumerate() {
        println!(
            "  [{i}] turn_hash={}  receipt_hash={}  previous={}",
            short(&r.turn_hash),
            short(&r.receipt_hash()),
            match r.previous_receipt_hash {
                Some(h) => short(&h),
                None => "(genesis)".to_string(),
            },
        );
    }
}

/// First 6 bytes of a 32-byte hash, hex-encoded, for compact display.
fn short(bytes: &[u8; 32]) -> String {
    bytes[..6].iter().map(|b| format!("{b:02x}")).collect()
}
