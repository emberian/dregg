//! Shared test helpers for sdk integration tests.
//!
//! Consolidates mock-receipt construction and cipherclerk setup so each test
//! file does not duplicate the same boilerplate.

use pyana_sdk::{AgentCipherclerk, CellId};
use pyana_turn::TurnReceipt;
use zeroize::Zeroizing;

/// Build a deterministic `AgentCipherclerk` from a label string.
/// Each unique label produces a distinct identity.
pub fn cclerk_from_label(label: &str) -> AgentCipherclerk {
    let key = *blake3::hash(format!("test-cclerk:{label}").as_bytes()).as_bytes();
    AgentCipherclerk::from_key_bytes(Zeroizing::new(key))
}

/// Build a minimal `TurnReceipt` suitable for chain tests.
///
/// The `previous_receipt_hash` field is left as `None` so that `append_receipt`
/// accepts it as a genesis receipt (or the first in a chain). For non-genesis
/// positions, callers must set the correct `previous_receipt_hash` before
/// passing to `append_receipt` — strict mode rejects mismatched values
/// (audit #77 fix).
pub fn mock_receipt(agent: CellId, pre_state: [u8; 32], post_state: [u8; 32]) -> TurnReceipt {
    TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: pre_state,
        post_state_hash: post_state,
        timestamp: 1000,
        effects_hash: [0u8; 32],
        computrons_used: 50,
        action_count: 1,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
    }
}

/// Build a mock receipt with a specific `previous_receipt_hash` already set.
///
/// Used to test what happens when the caller supplies a deliberately
/// wrong `previous_receipt_hash` before passing to `append_receipt`.
pub fn mock_receipt_with_prev(
    agent: CellId,
    pre_state: [u8; 32],
    post_state: [u8; 32],
    prev: Option<[u8; 32]>,
) -> TurnReceipt {
    let mut r = mock_receipt(agent, pre_state, post_state);
    r.previous_receipt_hash = prev;
    r
}
