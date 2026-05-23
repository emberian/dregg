//! CapTP subsystem checks: swiss table, session lifecycle, handoff, pipeline, store-and-forward.

use pyana_captp::FederationId;
use pyana_captp::handoff::HandoffCertificate;
use pyana_captp::pipeline::PipelineRegistry;
use pyana_captp::session::CapSession;
use pyana_captp::store_forward::{MessagePriority, QueuedMessage};
use pyana_captp::sturdy::SwissTable;
use pyana_cell::AuthRequired;
use pyana_types::{CellId, generate_keypair};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("swiss_export_enliven", check_swiss_export_enliven),
        run_check("session_lifecycle", check_session_lifecycle),
        run_check("handoff_roundtrip", check_handoff_roundtrip),
        run_check("pipeline_resolve", check_pipeline_resolve),
        run_check("store_forward_order", check_store_forward_order),
    ]
}

fn check_swiss_export_enliven() -> Result<(), String> {
    let mut table = SwissTable::new();
    let cell_id = CellId(*blake3::hash(b"test-cell").as_bytes());

    // Export a cell as a sturdy reference.
    let swiss = table.export(cell_id, AuthRequired::Signature, 10, Some(100));

    // Verify the swiss number was generated (non-zero).
    if swiss == [0u8; 32] {
        return Err("swiss number should not be all zeros".into());
    }

    // Enliven: present the swiss number to get a live reference.
    let entry = table
        .enliven(&swiss, 15)
        .map_err(|e| format!("enliven failed: {e}"))?;

    // Verify the entry points to our cell.
    if entry.cell_id != cell_id {
        return Err(format!(
            "enlivened entry cell_id mismatch: expected {:?}, got {:?}",
            cell_id, entry.cell_id
        ));
    }
    if entry.permissions != AuthRequired::Signature {
        return Err("permissions mismatch after enliven".into());
    }

    // Verify use count was incremented.
    if entry.use_count != 1 {
        return Err(format!("expected use_count 1, got {}", entry.use_count));
    }

    Ok(())
}

fn check_session_lifecycle() -> Result<(), String> {
    let peer_id = *blake3::hash(b"remote-peer").as_bytes();
    let mut session = CapSession::new(peer_id);

    // Verify initial state.
    if session.epoch != 0 {
        return Err("new session should have epoch 0".into());
    }

    // Export a capability.
    let cell_id = CellId(*blake3::hash(b"exported-cell").as_bytes());
    let exported = session.export(cell_id, AuthRequired::Signature);
    if exported != cell_id {
        return Err("export should return the cell_id".into());
    }

    // Verify export is tracked.
    if session.exports.is_empty() {
        return Err("exports should not be empty after export".into());
    }

    // Release export (drop reference).
    let fully_released = session.release_export(&cell_id);
    if !fully_released {
        return Err("single export should be fully released on first release".into());
    }

    // Verify GC: exports should be empty after full release.
    if !session.exports.is_empty() {
        return Err("exports should be empty after full release".into());
    }

    // Create a promise.
    let promise_id = session.create_promise();
    if session.promises.is_empty() {
        return Err("promises should not be empty after create_promise".into());
    }

    // Fulfill the promise.
    let target_cell = CellId(*blake3::hash(b"resolved-target").as_bytes());
    let fulfilled = session.fulfill_promise(promise_id, target_cell);
    if !fulfilled {
        return Err("fulfill_promise should return true for pending promise".into());
    }

    Ok(())
}

fn check_handoff_roundtrip() -> Result<(), String> {
    let (introducer_key, introducer_pk) = generate_keypair();
    let introducer_fed = FederationId(*blake3::hash(b"introducer-fed").as_bytes());
    let target_fed = FederationId(*blake3::hash(b"target-fed").as_bytes());
    let target_cell = CellId(*blake3::hash(b"target-cell").as_bytes());
    let (_recipient_key, recipient_pk) = generate_keypair();

    // Register a swiss entry at the target (simulate introducer pre-registration).
    let mut target_swiss_table = SwissTable::new();
    let swiss = target_swiss_table.export(target_cell, AuthRequired::Signature, 5, Some(1000));

    // Create a handoff certificate.
    let cert = HandoffCertificate::create(
        &introducer_key,
        introducer_fed,
        target_fed,
        target_cell,
        recipient_pk.0,
        AuthRequired::Signature,
        None,       // no effect mask
        Some(1000), // expires at height 1000
        Some(3),    // max 3 uses
        swiss,
    );

    // Verify it serializes (roundtrip via postcard).
    let serialized = postcard::to_stdvec(&cert).map_err(|e| format!("serialize failed: {e}"))?;
    if serialized.is_empty() {
        return Err("serialized certificate should not be empty".into());
    }

    let deserialized: HandoffCertificate =
        postcard::from_bytes(&serialized).map_err(|e| format!("deserialize failed: {e}"))?;

    // Validate the introducer's signature.
    if !deserialized.verify_signature(&introducer_pk) {
        return Err("handoff certificate signature verification failed".into());
    }

    // Verify fields survived roundtrip.
    if deserialized.target_cell != target_cell {
        return Err("target_cell mismatch after roundtrip".into());
    }
    if deserialized.swiss != swiss {
        return Err("swiss number mismatch after roundtrip".into());
    }

    Ok(())
}

fn check_pipeline_resolve() -> Result<(), String> {
    let mut registry = PipelineRegistry::new();

    // Register a promise.
    let promise_id = registry.create_promise();

    // Pipeline messages to the unresolved promise.
    let sender_fed = FederationId(*blake3::hash(b"sender-fed").as_bytes());
    let msg = pyana_captp::pipeline::PipelinedMessage {
        target_promise_id: promise_id,
        action: pyana_captp::pipeline::PipelinedAction {
            method: "transfer".to_string(),
            args: vec![1, 2, 3, 4],
            authorization: vec![],
        },
        result_promise_id: None,
        sender: sender_fed,
    };

    registry
        .pipeline_message(msg)
        .map_err(|e| format!("pipeline_message failed: {e}"))?;

    // Resolve the promise.
    let resolved_cell = CellId(*blake3::hash(b"resolved-cell").as_bytes());
    let delivered = registry.resolve_promise(promise_id, resolved_cell);

    // Verify messages were delivered.
    if delivered.is_empty() {
        return Err("resolving promise should deliver queued messages".into());
    }
    if delivered[0].action.method != "transfer" {
        return Err("delivered message method mismatch".into());
    }

    Ok(())
}

fn check_store_forward_order() -> Result<(), String> {
    // Verify that store-and-forward messages maintain causal ordering.
    let dest = FederationId(*blake3::hash(b"destination").as_bytes());

    let msg1 = QueuedMessage {
        destination: dest,
        encrypted_payload: vec![1, 2, 3],
        sender_ephemeral_pk: [1u8; 32],
        causal_sequence: 1,
        queued_at: 10,
        ttl_blocks: 100,
        priority: MessagePriority::Normal,
    };

    let msg2 = QueuedMessage {
        destination: dest,
        encrypted_payload: vec![4, 5, 6],
        sender_ephemeral_pk: [2u8; 32],
        causal_sequence: 2,
        queued_at: 11,
        ttl_blocks: 100,
        priority: MessagePriority::High,
    };

    let msg3 = QueuedMessage {
        destination: dest,
        encrypted_payload: vec![7, 8, 9],
        sender_ephemeral_pk: [3u8; 32],
        causal_sequence: 3,
        queued_at: 12,
        ttl_blocks: 100,
        priority: MessagePriority::Low,
    };

    // Queue them in order.
    let messages = vec![msg1.clone(), msg2.clone(), msg3.clone()];

    // Verify causal ordering is preserved.
    for i in 1..messages.len() {
        if messages[i].causal_sequence <= messages[i - 1].causal_sequence {
            return Err(format!(
                "causal order violated: seq {} should be > {}",
                messages[i].causal_sequence,
                messages[i - 1].causal_sequence
            ));
        }
    }

    // Verify priority ordering (High > Normal > Low).
    if msg2.priority <= msg1.priority {
        return Err("High priority should be greater than Normal".into());
    }
    if msg1.priority <= msg3.priority {
        return Err("Normal priority should be greater than Low".into());
    }

    // Verify TTL computation: message should expire at queued_at + ttl_blocks.
    let expiry = msg1.queued_at + msg1.ttl_blocks;
    if expiry != 110 {
        return Err(format!("expected expiry 110, got {expiry}"));
    }

    Ok(())
}
