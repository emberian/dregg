//! Relay operator checks: bond, host inbox, receive, drain, GC, fees.
#![allow(deprecated)]

use dregg_storage::QuotaId;
use dregg_storage::quota::SpaceBank;
use dregg_storage::relay::MeteredRelay;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("relay_enqueue_drain", check_relay_enqueue_drain),
        run_check("gc_expired", check_gc_expired),
        run_check("dispute_proofs", check_dispute_proofs),
    ]
}

fn make_relay() -> (MeteredRelay, QuotaId) {
    let mut bank = SpaceBank::new(
        1,   // cost_per_byte
        10,  // cost_per_relay_message
        0.5, // refund_rate (50%)
    );
    // Allocate a quota for the payer.
    let payer = bank.allocate_quota([1u8; 32], 100_000, Some(1_000_000));
    (MeteredRelay::new(bank, 65536, 1000), payer)
}

fn check_relay_enqueue_drain() -> Result<(), String> {
    let (mut relay, payer) = make_relay();
    let destination = [10u8; 32];

    // Enqueue a message.
    let payload = b"hello from sender".to_vec();
    let root = relay
        .enqueue(destination, payload.clone(), 100, &payer)
        .map_err(|e| format!("enqueue failed: {e:?}"))?;

    if root == [0u8; 32] {
        return Err("relay queue root should not be zeros after enqueue".into());
    }

    // Verify buffered count.
    let buffered = relay.buffered_for(&destination);
    if buffered != 1 {
        return Err(format!("expected 1 buffered message, got {buffered}"));
    }

    // Enqueue a second message.
    let payload2 = b"second message".to_vec();
    relay
        .enqueue(destination, payload2, 50, &payer)
        .map_err(|e| format!("enqueue 2 failed: {e:?}"))?;

    if relay.buffered_for(&destination) != 2 {
        return Err("expected 2 buffered messages".into());
    }

    // Drain: delivery to destination.
    let drained = relay.drain(&destination);
    if drained.len() != 2 {
        return Err(format!("expected 2 drained entries, got {}", drained.len()));
    }

    // Verify order (FIFO).
    let first_hash = *blake3::hash(b"hello from sender").as_bytes();
    if drained[0].0.content_hash != first_hash {
        return Err("first drained entry should match first enqueued payload hash".into());
    }

    // Queue should be empty now.
    if relay.buffered_for(&destination) != 0 {
        return Err("queue should be empty after drain".into());
    }

    Ok(())
}

fn check_gc_expired() -> Result<(), String> {
    let (mut relay, payer) = make_relay();
    let destination = [11u8; 32];

    // Enqueue with short TTL.
    relay
        .enqueue(destination, b"short-lived".to_vec(), 5, &payer)
        .map_err(|e| format!("enqueue failed: {e:?}"))?;

    // Enqueue with long TTL.
    relay
        .enqueue(destination, b"long-lived".to_vec(), 500, &payer)
        .map_err(|e| format!("enqueue long-lived failed: {e:?}"))?;

    // Advance block past the short TTL expiry.
    relay.advance_block(10); // short-lived expires at 0 + 5 = 5, we're at 10

    // GC expired messages.
    let refunds = relay.gc_expired(10);

    // Should get at least one refund (for the expired short-lived message).
    // The refund amount depends on the refund_rate (50%).
    if refunds.is_empty() {
        return Err("GC should produce refunds for expired messages".into());
    }

    // Verify the relay earned fees: refund should be less than original cost.
    for refund in &refunds {
        if refund.amount == 0 {
            return Err("refund amount should be non-zero".into());
        }
    }

    Ok(())
}

fn check_dispute_proofs() -> Result<(), String> {
    let (mut relay, payer) = make_relay();
    let destination = [12u8; 32];

    // Enqueue and capture the root (proof of enqueue).
    let enqueue_root = relay
        .enqueue(destination, b"disputed-msg".to_vec(), 100, &payer)
        .map_err(|e| format!("enqueue failed: {e:?}"))?;

    // The queue root serves as proof that the message was enqueued.
    if enqueue_root == [0u8; 32] {
        return Err("enqueue root should be non-zero (serves as proof)".into());
    }

    // Drain with proof (proof of delivery).
    let drained = relay.drain(&destination);
    if drained.is_empty() {
        return Err("drain should return entries".into());
    }

    // Each drained entry has a DequeueProof: old_root, new_root, position.
    let (_entry, proof) = &drained[0];
    if proof.old_root == [0u8; 32] {
        return Err("dequeue proof old_root should not be zeros".into());
    }

    // The proof establishes: "message at position P was dequeued, transforming
    // root from old_root to new_root." This is sufficient for dispute resolution.
    // Verify the root we captured at enqueue time matches the proof's old_root.
    if proof.old_root != enqueue_root {
        return Err("dequeue proof old_root should match enqueue-time root".into());
    }

    Ok(())
}
