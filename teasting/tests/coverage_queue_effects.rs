//! Executor-driven tests for the QUEUE family of `dregg_turn::Effect` variants.
//!
//! Every test calls `EmbeddedExecutor::submit_action` and asserts on real
//! `TurnReceipt` outcomes or `is_err()`.  No effect is merely constructed and
//! dropped without execution.
//!
//! Coverage: QueueAllocate, QueueEnqueue, QueueDequeue, QueueResize,
//!           QueueAtomicTx, QueuePipelineStep.
//!
//! Key cell-field layout (from apply.rs):
//!   field[0]: capacity (u64 le)
//!   field[1]: current length (u64 le)
//!   field[2]: owner cell id bytes
//!   field[3]: program VK hash (if any)
//!   field[4]: tail message hash (most recently enqueued)
//!   field[5]: authorized writer (all-zero = open)
//!   field[6]: head message hash (earliest; set on 0→1 transition)
//!
//! After QueueAllocate commits successfully the queue cell exists in the
//! ledger with the above layout.  Subsequent tests read field[0..=6] via
//! `with_ledger_mut` to assert observable state.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor, Effect};
use dregg_turn::QueueTxOp;

// ── Helpers ──────────────────────────────────────────────────────────────────

fn fresh_agent(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [seed; 32])
}

fn fresh_executor(cc: &AppCipherclerk) -> EmbeddedExecutor {
    EmbeddedExecutor::new(cc, "default")
}

fn blake3_field(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

/// Read a u64 stored as little-endian in the first 8 bytes of a field element.
fn read_u64_field(field: [u8; 32]) -> u64 {
    u64::from_le_bytes(field[..8].try_into().unwrap())
}

/// Derive the queue cell ID the same way apply_queue_allocate does.
///
/// IMPORTANT: `apply_queue_allocate` reads `actor.state.nonce()` during Phase 2
/// (call-forest execution), which is AFTER Phase 1 has already incremented the
/// agent's nonce by 1.  So if the cell's nonce before submission was N,
/// the value seen inside `apply_queue_allocate` is N+1.
///
/// Callers must pass `nonce_after_phase1 = nonce_before_submit + 1`.
///
/// queue_seed = blake3(actor_id || capacity_le8 || actor_nonce_le8)
/// queue_id   = CellId::derive_raw(queue_seed, [0u8; 32])
fn derive_queue_id(actor_id: &CellId, capacity: u64, nonce_after_phase1: u64) -> CellId {
    let hash = blake3::hash(
        &[
            actor_id.as_bytes().as_slice(),
            &capacity.to_le_bytes(),
            &nonce_after_phase1.to_le_bytes(),
        ]
        .concat(),
    );
    let queue_seed: [u8; 32] = *hash.as_bytes();
    let queue_token = [0u8; 32];
    CellId::derive_raw(&queue_seed, &queue_token)
}

/// Return the actor's current cell-state nonce from the ledger.
/// This is the nonce BEFORE the next turn's Phase 1 increments it.
/// Pass `nonce_before_submit() + 1` to `derive_queue_id`.
fn actor_nonce(executor: &EmbeddedExecutor, actor: &CellId) -> u64 {
    executor.with_ledger_mut(|ledger| {
        ledger.get(actor).map(|c| c.state.nonce()).unwrap_or(0)
    })
}

// ── Test 1: QueueAllocate ────────────────────────────────────────────────────

/// A QueueAllocate effect targeting the actor's own cell must succeed and
/// create a new queue cell with the correct capacity field.
#[test]
fn queue_allocate_creates_queue_cell_with_correct_capacity() {
    let cc = fresh_agent(0xA0);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();
    let capacity: u64 = 8;

    // Nonce before the turn executes. Phase 1 increments it by 1 before
    // apply_queue_allocate reads it, so we pass nonce_before + 1.
    let nonce_before = actor_nonce(&executor, &actor);

    let action = cc.make_action(
        actor,
        "queue.allocate",
        vec![Effect::QueueAllocate {
            capacity,
            program_vk: None,
        }],
    );

    let receipt = executor
        .submit_action(&cc, action)
        .expect("QueueAllocate must be accepted");

    assert_eq!(receipt.action_count, 1, "one action in the turn");

    // Derive what the executor created (nonce_before + 1 = nonce seen by apply).
    let queue_id = derive_queue_id(&actor, capacity, nonce_before + 1);

    // Verify the queue cell was actually created and has the right capacity.
    let (cap_in_cell, len_in_cell, owner_in_cell) =
        executor.with_ledger_mut(|ledger| {
            let qc = ledger
                .get(&queue_id)
                .expect("queue cell must exist after QueueAllocate");
            let cap = read_u64_field(qc.state.fields[0]);
            let len = read_u64_field(qc.state.fields[1]);
            let owner: [u8; 32] = qc.state.fields[2];
            (cap, len, owner)
        });

    assert_eq!(cap_in_cell, capacity, "field[0] must hold the allocated capacity");
    assert_eq!(len_in_cell, 0, "field[1] (length) must start at 0");
    assert_eq!(
        owner_in_cell,
        *actor.as_bytes(),
        "field[2] must record the allocating cell as owner"
    );
}

// ── Test 2: QueueEnqueue ─────────────────────────────────────────────────────

/// After allocating a queue, enqueuing a message must increment field[1]
/// (length) and write the message hash into field[4] (tail) and field[6]
/// (head, because this is the first message).
#[test]
fn queue_enqueue_increments_length_and_sets_tail_and_head() {
    let cc = fresh_agent(0xA1);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();
    let capacity: u64 = 4;

    let nonce_before = actor_nonce(&executor, &actor);

    // Step 1: allocate.
    let alloc = cc.make_action(
        actor,
        "queue.allocate",
        vec![Effect::QueueAllocate { capacity, program_vk: None }],
    );
    executor
        .submit_action(&cc, alloc)
        .expect("QueueAllocate must succeed");

    // nonce_before + 1 = the nonce apply_queue_allocate saw (Phase 1 increments first).
    let queue_id = derive_queue_id(&actor, capacity, nonce_before + 1);
    let msg_hash = blake3_field(b"message-one");

    // Step 2: enqueue one message (deposit = 0 → open queue, actor has balance).
    let enqueue = cc.make_action(
        actor,
        "queue.enqueue",
        vec![Effect::QueueEnqueue {
            queue: queue_id,
            message_hash: msg_hash,
            deposit: 0,
        }],
    );
    let receipt = executor
        .submit_action(&cc, enqueue)
        .expect("QueueEnqueue must be accepted");

    assert_eq!(receipt.action_count, 1);

    // Verify length, tail, and head in the queue cell.
    let (len, tail, head) = executor.with_ledger_mut(|ledger| {
        let qc = ledger.get(&queue_id).expect("queue cell must exist");
        let len = read_u64_field(qc.state.fields[1]);
        let tail = qc.state.fields[4];
        let head = qc.state.fields[6];
        (len, tail, head)
    });

    assert_eq!(len, 1, "length must be 1 after one enqueue");
    assert_eq!(tail, msg_hash, "field[4] (tail) must be the enqueued message hash");
    assert_eq!(
        head, msg_hash,
        "field[6] (head) must be set to message hash on the 0→1 transition"
    );
}

// ── Test 3: QueueDequeue ─────────────────────────────────────────────────────

/// After enqueuing a message, the queue owner dequeuing it must decrement
/// field[1] (length) to 0 and clear field[6] (head) to all-zeros.
#[test]
fn queue_dequeue_decrements_length_and_clears_head_when_empty() {
    let cc = fresh_agent(0xA2);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();
    let capacity: u64 = 2;

    let nonce_before = actor_nonce(&executor, &actor);

    // Allocate.
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate",
                vec![Effect::QueueAllocate { capacity, program_vk: None }],
            ),
        )
        .expect("allocate must succeed");

    // nonce_before + 1: apply_queue_allocate runs after Phase 1 increments nonce.
    let queue_id = derive_queue_id(&actor, capacity, nonce_before + 1);
    let msg = blake3_field(b"dequeue-test-message");

    // Enqueue one message.
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.enqueue",
                vec![Effect::QueueEnqueue { queue: queue_id, message_hash: msg, deposit: 0 }],
            ),
        )
        .expect("enqueue must succeed");

    // Dequeue — action must target the owner cell (action_target == owner).
    let dequeue = cc.make_action(
        actor,
        "queue.dequeue",
        vec![Effect::QueueDequeue { queue: queue_id }],
    );
    let receipt = executor
        .submit_action(&cc, dequeue)
        .expect("QueueDequeue must be accepted");

    assert_eq!(receipt.action_count, 1);

    // Verify the queue is now empty.
    let (len_after, head_after) = executor.with_ledger_mut(|ledger| {
        let qc = ledger.get(&queue_id).expect("queue cell must still exist");
        let len = read_u64_field(qc.state.fields[1]);
        let head = qc.state.fields[6];
        (len, head)
    });

    assert_eq!(len_after, 0, "length must return to 0 after dequeue");
    assert_eq!(
        head_after,
        [0u8; 32],
        "field[6] (head) must be cleared when queue becomes empty"
    );
}

// ── Test 4: QueueResize ──────────────────────────────────────────────────────

/// The queue owner can grow the queue's capacity.  After resize, field[0]
/// must reflect the new capacity.
#[test]
fn queue_resize_grows_capacity_field() {
    let cc = fresh_agent(0xA3);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();
    let initial_capacity: u64 = 4;
    let new_capacity: u64 = 16;

    let nonce_before = actor_nonce(&executor, &actor);

    // Allocate.
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate",
                vec![Effect::QueueAllocate { capacity: initial_capacity, program_vk: None }],
            ),
        )
        .expect("allocate must succeed");

    // nonce_before + 1: Phase 1 increments nonce before apply runs.
    let queue_id = derive_queue_id(&actor, initial_capacity, nonce_before + 1);

    // Resize.
    let resize = cc.make_action(
        actor,
        "queue.resize",
        vec![Effect::QueueResize { queue: queue_id, new_capacity }],
    );
    let receipt = executor
        .submit_action(&cc, resize)
        .expect("QueueResize must be accepted");

    assert_eq!(receipt.action_count, 1);

    let cap_after = executor.with_ledger_mut(|ledger| {
        read_u64_field(ledger.get(&queue_id).expect("queue must exist").state.fields[0])
    });

    assert_eq!(cap_after, new_capacity, "field[0] must reflect new capacity after resize");
}

// ── Test 5: QueueAtomicTx ────────────────────────────────────────────────────

/// An atomic transaction that enqueues onto one queue and dequeues from
/// another must succeed as a unit.  Both state changes are observable after
/// the single receipt commits.
#[test]
fn queue_atomic_tx_enqueue_and_dequeue_both_commit() {
    let cc = fresh_agent(0xA4);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();

    // Allocate two queues.
    let cap_a: u64 = 4;
    let cap_b: u64 = 4;
    // Read nonce BEFORE each submit; add +1 to get nonce seen by apply.
    let nonce_a = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.a",
                vec![Effect::QueueAllocate { capacity: cap_a, program_vk: None }],
            ),
        )
        .expect("allocate queue A");
    let queue_a = derive_queue_id(&actor, cap_a, nonce_a + 1);

    let nonce_b = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.b",
                vec![Effect::QueueAllocate { capacity: cap_b, program_vk: None }],
            ),
        )
        .expect("allocate queue B");
    let queue_b = derive_queue_id(&actor, cap_b, nonce_b + 1);

    // Pre-load queue B with one message so the atomic Dequeue on B has something to consume.
    let msg_b = blake3_field(b"pre-loaded-b");
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.enqueue.b",
                vec![Effect::QueueEnqueue { queue: queue_b, message_hash: msg_b, deposit: 0 }],
            ),
        )
        .expect("pre-load queue B");

    // Atomic Tx: enqueue a message into A and dequeue from B simultaneously.
    let msg_a = blake3_field(b"atomic-enqueue-into-a");
    let atomic = cc.make_action(
        actor,
        "queue.atomic_tx",
        vec![Effect::QueueAtomicTx {
            operations: vec![
                QueueTxOp::Enqueue { queue: queue_a, message_hash: msg_a, deposit: 0 },
                QueueTxOp::Dequeue { queue: queue_b },
            ],
        }],
    );
    let receipt = executor
        .submit_action(&cc, atomic)
        .expect("QueueAtomicTx must be accepted");

    assert_eq!(receipt.action_count, 1);

    // Verify both mutations are committed.
    let (len_a, tail_a, len_b) = executor.with_ledger_mut(|ledger| {
        let qa = ledger.get(&queue_a).expect("queue A must exist");
        let len_a = read_u64_field(qa.state.fields[1]);
        let tail_a = qa.state.fields[4];
        let qb = ledger.get(&queue_b).expect("queue B must exist");
        let len_b = read_u64_field(qb.state.fields[1]);
        (len_a, tail_a, len_b)
    });

    assert_eq!(len_a, 1, "queue A must have one message after atomic enqueue");
    assert_eq!(tail_a, msg_a, "queue A tail must be the atomically enqueued message");
    assert_eq!(len_b, 0, "queue B must be empty after atomic dequeue");
}

// ── Test 6: QueuePipelineStep ─────────────────────────────────────────────────

/// A pipeline step that dequeues from a source queue and fans out to one sink
/// queue must leave the source empty and the sink with one message (the moved
/// message hash in its tail and head fields).
#[test]
fn queue_pipeline_step_moves_message_from_source_to_sink() {
    let cc = fresh_agent(0xA5);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();

    // Allocate source queue.
    let cap_src: u64 = 4;
    let nonce_src = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.src",
                vec![Effect::QueueAllocate { capacity: cap_src, program_vk: None }],
            ),
        )
        .expect("allocate source queue");
    // +1: Phase 1 increments nonce before apply reads it.
    let queue_src = derive_queue_id(&actor, cap_src, nonce_src + 1);

    // Allocate sink queue.
    let cap_sink: u64 = 4;
    let nonce_sink = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.sink",
                vec![Effect::QueueAllocate { capacity: cap_sink, program_vk: None }],
            ),
        )
        .expect("allocate sink queue");
    let queue_sink = derive_queue_id(&actor, cap_sink, nonce_sink + 1);

    // Enqueue one message into the source.
    let msg = blake3_field(b"pipeline-message");
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.enqueue.src",
                vec![Effect::QueueEnqueue { queue: queue_src, message_hash: msg, deposit: 0 }],
            ),
        )
        .expect("enqueue into source must succeed");

    // Pipeline step: dequeue from source, fan out to sink.
    let pipeline_id = blake3_field(b"pipeline-id-v1");
    let step = cc.make_action(
        actor,
        "queue.pipeline_step",
        vec![Effect::QueuePipelineStep {
            pipeline_id,
            source: queue_src,
            sinks: vec![queue_sink],
        }],
    );
    let receipt = executor
        .submit_action(&cc, step)
        .expect("QueuePipelineStep must be accepted");

    assert_eq!(receipt.action_count, 1);

    // Source must be empty; sink must have one message (the moved hash).
    let (src_len, sink_len, sink_tail, sink_head) = executor.with_ledger_mut(|ledger| {
        let src = ledger.get(&queue_src).expect("source queue must exist");
        let src_len = read_u64_field(src.state.fields[1]);

        let sink = ledger.get(&queue_sink).expect("sink queue must exist");
        let sink_len = read_u64_field(sink.state.fields[1]);
        let sink_tail = sink.state.fields[4];
        let sink_head = sink.state.fields[6];

        (src_len, sink_len, sink_tail, sink_head)
    });

    assert_eq!(src_len, 0, "source queue must be empty after pipeline step");
    assert_eq!(sink_len, 1, "sink queue must have one message after pipeline step");
    assert_eq!(sink_tail, msg, "sink tail (field[4]) must be the moved message hash");
    assert_eq!(
        sink_head, msg,
        "sink head (field[6]) must be set to the moved message hash (0→1 transition)"
    );
}

// ── Test 7: QueueDequeue rejected on empty queue ─────────────────────────────

/// Attempting to dequeue from an empty queue must be rejected by the executor.
#[test]
fn queue_dequeue_rejected_when_empty() {
    let cc = fresh_agent(0xA6);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();

    let nonce_before = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate",
                vec![Effect::QueueAllocate { capacity: 4, program_vk: None }],
            ),
        )
        .expect("allocate must succeed");

    let queue_id = derive_queue_id(&actor, 4, nonce_before + 1);

    // No enqueue — try to dequeue from empty queue.
    let result = executor.submit_action(
        &cc,
        cc.make_action(
            actor,
            "queue.dequeue",
            vec![Effect::QueueDequeue { queue: queue_id }],
        ),
    );

    assert!(
        result.is_err(),
        "dequeuing from empty queue must be rejected; got: {result:?}"
    );
}

// ── Test 8: QueueAtomicTx rejected on second dequeue from empty queue ─────────

/// An atomic tx where the second operation tries to dequeue from an empty
/// queue must be rejected atomically — neither the enqueue nor the dequeue
/// should commit.
#[test]
fn queue_atomic_tx_rejected_when_dequeue_target_is_empty() {
    let cc = fresh_agent(0xA7);
    let executor = fresh_executor(&cc);
    let actor = executor.cell_id();

    let cap: u64 = 4;
    let nonce_enq = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.enq",
                vec![Effect::QueueAllocate { capacity: cap, program_vk: None }],
            ),
        )
        .expect("allocate enqueue-target queue");
    let queue_enq = derive_queue_id(&actor, cap, nonce_enq + 1);

    let nonce_deq = actor_nonce(&executor, &actor);
    executor
        .submit_action(
            &cc,
            cc.make_action(
                actor,
                "queue.allocate.deq",
                vec![Effect::QueueAllocate { capacity: cap, program_vk: None }],
            ),
        )
        .expect("allocate dequeue-target (empty) queue");
    let queue_deq = derive_queue_id(&actor, cap, nonce_deq + 1);

    // Atomic Tx: enqueue into queue_enq AND dequeue from queue_deq (empty).
    // The dequeue should fail, rolling back the enqueue too.
    let msg = blake3_field(b"this-should-not-commit");
    let result = executor.submit_action(
        &cc,
        cc.make_action(
            actor,
            "queue.atomic_tx",
            vec![Effect::QueueAtomicTx {
                operations: vec![
                    QueueTxOp::Enqueue { queue: queue_enq, message_hash: msg, deposit: 0 },
                    QueueTxOp::Dequeue { queue: queue_deq },
                ],
            }],
        ),
    );

    assert!(
        result.is_err(),
        "atomic tx with dequeue from empty queue must be rejected; got: {result:?}"
    );

    // Verify the enqueue did not commit (atomicity: both rolled back).
    let len_enq = executor.with_ledger_mut(|ledger| {
        read_u64_field(ledger.get(&queue_enq).expect("queue must exist").state.fields[1])
    });
    assert_eq!(
        len_enq, 0,
        "enqueue side must NOT have committed after atomic tx failure (atomicity)"
    );
}
