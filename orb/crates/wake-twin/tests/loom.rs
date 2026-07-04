//! Exhaustive schedule exploration of the wakeup protocol under loom.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p wake-twin --release
//! ```
//!
//! The doorbell here is a loom-instrumented counting semaphore with **no
//! timeout**, so a missed wakeup is a real deadlock and loom's deadlock
//! detection fails the test. Termination of every explored execution is
//! therefore the no-missed-wakeup property itself.

#![cfg(loom)]

use loom::sync::atomic::{AtomicUsize, Ordering};
use loom::sync::{Arc, Condvar, Mutex};
use wake_twin::{Doorbell, WakeProtocol};

/// Counting-semaphore doorbell (eventfd semantics): `ring` deposits a
/// persistent token, `wait` blocks until one is present and consumes all.
/// Rings are counted (with an uninstrumented counter, so no extra loom
/// state) for the wake-storm assertion.
struct SemBell {
    tokens: Mutex<usize>,
    available: Condvar,
    rings: std::sync::atomic::AtomicUsize,
}

impl SemBell {
    fn new() -> Self {
        SemBell {
            tokens: Mutex::new(0),
            available: Condvar::new(),
            rings: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    fn rings(&self) -> usize {
        self.rings.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl Doorbell for SemBell {
    fn ring(&self) {
        self.rings
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let mut tokens = self.tokens.lock().unwrap();
        *tokens += 1;
        self.available.notify_one();
    }

    fn wait(&self) {
        let mut tokens = self.tokens.lock().unwrap();
        while *tokens == 0 {
            tokens = self.available.wait(tokens).unwrap();
        }
        *tokens = 0;
    }
}

/// The consumer loop: drain (modeled as reading the published-item counter)
/// until `expected` items have been observed, blocking through the protocol
/// when idle. No timeout anywhere — if a publish can be stranded, this
/// deadlocks and loom reports it.
fn consume_until(proto: &WakeProtocol<SemBell>, items: &AtomicUsize, expected: usize) -> usize {
    let mut seen = 0;
    while seen < expected {
        // Clear-before-drain: anything published after this swap re-flags
        // `pending` and is the next round's problem.
        let _ = proto.take_pending();
        // "Drain": observe everything published so far.
        seen = items.load(Ordering::Acquire);
        if seen >= expected {
            break;
        }
        // Nothing (new) found: announce might_block, re-check, maybe block.
        let _ = proto.park_if_idle();
    }
    seen
}

/// NO MISSED WAKEUP, single producer: the producer publishes twice; the
/// consumer must observe both, either via the `pending` re-check before
/// blocking or via a doorbell ring that satisfies its wait. Every explored
/// interleaving must terminate.
#[test]
fn no_missed_wakeup_single_producer() {
    loom::model(|| {
        let proto = Arc::new(WakeProtocol::new(SemBell::new()));
        let items = Arc::new(AtomicUsize::new(0));

        let producer = {
            let proto = proto.clone();
            let items = items.clone();
            loom::thread::spawn(move || {
                for _ in 0..2 {
                    // Publish the work item, then run the protocol.
                    items.fetch_add(1, Ordering::Release);
                    proto.publish();
                }
            })
        };

        let seen = consume_until(&proto, &items, 2);
        producer.join().unwrap();

        assert_eq!(seen, 2, "every publish observed");
        // Coalescing soundness: never more rings than publishes.
        assert!(
            proto.bell().rings() <= 2,
            "wake storm: {} rings for 2 publishes",
            proto.bell().rings()
        );
    });
}

/// NO MISSED WAKEUP, two producers racing each other and the consumer: the
/// `pending` false→true edge is contended, so exactly the coalescing logic
/// (`was_pending` from the swap) decides who rings. Both items must still
/// be observed in every interleaving.
///
/// Three threads plus the fence-heavy protocol make unbounded exploration
/// intractable, so this model runs with a preemption bound of 3 (loom's
/// guidance: most concurrency bugs fall to bound 2). The single-producer
/// variant above stays fully exhaustive.
#[test]
fn no_missed_wakeup_two_producers() {
    let mut builder = loom::model::Builder::new();
    builder.preemption_bound = Some(3);
    builder.check(|| {
        let proto = Arc::new(WakeProtocol::new(SemBell::new()));
        let items = Arc::new(AtomicUsize::new(0));

        let spawn_producer = |proto: &Arc<WakeProtocol<SemBell>>, items: &Arc<AtomicUsize>| {
            let proto = proto.clone();
            let items = items.clone();
            loom::thread::spawn(move || {
                items.fetch_add(1, Ordering::Release);
                proto.publish();
            })
        };
        let p1 = spawn_producer(&proto, &items);
        let p2 = spawn_producer(&proto, &items);

        let seen = consume_until(&proto, &items, 2);
        p1.join().unwrap();
        p2.join().unwrap();

        assert_eq!(seen, 2, "every publish observed");
        assert!(
            proto.bell().rings() <= 2,
            "wake storm: {} rings for 2 publishes",
            proto.bell().rings()
        );
    });
}

/// Litmus: the same protocol with Release/Acquire instead of SeqCst admits
/// the store-buffering outcome — producer sees "consumer not blocking",
/// consumer sees "nothing pending" — i.e. the missed wakeup the SeqCst
/// pairing exists to forbid. Asserting loom reaches it keeps the green
/// tests above honest: loom would catch a weakened implementation.
#[test]
fn release_acquire_variant_admits_missed_wakeup() {
    use std::sync::atomic::{AtomicBool as StdAtomicBool, Ordering as StdOrdering};

    static MISSED: StdAtomicBool = StdAtomicBool::new(false);

    loom::model(|| {
        let pending = Arc::new(AtomicUsize::new(0));
        let might_block = Arc::new(AtomicUsize::new(0));

        let producer = {
            let pending = pending.clone();
            let might_block = might_block.clone();
            loom::thread::spawn(move || {
                pending.store(1, Ordering::Release);
                might_block.load(Ordering::Acquire) // 0 = "won't ring"
            })
        };

        might_block.store(1, Ordering::Release);
        let recheck = pending.load(Ordering::Acquire); // 0 = "will block"
        let producer_saw = producer.join().unwrap();

        if recheck == 0 && producer_saw == 0 {
            MISSED.store(true, StdOrdering::Relaxed);
        }
    });

    assert!(
        MISSED.load(StdOrdering::Relaxed),
        "loom explored the store-buffering outcome for the Release/Acquire \
         variant; if this stops firing, the green tests no longer witness \
         SeqCst necessity"
    );
}
