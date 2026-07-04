//! Exhaustive schedule exploration of the SPSC ring under loom.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p ring-twin --release
//! ```
//!
//! Loom explores every thread interleaving (up to its preemption bound, when
//! one is set below) and every C11-permitted read of each atomic. A lost
//! wakeup manifests as a detected deadlock — a future returns `Pending` with
//! no wake in flight and `loom::future::block_on` has nothing to run — so
//! the properties here are checked *by termination* as much as by the final
//! assertions.

#![cfg(loom)]

use loom::future::block_on;
use loom::thread;
use ring_twin::{PushError, channel};

/// Bounded model for the multi-item streams: the async send/recv paths run
/// several waker registrations and `SeqCst` fences per item, and unbounded
/// exploration of those models does not converge in reasonable time. A
/// preemption bound of 3 (loom's guidance: most concurrency bugs fall to
/// bound 2) keeps them tractable; the single-item close/park models and the
/// litmus below stay fully exhaustive.
fn model_bounded(f: impl Fn() + Send + Sync + 'static) {
    let mut builder = loom::model::Builder::new();
    builder.preemption_bound = Some(3);
    builder.check(f);
}

/// Item conservation + order on the tightest ring: capacity 1, two items.
/// Every send/recv crosses both the full edge (second push finds the ring
/// full and parks) and the empty edge (recv on the not-yet-pushed item
/// parks), so both waker directions and both check-register-recheck paths
/// are inside the explored state space.
#[test]
fn conservation_capacity_1() {
    model_bounded(|| {
        let (tx, mut rx) = channel::<u32>(1);
        let producer = thread::spawn(move || {
            block_on(async move {
                for i in 0..2u32 {
                    tx.send(i).await.expect("ring never closes in this test");
                }
            });
        });
        let received = block_on(async move {
            let mut out = Vec::new();
            for _ in 0..2 {
                out.push(rx.recv().await.expect("producer sends exactly 2"));
            }
            out
        });
        producer.join().unwrap();
        // Exactly once, in order: nothing lost, nothing duplicated.
        assert_eq!(received, vec![0, 1]);
    });
}

/// Same property with capacity 2 and three items: exercises the masked
/// wraparound of the free-running counters (slot reuse) while both edges
/// remain reachable.
#[test]
fn conservation_capacity_2_wraparound() {
    model_bounded(|| {
        let (tx, mut rx) = channel::<u32>(2);
        let producer = thread::spawn(move || {
            block_on(async move {
                for i in 0..3u32 {
                    tx.send(i).await.expect("ring never closes in this test");
                }
            });
        });
        let received = block_on(async move {
            let mut out = Vec::new();
            for _ in 0..3 {
                out.push(rx.recv().await.expect("producer sends exactly 3"));
            }
            out
        });
        producer.join().unwrap();
        assert_eq!(received, vec![0, 1, 2]);
    });
}

/// Close visibility, producer-side close: the receiver drains everything
/// published before the close, then observes `None`; a post-close push
/// fails. The receiver may be parked on the empty edge when the close
/// arrives, so this also checks that `close()` cannot lose the wake.
#[test]
fn close_after_send_drains_then_none() {
    model_bounded(|| {
        let (tx, mut rx) = channel::<u32>(2);
        let producer = thread::spawn(move || {
            block_on(async move {
                tx.send(7).await.expect("open");
                tx.close();
                // Post-close send fails and hands the value back.
                assert_eq!(tx.try_push(8), Err(PushError::Closed(8)));
            });
        });
        let received = block_on(async move {
            let mut out = Vec::new();
            while let Some(v) = rx.recv().await {
                out.push(v);
            }
            out
        });
        producer.join().unwrap();
        assert_eq!(received, vec![7], "item published before close is delivered");
    });
}

/// Close visibility, receiver-side close: a producer parked on the full
/// edge must be woken by the receiver's close and fail with `Closed`,
/// not sleep forever.
#[test]
fn close_wakes_sender_parked_on_full() {
    loom::model(|| {
        let (tx, rx) = channel::<u32>(1);
        tx.try_push(1).expect("empty ring accepts one item");
        let producer = thread::spawn(move || {
            block_on(async move {
                // Ring is full and the receiver never pops: the only exit
                // is the close waking us.
                let err = tx.send(2).await.expect_err("receiver closes");
                assert_eq!(err, PushError::Closed(2));
            });
        });
        rx.close();
        producer.join().unwrap();
        drop(rx); // ring drop reclaims the undrained item
    });
}

/// Close visibility, empty ring: a receiver parked on the empty edge is
/// woken by a close with nothing in flight and resolves to `None`.
#[test]
fn close_wakes_receiver_parked_on_empty() {
    loom::model(|| {
        let (tx, mut rx) = channel::<u32>(1);
        let consumer = thread::spawn(move || {
            block_on(async move {
                assert_eq!(rx.recv().await, None, "closed with nothing sent");
            });
        });
        tx.close();
        consumer.join().unwrap();
    });
}

/// Litmus: the check-register-recheck handoff built from Release/Acquire
/// alone admits the store-buffering outcome — BOTH the notifier's flag
/// check and the waiter's re-check read stale values, which is exactly the
/// lost-wakeup interleaving. This test asserts loom *finds* that outcome,
/// which is (a) why `WakeCell` carries `SeqCst` fences and (b) evidence
/// that the green tests above are meaningful: loom would have caught a
/// fence-free implementation.
#[test]
fn release_acquire_handoff_admits_store_buffering() {
    use loom::sync::Arc;
    use loom::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::atomic::{AtomicBool as StdAtomicBool, Ordering as StdOrdering};

    static LOST_WAKEUP_REACHED: StdAtomicBool = StdAtomicBool::new(false);

    loom::model(|| {
        let flag = Arc::new(AtomicUsize::new(0)); // "has_waker"
        let cond = Arc::new(AtomicUsize::new(0)); // "tail"
        let notifier = {
            let flag = flag.clone();
            let cond = cond.clone();
            thread::spawn(move || {
                cond.store(1, Ordering::Release); // publish the item
                flag.load(Ordering::Acquire) // wake only if a waiter is seen
            })
        };
        // Waiter: register, then re-check.
        flag.store(1, Ordering::Release);
        let recheck = cond.load(Ordering::Acquire);
        let wake_check = notifier.join().unwrap();
        if recheck == 0 && wake_check == 0 {
            // Waiter saw nothing and will sleep; notifier saw no waiter and
            // will not wake: the wakeup is lost.
            LOST_WAKEUP_REACHED.store(true, StdOrdering::Relaxed);
        }
    });

    assert!(
        LOST_WAKEUP_REACHED.load(StdOrdering::Relaxed),
        "loom explored the store-buffering outcome for the Release/Acquire-only \
         handoff; if this stops firing, the green ring tests no longer witness \
         fence necessity"
    );
}
