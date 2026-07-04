//! Non-loom smoke lane: the same protocol, real threads, real condvar
//! doorbell, big publish counts. No timeout anywhere — a missed wakeup
//! hangs this test rather than hiding in a latency spike.

#![cfg(not(loom))]

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use wake_twin::{Doorbell, WakeProtocol};

/// Counting-semaphore doorbell over std primitives (eventfd semantics).
struct SemBell {
    tokens: Mutex<usize>,
    available: Condvar,
    rings: AtomicUsize,
}

impl SemBell {
    fn new() -> Self {
        SemBell {
            tokens: Mutex::new(0),
            available: Condvar::new(),
            rings: AtomicUsize::new(0),
        }
    }
}

impl Doorbell for SemBell {
    fn ring(&self) {
        self.rings.fetch_add(1, Ordering::Relaxed);
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

#[test]
fn no_missed_wakeup_under_stress() {
    const PRODUCERS: usize = 2;
    const PER_PRODUCER: usize = 50_000;
    const TOTAL: usize = PRODUCERS * PER_PRODUCER;

    let proto = Arc::new(WakeProtocol::new(SemBell::new()));
    let items = Arc::new(AtomicUsize::new(0));

    let handles: Vec<_> = (0..PRODUCERS)
        .map(|_| {
            let proto = proto.clone();
            let items = items.clone();
            thread::spawn(move || {
                for _ in 0..PER_PRODUCER {
                    items.fetch_add(1, Ordering::Release);
                    proto.publish();
                }
            })
        })
        .collect();

    // Consumer: drain until everything published has been observed,
    // blocking through the protocol when idle. Hangs iff a wakeup is lost.
    let mut seen = 0;
    while seen < TOTAL {
        let _ = proto.take_pending();
        seen = items.load(Ordering::Acquire);
        if seen >= TOTAL {
            break;
        }
        let _ = proto.park_if_idle();
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(seen, TOTAL, "every publish observed");
    let rings = proto.bell().rings.load(Ordering::Relaxed);
    assert!(
        rings <= TOTAL,
        "wake storm: {rings} rings for {TOTAL} publishes"
    );
}
