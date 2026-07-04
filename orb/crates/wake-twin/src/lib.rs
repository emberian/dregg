//! A two-flag Dekker-style wakeup protocol, written as a small executable
//! model whose entire purpose is to be exhaustively schedule-checked under
//! [loom].
//!
//! # The problem
//!
//! An event-loop consumer drains work queues and then blocks in a syscall
//! until more work arrives. Producers on other threads enqueue work and must
//! wake the consumer — but the wake syscall is expensive, so it should be
//! issued only when the consumer might actually be blocked, and repeated
//! publishes should coalesce into one wake. Getting this wrong in either
//! direction is fatal: a missed wake strands work forever; a wake storm
//! turns every publish into a syscall.
//!
//! # The protocol
//!
//! Two shared flags, all accesses `SeqCst`:
//!
//! - `pending` — "there is unconsumed work." Set by producers, cleared by
//!   the consumer immediately **before** each drain (clear-before-drain, so
//!   work published after the clear re-flags itself).
//! - `might_block` — "the consumer may be about to block." Set by the
//!   consumer before its final pending check, cleared when it resumes.
//!
//! **Producer** ([`WakeProtocol::publish`], after making the work visible):
//! swap `pending` to `true`, then load `might_block`; if the consumer might
//! block **and** this publish made the `false → true` edge on `pending`,
//! ring the doorbell (the syscall stub). The edge condition is the
//! coalescing: with `pending` already set, some earlier publisher owned the
//! edge and the wake, or the consumer will see `pending` in its re-check.
//!
//! **Consumer** ([`WakeProtocol::park_if_idle`]): store `might_block :=
//! true`, then re-check `pending`; if set, retract `might_block` and drain
//! again instead of blocking; if clear, block on the doorbell, then retract
//! `might_block`.
//!
//! This is the store-buffering (Dekker) shape: producer stores `pending`
//! then loads `might_block`; consumer stores `might_block` then loads
//! `pending`. Sequential consistency at the two store→load points is what
//! forbids the outcome where both sides read the stale value (producer sees
//! "not blocking", consumer sees "nothing pending") — under Release/Acquire
//! that outcome is permitted and the wakeup is lost. The doorbell itself
//! must be a *semaphore*, not a pulse: a ring issued while the consumer is
//! not yet waiting must persist and satisfy the consumer's next wait
//! (eventfd semantics).
//!
//! In addition to the `SeqCst` accesses, the protocol carries an explicit
//! `SeqCst` **fence** between the store and the load on each side. Under
//! the C11 model the all-`SeqCst` accesses already forbid store buffering,
//! so the fences are formally redundant — but loom does not implement the
//! total order over `SeqCst` *accesses* completely (it explores the
//! store-buffering outcome for them), while it models `SeqCst` *fences*
//! precisely. The fences are what make the protocol *checkable*, and they
//! also keep the guarantee independent of how a given compiler maps
//! `SeqCst` accesses.
//!
//! # What the model omits
//!
//! The real consumer blocks with a timeout, which would eventually paper
//! over a lost wakeup. The model deliberately has **no timeout**: if the
//! protocol can strand a publish, the loom suite ends in a detected
//! deadlock instead of a silent latency spike.

mod sync;

use sync::{AtomicBool, Ordering, fence};

/// The syscall pair at the bottom of the protocol, abstracted so tests can
/// instrument it. Semantics are those of a counting semaphore (eventfd):
/// [`ring`](Doorbell::ring) deposits a token; [`wait`](Doorbell::wait)
/// blocks until at least one token is present, then consumes all tokens.
pub trait Doorbell {
    /// Producer-side wake syscall stub. Must deposit a persistent token.
    fn ring(&self);
    /// Consumer-side block syscall stub. Must return once a token is or
    /// becomes available, consuming it. Must NOT return spuriously with no
    /// token ever deposited (no timeout in the model).
    fn wait(&self);
}

/// The two-flag wakeup protocol around a [`Doorbell`].
///
/// Any number of producers may call [`publish`](WakeProtocol::publish);
/// exactly one consumer thread runs the
/// [`take_pending`](WakeProtocol::take_pending) /
/// [`park_if_idle`](WakeProtocol::park_if_idle) loop.
pub struct WakeProtocol<D> {
    /// "There is unconsumed work." Producers set; consumer clears before
    /// each drain.
    pending: AtomicBool,
    /// "The consumer may be about to block." Consumer sets before its final
    /// pending re-check and clears when it resumes.
    might_block: AtomicBool,
    bell: D,
}

impl<D: Doorbell> WakeProtocol<D> {
    pub fn new(bell: D) -> Self {
        WakeProtocol {
            pending: AtomicBool::new(false),
            might_block: AtomicBool::new(false),
            bell,
        }
    }

    /// Producer side. Call **after** the work item itself has been made
    /// visible (e.g. after the queue's own Release publication).
    ///
    /// Returns `true` iff this call issued a doorbell ring, which happens
    /// only when this publish made the `false → true` edge on `pending`
    /// while the consumer might block. At most one ring per edge — the
    /// coalescing guarantee.
    pub fn publish(&self) -> bool {
        // Dekker half A: store `pending`, then load `might_block`.
        let was_pending = self.pending.swap(true, Ordering::SeqCst);
        fence(Ordering::SeqCst);
        if !self.might_block.load(Ordering::SeqCst) {
            // Consumer is awake (or will re-check `pending` before it
            // blocks — SeqCst forbids both sides reading stale).
            return false;
        }
        if was_pending {
            // Some earlier publisher owned the false→true edge; its ring
            // (or the consumer's re-check) covers us.
            return false;
        }
        self.bell.ring();
        true
    }

    /// Consumer side, step 1: clear `pending` and report whether it was
    /// set. Call immediately **before** each drain, never after — work
    /// published after this clear re-flags `pending` for the next round.
    pub fn take_pending(&self) -> bool {
        self.pending.swap(false, Ordering::SeqCst)
    }

    /// Consumer side, step 2: after a drain that found nothing, announce
    /// intent to block and re-check. Returns `true` if the consumer
    /// actually blocked on the doorbell, `false` if the re-check found
    /// pending work (caller should loop and drain again).
    pub fn park_if_idle(&self) -> bool {
        // Dekker half B: store `might_block`, then load `pending`.
        self.might_block.store(true, Ordering::SeqCst);
        fence(Ordering::SeqCst);
        if self.pending.load(Ordering::SeqCst) {
            // A publish raced in; don't block.
            self.might_block.store(false, Ordering::SeqCst);
            return false;
        }
        self.bell.wait();
        self.might_block.store(false, Ordering::SeqCst);
        true
    }

    /// Access the underlying doorbell (test instrumentation).
    pub fn bell(&self) -> &D {
        &self.bell
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    /// Doorbell that only counts rings (no blocking — these tests never wait).
    struct CountingBell(AtomicUsize);

    impl Doorbell for CountingBell {
        fn ring(&self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
        fn wait(&self) {
            unreachable!("deterministic tests never block");
        }
    }

    #[test]
    fn no_ring_when_consumer_awake() {
        let p = WakeProtocol::new(CountingBell(AtomicUsize::new(0)));
        assert!(!p.publish());
        assert!(!p.publish());
        assert_eq!(p.bell().0.load(Ordering::SeqCst), 0);
        assert!(p.take_pending());
        assert!(!p.take_pending());
    }

    #[test]
    fn coalescing_exactly_one_ring_per_edge() {
        let p = WakeProtocol::new(CountingBell(AtomicUsize::new(0)));
        // Force the "consumer about to block" state.
        p.might_block.store(true, Ordering::SeqCst);
        assert!(p.publish(), "edge publish must ring");
        assert!(!p.publish(), "second publish coalesces");
        assert!(!p.publish(), "third publish coalesces");
        assert_eq!(p.bell().0.load(Ordering::SeqCst), 1);
        // Consumer drains; the next edge earns exactly one more ring.
        assert!(p.take_pending());
        assert!(p.publish());
        assert!(!p.publish());
        assert_eq!(p.bell().0.load(Ordering::SeqCst), 2);
    }
}
