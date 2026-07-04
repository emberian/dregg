//! A bounded single-producer/single-consumer ring, written as a small
//! executable model ("twin") whose entire purpose is to be exhaustively
//! schedule-checked under [loom].
//!
//! # The algorithm
//!
//! - **Free-running counters.** `head` (consumer position) and `tail`
//!   (producer position) increase monotonically and wrap only at the integer
//!   boundary; they are masked (`index & (capacity - 1)`) only when indexing
//!   the slot array. The governing invariant is
//!   `head <= tail <= head + capacity`; slot `i` holds an initialized value
//!   iff `head <= i < tail`.
//! - **Release/Acquire publication.** The producer writes the slot, then
//!   stores `tail` with `Release`; the consumer loads `tail` with `Acquire`
//!   before reading the slot (and symmetrically for `head` when returning a
//!   slot to the producer). This pair is what carries the data across the
//!   thread boundary.
//! - **SPSC is a structural assumption.** Exactly one producer and one
//!   consumer, enforced at the type level: `Sender` keeps its cached tail in
//!   a [`Cell`], which makes it `!Sync`; `Receiver` takes `&mut self` for
//!   every consuming operation. Neither handle can be aliased across threads.
//! - **Close flag.** Either side may set the shared `closed` flag (never
//!   cleared) and wake the peer. A closed ring rejects new pushes; the
//!   receiver may still drain items published before the close.
//! - **Check-register-recheck waker handoff, both directions.** When the
//!   consumer finds the ring empty it registers a waker and then re-checks
//!   `tail`; when the producer finds the ring full it registers a waker and
//!   then re-checks `head`. See [`WakeCell`] for why the handoff needs
//!   `SeqCst` fences and cannot be built from Release/Acquire alone.
//!
//! # Wake discipline
//!
//! Both directions wake unconditionally after moving their counter: the
//! producer wakes the consumer's cell after every push (and on close), the
//! consumer wakes the producer's cell after every pop (and on close). The
//! natural-looking optimization — "wake the producer only when the pop
//! transitioned the ring from full to non-full" — is unsound under weak
//! memory: the consumer computes *was-full* from an `Acquire` load of `tail`
//! that is allowed to be stale, so it can classify a pop-from-full as a
//! pop-from-non-full and skip the only wake a blocked producer would ever
//! receive. The unconditional wake is cheap when nobody is parked (one fence
//! plus one atomic load) and makes the handoff argument a pure two-party
//! fence pairing. The loom suite in `tests/loom.rs` includes a litmus test
//! demonstrating the failure of the fence-free variant.

#![deny(unsafe_op_in_unsafe_fn)]

mod sync;

use std::cell::Cell;
use std::future::Future;
use std::mem::MaybeUninit;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

use sync::{Arc, AtomicBool, AtomicUsize, Mutex, Ordering, UnsafeCell, fence};

/// Error returned by [`Sender::try_push`].
#[derive(Debug, PartialEq, Eq)]
pub enum PushError<T> {
    /// The ring is full; the value is handed back.
    Full(T),
    /// The ring is closed; the value is handed back.
    Closed(T),
}

impl<T> PushError<T> {
    /// Recover the value that could not be pushed.
    pub fn into_inner(self) -> T {
        match self {
            PushError::Full(v) | PushError::Closed(v) => v,
        }
    }
}

/// A single-waker notification cell with an atomic-flag fast path.
///
/// # Why the fences
///
/// The waiter runs *check condition → register → re-check condition*; the
/// notifier runs *make condition true → wake*. Written with plain
/// Release/Acquire these two sequences are exactly the store-buffering
/// litmus: waiter stores `has_waker`, then loads the condition; notifier
/// stores the condition, then loads `has_waker`. C11 permits **both** loads
/// to read the stale value — the waiter re-checks and sees nothing, the
/// notifier sees no waker and skips the wake, and the waiter sleeps forever
/// with the condition true. The `SeqCst` fences in [`register`] (between the
/// flag store and the caller's re-check) and [`wake`] (between the caller's
/// condition store and the flag load) restore the Dekker guarantee: the two
/// fences are totally ordered, so whichever side fenced second is guaranteed
/// to observe the other's store.
///
/// [`register`]: WakeCell::register
/// [`wake`]: WakeCell::wake
struct WakeCell {
    /// Fast-path flag: `true` while a waker may be parked in `slot`.
    has_waker: AtomicBool,
    slot: Mutex<Option<Waker>>,
}

impl WakeCell {
    fn new() -> Self {
        WakeCell {
            has_waker: AtomicBool::new(false),
            slot: Mutex::new(None),
        }
    }

    /// Park `waker` in the cell. The caller **must** re-check its wait
    /// condition after this returns; the embedded `SeqCst` fence orders the
    /// flag store before that re-check.
    fn register(&self, waker: &Waker) {
        *self.slot.lock().unwrap() = Some(waker.clone());
        self.has_waker.store(true, Ordering::SeqCst);
        fence(Ordering::SeqCst);
    }

    /// Wake and consume the parked waker, if any. The caller must have
    /// already published the state change the waiter is waiting on; the
    /// embedded `SeqCst` fence orders that publication before the flag load.
    fn wake(&self) {
        fence(Ordering::SeqCst);
        if !self.has_waker.load(Ordering::SeqCst) {
            return;
        }
        let waker = {
            let mut slot = self.slot.lock().unwrap();
            self.has_waker.store(false, Ordering::SeqCst);
            slot.take()
        };
        if let Some(w) = waker {
            w.wake();
        }
    }
}

/// State shared by the two endpoint handles.
struct Ring<T> {
    buffer: Box<[UnsafeCell<MaybeUninit<T>>]>,
    mask: usize,
    capacity: usize,
    /// Consumer position. Only the consumer stores to this (Release);
    /// the producer loads it (Acquire) for the full check.
    head: AtomicUsize,
    /// Producer position. Only the producer stores to this (Release);
    /// the consumer loads it (Acquire) for the empty check.
    tail: AtomicUsize,
    /// Set once by either side; never cleared.
    closed: AtomicBool,
    /// Woken by the producer after each push and on close.
    consumer_waker: WakeCell,
    /// Woken by the consumer after each pop and on close.
    producer_waker: WakeCell,
}

// SAFETY: the ring is shared between exactly two threads (one Sender, one
// Receiver — each Send but not Sync). Every slot is written only by the
// producer while `tail <= slot-index < head + capacity` and read only by the
// consumer while `head <= slot-index < tail`; the Release store of the
// counter and the Acquire load on the other side order the slot access.
unsafe impl<T: Send> Send for Ring<T> {}
unsafe impl<T: Send> Sync for Ring<T> {}

impl<T> Drop for Ring<T> {
    fn drop(&mut self) {
        // Sole owner at this point; drop any undrained items.
        let head = self.head.load(Ordering::Acquire);
        let tail = self.tail.load(Ordering::Acquire);
        let mut i = head;
        while i != tail {
            let slot = i & self.mask;
            // SAFETY: slots in [head, tail) are initialized and unaliased.
            self.buffer[slot].with_mut(|p| unsafe { (*p).assume_init_drop() });
            i = i.wrapping_add(1);
        }
    }
}

/// Producer handle. `Send` but `!Sync` (the cached tail lives in a `Cell`),
/// so exactly one thread can ever push.
pub struct Sender<T> {
    ring: Arc<Ring<T>>,
    /// Local copy of `tail`. Only this handle advances `tail`, so the cache
    /// is always exact; the `Cell` is what makes the type `!Sync`.
    cached_tail: Cell<usize>,
}

/// Consumer handle. `Send` but consuming operations take `&mut self`, so
/// exactly one thread can pop at a time.
pub struct Receiver<T> {
    ring: Arc<Ring<T>>,
    /// Local copy of `head`. Only this handle advances `head`.
    cached_head: usize,
}

/// Create a bounded SPSC ring. `capacity` must be a nonzero power of two.
pub fn channel<T: Send>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    assert!(
        capacity > 0 && capacity.is_power_of_two(),
        "ring capacity must be a nonzero power of two, got {capacity}"
    );
    let buffer: Box<[UnsafeCell<MaybeUninit<T>>]> = (0..capacity)
        .map(|_| UnsafeCell::new(MaybeUninit::uninit()))
        .collect();
    let ring = Arc::new(Ring {
        buffer,
        mask: capacity - 1,
        capacity,
        head: AtomicUsize::new(0),
        tail: AtomicUsize::new(0),
        closed: AtomicBool::new(false),
        consumer_waker: WakeCell::new(),
        producer_waker: WakeCell::new(),
    });
    (
        Sender {
            ring: ring.clone(),
            cached_tail: Cell::new(0),
        },
        Receiver {
            ring,
            cached_head: 0,
        },
    )
}

impl<T: Send> Sender<T> {
    /// Push a value, failing if the ring is full or closed.
    ///
    /// On success the consumer's waker is fired (fast-path: one fence and
    /// one atomic load when nobody is parked).
    pub fn try_push(&self, value: T) -> Result<(), PushError<T>> {
        if self.is_closed() {
            return Err(PushError::Closed(value));
        }
        let tail = self.cached_tail.get();
        let head = self.ring.head.load(Ordering::Acquire);
        if tail.wrapping_sub(head) >= self.ring.capacity {
            return Err(PushError::Full(value));
        }

        let slot = tail & self.ring.mask;
        // SAFETY: `head <= tail < head + capacity` was just established, so
        // this slot is outside [head, tail) — the consumer will not touch it
        // until the Release store below makes it visible.
        self.ring.buffer[slot].with_mut(|p| unsafe { (*p).write(value) });

        // Publish: the slot write above becomes visible to any Acquire load
        // of `tail` that observes the new value.
        self.ring.tail.store(tail.wrapping_add(1), Ordering::Release);
        self.cached_tail.set(tail.wrapping_add(1));

        self.ring.consumer_waker.wake();
        Ok(())
    }

    /// `true` once either side has closed the ring.
    pub fn is_closed(&self) -> bool {
        self.ring.closed.load(Ordering::Acquire)
    }

    /// Close the ring and wake the consumer so it can observe the close.
    pub fn close(&self) {
        self.ring.closed.store(true, Ordering::Release);
        self.ring.consumer_waker.wake();
    }

    /// Send a value, waiting (async) while the ring is full.
    ///
    /// Resolves to `Err(PushError::Closed(v))` if the ring closes before
    /// space becomes available.
    pub fn send(&self, value: T) -> SendFuture<'_, T> {
        SendFuture {
            tx: self,
            value: Some(value),
        }
    }

    fn poll_send(&self, value: &mut Option<T>, cx: &mut Context<'_>) -> Poll<Result<(), PushError<T>>> {
        match self.try_push(value.take().expect("polled after completion")) {
            Ok(()) => return Poll::Ready(Ok(())),
            Err(PushError::Closed(v)) => return Poll::Ready(Err(PushError::Closed(v))),
            Err(PushError::Full(v)) => *value = Some(v),
        }
        // Check-register-recheck: the ring was full; park a waker, then
        // re-run the full check (and the close check) before sleeping.
        self.ring.producer_waker.register(cx.waker());
        match self.try_push(value.take().expect("value present")) {
            Ok(()) => {
                // Consume our own registration so a later pop does not fire
                // a stale waker.
                self.ring.producer_waker.wake();
                Poll::Ready(Ok(()))
            }
            Err(PushError::Closed(v)) => {
                self.ring.producer_waker.wake();
                Poll::Ready(Err(PushError::Closed(v)))
            }
            Err(PushError::Full(v)) => {
                *value = Some(v);
                Poll::Pending
            }
        }
    }
}

/// Future returned by [`Sender::send`].
pub struct SendFuture<'a, T> {
    tx: &'a Sender<T>,
    value: Option<T>,
}

impl<T> Unpin for SendFuture<'_, T> {}

impl<T: Send> Future for SendFuture<'_, T> {
    type Output = Result<(), PushError<T>>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = &mut *self;
        this.tx.poll_send(&mut this.value, cx)
    }
}

impl<T: Send> Receiver<T> {
    /// Pop a value, returning `None` if the ring is currently empty.
    ///
    /// On success the producer's waker is fired unconditionally — see the
    /// module docs for why "wake only on the full→non-full edge" is unsound
    /// under weak memory.
    pub fn try_pop(&mut self) -> Option<T> {
        let head = self.cached_head;
        let tail = self.ring.tail.load(Ordering::Acquire);
        if head == tail {
            return None;
        }

        let slot = head & self.ring.mask;
        // SAFETY: head < tail, so the slot was initialized by the producer
        // and published by the Release store of `tail` we just observed.
        let value = self.ring.buffer[slot].with_mut(|p| unsafe { (*p).assume_init_read() });

        // Return the slot: visible to any Acquire load of `head` that
        // observes the new value.
        self.ring.head.store(head.wrapping_add(1), Ordering::Release);
        self.cached_head = head.wrapping_add(1);

        self.ring.producer_waker.wake();
        Some(value)
    }

    /// `true` once either side has closed the ring.
    pub fn is_closed(&self) -> bool {
        self.ring.closed.load(Ordering::Acquire)
    }

    /// Close the ring and wake the producer so it can observe the close.
    pub fn close(&self) {
        self.ring.closed.store(true, Ordering::Release);
        self.ring.producer_waker.wake();
    }

    /// Receive a value, waiting (async) while the ring is empty.
    ///
    /// Resolves to `None` only when the ring is closed **and** fully
    /// drained: items published before the close are always delivered.
    pub fn recv(&mut self) -> Recv<'_, T> {
        Recv { rx: self }
    }

    fn poll_recv(&mut self, cx: &mut Context<'_>) -> Poll<Option<T>> {
        if let Some(v) = self.try_pop() {
            return Poll::Ready(Some(v));
        }
        if self.is_closed() {
            // The Acquire load of `closed` synchronizes with the closer's
            // Release store, so everything pushed before the close is now
            // visible; one final pop drains it.
            return Poll::Ready(self.try_pop());
        }
        // Check-register-recheck: the ring was empty and open; park a waker,
        // then re-run both checks before sleeping.
        self.ring.consumer_waker.register(cx.waker());
        if let Some(v) = self.try_pop() {
            self.ring.consumer_waker.wake();
            return Poll::Ready(Some(v));
        }
        if self.is_closed() {
            self.ring.consumer_waker.wake();
            return Poll::Ready(self.try_pop());
        }
        Poll::Pending
    }
}

/// Future returned by [`Receiver::recv`].
pub struct Recv<'a, T> {
    rx: &'a mut Receiver<T>,
}

impl<T> Unpin for Recv<'_, T> {}

impl<T: Send> Future for Recv<'_, T> {
    type Output = Option<T>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.rx.poll_recv(cx)
    }
}
