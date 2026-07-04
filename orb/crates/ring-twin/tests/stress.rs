//! Non-loom smoke lane: the same source, real threads, big item counts.
//! This does not explore interleavings systematically (that is loom's job);
//! it exists so the twin also runs as ordinary code on real hardware.

#![cfg(not(loom))]

use std::future::Future;
use std::pin::pin;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};
use std::thread;

use ring_twin::{PushError, channel};

/// Minimal single-future executor: park the thread on `Pending`, let the
/// waker unpark it. Unpark-before-park is a token, so no lost wakeups at
/// this layer.
fn block_on<F: Future>(fut: F) -> F::Output {
    struct ThreadWaker(thread::Thread);
    impl std::task::Wake for ThreadWaker {
        fn wake(self: Arc<Self>) {
            self.0.unpark();
        }
    }

    let mut fut = pin!(fut);
    let waker = Waker::from(Arc::new(ThreadWaker(thread::current())));
    let mut cx = Context::from_waker(&waker);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => thread::park(),
        }
    }
}

const ITEMS: u64 = 100_000;

/// Spin lane: raw try_push/try_pop under real contention, then close.
#[test]
fn spin_conservation_and_close() {
    let (tx, mut rx) = channel::<u64>(8);

    let producer = thread::spawn(move || {
        for i in 0..ITEMS {
            let mut v = i;
            loop {
                match tx.try_push(v) {
                    Ok(()) => break,
                    Err(PushError::Full(back)) => {
                        v = back;
                        thread::yield_now();
                    }
                    Err(PushError::Closed(_)) => panic!("receiver never closes"),
                }
            }
        }
        tx.close();
    });

    let mut expected = 0u64;
    loop {
        match rx.try_pop() {
            Some(v) => {
                assert_eq!(v, expected, "order preserved, exactly once");
                expected += 1;
            }
            None => {
                if rx.is_closed() {
                    // Close is set after the last push; one more pop settles
                    // any item published just before the close.
                    match rx.try_pop() {
                        Some(v) => {
                            assert_eq!(v, expected);
                            expected += 1;
                        }
                        None => break,
                    }
                } else {
                    thread::yield_now();
                }
            }
        }
    }
    producer.join().unwrap();
    assert_eq!(expected, ITEMS, "every item received exactly once");
}

/// Async lane: the send/recv futures (the check-register-recheck paths)
/// under real threads and a real parking executor.
#[test]
fn async_conservation_and_close() {
    let (tx, mut rx) = channel::<u64>(4);

    let producer = thread::spawn(move || {
        block_on(async move {
            for i in 0..ITEMS {
                tx.send(i).await.expect("receiver never closes");
            }
            tx.close();
        });
    });

    let received = block_on(async move {
        let mut n = 0u64;
        while let Some(v) = rx.recv().await {
            assert_eq!(v, n, "order preserved, exactly once");
            n += 1;
        }
        n
    });

    producer.join().unwrap();
    assert_eq!(received, ITEMS, "drained fully, then observed close");
}

/// Close from the receiver side unblocks a sender stuck on a full ring.
#[test]
fn receiver_close_releases_blocked_sender() {
    let (tx, rx) = channel::<u64>(1);
    tx.try_push(1).unwrap();

    let producer = thread::spawn(move || {
        block_on(async move {
            let err = tx.send(2).await.expect_err("receiver closes without popping");
            assert_eq!(err, PushError::Closed(2));
        });
    });

    // Give the sender a chance to actually park before the close.
    thread::yield_now();
    rx.close();
    producer.join().unwrap();
}
