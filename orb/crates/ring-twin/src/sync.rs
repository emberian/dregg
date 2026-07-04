//! Synchronization primitives, switched between `std` and `loom`.
//!
//! Under `--cfg loom` every atomic, mutex, `Arc`, and `UnsafeCell` is the
//! loom-instrumented version, so the model checker can explore every
//! interleaving and every C11-permitted read of each atomic. Under normal
//! builds the same names resolve to the `std` primitives, so the identical
//! source is what the stress lane exercises.

#[cfg(loom)]
pub(crate) use loom::{
    cell::UnsafeCell,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicUsize, Ordering, fence},
    },
};

#[cfg(not(loom))]
pub(crate) use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, AtomicUsize, Ordering, fence},
};

/// `std` stand-in for `loom::cell::UnsafeCell`, exposing the same
/// closure-based API so the data-structure code is identical under both
/// configurations.
#[cfg(not(loom))]
#[derive(Debug)]
pub(crate) struct UnsafeCell<T>(std::cell::UnsafeCell<T>);

#[cfg(not(loom))]
impl<T> UnsafeCell<T> {
    pub(crate) fn new(data: T) -> UnsafeCell<T> {
        UnsafeCell(std::cell::UnsafeCell::new(data))
    }

    pub(crate) fn with_mut<R>(&self, f: impl FnOnce(*mut T) -> R) -> R {
        f(self.0.get())
    }
}
