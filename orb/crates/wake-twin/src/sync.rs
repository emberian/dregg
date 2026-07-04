//! Synchronization primitives, switched between `std` and `loom`.
//!
//! Under `--cfg loom` the atomics are the loom-instrumented versions, so the
//! model checker explores every interleaving and every C11-permitted read.
//! Under normal builds the same names resolve to `std`, so the identical
//! source is what the stress lane exercises.

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicBool, Ordering, fence};

#[cfg(not(loom))]
pub(crate) use std::sync::atomic::{AtomicBool, Ordering, fence};
