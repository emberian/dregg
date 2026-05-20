//! Derivation trace format and reference evaluator for the pyana ZK token system.
//!
//! This crate provides:
//! - Data structures for representing Datalog derivation traces
//! - A bottom-up Datalog evaluator that records proof traces
//! - A standalone trace verifier
//! - Standard policy rules for the pyana authorization model

pub mod types;
pub mod check;
pub mod eval;
pub mod verify;
pub mod policy;

pub use types::*;
pub use check::eval_check;
pub use eval::Evaluator;
pub use verify::verify_trace;
pub use policy::{standard_policy, secure_policy};

#[cfg(test)]
mod tests;
