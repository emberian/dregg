//! Derivation trace format and reference evaluator for the pyana ZK token system.
//!
//! This crate provides:
//! - Data structures for representing Datalog derivation traces
//! - A bottom-up Datalog evaluator that records proof traces
//! - A standalone trace verifier
//! - Standard policy rules for the pyana authorization model

pub mod check;
pub mod eval;
pub mod policy;
pub mod types;
pub mod verify;

pub use check::eval_check;
pub use eval::Evaluator;
pub use policy::{secure_policy, standard_policy};
pub use types::*;
pub use verify::verify_trace;

#[cfg(test)]
mod tests;
