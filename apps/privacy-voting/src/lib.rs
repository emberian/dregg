//! # pyana-privacy-voting
//!
//! Privacy-preserving voting on the pyana protocol. Voters with a valid
//! eligibility credential (a signed [`DelegatedToken`] envelope issued by a
//! known authority) submit hidden vote-commitments into a blinded queue, then
//! reveal during a separate phase. The tally is verifiable from the reveals
//! against the queue's commitment root.
//!
//! ## Modules
//!
//! - [`proposal`] — proposal metadata + lifecycle phases.
//! - [`ballot`]   — vote commitments (`blake3` with domain tag + randomness).
//! - [`eligibility`] — credential acceptance gated by [`crate::eligibility::EligibilityAuthority`].
//! - [`tally`]    — reveal log + Merkle root + per-option counting.
//! - [`server`]   — AppServer wiring + routes.
//!
//! ## What's private
//!
//! - The chosen `option_index` is hidden behind a 32-byte randomness during the
//!   commit phase. Without the reveal, no observer learns who voted for what.
//! - The voter's identity (their `delegatee` pubkey) is never persisted
//!   alongside the commitment. The double-vote-prevention set is keyed by
//!   pubkey but kept disjoint from the queue.
//!
//! ## What's verifiable
//!
//! - The blinded queue's commitment root anchors the full set of submissions.
//! - The reveal log's Merkle root anchors the set of reveals.
//! - The tally is computed from the reveal log; any observer with the log can
//!   recompute it.
//!
//! [`DelegatedToken`]: pyana_sdk::cipherclerk::DelegatedToken

pub mod ballot;
pub mod effects;
pub mod eligibility;
pub mod proposal;
pub mod server;
pub mod tally;

#[cfg(test)]
mod tests;

// Re-exports for downstream callers (e.g., the binary).
pub use eligibility::{EligibilityAuthority, EligibilityError, verify_eligibility};
pub use proposal::{Phase, Proposal, ProposalId, derive_proposal_id};
pub use server::{AppState, router};
