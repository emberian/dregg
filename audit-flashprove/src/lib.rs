//! `audit-flashprove`: commit-then-audit over FlashProve's `cp_verify`.
//!
//! The pipeline, in the order the theorem needs it (`minidregg/Selvage/AuditFlashProve.lean`):
//!
//! 1. **Commit.** Each served request becomes a [`record::RequestRecord`] (digests of the request,
//!    token and proof files, the pinned commitment ID, `r`, `e`, and the latest drand round the
//!    requester had seen). Its digest is appended to the `dregg-query` MMR ([`dregg_query::mmr`]),
//!    and the requester countersigns (position, record digest, MMR root, seen round).
//! 2. **Beacon.** The audit coin of position `t` comes from drand quicknet round `seen + 2`
//!    ([`beacon`]): a round that did not exist when the requester countersigned.
//! 3. **Decide.** Whether the audit fires, the checker's verdict and the alarm are the compiled
//!    Lean functions `fires`, `verdictOf`, `alarm` ([`decide`]); nothing in Rust decides.
//! 4. **Check.** A fired audit runs `cp_verify` under time and memory limits on the files the
//!    record commits to ([`runner`]). Exit 1 is a rejection; every other non-accept, a timeout,
//!    a kill, a missing proof, is `noVerdict`, and both alarm.
//! 5. **Receipt.** [`receipt::Receipt`] carries the MMR root and opening, the countersignature,
//!    the drand round and signature, the coin, the full `cp_verify` output and exit status, and
//!    the verdict and alarm; [`receipt::recheck`] re-derives every one offline through the same
//!    compiled Lean.

pub mod beacon;
pub mod decide;
pub mod experiment;
pub mod receipt;
pub mod record;
pub mod runner;

/// The SHA-256 of the Lean decision source this binary was built from.
pub const DECIDE_SRC_SHA256: &str = env!("FPAUDIT_DECIDE_SRC_SHA256");
