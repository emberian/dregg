//! # dregg-query — attested queries over the receipt fact-base
//!
//! The Q1+Q2 core of `.docs-history-noclaude/EPISTEMIC-DATALOG.md`, deliberately NOT a full
//! Datalog engine (the named trap): no IDB rules, no recursion, no
//! stratification — one conjunctive query at a time, over a closed EDB
//! schema, with the two things no Datalog DB has:
//!
//! - **the CALM grade from day one** ([`classify`]): every query is
//!   annotated monotone (coordination-free, rows final, cacheable) or
//!   finalized-dependent ("fresh as of height H") — the I-confluence /
//!   `modality_price_monotone` story applied per query;
//! - **the non-omission certificate** ([`attested`]): answers carry a range
//!   opening against the receipt-log MMR root, so a verifying answer is
//!   provably computed from EXACTLY the committed receipt range — nothing
//!   hidden, nothing forged, nothing reordered. The verifier re-derives the
//!   rows; the server is trusted for nothing but availability.
//!
//! ## Layout
//!
//! - [`fact`] — the EDB schema: `created` / `transfer` / `balance` /
//!   `granted` / `revoked` / `burned` / `field` / `lifecycle`, height-stamped,
//!   append-only.
//! - [`receipt`] — the receipt row consumed (node wire mirror + offline
//!   `Vec<ReceiptRecord>` mode) and fact extraction.
//! - [`query`] — terms / atoms / filters / safe negation + the nested-loop
//!   join evaluator.
//! - [`classify`] — the CALM classifier.
//! - [`mmr`] — the receipt-index MMR: the Rust embodiment of
//!   `metatheory/Dregg2/Lightclient/MMR.lean` (`RVerifies`,
//!   `server_cannot_omit_position`); prover + root-pinned range verifier.
//! - [`attested`] — `AttestedSlice` / `AttestedAnswer`: the
//!   certificate-carrying answer type and its `verify`.
//! - [`client`] — transport-agnostic node-API mirrors of the node-side
//!   `/api/receipts/index/{root,range}` handlers (served by `node/src/api.rs`)
//!   and the enrichment the typed effect summaries need.
//!
//! ## The proof story (what is and is not verified)
//!
//! The non-omission ARGUMENT is machine-checked in Lean
//! (`Dregg2/Lightclient/{HistoryIndex,AttestedQuery,MMR}.lean` — axiom-clean,
//! non-vacuous both ways). THIS crate is the unverified Rust mirror of the
//! MMR specialization: same structure, same acceptance condition, same
//! false-witness suite as the model's §7 (see `tests/`). The hash floor here
//! is blake3 with arity-separated domain tags standing in the model's
//! `Poseidon2SpongeCR` slot; the in-circuit Poseidon2 instantiation arrives
//! with THE ROTATION's `CommitBindsMMR` weld, at which point the trusted
//! root stops being out-of-band and is pinned by the IVC aggregate.

pub mod attested;
pub mod classify;
pub mod client;
pub mod fact;
mod hexutil;
pub mod mmr;
pub mod query;
pub mod receipt;
/// Streaming receipts: the producer side of `lake exe stream-check` (initiative 11).
pub mod stream;
/// Paged whole-log MMR window tiling — the anti-truncation / hidden-revocation
/// verifier over a range of the committed log.
pub mod windows;

pub use attested::{
    AttestError, AttestedAnswer, AttestedSlice, Coverage, RangeCertificate, answer,
    answer_whole_log,
};
pub use classify::{Classification, CoordinationClass, classify};
pub use fact::{Fact, FactBase, Height, Pred, Value};
pub use mmr::{Blake3Mmr, Mmr, MmrError, MmrHasher, Peak, RangeOpening, verify_range};
pub use query::{AggOp, Aggregate, Atom, Bindings, CmpOp, Filter, Query, QueryError, Term, eval};
pub use receipt::{EffectSummary, ReceiptRecord, extract_facts};
