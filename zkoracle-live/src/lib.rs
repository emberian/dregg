//! `dregg-zkoracle-live` — **the LIVE MPC-TLS backend for the zkOracle prover.**
//!
//! A genuine TLSNotary 2PC session against a real HTTPS host, a SEPARATE hosted notary that
//! co-derives the session keys and never sees plaintext, and a real `presentation.verify()`.
//! Everything downstream of the authenticated body — the CFG parse certificate, the
//! injection-free matcher, the cross-leg weld, the fact extractors — belongs to
//! [`dregg_zkoracle_prove`] and is shared verbatim with the fixture path.
//!
//! ```text
//!   dregg-zkoracle-prove   the attestation, the 3-leg composition, the fact extractors.
//!                          NO cargo features. Links no tlsn. Identical in every build.
//!   dregg-zkoracle-live    THIS crate: leg 1 from a real MPC-TLS session.
//!                          NO cargo features. Links tlsn unconditionally.
//! ```
//!
//! ## ⚑ WHY THIS IS A CRATE AND NOT A `tlsn-live` FEATURE
//!
//! It was a feature until 2026-07-27. Cargo features UNIFY ACROSS A WORKSPACE RESOLVE: a
//! feature any selected member enables is on for every member. `dregg-oracle` — a root member
//! deliberately kept out of `default-members` precisely to avoid this — had
//! `default = ["live"] -> dregg-zkoracle-prove/tlsn-live`. `--workspace` selects members
//! regardless of `default-members`, so the workaround did not hold, and MEASURED at that
//! commit:
//!
//! | invocation                                | `dregg-zkoracle-prove`'s own test suite      |
//! |-------------------------------------------|----------------------------------------------|
//! | `cargo test -p dregg-zkoracle-prove`      | 51 lib tests; FOUR binaries "running 0 tests" |
//! | `cargo test --workspace`                  | the same 51 **plus 10 real MPC-TLS 2PC tests** |
//!
//! Same source, two suites, decided by which OTHER packages cargo was asked about. And the
//! `verify_mpctls_leg` PROVENANCE GATE was a `#[cfg]`/`#[cfg(not)]` pair — genuine crypto or
//! an immediate fail-closed refusal — so a SECURITY-LOAD-BEARING branch was selected by the
//! package selection. That is not a thing a reader of either crate could see.
//!
//! A dependency EDGE does not unify. The heavy `mpz` 2PC/garbling + tokio + rustls stack is
//! still kept out of the bare dev loop, but by this crate being members-but-NOT-default-members
//! — a property of the selection, not of some other crate's feature list.

pub mod endpoints;
pub mod notary_server;
pub mod tlsn_bedrock;
pub mod tlsn_hop;
pub mod tlsn_live;
pub mod verify;

pub use verify::{TlsnHostLeg, TlsnLeg, verify_zkoracle_live, verify_zkoracle_live_host};
