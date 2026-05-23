//! Merkle membership circuit (Kimchi gates) — re-exports from parent module.
//!
//! The canonical implementation lives in `mina/mod.rs` where it is used by
//! `MinaBackend::prove_membership` / `verify_membership`. This sub-module
//! exists for organizational clarity but delegates to the parent definitions.
//!
//! For the standalone IPA verifier's membership circuit, see `step_verifier.rs`.

// The build_merkle_membership_circuit and generate_merkle_witness functions
// are defined directly in super (mina/mod.rs) and used by MinaBackend.
// No additional code needed here.
