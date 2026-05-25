//! Intent-layer bridge to the canonical `WitnessedPredicate` substrate.
//!
//! Per PREDICATE-INVENTORY §3 the workspace's witness-bearing predicate
//! algebras (DFA acceptance, temporal-predicate-DSL, Merkle-membership,
//! blinded-set non-revocation, bridge `Gte/Lte/...` predicates, Pedersen
//! equality, and `Custom { vk_hash }`) are unified under
//! [`pyana_cell::predicate::WitnessedPredicate`]. The intent crate uses
//! that vocabulary in three places:
//!
//! 1. **Match requirements** — an intent's `MatchSpec` can carry a
//!    `Vec<WitnessedPredicate>` of *predicate requirements*. Solvers and
//!    matchers reject candidate fulfillers unless every requirement
//!    verifies against the canonical registry.
//! 2. **Resource-pattern matching via DFA** — instead of glob-matching a
//!    `resource_pattern` string, the matcher can be configured to accept
//!    a [`WitnessedPredicate { kind: Dfa, … }`][WitnessedPredicateKind::Dfa]
//!    whose `commitment` is a route-table root and whose `proof_bytes`
//!    is the per-resource DFA acceptance trace produced by
//!    `dfa::air::compile_to_air`.
//! 3. **Compute-exchange temporal proofs** — sellers attach a
//!    [`WitnessedPredicate { kind: Temporal, … }`][WitnessedPredicateKind::Temporal]
//!    proving "uptime >= K over the last N receipts" without revealing
//!    the per-receipt values. The intent layer carries the predicate
//!    declaration and the proof; the canonical registry verifies.
//!
//! ## Registry plumbing
//!
//! The registry itself lives in `pyana_cell::predicate::WitnessedPredicateRegistry`.
//! Production wiring registers real verifiers (`pyana_circuit::dsl::circuit`'s
//! DFA verifier, `pyana_circuit::temporal_predicate_air`'s temporal
//! verifier, etc.). Tests can use `WitnessedPredicateRegistry::with_stubs()`
//! which accepts any non-empty proof.
//!
//! ## The `IntentPredicateVerifier` trait
//!
//! Intent-side callers want to evaluate predicates without manually
//! resolving input refs each time. [`IntentPredicateVerifier`] is a thin
//! adapter that pairs a `WitnessedPredicateRegistry` with intent-shaped
//! defaults: for `Dfa` predicates the input is "the resource string
//! UTF-8 bytes", for `Temporal` it's "the receipt-window bytes", etc.
//!
//! ```rust,ignore
//! use pyana_intent::predicate::{IntentPredicateVerifier, ResourceDfa};
//! let verifier = IntentPredicateVerifier::with_stub_registry();
//! let dfa = ResourceDfa::new(route_root, dfa_proof_bytes);
//! assert!(verifier.matches_resource(&dfa, "documents/private/x").is_ok());
//! ```

use std::sync::Arc;

pub use pyana_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};

/// A DFA-attested resource matcher.
///
/// Replaces the cleartext `resource_pattern: String` field's glob
/// semantics with a DFA-trace acceptance proof: the intent submitter
/// compiles their resource pattern to a DFA (`dfa::compiler::compile`),
/// publishes the resulting `router_root` commitment in the
/// `WitnessedPredicate`, and the prover (matcher / fulfiller) supplies
/// the per-input DFA trace as proof bytes.
///
/// The trace is checked by the canonical
/// `WitnessedPredicateKind::Dfa` verifier — for the stub registry this
/// only checks proof bytes are non-empty; for the production registry
/// (with `dfa::air::verify_acceptance` plugged in) the trace's
/// `router_root` is checked equal to `commitment` and the trace
/// reaches an accepting state on the supplied input.
///
/// This is the intent-layer face of the DFA caveat. Slot caveats
/// (`StateConstraint::Witnessed`) carry the same shape; topic-routing
/// (`dfa::filter::TopicFilter`) carries the same shape; the
/// `MatchSpec` carries the same shape. They all collapse to the same
/// `WitnessedPredicate` and dispatch through the same registry.
#[derive(Clone, Debug)]
pub struct ResourceDfa {
    /// The DFA route-table root that *defines* the resource pattern.
    /// Two intents with the same `route_root` agree on what counts as
    /// a "documents/private/*" pattern.
    pub route_root: [u8; 32],
    /// The per-input DFA acceptance trace. Produced by the prover
    /// (typically the cclerk posting the intent or evaluating a match
    /// candidate) via `dfa::air::compile_to_air`. The verifier
    /// re-checks the trace.
    pub proof_bytes: Vec<u8>,
}

impl ResourceDfa {
    /// Construct from a DFA root + proof bytes.
    pub fn new(route_root: [u8; 32], proof_bytes: Vec<u8>) -> Self {
        Self {
            route_root,
            proof_bytes,
        }
    }

    /// Materialize as a canonical [`WitnessedPredicate`]. The input is
    /// resolved from witness index 0 (the matcher's caller is responsible
    /// for supplying the input bytes via `PredicateInput::Bytes`).
    pub fn as_witnessed_predicate(&self) -> WitnessedPredicate {
        WitnessedPredicate {
            kind: WitnessedPredicateKind::Dfa,
            commitment: self.route_root,
            input_ref: InputRef::Witness { index: 0 },
            proof_witness_index: 0,
        }
    }
}

/// A temporal-predicate witnessed declaration for compute-exchange flows.
///
/// Compute-exchange intents typically attach a temporal predicate over
/// the seller's most recent N receipts — e.g. "uptime fact value >=
/// threshold over the last 100 turn receipts". The DSL hash binds the
/// predicate's shape (predicate_type + threshold + step count) without
/// revealing per-receipt values.
#[derive(Clone, Debug)]
pub struct TemporalPredicate {
    /// BLAKE3 of the canonical temporal-predicate DSL IR. Two intents
    /// with the same `dsl_hash` agree on what "uptime over last 100"
    /// means.
    pub dsl_hash: [u8; 32],
    /// The temporal-predicate STARK proof bytes (the
    /// `circuit::temporal_predicate_air` verifier reads `predicate_type`,
    /// `threshold`, `num_steps` from public input).
    pub proof_bytes: Vec<u8>,
}

impl TemporalPredicate {
    /// Construct from a DSL hash + proof bytes.
    pub fn new(dsl_hash: [u8; 32], proof_bytes: Vec<u8>) -> Self {
        Self {
            dsl_hash,
            proof_bytes,
        }
    }

    /// Materialize as a canonical [`WitnessedPredicate`]. The input is
    /// the receipt-chain values supplied via witness blob 0.
    pub fn as_witnessed_predicate(&self) -> WitnessedPredicate {
        WitnessedPredicate {
            kind: WitnessedPredicateKind::Temporal,
            commitment: self.dsl_hash,
            input_ref: InputRef::Witness { index: 0 },
            proof_witness_index: 0,
        }
    }
}

/// Errors from the intent-layer predicate verification facade.
///
/// Wraps `WitnessedPredicateError` with intent-shaped context — which
/// requirement, which fulfillment field, etc.
#[derive(Clone, Debug)]
pub enum IntentPredicateError {
    /// A `WitnessedPredicate` failed verification.
    Failed {
        /// Which requirement / predicate (1-based for human messages).
        index: usize,
        /// Underlying registry error.
        inner: WitnessedPredicateError,
    },
    /// A required `WitnessedPredicate` was not supplied.
    Missing { index: usize },
}

impl std::fmt::Display for IntentPredicateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Failed { index, inner } => {
                write!(f, "predicate #{index} verification failed: {inner}")
            }
            Self::Missing { index } => {
                write!(f, "required predicate #{index} not supplied")
            }
        }
    }
}

impl std::error::Error for IntentPredicateError {}

/// Verifier adapter that pairs a canonical [`WitnessedPredicateRegistry`]
/// with intent-shaped input resolution.
///
/// The trait surface is what intent's matcher / solver / fulfillment
/// flows talk to. The implementation routes through the canonical
/// registry — but callers don't have to spell out the input resolution
/// each time.
///
/// ## Why an adapter and not direct registry use
///
/// Each predicate kind expects its input in a particular shape (the
/// DFA verifier wants the bytestring; the temporal verifier wants the
/// chain values). The intent layer knows the *semantic* mapping (DFA
/// for `MatchSpec.resource_pattern`, temporal for compute-exchange's
/// SLA predicates) and applies it consistently. Apps can also call
/// the registry directly when they want non-standard input mappings.
pub struct IntentPredicateVerifier {
    registry: Arc<WitnessedPredicateRegistry>,
}

impl IntentPredicateVerifier {
    /// Construct a verifier wrapping an existing registry. Production
    /// callers pass the workspace-shared registry (with real DFA /
    /// Temporal / etc. verifiers registered); tests can pass
    /// `WitnessedPredicateRegistry::with_stubs()`.
    pub fn new(registry: WitnessedPredicateRegistry) -> Self {
        Self {
            registry: Arc::new(registry),
        }
    }

    /// Convenience constructor for tests: a stub-verifier registry that
    /// accepts any non-empty proof bytes for every built-in kind.
    pub fn with_stub_registry() -> Self {
        Self {
            registry: Arc::new(WitnessedPredicateRegistry::with_stubs()),
        }
    }

    /// Access the underlying registry (for advanced callers that want
    /// to register additional `Custom { vk_hash }` verifiers).
    pub fn registry(&self) -> &WitnessedPredicateRegistry {
        &self.registry
    }

    /// Check that a resource string satisfies a DFA-attested resource
    /// predicate. The input is the resource UTF-8 bytes; the proof is
    /// the DFA trace embedded in `dfa`.
    pub fn matches_resource(
        &self,
        dfa: &ResourceDfa,
        resource: &str,
    ) -> Result<(), IntentPredicateError> {
        let wp = dfa.as_witnessed_predicate();
        let input = PredicateInput::Bytes(resource.as_bytes());
        self.registry
            .verify(&wp, &input, &dfa.proof_bytes)
            .map_err(|inner| IntentPredicateError::Failed { index: 0, inner })
    }

    /// Verify a temporal predicate proof against its DSL-hash
    /// commitment. The `chain_values` are the cleartext-inside witness
    /// the prover compiled the proof over; the verifier re-checks
    /// against `proof_bytes`.
    pub fn verify_temporal(
        &self,
        temporal: &TemporalPredicate,
        chain_values: &[u8],
    ) -> Result<(), IntentPredicateError> {
        let wp = temporal.as_witnessed_predicate();
        let input = PredicateInput::Bytes(chain_values);
        self.registry
            .verify(&wp, &input, &temporal.proof_bytes)
            .map_err(|inner| IntentPredicateError::Failed { index: 0, inner })
    }

    /// Verify a list of [`WitnessedPredicate`] match requirements,
    /// pairing each with a per-requirement proof + input. Used by the
    /// solver to gate counterparty selection (predicate-attested intent
    /// matching, per the lane spec).
    ///
    /// Returns the first failure with the requirement's index.
    pub fn verify_all<'a>(
        &self,
        requirements: &[(WitnessedPredicate, PredicateInput<'a>, &'a [u8])],
    ) -> Result<(), IntentPredicateError> {
        for (i, (wp, input, proof)) in requirements.iter().enumerate() {
            if proof.is_empty() {
                return Err(IntentPredicateError::Missing { index: i });
            }
            if let Err(inner) = self.registry.verify(wp, input, proof) {
                return Err(IntentPredicateError::Failed { index: i, inner });
            }
        }
        Ok(())
    }
}

impl Default for IntentPredicateVerifier {
    fn default() -> Self {
        Self::with_stub_registry()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_verifier_accepts_nonempty_dfa_proof() {
        let verifier = IntentPredicateVerifier::with_stub_registry();
        let dfa = ResourceDfa::new([0x11; 32], vec![0xAB, 0xCD]);
        assert!(verifier.matches_resource(&dfa, "documents/x").is_ok());
    }

    #[test]
    fn stub_verifier_rejects_empty_dfa_proof() {
        let verifier = IntentPredicateVerifier::with_stub_registry();
        let dfa = ResourceDfa::new([0x11; 32], vec![]);
        let err = verifier
            .matches_resource(&dfa, "documents/x")
            .expect_err("empty proof should fail");
        match err {
            IntentPredicateError::Failed { .. } => {}
            other => panic!("wrong error variant: {other:?}"),
        }
    }

    #[test]
    fn temporal_predicate_shape() {
        let temporal = TemporalPredicate::new([0x22; 32], vec![0x01, 0x02, 0x03]);
        let wp = temporal.as_witnessed_predicate();
        assert!(matches!(wp.kind, WitnessedPredicateKind::Temporal));
        assert_eq!(wp.commitment, [0x22; 32]);
    }

    #[test]
    fn dfa_predicate_shape() {
        let dfa = ResourceDfa::new([0x33; 32], vec![0xFF]);
        let wp = dfa.as_witnessed_predicate();
        assert!(matches!(wp.kind, WitnessedPredicateKind::Dfa));
        assert_eq!(wp.commitment, [0x33; 32]);
    }

    #[test]
    fn verify_all_short_circuits_on_first_failure() {
        let verifier = IntentPredicateVerifier::with_stub_registry();
        let dfa_ok = ResourceDfa::new([0x11; 32], vec![0xAB]);
        let dfa_bad = ResourceDfa::new([0x22; 32], vec![]);

        let wp_ok = dfa_ok.as_witnessed_predicate();
        let wp_bad = dfa_bad.as_witnessed_predicate();
        let input = PredicateInput::Bytes(b"hello");

        let reqs = vec![
            (wp_ok.clone(), input.clone(), dfa_ok.proof_bytes.as_slice()),
            (
                wp_bad.clone(),
                input.clone(),
                dfa_bad.proof_bytes.as_slice(),
            ),
        ];
        let err = verifier.verify_all(&reqs).expect_err("second should fail");
        match err {
            IntentPredicateError::Missing { index: 1 } => {}
            other => panic!("expected Missing{{index: 1}}, got: {other:?}"),
        }
    }

    #[test]
    fn verify_all_accepts_all_valid() {
        let verifier = IntentPredicateVerifier::with_stub_registry();
        let dfa_a = ResourceDfa::new([0x11; 32], vec![0xAA]);
        let dfa_b = ResourceDfa::new([0x22; 32], vec![0xBB]);
        let wp_a = dfa_a.as_witnessed_predicate();
        let wp_b = dfa_b.as_witnessed_predicate();
        let input = PredicateInput::Bytes(b"resource/x");
        let reqs = vec![
            (wp_a, input.clone(), dfa_a.proof_bytes.as_slice()),
            (wp_b, input, dfa_b.proof_bytes.as_slice()),
        ];
        assert!(verifier.verify_all(&reqs).is_ok());
    }

    #[test]
    fn default_verifier_uses_stubs() {
        // Sanity: the Default impl uses stubs (so tests can construct
        // a verifier without spelling out registry configuration).
        let _ = IntentPredicateVerifier::default();
    }
}
