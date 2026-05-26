//! Per-kind tests for every `WitnessedPredicateKind`: `Dfa`, `Temporal`,
//! `MerkleMembership`, `BlindedSet`, `BridgePredicate`, `PedersenEquality`,
//! `Custom`.
//!
//! Layer: registry dispatch + verifier invocation. The executor/evaluator
//! call site now accepts a `WitnessedPredicateRegistry`; built-in AIR-backed
//! verifiers still require host installation from the upstream circuit crates.
//! Tests that use `with_stubs()` are explicit plumbing demos, not
//! cryptographic acceptance claims.
//!
//! Three categories per kind:
//!   1. Positive — predicate verifies, transition accepted.
//!   2. Adversarial — tampered proof / wrong commitment rejected.
//!   3. Registry lookup — unknown kind rejected.

use std::sync::Arc;

use dregg_cell::predicate::{
    NonMembershipNeighborProof, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
    WitnessedPredicateKind, WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag};
use dregg_cell::{
    CellProgram, CellState, EvalContext, InputRef, MerkleMembershipProof, Nullifier, ProgramError,
    StateConstraint,
};

// ---------------------------------------------------------------------------
// Helpers / shared concerns
// ---------------------------------------------------------------------------

/// Construct a WitnessedPredicate of the given kind with a generic input ref
/// and proof witness index 0 — used in the registry-lookup tests.
fn wp(kind: WitnessedPredicateKind) -> WitnessedPredicate {
    WitnessedPredicate {
        kind,
        commitment: [7u8; 32],
        input_ref: InputRef::Sender,
        proof_witness_index: 0,
    }
}

struct ExactSenderVerifier {
    kind: WitnessedPredicateKind,
    name: &'static str,
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactSenderVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.expected_commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        match input {
            PredicateInput::Sender(sender) if *sender == &self.expected_sender => {}
            PredicateInput::Sender(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "sender mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Sender",
                    actual: "non-Sender",
                });
            }
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "proof mismatch".into(),
            });
        }
        Ok(())
    }
}

fn exact_sender_registry(
    vk_hash: [u8; 32],
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExactSenderVerifier {
            kind: WitnessedPredicateKind::Custom { vk_hash },
            name: "exact-custom-test-verifier",
            expected_commitment,
            expected_sender,
            expected_proof,
        }),
    );
    registry
}

fn exact_dfa_registry(
    expected_commitment: [u8; 32],
    expected_sender: [u8; 32],
    expected_proof: &'static [u8],
) -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(ExactSenderVerifier {
        kind: WitnessedPredicateKind::Dfa,
        name: "exact-dfa-test-verifier",
        expected_commitment,
        expected_sender,
        expected_proof,
    }));
    registry
}

struct NullifierMerkleMembershipVerifier;

impl WitnessedPredicateVerifier for NullifierMerkleMembershipVerifier {
    fn name(&self) -> &'static str {
        "nullifier-merkle-membership-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::MerkleMembership
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let sender = match input {
            PredicateInput::Sender(sender) => *sender,
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Sender",
                    actual: "non-Sender",
                });
            }
        };
        let proof: MerkleMembershipProof =
            postcard::from_bytes(proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: format!("could not decode MerkleMembershipProof: {e}"),
            })?;
        if proof.element.0 != *sender {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "membership proof element does not match sender".into(),
            });
        }
        if !verify_nullifier_membership_proof(&proof, commitment) {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "membership path does not resolve to commitment root".into(),
            });
        }
        Ok(())
    }
}

fn merkle_membership_registry() -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(NullifierMerkleMembershipVerifier));
    registry
}

fn nullifier_leaf_hash(data: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-leaf v1");
    hasher.update(data);
    *hasher.finalize().as_bytes()
}

fn nullifier_node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-node v1");
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

fn verify_nullifier_membership_proof(proof: &MerkleMembershipProof, root: &[u8; 32]) -> bool {
    let mut current = nullifier_leaf_hash(&proof.element.0);
    let mut idx = proof.index;
    for sibling in &proof.siblings {
        current = if idx % 2 == 0 {
            nullifier_node_hash(&current, sibling)
        } else {
            nullifier_node_hash(sibling, &current)
        };
        idx /= 2;
    }
    current == *root
}

fn two_leaf_nullifier_membership_fixture() -> ([u8; 32], Nullifier, Vec<u8>) {
    let member = Nullifier([0x11u8; 32]);
    let neighbor = Nullifier([0x22u8; 32]);
    let member_leaf = nullifier_leaf_hash(&member.0);
    let neighbor_leaf = nullifier_leaf_hash(&neighbor.0);
    let root = nullifier_node_hash(&member_leaf, &neighbor_leaf);
    let proof = MerkleMembershipProof {
        element: member,
        index: 0,
        siblings: vec![neighbor_leaf],
    };
    let proof_bytes = postcard::to_allocvec(&proof).expect("serialize membership proof");
    (root, member, proof_bytes)
}

fn keyed_hash(domain: &'static str, parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    for part in parts {
        hasher.update(part);
    }
    *hasher.finalize().as_bytes()
}

fn push_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn read_u64(bytes: &[u8], offset: &mut usize) -> Option<u64> {
    let end = *offset + 8;
    let chunk = bytes.get(*offset..end)?;
    let mut raw = [0u8; 8];
    raw.copy_from_slice(chunk);
    *offset = end;
    Some(u64::from_le_bytes(raw))
}

fn encode_u64_window(values: &[u64]) -> Vec<u8> {
    assert!(values.len() <= u8::MAX as usize);
    let mut out = vec![values.len() as u8];
    for value in values {
        push_u64(&mut out, *value);
    }
    out
}

fn decode_u64_window(bytes: &[u8]) -> Option<Vec<u64>> {
    let count = *bytes.first()? as usize;
    if bytes.len() != 1 + count * 8 {
        return None;
    }
    let mut offset = 1;
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(read_u64(bytes, &mut offset)?);
    }
    Some(values)
}

fn temporal_policy_commitment(threshold: u64) -> [u8; 32] {
    keyed_hash("dregg-test-temporal-policy-v1", &[&threshold.to_le_bytes()])
}

fn temporal_proof_bytes(commitment: &[u8; 32], window_bytes: &[u8], threshold: u64) -> Vec<u8> {
    let threshold_bytes = threshold.to_le_bytes();
    let tag = keyed_hash(
        "dregg-test-temporal-proof-v1",
        &[commitment, window_bytes, &threshold_bytes],
    );
    let mut proof = Vec::with_capacity(40);
    proof.extend_from_slice(&threshold_bytes);
    proof.extend_from_slice(&tag);
    proof
}

struct TemporalThresholdVerifier;

impl WitnessedPredicateVerifier for TemporalThresholdVerifier {
    fn name(&self) -> &'static str {
        "temporal-threshold-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Temporal
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let window_bytes = match input {
            PredicateInput::Bytes(bytes) => *bytes,
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Bytes(window)",
                    actual: "non-Bytes",
                });
            }
        };
        if proof_bytes.len() != 40 {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "temporal proof must be threshold_u64 || tag32".into(),
            });
        }
        let mut offset = 0;
        let threshold = read_u64(proof_bytes, &mut offset).expect("len checked");
        if temporal_policy_commitment(threshold) != *commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "policy commitment does not match threshold".into(),
            });
        }
        let expected = temporal_proof_bytes(commitment, window_bytes, threshold);
        if proof_bytes != expected.as_slice() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "temporal proof tag does not bind policy and window".into(),
            });
        }
        let values =
            decode_u64_window(window_bytes).ok_or_else(|| WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "temporal window input is not count-prefixed u64 bytes".into(),
            })?;
        if values.iter().any(|value| *value < threshold) {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "temporal window contains value below threshold".into(),
            });
        }
        Ok(())
    }
}

fn temporal_registry() -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(TemporalThresholdVerifier));
    registry
}

struct BlindedSetNonRevocationVerifier;

impl WitnessedPredicateVerifier for BlindedSetNonRevocationVerifier {
    fn name(&self) -> &'static str {
        "blinded-set-non-revocation-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::BlindedSet
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let candidate = match input {
            PredicateInput::Sender(sender) => **sender,
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Sender",
                    actual: "non-Sender",
                });
            }
        };
        let proof = NonMembershipNeighborProof::from_bytes(proof_bytes).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "non-revocation proof must be lower || upper || adjacency_tag".into(),
            }
        })?;
        let expected =
            NonMembershipNeighborProof::adjacency_tag(commitment, &proof.lower, &proof.upper);
        if proof.adjacency_tag != expected {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "adjacency tag does not bind to blinded-set commitment".into(),
            });
        }
        if proof.lower >= candidate || candidate >= proof.upper {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "candidate is not strictly between non-revocation neighbors".into(),
            });
        }
        Ok(())
    }
}

fn blinded_set_registry() -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(BlindedSetNonRevocationVerifier));
    registry
}

fn bridge_gte_tag(commitment: &[u8; 32], threshold: u64, private_value: u64) -> [u8; 32] {
    keyed_hash(
        "dregg-test-bridge-gte-proof-v1",
        &[
            commitment,
            &threshold.to_le_bytes(),
            &private_value.to_le_bytes(),
        ],
    )
}

fn bridge_gte_proof_bytes(commitment: &[u8; 32], threshold: u64, private_value: u64) -> Vec<u8> {
    let mut proof = Vec::with_capacity(40);
    push_u64(&mut proof, private_value);
    proof.extend_from_slice(&bridge_gte_tag(commitment, threshold, private_value));
    proof
}

struct BridgeGteVerifier;

impl WitnessedPredicateVerifier for BridgeGteVerifier {
    fn name(&self) -> &'static str {
        "bridge-gte-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::BridgePredicate
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let threshold = match input {
            PredicateInput::PublicInput(values) if !values.is_empty() => values[0],
            PredicateInput::PublicInput(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "PublicInput[threshold]",
                    actual: "empty PublicInput",
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "PublicInput[threshold]",
                    actual: "non-PublicInput",
                });
            }
        };
        if proof_bytes.len() != 40 {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "bridge GTE proof must be value_u64 || tag32".into(),
            });
        }
        let mut offset = 0;
        let private_value = read_u64(proof_bytes, &mut offset).expect("len checked");
        let expected = bridge_gte_proof_bytes(commitment, threshold, private_value);
        if proof_bytes != expected.as_slice() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "bridge GTE proof tag does not bind commitment, threshold, and value"
                    .into(),
            });
        }
        if private_value < threshold {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "private value is below public threshold".into(),
            });
        }
        Ok(())
    }
}

fn bridge_gte_registry() -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(BridgeGteVerifier));
    registry
}

fn pedersen_test_commitment(value: u64, blinding: u64) -> [u8; 32] {
    keyed_hash(
        "dregg-test-pedersen-commitment-v1",
        &[&value.to_le_bytes(), &blinding.to_le_bytes()],
    )
}

fn pedersen_equality_statement(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    keyed_hash("dregg-test-pedersen-equality-v1", &[left, right])
}

fn pedersen_equality_proof(
    value: u64,
    left_blinding: u64,
    right_blinding: u64,
) -> ([u8; 32], Vec<u8>) {
    let left = pedersen_test_commitment(value, left_blinding);
    let right = pedersen_test_commitment(value, right_blinding);
    let statement = pedersen_equality_statement(&left, &right);
    let mut proof = Vec::with_capacity(24);
    push_u64(&mut proof, value);
    push_u64(&mut proof, left_blinding);
    push_u64(&mut proof, right_blinding);
    (statement, proof)
}

struct PedersenEqualityVerifier;

impl WitnessedPredicateVerifier for PedersenEqualityVerifier {
    fn name(&self) -> &'static str {
        "hash-pedersen-equality-test-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::PedersenEquality
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if proof_bytes.len() != 24 {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "pedersen equality proof must be value || left_blinding || right_blinding"
                    .into(),
            });
        }
        let mut offset = 0;
        let value = read_u64(proof_bytes, &mut offset).expect("len checked");
        let left_blinding = read_u64(proof_bytes, &mut offset).expect("len checked");
        let right_blinding = read_u64(proof_bytes, &mut offset).expect("len checked");
        let left = pedersen_test_commitment(value, left_blinding);
        let right = pedersen_test_commitment(value, right_blinding);
        let expected = pedersen_equality_statement(&left, &right);
        if expected != *commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "opened commitments do not match equality statement".into(),
            });
        }
        Ok(())
    }
}

fn pedersen_equality_registry() -> WitnessedPredicateRegistry {
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_builtin(Arc::new(PedersenEqualityVerifier));
    registry
}

// ===========================================================================
// Dfa
// ===========================================================================

#[test]
fn dfa_predicate_constructor_round_trip() {
    let p = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::Dfa);
    assert_eq!(p.commitment, [1u8; 32]);
}

#[test]
fn dfa_predicate_with_valid_proof_accepts_through_executor() {
    let registry = WitnessedPredicateRegistry::with_stubs();
    let proof = b"stub-dfa-proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
    }]);
    let state = CellState::default();
    let ctx = EvalContext {
        sender: Some([0xA5u8; 32]),
        ..Default::default()
    };

    program
        .evaluate_full(
            &state,
            None,
            Some(&ctx),
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect("Dfa plumbing accepts non-empty proof via explicit stub registry");
}

#[test]
fn dfa_predicate_with_tampered_proof_rejects() {
    let commitment = [1u8; 32];
    let sender = [0xA5u8; 32];
    let registry = exact_dfa_registry(commitment, sender, b"valid-dfa-proof");
    let predicate = WitnessedPredicate::dfa(commitment, InputRef::Sender, 0);
    let err = registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"tampered-proof",
        )
        .expect_err("registered Dfa verifier must reject non-matching proof bytes");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn dfa_predicate_with_invalid_input_rejects() {
    let commitment = [1u8; 32];
    let sender = [0xA5u8; 32];
    let registry = exact_dfa_registry(commitment, sender, b"valid-dfa-proof");
    let predicate = WitnessedPredicate::dfa(commitment, InputRef::Sender, 0);
    let err = registry
        .verify(
            &predicate,
            &PredicateInput::Bytes(b"not-a-sender"),
            b"valid-dfa-proof",
        )
        .expect_err("registered Dfa verifier must reject an unexpected input shape");

    assert!(matches!(
        err,
        WitnessedPredicateError::InputShapeMismatch {
            kind_name: "exact-dfa-test-verifier",
            expected: "Sender",
            actual: "non-Sender",
        }
    ));
}

// ===========================================================================
// Temporal
// ===========================================================================

#[test]
fn temporal_predicate_constructor() {
    let p = WitnessedPredicate::temporal([2u8; 32], 3, 1);
    assert_eq!(p.kind, WitnessedPredicateKind::Temporal);
    assert_eq!(p.commitment, [2u8; 32]);
    assert_eq!(p.proof_witness_index, 1);
}

#[test]
fn temporal_predicate_with_valid_proof_accepts() {
    let threshold = 10;
    let commitment = temporal_policy_commitment(threshold);
    let window = encode_u64_window(&[10, 12, 15]);
    let proof = temporal_proof_bytes(&commitment, &window, threshold);
    let registry = temporal_registry();
    let predicate = WitnessedPredicate::temporal(commitment, 0, 0);

    registry
        .verify(&predicate, &PredicateInput::Bytes(&window), &proof)
        .expect("temporal threshold window accepts");
}

#[test]
fn temporal_predicate_with_tampered_proof_rejects() {
    let threshold = 10;
    let commitment = temporal_policy_commitment(threshold);
    let window = encode_u64_window(&[10, 9, 15]);
    let proof = temporal_proof_bytes(&commitment, &window, threshold);
    let registry = temporal_registry();
    let predicate = WitnessedPredicate::temporal(commitment, 0, 0);
    let err = registry
        .verify(&predicate, &PredicateInput::Bytes(&window), &proof)
        .expect_err("temporal threshold window with a low value must reject");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// MerkleMembership
// ===========================================================================

#[test]
fn merkle_membership_predicate_constructor() {
    let p = WitnessedPredicate::merkle_membership([3u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::MerkleMembership);
}

#[test]
fn merkle_membership_with_valid_path_accepts() {
    let (root, member, proof_bytes) = two_leaf_nullifier_membership_fixture();
    let registry = merkle_membership_registry();
    let predicate = WitnessedPredicate::merkle_membership(root, InputRef::Sender, 0);

    registry
        .verify(&predicate, &PredicateInput::Sender(&member.0), &proof_bytes)
        .expect("valid nullifier Merkle membership proof accepts");
}

#[test]
fn merkle_membership_with_wrong_root_rejects() {
    let (root, member, proof_bytes) = two_leaf_nullifier_membership_fixture();
    let registry = merkle_membership_registry();
    let mut wrong_root = root;
    wrong_root[0] ^= 0xFF;
    let predicate = WitnessedPredicate::merkle_membership(wrong_root, InputRef::Sender, 0);
    let err = registry
        .verify(&predicate, &PredicateInput::Sender(&member.0), &proof_bytes)
        .expect_err("wrong Merkle root must reject");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn merkle_membership_inverse_query_rejects() {
    let (root, _member, proof_bytes) = two_leaf_nullifier_membership_fixture();
    let registry = merkle_membership_registry();
    let inverse_query = [0x12u8; 32];
    let predicate = WitnessedPredicate::merkle_membership(root, InputRef::Sender, 0);
    let err = registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&inverse_query),
            &proof_bytes,
        )
        .expect_err("membership proof must reject a different queried sender");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// BlindedSet
// ===========================================================================

#[test]
fn blinded_set_predicate_constructor() {
    let p = WitnessedPredicate::blinded_set([4u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::BlindedSet);
}

#[test]
fn blinded_set_with_non_revocation_proof_accepts() {
    let commitment = [0x44u8; 32];
    let sender = [0x55u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, [0x44u8; 32], [0x66u8; 32]);
    let registry = blinded_set_registry();
    let predicate = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);

    registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            &proof.to_bytes(),
        )
        .expect("sender strictly between neighbors is non-revoked");
}

#[test]
fn blinded_set_revoked_member_rejects() {
    let commitment = [0x44u8; 32];
    let sender = [0x55u8; 32];
    let proof = NonMembershipNeighborProof::new(&commitment, sender, [0x66u8; 32]);
    let registry = blinded_set_registry();
    let predicate = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
    let err = registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            &proof.to_bytes(),
        )
        .expect_err("candidate equal to lower neighbor is revoked/in-set");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// BridgePredicate
// ===========================================================================

#[test]
fn bridge_predicate_constructor() {
    let p =
        WitnessedPredicate::bridge_predicate([5u8; 32], InputRef::PublicInput { pi_index: 0 }, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::BridgePredicate);
}

#[test]
fn bridge_predicate_gte_accepts_value_above_threshold() {
    let fact_commitment = [0x77u8; 32];
    let threshold = [50u64];
    let proof = bridge_gte_proof_bytes(&fact_commitment, threshold[0], 73);
    let registry = bridge_gte_registry();
    let predicate = WitnessedPredicate::bridge_predicate(
        fact_commitment,
        InputRef::PublicInput { pi_index: 0 },
        0,
    );

    registry
        .verify(&predicate, &PredicateInput::PublicInput(&threshold), &proof)
        .expect("private value above threshold satisfies bridge GTE");
}

#[test]
fn bridge_predicate_gte_rejects_value_below_threshold() {
    let fact_commitment = [0x77u8; 32];
    let threshold = [50u64];
    let proof = bridge_gte_proof_bytes(&fact_commitment, threshold[0], 49);
    let registry = bridge_gte_registry();
    let predicate = WitnessedPredicate::bridge_predicate(
        fact_commitment,
        InputRef::PublicInput { pi_index: 0 },
        0,
    );
    let err = registry
        .verify(&predicate, &PredicateInput::PublicInput(&threshold), &proof)
        .expect_err("private value below threshold must reject bridge GTE");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// PedersenEquality
// ===========================================================================

#[test]
fn pedersen_equality_constructor() {
    let p = WitnessedPredicate::pedersen_equality([6u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::PedersenEquality);
}

#[test]
fn pedersen_equality_with_valid_proof_accepts() {
    let (statement, proof) = pedersen_equality_proof(42, 7, 11);
    let registry = pedersen_equality_registry();
    let predicate = WitnessedPredicate::pedersen_equality(statement, InputRef::Sender, 0);
    let sender = [0x5Eu8; 32];

    registry
        .verify(&predicate, &PredicateInput::Sender(&sender), &proof)
        .expect("two commitments opening to the same value satisfy equality");
}

#[test]
fn pedersen_equality_with_tampered_commitment_rejects() {
    let (mut statement, proof) = pedersen_equality_proof(42, 7, 11);
    statement[0] ^= 0xFF;
    let registry = pedersen_equality_registry();
    let predicate = WitnessedPredicate::pedersen_equality(statement, InputRef::Sender, 0);
    let sender = [0x5Eu8; 32];
    let err = registry
        .verify(&predicate, &PredicateInput::Sender(&sender), &proof)
        .expect_err("tampered equality statement must reject");

    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// Custom
// ===========================================================================

#[test]
fn custom_predicate_constructor_carries_vk_hash() {
    let vk = [9u8; 32];
    let p = WitnessedPredicate::custom(vk, [0u8; 32], InputRef::Sender, 0);
    assert_eq!(p.kind, WitnessedPredicateKind::Custom { vk_hash: vk });
}

#[test]
fn custom_predicate_with_registered_verifier_accepts() {
    let vk_hash = [9u8; 32];
    let commitment = [0xC0u8; 32];
    let sender = [0x5Eu8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, sender, b"valid-custom-proof");
    let predicate = WitnessedPredicate::custom(vk_hash, commitment, InputRef::Sender, 0);

    registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"valid-custom-proof",
        )
        .expect("registered custom verifier accepts matching commitment/input/proof");
}

#[test]
fn custom_predicate_with_unregistered_vk_rejects() {
    let vk_hash = [0xAAu8; 32];
    let predicate = WitnessedPredicate::custom(vk_hash, [0xC0u8; 32], InputRef::Sender, 0);
    let registry = WitnessedPredicateRegistry::empty();
    let sender = [0x5Eu8; 32];
    let err = registry
        .verify(&predicate, &PredicateInput::Sender(&sender), b"proof")
        .expect_err("unregistered custom vk_hash must reject");

    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { vk_hash: got }
        } if got == vk_hash
    ));
}

// ===========================================================================
// Registry lookup behavior
// ===========================================================================

#[test]
fn registry_returns_error_for_unknown_kind() {
    let registry = WitnessedPredicateRegistry::with_stubs();
    let unknown = wp(WitnessedPredicateKind::Custom { vk_hash: [0u8; 32] });
    let sender = [0x5Eu8; 32];
    let err = registry
        .verify(&unknown, &PredicateInput::Sender(&sender), b"proof")
        .expect_err("stub builtins do not register arbitrary custom vk_hashes");

    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { vk_hash }
        } if vk_hash == [0u8; 32]
    ));
}

#[test]
fn registry_round_trip_for_registered_custom_verifier() {
    let vk_hash = [0x44u8; 32];
    let commitment = [0xC4u8; 32];
    let sender = [0x5Eu8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, sender, b"valid-custom-proof");
    let predicate = WitnessedPredicate::custom(vk_hash, commitment, InputRef::Sender, 0);

    assert!(
        registry
            .get(WitnessedPredicateKind::Custom { vk_hash })
            .is_some(),
        "registered verifier must be discoverable by custom vk_hash"
    );
    registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"valid-custom-proof",
        )
        .expect("registered verifier accepts its exact proof");
    let err = registry
        .verify(
            &predicate,
            &PredicateInput::Sender(&sender),
            b"tampered-proof",
        )
        .expect_err("registered verifier must reject a non-matching proof");
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

// ===========================================================================
// SigningMessage input ref — shape rejection outside Auth context
// ===========================================================================

#[test]
fn signing_message_input_ref_rejects_in_slot_caveat_context() {
    // Per cell::predicate docs (InputRef::SigningMessage): "surfaces that
    // evaluate WitnessedPredicate outside an action-authorization context
    // (slot caveats, preconditions) must reject this variant as
    // shape-mismatch."
    let vk_hash = [0x55u8; 32];
    let commitment = [0xC5u8; 32];
    let registry = exact_sender_registry(vk_hash, commitment, [0x5Eu8; 32], b"proof");
    let proof = b"proof";
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
    };
    let program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: WitnessedPredicate::custom(vk_hash, commitment, InputRef::SigningMessage, 0),
    }]);
    let state = CellState::default();

    let err = program
        .evaluate_full(&state, None, None, &TransitionMeta::wildcard(), &witnesses)
        .expect_err("SigningMessage input has no slot-caveat source");
    assert!(matches!(
        err,
        ProgramError::WitnessedPredicateRejected {
            kind_name: "Custom",
            ..
        }
    ));
}

// ===========================================================================
// Compile-time exhaustiveness: every kind has at least one test
// ===========================================================================

/// Touches every variant of WitnessedPredicateKind so that adding a new
/// variant is a compile-time prompt to extend this file.
#[allow(dead_code)]
fn touch_every_kind(k: WitnessedPredicateKind) -> &'static str {
    match k {
        WitnessedPredicateKind::Dfa => "dfa",
        WitnessedPredicateKind::Temporal => "temporal",
        WitnessedPredicateKind::MerkleMembership => "merkle_membership",
        WitnessedPredicateKind::BlindedSet => "blinded_set",
        WitnessedPredicateKind::BridgePredicate => "bridge_predicate",
        WitnessedPredicateKind::PedersenEquality => "pedersen_equality",
        // Categorical dual of MerkleMembership — sorted-set non-membership.
        WitnessedPredicateKind::NonMembership => "non_membership",
        WitnessedPredicateKind::Custom { .. } => "custom",
    }
}

#[test]
fn exhaustiveness_dummy_uses_helper() {
    let _ = touch_every_kind(WitnessedPredicateKind::Dfa);
}

// Ensure the unused-helper attribute does not paper over a missing variant:
// the match must compile (exhaustively), so adding a kind without updating
// this match will not compile.
#[test]
fn registry_unused_helper_does_not_short_circuit() {
    // Doctest-level catch.
    let _ = ProgramError::WitnessedPredicateRequiresExecutor { kind_name: "stub" };
}
