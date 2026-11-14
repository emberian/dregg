//! # `Receipt` — the first of the SDK's two user-facing nouns.
//!
//! A [`Receipt`] is dregg's canonical proof-of-execution artifact: the
//! committed turn's hashes (turn / forest / effects), the pre/post state
//! roots, the agent cell, the federation binding, and the receipt-chain
//! link `previous_receipt_hash`. Every authorized submission
//! ([`AuthorizedTurn::submit`](crate::turns::AuthorizedTurn::submit))
//! returns one.
//!
//! The proof is **lazily attached**: a `Receipt` is born proofless (the
//! commit decision is the executor's; the STARK is additive attestation)
//! and a [`TurnProof`] — the composed full-turn STARK — can be attached
//! when a prover produces one (the node's async prove pool, a local
//! [`prove_full_turn`](crate::full_turn_proof::prove_full_turn) run, or a
//! fetched artifact). [`Receipt::proof()`] reads it; the internal proof
//! plumbing (`ComposedProof`, sub-proof components, PI layouts) stays off
//! the public surface.
//!
//! The second noun is [`AttestedHistory`](dregg_lightclient::AttestedHistory)
//! — the light-client artifact: the verdict obtained by verifying ONE
//! succinct whole-history aggregate. A `Receipt` says "this turn committed,
//! here is its place in a chain"; an `AttestedHistory` says "every turn of
//! this whole history executed correctly" — and between them that is the
//! entire user-facing proof story.

use std::sync::{Arc, OnceLock};

use dregg_turn::TurnReceipt;

use crate::full_turn_proof::{FullTurnProof, FullTurnVerifyError};

/// The proof attached to a [`Receipt`]: the composed full-turn STARK
/// (state transition + authorization + membership + conservation +
/// non-revocation in one verification), opaque on the public surface.
///
/// Obtain one from the proving pipeline
/// ([`prove_full_turn`](crate::full_turn_proof::prove_full_turn) /
/// [`prove_turn_self_sovereign`](crate::full_turn_proof::prove_turn_self_sovereign))
/// or by decoding a node-attached artifact, then attach it with
/// [`Receipt::attach_proof`].
#[derive(Clone, Debug)]
pub struct TurnProof(Arc<FullTurnProof>);

impl TurnProof {
    /// Wrap a composed full-turn proof.
    pub fn new(proof: FullTurnProof) -> Self {
        TurnProof(Arc::new(proof))
    }

    /// The turn hash this proof is bound to (replay protection: a proof
    /// only attests the turn it names).
    pub fn turn_hash(&self) -> [u8; 32] {
        self.0.turn_hash
    }

    /// The wire-serialized proof bytes.
    pub fn bytes(&self) -> &[u8] {
        &self.0.proof_bytes
    }

    /// Verify this proof against the turn it must attest and the expected pre/post
    /// state commitments.
    ///
    /// Thin delegation to
    /// [`verify_full_turn`](crate::full_turn_proof::verify_full_turn);
    /// freshness-critical verifiers (no-double-spend) should use
    /// [`verify_full_turn_bound`](crate::full_turn_proof::verify_full_turn_bound)
    /// on the inner proof via [`Self::inner`].
    ///
    /// ⚠ **`expected_turn_hash` must come from the CALLER, not from this object.** The
    /// docblock on [`Self::turn_hash`] has always claimed "replay protection: a proof only
    /// attests the turn it names", and until the turn-identity flag day nothing enforced
    /// it — this method dropped the turn entirely. Passing [`Self::turn_hash`] back in here
    /// would restore the appearance and not the property: the comparison would be `x != x`
    /// and could not fire. Pass the hash of the turn you are checking (`turn.hash()`, or the
    /// hash you fetched the artifact by).
    pub fn verify(
        &self,
        expected_turn_hash: [u8; 32],
        expected_old_commit: [dregg_circuit::BabyBear; 8],
        expected_new_commit: [dregg_circuit::BabyBear; 8],
    ) -> Result<(), FullTurnVerifyError> {
        crate::full_turn_proof::verify_full_turn(
            &self.0,
            expected_turn_hash,
            expected_old_commit,
            expected_new_commit,
        )
    }

    /// Access the underlying composed proof (plumbing surface, for
    /// verifiers that need the bound entry points or component flags).
    pub fn inner(&self) -> &FullTurnProof {
        &self.0
    }
}

impl From<FullTurnProof> for TurnProof {
    fn from(p: FullTurnProof) -> Self {
        TurnProof::new(p)
    }
}

/// **The receipt noun.** A committed turn's proof-of-execution, with the
/// composed STARK proof lazily attached. See the module docs.
///
/// Dereferences to the wire-level [`TurnReceipt`], so every field and
/// method of the canonical receipt shape (`receipt_hash()`, `turn_hash`,
/// `post_state_hash`, …) is available directly on `Receipt`.
#[derive(Clone, Debug)]
pub struct Receipt {
    receipt: TurnReceipt,
    proof: OnceLock<TurnProof>,
    proof_status_hint: Option<String>,
}

impl Receipt {
    /// Wrap a committed receipt (proofless; attach later).
    pub fn new(receipt: TurnReceipt) -> Self {
        Receipt {
            receipt,
            proof: OnceLock::new(),
            proof_status_hint: None,
        }
    }

    /// Preserve the node's policy hint without treating it as verified evidence.
    /// In particular, `not_required` never satisfies `has_proof` or verification.
    pub fn with_proof_status_hint(mut self, status: Option<String>) -> Self {
        self.proof_status_hint = status;
        self
    }

    pub fn proof_status_hint(&self) -> Option<&str> {
        self.proof_status_hint.as_deref()
    }

    /// The attached proof, if one has been attached (lazily — receipts are
    /// born proofless; the STARK is additive attestation produced by a
    /// prover after commit).
    pub fn proof(&self) -> Option<&TurnProof> {
        self.proof.get()
    }

    /// Whether a proof has been attached. A node policy of `not_required` is
    /// signature attestation only and never satisfies this check.
    pub fn has_proof(&self) -> bool {
        self.proof.get().is_some()
    }

    /// Attach the composed turn proof. Idempotent-at-first-writer: returns
    /// `Err` with the rejected proof if one was already attached (a receipt
    /// never silently swaps attestations) or if the proof names a different
    /// `turn_hash` than this receipt (a mis-bound attachment is refused,
    /// not stored).
    pub fn attach_proof(&self, proof: impl Into<TurnProof>) -> Result<(), TurnProof> {
        let proof = proof.into();
        if proof.turn_hash() != self.receipt.turn_hash {
            return Err(proof);
        }
        self.proof.set(proof)
    }

    /// Lazily attach: return the attached proof, producing it with `f` if
    /// none is attached yet. A produced proof bound to the wrong turn hash
    /// is refused (error), never stored.
    pub fn proof_or_attach<E>(
        &self,
        f: impl FnOnce() -> Result<TurnProof, E>,
    ) -> Result<&TurnProof, ProofAttachError<E>> {
        if self.proof.get().is_none() {
            let produced = f().map_err(ProofAttachError::Produce)?;
            if produced.turn_hash() != self.receipt.turn_hash {
                return Err(ProofAttachError::WrongTurn {
                    expected: self.receipt.turn_hash,
                    got: produced.turn_hash(),
                });
            }
            // A racing attach of the same receipt's proof is fine; first
            // writer wins and we read whatever landed.
            let _ = self.proof.set(produced);
        }
        Ok(self.proof.get().expect("set above or already present"))
    }

    /// The wire-level receipt (canonical serialization shape).
    pub fn as_turn_receipt(&self) -> &TurnReceipt {
        &self.receipt
    }

    /// Unwrap into the wire-level receipt (drops any attached proof).
    pub fn into_turn_receipt(self) -> TurnReceipt {
        self.receipt
    }
}

/// Why [`Receipt::proof_or_attach`] failed.
#[derive(Debug)]
pub enum ProofAttachError<E> {
    /// The producer closure failed.
    Produce(E),
    /// The produced proof is bound to a different turn than this receipt.
    WrongTurn { expected: [u8; 32], got: [u8; 32] },
}

impl From<TurnReceipt> for Receipt {
    fn from(receipt: TurnReceipt) -> Self {
        Receipt::new(receipt)
    }
}

impl std::ops::Deref for Receipt {
    type Target = TurnReceipt;
    fn deref(&self) -> &TurnReceipt {
        &self.receipt
    }
}

impl serde::Serialize for Receipt {
    /// Serializes as the wire-level [`TurnReceipt`] — the proof travels
    /// separately (it is attestation about the receipt, not part of it).
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.receipt.serialize(s)
    }
}

impl<'de> serde::Deserialize<'de> for Receipt {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(Receipt::new(TurnReceipt::deserialize(d)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn not_required_hint_is_never_a_validity_proof() {
        let receipt = Receipt::new(TurnReceipt::default())
            .with_proof_status_hint(Some("not_required".into()));
        assert_eq!(receipt.proof_status_hint(), Some("not_required"));
        assert!(!receipt.has_proof());
        assert!(receipt.proof().is_none());
        let plain = Receipt::new(TurnReceipt::default());
        assert_eq!(receipt.receipt_hash(), plain.receipt_hash());
        assert_eq!(
            postcard::to_stdvec(&receipt).unwrap(),
            postcard::to_stdvec(&plain).unwrap()
        );
    }

    #[test]
    fn receipt_derefs_and_roundtrips() {
        let tr = TurnReceipt {
            turn_hash: [7u8; 32],
            ..Default::default()
        };
        let r = Receipt::new(tr.clone());
        assert_eq!(r.turn_hash, [7u8; 32]);
        assert_eq!(r.receipt_hash(), tr.receipt_hash());
        assert!(!r.has_proof());
        let json = serde_json::to_string(&r).unwrap();
        let back: Receipt = serde_json::from_str(&json).unwrap();
        assert_eq!(back.turn_hash, [7u8; 32]);
    }
}
