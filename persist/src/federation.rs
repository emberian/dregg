//! Federation state persistent storage.
//!
//! Persists the revocation set (which token IDs have been revoked) and the
//! attested roots (consensus-signed Merkle roots at each block height).
//!
//! The revocation set is stored as individual key-value pairs for O(1) lookup.
//! Attested roots are stored indexed by height for ordered retrieval.

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

pub use dregg_types::{FederationId, PublicKey, Signature, ThresholdQC};

pub use dregg_federation::frost::MlDsaPublicKey;

/// One committee member's HYBRID finalization-vote signature over an attested
/// root — BOTH halves (ed25519 ∧ ML-DSA-65), plus a REDUNDANT copy of the
/// voter's ML-DSA-65 public key carried ALONGSIDE the signature.
///
/// The `ml_dsa_pubkey` field is a wire convenience (a copy of the voter's key),
/// NOT a trust root. On re-verify, [`Self::verify_finalization_quorum`] PINS it
/// to the genesis-ENROLLED ML-DSA roster passed at restart: the self-carried key
/// must EQUAL `ml_dsa_committee[voter_index]` and the PQ half is checked under
/// that enrolled key. A restarting node therefore needs the enrolled ML-DSA
/// roster aligned with the committee it verifies against (the current committee's
/// via `known_federation_ml_dsa_keys`; historical committees carry an aligned
/// `derived_committee_ml_dsa_history`, which may be EMPTY for a purely on-chain
/// amended committee — in which case the hybrid re-verify REFUSES that root
/// rather than downgrade to ed25519-only).
///
/// This closes the quantum-forgery downgrade: without the pin, a quantum
/// adversary who breaks ed25519 for member `P` could attach its OWN fresh ML-DSA
/// keypair and a PQ signature valid under it, and BOTH halves would pass (the PQ
/// half was checked against the attacker's self-carried key). With the pin, the
/// PQ half must verify under `P`'s enrolled key, which the adversary does not
/// hold — so a quantum adversary who breaks ed25519 alone still cannot re-anchor
/// a forged root on restart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuorumSignature {
    /// The voter's federation Ed25519 public key (the committee identity).
    pub voter: PublicKey,
    /// The ed25519 (CLASSICAL) signature over
    /// [`dregg_types::finalization_vote_signing_message`].
    pub signature: Signature,
    /// A REDUNDANT copy of the voter's ML-DSA-65 (FIPS 204) public key, as its
    /// 1952 serialized bytes (`Vec<u8>` because the 1952-byte array is beyond
    /// serde's array-derive ceiling). At verify time this is PINNED equal to the
    /// enrolled roster key for the voter's committee index — never trusted on its
    /// own.
    pub ml_dsa_pubkey: Vec<u8>,
    /// The ML-DSA-65 (POST-QUANTUM) signature over the SAME canonical bytes as
    /// `signature`, verified under the ENROLLED key. The quorum counts a signer
    /// only when BOTH halves verify (and the enrolled-key pin holds), so a
    /// quantum adversary who breaks ed25519 alone still cannot re-anchor a forged
    /// root on restart.
    pub pq_signature: Vec<u8>,
}

impl QuorumSignature {
    /// **The ONE production mapping** from a stored finalization-vote signature
    /// to the wire [`dregg_types::HybridQuorumSig`] carried on an
    /// `AttestedRoot::hybrid_quorum`.
    ///
    /// ⚑ It is a named function rather than three inline `.map(|qs| …)` closures
    /// because the field it feeds was, until this change, checked by one
    /// consumer against a preimage these signatures were never over. A test that
    /// assembles the wire quorum by hand is a test of the test; every producer
    /// (`node/src/blocklace_sync.rs` on both finalized paths, `node/src/api.rs`'s
    /// anchor endpoint) and every exhibit now goes through here, so a root built
    /// in a test is byte-for-byte the shape the node builds.
    pub fn to_hybrid(&self) -> dregg_types::HybridQuorumSig {
        dregg_types::HybridQuorumSig {
            pubkey: self.voter,
            signature: self.signature,
            ml_dsa_pubkey: self.ml_dsa_pubkey.clone(),
            pq_signature: self.pq_signature.clone(),
        }
    }
}

/// Map a whole assembled finalization quorum onto the wire `hybrid_quorum`.
/// See [`QuorumSignature::to_hybrid`] for why this is not an inline closure.
pub fn hybrid_quorum_from_finalization_quorum(
    quorum: &[QuorumSignature],
) -> Vec<dregg_types::HybridQuorumSig> {
    quorum.iter().map(QuorumSignature::to_hybrid).collect()
}

/// A stored attested root, capturing the federation's consensus state at a
/// particular block height.
///
/// Uses the canonical `dregg_types::PublicKey` (32 bytes) and
/// `dregg_types::Signature` (64 bytes) for correct Ed25519 representation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredAttestedRoot {
    /// The Merkle root of the revocation tree (cell state).
    pub merkle_root: [u8; 32],
    /// The note commitment tree root.
    #[serde(default)]
    pub note_tree_root: Option<[u8; 32]>,
    /// The nullifier set root.
    #[serde(default)]
    pub nullifier_set_root: Option<[u8; 32]>,
    /// The block height at which this root was agreed upon.
    pub height: u64,
    /// Unix timestamp (seconds) when finalized.
    pub timestamp: i64,
    /// The blocklace block id this attestation is anchored to.
    /// `None` for legacy roots; production roots from the live node carry it.
    #[serde(default)]
    pub blocklace_block_id: Option<[u8; 32]>,
    /// The Cordial Miners finality round at the anchoring block.
    #[serde(default)]
    pub finality_round: Option<u64>,
    /// Quorum signatures: Vec of (public_key, signature) with FULL 64-byte sigs.
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold aggregate QC (serialized BLS).
    pub threshold_qc: Option<ThresholdQC>,
    /// The number of signatures required for validity.
    pub threshold: usize,
    /// The federation id this attestation is produced by (v3 binding).
    /// `FederationId::PLACEHOLDER` for legacy roots produced before v3.
    #[serde(default)]
    pub federation_id: FederationId,
    /// v4 (#80): Merkle root over the canonical `receipt_hash()` of every
    /// receipt this attestation covers. `None` for legacy roots predating
    /// the receipt-stream binding. See `dregg_types::AttestedRoot`.
    #[serde(default)]
    pub receipt_stream_root: Option<[u8; 32]>,
    /// N3 committee-restart fix (Fix B): the assembled quorum of committee
    /// **finalization votes** over this root's `(blocklace_block_id,
    /// merkle_root, receipt_stream_root)` — each a distinct committee member's
    /// hybrid signature over
    /// [`dregg_types::finalization_vote_signing_message`] (v4).
    ///
    /// ⚑ **v4 is why this record is now more than a restart anchor.** Through v3
    /// the vote preimage was `(block_id, merkle_root)` only — a whole-ledger
    /// BLAKE3 image and a block id, covering no value derived from the TURN the
    /// block carried. Absorbing `receipt_stream_root` makes these same
    /// signatures the committee's statement about a per-turn value, which is
    /// what `dregg_federation::TurnAnchorV1` needs and what it refused for
    /// lack of on any federation with `threshold > 1`.
    ///
    /// This is the record that lets a FULL-MODE committee node restart cleanly.
    /// `quorum_signatures` carries the local node's signature over the full
    /// `signing_message()` preimage (the light-client attestation); a full-mode
    /// node only ever holds ONE such local signature synchronously, so on its
    /// own it is `1 < threshold` and cannot re-anchor. `finalization_quorum`
    /// instead accumulates the >=threshold cross-node vote signatures (which
    /// arrive async over gossip and are back-filled here as the quorum forms),
    /// verified on restart by [`Self::verify_finalization_quorum`]. Empty for
    /// legacy roots and for a freshly persisted head whose vote quorum has not
    /// yet assembled (the anchor recovers to the last quorum-carrying root).
    ///
    /// HYBRID: each [`QuorumSignature`] carries BOTH the ed25519 and the ML-DSA-65
    /// half PLUS a redundant copy of the voter's ML-DSA public key, so the restart
    /// re-verifier re-checks the FULL hybrid quorum (classical ∧ pq) — with the PQ
    /// half PINNED to the genesis-enrolled ML-DSA roster the restart threads in
    /// (`verify_finalization_quorum`'s `ml_dsa_committee`), never the self-carried
    /// key. Widening this field changes the postcard wire
    /// shape of a `StoredAttestedRoot`: postcard is non-self-describing, so
    /// attested roots persisted before this change will NOT decode after upgrade.
    /// That is ACCEPTED (state wipe on upgrade, as prior schema additions were) —
    /// no versioned decode is provided by design; this is a mesh flag-day field.
    #[serde(default)]
    pub finalization_quorum: Vec<QuorumSignature>,
}

impl StoredAttestedRoot {
    /// Check structural completeness only (QC present, threshold count met).
    ///
    /// Does NOT verify signatures. For trusted verification, use
    /// [`verify_signatures`](Self::verify_signatures) with the committee keys.
    ///
    /// ⚑ THE PREDICATE WAS WRONG, NOT THE POPULATION (2026-08-08). Until this
    /// change the body was `quorum_signatures.len() >= threshold` alone. On a
    /// FULL-MODE node `quorum_signatures` structurally holds exactly ONE entry —
    /// this node's own light-client signature over [`Self::signing_message`],
    /// which is all a single process can produce synchronously; the field's own
    /// docs say so. The cross-node committee agreement lands in
    /// [`Self::finalization_quorum`], back-filled as the >=threshold hybrid
    /// finalization votes arrive over gossip. So every genuinely finalized root
    /// on every full-mode federation read `sigs=1 thr=3 complete=false` while
    /// carrying a real quorum of 3–4, and any consumer treating this (or its
    /// `is_valid` alias) as "final" got `false` on roots that WERE final.
    ///
    /// The fix is to consult the population that actually carries the quorum.
    /// Both legs count DISTINCT signers, mirroring [`Self::verify_signatures`]:
    /// duplicating one row never manufactures a quorum. `threshold == 0` is not
    /// an authority and is refused here as it already is there — an empty
    /// signature set over a zero threshold used to return `true`.
    ///
    /// STILL COUNT-ONLY. This says "enough distinct committee identities are
    /// attached", never "their signatures verify". Cryptographic verdicts come
    /// from [`Self::verify_signatures`] (light-client leg) and
    /// [`Self::verify_finalization_quorum`] (committee-vote leg).
    pub fn is_structurally_complete(&self) -> bool {
        if self.threshold_qc.is_some() {
            return true;
        }
        if self.threshold == 0 {
            return false;
        }
        self.distinct_local_signers() >= self.threshold
            || self.distinct_finalization_voters() >= self.threshold
    }

    /// Distinct committee identities in `quorum_signatures` (the light-client
    /// attestation population). Count-only; no signature is checked.
    pub fn distinct_local_signers(&self) -> usize {
        self.quorum_signatures
            .iter()
            .map(|(pk, _)| *pk)
            .collect::<std::collections::HashSet<_>>()
            .len()
    }

    /// Distinct committee identities in `finalization_quorum` (the cross-node
    /// committee-vote population). Count-only; no signature is checked — the
    /// cryptographic leg is [`Self::verify_finalization_quorum`].
    pub fn distinct_finalization_voters(&self) -> usize {
        self.finalization_quorum
            .iter()
            .map(|qs| qs.voter)
            .collect::<std::collections::HashSet<_>>()
            .len()
    }

    /// Deprecated alias for [`is_structurally_complete`](Self::is_structurally_complete).
    #[deprecated(
        note = "Use is_structurally_complete() (count-only) or verify_signatures() for cryptographic verification"
    )]
    pub fn is_valid(&self) -> bool {
        self.is_structurally_complete()
    }

    /// The quorum bar this root must clear against `committee`.
    ///
    /// ⚑ The stored `threshold` field is NOT covered by any signed preimage
    /// (`signing_message` / `finalization_vote_signing_message` omit it), so an
    /// offline store tamper can rewrite it to `1` and promote a single member
    /// signature into a "verified quorum". The committee being verified against
    /// therefore sets the FLOOR: the strict BFT supermajority of ITS size
    /// (`⌊2n/3⌋+1` — the same `dregg_blocklace::supermajority_threshold` every
    /// live quorum is assembled at). The self-declared field can only RAISE the
    /// bar, never lower it below that floor. n=1 (solo) floors at 1, so solo
    /// semantics are unchanged.
    fn required_quorum(&self, committee: &[PublicKey]) -> usize {
        self.threshold
            .max(dregg_blocklace::supermajority_threshold(committee.len()))
    }

    /// Verify signatures cryptographically against a set of known committee keys.
    ///
    /// Checks that the quorum bar is met AND each signature verifies against
    /// the corresponding public key in `committee`.  Quorums count distinct
    /// committee identities: duplicating one valid `(key, signature)` row never
    /// manufactures a quorum, and a zero threshold is not an authority. The bar
    /// is [`Self::required_quorum`] — the committee's own supermajority, which
    /// the stored (unsigned, tamperable) `threshold` field can raise but never
    /// lower.
    pub fn verify_signatures(&self, committee: &[PublicKey]) -> bool {
        let required = self.required_quorum(committee);
        if self.threshold == 0 || committee.is_empty() || self.quorum_signatures.len() < required {
            return false;
        }
        let message = self.signing_message();
        let mut distinct = std::collections::HashSet::new();
        for (pk, sig) in &self.quorum_signatures {
            if !committee.contains(pk) {
                return false;
            }
            if !pk.verify(&message, sig) {
                return false;
            }
            distinct.insert(pk.0);
        }
        distinct.len() >= required
    }

    /// Does this root carry a (non-empty) finalization-vote quorum record?
    ///
    /// Distinguishes a genuinely-unsigned/trailing head (empty — the vote
    /// quorum has not assembled yet, which the restart anchor treats as
    /// "not yet anchored", NOT as forgery) from a root that CLAIMS a quorum
    /// (non-empty — which must then verify or the root is rejected as forged).
    pub fn has_finalization_quorum(&self) -> bool {
        !self.finalization_quorum.is_empty()
    }

    /// Verify the assembled committee **finalization-vote** quorum
    /// (`finalization_quorum`) — the N3 committee-restart anchor (Fix B).
    ///
    /// Returns `true` only when ALL of:
    ///   * this root is anchored to a blocklace block (`blocklace_block_id` is
    ///     `Some` — the vote preimage binds it);
    ///   * every signer is a committee member (at some index `i`) whose BOTH
    ///     signature halves — ed25519 AND ML-DSA-65 — verify over
    ///     [`dregg_types::finalization_vote_signing_message`] for THIS root's
    ///     `(blocklace_block_id, merkle_root)`, with the PQ half verified under
    ///     the ENROLLED key `ml_dsa_committee[i]` (the self-carried
    ///     `ml_dsa_pubkey` must EQUAL it). A signature over any other root or
    ///     block, a valid ed25519 half with a broken/missing PQ half, or a
    ///     self-carried PQ key that differs from the enrolled one, does not count
    ///     (fail-closed hybrid: `classical ∧ pq`, PQ key pinned to genesis);
    ///   * the number of **distinct** fully-valid committee signers is
    ///     `>=` [`Self::required_quorum`] — the committee's own supermajority,
    ///     which the stored (unsigned) `threshold` can raise but never lower
    ///     (an equivocating/duplicated voter counts at most once, so a single
    ///     member cannot inflate the quorum).
    ///   * the enrolled ML-DSA roster is pairwise **DISTINCT** — no two committee
    ///     slots share ONE enrolled PQ authority (see the roster paragraph below).
    ///
    /// `ml_dsa_committee` is the genesis-ENROLLED ML-DSA-65 roster, aligned
    /// index-for-index with `committee`. A misaligned/empty roster
    /// (`ml_dsa_committee.len() != committee.len()`) cannot pin any signer's PQ
    /// half, so the whole re-verify REFUSES — never a silent ed25519-only
    /// downgrade. The roster must ALSO be pairwise DISTINCT: a duplicate
    /// enrollment (the same ML-DSA key at two positions — the genesis/enrollment
    /// path checks only length alignment) would let ONE holder of that key fill
    /// two PQ slots, so a quantum adversary who breaks ed25519 alone could reuse
    /// the ONE enrolled key's PQ signature at both positions and collapse a
    /// 2-of-2 quantum bar to 1-of-1. This is what defeats a quantum adversary who
    /// breaks ed25519 alone: the PQ half must verify under the enrolled key it
    /// does not hold, mirroring the FROST positional pin.
    ///
    /// This never accepts a root without a genuine >=threshold committee quorum
    /// over the exact finalized state — it closes the liveness fail-close
    /// WITHOUT relaxing the soundness bar.
    pub fn verify_finalization_quorum(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
    ) -> bool {
        // One of this crate's entries into `dregg-pq` (the enrolled ML-DSA half is checked below).
        // See `FaithfulNoteRootEnvelopeV1::verify_hybrid` for why the install is here.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let Some(block_id) = self.blocklace_block_id else {
            return false;
        };
        // The bar is the committee's own supermajority (see `required_quorum`):
        // the stored `threshold` is unsigned and tamperable, so it can never
        // LOWER the number of distinct valid signers demanded here.
        let required = self.required_quorum(committee);
        if committee.is_empty() || self.finalization_quorum.len() < required {
            return false;
        }
        // The enrolled PQ roster MUST align index-for-index with the ed25519
        // committee, or there is no enrolled key to pin each signer against —
        // fail closed (an EMPTY roster is included here: no silent downgrade).
        if ml_dsa_committee.len() != committee.len() {
            return false;
        }
        // The enrolled ML-DSA roster must ALSO be pairwise DISTINCT: distinct
        // classical committee slots cannot share ONE enrolled PQ authority.
        // Without this, a roster that enrols the same ML-DSA key at two positions
        // lets ONE holder of that key fill two PQ slots — a quantum adversary who
        // breaks ed25519 forges both classical halves, reuses the ONE enrolled
        // key's PQ signature at both positions, and a 2-of-2 quantum bar collapses
        // to 1-of-1. The same distinct-roster contract as the sibling hybrid
        // carriers `federation::frost::verify_pq_quorum_half` (task/4847) and
        // `federation::receipt::verify_hybrid_quorum_sigs` (task/4721). Checked
        // over the WHOLE roster — including positions absent from this root's
        // quorum — so a quorum drawn only from distinct slots cannot launder a
        // duplicate enrollment elsewhere in the roster.
        if ml_dsa_committee
            .iter()
            .enumerate()
            .any(|(i, key)| ml_dsa_committee[..i].contains(key))
        {
            return false;
        }
        // v4: the vote preimage absorbs THIS root's `receipt_stream_root`, so a
        // quorum that re-anchors a restart is also a quorum over the receipts
        // the anchored block committed — the restart anchor and the per-turn
        // anchor are now the same signatures.
        let message = dregg_types::finalization_vote_signing_message(
            &block_id,
            &self.merkle_root,
            self.receipt_stream_root,
        );
        let mut distinct: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
        for qs in &self.finalization_quorum {
            // Membership — and the voter's ENROLLED index.
            let Some(idx) = committee.iter().position(|c| c == &qs.voter) else {
                return false;
            };
            // CLASSICAL half.
            if !qs.voter.verify(&message, &qs.signature) {
                return false;
            }
            // POST-QUANTUM half (ML-DSA-65) — PINNED to the enrolled roster. The
            // self-carried key must be a byte-identical copy of the enrolled key
            // (never trusted on its own), and the PQ signature is verified under
            // the ENROLLED key. A mismatch or a failing signature refuses the
            // whole quorum — never a silent ed25519-only downgrade.
            let enrolled = &ml_dsa_committee[idx];
            if qs.ml_dsa_pubkey.as_slice() != enrolled.0.as_slice() {
                return false;
            }
            if !enrolled.verify(&message, &qs.pq_signature) {
                return false;
            }
            distinct.insert(qs.voter.0);
        }
        distinct.len() >= required
    }

    /// Does at least one committee-member signature validly bind THIS root's
    /// `merkle_root` — from EITHER the light-client `quorum_signatures` (over
    /// `signing_message`) OR the `finalization_quorum` (over the
    /// finalization-vote message)?
    ///
    /// This is weaker than a quorum (a single valid signature suffices) and is
    /// used ONLY for the restart tamper-check: even when a full committee quorum
    /// has not yet assembled for a trailing head, a ledger recovered to a root
    /// that does NOT match any self/committee-signed root must still be refused.
    /// It preserves the merkle_root-binding integrity the lone local signature
    /// provides, without treating that lone signature as a quorum anchor.
    ///
    /// HYBRID BAR on the vote leg. A `finalization_quorum` entry counts here
    /// only when BOTH its halves — ed25519 AND ML-DSA-65 under the ENROLLED key
    /// `ml_dsa_committee[i]` — verify over the finalization-vote message
    /// (classical ∧ pq, PQ key pinned), the SAME bar
    /// [`verify_finalization_quorum`](Self::verify_finalization_quorum) sets
    /// per signer. Every genuinely emitted vote carries both halves
    /// (`FinalizationVote::sign` is hybrid), so requiring both loses nothing —
    /// while a valid ed25519 half riding with a forged/absent PQ half, or a
    /// self-carried PQ key that is not the enrolled one, is NOT a committee
    /// binding and must not be treated as one. When the enrolled roster is not
    /// aligned with `committee` (e.g. a purely on-chain amended committee with no
    /// recorded ML-DSA roster) the hybrid vote leg is skipped entirely — never a
    /// silent ed25519-only pass on that leg.
    ///
    /// The `quorum_signatures` leg (the node's OWN light-client signature over
    /// `signing_message()`) remains ed25519-only BY STRUCTURE: that field is
    /// `(PublicKey, Signature)` pairs with no PQ material on its wire. It is a
    /// lone local self-binding, never an anchor — anchoring always goes through
    /// the full hybrid `verify_finalization_quorum` — and a positive result
    /// from THIS check can only REFUSE a mismatched ledger, never accept one.
    pub fn has_any_valid_committee_signature(
        &self,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
    ) -> bool {
        // The other entry into `dregg-pq` on this type — see `verify_finalization_quorum`.
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let full_msg = self.signing_message();
        for (pk, sig) in &self.quorum_signatures {
            if committee.contains(pk) && pk.verify(&full_msg, sig) {
                return true;
            }
        }
        // The finalization-vote leg is HYBRID and PINNED — only consult it when
        // the enrolled roster aligns with the committee (otherwise there is no
        // enrolled key to pin each signer's PQ half against, and this leg must
        // NOT fall back to ed25519-only).
        if ml_dsa_committee.len() == committee.len()
            && let Some(block_id) = self.blocklace_block_id
        {
            let vote_msg = dregg_types::finalization_vote_signing_message(
                &block_id,
                &self.merkle_root,
                self.receipt_stream_root,
            );
            for qs in &self.finalization_quorum {
                // Membership — and the voter's enrolled index.
                let Some(idx) = committee.iter().position(|c| c == &qs.voter) else {
                    continue;
                };
                // CLASSICAL half.
                if !qs.voter.verify(&vote_msg, &qs.signature) {
                    continue;
                }
                // POST-QUANTUM half — PINNED to the enrolled roster. A
                // self-carried key differing from the enrolled one, or a failing
                // signature, means this entry is NOT a valid committee binding.
                let enrolled = &ml_dsa_committee[idx];
                if qs.ml_dsa_pubkey.as_slice() != enrolled.0.as_slice() {
                    continue;
                }
                if enrolled.verify(&vote_msg, &qs.pq_signature) {
                    return true;
                }
            }
        }
        false
    }

    /// Compute the canonical message that was signed for this attested root.
    ///
    /// Mirrors [`dregg_types::AttestedRoot::signing_message`] (v3): includes
    /// `federation_id`, `note_tree_root`, `nullifier_set_root`,
    /// `blocklace_block_id`, and `finality_round` with `0x00 | 0x01 || value`
    /// framing for unambiguous `Option` encoding.
    ///
    /// `pub(crate)` so the recovery-anchor diagnosis test can reconstruct the
    /// exact bytes a genuine committee quorum must sign (see
    /// `tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`).
    pub(crate) fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        // v5 (N3 committee-restart fix): the wall-clock `timestamp` is DROPPED
        // from the signed preimage so the root's preimage is deterministic
        // across the committee. v6 (state anchor): `merkle_root` STAYS the BLAKE3
        // whole-image `canonical_ledger_root` — it is the restart anchor this very
        // function re-verifies — while the receipts under `receipt_stream_root` moved
        // to the AIR-bound chip 8-felt commitment (`dregg_turn::state_commit`).
        // Mirrors `dregg_types::AttestedRoot::signing_message` and MUST stay
        // byte-identical to it.
        msg.extend_from_slice(b"dregg-attested-root-v6");
        msg.extend_from_slice(&self.federation_id.0);
        msg.extend_from_slice(&self.merkle_root);
        match self.note_tree_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        match self.nullifier_set_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        msg.extend_from_slice(&self.height.to_le_bytes());
        // NOTE (v5): `timestamp` is intentionally NOT mixed in (determinism).
        match self.blocklace_block_id {
            Some(ref id) => {
                msg.push(0x01);
                msg.extend_from_slice(id);
            }
            None => msg.push(0x00),
        }
        match self.finality_round {
            Some(round) => {
                msg.push(0x01);
                msg.extend_from_slice(&round.to_le_bytes());
            }
            None => msg.push(0x00),
        }
        // v4 (#80): receipt_stream_root with 0x00 / 0x01||32-byte framing.
        match self.receipt_stream_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => msg.push(0x00),
        }
        msg
    }

    /// Short hex of the Merkle root for display.
    pub fn root_hex(&self) -> String {
        self.merkle_root
            .iter()
            .take(4)
            .map(|b| format!("{b:02x}"))
            .collect()
    }
}

impl PersistentStore {
    // =========================================================================
    // Revocation Storage
    // =========================================================================

    /// Store a revocation for a token ID.
    ///
    /// Records the current time as the revocation timestamp.
    /// Idempotent: re-revoking an already-revoked token is a no-op.
    pub fn store_revocation(&self, token_id: &str) -> Result<()> {
        let timestamp = current_timestamp();
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            // Only insert if not already present (idempotent).
            if table.get(token_id)?.is_none() {
                table.insert(token_id, timestamp)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Store a revocation with an explicit timestamp.
    pub fn store_revocation_at(&self, token_id: &str, timestamp: i64) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            if table.get(token_id)?.is_none() {
                table.insert(token_id, timestamp)?;
            }
        }
        write_txn.commit()?;
        Ok(())
    }

    /// Check whether a token ID has been revoked.
    pub fn is_revoked(&self, token_id: &str) -> Result<bool> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        Ok(table.get(token_id)?.is_some())
    }

    /// Get the timestamp when a token was revoked, if it was.
    pub fn revocation_time(&self, token_id: &str) -> Result<Option<i64>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        match table.get(token_id)? {
            Some(guard) => Ok(Some(guard.value())),
            None => Ok(None),
        }
    }

    /// Count the total number of revoked tokens.
    pub fn revocation_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;
        Ok(table.len()?)
    }

    /// List all revoked token IDs.
    pub fn list_revocations(&self) -> Result<Vec<String>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::REVOCATIONS)?;

        let mut ids = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            ids.push(entry.0.value().to_string());
        }
        Ok(ids)
    }

    /// Batch-revoke multiple tokens in a single transaction.
    pub fn store_revocations_batch(&self, token_ids: &[&str]) -> Result<u64> {
        let timestamp = current_timestamp();
        let write_txn = self.db.begin_write()?;
        let mut count = 0u64;
        {
            let mut table = write_txn.open_table(tables::REVOCATIONS)?;
            for token_id in token_ids {
                if table.get(*token_id)?.is_none() {
                    table.insert(*token_id, timestamp)?;
                    count += 1;
                }
            }
        }
        write_txn.commit()?;
        Ok(count)
    }

    // =========================================================================
    // Attested Root Storage
    // =========================================================================

    /// Store an attested root at a given height.
    ///
    /// Also updates the metadata to track the latest height.
    pub fn store_attested_root(&self, root: &StoredAttestedRoot) -> Result<()> {
        let write_txn = self.db.begin_write()?;
        store_attested_root_in(&write_txn, root, AttestedRootWrite::Replace)?;
        write_txn.commit()?;
        Ok(())
    }

    /// Load the latest (highest-height) attested root.
    pub fn latest_attested_root(&self) -> Result<Option<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;

        let height = match meta.get(tables::META_LATEST_ROOT_HEIGHT)? {
            Some(guard) => guard.value(),
            None => return Ok(None),
        };

        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;
        match table.get(height)? {
            Some(value) => {
                let root: StoredAttestedRoot = postcard::from_bytes(value.value())?;
                Ok(Some(root))
            }
            None => Ok(None),
        }
    }

    /// Load an attested root at a specific height.
    pub fn attested_root_at_height(&self, height: u64) -> Result<Option<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;

        match table.get(height)? {
            Some(value) => {
                let root: StoredAttestedRoot = postcard::from_bytes(value.value())?;
                Ok(Some(root))
            }
            None => Ok(None),
        }
    }

    /// Count the total number of stored attested roots.
    pub fn attested_root_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;
        Ok(table.len()?)
    }

    /// The highest-height attested root and the number of stored roots, read
    /// in ONE transaction without decoding any other row.
    ///
    /// Equal to `(all_attested_roots().max_by_key(height), all_attested_roots().len())`
    /// but O(log n): redb orders the `u64` keys, so the last entry is the
    /// highest height. Reads the table itself rather than
    /// `META_LATEST_ROOT_HEIGHT`, so a pruned or legacy store cannot make the
    /// two disagree.
    pub fn attested_root_summary(&self) -> Result<(Option<StoredAttestedRoot>, u64)> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;
        let latest = match table.last()? {
            Some((_, value)) => Some(postcard::from_bytes(value.value())?),
            None => None,
        };
        Ok((latest, table.len()?))
    }

    /// Load all attested roots in height order.
    pub fn all_attested_roots(&self) -> Result<Vec<StoredAttestedRoot>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::ATTESTED_ROOTS)?;

        let mut roots = Vec::new();
        let iter = table.iter()?;
        for entry in iter {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let root: StoredAttestedRoot = postcard::from_bytes(entry.1.value())?;
            roots.push(root);
        }
        Ok(roots)
    }
}

/// Mutation policy for an attested-root write inside a larger transaction.
pub(crate) enum AttestedRootWrite {
    /// The ordinary backfill path may replace a root at the same height with
    /// the same state plus its newly assembled finalization quorum.
    Replace,
    /// A fresh finalized commit must not overwrite a competing attestation.
    Fresh,
    /// Crash replay requires the exact bytes already written by the original
    /// atomic commit and never repairs a missing row.
    ExactReplay,
}

/// Store one attested root inside a caller-owned redb transaction.
pub(crate) fn store_attested_root_in(
    write: &redb::WriteTransaction,
    root: &StoredAttestedRoot,
    policy: AttestedRootWrite,
) -> Result<()> {
    let serialized = postcard::to_stdvec(root)?;
    let mut table = write.open_table(tables::ATTESTED_ROOTS)?;
    if let Some(existing) = table.get(root.height)? {
        let existing_bytes = existing.value();
        match policy {
            AttestedRootWrite::Replace => {}
            AttestedRootWrite::Fresh => {
                return Err(StoreError::Integrity(format!(
                    "attested root height {} already exists; refusing finalized-root overwrite",
                    root.height
                )));
            }
            AttestedRootWrite::ExactReplay if existing_bytes == serialized.as_slice() => {
                return Ok(());
            }
            AttestedRootWrite::ExactReplay => {
                return Err(StoreError::Integrity(format!(
                    "attested root replay at height {} differs from durable root",
                    root.height
                )));
            }
        }
    } else if matches!(policy, AttestedRootWrite::ExactReplay) {
        return Err(StoreError::Integrity(format!(
            "attested root replay at height {} is missing from durable store",
            root.height
        )));
    }
    table.insert(root.height, serialized.as_slice())?;

    let mut meta = write.open_table(tables::METADATA)?;
    let current_latest = meta
        .get(tables::META_LATEST_ROOT_HEIGHT)?
        .map(|g| g.value())
        .unwrap_or(0);
    if root.height >= current_latest {
        meta.insert(tables::META_LATEST_ROOT_HEIGHT, root.height)?;
    }
    Ok(())
}

/// Get the current unix timestamp in seconds.
fn current_timestamp() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod quorum_floor_tests {
    use super::*;

    fn key(seed: u8) -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[seed; 32])
    }
    fn pubkey(sk: &ed25519_dalek::SigningKey) -> PublicKey {
        PublicKey(sk.verifying_key().to_bytes())
    }

    /// A root with NO signatures yet — the preimage every pole below signs.
    fn bare_root() -> StoredAttestedRoot {
        StoredAttestedRoot {
            merkle_root: [0x11; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 7,
            timestamp: 1_700_000_000,
            blocklace_block_id: Some([0x22; 32]),
            finality_round: Some(3),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: 0,
            federation_id: FederationId::default(),
            receipt_stream_root: None,
            finalization_quorum: Vec::new(),
        }
    }

    fn sign_with(
        root: &StoredAttestedRoot,
        sk: &ed25519_dalek::SigningKey,
    ) -> (PublicKey, Signature) {
        use ed25519_dalek::Signer;
        let msg = root.signing_message();
        (pubkey(sk), Signature(sk.sign(&msg).to_bytes()))
    }

    /// ⚑ THE PREMISE THIS WHOLE FIX RESTS ON, ASSERTED RATHER THAN READ ONCE:
    /// `threshold` is not covered by the signed preimage. Move the field, and
    /// the bytes every committee member signed do not move — so a store tamper
    /// that rewrites it invalidates nothing.
    #[test]
    fn the_threshold_field_is_not_in_the_signed_preimage() {
        let mut a = bare_root();
        a.threshold = 1;
        let mut b = bare_root();
        b.threshold = 999;
        assert_eq!(
            a.signing_message(),
            b.signing_message(),
            "if this ever fails the field became authenticated and `required_quorum`'s floor \
             is no longer load-bearing — re-derive it rather than deleting this test"
        );
    }

    /// HONEST POLE: a real supermajority of a 4-member committee verifies.
    /// Without this, every refusal below is satisfied just as well by a
    /// predicate that refuses everything.
    #[test]
    fn an_honest_supermajority_verifies() {
        let sks: Vec<_> = (1u8..=4).map(key).collect();
        let committee: Vec<PublicKey> = sks.iter().map(pubkey).collect();
        assert_eq!(
            dregg_blocklace::supermajority_threshold(committee.len()),
            3,
            "n=4 floors at 3; if this moves the poles below are measuring another bar"
        );

        let mut root = bare_root();
        root.threshold = 3;
        let sigs: Vec<_> = sks[..3].iter().map(|sk| sign_with(&root, sk)).collect();
        root.quorum_signatures = sigs;
        assert!(
            root.verify_signatures(&committee),
            "three distinct valid committee signatures ARE the supermajority of four"
        );
    }

    /// ⚑ THE TAMPER POLE: `threshold` rewritten to 1 with a single genuine
    /// signature. Before this fix that read back as a verified quorum, because
    /// the bar was the tampered field itself.
    #[test]
    fn a_rewritten_threshold_of_one_cannot_promote_a_lone_signature() {
        let sks: Vec<_> = (1u8..=4).map(key).collect();
        let committee: Vec<PublicKey> = sks.iter().map(pubkey).collect();

        let mut root = bare_root();
        root.threshold = 1; // the tamper
        let lone = sign_with(&root, &sks[0]);

        // ASSERT THE FALSIFIER IS LIVE before reading the verdict: the tamper is
        // present, and the lone signature is a GENUINE committee signature that
        // verifies on its own — so a refusal below is about the QUORUM BAR and
        // not about a broken signature.
        assert_eq!(root.threshold, 1, "the tamper must be present");
        assert!(
            committee.contains(&lone.0),
            "the signer is a committee member"
        );
        assert!(
            lone.0.verify(&root.signing_message(), &lone.1),
            "the lone signature must actually verify, or this test refuses for the wrong reason"
        );

        root.quorum_signatures = vec![lone];
        assert!(
            !root.verify_signatures(&committee),
            "SOUNDNESS: a store tamper set threshold=1 and one valid signature read back as a \
             verified quorum — the committee's own supermajority is the floor"
        );
    }

    /// The field can still RAISE the bar — it is a floor, not a replacement.
    #[test]
    fn a_higher_declared_threshold_still_binds() {
        let sks: Vec<_> = (1u8..=4).map(key).collect();
        let committee: Vec<PublicKey> = sks.iter().map(pubkey).collect();
        let mut root = bare_root();
        root.threshold = 4;
        root.quorum_signatures = sks[..3].iter().map(|sk| sign_with(&root, sk)).collect();
        assert!(
            !root.verify_signatures(&committee),
            "three signatures do not clear a self-declared bar of four"
        );
    }

    /// An empty committee is not an authority — its floor is 1 and it can
    /// contain no valid signer, so the refusal is stated explicitly rather than
    /// left to `contains` on an empty slice.
    #[test]
    fn an_empty_committee_verifies_nothing() {
        let sk = key(1);
        let mut root = bare_root();
        root.threshold = 1;
        root.quorum_signatures = vec![sign_with(&root, &sk)];
        assert!(
            !root.verify_signatures(&[]),
            "an empty committee is not a quorum"
        );
    }

    /// Solo (n=1) is unchanged: the floor is 1, so a single-member federation
    /// still anchors on its own signature.
    #[test]
    fn solo_semantics_are_unchanged() {
        let sk = key(9);
        let committee = vec![pubkey(&sk)];
        assert_eq!(dregg_blocklace::supermajority_threshold(1), 1);
        let mut root = bare_root();
        root.threshold = 1;
        root.quorum_signatures = vec![sign_with(&root, &sk)];
        assert!(
            root.verify_signatures(&committee),
            "n=1 floors at 1 — the fix must not break solo"
        );
    }
}
