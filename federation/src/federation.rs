//! Unified `Federation` type — the canonical owner of
//! (federation_id, committee, epoch, threshold, local seat).
//!
//! See `FEDERATION-UNIFICATION-DESIGN.md` §2. This collapses the four disjoint
//! "federation" concepts (Morpheus simulator, `FederationCommittee`,
//! `FederationMode`, raw `federation_id` bytes) into a single type.
//!
//! Everywhere code currently passes around
//! `(federation_id, FederationCommittee, FederationMode, threshold)` as four
//! parameters, it should accept `&Federation` instead.
//!
//! # What this type owns vs references
//!
//! - **Owns:** Ed25519 member pubkeys, epoch, threshold, derived id, and
//!   (optionally) the BLS committee context.
//! - **References:** The blocklace this federation produces. Per design §7.Q1
//!   the embedded `Arc<Blocklace>` was deferred — `Federation` is a pure
//!   attestation context, and the blocklace lives separately (typically held
//!   alongside `Federation` in `node::state::State`). This keeps `Federation`
//!   light enough to clone freely and avoids a `pyana-blocklace` dep on the
//!   federation crate that wasn't there before.
//!
//! The 1-to-1 binding is preserved by convention: `node::state::State`
//! contains both `Federation` and `Blocklace`, and `KnownFederations` entries
//! that we are not a member of carry only the attestation context.

use std::sync::Arc;

use crate::identity::derive_federation_id_with_epoch;
use crate::threshold::FederationCommittee;
use crate::types::PublicKey;
use pyana_types::FederationId;

use crate::threshold::MemberSecret;

// =============================================================================
// LocalSeat
// =============================================================================

/// The local node's seat in a federation: the secret material needed to sign
/// as a member.
///
/// `None` on the `Federation` value means "we are a verifier-only registrant"
/// (i.e. an entry in `KnownFederations` we want to verify receipts from but
/// are not a member of).
#[derive(Clone)]
pub struct LocalSeat {
    /// Index in `Federation::members` (after sorting).
    pub index: usize,
    /// Local Ed25519 signing key.
    pub signing_key: pyana_types::SigningKey,
    /// Local BLS member secret, present when `bls_committee.is_some()`.
    pub bls_secret: Option<MemberSecret>,
}

impl std::fmt::Debug for LocalSeat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LocalSeat")
            .field("index", &self.index)
            .field("signing_key", &"<redacted>")
            .finish()
    }
}

// =============================================================================
// Federation
// =============================================================================

/// A federation: a committee of nodes attesting a shared ledger.
///
/// The canonical owner of (federation_id, committee, epoch, threshold).
///
/// # Identity
///
/// `Federation::id()` is derived as `H(sorted(members) || epoch)`. Two
/// federations with the same committee at the same epoch *are the same
/// federation*. Rotating the committee or bumping the epoch mints a fresh id.
///
/// # Mode
///
/// There is no `FederationMode` field. A "solo" federation is just a committee
/// of one (`members.len() == 1`); call `is_solo()` to test for that case.
///
/// # Cloning
///
/// `Federation` is cheap to clone — the `FederationCommittee` is wrapped in
/// `Arc` so the heavy KZG state is shared. `LocalSeat` is small and cloneable.
#[derive(Clone)]
pub struct Federation {
    /// Sorted Ed25519 public keys of committee members. Sorted lexicographically
    /// by the constructor; read-only after construction.
    members: Vec<PublicKey>,

    /// BLS threshold context for constant-size aggregate signatures. `None`
    /// for solo / pre-bootstrap federations that haven't run BLS setup yet;
    /// in that case the only available `ReceiptQc` flavor is `Votes` (Ed25519
    /// fallback).
    bls_committee: Option<Arc<FederationCommittee>>,

    /// Current committee epoch. Bumped by `apply_epoch_transition`. Part of
    /// the `federation_id` preimage; rotating it mints a fresh id.
    epoch: u64,

    /// Minimum unique signers (or BLS aggregate weight) required for a valid
    /// quorum certificate.
    threshold: u32,

    /// Cached id = H(sorted(members) || epoch). Recomputed by the constructor
    /// and any epoch-transition mutator; never set by callers directly.
    id: FederationId,

    /// Local node's seat in this federation, if any. `None` for verifier-only
    /// registrants (cross-federation peers we know about but aren't a member
    /// of). `Some(_)` carries the local Ed25519 signing key and optionally
    /// the BLS member secret.
    local_seat: Option<LocalSeat>,
}

impl Federation {
    /// Construct a federation from its committee pubkeys.
    ///
    /// The `members` slice is sorted lexicographically internally; `id` is
    /// recomputed from the sorted result so callers don't need to canonicalize
    /// first.
    pub fn from_committee(
        members: Vec<PublicKey>,
        epoch: u64,
        threshold: u32,
        bls_committee: Option<Arc<FederationCommittee>>,
        local_seat: Option<LocalSeat>,
    ) -> Self {
        let mut sorted = members;
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        let id_bytes = derive_federation_id_with_epoch(&sorted, epoch);
        let id = FederationId(id_bytes);
        // Reindex local_seat against the sorted members if present so the
        // caller doesn't have to know the canonical order.
        let local_seat = local_seat.map(|mut seat| {
            if let Some(idx) = sorted
                .iter()
                .position(|pk| pk.0 == seat.signing_key.public_key().0)
            {
                seat.index = idx;
            }
            seat
        });
        Self {
            members: sorted,
            bls_committee,
            epoch,
            threshold,
            id,
            local_seat,
        }
    }

    /// Convenience constructor for a committee of one (Solo).
    pub fn solo(local_seat: LocalSeat) -> Self {
        let pk = local_seat.signing_key.public_key();
        Self::from_committee(vec![pk], 0, 1, None, Some(local_seat))
    }

    /// Construct a verifier-only federation (no local seat).
    ///
    /// Used when registering a peer federation in `KnownFederations` to
    /// verify cross-federation receipts.
    pub fn verifier_only(members: Vec<PublicKey>, epoch: u64, threshold: u32) -> Self {
        Self::from_committee(members, epoch, threshold, None, None)
    }

    /// The federation's identity (derived from committee + epoch).
    pub fn id(&self) -> FederationId {
        self.id
    }

    /// The federation's identity as raw bytes (`[u8; 32]`).
    pub fn id_bytes(&self) -> [u8; 32] {
        self.id.0
    }

    /// The sorted Ed25519 committee pubkeys.
    pub fn members(&self) -> &[PublicKey] {
        &self.members
    }

    /// The current committee epoch.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Minimum unique signers required for a quorum certificate.
    pub fn threshold(&self) -> u32 {
        self.threshold
    }

    /// Threshold as `usize` (the form most call sites need).
    pub fn threshold_usize(&self) -> usize {
        self.threshold as usize
    }

    /// The BLS committee context, if BLS setup has been run.
    pub fn bls_committee(&self) -> Option<&FederationCommittee> {
        self.bls_committee.as_deref()
    }

    /// The local node's seat, if we are a member.
    pub fn local_seat(&self) -> Option<&LocalSeat> {
        self.local_seat.as_ref()
    }

    /// Are we operating in degenerate-committee mode (`members.len() == 1`)?
    ///
    /// This replaces the deleted `FederationMode::Solo` flag — solo is no
    /// longer a runtime mode but a property of the committee size.
    pub fn is_solo(&self) -> bool {
        self.members.len() == 1
    }

    /// Number of committee members.
    pub fn num_members(&self) -> usize {
        self.members.len()
    }

    /// Replace the BLS committee context. Used when BLS setup completes after
    /// the federation has been constructed (e.g. lazy setup at first use).
    pub fn set_bls_committee(&mut self, committee: Arc<FederationCommittee>) {
        self.bls_committee = Some(committee);
    }

    /// Replace the local seat (e.g. after key rotation).
    pub fn set_local_seat(&mut self, seat: Option<LocalSeat>) {
        self.local_seat = seat.map(|mut s| {
            if let Some(idx) = self
                .members
                .iter()
                .position(|pk| pk.0 == s.signing_key.public_key().0)
            {
                s.index = idx;
            }
            s
        });
    }

    /// Apply an epoch transition: replace the committee and bump the epoch.
    /// Recomputes the cached id.
    pub fn apply_epoch_transition(
        &mut self,
        new_members: Vec<PublicKey>,
        new_epoch: u64,
        new_threshold: u32,
    ) {
        let mut sorted = new_members;
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        self.members = sorted;
        self.epoch = new_epoch;
        self.threshold = new_threshold;
        self.id = FederationId(derive_federation_id_with_epoch(&self.members, self.epoch));
        // Reindex local_seat against the new committee.
        if let Some(ref mut seat) = self.local_seat {
            if let Some(idx) = self
                .members
                .iter()
                .position(|pk| pk.0 == seat.signing_key.public_key().0)
            {
                seat.index = idx;
            }
            // If the local member is no longer in the committee, we leave
            // local_seat in place; callers may want to demote to verifier-only
            // explicitly via `set_local_seat(None)`.
        }
    }

    /// Verify a `FederationReceipt` against this federation's committee + epoch.
    ///
    /// Replaces the four-parameter
    /// `FederationReceipt::verify(committee, known_keys, threshold, expected_epoch)`
    /// API at the caller-facing layer. The raw form remains on
    /// `FederationReceipt` for wire/serde callers.
    pub fn verify_receipt(&self, receipt: &crate::receipt::FederationReceipt) -> bool {
        receipt.verify(
            self.bls_committee(),
            &self.members,
            self.threshold_usize(),
            self.epoch,
        )
    }

    /// Verify an `AttestedRoot` against this federation's Ed25519 committee.
    ///
    /// Note: full BLS verification of an `AttestedRoot`'s `threshold_qc`
    /// requires the BLS committee and lives in
    /// `pyana_types::verify_attested_root_with_committee`; this method covers
    /// the Ed25519 path (the common case for the live blocklace_sync
    /// verifier).
    pub fn verify_attested_root(&self, root: &pyana_types::AttestedRoot) -> bool {
        root.is_valid(&self.members)
    }

    /// Verify that a federation_id (likely from a `FederationReceipt` field
    /// or a CapTP routing message) matches this federation. Constant-time
    /// equality on a 32-byte hash.
    pub fn id_matches(&self, fed_id: &FederationId) -> bool {
        self.id == *fed_id
    }

    /// Build an `AttestedRoot` bound to this federation.
    ///
    /// This is the *only* canonical constructor for an `AttestedRoot` —
    /// it enforces `blocklace_block_id` and `finality_round` presence and
    /// pre-populates the threshold from the federation's committee.
    ///
    /// The returned root has empty `quorum_signatures` and no `threshold_qc`;
    /// the caller collects member signatures over
    /// `root.signing_message_with_federation(&federation.id())` and appends them
    /// before publishing.
    ///
    /// Per design §4: every `AttestedRoot` produced via this federation MUST
    /// bind to a specific blocklace block — this enforces the binding.
    pub fn build_attested_root(
        &self,
        merkle_root: [u8; 32],
        note_tree_root: Option<[u8; 32]>,
        nullifier_set_root: Option<[u8; 32]>,
        height: u64,
        timestamp: i64,
        blocklace_block_id: [u8; 32],
        finality_round: u64,
    ) -> pyana_types::AttestedRoot {
        pyana_types::AttestedRoot {
            merkle_root,
            note_tree_root,
            nullifier_set_root,
            height,
            timestamp,
            blocklace_block_id: Some(blocklace_block_id),
            finality_round: Some(finality_round),
            quorum_signatures: Vec::new(),
            threshold_qc: None,
            threshold: self.threshold_usize(),
            federation_id: self.id,
            // v4 (#80): receipt stream binding — federations that have
            // not yet attested a receipt-stream root advertise `None`,
            // which the verifier treats as v3-legacy.
            receipt_stream_root: None,
        }
    }
}

impl std::fmt::Debug for Federation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Federation")
            .field("id", &self.id)
            .field("members", &self.members.len())
            .field("epoch", &self.epoch)
            .field("threshold", &self.threshold)
            .field("bls_committee", &self.bls_committee.is_some())
            .field("local_seat", &self.local_seat.is_some())
            .field("solo", &self.is_solo())
            .finish()
    }
}

// =============================================================================
// KnownFederations
// =============================================================================

/// A registry of federations the local node knows about.
///
/// Replaces the disjoint pair of `node::state::known_federation_keys:
/// Vec<PublicKey>` (own-federation keys) and `wire::CapTpState::
/// known_federations: Vec<FederationId>` (routing list with no committee
/// material).
///
/// Per design §5/§8: persisted at `$DATA_DIR/known_federations/` in
/// production; in-memory in tests. Threaded into both `node::state::State`
/// and `wire::server::CapTpState` so cross-federation receipt verification
/// is a single lookup.
#[derive(Clone, Default)]
pub struct KnownFederations {
    entries: std::collections::HashMap<FederationId, Arc<Federation>>,
}

impl KnownFederations {
    /// Empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a federation. Replaces any existing entry with the same id
    /// (epoch rotation of the same federation chain).
    pub fn register(&mut self, fed: Arc<Federation>) {
        self.entries.insert(fed.id(), fed);
    }

    /// Look up a federation by id.
    pub fn get(&self, id: &FederationId) -> Option<&Arc<Federation>> {
        self.entries.get(id)
    }

    /// Number of registered federations.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// True if no federations are registered.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate over all registered federations.
    pub fn iter(&self) -> impl Iterator<Item = (&FederationId, &Arc<Federation>)> {
        self.entries.iter()
    }

    /// All registered federation ids (e.g. for CapTP routing).
    pub fn ids(&self) -> Vec<FederationId> {
        self.entries.keys().copied().collect()
    }

    /// Drop a federation from the registry. Returns true if the id was present.
    pub fn remove(&mut self, id: &FederationId) -> bool {
        self.entries.remove(id).is_some()
    }

    /// Verify a federation receipt by looking up its `federation_id` and
    /// delegating to that federation's committee context.
    ///
    /// Returns `false` if the federation is unknown.
    pub fn verify_receipt(&self, receipt: &crate::receipt::FederationReceipt) -> bool {
        let id = FederationId(receipt.federation_id);
        match self.entries.get(&id) {
            Some(fed) => fed.verify_receipt(receipt),
            None => false,
        }
    }

    /// Locate the local-seat federation, if exactly one is registered as
    /// `local_seat.is_some()`. Returns `None` if zero or more than one
    /// federation has a local seat (the latter is a configuration error per
    /// §8 invariants but we don't panic in release builds).
    pub fn local(&self) -> Option<&Arc<Federation>> {
        let mut local: Option<&Arc<Federation>> = None;
        for fed in self.entries.values() {
            if fed.local_seat().is_some() {
                if local.is_some() {
                    return None; // ambiguous
                }
                local = Some(fed);
            }
        }
        local
    }
}

impl std::fmt::Debug for KnownFederations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KnownFederations")
            .field("count", &self.entries.len())
            .field(
                "ids",
                &self
                    .entries
                    .keys()
                    .map(|id| id.short_hex())
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::derive_federation_id_with_epoch;
    use pyana_types::generate_keypair;

    #[test]
    fn id_is_derived_from_members_and_epoch() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let fed = Federation::verifier_only(vec![a.clone(), b.clone()], 0, 2);
        let expected = derive_federation_id_with_epoch(&fed.members, 0);
        assert_eq!(fed.id().0, expected);
    }

    #[test]
    fn id_is_order_independent() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let f1 = Federation::verifier_only(vec![a.clone(), b.clone()], 0, 2);
        let f2 = Federation::verifier_only(vec![b, a], 0, 2);
        assert_eq!(f1.id(), f2.id());
    }

    #[test]
    fn is_solo_detects_single_member() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let solo = Federation::verifier_only(vec![a.clone()], 0, 1);
        let pair = Federation::verifier_only(vec![a, b], 0, 2);
        assert!(solo.is_solo());
        assert!(!pair.is_solo());
    }

    #[test]
    fn epoch_transition_recomputes_id() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let (_, c) = generate_keypair();
        let mut fed = Federation::verifier_only(vec![a.clone(), b.clone()], 0, 2);
        let id0 = fed.id();
        fed.apply_epoch_transition(vec![a, b, c], 1, 2);
        assert_ne!(id0, fed.id());
        assert_eq!(fed.epoch(), 1);
        assert_eq!(fed.num_members(), 3);
    }

    #[test]
    fn known_federations_lookup() {
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let fed = Arc::new(Federation::verifier_only(vec![a, b], 0, 2));
        let mut reg = KnownFederations::new();
        let id = fed.id();
        reg.register(fed);
        assert!(reg.get(&id).is_some());
        assert_eq!(reg.len(), 1);
        assert!(reg.get(&FederationId([9u8; 32])).is_none());
    }

    #[test]
    fn known_federations_local_seat_lookup() {
        let (sk_a, pk_a) = generate_keypair();
        let (_, pk_b) = generate_keypair();
        let seat = LocalSeat {
            index: 0,
            signing_key: sk_a,
            bls_secret: None,
        };
        let local_fed = Arc::new(Federation::from_committee(
            vec![pk_a, pk_b.clone()],
            0,
            2,
            None,
            Some(seat),
        ));
        let peer_fed = Arc::new(Federation::verifier_only(vec![pk_b], 0, 1));
        let mut reg = KnownFederations::new();
        reg.register(local_fed.clone());
        reg.register(peer_fed);
        assert_eq!(reg.local().unwrap().id(), local_fed.id());
    }
}
