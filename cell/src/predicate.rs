//! Witness-attached predicate unification (PREDICATE-INVENTORY §3, §7).
//!
//! `WitnessedPredicate` is the *shared shape* for predicate kinds that
//! ride along with a 32-byte commitment, a witness/input pointer, and a
//! verifier-callable proof bytes blob. It collapses the 15-or-so
//! witness-bearing predicate kinds scattered across the tree (DFA-match,
//! temporal-predicate, blinded-set non-revocation, bridge predicate
//! proofs, Pedersen conservation, custom AIRs, …) under one algebraic
//! object, so any *surface* that wants to declare such a predicate
//! (slot caveats, per-action preconditions, capability caveats) can do
//! so by holding a `WitnessedPredicate` and delegating verification to
//! the registry.
//!
//! The non-witnessed predicate kinds — static cleartext slot caveats,
//! the lattice-shaped capability authority predicates, aggregate-sig
//! threshold predicates, structural matchers, bearer-possession — do
//! **not** collapse here; PREDICATE-INVENTORY §3.6 enumerates them.
//!
//! ## Registry shape
//!
//! Built-in `WitnessedPredicateKind` variants are platform-reserved and
//! resolve to closed-form verifiers (currently stub implementations that
//! defer to other crates' real verifiers via the executor wiring; see
//! the verifier trait below). `Custom { vk_hash }` is the open variant
//! for app-registered kinds — `vk_hash` keys an externally-registered
//! verifier, mirroring `Effect::Custom`'s 32-byte verifier-key hash
//! shape (cf. `DESIGN-max-custom-effects.md`) and the macaroon
//! `CaveatType` ID-range registry (`macaroon/src/caveat.rs:27-45`).
//!
//! ## Boundary contracts
//!
//! Per-kind boundary contracts live on each variant's rustdoc per
//! `BOUNDARIES.md §5.2`'s convention. Editorial discipline — apps that
//! register a `Custom` kind are responsible for documenting their own.
//!
//! ## v1 scope (deliberate)
//!
//! v1 ships `WitnessedPredicate` as the shape + a stubbed registry.
//! Existing witness-bearing variants (`StateConstraint::TemporalPredicate`,
//! `cell::peer_exchange::PeerStateTransition::transition_proof`, etc.)
//! keep their typed shapes. Phase 2+ rewires them to delegate. See
//! PREDICATE-INVENTORY §7.

use serde::{Deserialize, Serialize};

/// Compute the canonical VK hash for an app-defined custom predicate.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.2: the `vk_hash` inside
/// [`WitnessedPredicateKind::Custom`] (and the matching
/// `Authorization::Custom` / `Effect::Custom` carriers) commits to a
/// canonical encoding of the predicate's executable bytes — DSL AST
/// postcard, WASM bytecode, AIR descriptor, or whatever authoring
/// representation the app chose. The encoder treats the bytes as
/// opaque and produces a domain-keyed BLAKE3 hash:
///
/// ```text
/// vk_hash = BLAKE3_keyed("dregg-witnessed-predicate-vk-v1",
///                        len(bytes) || bytes)
/// ```
///
/// The length prefix makes the encoding unambiguous against
/// concatenation: two predicates whose bytes happen to share a prefix
/// produce different vk_hashes.
///
/// # Why opaque bytes?
///
/// Custom predicates may be authored in many representations: dregg-DSL
/// IR, WASM, raw AIR descriptors, Pickles circuit serializations, etc.
/// The platform does not pick the language; it picks the *commitment
/// shape*. Apps using the same language interoperate transparently;
/// apps using different languages get distinct vk_hashes by virtue of
/// distinct byte representations.
///
/// # Re-execution contract
///
/// Any validator with the canonical bytes (pulled from a program
/// registry or carried inline on a receipt) can:
/// 1. Verify `canonical_predicate_vk(bytes) == vk_hash`.
/// 2. Decode the bytes into the predicate's authoring representation.
/// 3. Re-execute against witness data + the resolved input.
/// 4. Compare its acceptance bit to the executor's claimed bit.
///
/// # Boundary contract
///
/// Same as `canonical_program_vk`:
/// - Cleartext-inside:  predicate author + validators.
/// - Commitment-inside: receipt observers.
/// - Acceptance-inside: post-recursion validators.
/// - Out-of-band:       everyone else.
/// Enforced by: BLAKE3 keyed-hash binding canonical bytes to vk_hash.
/// Failure mode if violated: validator's re-execution disagrees with
/// the executor's acceptance bit; soundness failure.
pub fn canonical_predicate_vk(predicate_bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-witnessed-predicate-vk-v1");
    hasher.update(&(predicate_bytes.len() as u64).to_le_bytes());
    hasher.update(predicate_bytes);
    *hasher.finalize().as_bytes()
}

/// Compute the canonical **layered** (v2) VK hash for a custom predicate.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §v2, the `vk_hash` inside
/// [`WitnessedPredicateKind::Custom`] (and the matching
/// `Authorization::Custom` / `Effect::Custom` carriers) commits to
/// four components: the predicate's authoring bytes, the AIR
/// fingerprint of the verifier's AIR, the verifier-impl fingerprint,
/// and the proving-system identifier.
///
/// This is the predicate-side analog of
/// [`crate::factory::canonical_program_vk_v2`]. Use it for new VK
/// identifiers; the legacy [`canonical_predicate_vk`] (program-bytes-
/// only) remains as the bottom layer that v2 feeds.
pub fn canonical_predicate_vk_v2(
    predicate_bytes: &[u8],
    air_fingerprint: [u8; 32],
    verifier_fingerprint: crate::vk_v2::VerifierFingerprint,
    proving_system_id: crate::vk_v2::ProvingSystemId,
) -> [u8; 32] {
    crate::vk_v2::canonical_vk_v2(&crate::vk_v2::VkComponents {
        program_bytes: predicate_bytes,
        air_fingerprint,
        verifier_fingerprint,
        proving_system_id,
    })
}

/// A witness-attached predicate declaration.
///
/// Carries the *shape* (kind), the *commitment* binding the predicate's
/// shape/audience, the *input pointer* naming where the verifier
/// resolves its input from, and the *proof witness index* naming where
/// the verifier reads the proof bytes from in the action's witness
/// blobs vec.
///
/// The verifier is *not* embedded in the declaration — declarations are
/// serializable wire/state-bound data; the verifier is registered
/// separately and dispatched by kind.
///
/// # Replay semantics
///
/// Per PREDICATE-INVENTORY §6.3: when a receipt carries a witnessed
/// predicate, it must also carry the *snapshotted commitment* (resolved
/// at receipt-time) so scope-2 replay is deterministic. Replayers
/// reconstruct the verifier input from the snapshot, not from the
/// replayer's live chain. The receipt-builder populates the snapshot;
/// the replayer reads it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessedPredicate {
    /// Which predicate algebra applies.
    pub kind: WitnessedPredicateKind,
    /// The 32-byte commitment binding the predicate's shape and
    /// audience. Each kind's verifier interprets this — for `Dfa` it's
    /// the route-table root; for `Temporal` it's the DSL hash; for
    /// `BlindedSet` it's the Poseidon2 set commitment; for
    /// `MerkleMembership` it's the leaf-Merkle root; for `Custom` it's
    /// the verifier-key hash of the registered AIR.
    pub commitment: [u8; 32],
    /// Where the verifier reads its input from.
    pub input_ref: InputRef,
    /// Index into the action's `witness_blobs` vec naming which proof
    /// bytes feed the verifier. Lets one action carry multiple
    /// witnessed predicates, each pointing at its own proof.
    pub proof_witness_index: usize,
}

/// Where a `WitnessedPredicate`'s verifier reads its input from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InputRef {
    /// Read from the cell's state slot at this index.
    Slot { index: u8 },
    /// Read from the action's witness blob at this index. The witness
    /// can be cleartext (per PREDICATE-INVENTORY §5: "cleartext-inside
    /// the sender") while the proof is the acceptance-inside shell.
    Witness { index: usize },
    /// Public input — the verifier reads from the proof's own PI vec.
    /// Use this for predicates whose input is already part of the
    /// proof's public statement (e.g. `BridgePredicateProof`'s
    /// `fact_commitment`).
    PublicInput { pi_index: usize },
    /// The sender's identity / public key. Use for sender-bound
    /// witnessed predicates (BlindedSenderAuthorized, signature
    /// attestations).
    Sender,
    /// The canonical action signing message — the bytes
    /// `compute_partial_signing_message(action, position, federation_id,
    /// turn_nonce)` produces (federation_id + action hash + position +
    /// turn_nonce). Used by `Authorization::Custom` so the predicate
    /// proves "the caller authorized THIS turn at THIS federation at
    /// THIS nonce position" (AUTHORIZATION-CUSTOM-DESIGN §11.5).
    ///
    /// The executor binds this input automatically when dispatching a
    /// `WitnessedPredicate` for authorization; surfaces that evaluate
    /// `WitnessedPredicate` outside an action-authorization context
    /// (slot caveats, preconditions) must reject this variant as
    /// shape-mismatch.
    SigningMessage,
}

/// The predicate-algebra kind a [`WitnessedPredicate`] uses.
///
/// Platform-reserved built-ins enumerate the witness-bearing predicate
/// algebras already present in the tree. `Custom { vk_hash }` is the
/// open escape for app-defined kinds, mirroring `Effect::Custom`'s
/// 32-byte verifier-key hash precedent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WitnessedPredicateKind {
    /// DFA-bytestring acceptance per `wire::dfa_router` / RBG compiler
    /// (`circuit::dsl::circuit:1711-1941`). Input is the message
    /// bytestring; proof is the AIR trace STARK. Commitment is the
    /// route-table root.
    ///
    /// Boundary:
    /// - Cleartext-inside:  route-table-author + input-presenter.
    /// - Commitment-inside: anyone with route-table-root.
    /// - Acceptance-inside: STARK verifier.
    /// - Out-of-band:       everyone else.
    Dfa,
    /// Temporal predicate over N receipts per
    /// `circuit::temporal_predicate_dsl`. Input is the receipt-chain's
    /// per-step values; proof is the predicate AIR STARK. Commitment
    /// is the DSL IR hash.
    ///
    /// Boundary:
    /// - Cleartext-inside:  the chain-value holder.
    /// - Commitment-inside: anyone with the DSL hash + state roots.
    /// - Acceptance-inside: STARK verifier (learns predicate_type,
    ///   threshold, num_steps from PI).
    /// - Out-of-band:       anyone without the proof.
    Temporal,
    /// Poseidon2 Merkle membership against a leaf-Merkle root. Input
    /// is the leaf; commitment is the root. Subsumes the placeholder
    /// `cell::capability_proof::StarkMembership` once a real gadget
    /// lands.
    ///
    /// Boundary:
    /// - Cleartext-inside:  set author + leaf-holder.
    /// - Commitment-inside: anyone with the root.
    /// - Acceptance-inside: STARK / Merkle verifier.
    /// - Out-of-band:       everyone else.
    MerkleMembership,
    /// **Categorical dual of [`Self::MerkleMembership`].** Proof-of-
    /// non-membership against a sorted-leaf Merkle set. Input is the
    /// candidate leaf (the value alleged to be *absent*); commitment
    /// is the sorted-set Merkle root. The proof is a sorted-set
    /// neighbor-witness: the prover exhibits adjacent leaves
    /// `A < candidate < B` from the sorted leaf-list, each with their
    /// own Merkle path against `commitment`, and the verifier checks
    /// that the candidate falls in the open interval `(A, B)` (and
    /// that A, B are *consecutive* in the leaf order). The neighbors
    /// belong to the set; the candidate provably does not.
    ///
    /// Powers `StateConstraint::Renounced` (Tier 2 categorical
    /// primitive per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2 / §9.2.1`):
    /// "the prover's identity is *not* in this authorized set." App
    /// drivers: governance recusal, compliance attestation
    /// ("blacklist non-membership"), selective non-disclosure
    /// ("prove I'm NOT in the under-18 set"), revocation lookups.
    ///
    /// Boundary:
    /// - Cleartext-inside:  set author + neighbor-witnesses.
    /// - Commitment-inside: anyone with the sorted-set root.
    /// - Acceptance-inside: STARK / Merkle neighbor-witness verifier.
    /// - Out-of-band:       everyone else.
    NonMembership,
    /// Poseidon2 commitment to a set + non-revocation / non-membership
    /// proof against the blinded commitment. Used by
    /// `StateConstraint::SenderAuthorized { AuthorizedSet::BlindedSet { .. } }`.
    ///
    /// Boundary:
    /// - Cleartext-inside:  set author + each member's own membership.
    /// - Commitment-inside: federation (sees only the Poseidon2 root).
    /// - Acceptance-inside: STARK non-revocation verifier.
    /// - Out-of-band:       everyone else.
    BlindedSet,
    /// `BridgePredicateProof` — Gte/Lte/Gt/Lt/Neq/InRange over a
    /// committed fact attribute. Input is the hidden `private_value`;
    /// commitment is `fact_commitment = Poseidon2(fact_hash, state_root)`.
    ///
    /// Boundary:
    /// - Cleartext-inside:  fact-holder.
    /// - Commitment-inside: anyone with the fact_commitment.
    /// - Acceptance-inside: STARK predicate-proof verifier.
    /// - Out-of-band:       anyone without the proof.
    BridgePredicate,
    /// Pedersen equality / range proof — `ConservationProof` or
    /// `BulletproofRangeProof`. Verifier signature differs from
    /// FRI-STARK (Schnorr / Bulletproof); this kind exists so apps
    /// can declare a Pedersen-curtain predicate from the same surface.
    ///
    /// Boundary:
    /// - Cleartext-inside:  value-holder (knows blinding + value).
    /// - Commitment-inside: anyone with the Pedersen commitment.
    /// - Acceptance-inside: Schnorr / Bulletproof verifier.
    /// - Out-of-band:       everyone else.
    PedersenEquality,
    /// Custom — `vk_hash` names a registered AIR / verifier. App-side
    /// extensibility escape. Boundary contract is the registering
    /// app's responsibility; the registry validates the verifier
    /// fn-ptr matches the hash but cannot validate boundary claims.
    Custom { vk_hash: [u8; 32] },
}

impl WitnessedPredicate {
    /// Construct a built-in DFA-acceptance witnessed predicate.
    pub fn dfa(route_table_root: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::Dfa,
            commitment: route_table_root,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in Temporal-predicate witnessed predicate.
    pub fn temporal(dsl_hash: [u8; 32], witness_index: usize, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::Temporal,
            commitment: dsl_hash,
            input_ref: InputRef::Witness {
                index: witness_index,
            },
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in Merkle-membership witnessed predicate.
    pub fn merkle_membership(set_root: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::MerkleMembership,
            commitment: set_root,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in non-membership witnessed predicate (the
    /// categorical dual of [`Self::merkle_membership`]). Used by
    /// `StateConstraint::Renounced` and "blacklist absence"
    /// attestations; the proof is a sorted-set neighbor-witness
    /// against `sorted_set_root`.
    pub fn non_membership(sorted_set_root: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::NonMembership,
            commitment: sorted_set_root,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in BlindedSet membership witnessed predicate.
    pub fn blinded_set(set_commitment: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::BlindedSet,
            commitment: set_commitment,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in BridgePredicate witnessed predicate.
    pub fn bridge_predicate(fact_commitment: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::BridgePredicate,
            commitment: fact_commitment,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a built-in Pedersen-equality witnessed predicate.
    pub fn pedersen_equality(commitment: [u8; 32], input: InputRef, proof_idx: usize) -> Self {
        Self {
            kind: WitnessedPredicateKind::PedersenEquality,
            commitment,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }

    /// Construct a custom witnessed predicate, app-defined.
    pub fn custom(
        vk_hash: [u8; 32],
        commitment: [u8; 32],
        input: InputRef,
        proof_idx: usize,
    ) -> Self {
        Self {
            kind: WitnessedPredicateKind::Custom { vk_hash },
            commitment,
            input_ref: input,
            proof_witness_index: proof_idx,
        }
    }
}

/// Resolved input passed to a registered verifier.
///
/// The executor resolves a [`WitnessedPredicate`]'s `input_ref` against
/// the current execution context (cell state, action witness blobs,
/// proof PI, sender pk) and hands the verifier this concrete value.
#[derive(Clone, Debug)]
pub enum PredicateInput<'a> {
    /// 32-byte field-element slot value (from `InputRef::Slot`).
    Slot(&'a [u8; 32]),
    /// Arbitrary cleartext witness bytes (from `InputRef::Witness`).
    Bytes(&'a [u8]),
    /// Public-input felts (from `InputRef::PublicInput`).
    PublicInput(&'a [u64]),
    /// Sender public key (from `InputRef::Sender`).
    Sender(&'a [u8; 32]),
    /// Canonical action signing message bytes (from
    /// `InputRef::SigningMessage`). Used by `Authorization::Custom`.
    SigningMessage(&'a [u8]),
}

/// Errors a witnessed-predicate verifier can produce.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessedPredicateError {
    /// The verifier rejected the proof.
    Rejected {
        kind_name: &'static str,
        reason: String,
    },
    /// The verifier requires a specific input shape that wasn't
    /// supplied (e.g. `Slot` got but expected `Witness`).
    InputShapeMismatch {
        kind_name: &'static str,
        expected: &'static str,
        actual: &'static str,
    },
    /// No verifier is registered for this kind.
    KindNotRegistered { kind: WitnessedPredicateKind },
    /// The action did not carry the expected proof blob.
    ProofMissing { proof_witness_index: usize },
}

impl core::fmt::Display for WitnessedPredicateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Rejected { kind_name, reason } => {
                write!(f, "witnessed predicate {kind_name} rejected: {reason}")
            }
            Self::InputShapeMismatch {
                kind_name,
                expected,
                actual,
            } => write!(
                f,
                "witnessed predicate {kind_name} input shape mismatch: expected {expected}, got {actual}"
            ),
            Self::KindNotRegistered { kind } => {
                write!(
                    f,
                    "no verifier registered for witnessed predicate kind {kind:?}"
                )
            }
            Self::ProofMissing {
                proof_witness_index,
            } => write!(
                f,
                "witnessed predicate proof missing at witness_index {proof_witness_index}"
            ),
        }
    }
}

impl std::error::Error for WitnessedPredicateError {}

/// A registered verifier for a `WitnessedPredicateKind`.
///
/// The trait is intentionally object-safe so the registry can hold
/// `Arc<dyn WitnessedPredicateVerifier>` and dispatch by kind at
/// runtime. Implementations live wherever the underlying algebra
/// lives — `circuit::dsl::circuit` for the DFA AIR,
/// `circuit::temporal_predicate_dsl` for Temporal, etc. — and register
/// themselves via [`WitnessedPredicateRegistry::register_builtin`] or
/// [`WitnessedPredicateRegistry::register_custom`].
pub trait WitnessedPredicateVerifier: Send + Sync {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &'static str;

    /// The kind this verifier handles.
    fn kind(&self) -> WitnessedPredicateKind;

    /// Verify a proof against this kind's algebra. Returns `Ok(())` on
    /// accept; returns a `WitnessedPredicateError::Rejected` (or
    /// `InputShapeMismatch`) on reject. The verifier may NOT make
    /// any state mutations.
    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError>;
}

use std::collections::BTreeMap;
use std::sync::Arc;

/// Verifies that two sorted-set neighbor leaves are bound to **consecutive
/// leaf indices under a committed Merkle root** — the cryptographic teeth that
/// close the Silver non-membership wide-bracket forge.
///
/// # Why this is a separate, injected trait
///
/// The real adjacency check is a STARK
/// (`dregg_circuit::membership_adjacency_air`). The `dregg-cell` crate must not
/// depend on `dregg-circuit` in its default build (dependency-cycle layering;
/// cf. [`NotYetWiredVerifier`]), so the cell-side neighbor verifiers
/// ([`SortedNeighborNonMembershipVerifier`], [`CredentialSetMembershipVerifier`])
/// hold an `Option<Arc<dyn NeighborAdjacencyVerifier>>`. The host (the
/// `dregg-turn` executor, which *does* link `dregg-circuit`) installs the real
/// STARK-backed implementation via
/// [`WitnessedPredicateRegistry::register_builtin`].
///
/// # Fail-closed contract
///
/// When **no** adjacency verifier is installed, the neighbor verifiers
/// **reject** every non-membership / non-revocation proof. This is the
/// "improve, don't degrade" posture: the previous commitment-keyed-tag-only
/// form silently accepted attacker-chosen wide brackets
/// (`lower=0x00…`, `upper=0xFF…`) for any candidate. Refusing until the real
/// adjacency STARK is wired is strictly sounder than that forge.
pub trait NeighborAdjacencyVerifier: Send + Sync {
    /// Verify that `lower` and `upper` are **consecutive** leaves under the
    /// sorted-set Merkle `root`, using the prover-supplied `adjacency_proof`
    /// bytes. Returns `Ok(())` on accept; an explanatory `Err(reason)` on
    /// reject. Implementations MUST bind the proof to `(root, lower, upper)`
    /// and enforce `index(upper) == index(lower) + 1`.
    fn verify_adjacency(
        &self,
        root: &[u8; 32],
        lower: &[u8; 32],
        upper: &[u8; 32],
        adjacency_proof: &[u8],
    ) -> Result<(), String>;
}

/// Authority resolving a BlindedSet predicate `commitment` (the stable
/// `(issuer, schema)` tag) to the issuer's **real, on-chain-published**
/// membership/revocation accumulator roots.
///
/// # Why this exists (the self-fabrication forge)
///
/// A [`CredentialSetMembershipProof`] carries `issuer_set_root` /
/// `revocation_root` *inside the proof*. The membership Merkle path and the
/// binding tag are self-consistent for ANY pair of roots — including a pair
/// the prover invented. So a prover can build their own one-leaf accumulator
/// (containing only themselves) with an empty revocation set, point
/// `issuer_set_root` at it, and self-attest membership in an issuer's set they
/// were never admitted to. Closed-form hashing alone cannot detect this,
/// because nothing pins the prover-supplied roots to the issuer's published
/// state.
///
/// An `IssuerRootAuthority` closes the forge: the host installs an authority
/// that knows (from the issuer cell's on-chain `MEMBERSHIP_ROOT_SLOT` /
/// `REVOCATION_ROOT_SLOT`, a federation root registry, etc.) which roots are
/// genuinely the issuer's. [`CredentialSetMembershipVerifier`] consults it and
/// rejects any proof whose roots are not authorized for the `commitment`.
///
/// # Fail-closed contract
///
/// When **no** authority is installed, [`CredentialSetMembershipVerifier`]
/// **rejects every BlindedSet proof** — it has no channel to the issuer's real
/// roots and so cannot soundly distinguish an honest member from a
/// self-fabricator. Refusing is strictly sounder than accepting attacker-chosen
/// roots ("improve, don't degrade").
pub trait IssuerRootAuthority: Send + Sync {
    /// Return `Ok(())` iff `(issuer_set_root, revocation_root)` are the issuer's
    /// genuine published roots for the BlindedSet `commitment`. Return an
    /// explanatory `Err(reason)` otherwise (unknown commitment, root mismatch).
    fn verify_issuer_roots(
        &self,
        commitment: &[u8; 32],
        issuer_set_root: &[u8; 32],
        revocation_root: &[u8; 32],
    ) -> Result<(), String>;
}

/// A static [`IssuerRootAuthority`] backed by an in-memory table of
/// `commitment -> (issuer_set_root, revocation_root)` bindings.
///
/// Production hosts that read issuer roots from on-chain slots install their
/// own authority; this one suits hosts that snapshot the issuer registry and
/// fixed-point test wiring. A commitment absent from the table (or present with
/// different roots) is rejected — fail-closed by construction.
#[derive(Clone, Debug, Default)]
pub struct StaticIssuerRootAuthority {
    bindings: BTreeMap<[u8; 32], ([u8; 32], [u8; 32])>,
}

impl StaticIssuerRootAuthority {
    /// Construct an empty authority (rejects everything until roots are added).
    pub fn new() -> Self {
        Self {
            bindings: BTreeMap::new(),
        }
    }

    /// Authorize `(issuer_set_root, revocation_root)` for `commitment`.
    pub fn authorize(
        mut self,
        commitment: [u8; 32],
        issuer_set_root: [u8; 32],
        revocation_root: [u8; 32],
    ) -> Self {
        self.bindings
            .insert(commitment, (issuer_set_root, revocation_root));
        self
    }
}

impl IssuerRootAuthority for StaticIssuerRootAuthority {
    fn verify_issuer_roots(
        &self,
        commitment: &[u8; 32],
        issuer_set_root: &[u8; 32],
        revocation_root: &[u8; 32],
    ) -> Result<(), String> {
        match self.bindings.get(commitment) {
            None => Err(
                "no issuer roots registered for this (issuer, schema) commitment; \
                 the prover-supplied accumulator is not a recognized issuer set"
                    .to_string(),
            ),
            Some((set_root, rev_root)) => {
                if set_root != issuer_set_root {
                    return Err(
                        "issuer_set_root does not match the issuer's published membership root \
                         (self-fabricated accumulator rejected)"
                            .to_string(),
                    );
                }
                if rev_root != revocation_root {
                    return Err(
                        "revocation_root does not match the issuer's published revocation root"
                            .to_string(),
                    );
                }
                Ok(())
            }
        }
    }
}

/// The registry resolving [`WitnessedPredicateKind`]s to their
/// verifiers.
///
/// Per PREDICATE-INVENTORY §6.2: a *closed enum for the platform set,
/// with a `Custom { vk_hash }` escape for app-defined kinds*. The
/// closed set is keyed on the kind discriminant; the custom set is
/// keyed on the 32-byte `vk_hash`.
///
/// The registry is intentionally **not** a singleton — each executor
/// instance can hold its own (a host that wants to refuse a kind
/// simply doesn't register it).
#[derive(Default, Clone)]
pub struct WitnessedPredicateRegistry {
    /// Built-in kind verifiers (Dfa, Temporal, MerkleMembership,
    /// BlindedSet, BridgePredicate, PedersenEquality).
    builtins: BTreeMap<BuiltinKey, Arc<dyn WitnessedPredicateVerifier>>,
    /// App-registered custom verifiers, keyed on `vk_hash`.
    custom: BTreeMap<[u8; 32], Arc<dyn WitnessedPredicateVerifier>>,
}

impl std::fmt::Debug for WitnessedPredicateRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WitnessedPredicateRegistry")
            .field("builtins_count", &self.builtins.len())
            .field("custom_count", &self.custom.len())
            .finish()
    }
}

/// Ordering key for the built-in registry. Closed enum kinds are
/// totally ordered by their discriminant; `Custom` is *not* a built-in
/// — it lives in the `custom` map keyed on vk_hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BuiltinKey {
    Dfa,
    Temporal,
    MerkleMembership,
    NonMembership,
    BlindedSet,
    BridgePredicate,
    PedersenEquality,
}

impl BuiltinKey {
    fn from_kind(k: WitnessedPredicateKind) -> Option<Self> {
        match k {
            WitnessedPredicateKind::Dfa => Some(Self::Dfa),
            WitnessedPredicateKind::Temporal => Some(Self::Temporal),
            WitnessedPredicateKind::MerkleMembership => Some(Self::MerkleMembership),
            WitnessedPredicateKind::NonMembership => Some(Self::NonMembership),
            WitnessedPredicateKind::BlindedSet => Some(Self::BlindedSet),
            WitnessedPredicateKind::BridgePredicate => Some(Self::BridgePredicate),
            WitnessedPredicateKind::PedersenEquality => Some(Self::PedersenEquality),
            WitnessedPredicateKind::Custom { .. } => None,
        }
    }
}

impl WitnessedPredicateRegistry {
    /// Construct an empty registry. Use [`Self::with_stubs`] for the
    /// development-default registry that returns
    /// `KindNotRegistered` rejections for every built-in (useful for
    /// tests where the surface contract matters but the proof algebra
    /// is out of scope).
    pub fn empty() -> Self {
        Self::default()
    }

    /// Construct a registry with stub verifiers for every built-in
    /// kind. Each stub returns `Ok(())` only when the proof bytes are
    /// not empty and have the kind's documented length-prefix shape;
    /// otherwise returns `Rejected`. Stubs do NOT replace real
    /// cryptographic verification — they exist so callers that want
    /// to exercise the registry plumbing without pulling in the
    /// circuit crate can do so.
    ///
    /// Production callers should register real verifiers from the
    /// `dregg-circuit` (or app-side) crates before evaluating any
    /// real witnessed predicate.
    pub fn with_stubs() -> Self {
        let mut r = Self::empty();
        r.register_builtin(Arc::new(StubVerifier::dfa()));
        r.register_builtin(Arc::new(StubVerifier::temporal()));
        r.register_builtin(Arc::new(StubVerifier::merkle_membership()));
        // NonMembership / BlindedSet ship REAL verifiers, but their soundness
        // now requires a Merkle-adjacency STARK (consecutive-index binding)
        // that the cell crate cannot run. Under `with_stubs` no adjacency
        // verifier is installed, so these fail closed — their accept path is
        // exercised in the `dregg-turn` integration tests where the
        // circuit-backed adjacency verifier is installed.
        r.register_builtin(Arc::new(SortedNeighborNonMembershipVerifier::fail_closed()));
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::fail_closed()));
        r.register_builtin(Arc::new(StubVerifier::bridge_predicate()));
        r.register_builtin(Arc::new(StubVerifier::pedersen_equality()));
        r
    }

    /// Construct the executor-default registry — Cav-Codex Block 3.5
    /// **post AIR-soundness audit (commit `ce1e2def`).**
    ///
    /// # Soundness contract
    ///
    /// The default registry installs verifiers that **reject** any proof
    /// whose underlying cryptographic algebra is not yet wired into the
    /// cell crate. Concretely:
    ///
    /// - `Dfa`, `Temporal`, `MerkleMembership`, `BlindedSet`,
    ///   `BridgePredicate`, `PedersenEquality` →
    ///   [`NotYetWiredVerifier`]: every `verify(...)` returns
    ///   [`WitnessedPredicateError::Rejected`] with a `not yet wired`
    ///   reason regardless of proof bytes.
    /// - `NonMembership` → [`SortedNeighborNonMembershipVerifier`]: a
    ///   real (Silver-Sound) sorted-set neighbor verifier. See
    ///   [`NonMembershipNeighborProof::adjacency_tag`] for the
    ///   commitment-keyed adjacency binding that closes the prior
    ///   public-sentinel attack.
    ///
    /// # Why reject by default?
    ///
    /// Previously (`pub fn default_builtins() -> Self { Self::with_stubs() }`)
    /// the registry returned `with_stubs()`, which accepted any non-empty
    /// proof bytes for every kind. This was a **complete soundness loss**:
    /// a playground prover could submit a 1-byte garbage "proof" against
    /// any commitment and pass every `Witnessed` slot caveat / precondition
    /// / authorization. The AIR-soundness audit
    /// (`AIR-SOUNDNESS-AUDIT.md`) flagged this as the single largest
    /// playground risk amplifier.
    ///
    /// The cell crate cannot depend on `dregg-circuit` (it would close a
    /// dependency cycle), so the *real* per-kind verifiers must be
    /// installed by the host at startup via
    /// [`WitnessedPredicateRegistry::register_builtin`]. Until that
    /// install happens, refusing is the only honest behavior — accepting
    /// garbage was a soundness lie dressed up as fail-safe-but-loud.
    ///
    /// # Migration for callers
    ///
    /// - **Production hosts** must install real verifiers (e.g. the
    ///   forthcoming `dregg_circuit::witnessed_predicate::default_registry()`
    ///   adapter) for every kind they intend to exercise.
    /// - **Tests** that exercise *plumbing only* (executor dispatch,
    ///   registry routing, error mapping) should switch to
    ///   [`Self::with_stubs`], which preserves the prior permissive
    ///   behavior under an explicit name.
    /// - **Tests** that exercise adversarial-proof rejection benefit
    ///   from the default — it now rejects forged proofs out of the box.
    pub fn default_builtins() -> Self {
        let mut r = Self::empty();
        r.register_builtin(Arc::new(NotYetWiredVerifier::dfa()));
        r.register_builtin(Arc::new(NotYetWiredVerifier::temporal()));
        r.register_builtin(Arc::new(NotYetWiredVerifier::merkle_membership()));
        // NonMembership / BlindedSet ship real verifiers, but they now REQUIRE
        // a Merkle-adjacency STARK that the cell crate cannot run. The cell-only
        // default therefore installs them FAIL-CLOSED (no adjacency verifier);
        // the host upgrades them to the circuit-backed form via
        // `register_builtin` (see `dregg_turn::executor::membership_verifier`).
        r.register_builtin(Arc::new(SortedNeighborNonMembershipVerifier::fail_closed()));
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::fail_closed()));
        r.register_builtin(Arc::new(NotYetWiredVerifier::bridge_predicate()));
        r.register_builtin(Arc::new(NotYetWiredVerifier::pedersen_equality()));
        r
    }

    /// Register (or replace) a built-in kind's verifier. Custom kinds
    /// (whose verifiers are keyed on vk_hash) go through
    /// [`Self::register_custom`].
    pub fn register_builtin(&mut self, verifier: Arc<dyn WitnessedPredicateVerifier>) {
        let key = BuiltinKey::from_kind(verifier.kind())
            .expect("register_builtin called with Custom kind; use register_custom");
        self.builtins.insert(key, verifier);
    }

    /// Register an app-defined `Custom { vk_hash }` verifier.
    pub fn register_custom(
        &mut self,
        vk_hash: [u8; 32],
        verifier: Arc<dyn WitnessedPredicateVerifier>,
    ) {
        debug_assert!(
            matches!(verifier.kind(), WitnessedPredicateKind::Custom { vk_hash: h } if h == vk_hash),
            "register_custom: verifier.kind() vk_hash must match passed vk_hash"
        );
        self.custom.insert(vk_hash, verifier);
    }

    /// Look up a verifier for the given kind. Returns `None` if no
    /// verifier is registered for that kind.
    pub fn get(&self, kind: WitnessedPredicateKind) -> Option<Arc<dyn WitnessedPredicateVerifier>> {
        match kind {
            WitnessedPredicateKind::Custom { vk_hash } => self.custom.get(&vk_hash).cloned(),
            other => BuiltinKey::from_kind(other).and_then(|k| self.builtins.get(&k).cloned()),
        }
    }

    /// Verify a `WitnessedPredicate` against its registered kind's
    /// verifier. The caller is responsible for resolving the
    /// `input_ref` into a concrete [`PredicateInput`] and supplying
    /// the proof bytes.
    pub fn verify(
        &self,
        wp: &WitnessedPredicate,
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let verifier = self
            .get(wp.kind)
            .ok_or(WitnessedPredicateError::KindNotRegistered { kind: wp.kind })?;
        verifier.verify(&wp.commitment, input, proof_bytes)
    }
}

// ─────────────────────────────────────────────────────────────────────
// WitnessProducer — left adjoint of WitnessedPredicateVerifier
// (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.4 + §4.1 + §9.1.4)
// ─────────────────────────────────────────────────────────────────────

/// Errors a `WitnessProducer` can surface while constructing proof
/// bytes for a `WitnessedPredicate`.
///
/// Symmetric to [`WitnessedPredicateError`] on the verifier side: each
/// "the verifier rejected" shape has a corresponding "the producer
/// could not synthesize" shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessProducerError {
    /// The producer received an input shape it cannot fold into a
    /// witness — e.g. `Sender` input given to a producer that expects
    /// `Slot`-shaped witnesses.
    InputShapeMismatch {
        kind_name: &'static str,
        expected: &'static str,
        actual: &'static str,
    },
    /// The producer could not synthesize a witness from the supplied
    /// input (commitment mismatch, missing aux data, AIR proving
    /// error, etc.). `reason` carries the producer-side diagnostic.
    ProducerFailed {
        kind_name: &'static str,
        reason: String,
    },
    /// The producer's vk_hash differs from the requested commitment;
    /// the registry routed to the wrong producer (or the caller is
    /// trying to forge a proof under a different VK).
    VkHashMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// No producer is registered for this kind.
    KindNotRegistered { kind: WitnessedPredicateKind },
}

impl core::fmt::Display for WitnessProducerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InputShapeMismatch {
                kind_name,
                expected,
                actual,
            } => write!(
                f,
                "witness producer {kind_name} input shape mismatch: expected {expected}, got {actual}"
            ),
            Self::ProducerFailed { kind_name, reason } => {
                write!(f, "witness producer {kind_name} failed: {reason}")
            }
            Self::VkHashMismatch { expected, actual } => write!(
                f,
                "witness producer vk_hash mismatch: expected {expected:02x?}, got {actual:02x?}"
            ),
            Self::KindNotRegistered { kind } => write!(
                f,
                "no witness producer registered for predicate kind {kind:?}"
            ),
        }
    }
}

impl std::error::Error for WitnessProducerError {}

/// Producer-side counterpart to [`WitnessedPredicateVerifier`] — the
/// left adjoint of the `Predicate ⊣ Witness` adjunction.
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.4 + §4.1 + §9.1.4: every
/// prover in the tree (`BridgePredicateProof::new`,
/// `PortableNoteProof::from_witness`, `BlindedMerkleStarkAir::prove`,
/// …) already implements *this shape* ad hoc. Naming it lifts the
/// asymmetry from "verifier-only trait, prover-side bespoke" to a
/// symmetric pair:
///
/// - [`WitnessedPredicateVerifier::verify`] is the **counit**: given a
///   witness, decide acceptance.
/// - [`WitnessProducer::produce`] is the **unit**: given an input,
///   synthesize the witness that the counit accepts.
/// - The unit-counit identity: for every well-formed
///   `(commitment, input, witness)`, the proof bytes the producer
///   returns must verify under the registered verifier with the same
///   `(commitment, input)`. Round-trip tests assert this.
///
/// # Object-safety
///
/// The trait is object-safe so [`WitnessProducerRegistry`] holds
/// `Arc<dyn WitnessProducer>` and dispatches by kind at runtime,
/// mirroring [`WitnessedPredicateRegistry`].
///
/// # Witness vs. input
///
/// The signature splits **input** (the predicate's public datum the
/// verifier's PI loop binds against; resolved from [`InputRef`]) from
/// **witness** (the prover-side secret / auxiliary data — Merkle
/// paths, openings, full preimages of commitments). Both are needed
/// to produce proof bytes; only input is needed to verify.
///
/// # vk_hash binding
///
/// Each producer publishes its `vk_hash` (for `Custom` kinds) or
/// returns `[0u8; 32]` for built-in kinds. The registry checks the
/// hash on dispatch so a producer registered for vk `H1` cannot be
/// invoked under vk `H2`. This is the producer-side analog of the
/// verifier's `kind()` dispatch.
pub trait WitnessProducer: Send + Sync {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &'static str;

    /// The predicate kind this producer synthesizes proofs for.
    fn kind(&self) -> WitnessedPredicateKind;

    /// For `Custom` kinds, the verifier-key hash this producer
    /// targets. For built-in kinds, returns the all-zero hash. The
    /// registry uses this to disambiguate multiple `Custom`
    /// producers.
    fn vk_hash(&self) -> [u8; 32] {
        match self.kind() {
            WitnessedPredicateKind::Custom { vk_hash } => vk_hash,
            _ => [0u8; 32],
        }
    }

    /// Synthesize proof bytes for a [`WitnessedPredicate`] given a
    /// concrete input and a witness blob.
    ///
    /// - `commitment`: the predicate's commitment (must match what
    ///   the verifier expects — Merkle root, DSL hash, blinded set
    ///   commitment, etc.).
    /// - `input`: the resolved [`PredicateInput`] (same shape the
    ///   verifier consumes).
    /// - `witness_bytes`: the prover-side auxiliary data —
    ///   Merkle path, opening, full message, etc.
    ///
    /// Returns the proof bytes the verifier accepts. The unit-counit
    /// identity: feeding the result back through the verifier's
    /// `verify` (with the same commitment + input) must accept.
    fn produce(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        witness_bytes: &[u8],
    ) -> Result<Vec<u8>, WitnessProducerError>;
}

/// Registry of [`WitnessProducer`]s — the producer-side mirror of
/// [`WitnessedPredicateRegistry`].
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §4.1: the adjunction
/// `Predicate ⊣ Witness` is complete when both functors are named.
/// This registry is the **left adjoint / free** functor; the
/// verifier registry is the **right adjoint / forgetful** functor.
/// Holding both side-by-side gives every kind a symmetric prover-
/// side API.
///
/// # SDK ergonomics
///
/// Today an SDK that wants to construct a proof for a
/// `Witnessed { wp }` slot caveat picks the right per-kind prover by
/// hand (`BridgePredicateProof::new`, etc.). With this registry the
/// SDK calls `producer_registry.produce(&wp, &input, witness_bytes)`
/// and the same kind-dispatch logic the verifier already uses fires
/// on the producer side. Per-kind impls are still kind-specific code;
/// dispatch is unified.
#[derive(Default, Clone)]
pub struct WitnessProducerRegistry {
    /// Built-in kind producers.
    builtins: BTreeMap<BuiltinKey, Arc<dyn WitnessProducer>>,
    /// App-registered custom producers, keyed on `vk_hash`.
    custom: BTreeMap<[u8; 32], Arc<dyn WitnessProducer>>,
}

impl std::fmt::Debug for WitnessProducerRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WitnessProducerRegistry")
            .field("builtins_count", &self.builtins.len())
            .field("custom_count", &self.custom.len())
            .finish()
    }
}

impl WitnessProducerRegistry {
    /// Construct an empty registry.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Construct a registry with stub producers for every built-in
    /// kind — symmetric to [`WitnessedPredicateRegistry::with_stubs`].
    /// Each stub produces a length-prefixed witness blob that the
    /// matching stub verifier accepts (non-empty proof bytes); round-
    /// tripping a stub producer's output through a stub verifier
    /// satisfies the unit-counit identity in tests.
    ///
    /// Production callers must replace stubs with real per-kind
    /// producers (`dregg-circuit` for Dfa / Temporal /
    /// MerkleMembership / BlindedSet / BridgePredicate /
    /// PedersenEquality, app-side for `Custom`).
    pub fn with_stubs() -> Self {
        let mut r = Self::empty();
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::Dfa,
            name: "stub-producer-dfa",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::Temporal,
            name: "stub-producer-temporal",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::MerkleMembership,
            name: "stub-producer-merkle-membership",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::NonMembership,
            name: "stub-producer-non-membership",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::BlindedSet,
            name: "stub-producer-blinded-set",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::BridgePredicate,
            name: "stub-producer-bridge-predicate",
        }));
        r.register_builtin(Arc::new(StubProducer {
            kind: WitnessedPredicateKind::PedersenEquality,
            name: "stub-producer-pedersen-equality",
        }));
        r
    }

    /// Register (or replace) a built-in producer.
    pub fn register_builtin(&mut self, producer: Arc<dyn WitnessProducer>) {
        let key = BuiltinKey::from_kind(producer.kind())
            .expect("register_builtin called with Custom kind; use register_custom");
        self.builtins.insert(key, producer);
    }

    /// Register an app-defined `Custom { vk_hash }` producer.
    pub fn register_custom(&mut self, vk_hash: [u8; 32], producer: Arc<dyn WitnessProducer>) {
        debug_assert!(
            matches!(producer.kind(), WitnessedPredicateKind::Custom { vk_hash: h } if h == vk_hash),
            "register_custom: producer.kind() vk_hash must match passed vk_hash"
        );
        self.custom.insert(vk_hash, producer);
    }

    /// Look up a producer for the given kind.
    pub fn get(&self, kind: WitnessedPredicateKind) -> Option<Arc<dyn WitnessProducer>> {
        match kind {
            WitnessedPredicateKind::Custom { vk_hash } => self.custom.get(&vk_hash).cloned(),
            other => BuiltinKey::from_kind(other).and_then(|k| self.builtins.get(&k).cloned()),
        }
    }

    /// Produce proof bytes for a [`WitnessedPredicate`] given a
    /// resolved input and witness. The caller is responsible for
    /// resolving the predicate's `input_ref` into a concrete
    /// [`PredicateInput`] — the same way the verifier registry's
    /// `verify` consumes it.
    pub fn produce(
        &self,
        wp: &WitnessedPredicate,
        input: &PredicateInput<'_>,
        witness_bytes: &[u8],
    ) -> Result<Vec<u8>, WitnessProducerError> {
        let producer = self
            .get(wp.kind)
            .ok_or(WitnessProducerError::KindNotRegistered { kind: wp.kind })?;
        // Enforce vk_hash consistency for Custom kinds.
        if let WitnessedPredicateKind::Custom { vk_hash } = wp.kind {
            let registered = producer.vk_hash();
            if registered != vk_hash {
                return Err(WitnessProducerError::VkHashMismatch {
                    expected: vk_hash,
                    actual: registered,
                });
            }
        }
        producer.produce(&wp.commitment, input, witness_bytes)
    }
}

/// Stub producer mirroring [`StubVerifier`]. Synthesizes a
/// domain-tagged length-prefixed blob of the form
/// `b"stub-witness:" || u32(witness_len) || witness_bytes`. The stub
/// verifier accepts any non-empty proof bytes, so this satisfies the
/// unit-counit identity for tests.
struct StubProducer {
    kind: WitnessedPredicateKind,
    name: &'static str,
}

impl WitnessProducer for StubProducer {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn produce(
        &self,
        _commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        witness_bytes: &[u8],
    ) -> Result<Vec<u8>, WitnessProducerError> {
        let mut out = Vec::with_capacity(13 + 4 + witness_bytes.len());
        out.extend_from_slice(b"stub-witness:");
        out.extend_from_slice(&(witness_bytes.len() as u32).to_le_bytes());
        out.extend_from_slice(witness_bytes);
        Ok(out)
    }
}

// ─────────────────────────────────────────────────────────────────────
// Stub verifiers
// ─────────────────────────────────────────────────────────────────────

/// A stub verifier for development / unit tests. Accepts non-empty
/// proof bytes; rejects empty ones. Does NOT perform real
/// cryptographic verification.
///
/// Production callers MUST replace stubs with real verifiers before
/// evaluating any witnessed predicate. The presence of a stub in the
/// registry is a deliberate fail-safe-but-loud signal: the kind is
/// declarable and the surface plumbing works, but soundness is the
/// real verifier's job.
struct StubVerifier {
    kind: WitnessedPredicateKind,
    name: &'static str,
}

impl StubVerifier {
    fn dfa() -> Self {
        Self {
            kind: WitnessedPredicateKind::Dfa,
            name: "stub-dfa",
        }
    }
    fn temporal() -> Self {
        Self {
            kind: WitnessedPredicateKind::Temporal,
            name: "stub-temporal",
        }
    }
    fn merkle_membership() -> Self {
        Self {
            kind: WitnessedPredicateKind::MerkleMembership,
            name: "stub-merkle-membership",
        }
    }
    fn bridge_predicate() -> Self {
        Self {
            kind: WitnessedPredicateKind::BridgePredicate,
            name: "stub-bridge-predicate",
        }
    }
    fn pedersen_equality() -> Self {
        Self {
            kind: WitnessedPredicateKind::PedersenEquality,
            name: "stub-pedersen-equality",
        }
    }
}

impl WitnessedPredicateVerifier for StubVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // SOUNDNESS GATE. The accept path of this stub exists ONLY in test
        // builds (`cfg(test)`) or builds explicitly compiled with the
        // `test-stubs` feature. In any other build — i.e. every production
        // binary — `StubVerifier::verify` is FAIL-CLOSED: it rejects every
        // proof regardless of its bytes. This makes it structurally
        // impossible for a misconfigured host that selects the stub registry
        // (`WitnessedPredicateRegistry::with_stubs()`) to authorize a forged
        // witness, because the stub never returns `Ok(())` outside a test
        // build. See the `test-stubs` feature in `cell/Cargo.toml`.
        #[cfg(not(any(test, feature = "test-stubs")))]
        {
            let _ = proof_bytes;
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name,
                reason: "StubVerifier is fail-closed in non-test builds: \
                         it never accepts a proof unless the crate is \
                         compiled with `cfg(test)` or the `test-stubs` \
                         feature. A real verifier for this kind must be \
                         installed via `register_builtin`."
                    .into(),
            });
        }

        // Test-only accept path: non-empty proof bytes pass, empty ones are
        // rejected so plumbing tests can exercise both arms.
        #[cfg(any(test, feature = "test-stubs"))]
        {
            if proof_bytes.is_empty() {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name,
                    reason: "stub verifier requires non-empty proof bytes".into(),
                });
            }
            Ok(())
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// NotYetWiredVerifier — soundness-honest default for kinds whose real
// verifier lives in `dregg-circuit` and must be host-installed.
// ─────────────────────────────────────────────────────────────────────

/// A verifier that **always rejects**, used as the default registration
/// for built-in predicate kinds whose real cryptographic verifier has
/// not been installed by the host.
///
/// # Why this exists
///
/// The cell crate cannot depend on `dregg-circuit` (cycle). The real
/// per-kind verifiers (`dsl::circuit` for Dfa, `dsl::membership` for
/// Merkle/BlindedSet, `temporal_predicate_dsl` for Temporal,
/// `bridge::present::verify_predicate_proof` for BridgePredicate,
/// Schnorr/Bulletproof for PedersenEquality) live in upstream crates.
/// Production hosts MUST install those verifiers via
/// [`WitnessedPredicateRegistry::register_builtin`] before any
/// `Witnessed { wp }` caveat is evaluated.
///
/// Until the host installs the real verifier, the only honest behavior
/// is to refuse — accepting garbage proofs (the previous behavior of
/// [`StubVerifier`] under `default_builtins`) was a complete soundness
/// loss for every witnessed-predicate caveat.
///
/// # Boundary
///
/// - The rejection reason names the missing crate / surface so an
///   operator can diagnose "I forgot to wire the bridge verifier" vs.
///   "I forgot to wire the Schnorr Pedersen adapter."
/// - The `proof_bytes` are ignored: there is no proof shape this
///   verifier accepts. This is intentional and matches the "improve,
///   don't degrade" discipline — a structural-only check that lets a
///   forged 96-byte blob through would be worse than honest rejection.
struct NotYetWiredVerifier {
    kind: WitnessedPredicateKind,
    name: &'static str,
    /// Human-readable name of the upstream module that should be wired
    /// into the registry for this kind.
    upstream: &'static str,
}

impl NotYetWiredVerifier {
    fn dfa() -> Self {
        Self {
            kind: WitnessedPredicateKind::Dfa,
            name: "not-yet-wired-dfa",
            upstream: "dregg_circuit::dsl::circuit",
        }
    }
    fn temporal() -> Self {
        Self {
            kind: WitnessedPredicateKind::Temporal,
            name: "not-yet-wired-temporal",
            upstream: "dregg_circuit::temporal_predicate_dsl",
        }
    }
    fn merkle_membership() -> Self {
        Self {
            kind: WitnessedPredicateKind::MerkleMembership,
            name: "not-yet-wired-merkle-membership",
            upstream: "dregg_circuit::dsl::membership::verify_membership_dsl_full",
        }
    }
    fn bridge_predicate() -> Self {
        Self {
            kind: WitnessedPredicateKind::BridgePredicate,
            name: "not-yet-wired-bridge-predicate",
            upstream: "dregg_bridge::present::verify_predicate_proof",
        }
    }
    fn pedersen_equality() -> Self {
        Self {
            kind: WitnessedPredicateKind::PedersenEquality,
            name: "not-yet-wired-pedersen-equality",
            upstream: "dregg_circuit::value_commitment (Schnorr) / bulletproofs (range)",
        }
    }
}

impl WitnessedPredicateVerifier for NotYetWiredVerifier {
    fn name(&self) -> &'static str {
        self.name
    }

    fn kind(&self) -> WitnessedPredicateKind {
        self.kind
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        _proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        Err(WitnessedPredicateError::Rejected {
            kind_name: self.name,
            reason: format!(
                "real verifier not yet installed in registry: host must call \
                 WitnessedPredicateRegistry::register_builtin with the \
                 adapter for `{}` before this kind can be verified",
                self.upstream
            ),
        })
    }
}

// ─────────────────────────────────────────────────────────────────────
// NonMembership: real (non-stub) sorted-set neighbor verifier
// ─────────────────────────────────────────────────────────────────────

/// Wire encoding for a [`WitnessedPredicateKind::NonMembership`] proof.
///
/// `lower` and `upper` are the adjacent leaves that witness the
/// candidate's absence: the prover asserts `lower < candidate < upper`
/// and that `lower, upper` are *consecutive* in the sorted leaf list.
///
/// Phase-1 wire shape (Merkle-paths-as-bytes deferred to the STARK
/// gadget). The verifier here enforces the *structural* invariants of
/// the neighbor witness:
/// 1. `lower < candidate` (lexicographic byte order),
/// 2. `candidate < upper`,
/// 3. `adjacency_tag == [`Self::adjacency_tag`]`(commitment, lower, upper)
///    — a per-(set, lower, upper) keyed BLAKE3 derivation that the
///    prover must reconstruct from the sorted set's Merkle root. This
///    closes the prior "public sentinel" attack
///    (`AIR-SOUNDNESS-AUDIT.md` finding #2) where an attacker chose
///    arbitrary `lower=0x00…`, `upper=0xFF…`, `tag=0xFE…` and bypassed
///    `Renounced` for an unknown set: today the tag binds to the
///    commitment, so a prover who doesn't know the set's `commitment`
///    cannot reconstruct the tag.
///
/// # Silver-Sound vs. Golden-Sound
///
/// This is **explicitly Silver-Sound, not Sound.** The tag commits to
/// the *set's root* but not to "lower and upper are adjacent leaves
/// **under** that root." An attacker who *knows the set's commitment*
/// (e.g. it was published) can still forge `lower=0x00…`,
/// `upper=0xFF…`, compute a valid `adjacency_tag`, and claim
/// non-membership for any candidate without any Merkle path. Closing
/// that attack requires a real Merkle adjacency STARK that proves
/// `MerklePath(commitment, lower)` and `MerklePath(commitment, upper)`
/// at *consecutive leaf indices* — the Golden Vision lift. Until that
/// lands, this verifier is the **interim** form: stronger than the
/// pre-audit public sentinel (no one without the commitment can forge),
/// weaker than the full Merkle gadget (anyone with the commitment can).
///
/// # Versioning
///
/// The keyed-derive domain `dregg-nonmembership-adjacency-v1` is a
/// versioned wire format. The Golden lift will introduce
/// `dregg-nonmembership-adjacency-v2` with a different layout that
/// includes leaf-index public inputs; v1 and v2 produce different
/// tags so the cut-over is unambiguous.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipNeighborProof {
    pub lower: [u8; 32],
    pub upper: [u8; 32],
    /// Per-(commitment, lower, upper) keyed adjacency commitment;
    /// reconstruct via [`Self::adjacency_tag`].
    pub adjacency_tag: [u8; 32],
}

impl NonMembershipNeighborProof {
    /// Encode the proof to its 96-byte wire form
    /// (lower || upper || adjacency_tag).
    pub fn to_bytes(&self) -> [u8; 96] {
        let mut out = [0u8; 96];
        out[0..32].copy_from_slice(&self.lower);
        out[32..64].copy_from_slice(&self.upper);
        out[64..96].copy_from_slice(&self.adjacency_tag);
        out
    }
    /// Decode from the 96-byte wire form.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 96 {
            return None;
        }
        let mut lower = [0u8; 32];
        let mut upper = [0u8; 32];
        let mut tag = [0u8; 32];
        lower.copy_from_slice(&bytes[0..32]);
        upper.copy_from_slice(&bytes[32..64]);
        tag.copy_from_slice(&bytes[64..96]);
        Some(Self {
            lower,
            upper,
            adjacency_tag: tag,
        })
    }

    /// Compute the canonical adjacency tag for a non-membership
    /// neighbor witness.
    ///
    /// `tag = BLAKE3_keyed("dregg-nonmembership-adjacency-v1",
    ///                     commitment || lower || upper)`.
    ///
    /// The prover must reconstruct this from the set's Merkle root
    /// (`commitment`) and the chosen adjacent leaves. An attacker who
    /// doesn't know `commitment` cannot reconstruct the tag, which is
    /// what closes the prior public-sentinel attack — the previous
    /// `CONSECUTIVE_TAG = [0xFE; 32]` was a public constant, so anyone
    /// could "prove" non-membership for arbitrary sets.
    ///
    /// # Silver-vs-Golden gap
    ///
    /// This binds the tag to the set's *commitment* but **not** to a
    /// real Merkle adjacency relation. An attacker who knows
    /// `commitment` (e.g. a public root) can still pick
    /// `lower = 0x00…`, `upper = 0xFF…` and recompute the tag. The
    /// remaining attack requires the real Merkle adjacency STARK
    /// (Golden Vision); this commitment-keyed form is the interim
    /// rung. Document this when wiring `Renounced` flows.
    pub fn adjacency_tag(commitment: &[u8; 32], lower: &[u8; 32], upper: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-nonmembership-adjacency-v1");
        hasher.update(commitment);
        hasher.update(lower);
        hasher.update(upper);
        *hasher.finalize().as_bytes()
    }

    /// Construct a well-formed neighbor proof against a known set
    /// commitment. Prover-side helper that pairs with
    /// [`Self::adjacency_tag`].
    pub fn new(commitment: &[u8; 32], lower: [u8; 32], upper: [u8; 32]) -> Self {
        let adjacency_tag = Self::adjacency_tag(commitment, &lower, &upper);
        Self {
            lower,
            upper,
            adjacency_tag,
        }
    }
}

/// Wire encoding for a [`WitnessedPredicateKind::NonMembership`] proof,
/// **v2** — the sorted-neighbor witness *plus* a real Merkle-adjacency STARK
/// proof that binds `lower`/`upper` to consecutive leaf indices under the
/// committed root.
///
/// This supersedes the bare 96-byte [`NonMembershipNeighborProof`] wire form,
/// whose commitment-keyed `adjacency_tag` was forgeable by anyone who knew the
/// public set commitment (the documented Silver gap). The `adjacency_proof`
/// bytes are opaque to the cell crate; they are checked by the host-installed
/// [`NeighborAdjacencyVerifier`] (a STARK in `dregg-circuit`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProofV2 {
    /// The sorted-neighbor witness (`lower < candidate < upper` + tag).
    pub neighbor: NonMembershipNeighborProof,
    /// Serialized Merkle-adjacency STARK proving `lower`/`upper` are
    /// consecutive leaves under the committed root.
    pub adjacency_proof: Vec<u8>,
}

impl NonMembershipProofV2 {
    /// Serialize to postcard wire bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("NonMembershipProofV2 serialization is infallible")
    }
    /// Deserialize from postcard wire bytes; `None` on malformed/empty input.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.is_empty() {
            return None;
        }
        postcard::from_bytes(bytes).ok()
    }
}

/// Real (Golden-Sound) verifier for [`WitnessedPredicateKind::NonMembership`].
///
/// Holds an optional host-installed [`NeighborAdjacencyVerifier`]. When present,
/// the verifier REQUIRES a [`NonMembershipProofV2`] carrying a Merkle-adjacency
/// STARK that binds `lower`/`upper` to consecutive leaf indices under the
/// committed root — closing the wide-bracket forge. When **absent**, it fails
/// closed (rejects every proof): the cell crate cannot verify the STARK itself,
/// and accepting the bare neighbor witness would re-open the forge.
#[derive(Clone, Default)]
pub struct SortedNeighborNonMembershipVerifier {
    adjacency: Option<Arc<dyn NeighborAdjacencyVerifier>>,
}

impl SortedNeighborNonMembershipVerifier {
    /// Construct the fail-closed verifier (no adjacency STARK installed).
    pub fn fail_closed() -> Self {
        Self { adjacency: None }
    }

    /// Construct with a host-installed adjacency STARK verifier (the
    /// production form; `dregg-turn` installs the `dregg-circuit`-backed one).
    pub fn with_adjacency(adjacency: Arc<dyn NeighborAdjacencyVerifier>) -> Self {
        Self {
            adjacency: Some(adjacency),
        }
    }
}

impl WitnessedPredicateVerifier for SortedNeighborNonMembershipVerifier {
    fn name(&self) -> &'static str {
        "sorted-neighbor-non-membership"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::NonMembership
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // Require the v2 wire form carrying a Merkle-adjacency STARK proof.
        let proof_v2 = NonMembershipProofV2::from_bytes(proof_bytes).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: format!(
                    "non-membership proof must be a postcard NonMembershipProofV2 \
                     (neighbor witness + Merkle-adjacency STARK); got {} bytes that did \
                     not decode",
                    proof_bytes.len()
                ),
            }
        })?;
        let proof = proof_v2.neighbor;
        // Resolve the candidate bytes from the input.
        let candidate: [u8; 32] = match input {
            PredicateInput::Slot(s) => **s,
            PredicateInput::Sender(s) => **s,
            PredicateInput::Bytes(b) => {
                if b.len() != 32 {
                    return Err(WitnessedPredicateError::InputShapeMismatch {
                        kind_name: "NonMembership",
                        expected: "32-byte candidate",
                        actual: "non-32-byte Bytes",
                    });
                }
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "NonMembership",
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "NonMembership",
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "SigningMessage",
                });
            }
        };
        // Enforce the per-(commitment, lower, upper) adjacency tag. This is
        // the first (cheap) gate: a prover who doesn't know the set's
        // `commitment` cannot reconstruct the tag (closes the legacy
        // public-`[0xFE;32]`-sentinel attack, AIR-soundness-audit finding #2).
        let expected =
            NonMembershipNeighborProof::adjacency_tag(commitment, &proof.lower, &proof.upper);
        if proof.adjacency_tag != expected {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: "adjacency_tag does not match BLAKE3_keyed(\"dregg-nonmembership-adjacency-v1\", commitment || lower || upper); the prover did not bind to this set's commitment".into(),
            });
        }
        // Enforce strict ordering: lower < candidate < upper.
        if proof.lower >= candidate {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: "lower neighbor is not strictly below the candidate (the candidate is on or below the lower bound)".into(),
            });
        }
        if candidate >= proof.upper {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: "candidate is not strictly below the upper neighbor (the candidate equals or exceeds the upper bound)".into(),
            });
        }
        // GOLDEN TEETH: require a real Merkle-adjacency STARK binding
        // `lower`/`upper` to CONSECUTIVE leaf indices under the committed root.
        // This closes the documented Silver wide-bracket forge: a prover who
        // knows the public `commitment` can no longer pick `lower=0x00…`,
        // `upper=0xFF…` — those are not adjacent leaves of the committed tree,
        // so no adjacency proof exists for them.
        //
        // FAIL CLOSED: if no adjacency verifier is installed (the cell crate
        // alone cannot run the STARK), reject. The host (`dregg-turn`) installs
        // the `dregg-circuit`-backed verifier via `register_builtin`.
        match &self.adjacency {
            Some(adj) => adj
                .verify_adjacency(
                    commitment,
                    &proof.lower,
                    &proof.upper,
                    &proof_v2.adjacency_proof,
                )
                .map_err(|reason| WitnessedPredicateError::Rejected {
                    kind_name: "NonMembership",
                    reason: format!(
                        "Merkle-adjacency STARK rejected (lower/upper are not consecutive \
                         leaves under the committed root): {reason}"
                    ),
                }),
            None => Err(WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: "no Merkle-adjacency verifier installed: this registry cannot soundly \
                         check that lower/upper are consecutive leaves of the committed set, so \
                         it fails closed. The host must register the dregg-circuit-backed \
                         SortedNeighborNonMembershipVerifier (see \
                         dregg_turn::executor::membership_verifier)."
                    .into(),
            }),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// BlindedSet: real (non-stub) credential-set membership verifier
// ─────────────────────────────────────────────────────────────────────

/// Wire encoding for a [`WitnessedPredicateKind::BlindedSet`] proof — a
/// cell-native credential-set membership / non-revocation witness.
///
/// # What a BlindedSet proof is
///
/// `WitnessedPredicateKind::BlindedSet` powers
/// `StateConstraint::SenderAuthorized { AuthorizedSet::CredentialSet { .. } }`
/// (the cross-app identity-attested tier; see
/// `cell::program::AuthorizedSet::CredentialSet`). The predicate's
/// `commitment` is the **stable (issuer, schema) tag**
/// `blake3_derive_key("dregg-credential-set-v1") || issuer_cell ||
/// credential_schema_id` — it identifies *which* issuer-cell/schema pair
/// gates the action, but it is **not** itself a member-set root.
///
/// The set of authorized holders is a *blinded* accumulator the issuer
/// publishes: the federation sees only its 32-byte Poseidon-style root.
/// A holder proves "I am in the issuer's authorized set for this schema
/// **and** I am not revoked" by exhibiting:
///
/// 1. `issuer_set_root` — the issuer's published membership-accumulator
///    root. The federation only ever sees the root (the "blinded" part).
/// 2. A Merkle membership path from the **hiding committed leaf**
///    `committed_leaf = H_keyed("dregg-credential-holder-commit-v1",
///    commitment || holder || holder_blinding)` up to `issuer_set_root`. The
///    leaf binds the holder pubkey **and** the (issuer, schema) commitment, so
///    a path valid under one (issuer, schema) is not valid under another, and a
///    path for holder A is not valid for holder B — yet because the leaf is a
///    *hiding commitment*, the issuer's tree (and any observer of the published
///    root or the proof) never sees the holder pubkey. The holder pubkey is in
///    NO public input. Anti-replay is enforced separately: the verifier
///    recomputes `committed_leaf` from the *presenting* sender's pubkey +
///    `holder_blinding`, so the proof only opens for the holder it was minted
///    for.
/// 3. `revocation_root` — the issuer's published non-revocation
///    accumulator root (sorted-leaf set of revoked *committed leaves*, same
///    hiding domain so non-revocation stays blind).
/// 4. A sorted-neighbor non-membership witness
///    ([`NonMembershipNeighborProof`]) proving `committed_leaf` is absent from
///    `revocation_root`.
/// 5. `binding_tag` — `H_keyed("dregg-credential-set-binding-v2",
///    commitment || committed_leaf || issuer_set_root || revocation_root)`.
///    This cryptographically welds the four **blind** public quantities
///    together so a proof cannot be transplanted across (issuer, schema) or
///    have its roots swapped — without exposing the holder.
///
/// # Verification (what the verifier actually checks)
///
/// The cell-side checks are closed-form hash recomputations (no `dregg-circuit`
/// dependency; cf. [`NotYetWiredVerifier`]); the issuer-root binding and
/// non-revocation adjacency STARK are delegated to host-installed traits. The
/// verifier:
///
/// - decodes the proof (rejects empty / malformed bytes),
/// - recomputes `committed_leaf` from the presenting `(commitment, sender,
///   holder_blinding)` and rejects unless it matches (anti-replay / transplant
///   defense, holder-blind),
/// - recomputes `binding_tag` from `(commitment, committed_leaf,
///   issuer_set_root, revocation_root)` and rejects on mismatch (transplant /
///   root-swap defense),
/// - walks `merkle_path` from `committed_leaf` to a root, rejecting unless it
///   equals `issuer_set_root` (membership),
/// - binds `issuer_set_root` / `revocation_root` to the issuer's real published
///   roots via the host-installed [`IssuerRootAuthority`] (rejecting
///   self-fabricated accumulators),
/// - verifies the sorted-neighbor non-membership of `committed_leaf` against
///   `revocation_root` (non-revocation).
///
/// The closed-form checks need no `dregg-circuit` dependency; the
/// [`IssuerRootAuthority`] and [`NeighborAdjacencyVerifier`] are host-installed
/// (the `dregg-turn` executor links the real implementations).
///
/// # Soundness statement (holder-blind + issuer-bound)
///
/// - **Holder anonymity (closed):** the holder pubkey appears in NO public
///   input. The tree leaf is a hiding commitment `committed_leaf`; the binding
///   tag covers `committed_leaf`, not the holder. An observer of the issuer's
///   published root or of the proof bytes cannot recover the holder. Anti-replay
///   is still enforced — the verifier recomputes `committed_leaf` from the
///   presenting sender + blinding, so the proof only opens for the holder it was
///   minted for.
/// - **Issuer-root binding (closed):** the prover-supplied `issuer_set_root` /
///   `revocation_root` are checked against the issuer's REAL published roots via
///   the host-installed [`IssuerRootAuthority`]. A prover who fabricates their
///   own one-leaf accumulator (and an empty revocation set) to self-attest is
///   rejected, because their root is not the issuer's. When no authority is
///   installed the verifier **fails closed** (rejects every proof).
/// - **Also closed:** empty/garbage proofs, wrong-holder transplant (the leaf
///   commitment does not open under another holder), cross-(issuer,schema)
///   replay (the leaf and tag bind `commitment`), revoked holders
///   (non-revocation neighbor witness over `committed_leaf` + adjacency STARK),
///   and root-swap (the binding tag covers both roots).
/// - **Open (the residual Golden gap):** the [`IssuerRootAuthority`] equates the
///   roots to a host-trusted registry/snapshot; it does not (yet) carry a STARK
///   proving the roots are reads of the issuer cell's state at the turn's state
///   root. The Golden lift replaces the authority's equality check with that
///   in-circuit state-read proof.
///
/// # Versioning
///
/// The keyed-derive domains `dregg-credential-holder-commit-v1`,
/// `dregg-credential-merkle-v1`, and `dregg-credential-set-binding-v2`
/// are versioned wire formats; the `-v2` binding domain (and the
/// holder-commit leaf) supersede the prior raw-holder `-v1` scheme,
/// making the holder-blinding cut-over unambiguous.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CredentialSetMembershipProof {
    /// The **hiding commitment** to the holder that is the membership-tree
    /// leaf: `committed_leaf = H_keyed("dregg-credential-holder-commit-v1",
    /// commitment || holder || holder_blinding)`. The issuer's tree and every
    /// observer of the proof see only this commitment — never the raw holder
    /// pubkey — so the holder is anonymous against the issuer's published
    /// accumulator. The Merkle path is over `committed_leaf`, and the binding
    /// tag covers `committed_leaf` (NOT the holder), so the holder pubkey never
    /// enters the proof's public inputs.
    pub committed_leaf: [u8; 32],
    /// The blinding factor opening `committed_leaf` to the presenting holder.
    /// The verifier recomputes `committed_leaf` from `(commitment, sender,
    /// holder_blinding)` to bind the proof to *this* presenter (anti-replay),
    /// while the blinding keeps the leaf hiding in the issuer's tree.
    pub holder_blinding: [u8; 32],
    /// The issuer's published membership-accumulator root (blinded set).
    pub issuer_set_root: [u8; 32],
    /// The issuer's published non-revocation accumulator root.
    pub revocation_root: [u8; 32],
    /// Merkle path from the holder leaf to `issuer_set_root`. Each entry
    /// is `(sibling, holder_is_right_child)`: when `is_right` is true the
    /// running hash is the *right* child and `sibling` the left, else the
    /// running hash is the left child.
    pub merkle_path: Vec<(([u8; 32]), bool)>,
    /// Sorted-neighbor non-membership witness proving `holder` is absent
    /// from `revocation_root`.
    pub non_revocation: NonMembershipNeighborProof,
    /// Serialized Merkle-adjacency STARK proving the non-revocation neighbors
    /// (`non_revocation.lower`/`.upper`) are CONSECUTIVE leaves under
    /// `revocation_root`. Without this, the non-revocation leg is forgeable by
    /// anyone who knows `revocation_root` (the documented Silver gap). Checked
    /// by the host-installed [`NeighborAdjacencyVerifier`].
    #[serde(default)]
    pub revocation_adjacency_proof: Vec<u8>,
    /// Keyed binding tag over (commitment, holder, issuer_set_root,
    /// revocation_root). Reconstruct via [`Self::binding_tag`].
    pub binding_tag: [u8; 32],
}

impl CredentialSetMembershipProof {
    /// Compute the **hiding** holder-commitment leaf for the membership
    /// accumulator.
    ///
    /// `leaf = H_keyed("dregg-credential-holder-commit-v1", commitment ||
    /// holder || holder_blinding)`. Binding the leaf to the (issuer, schema)
    /// `commitment` and the `holder` pubkey keeps a membership path
    /// non-transplantable across holders and across (issuer, schema) pairs; the
    /// `holder_blinding` makes the commitment **hiding**, so the issuer's tree
    /// (and any observer of the published root) cannot link the leaf back to the
    /// holder. This is the holder-anonymity primitive: the leaf in the tree is a
    /// commitment, not the holder itself.
    pub fn holder_commit_leaf(
        commitment: &[u8; 32],
        holder: &[u8; 32],
        holder_blinding: &[u8; 32],
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-credential-holder-commit-v1");
        h.update(commitment);
        h.update(holder);
        h.update(holder_blinding);
        *h.finalize().as_bytes()
    }

    /// Combine two Merkle children into their parent hash (domain-keyed).
    fn merkle_parent(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-credential-merkle-v1");
        h.update(left);
        h.update(right);
        *h.finalize().as_bytes()
    }

    /// Walk `merkle_path` from `leaf` to the root it implies.
    pub fn merkle_root_from_path(leaf: [u8; 32], path: &[([u8; 32], bool)]) -> [u8; 32] {
        let mut acc = leaf;
        for (sibling, is_right) in path {
            acc = if *is_right {
                // acc is the right child, sibling is the left.
                Self::merkle_parent(sibling, &acc)
            } else {
                Self::merkle_parent(&acc, sibling)
            };
        }
        acc
    }

    /// Compute the canonical binding tag.
    ///
    /// `tag = H_keyed("dregg-credential-set-binding-v2", commitment ||
    /// committed_leaf || issuer_set_root || revocation_root)`. Welds the four
    /// **blind** public quantities so the proof cannot be transplanted across
    /// (issuer, schema) or have its roots swapped — WITHOUT placing the holder
    /// pubkey in the tag. The holder is bound transitively through
    /// `committed_leaf` (the hiding commitment), so holder anonymity is
    /// preserved while transplant resistance is retained.
    ///
    /// The `-v2` domain differs from the prior `-v1` (which committed the raw
    /// holder); the version bump makes the holder-blinding cut-over
    /// unambiguous.
    pub fn binding_tag(
        commitment: &[u8; 32],
        committed_leaf: &[u8; 32],
        issuer_set_root: &[u8; 32],
        revocation_root: &[u8; 32],
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-credential-set-binding-v2");
        h.update(commitment);
        h.update(committed_leaf);
        h.update(issuer_set_root);
        h.update(revocation_root);
        *h.finalize().as_bytes()
    }

    /// Serialize to postcard wire bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self)
            .expect("CredentialSetMembershipProof serialization is infallible")
    }

    /// Deserialize from postcard wire bytes. Returns `None` on malformed
    /// input (including empty bytes).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.is_empty() {
            return None;
        }
        postcard::from_bytes(bytes).ok()
    }

    /// Construct a well-formed honest **holder-blinded** proof for a holder
    /// against a known issuer membership accumulator. Prover-side helper.
    ///
    /// - `commitment`: the (issuer, schema) tag
    ///   ([`crate::program::AuthorizedSet::credential_set_commitment`]).
    /// - `holder`: the holder pubkey (the `InputRef::Sender` value). It is
    ///   **never placed in the proof** — only its hiding commitment is.
    /// - `holder_blinding`: the per-credential blinding that makes the leaf
    ///   commitment hiding (the issuer assigns this when minting the leaf).
    /// - `merkle_path`: the membership path from the committed-leaf up to the
    ///   issuer's accumulator root.
    /// - `revocation_root`: the issuer's published revocation root (a sorted
    ///   set of revoked *committed leaves*, mirroring the membership domain so
    ///   non-revocation stays blind).
    /// - `rev_lower`/`rev_upper`: the sorted-set neighbors bracketing this
    ///   credential's `committed_leaf` in the revocation set (witnessing
    ///   non-revocation without revealing the holder).
    ///
    /// The `committed_leaf`, `issuer_set_root`, and `binding_tag` are derived so
    /// the result verifies under [`CredentialSetMembershipVerifier`] (given a
    /// matching [`IssuerRootAuthority`] and [`NeighborAdjacencyVerifier`]).
    /// `revocation_adjacency_proof` carries the Merkle-adjacency STARK proving
    /// `rev_lower`/`rev_upper` are consecutive leaves under `revocation_root`.
    /// Pass an empty vec only for tests exercising the fail-closed path.
    pub fn new(
        commitment: &[u8; 32],
        holder: &[u8; 32],
        holder_blinding: &[u8; 32],
        merkle_path: Vec<([u8; 32], bool)>,
        revocation_root: [u8; 32],
        rev_lower: [u8; 32],
        rev_upper: [u8; 32],
        revocation_adjacency_proof: Vec<u8>,
    ) -> Self {
        let committed_leaf = Self::holder_commit_leaf(commitment, holder, holder_blinding);
        let issuer_set_root = Self::merkle_root_from_path(committed_leaf, &merkle_path);
        let non_revocation =
            NonMembershipNeighborProof::new(&revocation_root, rev_lower, rev_upper);
        let binding_tag = Self::binding_tag(
            commitment,
            &committed_leaf,
            &issuer_set_root,
            &revocation_root,
        );
        Self {
            committed_leaf,
            holder_blinding: *holder_blinding,
            issuer_set_root,
            revocation_root,
            merkle_path,
            non_revocation,
            revocation_adjacency_proof,
            binding_tag,
        }
    }
}

/// Real verifier for [`WitnessedPredicateKind::BlindedSet`] credential-set
/// membership proofs. See [`CredentialSetMembershipProof`] for the full
/// soundness contract.
///
/// Holds an optional host-installed [`NeighborAdjacencyVerifier`]. The
/// non-revocation leg REQUIRES a Merkle-adjacency STARK (consecutive revocation
/// neighbors under `revocation_root`); without an installed verifier it fails
/// closed, exactly like [`SortedNeighborNonMembershipVerifier`].
#[derive(Clone, Default)]
pub struct CredentialSetMembershipVerifier {
    adjacency: Option<Arc<dyn NeighborAdjacencyVerifier>>,
    issuer_roots: Option<Arc<dyn IssuerRootAuthority>>,
}

impl CredentialSetMembershipVerifier {
    /// Construct the fail-closed verifier (no adjacency STARK / issuer-root
    /// authority installed). Rejects every proof.
    pub fn fail_closed() -> Self {
        Self {
            adjacency: None,
            issuer_roots: None,
        }
    }

    /// Construct with a host-installed adjacency STARK verifier. The
    /// issuer-root authority is still absent, so this still fails closed on the
    /// issuer-root-binding step (use [`Self::production`] for the full wiring).
    pub fn with_adjacency(adjacency: Arc<dyn NeighborAdjacencyVerifier>) -> Self {
        Self {
            adjacency: Some(adjacency),
            issuer_roots: None,
        }
    }

    /// Construct with a host-installed [`IssuerRootAuthority`] (binds the
    /// prover-supplied roots to the issuer's real published roots) but no
    /// adjacency verifier — fails closed at the non-revocation adjacency step.
    pub fn with_issuer_roots(issuer_roots: Arc<dyn IssuerRootAuthority>) -> Self {
        Self {
            adjacency: None,
            issuer_roots: Some(issuer_roots),
        }
    }

    /// Construct the **production** verifier: both the adjacency STARK verifier
    /// AND the issuer-root authority installed. Only this configuration can
    /// soundly ACCEPT a proof (the others fail closed on a missing leg).
    pub fn production(
        adjacency: Arc<dyn NeighborAdjacencyVerifier>,
        issuer_roots: Arc<dyn IssuerRootAuthority>,
    ) -> Self {
        Self {
            adjacency: Some(adjacency),
            issuer_roots: Some(issuer_roots),
        }
    }
}

impl WitnessedPredicateVerifier for CredentialSetMembershipVerifier {
    fn name(&self) -> &'static str {
        "credential-set-membership"
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
        // Resolve the holder (sender) bytes from the input. The credential
        // gate binds the credential to the *holder* presenting it.
        let holder: [u8; 32] = match input {
            PredicateInput::Sender(s) => **s,
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) => {
                if b.len() != 32 {
                    return Err(WitnessedPredicateError::InputShapeMismatch {
                        kind_name: "BlindedSet",
                        expected: "32-byte holder",
                        actual: "non-32-byte Bytes",
                    });
                }
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "BlindedSet",
                    expected: "Sender/Slot/Bytes (32-byte holder)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "BlindedSet",
                    expected: "Sender/Slot/Bytes (32-byte holder)",
                    actual: "SigningMessage",
                });
            }
        };

        // Decode the proof; reject empty / malformed bytes. This is the
        // line that closes the prior playground bypass (a 1-byte garbage
        // "proof" no longer parses).
        let proof = CredentialSetMembershipProof::from_bytes(proof_bytes).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: format!(
                    "credential-set membership proof must be a non-empty postcard \
                     CredentialSetMembershipProof; got {} bytes that did not decode",
                    proof_bytes.len()
                ),
            }
        })?;

        // 1. Holder binding (anti-replay) WITHOUT revealing the holder in the
        //    proof's public inputs. The verifier recomputes the hiding leaf
        //    commitment from (commitment, sender, holder_blinding) and checks
        //    it equals the proof's `committed_leaf`. This binds the proof to
        //    *this* presenter — a proof minted for holder A does not open under
        //    holder B's pubkey — while the leaf carried in the proof / the
        //    issuer's tree is a hiding commitment, never the holder pubkey. The
        //    holder pubkey appears in NO public input (binding tag, leaf, PI).
        let recomputed_leaf = CredentialSetMembershipProof::holder_commit_leaf(
            commitment,
            &holder,
            &proof.holder_blinding,
        );
        if recomputed_leaf != proof.committed_leaf {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "committed_leaf does not open to the presenting holder under \
                         H_keyed(\"dregg-credential-holder-commit-v1\", commitment || holder || \
                         holder_blinding); the proof was minted for a different holder (transplant \
                         rejected)"
                    .into(),
            });
        }

        // 2. Binding tag: weld (commitment, committed_leaf, issuer_set_root,
        //    revocation_root) — BLIND quantities only. Rejects transplant
        //    across (issuer, schema) and root-swap, without the holder pubkey.
        let expected_tag = CredentialSetMembershipProof::binding_tag(
            commitment,
            &proof.committed_leaf,
            &proof.issuer_set_root,
            &proof.revocation_root,
        );
        if proof.binding_tag != expected_tag {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "binding_tag does not match H_keyed(\"dregg-credential-set-binding-v2\", \
                         commitment || committed_leaf || issuer_set_root || revocation_root); the \
                         proof is not bound to this (issuer, schema) commitment + leaf + roots"
                    .into(),
            });
        }

        // 3. Membership: walk the Merkle path from the committed leaf; it must
        //    reach the issuer's published set root.
        let reached = CredentialSetMembershipProof::merkle_root_from_path(
            proof.committed_leaf,
            &proof.merkle_path,
        );
        if reached != proof.issuer_set_root {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "Merkle membership path does not reconstruct issuer_set_root from the \
                         committed leaf; the holder is not provably in the issuer's authorized set"
                    .into(),
            });
        }

        // 4. ISSUER-ROOT BINDING: the prover-supplied issuer_set_root /
        //    revocation_root must be the issuer's REAL published roots for this
        //    (issuer, schema) commitment. Without this, a prover can fabricate
        //    their own one-leaf accumulator and self-attest (the membership
        //    path is self-consistent for any root). Fail closed when no
        //    authority is installed — the cell crate has no channel to the
        //    issuer cell's on-chain state, so it cannot soundly distinguish an
        //    honest member from a self-fabricator.
        match &self.issuer_roots {
            Some(authority) => authority
                .verify_issuer_roots(commitment, &proof.issuer_set_root, &proof.revocation_root)
                .map_err(|reason| WitnessedPredicateError::Rejected {
                    kind_name: "BlindedSet",
                    reason: format!(
                        "issuer-root binding failed (prover-supplied accumulator is not the \
                         issuer's published set): {reason}"
                    ),
                })?,
            None => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: "BlindedSet",
                    reason: "no issuer-root authority installed: this registry cannot bind the \
                             prover-supplied roots to the issuer's real published roots, so it \
                             fails closed (a self-fabricated accumulator would otherwise be \
                             accepted). The host must register a CredentialSetMembershipVerifier \
                             with an IssuerRootAuthority (see \
                             dregg_turn::executor::membership_verifier)."
                        .into(),
                });
            }
        }

        // 5. Non-revocation: the holder's COMMITTED LEAF must be absent from
        //    the issuer's revocation accumulator (a sorted set of revoked
        //    committed leaves — same domain, so non-revocation stays blind).
        //    Reuse the sorted-neighbor algebra, verifying against
        //    `revocation_root` and bracketing `committed_leaf`.
        let leaf_key = proof.committed_leaf;
        let nr = &proof.non_revocation;
        let expected_adj =
            NonMembershipNeighborProof::adjacency_tag(&proof.revocation_root, &nr.lower, &nr.upper);
        if nr.adjacency_tag != expected_adj {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "non_revocation.adjacency_tag is not bound to revocation_root; \
                         the non-revocation witness is not anchored to the issuer's revocation set"
                    .into(),
            });
        }
        if nr.lower >= leaf_key {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "non-revocation lower neighbor is not strictly below the committed leaf \
                         (the holder may be revoked)"
                    .into(),
            });
        }
        if leaf_key >= nr.upper {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "committed leaf is not strictly below the non-revocation upper neighbor \
                         (the holder may be revoked)"
                    .into(),
            });
        }

        // 6. GOLDEN TEETH: require a real Merkle-adjacency STARK binding the
        //    non-revocation neighbors to CONSECUTIVE leaf indices under
        //    `revocation_root`. Without this, a holder who knows
        //    `revocation_root` could pick wide-bracket sentinels and forge
        //    non-revocation. Fail closed when no adjacency verifier is
        //    installed (the cell crate cannot run the STARK itself).
        match &self.adjacency {
            Some(adj) => adj
                .verify_adjacency(
                    &proof.revocation_root,
                    &nr.lower,
                    &nr.upper,
                    &proof.revocation_adjacency_proof,
                )
                .map_err(|reason| WitnessedPredicateError::Rejected {
                    kind_name: "BlindedSet",
                    reason: format!(
                        "non-revocation Merkle-adjacency STARK rejected (revocation neighbors \
                         are not consecutive leaves under revocation_root): {reason}"
                    ),
                }),
            None => Err(WitnessedPredicateError::Rejected {
                kind_name: "BlindedSet",
                reason: "no Merkle-adjacency verifier installed: this registry cannot soundly \
                         check non-revocation neighbor adjacency, so it fails closed. The host \
                         must register the dregg-circuit-backed CredentialSetMembershipVerifier \
                         (see dregg_turn::executor::membership_verifier)."
                    .into(),
            }),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructors_produce_expected_shape() {
        let wp = WitnessedPredicate::dfa([1u8; 32], InputRef::Witness { index: 0 }, 1);
        assert_eq!(wp.kind, WitnessedPredicateKind::Dfa);
        assert_eq!(wp.commitment, [1u8; 32]);
        assert_eq!(wp.proof_witness_index, 1);
        assert!(matches!(wp.input_ref, InputRef::Witness { index: 0 }));
    }

    #[test]
    fn registry_empty_yields_kind_not_registered() {
        let reg = WitnessedPredicateRegistry::empty();
        let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Witness { index: 0 }, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Bytes(b"input"), b"proof")
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessedPredicateError::KindNotRegistered {
                kind: WitnessedPredicateKind::Dfa
            }
        ));
    }

    #[test]
    fn stub_registry_accepts_non_empty_proof_for_each_builtin() {
        let reg = WitnessedPredicateRegistry::with_stubs();
        // Note: BlindedSet and NonMembership are NOT in this loop — even
        // under `with_stubs` they install REAL (Silver-Sound) verifiers
        // that reject opaque `b"proof"` bytes. Their accept/reject
        // behavior is exercised by their dedicated test sections.
        for wp in [
            WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::temporal([0u8; 32], 0, 0),
            WitnessedPredicate::merkle_membership([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::bridge_predicate(
                [0u8; 32],
                InputRef::PublicInput { pi_index: 0 },
                0,
            ),
            WitnessedPredicate::pedersen_equality([0u8; 32], InputRef::Slot { index: 0 }, 0),
        ] {
            let dummy_pk = [0u8; 32];
            let input = PredicateInput::Sender(&dummy_pk);
            reg.verify(&wp, &input, b"proof").unwrap_or_else(|e| {
                panic!(
                    "stub verifier should accept non-empty proof for {:?}: {e}",
                    wp.kind
                )
            });
        }
    }

    #[test]
    fn stub_registry_rejects_empty_proof() {
        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
        let dummy_pk = [0u8; 32];
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&dummy_pk), b"")
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn custom_kind_routes_through_custom_registry() {
        struct AcceptAll;
        impl WitnessedPredicateVerifier for AcceptAll {
            fn name(&self) -> &'static str {
                "accept-all"
            }
            fn kind(&self) -> WitnessedPredicateKind {
                WitnessedPredicateKind::Custom { vk_hash: [7u8; 32] }
            }
            fn verify(
                &self,
                _commitment: &[u8; 32],
                _input: &PredicateInput<'_>,
                _proof_bytes: &[u8],
            ) -> Result<(), WitnessedPredicateError> {
                Ok(())
            }
        }

        let mut reg = WitnessedPredicateRegistry::empty();
        reg.register_custom([7u8; 32], Arc::new(AcceptAll));

        let wp = WitnessedPredicate::custom([7u8; 32], [0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        reg.verify(&wp, &PredicateInput::Sender(&pk), b"")
            .expect("custom kind dispatch should succeed");
    }

    #[test]
    fn custom_kind_unregistered_vk_hash_yields_kind_not_registered() {
        let reg = WitnessedPredicateRegistry::empty();
        let wp = WitnessedPredicate::custom([99u8; 32], [0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"proof")
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessedPredicateError::KindNotRegistered {
                kind: WitnessedPredicateKind::Custom { .. }
            }
        ));
    }

    #[test]
    fn witnessed_predicate_roundtrips_serde() {
        let wp = WitnessedPredicate::temporal([42u8; 32], 3, 7);
        let bytes = postcard::to_allocvec(&wp).expect("serialize");
        let back: WitnessedPredicate = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(back, wp);
    }

    #[test]
    fn input_ref_variants_roundtrip_serde() {
        for ir in [
            InputRef::Slot { index: 4 },
            InputRef::Witness { index: 9 },
            InputRef::PublicInput { pi_index: 2 },
            InputRef::Sender,
            InputRef::SigningMessage,
        ] {
            let bytes = postcard::to_allocvec(&ir).expect("serialize");
            let back: InputRef = postcard::from_bytes(&bytes).expect("deserialize");
            assert_eq!(back, ir);
        }
    }

    // ─── Canonical predicate VK tests (VK-AS-RE-EXECUTION-RECIPE.md §2.2)

    #[test]
    fn canonical_predicate_vk_is_deterministic() {
        let bytes = b"some-dsl-ast-bytes";
        let h1 = canonical_predicate_vk(bytes);
        let h2 = canonical_predicate_vk(bytes);
        assert_eq!(h1, h2);
    }

    #[test]
    fn canonical_predicate_vk_differs_for_different_inputs() {
        let h1 = canonical_predicate_vk(b"predicate-a");
        let h2 = canonical_predicate_vk(b"predicate-b");
        assert_ne!(h1, h2);
    }

    #[test]
    fn canonical_predicate_vk_distinguishes_empty_from_other() {
        // Empty bytes must hash to something distinct from any non-empty
        // input (the length prefix achieves this regardless of BLAKE3's
        // own collision resistance).
        let empty = canonical_predicate_vk(b"");
        let non_empty = canonical_predicate_vk(b"\x00");
        assert_ne!(empty, non_empty);
    }

    #[test]
    fn canonical_predicate_vk_length_prefix_disambiguates_concatenation() {
        // Without the length prefix, `concat(a, b)` could collide with
        // alternative splits. With the prefix, distinct splits hash
        // distinctly.
        let h1 = canonical_predicate_vk(b"ab");
        let h2 = canonical_predicate_vk(b"abc");
        let h3 = canonical_predicate_vk(b"abcd");
        assert_ne!(h1, h2);
        assert_ne!(h2, h3);
        assert_ne!(h1, h3);
    }

    #[test]
    fn canonical_predicate_vk_keyed_domain_independence() {
        // The same opaque bytes used at different layers produce
        // distinct hashes because of the BLAKE3 keyed-derive domain.
        // We can't test this against `canonical_program_vk` here (it
        // takes a `CellProgram`, not bytes), but we can confirm the
        // predicate-VK hash is *not* equal to a vanilla BLAKE3 of the
        // same bytes — the domain key must be in play.
        let bytes = b"hello-world";
        let predicate_vk = canonical_predicate_vk(bytes);
        let raw = *blake3::hash(bytes).as_bytes();
        assert_ne!(predicate_vk, raw);
    }

    #[test]
    fn kind_variants_roundtrip_serde_including_custom() {
        for k in [
            WitnessedPredicateKind::Dfa,
            WitnessedPredicateKind::Temporal,
            WitnessedPredicateKind::MerkleMembership,
            WitnessedPredicateKind::NonMembership,
            WitnessedPredicateKind::BlindedSet,
            WitnessedPredicateKind::BridgePredicate,
            WitnessedPredicateKind::PedersenEquality,
            WitnessedPredicateKind::Custom { vk_hash: [9u8; 32] },
        ] {
            let bytes = postcard::to_allocvec(&k).expect("serialize");
            let back: WitnessedPredicateKind = postcard::from_bytes(&bytes).expect("deserialize");
            assert_eq!(back, k);
        }
    }

    // ─── NonMembership / Renunciation tests (Tier 2 §3.2 / §9.2.1) ───────

    /// Canonical set-commitment used in NonMembership tests.
    const SET_COMMITMENT: [u8; 32] = [0xAB; 32];

    /// A mock adjacency verifier for cell-side unit tests. The REAL adjacency
    /// STARK lives in `dregg-circuit` / `dregg-turn`; here we only need to
    /// exercise the cell verifier's plumbing (structural checks + the
    /// install/fail-closed branch). The mock accepts iff `adjacency_proof ==
    /// b"ADJ-OK"` and `lower < upper`, modelling "consecutive under root."
    struct MockAdjacency;
    impl NeighborAdjacencyVerifier for MockAdjacency {
        fn verify_adjacency(
            &self,
            _root: &[u8; 32],
            lower: &[u8; 32],
            upper: &[u8; 32],
            adjacency_proof: &[u8],
        ) -> Result<(), String> {
            if adjacency_proof != b"ADJ-OK" {
                return Err("mock: missing/invalid adjacency proof".into());
            }
            if lower >= upper {
                return Err("mock: lower !< upper".into());
            }
            Ok(())
        }
    }

    /// A registry whose NonMembership/BlindedSet verifiers have the mock
    /// adjacency verifier installed (mirrors the production turn-layer wiring).
    fn registry_with_mock_adjacency() -> WitnessedPredicateRegistry {
        let mut r = WitnessedPredicateRegistry::with_stubs();
        let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(MockAdjacency);
        r.register_builtin(Arc::new(
            SortedNeighborNonMembershipVerifier::with_adjacency(adj.clone()),
        ));
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::with_adjacency(
            adj,
        )));
        r
    }

    /// Build a v2 non-membership proof carrying the mock-accepted adjacency
    /// blob `b"ADJ-OK"`.
    fn honest_renunciation_v2(lower: [u8; 32], upper: [u8; 32]) -> Vec<u8> {
        NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(&SET_COMMITMENT, lower, upper),
            adjacency_proof: b"ADJ-OK".to_vec(),
        }
        .to_bytes()
    }

    #[test]
    fn non_membership_accepts_legal_renunciation() {
        // Candidate 0x05 falls in (0x04, 0x06); honest witness + adjacency
        // proof accepts when the adjacency verifier is installed.
        let candidate = [0x05u8; 32];
        let bytes = honest_renunciation_v2([0x04u8; 32], [0x06u8; 32]);

        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        reg.verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .expect("legal renunciation should verify");
    }

    #[test]
    fn non_membership_fails_closed_without_adjacency_verifier() {
        // Same honest proof, but the default (cell-only) registry has NO
        // adjacency verifier installed → fail closed.
        let candidate = [0x05u8; 32];
        let bytes = honest_renunciation_v2([0x04u8; 32], [0x06u8; 32]);
        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => {
                assert!(
                    reason.contains("no Merkle-adjacency verifier installed"),
                    "{reason}"
                )
            }
            other => panic!("expected fail-closed Rejected, got {other:?}"),
        }
    }

    #[test]
    fn non_membership_rejects_candidate_equal_to_lower_neighbor() {
        // Candidate == lower neighbor → candidate IS in set → renunciation
        // must reject (the prover IS in the set but claims non-membership).
        let candidate = [0x05u8; 32];
        let bytes = honest_renunciation_v2([0x05u8; 32], [0x06u8; 32]);

        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_candidate_equal_to_upper_neighbor() {
        let candidate = [0x05u8; 32];
        let bytes = honest_renunciation_v2([0x04u8; 32], [0x05u8; 32]);

        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_out_of_interval_candidate() {
        // Candidate above the upper neighbor: out-of-interval.
        let candidate = [0x09u8; 32];
        let bytes = honest_renunciation_v2([0x04u8; 32], [0x06u8; 32]);

        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_forged_zero_adjacency_tag() {
        // Even if lower < candidate < upper and adjacency installed, a forged
        // commitment-keyed adjacency_tag breaks the cheap binding gate.
        let candidate = [0x05u8; 32];
        let mut neighbor =
            NonMembershipNeighborProof::new(&SET_COMMITMENT, [0x04u8; 32], [0x06u8; 32]);
        neighbor.adjacency_tag = [0u8; 32]; // forged
        let bytes = NonMembershipProofV2 {
            neighbor,
            adjacency_proof: b"ADJ-OK".to_vec(),
        }
        .to_bytes();
        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_missing_adjacency_proof() {
        // Valid neighbor witness but the adjacency proof blob is absent/invalid:
        // the installed adjacency verifier rejects. THE FORGE-CLOSE: a prover
        // who knows the commitment can recompute the tag but cannot supply a
        // real consecutive-index adjacency proof.
        let candidate = [0x42u8; 32];
        let bytes = NonMembershipProofV2 {
            // Wide bracket: knows the commitment, picks 0x00…/0xFF…
            neighbor: NonMembershipNeighborProof::new(&SET_COMMITMENT, [0x00u8; 32], [0xFFu8; 32]),
            adjacency_proof: Vec::new(), // no adjacency proof
        }
        .to_bytes();
        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "wide-bracket forge without a real adjacency proof must reject; got {err:?}"
        );
    }

    #[test]
    fn non_membership_rejects_malformed_proof_bytes() {
        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let pk = [0u8; 32];
        // Wrong length:
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"short")
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_proof_roundtrips_bytes() {
        let p = NonMembershipNeighborProof::new(&SET_COMMITMENT, [1u8; 32], [3u8; 32]);
        let bytes = p.to_bytes();
        let back = NonMembershipNeighborProof::from_bytes(&bytes).unwrap();
        assert_eq!(back, p);
    }

    // ─── AIR-soundness-audit (ce1e2def) finding #2 adversarial tests ───
    //
    // The prior public-sentinel attack: pick lower=0x00…, upper=0xFF…,
    // adjacency_tag=0xFE…, "prove" non-membership in an arbitrary set
    // without knowing the set's commitment. Today the adjacency_tag is
    // derived from BLAKE3_keyed("dregg-nonmembership-adjacency-v1",
    // commitment || lower || upper), so a prover who doesn't know the
    // commitment cannot reconstruct the tag.

    #[test]
    fn audit_attack_non_membership_rejects_legacy_public_sentinel() {
        // The pre-audit attack: pick wide-bracket neighbors and the public
        // sentinel [0xFE; 32]. The verifier rejects because the sentinel does
        // not match the per-commitment adjacency_tag derivation (and the bare
        // 96-byte form no longer parses as a v2 proof anyway).
        let candidate = [0x42u8; 32];
        let neighbor = NonMembershipNeighborProof {
            lower: [0x00u8; 32],
            upper: [0xFFu8; 32],
            adjacency_tag: [0xFEu8; 32], // the prior public constant
        };
        let bytes = NonMembershipProofV2 {
            neighbor,
            adjacency_proof: b"ADJ-OK".to_vec(),
        }
        .to_bytes();
        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "pre-audit sentinel attack must reject; got {err:?}"
        );
    }

    #[test]
    fn audit_attack_non_membership_rejects_wrong_commitment_keyed_tag() {
        // An attacker constructs a *well-formed* tag against a different
        // commitment, then submits the proof against `SET_COMMITMENT`. The
        // verifier recomputes the tag against the declared commitment and
        // rejects.
        let candidate = [0x42u8; 32];
        let wrong_commitment = [0xCCu8; 32];
        let bytes = NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(
                &wrong_commitment,
                [0x00u8; 32],
                [0xFFu8; 32],
            ),
            adjacency_proof: b"ADJ-OK".to_vec(),
        }
        .to_bytes();
        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "wrong-commitment tag attack must reject; got {err:?}"
        );
    }

    /// FORGE CLOSED (fail-before / pass-after): a prover who knows the public
    /// set commitment picks a wide bracket (lower=0x00…, upper=0xFF…) and
    /// recomputes a valid commitment-keyed `adjacency_tag`. Pre-fix, the
    /// Silver verifier ACCEPTED this for any candidate. Now the verifier
    /// REQUIRES a Merkle-adjacency STARK proving lower/upper are consecutive
    /// leaves — and 0x00…/0xFF… are not adjacent leaves of any real set, so the
    /// installed (mock here, STARK in production) adjacency verifier REJECTS.
    #[test]
    fn audit_forge_wide_bracket_now_rejected_by_adjacency() {
        let candidate = [0x42u8; 32];
        // Attacker knows SET_COMMITMENT (public); recomputes a valid tag, but
        // cannot supply a real consecutive-index adjacency proof.
        let bytes = NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(&SET_COMMITMENT, [0x00u8; 32], [0xFFu8; 32]),
            adjacency_proof: Vec::new(), // no real adjacency proof exists
        }
        .to_bytes();
        let reg = registry_with_mock_adjacency();
        let wp = WitnessedPredicate::non_membership(SET_COMMITMENT, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "wide-bracket forge must now be REJECTED by the adjacency requirement; got {err:?}"
        );
    }

    // ─── WitnessProducer — left adjoint of WitnessedPredicateVerifier ──
    // CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.4 + §4.1 + §9.1.4.

    #[test]
    fn producer_registry_empty_yields_kind_not_registered() {
        let reg = WitnessProducerRegistry::empty();
        let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        let err = reg
            .produce(&wp, &PredicateInput::Sender(&pk), b"witness")
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessProducerError::KindNotRegistered {
                kind: WitnessedPredicateKind::Dfa
            }
        ));
    }

    #[test]
    fn producer_stub_round_trip_verifier_accepts() {
        // Unit-counit identity: produce(input, witness) -> proof_bytes;
        // verify(proof_bytes) accepts. Walks every built-in kind.
        let producers = WitnessProducerRegistry::with_stubs();
        let verifiers = WitnessedPredicateRegistry::with_stubs();
        // BlindedSet is excluded: its real verifier requires a structured
        // CredentialSetMembershipProof, not the stub producer's opaque
        // length-prefixed blob. Its round-trip is covered by
        // `blinded_set_accepts_honest_membership_proof`.
        for wp in [
            WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::temporal([0u8; 32], 0, 0),
            WitnessedPredicate::merkle_membership([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::bridge_predicate(
                [0u8; 32],
                InputRef::PublicInput { pi_index: 0 },
                0,
            ),
            WitnessedPredicate::pedersen_equality([0u8; 32], InputRef::Slot { index: 0 }, 0),
        ] {
            let pk = [0u8; 32];
            let input = PredicateInput::Sender(&pk);
            let proof_bytes = producers
                .produce(&wp, &input, b"witness-bytes")
                .expect("producer succeeds for builtin stub");
            assert!(!proof_bytes.is_empty(), "produced bytes non-empty");
            verifiers
                .verify(&wp, &input, &proof_bytes)
                .unwrap_or_else(|e| {
                    panic!(
                        "round-trip: producer output should verify for {:?}: {e}",
                        wp.kind
                    )
                });
        }
    }

    #[test]
    fn producer_tampered_witness_still_verifies_under_stubs_but_distinct() {
        // The stub verifier accepts any non-empty bytes; the unit-
        // counit identity holds *and* the produced bytes for distinct
        // inputs are themselves distinct (so a real verifier could
        // distinguish). We assert the latter (the stub itself can't
        // reject a tampered witness — that's the real verifier's job).
        let producers = WitnessProducerRegistry::with_stubs();
        let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        let a = producers
            .produce(&wp, &PredicateInput::Sender(&pk), b"witness-a")
            .unwrap();
        let b = producers
            .produce(&wp, &PredicateInput::Sender(&pk), b"witness-b")
            .unwrap();
        assert_ne!(
            a, b,
            "distinct witness bytes must yield distinct producer outputs"
        );
    }

    #[test]
    fn producer_custom_kind_routes_through_custom_registry() {
        struct AcceptAllProducer {
            vk: [u8; 32],
        }
        impl WitnessProducer for AcceptAllProducer {
            fn name(&self) -> &'static str {
                "accept-all-producer"
            }
            fn kind(&self) -> WitnessedPredicateKind {
                WitnessedPredicateKind::Custom { vk_hash: self.vk }
            }
            fn produce(
                &self,
                _commitment: &[u8; 32],
                _input: &PredicateInput<'_>,
                witness_bytes: &[u8],
            ) -> Result<Vec<u8>, WitnessProducerError> {
                let mut out = Vec::with_capacity(witness_bytes.len() + 6);
                out.extend_from_slice(b"custom");
                out.extend_from_slice(witness_bytes);
                Ok(out)
            }
        }

        let vk = [7u8; 32];
        let mut reg = WitnessProducerRegistry::empty();
        reg.register_custom(vk, Arc::new(AcceptAllProducer { vk }));
        let wp = WitnessedPredicate::custom(vk, [0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        let out = reg
            .produce(&wp, &PredicateInput::Sender(&pk), b"hello")
            .expect("custom producer dispatches");
        assert!(out.starts_with(b"custom"));
    }

    #[test]
    fn producer_custom_kind_unregistered_vk_hash_yields_kind_not_registered() {
        let reg = WitnessProducerRegistry::empty();
        let wp = WitnessedPredicate::custom([99u8; 32], [0u8; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        let err = reg
            .produce(&wp, &PredicateInput::Sender(&pk), b"witness")
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessProducerError::KindNotRegistered {
                kind: WitnessedPredicateKind::Custom { .. }
            }
        ));
    }

    #[test]
    fn producer_vk_hash_default_is_zero_for_builtins() {
        // Built-in kinds report all-zero vk_hash; only Custom kinds
        // carry meaningful vk_hash from their discriminant.
        let producers = WitnessProducerRegistry::with_stubs();
        let p = producers
            .get(WitnessedPredicateKind::Dfa)
            .expect("dfa stub");
        assert_eq!(p.vk_hash(), [0u8; 32]);
    }

    // ─── AIR-soundness-audit (ce1e2def) adversarial tests ──────────────
    //
    // Each test below mirrors the prior playground-bypass attack for one
    // witness-bearing predicate kind: "construct any 1-byte 'proof' and
    // submit it against a known commitment; assert the default registry
    // rejects it." Before the audit fix, `default_builtins()` returned
    // `with_stubs()` and every one of these passed for any non-empty
    // bytes, silently bypassing every authorization predicate in the
    // system.

    fn assert_default_rejects_garbage(wp: WitnessedPredicate, kind_label: &str) {
        let reg = WitnessedPredicateRegistry::default_builtins();
        let pk = [0u8; 32];
        let input = PredicateInput::Sender(&pk);
        // 1-byte "proof" — the prior attack payload.
        let err = reg
            .verify(&wp, &input, &[0x42u8])
            .unwrap_err_or_else_helper(kind_label);
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "{kind_label}: default_builtins must REJECT 1-byte forged proof; got {err:?}"
        );
        // Random 64-byte garbage — same expectation.
        let garbage: Vec<u8> = (0..64u8).collect();
        let err = reg
            .verify(&wp, &input, &garbage)
            .unwrap_err_or_else_helper(kind_label);
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "{kind_label}: default_builtins must REJECT 64-byte garbage proof; got {err:?}"
        );
    }

    // Local helper trait so the inline call site reads naturally without
    // pulling in a new trait into the public surface.
    trait UnwrapErrHelper<T, E> {
        fn unwrap_err_or_else_helper(self, label: &str) -> E;
    }
    impl<T: std::fmt::Debug, E> UnwrapErrHelper<T, E> for Result<T, E> {
        fn unwrap_err_or_else_helper(self, label: &str) -> E {
            match self {
                Ok(v) => panic!(
                    "{label}: expected default_builtins to reject forged proof, \
                     but it ACCEPTED (returned Ok({v:?})). This is a silent \
                     soundness loss — every witnessed-predicate caveat would \
                     bypass under this default."
                ),
                Err(e) => e,
            }
        }
    }

    #[test]
    fn audit_attack_default_rejects_dfa_forged_one_byte_proof() {
        assert_default_rejects_garbage(
            WitnessedPredicate::dfa(
                [0xAB; 32], // route-table root
                InputRef::Sender,
                0,
            ),
            "Dfa",
        );
    }

    #[test]
    fn audit_attack_default_rejects_temporal_forged_one_byte_proof() {
        assert_default_rejects_garbage(WitnessedPredicate::temporal([0xCD; 32], 0, 0), "Temporal");
    }

    #[test]
    fn audit_attack_default_rejects_merkle_membership_forged_one_byte_proof() {
        assert_default_rejects_garbage(
            WitnessedPredicate::merkle_membership([0xEF; 32], InputRef::Sender, 0),
            "MerkleMembership",
        );
    }

    #[test]
    fn audit_attack_default_rejects_blinded_set_forged_one_byte_proof() {
        assert_default_rejects_garbage(
            WitnessedPredicate::blinded_set([0x12; 32], InputRef::Sender, 0),
            "BlindedSet",
        );
    }

    #[test]
    fn audit_attack_default_rejects_bridge_predicate_forged_one_byte_proof() {
        assert_default_rejects_garbage(
            WitnessedPredicate::bridge_predicate(
                [0x34; 32],
                InputRef::PublicInput { pi_index: 0 },
                0,
            ),
            "BridgePredicate",
        );
    }

    #[test]
    fn audit_attack_default_rejects_pedersen_equality_forged_one_byte_proof() {
        assert_default_rejects_garbage(
            WitnessedPredicate::pedersen_equality([0x56; 32], InputRef::Slot { index: 0 }, 0),
            "PedersenEquality",
        );
    }

    /// The default registry MUST install the real NonMembership
    /// verifier (not a NotYetWired-style rejecter) because it's the one
    /// kind whose cryptographic algebra ships in this crate.
    #[test]
    fn audit_default_registry_keeps_nonmembership_real_verifier() {
        let reg = WitnessedPredicateRegistry::default_builtins();
        let v = reg
            .get(WitnessedPredicateKind::NonMembership)
            .expect("NonMembership must be registered in default_builtins");
        assert_eq!(v.name(), "sorted-neighbor-non-membership");
    }

    // ─── BlindedSet credential-set membership verifier ──────────────────
    //
    // The credential-gated cross-app tier (nameservice attested
    // registration, governed-namespace credential voting) dispatches
    // `AuthorizedSet::CredentialSet` to `WitnessedPredicateKind::BlindedSet`.
    // Before this verifier landed, BlindedSet mapped to NotYetWiredVerifier
    // (reject-all), so the tier could never ACCEPT. These tests prove the
    // real verifier ACCEPTS a valid honest proof and REJECTS empty/invalid
    // ones — closing task #140 to Silver-Sound.

    /// The (issuer, schema) commitment used in BlindedSet tests — mirrors
    /// `AuthorizedSet::credential_set_commitment`.
    fn cred_commitment() -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-credential-set-v1");
        h.update(&[0xEEu8; 32]); // issuer_cell
        h.update(&[0x11u8; 32]); // credential_schema_id
        *h.finalize().as_bytes()
    }

    /// The per-credential holder blinding used by the BlindedSet tests.
    const HOLDER_BLINDING: [u8; 32] = [0xB1u8; 32];

    /// Build an honest single-member accumulator + non-revocation witness
    /// for `holder` (holder-blinded). The membership path is a depth-1 tree
    /// whose other leaf is a fixed sibling; the revocation set has the holder's
    /// *committed leaf* absent in the open interval (lower, upper).
    fn honest_credential_proof(
        commitment: &[u8; 32],
        holder: &[u8; 32],
    ) -> CredentialSetMembershipProof {
        honest_credential_proof_blinded(commitment, holder, &HOLDER_BLINDING)
    }

    fn honest_credential_proof_blinded(
        commitment: &[u8; 32],
        holder: &[u8; 32],
        blinding: &[u8; 32],
    ) -> CredentialSetMembershipProof {
        let sibling = [0x77u8; 32];
        let path = vec![(sibling, false)]; // committed leaf is the left child
        let revocation_root = [0x33u8; 32];
        // The non-revocation neighbors bracket the *committed leaf*, not the
        // holder (keeps non-revocation blind). Pick neighbors strictly
        // bracketing committed_leaf by decrementing/incrementing its last byte.
        let leaf = CredentialSetMembershipProof::holder_commit_leaf(commitment, holder, blinding);
        let lower = {
            let mut l = leaf;
            // ensure strictly below: zero the last byte (leaf last byte chosen
            // below to be > 0 by construction is not guaranteed, so subtract on
            // a non-zero byte). Use a robust bracket: zero out the low 16 bytes.
            for b in l[16..].iter_mut() {
                *b = 0;
            }
            l
        };
        let upper = {
            let mut u = leaf;
            for b in u[16..].iter_mut() {
                *b = 0xFF;
            }
            u
        };
        // The mock adjacency verifier accepts `b"ADJ-OK"`; the production prover
        // supplies a real consecutive-index STARK here.
        CredentialSetMembershipProof::new(
            commitment,
            holder,
            blinding,
            path,
            revocation_root,
            lower,
            upper,
            b"ADJ-OK".to_vec(),
        )
    }

    /// Build a `StaticIssuerRootAuthority` authorizing the given proof's roots
    /// under `commitment` (so the issuer-root-binding leg passes).
    fn issuer_authority_for(
        commitment: &[u8; 32],
        proof: &CredentialSetMembershipProof,
    ) -> Arc<dyn IssuerRootAuthority> {
        Arc::new(StaticIssuerRootAuthority::new().authorize(
            *commitment,
            proof.issuer_set_root,
            proof.revocation_root,
        ))
    }

    /// A production-shaped registry for a specific honest proof: mock adjacency
    /// + an issuer-root authority that recognizes the proof's roots.
    fn registry_for_proof(
        commitment: &[u8; 32],
        proof: &CredentialSetMembershipProof,
    ) -> WitnessedPredicateRegistry {
        let mut r = WitnessedPredicateRegistry::with_stubs();
        let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(MockAdjacency);
        let auth = issuer_authority_for(commitment, proof);
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::production(
            adj, auth,
        )));
        r
    }

    #[test]
    fn blinded_set_accepts_honest_membership_proof() {
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let proof = honest_credential_proof(&commitment, &holder);
        let bytes = proof.to_bytes();

        let reg = registry_for_proof(&commitment, &proof);
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        reg.verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .expect("honest credential-set membership proof must verify");
    }

    /// HOLDER ANONYMITY: the holder pubkey must NOT appear anywhere in the
    /// serialized proof's public inputs (committed_leaf, binding_tag,
    /// issuer_set_root, merkle path). Only the hiding commitment does.
    #[test]
    fn blinded_set_holder_pubkey_absent_from_public_inputs() {
        let commitment = cred_commitment();
        // Use a distinctive holder so a byte-scan is meaningful.
        let holder = [0xA7u8; 32];
        let proof = honest_credential_proof(&commitment, &holder);

        // The raw holder pubkey must not be a field of the proof.
        assert_ne!(
            proof.committed_leaf, holder,
            "leaf must be a commitment, not the holder"
        );
        assert_ne!(proof.binding_tag, holder);
        assert_ne!(proof.issuer_set_root, holder);
        // And it must not appear as a contiguous 32-byte run in the wire bytes.
        let bytes = proof.to_bytes();
        let needle = &holder[..];
        let found = bytes.windows(32).any(|w| w == needle);
        assert!(
            !found,
            "holder pubkey leaked into the serialized BlindedSet proof public inputs"
        );
    }

    /// ISSUER-ROOT FORGE (fail-before / pass-after): a prover fabricates their
    /// OWN one-leaf accumulator (containing only themselves) and self-attests.
    /// The membership path + binding tag are internally consistent, but the
    /// issuer-root authority does not recognize the fabricated root, so it
    /// rejects. (Pre-fix there was no authority and this self-attestation
    /// succeeded.)
    #[test]
    fn blinded_set_rejects_self_fabricated_accumulator() {
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        // The forger's self-built proof (well-formed, but its root is theirs).
        let forged = honest_credential_proof(&commitment, &holder);

        // The issuer's REAL authority recognizes a DIFFERENT root (a different
        // member set), not the forger's fabricated one.
        let honest_other =
            honest_credential_proof_blinded(&commitment, &[0x09u8; 32], &[0xC2u8; 32]);
        let mut r = WitnessedPredicateRegistry::with_stubs();
        let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(MockAdjacency);
        let auth: Arc<dyn IssuerRootAuthority> =
            Arc::new(StaticIssuerRootAuthority::new().authorize(
                commitment,
                honest_other.issuer_set_root,
                honest_other.revocation_root,
            ));
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::production(
            adj, auth,
        )));

        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = r
            .verify(&wp, &PredicateInput::Sender(&holder), &forged.to_bytes())
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => assert!(
                reason.contains("issuer-root binding failed") || reason.contains("self-fabricated"),
                "expected issuer-root rejection, got: {reason}"
            ),
            other => panic!("expected issuer-root Rejected, got {other:?}"),
        }
    }

    /// Fail-closed when no issuer-root authority is installed (even with a valid
    /// adjacency verifier): an honest, otherwise-valid proof is rejected at the
    /// issuer-root-binding step.
    #[test]
    fn blinded_set_fails_closed_without_issuer_authority() {
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let proof = honest_credential_proof(&commitment, &holder);
        let mut r = WitnessedPredicateRegistry::with_stubs();
        let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(MockAdjacency);
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::with_adjacency(
            adj,
        )));
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = r
            .verify(&wp, &PredicateInput::Sender(&holder), &proof.to_bytes())
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => assert!(
                reason.contains("no issuer-root authority installed"),
                "{reason}"
            ),
            other => panic!("expected fail-closed Rejected, got {other:?}"),
        }
    }

    #[test]
    fn blinded_set_fails_closed_without_adjacency_verifier() {
        // An issuer-root authority is installed (so the issuer-root step
        // passes) but NO adjacency verifier; an otherwise-honest proof fails
        // closed at the non-revocation adjacency step.
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let proof = honest_credential_proof(&commitment, &holder);
        let bytes = proof.to_bytes();
        let mut reg = WitnessedPredicateRegistry::with_stubs();
        let auth = issuer_authority_for(&commitment, &proof);
        reg.register_builtin(Arc::new(
            CredentialSetMembershipVerifier::with_issuer_roots(auth),
        ));
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => {
                assert!(
                    reason.contains("no Merkle-adjacency verifier installed"),
                    "{reason}"
                )
            }
            other => panic!("expected fail-closed Rejected, got {other:?}"),
        }
    }

    #[test]
    fn blinded_set_rejects_wide_bracket_non_revocation_forge() {
        // FORGE CLOSE: a holder who knows revocation_root picks wide-bracket
        // non-revocation neighbors but cannot supply a real adjacency proof.
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let mut proof = honest_credential_proof(&commitment, &holder);
        // Replace non-revocation neighbors with a wide bracket and drop the
        // adjacency proof; re-derive the (cheap) tag so only adjacency gates.
        let revocation_root = proof.revocation_root;
        proof.non_revocation =
            NonMembershipNeighborProof::new(&revocation_root, [0x00u8; 32], [0xFFu8; 32]);
        proof.revocation_adjacency_proof = Vec::new();
        let reg = registry_for_proof(&commitment, &proof);
        let bytes = proof.to_bytes();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "wide-bracket non-revocation forge must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_rejects_empty_proof() {
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), b"")
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn blinded_set_rejects_garbage_proof() {
        // 1-byte and 64-byte garbage — the prior playground bypass payload.
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        for garbage in [vec![0x42u8], (0..64u8).collect::<Vec<u8>>()] {
            let err = reg
                .verify(&wp, &PredicateInput::Sender(&holder), &garbage)
                .unwrap_err();
            assert!(
                matches!(err, WitnessedPredicateError::Rejected { .. }),
                "garbage proof must reject"
            );
        }
    }

    #[test]
    fn blinded_set_rejects_wrong_holder_transplant() {
        // A proof minted for holder A must not verify when presented by
        // holder B (the leaf and binding tag both bind the holder).
        let commitment = cred_commitment();
        let holder_a = [0x05u8; 32];
        let holder_b = [0x06u8; 32];
        let proof = honest_credential_proof(&commitment, &holder_a);
        let bytes = proof.to_bytes();

        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder_b), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "transplant to a different holder must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_rejects_wrong_commitment_transplant() {
        // A proof minted under (issuer_A, schema_A) must not verify under a
        // different commitment (the leaf + binding tag bind the commitment).
        let commitment_a = cred_commitment();
        let commitment_b = {
            let mut h = blake3::Hasher::new_derive_key("dregg-credential-set-v1");
            h.update(&[0xEEu8; 32]);
            h.update(&[0x22u8; 32]); // different schema
            *h.finalize().as_bytes()
        };
        let holder = [0x05u8; 32];
        let proof = honest_credential_proof(&commitment_a, &holder);
        let bytes = proof.to_bytes();

        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment_b, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "cross-(issuer,schema) transplant must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_rejects_forged_membership_path() {
        // Forge the Merkle path so it no longer reconstructs the claimed
        // issuer_set_root, but recompute the binding tag so the tag check
        // passes — isolating the membership check.
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let mut proof = honest_credential_proof(&commitment, &holder);
        // Tamper the sibling so the path reaches a different root.
        proof.merkle_path[0].0 = [0xAAu8; 32];
        // Re-bind the tag to the (unchanged) claimed roots so we exercise
        // the membership check, not the tag check.
        proof.binding_tag = CredentialSetMembershipProof::binding_tag(
            &commitment,
            &holder,
            &proof.issuer_set_root,
            &proof.revocation_root,
        );
        let bytes = proof.to_bytes();

        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "forged membership path must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_rejects_revoked_holder() {
        // The holder IS in the revocation set: the non-revocation neighbor
        // witness cannot bracket the committed leaf in an open interval.
        // Simulate by building a non-revocation witness whose lower neighbor
        // equals the committed leaf (i.e. the leaf is present at `lower`).
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let blinding = HOLDER_BLINDING;
        let sibling = [0x77u8; 32];
        let path = vec![(sibling, false)];
        let revocation_root = [0x33u8; 32];
        let leaf =
            CredentialSetMembershipProof::holder_commit_leaf(&commitment, &holder, &blinding);
        // lower == committed_leaf ⇒ leaf is in the revocation set ⇒ reject.
        let upper = {
            let mut u = leaf;
            for b in u[16..].iter_mut() {
                *b = 0xFF;
            }
            u
        };
        let proof = CredentialSetMembershipProof::new(
            &commitment,
            &holder,
            &blinding,
            path,
            revocation_root,
            leaf,  // lower == committed_leaf (revoked)
            upper, // upper
            b"ADJ-OK".to_vec(),
        );
        let bytes = proof.to_bytes();

        let reg = registry_for_proof(&commitment, &proof);
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "revoked holder must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_rejects_swapped_revocation_root() {
        // Swap the revocation_root after minting so the non-revocation
        // adjacency tag no longer anchors to it AND the binding tag breaks.
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let mut proof = honest_credential_proof(&commitment, &holder);
        proof.revocation_root = [0x99u8; 32]; // swapped, tag now stale
        let bytes = proof.to_bytes();

        let reg = WitnessedPredicateRegistry::default_builtins();
        let wp = WitnessedPredicate::blinded_set(commitment, InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&holder), &bytes)
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "swapped revocation root must reject; got {err:?}"
        );
    }

    #[test]
    fn blinded_set_default_registry_installs_real_verifier() {
        let reg = WitnessedPredicateRegistry::default_builtins();
        let v = reg
            .get(WitnessedPredicateKind::BlindedSet)
            .expect("BlindedSet must be registered in default_builtins");
        assert_eq!(v.name(), "credential-set-membership");
    }

    #[test]
    fn credential_set_membership_proof_roundtrips_bytes() {
        let commitment = cred_commitment();
        let holder = [0x05u8; 32];
        let proof = honest_credential_proof(&commitment, &holder);
        let bytes = proof.to_bytes();
        let back = CredentialSetMembershipProof::from_bytes(&bytes).unwrap();
        assert_eq!(back, proof);
    }
}
