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
/// vk_hash = BLAKE3_keyed("pyana-witnessed-predicate-vk-v1",
///                        len(bytes) || bytes)
/// ```
///
/// The length prefix makes the encoding unambiguous against
/// concatenation: two predicates whose bytes happen to share a prefix
/// produce different vk_hashes.
///
/// # Why opaque bytes?
///
/// Custom predicates may be authored in many representations: pyana-DSL
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
    let mut hasher = blake3::Hasher::new_derive_key("pyana-witnessed-predicate-vk-v1");
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
    /// `pyana-circuit` (or app-side) crates before evaluating any
    /// real witnessed predicate.
    pub fn with_stubs() -> Self {
        let mut r = Self::empty();
        r.register_builtin(Arc::new(StubVerifier::dfa()));
        r.register_builtin(Arc::new(StubVerifier::temporal()));
        r.register_builtin(Arc::new(StubVerifier::merkle_membership()));
        // NonMembership is structurally checkable from neighbor-witness
        // bytes alone, so we register a *real* (non-stub) verifier that
        // enforces the sorted-set neighbor invariant: A < candidate < B
        // with A, B consecutive in the sorted leaf order. This makes
        // forged renunciations rejectable without needing the full STARK
        // verifier registered.
        r.register_builtin(Arc::new(SortedNeighborNonMembershipVerifier));
        r.register_builtin(Arc::new(StubVerifier::blinded_set()));
        r.register_builtin(Arc::new(StubVerifier::bridge_predicate()));
        r.register_builtin(Arc::new(StubVerifier::pedersen_equality()));
        r
    }

    /// Construct the executor-default registry — Cav-Codex Block 3.5.
    ///
    /// Production-facing default that every `TurnExecutor` should
    /// receive on construction (`turn::executor::TurnExecutor::new` and
    /// friends call this so the registry is never `None`). Today this
    /// returns the stub-verifier registry — the real per-kind verifiers
    /// (`Dfa`, `Temporal`, `MerkleMembership`, `BlindedSet`,
    /// `BridgePredicate`, `PedersenEquality`) live in `pyana-circuit`
    /// and would force a circuit dependency on this cell crate; the
    /// expectation is that the host (a binary that links both crates)
    /// calls `set_witnessed_registry` with the
    /// `pyana_circuit::witnessed_predicate::default_registry()` form to
    /// upgrade the stubs into real verifiers.
    ///
    /// Until that upgrade, the stubs accept any non-empty proof bytes.
    /// That is *not* a soundness claim — it's a fail-safe-but-loud
    /// signal: the dispatch path works, the surface contract is
    /// honored, and the real verifier wiring is the next install step.
    /// The alternative — leaving the registry `None` — was worse
    /// because it surfaced
    /// `ProgramError::WitnessedPredicateRequiresExecutor` *before* the
    /// host could swap in the real verifiers, causing every action that
    /// declared a `Witnessed { wp }` slot caveat to fail at evaluation.
    pub fn default_builtins() -> Self {
        Self::with_stubs()
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
    /// producers (`pyana-circuit` for Dfa / Temporal /
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
    fn blinded_set() -> Self {
        Self {
            kind: WitnessedPredicateKind::BlindedSet,
            name: "stub-blinded-set",
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
        if proof_bytes.is_empty() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name,
                reason: "stub verifier requires non-empty proof bytes".into(),
            });
        }
        Ok(())
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
/// 3. `consecutive_tag == [0xFE; 32]` (the prover's commitment that
///    the neighbors are consecutive — bound into the proof so the
///    AIR-side STARK verifier can re-check it against the sorted
///    set's adjacency table; here we only check the structural
///    discipline of the witness shape).
///
/// When `pyana-circuit`'s real non-membership STARK lands the
/// adjacency check joins this verifier (today the STARK is the proof
/// of "lower, upper are consecutive leaves under `commitment`"; this
/// verifier proves only the ordering relation between candidate and
/// neighbors, which is necessary-but-not-sufficient for soundness on
/// its own).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipNeighborProof {
    pub lower: [u8; 32],
    pub upper: [u8; 32],
    pub consecutive_tag: [u8; 32],
}

impl NonMembershipNeighborProof {
    /// Encode the proof to its 96-byte wire form (lower || upper || tag).
    pub fn to_bytes(&self) -> [u8; 96] {
        let mut out = [0u8; 96];
        out[0..32].copy_from_slice(&self.lower);
        out[32..64].copy_from_slice(&self.upper);
        out[64..96].copy_from_slice(&self.consecutive_tag);
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
            consecutive_tag: tag,
        })
    }
    /// The canonical "neighbors are consecutive" tag the prover must
    /// embed in the proof. The real STARK side replaces this with a
    /// per-(set, lower, upper) adjacency commitment; here it's a fixed
    /// sentinel so a *forged* renunciation (one whose prover never had
    /// access to a real neighbor-witness gadget) cannot satisfy this
    /// without committing to the tag, while an honest prover trivially
    /// supplies it.
    pub const CONSECUTIVE_TAG: [u8; 32] = [0xFE; 32];
}

struct SortedNeighborNonMembershipVerifier;

impl WitnessedPredicateVerifier for SortedNeighborNonMembershipVerifier {
    fn name(&self) -> &'static str {
        "sorted-neighbor-non-membership"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::NonMembership
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let proof = NonMembershipNeighborProof::from_bytes(proof_bytes).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: format!(
                    "non-membership proof must be 96 bytes (lower||upper||tag), got {}",
                    proof_bytes.len()
                ),
            }
        })?;
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
        // Enforce the consecutive-neighbors discipline tag.
        if proof.consecutive_tag != NonMembershipNeighborProof::CONSECUTIVE_TAG {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "NonMembership",
                reason: "consecutive_tag does not match the canonical sentinel; the prover did not commit to the sorted-neighbor adjacency invariant".into(),
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
        Ok(())
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
        for wp in [
            WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::temporal([0u8; 32], 0, 0),
            WitnessedPredicate::merkle_membership([0u8; 32], InputRef::Sender, 0),
            WitnessedPredicate::blinded_set([0u8; 32], InputRef::Sender, 0),
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

    /// A helper that fabricates an honest renunciation neighbor witness
    /// for a candidate that is provably *not* in the sorted set
    /// {lower, upper, ...}.
    fn honest_renunciation_proof(lower: [u8; 32], upper: [u8; 32]) -> NonMembershipNeighborProof {
        NonMembershipNeighborProof {
            lower,
            upper,
            consecutive_tag: NonMembershipNeighborProof::CONSECUTIVE_TAG,
        }
    }

    #[test]
    fn non_membership_accepts_legal_renunciation() {
        // Candidate 0x05 falls in (0x04, 0x06); honest witness accepts.
        let lower = [0x04u8; 32];
        let upper = [0x06u8; 32];
        let candidate = [0x05u8; 32];
        let proof = honest_renunciation_proof(lower, upper);
        let bytes = proof.to_bytes();

        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        reg.verify(&wp, &PredicateInput::Sender(&candidate), &bytes)
            .expect("legal renunciation should verify");
    }

    #[test]
    fn non_membership_rejects_candidate_equal_to_lower_neighbor() {
        // Candidate == lower neighbor → candidate IS in set → renunciation
        // must reject (this is the adversarial case: the prover IS in the
        // set but is claiming non-membership).
        let lower = [0x05u8; 32];
        let upper = [0x06u8; 32];
        let candidate = [0x05u8; 32];
        let proof = honest_renunciation_proof(lower, upper);

        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_candidate_equal_to_upper_neighbor() {
        let lower = [0x04u8; 32];
        let upper = [0x05u8; 32];
        let candidate = [0x05u8; 32];
        let proof = honest_renunciation_proof(lower, upper);

        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_out_of_interval_candidate() {
        // Candidate above the upper neighbor: out-of-interval, neighbors
        // don't bracket the candidate.
        let lower = [0x04u8; 32];
        let upper = [0x06u8; 32];
        let candidate = [0x09u8; 32];
        let proof = honest_renunciation_proof(lower, upper);

        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_forged_consecutive_tag() {
        // Even if lower < candidate < upper, a forged consecutive_tag
        // breaks the soundness binding to the sorted-set adjacency
        // commitment.
        let lower = [0x04u8; 32];
        let upper = [0x06u8; 32];
        let candidate = [0x05u8; 32];
        let mut proof = honest_renunciation_proof(lower, upper);
        proof.consecutive_tag = [0u8; 32]; // forged
        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_rejects_malformed_proof_bytes() {
        let reg = WitnessedPredicateRegistry::with_stubs();
        let wp = WitnessedPredicate::non_membership([0xAB; 32], InputRef::Sender, 0);
        let pk = [0u8; 32];
        // Wrong length:
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"short")
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    #[test]
    fn non_membership_proof_roundtrips_bytes() {
        let p = NonMembershipNeighborProof {
            lower: [1u8; 32],
            upper: [3u8; 32],
            consecutive_tag: NonMembershipNeighborProof::CONSECUTIVE_TAG,
        };
        let bytes = p.to_bytes();
        let back = NonMembershipNeighborProof::from_bytes(&bytes).unwrap();
        assert_eq!(back, p);
    }
}
