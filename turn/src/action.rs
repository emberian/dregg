//! Action types: the building blocks of a call forest.
//!
//! An Action is a single operation in the call forest, analogous to Mina's AccountUpdate.
//! Each action targets a cell, specifies a method, carries authorization, declares
//! preconditions, and produces effects.

use pyana_cell::note_bridge::{BridgeReceipt, PortableNoteProof};
use pyana_cell::permissions::AuthRequired;
use pyana_cell::predicate::WitnessedPredicate;
use pyana_cell::state::FieldElement;
use pyana_cell::{CapabilityRef, CellId, NoteCommitment, Nullifier, Preconditions, SealedBox};
#[allow(unused_imports)]
use pyana_cell::{ValueCommitment, ValueCommitmentBytes};
use serde::{Deserialize, Serialize};

use crate::conditional::{ConditionProof, ProofCondition};
use crate::escrow::{EscrowClaimAuth, EscrowCondition};

/// How much of the turn an action's signer commits to.
///
/// This controls what goes into the signing message:
/// - `Full`: signs over the entire turn hash (maximum binding, current default)
/// - `Partial`: signs over only this action's content + its position in the forest,
///   allowing composability where signers don't need to see other actions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CommitmentMode {
    /// Sign over the entire turn hash (current behavior — maximum binding).
    Full,
    /// Sign over only this action's hash + its position in the forest.
    /// Allows composability: signer doesn't need to see other actions.
    Partial,
}

impl Default for CommitmentMode {
    fn default() -> Self {
        CommitmentMode::Full
    }
}

/// A Symbol is a BLAKE3-hashed method or topic name, stored as a field element.
pub type Symbol = FieldElement;

/// Compute a symbol from a string name.
pub fn symbol(name: &str) -> Symbol {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// A single operation in the call forest.
///
/// Analogous to Mina's AccountUpdate: targets a cell, performs a method,
/// requires authorization, checks preconditions, and produces effects.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Action {
    /// Which cell is being acted upon.
    pub target: CellId,
    /// What operation (method name hashed to symbol).
    pub method: Symbol,
    /// Arguments to the operation.
    pub args: Vec<FieldElement>,
    /// How this action is authorized.
    pub authorization: Authorization,
    /// What must be true before this action can execute.
    pub preconditions: Preconditions,
    /// What changes result from this action.
    pub effects: Vec<Effect>,
    /// Can children use parent's capabilities?
    pub may_delegate: DelegationMode,
    /// How much of the turn this action's signer commits to.
    /// Full = signs over entire turn hash (default, maximum binding).
    /// Partial = signs over only this action + position (enables multi-party composition).
    #[serde(default)]
    pub commitment_mode: CommitmentMode,
    /// Signed balance modification (Mina-style).
    ///
    /// When set, this applies a signed delta to the target cell's balance:
    /// - Negative values withdraw (produce excess available to other actions)
    /// - Positive values deposit (consume excess from other actions)
    ///
    /// At turn end, the sum of all balance_change deltas must be zero (conservation law).
    /// This enables composable patterns like DEX fills without explicit Transfer pairing.
    #[serde(default)]
    pub balance_change: Option<i64>,
    /// Canonical witness carrier for witness-attached predicates.
    ///
    /// Each blob is an opaque bytestring identified by its index in this vec.
    /// `WitnessedPredicate` clauses (in [`Preconditions::witnessed`] or in
    /// [`pyana_cell::StateConstraint::Witnessed`]) reference a blob by index
    /// via `WitnessedPredicate::proof_witness_index`. Variant-specific
    /// witnesses (Merkle paths for `SenderAuthorized`, preimage bytes for
    /// `PreimageGate`, per-(cell,sender) epoch counters for `RateLimit`,
    /// `Custom` predicate STARK proofs, etc.) are encoded as
    /// [`WitnessBlob`] entries here.
    ///
    /// Turn::hash v3 covers this field (see [`Action::hash`]); existing
    /// signatures that signed an empty vec are byte-identical to actions
    /// that omitted the field (postcard skips empty vecs by default).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub witness_blobs: Vec<WitnessBlob>,
}

/// A single witness blob carried alongside an [`Action`].
///
/// Witness blobs are the canonical carrier for the inputs that
/// witness-attached predicates (`WitnessedPredicate`) and slot-caveat
/// enforcement need. The encoding is **typed-tag + bytes** so the
/// executor can dispatch without parsing the variant; the bytes are
/// then interpreted per-tag.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessBlob {
    /// What kind of witness this is. Determines how `bytes` is parsed.
    pub kind: WitnessKind,
    /// The opaque witness payload. Encoding is determined by `kind`.
    pub bytes: Vec<u8>,
}

impl WitnessBlob {
    /// Construct a `WitnessBlob` with the given kind and raw bytes.
    pub fn new(kind: WitnessKind, bytes: Vec<u8>) -> Self {
        Self { kind, bytes }
    }
    /// Convenience: a Merkle-membership-proof blob (for `SenderAuthorized`).
    pub fn merkle_path(path_bytes: Vec<u8>) -> Self {
        Self {
            kind: WitnessKind::MerklePath,
            bytes: path_bytes,
        }
    }
    /// Convenience: a 32-byte preimage blob (for `PreimageGate`).
    pub fn preimage(preimage: [u8; 32]) -> Self {
        Self {
            kind: WitnessKind::Preimage32,
            bytes: preimage.to_vec(),
        }
    }
    /// Convenience: a STARK / custom proof bytes blob.
    pub fn proof(proof_bytes: Vec<u8>) -> Self {
        Self {
            kind: WitnessKind::ProofBytes,
            bytes: proof_bytes,
        }
    }
    /// Convenience: a u32 rate-limit count blob (for `RateLimit`).
    pub fn rate_limit_count(count: u32) -> Self {
        Self {
            kind: WitnessKind::RateLimitCount,
            bytes: count.to_le_bytes().to_vec(),
        }
    }
    /// Decode `RateLimitCount` payload to its u32 value.
    pub fn as_rate_limit_count(&self) -> Option<u32> {
        if self.kind != WitnessKind::RateLimitCount || self.bytes.len() != 4 {
            return None;
        }
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&self.bytes);
        Some(u32::from_le_bytes(buf))
    }
    /// Decode `Preimage32` payload to its 32-byte value.
    pub fn as_preimage32(&self) -> Option<[u8; 32]> {
        if self.kind != WitnessKind::Preimage32 || self.bytes.len() != 32 {
            return None;
        }
        let mut buf = [0u8; 32];
        buf.copy_from_slice(&self.bytes);
        Some(buf)
    }
}

/// Kinds of witness payloads carried in `Action::witness_blobs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessKind {
    /// 32-byte preimage payload (for `PreimageGate`).
    Preimage32,
    /// Merkle-membership-proof bytes (for `SenderAuthorized` /
    /// `MerkleMembership` witnessed predicates).
    MerklePath,
    /// u32 little-endian rate-limit counter snapshot (for `RateLimit`).
    RateLimitCount,
    /// STARK / Plonk / Bulletproof proof bytes (for `WitnessedPredicate`
    /// dispatch, custom-AIR proofs, etc.).
    ProofBytes,
    /// Cleartext bytes — interpreted by the receiving verifier.
    Cleartext,
}

/// How an action is authorized.
///
/// Maps to the authorization models in Mina: signature, proof, or none.
/// Adds `Breadstuff` for capability token authorization.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Authorization {
    /// Ed25519 signature over the action hash (stored as two 32-byte halves).
    Signature([u8; 32], [u8; 32]),
    /// Zero-knowledge proof bytes with the bound (action, resource) pair.
    ///
    /// The `bound_action` and `bound_resource` fields record what the prover
    /// committed to at proving time (from `AuthRequest.action` and
    /// `app_id.or(service)`). The verifier recomputes the binding from these
    /// strings and checks it against the proof's public inputs.
    Proof {
        proof_bytes: Vec<u8>,
        bound_action: String,
        bound_resource: String,
    },
    /// Capability token hash (breadstuff authorization).
    Breadstuff([u8; 32]),
    /// Bearer capability: proof-carrying authorization that exercises a capability
    /// WITHOUT requiring it to be in the actor's c-list. The proof demonstrates
    /// delegated authority from a root holder through a delegation chain.
    ///
    /// This enables E-language alignment: a capability can be exercised immediately
    /// in the same turn it is delegated, with no persistence in any cell's state.
    Bearer(BearerCapProof),
    /// No authorization provided (only valid if the cell's permissions allow it).
    ///
    /// Named `Unchecked` rather than `None` to make it grep-able and ensure
    /// code review flags its usage. Previously called `None`.
    #[serde(alias = "None")]
    Unchecked,
    /// Authorization derived from a verified CapTP delivery (Seam 3, Stage 7 / P1.B).
    ///
    /// When a CapTP wire message (EnlivenSturdyRef, DropRemoteRef, PresentHandoff,
    /// CapHello-driven export) is received, the wire layer constructs a Turn that
    /// mirrors the CapTP-side state mutation on-chain. The cryptographic legitimacy
    /// of that delivery is captured here:
    ///
    /// - `handoff_cert` is the introducer-signed certificate naming the recipient,
    ///   target cell, swiss number, permissions, allowed_effects, and nonce. Its
    ///   `introducer_signature` binds the certificate to the introducer's identity.
    /// - `sender_pk` is the recipient public key named in the certificate (the
    ///   entity that delivered the CapTP wire message).
    /// - `sender_signature` is a 64-byte ed25519 signature by `sender_pk` over
    ///   the canonical CapTP-delivery signing message (see
    ///   `Authorization::captp_delivered_signing_message`). This binds the
    ///   specific Turn (agent, target, effects, nonce) to this certificate's
    ///   nonce — defeating replay against unrelated turns.
    ///
    /// The executor verifies (a) the introducer signature on the cert against
    /// `introducer_pk`, (b) the sender signature over the canonical message
    /// against `sender_pk`, (c) that `sender_pk == handoff_cert.recipient_pk`,
    /// and (d) that the cert's `allowed_effects` (when present) covers every
    /// effect in the action.
    CapTpDelivered {
        /// The introducer-signed handoff certificate that authorized this delivery.
        handoff_cert: pyana_captp::HandoffCertificate,
        /// The introducer's public key (used to verify `handoff_cert.introducer_signature`).
        /// Must derive from `handoff_cert.introducer` (the federation id) — the executor
        /// rejects the variant if they disagree.
        introducer_pk: [u8; 32],
        /// The recipient/sender public key. Must equal `handoff_cert.recipient_pk`.
        sender_pk: [u8; 32],
        /// Ed25519 signature by `sender_pk` over `captp_delivered_signing_message`.
        #[serde(with = "crate::escrow::serde_sig64")]
        sender_signature: [u8; 64],
    },
    /// App-defined authorization: a [`WitnessedPredicate`] proves the
    /// authorization condition holds for THIS turn at THIS federation
    /// at THIS nonce position (per `AUTHORIZATION-CUSTOM-DESIGN.md`).
    ///
    /// The predicate's `input_ref` SHOULD be
    /// [`InputRef::SigningMessage`](pyana_cell::InputRef::SigningMessage),
    /// which the executor binds to the bytes
    /// `compute_partial_signing_message(action, position, federation_id,
    /// turn_nonce)` produces. The same federation/nonce binding the
    /// `Signature` path enjoys carries to `Custom`.
    ///
    /// `predicate.proof_witness_index` names the entry in
    /// [`Action::witness_blobs`] that carries the proof bytes; the
    /// verifier is resolved via the executor's
    /// `WitnessedPredicateRegistry` keyed on `predicate.kind`. Unknown
    /// kinds reject with [`TurnError::AuthModeNotRegistered`].
    ///
    /// When the target cell's [`AuthRequired::Custom { vk_hash }`] is
    /// set, the executor additionally requires that
    /// `predicate.kind == WitnessedPredicateKind::Custom { vk_hash }`
    /// — the cell declares which mode it accepts (design §10.4).
    Custom {
        /// The witnessed predicate that proves the authorization
        /// condition. Its commitment names the auth-mode-specific
        /// audience root (e.g., multisig signer set, time-lock DSL
        /// hash, credential ring root); its proof witnesses the
        /// authorization condition over the canonical signing message.
        predicate: WitnessedPredicate,
    },
    /// **Disjunctive multi-mode authorization: any one of `candidates`
    /// suffices.** Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3 / §9.2.3`,
    /// this is the categorical coproduct in the `Authorization`
    /// category — the missing "alternation" primitive.
    ///
    /// **App drivers.** *Multi-key wallets* ("authorized by any of
    /// these 3 keys"); *recovery flows* ("primary OR backup OR
    /// social-recovery quorum"); *cross-mode bridge requests* ("signed
    /// by this federation OR proven by this STARK"); *hot/cold cap
    /// exercise* ("by the hot key OR by a Custom presentation of the
    /// cold-vault proof"). Each candidate may itself be any
    /// [`Authorization`] variant — `Signature`, `Proof`, `Custom`,
    /// `Bearer`, even a nested `OneOf` (combinatorial blow-up is the
    /// app's problem; nest sparingly).
    ///
    /// **Caveat: M-of-N is *not* `OneOf` of M-tuples** (combinatorial
    /// blow-up). For genuine M-of-N threshold authorization use
    /// [`Authorization::Custom`] with a threshold-sig
    /// `WitnessedPredicate`. `OneOf` is *purely* 1-of-N alternation;
    /// the executor verifies *exactly one* indexed candidate.
    ///
    /// **Soundness contract.** `proof_index` is the prover's
    /// declaration of *which* candidate they're satisfying. The
    /// executor recursively verifies only that one candidate. The
    /// signing-message / nonce / federation-id bindings of the
    /// **indexed candidate** are what guard against replay — the
    /// outer `OneOf` does not add its own binding.
    ///
    /// **Authorization::OneOf::Unchecked is rejected.** A candidate
    /// of `Authorization::Unchecked` reduces this primitive to
    /// "auth-bypass-by-naming-Unchecked" — the executor rejects
    /// any `OneOf` whose indexed candidate is `Unchecked`, mirroring
    /// the executor honesty audit's posture against `Unchecked`
    /// auth (`EXECUTOR-HONESTY-AUDIT.md`).
    ///
    /// **Nested `OneOf` is rejected.** A `OneOf` whose indexed
    /// candidate is itself a `OneOf` is rejected to bound the
    /// recursion depth and audit surface. Apps that want nested
    /// alternation should flatten the `candidates` list.
    OneOf {
        /// The disjunctive candidates. Any *one* satisfying the
        /// chosen `proof_index` authorizes the action.
        candidates: Vec<Authorization>,
        /// Which candidate (0-indexed into `candidates`) the prover
        /// is claiming satisfies the authorization.
        proof_index: u32,
    },
}

/// Proof-carrying bearer capability: demonstrates delegated authority to exercise
/// a capability without holding it in a c-list.
///
/// Bearer caps are ephemeral -- they exist only for the duration of a single turn
/// and never persist in any cell's state. This makes them ideal for immediate
/// inline delegation where a one-turn delay is unacceptable.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BearerCapProof {
    /// The capability target being exercised.
    pub target: CellId,
    /// The permission level being exercised (must be subset of delegator's permissions).
    pub permissions: AuthRequired,
    /// The delegation chain proof (shows how authority flows from root to bearer).
    pub delegation_proof: DelegationProofData,
    /// Expiry height (mandatory for bearer caps -- limits the revocation window).
    pub expires_at: u64,
    /// Optional revocation channel binding. If set, the channel must be active
    /// for the bearer cap to be exercisable.
    pub revocation_channel: Option<[u8; 32]>,
    /// Optional facet restriction on this bearer capability.
    ///
    /// When set, the bearer can only exercise effects whose kind bits are within
    /// this mask. This must be a subset of the delegator's `allowed_effects` (if any).
    /// Enforces E-language facet attenuation: a delegated bearer can only restrict,
    /// never amplify, the delegator's facet.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allowed_effects: Option<pyana_cell::EffectMask>,
}

/// How the delegation chain is proven for a bearer capability.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DelegationProofData {
    /// Signed attestation: delegator signs "I delegate {permissions} on {target}
    /// to {bearer_pk} until {expires_at}".
    SignedDelegation {
        /// Public key of the delegator (must hold the cap in their c-list).
        delegator_pk: [u8; 32],
        /// Ed25519 signature from delegator over the delegation message.
        #[serde(with = "crate::escrow::serde_sig64")]
        signature: [u8; 64],
        /// Public key of the bearer (the entity exercising the cap).
        bearer_pk: [u8; 32],
    },
    /// STARK proof of derivation chain (verifiable without delegator online).
    StarkDelegation {
        /// Serialized STARK proof bytes.
        proof_bytes: Vec<u8>,
        /// Commitment to the root issuer of the capability.
        root_issuer_commitment: [u8; 32],
    },
}

impl Authorization {
    /// Map this authorization to the corresponding AuthKind for permission checking.
    /// Returns None for Authorization::Unchecked, Breadstuff, and Bearer (handled separately).
    pub fn to_auth_kind(&self) -> Option<pyana_cell::AuthKind> {
        match self {
            Authorization::Signature(_, _) => Some(pyana_cell::AuthKind::Signature),
            Authorization::Proof { .. } => Some(pyana_cell::AuthKind::Proof),
            Authorization::Breadstuff(_) => None,
            Authorization::Bearer(_) => None,
            Authorization::Unchecked => None,
            Authorization::CapTpDelivered { .. } => None,
            // Custom is not part of the Sig/Proof lattice; cells that
            // require Custom auth declare `AuthRequired::Custom { vk_hash }`
            // and the executor checks the predicate directly.
            Authorization::Custom { .. } => None,
            // OneOf is a disjunction — its discriminant depends on
            // which candidate the executor verifies, not on the
            // wrapper. Permission checks dispatch by inspecting the
            // chosen candidate at `verify_authorization` time.
            Authorization::OneOf { .. } => None,
        }
    }

    /// Create a Signature authorization from a 64-byte signature.
    pub fn from_sig_bytes(bytes: [u8; 64]) -> Self {
        let mut r = [0u8; 32];
        let mut s = [0u8; 32];
        r.copy_from_slice(&bytes[..32]);
        s.copy_from_slice(&bytes[32..]);
        Authorization::Signature(r, s)
    }

    /// Canonical signing message for `Authorization::CapTpDelivered`.
    ///
    /// Binds the sender's signature to:
    /// - domain separator (`b"pyana-captp-delivered-v1"`),
    /// - the handoff certificate's nonce (cert-binding — same delegation),
    /// - the agent CellId (who runs the turn at the receiving federation),
    /// - the target CellId (which cell the action mutates),
    /// - the turn nonce (replay protection),
    /// - and the canonical postcard encoding of the action's effects.
    ///
    /// Verifiers MUST recompute this from the on-the-wire Turn fields and the
    /// cert nonce — the recipient cannot retroactively repoint their signed
    /// claim to a different turn.
    pub fn captp_delivered_signing_message(
        cert_nonce: &[u8; 32],
        agent: &pyana_cell::CellId,
        target: &pyana_cell::CellId,
        turn_nonce: u64,
        effects: &[Effect],
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(128);
        msg.extend_from_slice(b"pyana-captp-delivered-v1");
        msg.extend_from_slice(cert_nonce);
        msg.extend_from_slice(&agent.0);
        msg.extend_from_slice(&target.0);
        msg.extend_from_slice(&turn_nonce.to_le_bytes());
        // Effects are postcard-serialized for a canonical bytewise encoding.
        // The wire-layer builder uses the same encoding, so both sides agree.
        let effects_bytes = postcard::to_allocvec(effects).expect("effects serialization failed");
        msg.extend_from_slice(&(effects_bytes.len() as u32).to_le_bytes());
        msg.extend_from_slice(&effects_bytes);
        msg
    }
}

/// Delegation mode for child cells. Currently only `None` is enforced;
/// `ParentsOwn` and `Inherit` are planned but not yet implemented in the executor.
/// Use three-party introduction (Effect::Introduce) for explicit capability delegation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DelegationMode {
    /// Children cannot use parent's capabilities.
    None,
    /// Children can use capabilities that the parent owns.
    /// NOTE: Not yet differentiated from `None` in capability-chain walking.
    /// The executor rejects missing capabilities identically for all modes.
    ParentsOwn,
    /// Children inherit parent's delegation mode transitively.
    /// NOTE: Not yet differentiated from `None` in capability-chain walking.
    /// The executor rejects missing capabilities identically for all modes.
    Inherit,
    /// Snapshot+refresh: child inherits parent's capabilities as a point-in-time
    /// snapshot. Child can act using the snapshot offline. Refresh to pick up new
    /// capabilities. Revocation is eventual (bounded by max_staleness).
    SnapshotRefresh,
}

/// An effect produced by an action — what changes in the ledger.
///
/// Analogous to Mina's balance_change + state updates, but generalized for
/// the cell model.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Effect {
    /// Set a state field on a cell.
    SetField {
        cell: CellId,
        index: usize,
        value: FieldElement,
    },
    /// Transfer computrons between cells.
    Transfer {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    /// Grant a capability from one cell to another.
    GrantCapability {
        from: CellId,
        to: CellId,
        cap: CapabilityRef,
    },
    /// Revoke a capability from a cell.
    RevokeCapability { cell: CellId, slot: u32 },
    /// Emit an event from a cell (does not modify state, but is part of the receipt).
    EmitEvent { cell: CellId, event: Event },
    /// Increment a cell's nonce by 1.
    IncrementNonce { cell: CellId },
    /// Create a new cell in the ledger.
    CreateCell {
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: u64,
    },
    /// Update the permissions on a cell.
    ///
    /// SECURITY: This effect is always applied LAST within an action, after all
    /// other effects. Permission checks for all effects use the ORIGINAL permissions
    /// (snapshotted before any effects in this action run). This prevents an action
    /// from weakening permissions and then exploiting the weakened permissions in
    /// subsequent effects within the same action.
    SetPermissions {
        cell: CellId,
        new_permissions: pyana_cell::Permissions,
    },
    /// Update the verification key on a cell.
    ///
    /// SECURITY: Like SetPermissions, this is applied LAST within an action.
    SetVerificationKey {
        cell: CellId,
        new_vk: Option<pyana_cell::VerificationKey>,
    },
    /// Spend (consume) a note by revealing its nullifier.
    /// The proof must demonstrate: the nullifier corresponds to a valid note
    /// in the note tree, and the spender has authority.
    NoteSpend {
        nullifier: Nullifier,
        /// Root of the note tree at the time of proof generation.
        note_tree_root: [u8; 32],
        /// The value being released (for conservation tracking).
        value: u64,
        /// The asset type of the note being spent.
        asset_type: u64,
        /// The STARK spending proof (serialized). Proves:
        /// 1. The spender knows the note's opening (preimage of the commitment)
        /// 2. The nullifier is correctly derived from the note's secret data
        /// 3. The note commitment exists in the note tree (Merkle membership against the root)
        spending_proof: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path instead
        /// of cleartext value comparison. All notes in a turn must either all have
        /// commitments or all lack them (mixed is rejected).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value_commitment: Option<[u8; 32]>,
    },
    /// Create a new note (add commitment to note tree).
    NoteCreate {
        commitment: NoteCommitment,
        /// The value being locked in this note (for conservation tracking).
        value: u64,
        /// The asset type of the note being created.
        asset_type: u64,
        /// Encrypted note content (only recipient can decrypt).
        encrypted_note: Vec<u8>,
        /// Optional Pedersen value commitment (compressed Ristretto point, 32 bytes).
        /// When present, the executor uses the committed conservation path.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        value_commitment: Option<[u8; 32]>,
        /// Optional range proof attesting the committed value is in [0, 2^64).
        /// Required when value_commitment is present to prevent hidden inflation.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        range_proof: Option<Vec<u8>>,
    },
    /// Create a new sealer/unsealer pair for partition-tolerant capability transfer.
    CreateSealPair {
        /// Cell that will hold the sealer capability.
        sealer_holder: CellId,
        /// Cell that will hold the unsealer capability.
        unsealer_holder: CellId,
    },
    /// Seal a capability into an opaque box.
    Seal {
        /// The pair to seal with.
        pair_id: [u8; 32],
        /// The capability to seal.
        capability: CapabilityRef,
    },
    /// Unseal a box, recovering the original capability.
    Unseal {
        /// The sealed box to open.
        sealed_box: SealedBox,
        /// The cell that should receive the unsealed capability.
        recipient: CellId,
    },
    /// Spawn a child cell with snapshot+refresh delegation.
    /// The child inherits the actor's current c-list as a snapshot.
    SpawnWithDelegation {
        /// Public key of the new child cell.
        child_public_key: [u8; 32],
        /// Token domain of the new child cell.
        child_token_id: [u8; 32],
        /// Maximum acceptable staleness (seconds) for the delegation snapshot.
        max_staleness: u64,
    },
    /// Child refreshes its delegation snapshot from its parent.
    /// The actor must be the child cell (self-refresh).
    RefreshDelegation,
    /// Parent revokes delegation to a child by bumping its own epoch.
    /// The child's snapshot becomes stale relative to the new epoch.
    RevokeDelegation {
        /// The child cell whose delegation is being revoked.
        child: CellId,
    },
    /// Bridge a note from another federation by presenting a portable spending proof.
    ///
    /// When processed:
    /// 1. Verify the portable note proof against trusted federation roots.
    /// 2. Check the nullifier hasn't already been bridged (prevent double-bridge).
    /// 3. Create a new note commitment in the local note tree.
    /// 4. Credit the value to the receiving cell.
    BridgeMint {
        /// The portable proof carrying the STARK spending proof from the source federation.
        portable_proof: PortableNoteProof,
    },
    /// Phase 1: Lock a note for cross-federation bridge transfer.
    ///
    /// Instead of immediately burning the note, this creates a conditional lock.
    /// The note cannot be spent or re-locked until the bridge is finalized or cancelled.
    /// If the destination federation is offline or refuses, the note can be recovered
    /// after the timeout.
    BridgeLock {
        /// The nullifier of the note being locked.
        nullifier: [u8; 32],
        /// The destination federation's identity.
        destination: [u8; 32],
        /// The value being bridged.
        value: u64,
        /// The asset type being bridged.
        asset_type: u64,
        /// Block height at which this lock expires (can be cancelled after).
        timeout_height: u64,
        /// The serialized spending proof for destination to verify.
        spending_proof: Vec<u8>,
    },
    /// Phase 3: Finalize a bridge by presenting a valid receipt from the destination.
    ///
    /// The receipt proves the destination federation minted the value. On success,
    /// the note's nullifier becomes permanently spent.
    BridgeFinalize {
        /// The nullifier of the pending bridge to finalize.
        nullifier: [u8; 32],
        /// The signed receipt from the destination federation.
        receipt: BridgeReceipt,
    },
    /// Phase 4: Cancel a bridge after the timeout has expired.
    ///
    /// If the bridge was not finalized before the timeout height, the note is
    /// unlocked and returned to the owner. Prevents value-trapping when the
    /// destination federation is offline or refuses the bridge.
    BridgeCancel {
        /// The nullifier of the pending bridge to cancel.
        nullifier: [u8; 32],
    },
    /// Pipelined send: dispatch an action to the result of a pending turn.
    /// Three-party introduction.
    Introduce {
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        permissions: pyana_cell::AuthRequired,
    },
    PipelinedSend {
        /// The eventual target — resolved during pipeline execution.
        target: crate::eventual::EventualRef,
        /// The action to send to the resolved target.
        action: Box<Action>,
    },
    /// Create a bonded proof obligation: the actor commits to delivering a proof
    /// satisfying `condition` before `deadline_height`, with `stake` locked as bond.
    /// If the proof is not delivered, the stake is slashed to the beneficiary.
    CreateObligation {
        /// Who benefits (receives stake on failure, or whose ConditionalTurn resolves).
        beneficiary: CellId,
        /// What must be proven.
        condition: ProofCondition,
        /// Federation height deadline.
        deadline_height: u64,
        /// Note commitment representing the locked stake.
        stake: NoteCommitment,
        /// Numeric amount to lock from the obligor's cell balance as bond.
        /// This is subtracted on creation, returned on fulfillment, or transferred
        /// to the beneficiary on slash.
        stake_amount: u64,
    },
    /// Fulfill a proof obligation by presenting the required proof.
    /// On success, the locked stake is returned to the obligor.
    FulfillObligation {
        /// ID of the obligation being fulfilled.
        obligation_id: [u8; 32],
        /// The proof satisfying the obligation's condition.
        proof: ConditionProof,
    },
    /// Slash an expired obligation: transfer the locked stake to the beneficiary.
    /// Only valid after the obligation's deadline has passed without fulfillment.
    SlashObligation {
        /// ID of the obligation to slash.
        obligation_id: [u8; 32],
    },
    /// Create a conditional escrow: lock value from the sender, release to recipient
    /// if `condition` is met, else allow refund after `timeout_height`.
    CreateEscrow {
        /// The escrow creator (funds source).
        cell: CellId,
        /// Who gets the funds if condition is met.
        recipient: CellId,
        /// Amount to lock in escrow.
        amount: u64,
        /// What must be satisfied for release.
        condition: EscrowCondition,
        /// Block height after which refund is allowed.
        timeout_height: u64,
        /// Unique identifier for this escrow.
        escrow_id: [u8; 32],
    },
    /// Release an escrow by satisfying its condition.
    /// Transfers the escrowed amount to the recipient.
    ReleaseEscrow {
        /// ID of the escrow to release.
        escrow_id: [u8; 32],
        /// Proof satisfying the condition (if condition requires one).
        proof: Option<Vec<u8>>,
    },
    /// Refund an escrow after its timeout has passed.
    /// Returns the escrowed amount to the original creator.
    RefundEscrow {
        /// ID of the escrow to refund.
        escrow_id: [u8; 32],
    },
    /// Create a privacy-preserving committed escrow.
    ///
    /// All party identities and the value are hidden behind cryptographic commitments.
    /// The range proof must demonstrate the committed value is in `[0, 2^64)`.
    /// The value commitment encodes the actual locked amount (verified via range proof),
    /// and the corresponding cleartext amount is deducted from the creator's balance.
    CreateCommittedEscrow {
        /// Commitment to the creator's identity (BLAKE3 of CellId + blinding).
        creator_commitment: [u8; 32],
        /// Commitment to the recipient's identity (BLAKE3 of CellId + blinding).
        recipient_commitment: [u8; 32],
        /// Pedersen commitment to the escrowed value (compressed Ristretto).
        value_commitment: ValueCommitmentBytes,
        /// Commitment to the escrow condition (BLAKE3 of condition + nonce).
        condition_commitment: [u8; 32],
        /// Block height after which refund is allowed (public for enforcement).
        timeout_height: u64,
        /// Deterministic escrow ID (derived from commitments).
        escrow_id: [u8; 32],
        /// Range proof showing the committed value is in [0, 2^64).
        range_proof: Vec<u8>,
        /// The actual amount to lock (must match the value commitment opening).
        /// This is needed to deduct from the creator's balance; the commitment
        /// binds this value cryptographically via the range proof.
        amount: u64,
    },
    /// Release a committed escrow by proving recipient identity.
    ///
    /// The claimer proves they are the recipient by revealing the opening of the
    /// recipient_commitment and signing the escrow_id. In the initial implementation
    /// this is a signed statement; a future version will accept a ZK presentation
    /// proof bound to the escrow_id.
    ReleaseCommittedEscrow {
        /// ID of the committed escrow to release.
        escrow_id: [u8; 32],
        /// Authorization proving the claimer is the committed recipient.
        claim_auth: EscrowClaimAuth,
        /// The recipient CellId to credit (must match the claim_auth opening).
        recipient: CellId,
    },
    /// Refund a committed escrow after timeout by proving creator identity.
    ///
    /// The creator proves their identity by revealing the opening of the
    /// creator_commitment and signing the escrow_id.
    RefundCommittedEscrow {
        /// ID of the committed escrow to refund.
        escrow_id: [u8; 32],
        /// Authorization proving the claimer is the committed creator.
        claim_auth: EscrowClaimAuth,
        /// The creator CellId to credit (must match the claim_auth opening).
        creator: CellId,
    },
    /// Exercise a capability from the actor's c-list in one atomic step.
    ///
    /// This is the categorical "evaluation map" (eval: B^A x A -> B): look up a
    /// capability by slot, verify permissions, and execute inner effects against
    /// the capability's target cell. Combines c-list lookup + sub-action into a
    /// single effect, eliminating the two-step lookup-then-submit pattern.
    ExerciseViaCapability {
        /// Which slot in the actor's c-list to exercise.
        cap_slot: u32,
        /// The effects to perform on the target cell (resolved from the capability).
        inner_effects: Vec<Effect>,
    },
    /// Transition a hosted cell to sovereign mode.
    ///
    /// When executed: moves the cell from `cells` to `sovereign_commitments`
    /// (stores only the 32-byte state commitment, deletes the full state).
    /// The agent becomes responsible for maintaining and providing cell state.
    MakeSovereign {
        /// The cell to make sovereign.
        cell: CellId,
    },
    /// Create a new cell from a deployed factory.
    ///
    /// The factory's constraints are validated against the creation parameters.
    /// On success, the new cell is created with the specified program, capabilities,
    /// initial state, and provenance recording which factory created it.
    CreateCellFromFactory {
        /// The factory VK hash identifying which factory to use.
        factory_vk: [u8; 32],
        /// Owner public key for the new cell.
        owner_pubkey: [u8; 32],
        /// Token domain for the new cell.
        token_id: [u8; 32],
        /// Creation parameters (validated against factory descriptor).
        params: pyana_cell::factory::FactoryCreationParams,
    },

    // ─── Queue Operations ─────────────────────────────────────────────────────
    /// Allocate a new queue with specified capacity.
    /// Costs: capacity * cost_per_slot computrons from the agent's balance.
    /// The new queue is represented as a cell with queue metadata in its state fields.
    QueueAllocate {
        /// Capacity (max entries).
        capacity: u64,
        /// Optional program VK hash (for programmable queues).
        program_vk: Option<[u8; 32]>,
    },

    /// Enqueue a message to a queue.
    /// Sender pays deposit (anti-spam, refundable on dequeue).
    QueueEnqueue {
        /// Target queue (cell ID of the queue cell).
        queue: CellId,
        /// Content hash of the message (the message itself is delivered out-of-band).
        message_hash: [u8; 32],
        /// Deposit amount (computrons).
        deposit: u64,
    },

    /// Dequeue the next message from a queue (FIFO consumption).
    /// Only the queue owner can dequeue.
    QueueDequeue {
        /// Queue to dequeue from.
        queue: CellId,
    },

    /// Resize a queue (change capacity).
    /// Growing costs additional computrons. Shrinking is free (but can't shrink below current occupancy).
    QueueResize {
        /// Queue cell to resize.
        queue: CellId,
        /// New capacity.
        new_capacity: u64,
    },

    /// Execute an atomic cross-queue transaction.
    /// All operations succeed or all are rolled back.
    QueueAtomicTx {
        /// The operations to perform atomically.
        operations: Vec<QueueTxOp>,
    },

    /// Execute a pipeline step: dequeue from source, route through pipeline, enqueue to sink(s).
    QueuePipelineStep {
        /// Pipeline identity (content-addressed from stage descriptions).
        pipeline_id: [u8; 32],
        /// Source queue.
        source: CellId,
        /// Sink queue(s) — pipeline determines routing.
        sinks: Vec<CellId>,
    },

    // ─── CapTP Runtime Effects (Stage 7 / P1.A) ───────────────────────────
    //
    // The wire layer's CapTP handlers used to mutate `CapTpState` directly
    // (see `wire/src/server.rs` :2243-2350). With these variants present,
    // each CapTP operation becomes a turn-submitted Effect that runs through
    // the executor and projects to its respective AIR variant (selectors
    // 14..17 in `circuit/src/effect_vm.rs`).
    //
    // Field shapes are deliberately minimal here. The richer
    // `SwissMembershipProof` / `RefcountMembershipProof` /
    // `ApprovedHandoffProof` types proposed in `DESIGN-captp-integration.md`
    // remain available for a future expansion; for now the executor reads
    // membership witnesses from the federation's mirror state.
    /// Export a cell as a sturdy reference (CapTP). The executor inserts a
    /// swiss-table entry, derives the swiss number, and bumps the cell's
    /// export counter (state.fields[7]).
    ExportSturdyRef {
        /// 32-byte unguessable swiss number (or seed; the on-chain effect
        /// commits to the exact swiss number used for routing).
        swiss_number: [u8; 32],
        /// The cell being exported (the bearer of the sturdy ref talks to
        /// THIS cell when enlivening).
        target: CellId,
    },
    /// Enliven a sturdy ref: validate a presented swiss number against the
    /// committed swiss-table state and grant a routing entry to `bearer`.
    /// The executor verifies membership of `swiss_number` in the target's
    /// swiss table and bumps the entry's use-count (state.fields[6]).
    EnlivenRef {
        /// The swiss number being presented.
        swiss_number: [u8; 32],
        /// The cell that ends up holding the live ref (gets the routing
        /// entry added to its c-list).
        bearer: CellId,
    },
    /// Drop a remote reference / GC decrement (CapTP). The executor verifies
    /// the refcount is > 0 and decrements it (state.fields[5]).
    DropRef {
        /// 32-byte identifier of the reference being dropped (per-export id).
        ref_id: [u8; 32],
    },
    /// **Categorical dual of acting-effects: proof of *non-action*.**
    ///
    /// A `Refusal` is a structural artifact that the prover did *not*
    /// take action `offered_action_commitment` within some window.
    /// This is NOT a cancellation (which would mutate the cancelled
    /// action) — it is *evidence of absence*, the categorical
    /// "initial object" in the Effect category that
    /// `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3 / §9.2.2` names.
    ///
    /// **App drivers:**
    /// - *Auditable rejection in HFT-style flows.* "I received an
    ///   order; I declined to fill; here is the proof I declined and
    ///   the reason." Silence is otherwise indistinguishable from
    ///   outage; a `Refusal` makes the rejection a first-class on-
    ///   chain artifact.
    /// - *Non-repudiation of timely response.* The receiver
    ///   committed, on-chain, to having considered (and declined) a
    ///   specific offer-commitment within a window.
    /// - *Compliance: "I did not bid above X within block-range
    ///   [a, b]."* The proof binds the *absence* of a matching
    ///   action under the prover's identity within the window.
    ///
    /// **How the proof works.** Proving a *negative* is hard; the
    /// proof references a `proof_witness_index` into the action's
    /// `witness_blobs`, and the carried bytes are one of:
    /// - A *receipt-chain scan witness* — postcard-encoded receipt
    ///   chain of every turn the prover authored within the window,
    ///   plus an inclusion-completeness proof that no other turn
    ///   exists. The verifier checks none match
    ///   `offered_action_commitment`.
    /// - A *bloom-filter non-membership proof* against an
    ///   offered-actions registry; the witnessed-predicate verifier
    ///   dispatches by `WitnessedPredicateKind::NonMembership` on
    ///   the registry's sorted-set root.
    /// - A *custom non-action AIR* the app registers via
    ///   `WitnessedPredicateKind::Custom`.
    ///
    /// The choice is left to the app — the executor only validates
    /// the carried witness through the
    /// `WitnessedPredicateRegistry`, treating the `Refusal` as a
    /// state-mutating effect that bumps the target cell's nonce and
    /// records the refusal commitment + reason for auditability.
    Refusal {
        /// The cell whose history attests to the non-action.
        ///
        /// The refusal is anchored to a specific cell — its nonce
        /// bumps, its refusal-log slot (cell-specific; typically the
        /// "audit" slot) records `(offered_action_commitment,
        /// refusal_reason)`. Cross-cell refusals chain through
        /// multiple `Refusal` effects.
        cell: CellId,
        /// 32-byte commitment to the (action, offerer, window) tuple
        /// the prover is refusing. Typically `blake3("pyana-offered-
        /// action-v1" || offerer || action_bytes || window_start ||
        /// window_end)`. The verifier of the carried non-action
        /// witness checks the witness binds to this commitment.
        offered_action_commitment: [u8; 32],
        /// Why the prover refused.
        refusal_reason: RefusalReason,
        /// Index into `Action::witness_blobs` carrying the non-action
        /// proof bytes. The witness is verified via the
        /// `WitnessedPredicateRegistry` keyed on a kind chosen by
        /// the app (typically `NonMembership` against an offered-
        /// actions registry root; or a `Custom` non-action AIR).
        ///
        /// The witness verifier's commitment is implicitly
        /// `offered_action_commitment` — i.e. the verifier checks
        /// that the carried proof binds the absence to *this*
        /// specific offered action.
        proof_witness_index: u32,
    },
    /// Validate a handoff certificate and accept the bearer (CapTP).
    /// Off-chain Ed25519 signature verification has already happened (the
    /// federation maintains `approved_handoffs_root`); the executor proves
    /// Merkle membership of `cert_hash` in the root and consumes the leaf
    /// (single-use guarantee per `DESIGN-captp-integration.md` §9.4).
    ValidateHandoff {
        /// The Poseidon2 hash of the handoff certificate (matches the leaf
        /// the federation inserted when accepting the cert).
        cert_hash: [u8; 32],
    },
}

/// Why a [`Effect::Refusal`] was issued. Refusals are *evidence of
/// absence*, but the reason field gives downstream auditors a
/// structured signal beyond raw non-action.
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RefusalReason {
    /// The prover deliberately declined the offered action — explicit
    /// rejection (e.g. "the price was wrong").
    Declined,
    /// The prover lacked authority to take the action (e.g. cap
    /// revoked, facet disallows). Distinct from `Declined` because
    /// the failure is structural rather than discretionary.
    NoAuthority,
    /// The window during which the offered action was valid has
    /// expired before the prover could (or would) act.
    WindowExpired,
    /// App-specific reason — the 32-byte commitment is opaque to the
    /// substrate; apps decode via their `CustomEffectVerifier` or by
    /// pairing this with an `EmitEvent` carrying the decoded reason.
    Custom { reason_hash: [u8; 32] },
}

/// An operation within an atomic queue transaction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum QueueTxOp {
    /// Enqueue a message as part of an atomic transaction.
    Enqueue {
        queue: CellId,
        message_hash: [u8; 32],
        deposit: u64,
    },
    /// Dequeue a message as part of an atomic transaction.
    Dequeue { queue: CellId },
}

/// An event emitted by an action.
///
/// Events are logged in the receipt but do not modify ledger state.
/// They are indexed by topic for off-chain consumption.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Event {
    /// The topic of this event (hashed method/event name).
    pub topic: Symbol,
    /// Arbitrary data fields.
    pub data: Vec<FieldElement>,
}

impl Action {
    /// Compute the BLAKE3 hash of this action (for Merkle tree inclusion).
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevents type confusion with other hash preimages.
        hasher.update(b"pyana-action-v2:");
        hasher.update(self.target.as_bytes());
        hasher.update(&self.method);
        for arg in &self.args {
            hasher.update(arg);
        }
        // Hash authorization discriminant + data.
        match &self.authorization {
            Authorization::Signature(r, s) => {
                hasher.update(&[0u8]);
                hasher.update(r);
                hasher.update(s);
            }
            Authorization::Proof {
                proof_bytes,
                bound_action,
                bound_resource,
            } => {
                hasher.update(&[1u8]);
                hasher.update(proof_bytes);
                hasher.update(bound_action.as_bytes());
                hasher.update(bound_resource.as_bytes());
            }
            Authorization::Breadstuff(token) => {
                hasher.update(&[2u8]);
                hasher.update(token);
            }
            Authorization::Bearer(proof) => {
                hasher.update(&[4u8]);
                hasher.update(proof.target.as_bytes());
                hasher.update(&proof.expires_at.to_le_bytes());
                match &proof.delegation_proof {
                    DelegationProofData::SignedDelegation {
                        delegator_pk,
                        signature,
                        bearer_pk,
                    } => {
                        hasher.update(&[0u8]);
                        hasher.update(delegator_pk);
                        hasher.update(signature);
                        hasher.update(bearer_pk);
                    }
                    DelegationProofData::StarkDelegation {
                        proof_bytes,
                        root_issuer_commitment,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
                        hasher.update(proof_bytes);
                        hasher.update(root_issuer_commitment);
                    }
                }
                if let Some(rc) = &proof.revocation_channel {
                    hasher.update(&[1u8]);
                    hasher.update(rc);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Authorization::Unchecked => {
                hasher.update(&[3u8]);
            }
            Authorization::CapTpDelivered {
                handoff_cert,
                introducer_pk,
                sender_pk,
                sender_signature,
            } => {
                hasher.update(&[5u8]);
                // Hash the cert's signing message (covers all cert fields) + its
                // signature, plus the sender pk and signature.
                let cert_msg = handoff_cert.signing_message();
                hasher.update(&(cert_msg.len() as u64).to_le_bytes());
                hasher.update(&cert_msg);
                hasher.update(&handoff_cert.introducer_signature.0);
                hasher.update(introducer_pk);
                hasher.update(sender_pk);
                hasher.update(sender_signature);
            }
            Authorization::Custom { predicate } => {
                hasher.update(&[6u8]);
                // Hash the predicate's structural shape so a tampering
                // executor can't substitute a different predicate
                // (different kind, commitment, input_ref, or proof
                // index) under the same signed-turn envelope. Use
                // postcard for a canonical byte encoding that's
                // forward-compatible with the kind enum.
                let pred_bytes = postcard::to_allocvec(predicate).unwrap_or_default();
                hasher.update(&(pred_bytes.len() as u64).to_le_bytes());
                hasher.update(&pred_bytes);
            }
            Authorization::OneOf {
                candidates,
                proof_index,
            } => {
                hasher.update(&[7u8]);
                hasher.update(&proof_index.to_le_bytes());
                hasher.update(&(candidates.len() as u64).to_le_bytes());
                // Bind the entire candidate list into the hash so a
                // tampering executor can't shuffle / add / remove
                // candidates after signing. We use postcard for a
                // canonical byte encoding — `Authorization` already
                // derives Serialize.
                let cand_bytes = postcard::to_allocvec(candidates).unwrap_or_default();
                hasher.update(&(cand_bytes.len() as u64).to_le_bytes());
                hasher.update(&cand_bytes);
            }
        }
        // Hash delegation mode.
        hasher.update(&[self.may_delegate as u8]);
        // Hash commitment mode.
        hasher.update(&[self.commitment_mode as u8]);
        // Hash balance_change.
        if let Some(delta) = self.balance_change {
            hasher.update(&[1u8]); // discriminant: Some
            hasher.update(&delta.to_le_bytes());
        } else {
            hasher.update(&[0u8]); // discriminant: None
        }
        // Hash effects.
        for effect in &self.effects {
            hasher.update(&effect.hash());
        }
        // Hash preconditions to prevent downgrade attacks where an attacker removes
        // preconditions (e.g., minimum balance guards) from a signed action.
        let preconds_bytes = postcard::to_allocvec(&self.preconditions).unwrap_or_default();
        hasher.update(&preconds_bytes);
        // Hash witness_blobs (Cav-Codex Block 3) so a tampering verifier
        // can't strip or substitute the witness payloads a signed action
        // committed to. Empty vec hashes to the length prefix only; this
        // is byte-equivalent to actions that were signed before this
        // field was added (Turn v3 preimage extension).
        hasher.update(&(self.witness_blobs.len() as u64).to_le_bytes());
        for wb in &self.witness_blobs {
            let kind_disc: u8 = match wb.kind {
                WitnessKind::Preimage32 => 0,
                WitnessKind::MerklePath => 1,
                WitnessKind::RateLimitCount => 2,
                WitnessKind::ProofBytes => 3,
                WitnessKind::Cleartext => 4,
            };
            hasher.update(&[kind_disc]);
            hasher.update(&(wb.bytes.len() as u64).to_le_bytes());
            hasher.update(&wb.bytes);
        }
        *hasher.finalize().as_bytes()
    }
}

impl Effect {
    /// Compute the BLAKE3 hash of this effect.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        match self {
            Effect::SetField { cell, index, value } => {
                hasher.update(&[0u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&(*index as u64).to_le_bytes());
                hasher.update(value);
            }
            Effect::Transfer { from, to, amount } => {
                hasher.update(&[1u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(&amount.to_le_bytes());
            }
            Effect::GrantCapability { from, to, cap } => {
                hasher.update(&[2u8]);
                hasher.update(from.as_bytes());
                hasher.update(to.as_bytes());
                hasher.update(cap.target.as_bytes());
                hasher.update(&cap.slot.to_le_bytes());
            }
            Effect::RevokeCapability { cell, slot } => {
                hasher.update(&[3u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&slot.to_le_bytes());
            }
            Effect::EmitEvent { cell, event } => {
                hasher.update(&[4u8]);
                hasher.update(cell.as_bytes());
                hasher.update(&event.topic);
                for d in &event.data {
                    hasher.update(d);
                }
            }
            Effect::IncrementNonce { cell } => {
                hasher.update(&[5u8]);
                hasher.update(cell.as_bytes());
            }
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => {
                hasher.update(&[6u8]);
                hasher.update(public_key);
                hasher.update(token_id);
                hasher.update(&balance.to_le_bytes());
            }
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => {
                hasher.update(&[7u8]);
                hasher.update(cell.as_bytes());
                // Hash each permission field's discriminant.
                let perms = [
                    &new_permissions.send,
                    &new_permissions.receive,
                    &new_permissions.set_state,
                    &new_permissions.set_permissions,
                    &new_permissions.set_verification_key,
                    &new_permissions.increment_nonce,
                    &new_permissions.delegate,
                    &new_permissions.access,
                ];
                for p in perms {
                    match p {
                        pyana_cell::AuthRequired::None => {
                            hasher.update(&[0u8]);
                        }
                        pyana_cell::AuthRequired::Signature => {
                            hasher.update(&[1u8]);
                        }
                        pyana_cell::AuthRequired::Proof => {
                            hasher.update(&[2u8]);
                        }
                        pyana_cell::AuthRequired::Either => {
                            hasher.update(&[3u8]);
                        }
                        pyana_cell::AuthRequired::Impossible => {
                            hasher.update(&[4u8]);
                        }
                        pyana_cell::AuthRequired::Custom { vk_hash } => {
                            hasher.update(&[5u8]);
                            hasher.update(vk_hash);
                        }
                    }
                }
            }
            Effect::SetVerificationKey { cell, new_vk } => {
                hasher.update(&[8u8]);
                hasher.update(cell.as_bytes());
                if let Some(vk) = new_vk {
                    hasher.update(&[1u8]);
                    hasher.update(&vk.data);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                asset_type,
                spending_proof,
                value_commitment,
            } => {
                hasher.update(&[9u8]);
                hasher.update(&nullifier.0);
                hasher.update(note_tree_root);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(spending_proof);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::NoteCreate {
                commitment,
                value,
                asset_type,
                encrypted_note,
                value_commitment,
                range_proof,
            } => {
                hasher.update(&[10u8]);
                hasher.update(&commitment.0);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&(encrypted_note.len() as u64).to_le_bytes());
                hasher.update(encrypted_note);
                match value_commitment {
                    Some(vc) => {
                        hasher.update(&[1u8]);
                        hasher.update(vc);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                match range_proof {
                    Some(rp) => {
                        hasher.update(&[1u8]);
                        hasher.update(&(rp.len() as u64).to_le_bytes());
                        hasher.update(rp);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::CreateSealPair {
                sealer_holder,
                unsealer_holder,
            } => {
                hasher.update(&[13u8]);
                hasher.update(sealer_holder.as_bytes());
                hasher.update(unsealer_holder.as_bytes());
            }
            Effect::Seal {
                pair_id,
                capability,
            } => {
                hasher.update(&[14u8]);
                hasher.update(pair_id);
                hasher.update(capability.target.as_bytes());
                hasher.update(&capability.slot.to_le_bytes());
            }
            Effect::Unseal {
                sealed_box,
                recipient,
            } => {
                hasher.update(&[15u8]);
                hasher.update(&sealed_box.pair_id);
                hasher.update(&sealed_box.ephemeral_public);
                hasher.update(&sealed_box.commitment);
                hasher.update(&sealed_box.nonce);
                hasher.update(recipient.as_bytes());
            }
            Effect::BridgeMint { portable_proof } => {
                hasher.update(&[21u8]);
                hasher.update(&portable_proof.nullifier);
                hasher.update(&portable_proof.destination_commitment.0);
                hasher.update(&portable_proof.value.to_le_bytes());
                hasher.update(&portable_proof.asset_type.to_le_bytes());
                hasher.update(&portable_proof.source_root.merkle_root);
                hasher.update(&portable_proof.source_root.height.to_le_bytes());
            }
            Effect::BridgeLock {
                nullifier,
                destination,
                value,
                asset_type,
                timeout_height,
                spending_proof,
            } => {
                hasher.update(&[26u8]);
                hasher.update(nullifier);
                hasher.update(destination);
                hasher.update(&value.to_le_bytes());
                hasher.update(&asset_type.to_le_bytes());
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(&(spending_proof.len() as u64).to_le_bytes());
                hasher.update(spending_proof);
            }
            Effect::BridgeFinalize { nullifier, receipt } => {
                hasher.update(&[27u8]);
                hasher.update(nullifier);
                hasher.update(&receipt.nullifier);
                hasher.update(&receipt.destination_federation);
                hasher.update(&receipt.mint_height.to_le_bytes());
                hasher.update(&receipt.signature);
            }
            Effect::BridgeCancel { nullifier } => {
                hasher.update(&[28u8]);
                hasher.update(nullifier);
            }
            Effect::Introduce {
                introducer,
                recipient,
                target,
                permissions,
            } => {
                hasher.update(&[17u8]);
                hasher.update(introducer.as_bytes());
                hasher.update(recipient.as_bytes());
                hasher.update(target.as_bytes());
                match permissions {
                    pyana_cell::AuthRequired::None => {
                        hasher.update(&[0u8]);
                    }
                    pyana_cell::AuthRequired::Signature => {
                        hasher.update(&[1u8]);
                    }
                    pyana_cell::AuthRequired::Proof => {
                        hasher.update(&[2u8]);
                    }
                    pyana_cell::AuthRequired::Either => {
                        hasher.update(&[3u8]);
                    }
                    pyana_cell::AuthRequired::Impossible => {
                        hasher.update(&[4u8]);
                    }
                    pyana_cell::AuthRequired::Custom { vk_hash } => {
                        hasher.update(&[5u8]);
                        hasher.update(vk_hash);
                    }
                }
            }
            Effect::PipelinedSend { target, action } => {
                hasher.update(&[16u8]);
                hasher.update(&target.source_turn);
                hasher.update(&target.output_slot.to_le_bytes());
                hasher.update(&action.hash());
            }
            Effect::CreateObligation {
                beneficiary,
                condition,
                deadline_height,
                stake,
                stake_amount,
            } => {
                hasher.update(&[22u8]);
                hasher.update(beneficiary.as_bytes());
                hasher.update(&deadline_height.to_le_bytes());
                hasher.update(&stake.0);
                hasher.update(&stake_amount.to_le_bytes());
                // Include condition discriminant.
                match condition {
                    ProofCondition::HashPreimage { hash } => {
                        hasher.update(&[0u8]);
                        hasher.update(hash);
                    }
                    ProofCondition::RemoteProof {
                        federation_root,
                        expected_air,
                        expected_conclusion,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(federation_root);
                        hasher.update(expected_air.as_bytes());
                        hasher.update(&expected_conclusion.to_le_bytes());
                    }
                    ProofCondition::LocalProof {
                        expected_air,
                        expected_public_inputs,
                    } => {
                        hasher.update(&[2u8]);
                        hasher.update(expected_air.as_bytes());
                        for pi in expected_public_inputs {
                            hasher.update(&pi.to_le_bytes());
                        }
                    }
                    ProofCondition::TurnExecuted { turn_hash } => {
                        hasher.update(&[3u8]);
                        hasher.update(turn_hash);
                    }
                }
            }
            Effect::FulfillObligation {
                obligation_id,
                proof,
            } => {
                hasher.update(&[23u8]);
                hasher.update(obligation_id);
                match proof {
                    ConditionProof::Preimage(preimage) => {
                        hasher.update(&[0u8]);
                        hasher.update(preimage);
                    }
                    ConditionProof::StarkProof {
                        proof_bytes,
                        federation_root,
                        public_outputs,
                        air_name,
                    } => {
                        hasher.update(&[1u8]);
                        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
                        hasher.update(proof_bytes);
                        hasher.update(federation_root);
                        for po in public_outputs {
                            hasher.update(&po.to_le_bytes());
                        }
                        hasher.update(air_name.as_bytes());
                    }
                    ConditionProof::Receipt(receipt) => {
                        hasher.update(&[2u8]);
                        hasher.update(&receipt.turn_hash);
                    }
                }
            }
            Effect::SlashObligation { obligation_id } => {
                hasher.update(&[24u8]);
                hasher.update(obligation_id);
            }
            Effect::CreateEscrow {
                cell,
                recipient,
                amount,
                condition,
                timeout_height,
                escrow_id,
            } => {
                hasher.update(&[29u8]);
                hasher.update(cell.as_bytes());
                hasher.update(recipient.as_bytes());
                hasher.update(&amount.to_le_bytes());
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(escrow_id);
                match condition {
                    EscrowCondition::ProofPresented { verification_key } => {
                        hasher.update(&[0u8]);
                        hasher.update(verification_key);
                    }
                    EscrowCondition::SignedByAll { signers } => {
                        hasher.update(&[1u8]);
                        for signer in signers {
                            hasher.update(signer);
                        }
                    }
                    EscrowCondition::PredicateSatisfied { predicate_hash } => {
                        hasher.update(&[2u8]);
                        hasher.update(predicate_hash);
                    }
                }
            }
            Effect::ReleaseEscrow { escrow_id, proof } => {
                hasher.update(&[30u8]);
                hasher.update(escrow_id);
                if let Some(p) = proof {
                    hasher.update(&[1u8]);
                    hasher.update(&(p.len() as u64).to_le_bytes());
                    hasher.update(p);
                } else {
                    hasher.update(&[0u8]);
                }
            }
            Effect::RefundEscrow { escrow_id } => {
                hasher.update(&[31u8]);
                hasher.update(escrow_id);
            }
            Effect::CreateCommittedEscrow {
                creator_commitment,
                recipient_commitment,
                value_commitment,
                condition_commitment,
                timeout_height,
                escrow_id,
                range_proof,
                amount,
            } => {
                hasher.update(&[32u8]);
                hasher.update(creator_commitment);
                hasher.update(recipient_commitment);
                hasher.update(&value_commitment.0);
                hasher.update(condition_commitment);
                hasher.update(&timeout_height.to_le_bytes());
                hasher.update(escrow_id);
                hasher.update(&(range_proof.len() as u64).to_le_bytes());
                hasher.update(range_proof);
                hasher.update(&amount.to_le_bytes());
            }
            Effect::ReleaseCommittedEscrow {
                escrow_id,
                claim_auth,
                recipient,
            } => {
                hasher.update(&[33u8]);
                hasher.update(escrow_id);
                hasher.update(claim_auth.cell_id.as_bytes());
                hasher.update(&claim_auth.blinding);
                hasher.update(&claim_auth.signature);
                hasher.update(recipient.as_bytes());
            }
            Effect::RefundCommittedEscrow {
                escrow_id,
                claim_auth,
                creator,
            } => {
                hasher.update(&[34u8]);
                hasher.update(escrow_id);
                hasher.update(claim_auth.cell_id.as_bytes());
                hasher.update(&claim_auth.blinding);
                hasher.update(&claim_auth.signature);
                hasher.update(creator.as_bytes());
            }
            Effect::SpawnWithDelegation {
                child_public_key,
                child_token_id,
                max_staleness,
            } => {
                hasher.update(&[18u8]);
                hasher.update(child_public_key);
                hasher.update(child_token_id);
                hasher.update(&max_staleness.to_le_bytes());
            }
            Effect::RefreshDelegation => {
                hasher.update(&[19u8]);
            }
            Effect::RevokeDelegation { child } => {
                hasher.update(&[20u8]);
                hasher.update(child.as_bytes());
            }
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => {
                hasher.update(&[25u8]);
                hasher.update(&cap_slot.to_le_bytes());
                for inner in inner_effects {
                    hasher.update(&inner.hash());
                }
            }
            Effect::MakeSovereign { cell } => {
                hasher.update(&[35u8]);
                hasher.update(cell.as_bytes());
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            } => {
                hasher.update(&[36u8]);
                hasher.update(factory_vk);
                hasher.update(owner_pubkey);
                hasher.update(token_id);
                // Hash params deterministically.
                let mode_byte = match params.mode {
                    pyana_cell::CellMode::Hosted => 0u8,
                    pyana_cell::CellMode::Sovereign => 1u8,
                };
                hasher.update(&[mode_byte]);
                match &params.program_vk {
                    Some(vk) => {
                        hasher.update(&[1u8]);
                        hasher.update(vk);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
                hasher.update(&(params.initial_fields.len() as u64).to_le_bytes());
                for (idx, val) in &params.initial_fields {
                    hasher.update(&idx.to_le_bytes());
                    hasher.update(&val.to_le_bytes());
                }
                hasher.update(&(params.initial_caps.len() as u64).to_le_bytes());
                hasher.update(&params.owner_pubkey);
            }
            Effect::QueueAllocate {
                capacity,
                program_vk,
            } => {
                hasher.update(&[37u8]);
                hasher.update(&capacity.to_le_bytes());
                match program_vk {
                    Some(vk) => {
                        hasher.update(&[1u8]);
                        hasher.update(vk);
                    }
                    None => {
                        hasher.update(&[0u8]);
                    }
                }
            }
            Effect::QueueEnqueue {
                queue,
                message_hash,
                deposit,
            } => {
                hasher.update(&[38u8]);
                hasher.update(queue.as_bytes());
                hasher.update(message_hash);
                hasher.update(&deposit.to_le_bytes());
            }
            Effect::QueueDequeue { queue } => {
                hasher.update(&[39u8]);
                hasher.update(queue.as_bytes());
            }
            Effect::QueueResize {
                queue,
                new_capacity,
            } => {
                hasher.update(&[40u8]);
                hasher.update(queue.as_bytes());
                hasher.update(&new_capacity.to_le_bytes());
            }
            Effect::QueueAtomicTx { operations } => {
                hasher.update(&[41u8]);
                hasher.update(&(operations.len() as u64).to_le_bytes());
                for op in operations {
                    match op {
                        QueueTxOp::Enqueue {
                            queue,
                            message_hash,
                            deposit,
                        } => {
                            hasher.update(&[0u8]);
                            hasher.update(queue.as_bytes());
                            hasher.update(message_hash);
                            hasher.update(&deposit.to_le_bytes());
                        }
                        QueueTxOp::Dequeue { queue } => {
                            hasher.update(&[1u8]);
                            hasher.update(queue.as_bytes());
                        }
                    }
                }
            }
            Effect::QueuePipelineStep {
                pipeline_id,
                source,
                sinks,
            } => {
                hasher.update(&[42u8]);
                hasher.update(pipeline_id);
                hasher.update(source.as_bytes());
                hasher.update(&(sinks.len() as u64).to_le_bytes());
                for sink in sinks {
                    hasher.update(sink.as_bytes());
                }
            }
            // ── CapTP runtime effects (Stage 7 / P1.A) ────────────────────
            Effect::ExportSturdyRef {
                swiss_number,
                target,
            } => {
                hasher.update(&[43u8]);
                hasher.update(swiss_number);
                hasher.update(target.as_bytes());
            }
            Effect::EnlivenRef {
                swiss_number,
                bearer,
            } => {
                hasher.update(&[44u8]);
                hasher.update(swiss_number);
                hasher.update(bearer.as_bytes());
            }
            Effect::DropRef { ref_id } => {
                hasher.update(&[45u8]);
                hasher.update(ref_id);
            }
            Effect::ValidateHandoff { cert_hash } => {
                hasher.update(&[46u8]);
                hasher.update(cert_hash);
            }
            Effect::Refusal {
                cell,
                offered_action_commitment,
                refusal_reason,
                proof_witness_index,
            } => {
                hasher.update(&[47u8]);
                hasher.update(cell.as_bytes());
                hasher.update(offered_action_commitment);
                match refusal_reason {
                    RefusalReason::Declined => hasher.update(&[0u8]),
                    RefusalReason::NoAuthority => hasher.update(&[1u8]),
                    RefusalReason::WindowExpired => hasher.update(&[2u8]),
                    RefusalReason::Custom { reason_hash } => {
                        hasher.update(&[3u8]);
                        hasher.update(reason_hash);
                    }
                }
                hasher.update(&proof_witness_index.to_le_bytes());
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Return the number of bytes of data in this effect (for cost estimation).
    pub fn data_bytes(&self) -> usize {
        match self {
            Effect::SetField { .. } => 32 + 8 + 32, // cell + index + value
            Effect::Transfer { .. } => 32 + 32 + 8,
            Effect::GrantCapability { .. } => 32 + 32 + 36,
            Effect::RevokeCapability { .. } => 32 + 4,
            Effect::EmitEvent { event, .. } => 32 + 32 + event.data.len() * 32,
            Effect::IncrementNonce { .. } => 32,
            Effect::CreateCell { .. } => 32 + 32 + 8,
            Effect::SetPermissions { .. } => 32 + 8 * 1, // cell + 8 permission fields
            Effect::SetVerificationKey { new_vk, .. } => {
                32 + new_vk.as_ref().map_or(1, |vk| 1 + vk.data.len())
            }
            Effect::NoteSpend {
                spending_proof,
                value_commitment,
                ..
            } => {
                32 + 32 + 8 + 8 + spending_proof.len() + value_commitment.map_or(0, |_| 32) // nullifier + root + value + asset_type + proof + opt commitment
            }
            Effect::NoteCreate {
                encrypted_note,
                value_commitment,
                range_proof,
                ..
            } => {
                32 + 8
                    + 8
                    + encrypted_note.len()
                    + value_commitment.map_or(0, |_| 32)
                    + range_proof.as_ref().map_or(0, |rp| rp.len()) // commitment + value + asset_type + ciphertext + opt vc + opt rp
            }
            Effect::CreateSealPair { .. } => 32 + 32,
            Effect::Seal { .. } => 32 + 32 + 4,
            Effect::Unseal { sealed_box, .. } => {
                32 + 32 + 32 + sealed_box.ciphertext.len() + 32 + 32
            }
            Effect::BridgeMint { portable_proof } => {
                32 + 32 + 8 + 8 + portable_proof.spending_proof.len() // nullifier + commitment + value + asset + proof
            }
            Effect::BridgeLock { spending_proof, .. } => {
                32 + 32 + 8 + 8 + 8 + spending_proof.len() // nullifier + dest + value + asset + timeout + proof
            }
            Effect::BridgeFinalize { .. } => {
                32 + 32 + 32 + 8 + 64 // nullifier + receipt(nullifier + dest + height + sig)
            }
            Effect::BridgeCancel { .. } => 32, // nullifier
            Effect::PipelinedSend { .. } => 32 + 4 + 32,
            Effect::Introduce { .. } => 97,
            Effect::SpawnWithDelegation { .. } => 32 + 32 + 8,
            Effect::RefreshDelegation => 0,
            Effect::RevokeDelegation { .. } => 32,
            Effect::CreateObligation { stake, .. } => {
                32 + 32 + 8 + stake.0.len() + 8 // beneficiary + condition + deadline + stake + stake_amount
            }
            Effect::FulfillObligation { proof, .. } => {
                32 + match proof {
                    ConditionProof::Preimage(_) => 32,
                    ConditionProof::StarkProof { proof_bytes, .. } => proof_bytes.len() + 32 + 32,
                    ConditionProof::Receipt(_) => 32,
                }
            }
            Effect::SlashObligation { .. } => 32,
            Effect::CreateEscrow { condition, .. } => {
                32 + 32
                    + 8
                    + 8
                    + 32
                    + match condition {
                        EscrowCondition::ProofPresented { .. } => 32,
                        EscrowCondition::SignedByAll { signers } => signers.len() * 32,
                        EscrowCondition::PredicateSatisfied { .. } => 32,
                    }
            }
            Effect::ReleaseEscrow { proof, .. } => 32 + proof.as_ref().map_or(0, |p| p.len()),
            Effect::RefundEscrow { .. } => 32,
            Effect::CreateCommittedEscrow { range_proof, .. } => {
                32 + 32 + 32 + 32 + 8 + 32 + range_proof.len() + 8
                // creator_comm + recipient_comm + value_comm + condition_comm + timeout + escrow_id + range_proof + amount
            }
            Effect::ReleaseCommittedEscrow { .. } => {
                32 + 32 + 32 + 64 + 32 // escrow_id + pubkey + blinding + signature + recipient
            }
            Effect::RefundCommittedEscrow { .. } => {
                32 + 32 + 32 + 64 + 32 // escrow_id + pubkey + blinding + signature + creator
            }
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                4 + inner_effects.iter().map(|e| e.data_bytes()).sum::<usize>()
            }
            Effect::MakeSovereign { .. } => 32, // cell id
            Effect::CreateCellFromFactory { params, .. } => {
                32 + 32
                    + 32
                    + 1
                    + 33
                    + params.initial_fields.len() * 12
                    + params.initial_caps.len() * 34
                    + 32
            }
            Effect::QueueAllocate { program_vk, .. } => {
                8 + program_vk.map_or(1, |_| 33) // capacity + opt vk
            }
            Effect::QueueEnqueue { .. } => 32 + 32 + 8, // queue + message_hash + deposit
            Effect::QueueDequeue { .. } => 32,          // queue
            Effect::QueueResize { .. } => 32 + 8,       // queue + new_capacity
            Effect::QueueAtomicTx { operations } => {
                8 + operations.len() * (32 + 32 + 8) // count + ops (worst case: all enqueues)
            }
            Effect::QueuePipelineStep { sinks, .. } => {
                32 + 32 + 8 + sinks.len() * 32 // pipeline_id + source + count + sinks
            }
            // CapTP runtime effects: small fixed-size blobs.
            Effect::ExportSturdyRef { .. } => 32 + 32, // swiss + target
            Effect::EnlivenRef { .. } => 32 + 32,      // swiss + bearer
            Effect::DropRef { .. } => 32,              // ref_id
            Effect::ValidateHandoff { .. } => 32,      // cert_hash
            // Refusal: cell + commitment + reason-discriminant (+ opt 32-byte
            // custom reason hash) + u32 witness index.
            Effect::Refusal { refusal_reason, .. } => {
                32 + 32
                    + 1
                    + match refusal_reason {
                        RefusalReason::Custom { .. } => 32,
                        _ => 0,
                    }
                    + 4
            }
        }
    }

    /// Returns true if this effect is a permission-changing effect.
    ///
    /// Permission-changing effects (SetPermissions, SetVerificationKey) are always
    /// applied LAST within an action to prevent an action from weakening permissions
    /// and exploiting the weakened state in subsequent effects.
    pub fn is_permission_effect(&self) -> bool {
        matches!(
            self,
            Effect::SetPermissions { .. } | Effect::SetVerificationKey { .. }
        )
    }

    /// Return the effect kind bitmask for this effect.
    ///
    /// Used by `ExerciseViaCapability` to check whether a faceted capability
    /// permits this operation. Each effect type maps to exactly one bit in the
    /// [`EffectMask`](pyana_cell::EffectMask).
    pub fn effect_kind_mask(&self) -> pyana_cell::EffectMask {
        match self {
            Effect::SetField { .. } => pyana_cell::EFFECT_SET_FIELD,
            Effect::Transfer { .. } => pyana_cell::EFFECT_TRANSFER,
            Effect::GrantCapability { .. } => pyana_cell::EFFECT_GRANT_CAPABILITY,
            Effect::RevokeCapability { .. } => pyana_cell::EFFECT_REVOKE_CAPABILITY,
            Effect::EmitEvent { .. } => pyana_cell::EFFECT_EMIT_EVENT,
            Effect::IncrementNonce { .. } => pyana_cell::EFFECT_INCREMENT_NONCE,
            Effect::CreateCell { .. } => pyana_cell::EFFECT_CREATE_CELL,
            Effect::SetPermissions { .. } => pyana_cell::EFFECT_SET_PERMISSIONS,
            Effect::SetVerificationKey { .. } => pyana_cell::EFFECT_SET_VERIFICATION_KEY,
            Effect::NoteSpend { .. } => pyana_cell::EFFECT_NOTE_SPEND,
            Effect::NoteCreate { .. } => pyana_cell::EFFECT_NOTE_CREATE,
            Effect::CreateSealPair { .. } | Effect::Seal { .. } | Effect::Unseal { .. } => {
                pyana_cell::EFFECT_SEAL_OPS
            }
            Effect::BridgeMint { .. }
            | Effect::BridgeLock { .. }
            | Effect::BridgeFinalize { .. }
            | Effect::BridgeCancel { .. } => pyana_cell::EFFECT_BRIDGE_OPS,
            Effect::Introduce { .. } | Effect::PipelinedSend { .. } => pyana_cell::EFFECT_INTRODUCE,
            Effect::CreateObligation { .. }
            | Effect::FulfillObligation { .. }
            | Effect::SlashObligation { .. } => pyana_cell::EFFECT_OBLIGATION_OPS,
            Effect::CreateEscrow { .. }
            | Effect::ReleaseEscrow { .. }
            | Effect::RefundEscrow { .. }
            | Effect::CreateCommittedEscrow { .. }
            | Effect::ReleaseCommittedEscrow { .. }
            | Effect::RefundCommittedEscrow { .. } => pyana_cell::EFFECT_ESCROW_OPS,
            Effect::SpawnWithDelegation { .. }
            | Effect::RefreshDelegation
            | Effect::RevokeDelegation { .. } => pyana_cell::EFFECT_DELEGATION_OPS,
            Effect::ExerciseViaCapability { .. } => pyana_cell::EFFECT_ALL,
            Effect::MakeSovereign { .. } => pyana_cell::EFFECT_SOVEREIGN_OPS,
            Effect::CreateCellFromFactory { .. } => pyana_cell::EFFECT_CREATE_CELL,
            Effect::QueueAllocate { .. }
            | Effect::QueueEnqueue { .. }
            | Effect::QueueDequeue { .. }
            | Effect::QueueResize { .. }
            | Effect::QueueAtomicTx { .. }
            | Effect::QueuePipelineStep { .. } => pyana_cell::EFFECT_QUEUE_OPS,
            Effect::ExportSturdyRef { .. }
            | Effect::EnlivenRef { .. }
            | Effect::DropRef { .. }
            | Effect::ValidateHandoff { .. } => pyana_cell::EFFECT_CAPTP_OPS,
            Effect::Refusal { .. } => pyana_cell::EFFECT_REFUSAL,
        }
    }
}

impl Event {
    /// Create a new event.
    pub fn new(topic: Symbol, data: Vec<FieldElement>) -> Self {
        Self { topic, data }
    }
}
