//! Typed trace events. Every variant is tagged with a stable `kind` string
//! when serialized.

use pyana_cell::{AuthRequired, CellId};
use pyana_circuit::field::BabyBear;
use pyana_turn::{
    action::{Authorization, BearerCapProof, DelegationProofData},
    bilateral_schedule::{
        BilateralCounts, BilateralRoots, GrantEntry, IntroduceEntry, TransferEntry,
    },
};
use serde::Serialize;

use crate::schema::{SCHEMA_VERSION, hex_bytes, hex32, iso8601_from_millis};

/// A single trace event in the Studio event stream.
///
/// The serialized shape is:
///
/// ```json
/// {
///   "kind": "<discriminator>",
///   "envelope": { ... cross-cutting context ... },
///   "payload": { ... variant body ... }
/// }
/// ```
///
/// The `kind` discriminator is stable across schema-additive changes; the
/// `payload` shape is per-variant. See [`TraceEventKind`] for the enumeration
/// of every emitted kind.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind", content = "body")]
pub enum TraceEvent {
    /// An authorization variant was observed on an action.
    Authorization(EventBody<AuthorizationPayload>),
    /// A sovereign-cell witness was verified by the executor.
    SovereignWitnessVerified(EventBody<SovereignWitnessPayload>),
    /// A `StateConstraint` (slot caveat) was evaluated.
    StateConstraintEvaluated(EventBody<StateConstraintPayload>),
    /// A bilateral receipt (γ.2 binding) was produced for one entry.
    BilateralReceipt(EventBody<BilateralReceiptPayload>),
    /// A bilateral roll-up for one cell, summarising the per-direction
    /// accumulator state after a turn.
    BilateralRollup(EventBody<BilateralRollupPayload>),
    /// A federation event (join / leave / attestation / id derivation).
    Federation(EventBody<FederationPayload>),
    /// A turn started / committed / rejected / expired.
    TurnLifecycle(EventBody<TurnLifecyclePayload>),
}

impl TraceEvent {
    /// The stable string discriminator. Matches the JSON `kind` field.
    pub fn kind(&self) -> TraceEventKind {
        match self {
            TraceEvent::Authorization(_) => TraceEventKind::Authorization,
            TraceEvent::SovereignWitnessVerified(_) => TraceEventKind::SovereignWitnessVerified,
            TraceEvent::StateConstraintEvaluated(_) => TraceEventKind::StateConstraintEvaluated,
            TraceEvent::BilateralReceipt(_) => TraceEventKind::BilateralReceipt,
            TraceEvent::BilateralRollup(_) => TraceEventKind::BilateralRollup,
            TraceEvent::Federation(_) => TraceEventKind::Federation,
            TraceEvent::TurnLifecycle(_) => TraceEventKind::TurnLifecycle,
        }
    }

    /// Borrow the envelope (cross-cutting context).
    pub fn envelope(&self) -> &EventEnvelope {
        match self {
            TraceEvent::Authorization(b) => &b.envelope,
            TraceEvent::SovereignWitnessVerified(b) => &b.envelope,
            TraceEvent::StateConstraintEvaluated(b) => &b.envelope,
            TraceEvent::BilateralReceipt(b) => &b.envelope,
            TraceEvent::BilateralRollup(b) => &b.envelope,
            TraceEvent::Federation(b) => &b.envelope,
            TraceEvent::TurnLifecycle(b) => &b.envelope,
        }
    }
}

/// The stable string discriminator carried in JSON's `kind` field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraceEventKind {
    Authorization,
    SovereignWitnessVerified,
    StateConstraintEvaluated,
    BilateralReceipt,
    BilateralRollup,
    Federation,
    TurnLifecycle,
}

impl TraceEventKind {
    /// The lowercase snake-case discriminator string.
    pub fn as_str(&self) -> &'static str {
        match self {
            TraceEventKind::Authorization => "authorization",
            TraceEventKind::SovereignWitnessVerified => "sovereign_witness_verified",
            TraceEventKind::StateConstraintEvaluated => "state_constraint_evaluated",
            TraceEventKind::BilateralReceipt => "bilateral_receipt",
            TraceEventKind::BilateralRollup => "bilateral_rollup",
            TraceEventKind::Federation => "federation",
            TraceEventKind::TurnLifecycle => "turn_lifecycle",
        }
    }
}

/// Generic event body: envelope + variant payload. Flattened in JSON so that
/// the wire shape is `{ "kind": ..., "envelope": ..., "payload": ... }`.
#[derive(Clone, Debug, Serialize)]
pub struct EventBody<P> {
    pub envelope: EventEnvelope,
    pub payload: P,
}

/// Cross-cutting context attached to every event. Lets a Studio-side
/// timeline reconstruction tool group events by turn, by cell, by federation,
/// without rebuilding state.
#[derive(Clone, Debug, Serialize)]
pub struct EventEnvelope {
    /// Schema version; matches [`SCHEMA_VERSION`] at emit time.
    pub schema_version: u32,
    /// Monotonic per-`EventLog` sequence number. Replay tools can order
    /// events using this even when timestamps tie.
    pub seq: u64,
    /// ISO 8601 / RFC 3339 UTC timestamp with millisecond precision.
    pub timestamp: String,
    /// Originating turn hash, hex-encoded. `None` for events that exist
    /// independently of a turn (e.g. a federation-id derivation event).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turn_hash: Option<String>,
    /// Actor `CellId` (turn submitter), hex-encoded.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub actor: Option<String>,
    /// `FederationId` the event was observed inside, hex-encoded.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub federation_id: Option<String>,
    /// `CellId` the event pertains to (target cell, witness cell, etc.).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cell_id: Option<String>,
}

impl EventEnvelope {
    /// Build a fresh envelope with the schema_version pinned to current.
    pub fn new(seq: u64, unix_millis: i64) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            seq,
            timestamp: iso8601_from_millis(unix_millis),
            turn_hash: None,
            actor: None,
            federation_id: None,
            cell_id: None,
        }
    }

    /// Builder: attach turn hash.
    pub fn with_turn_hash(mut self, hash: &[u8; 32]) -> Self {
        self.turn_hash = Some(hex32(hash));
        self
    }

    /// Builder: attach actor cell id.
    pub fn with_actor(mut self, actor: &CellId) -> Self {
        self.actor = Some(hex32(actor.as_bytes()));
        self
    }

    /// Builder: attach federation id.
    pub fn with_federation_id(mut self, fed_id: &[u8; 32]) -> Self {
        self.federation_id = Some(hex32(fed_id));
        self
    }

    /// Builder: attach cell id (target).
    pub fn with_cell_id(mut self, cell: &CellId) -> Self {
        self.cell_id = Some(hex32(cell.as_bytes()));
        self
    }
}

// ---------------------------------------------------------------------------
// Authorization payload
// ---------------------------------------------------------------------------

/// Structured rendering of an [`Authorization`] variant. The variant tag is
/// the `auth_kind` field; the payload is per-variant flat fields, all of
/// which are hex-encoded where they would otherwise be raw bytes.
///
/// # Boundary discipline
///
/// - `Signature` emits the `(r, s)` pair as hex (these are public).
/// - `Proof` emits a BLAKE3 hash of the proof bytes (not the proof bytes
///   themselves — they are large and the hash is sufficient for cross-tool
///   identity).
/// - `Breadstuff` emits the token hash directly (it IS a hash).
/// - `Bearer` emits the delegation summary: target, permissions,
///   `delegator_pk` or root_issuer_commitment, expires_at, optional
///   revocation channel, optional allowed_effects, plus a hash of the
///   `delegation_proof` payload. Bearer signing keys / proof bytes are
///   never serialized.
/// - `CapTpDelivered` emits the certificate hash, recipient public key,
///   certificate nonce, expiry, and the sender signature (which is public);
///   it does NOT emit the introducer secret.
/// - `Unchecked` carries no payload — its mere appearance is the signal.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case", tag = "auth_kind")]
pub enum AuthorizationPayload {
    Signature {
        /// First 32 bytes of the signature (Ed25519 `r`).
        r_hex: String,
        /// Last 32 bytes of the signature (Ed25519 `s`).
        s_hex: String,
    },
    Proof {
        /// BLAKE3 hash of `proof_bytes`. The bytes themselves can be many KB
        /// and aren't needed for trace identity.
        proof_bytes_hash: String,
        proof_bytes_len: usize,
        bound_action: String,
        bound_resource: String,
    },
    Breadstuff {
        /// Capability token hash (this IS a hash; emitted directly).
        token_hash: String,
    },
    Bearer {
        target: String,
        permissions: String,
        expires_at: u64,
        revocation_channel: Option<String>,
        allowed_effects: Option<u32>,
        delegation: BearerDelegationSummary,
    },
    Unchecked,
    CapTpDelivered {
        /// Hash of the `HandoffCertificate` (BLAKE3 over its canonical
        /// signing message — i.e. the same bytes the introducer signed).
        cert_hash: String,
        /// Introducer federation id (hex).
        introducer_federation: String,
        /// Target federation id (hex).
        target_federation: String,
        /// Target cell on the destination federation (hex).
        target_cell: String,
        /// Recipient public key (hex).
        recipient_pk: String,
        /// Public key the wire layer captured for the introducer.
        introducer_pk: String,
        /// Sender public key (must equal `recipient_pk`).
        sender_pk: String,
        /// First 16 bytes of the recipient/sender signature (hex). The full
        /// 64-byte signature is public; truncating keeps the studio JSON
        /// readable. The full sig appears in the receipt itself.
        sender_signature_prefix: String,
        /// Certificate nonce (replay binding, hex).
        cert_nonce: String,
        /// Optional cert expiry height.
        expires_at: Option<u64>,
        /// Optional cert max-use counter.
        max_uses: Option<u32>,
        /// Permissions delegated by this cert.
        permissions: String,
        /// Effect mask the cert restricts (None = full effect set).
        allowed_effects: Option<u32>,
    },
}

/// Structured rendering of [`DelegationProofData`].
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case", tag = "delegation_kind")]
pub enum BearerDelegationSummary {
    SignedDelegation {
        delegator_pk: String,
        bearer_pk: String,
        signature_prefix: String,
    },
    StarkDelegation {
        proof_bytes_hash: String,
        proof_bytes_len: usize,
        root_issuer_commitment: String,
    },
}

impl AuthorizationPayload {
    /// Project an [`Authorization`] into the structured payload, applying
    /// the boundary-discipline rules documented at [`AuthorizationPayload`].
    pub fn from_authorization(auth: &Authorization) -> Self {
        match auth {
            Authorization::Signature(r, s) => AuthorizationPayload::Signature {
                r_hex: hex32(r),
                s_hex: hex32(s),
            },
            Authorization::Proof {
                proof_bytes,
                bound_action,
                bound_resource,
            } => AuthorizationPayload::Proof {
                proof_bytes_hash: hex32(blake3::hash(proof_bytes).as_bytes()),
                proof_bytes_len: proof_bytes.len(),
                bound_action: bound_action.clone(),
                bound_resource: bound_resource.clone(),
            },
            Authorization::Breadstuff(token) => AuthorizationPayload::Breadstuff {
                token_hash: hex32(token),
            },
            Authorization::Bearer(b) => AuthorizationPayload::Bearer {
                target: hex32(b.target.as_bytes()),
                permissions: auth_required_str(&b.permissions).to_string(),
                expires_at: b.expires_at,
                revocation_channel: b.revocation_channel.as_ref().map(hex32),
                allowed_effects: b.allowed_effects.map(|m| m.0),
                delegation: bearer_delegation_summary(b),
            },
            Authorization::Unchecked => AuthorizationPayload::Unchecked,
            Authorization::CapTpDelivered {
                handoff_cert,
                introducer_pk,
                sender_pk,
                sender_signature,
            } => {
                let signing_message = handoff_cert.signing_message();
                let cert_hash = blake3::hash(&signing_message);
                let mut sig_prefix = [0u8; 16];
                sig_prefix.copy_from_slice(&sender_signature[..16]);
                AuthorizationPayload::CapTpDelivered {
                    cert_hash: hex32(cert_hash.as_bytes()),
                    introducer_federation: hex32(&handoff_cert.introducer.0),
                    target_federation: hex32(&handoff_cert.target_federation.0),
                    target_cell: hex32(handoff_cert.target_cell.as_bytes()),
                    recipient_pk: hex32(&handoff_cert.recipient_pk),
                    introducer_pk: hex32(introducer_pk),
                    sender_pk: hex32(sender_pk),
                    sender_signature_prefix: hex_bytes(&sig_prefix),
                    cert_nonce: hex32(&handoff_cert.nonce),
                    expires_at: handoff_cert.expires_at,
                    max_uses: handoff_cert.max_uses,
                    permissions: auth_required_str(&handoff_cert.permissions).to_string(),
                    allowed_effects: handoff_cert.allowed_effects.map(|m| m.0),
                }
            }
        }
    }
}

fn bearer_delegation_summary(b: &BearerCapProof) -> BearerDelegationSummary {
    match &b.delegation_proof {
        DelegationProofData::SignedDelegation {
            delegator_pk,
            signature,
            bearer_pk,
        } => {
            let mut sig_prefix = [0u8; 16];
            sig_prefix.copy_from_slice(&signature[..16]);
            BearerDelegationSummary::SignedDelegation {
                delegator_pk: hex32(delegator_pk),
                bearer_pk: hex32(bearer_pk),
                signature_prefix: hex_bytes(&sig_prefix),
            }
        }
        DelegationProofData::StarkDelegation {
            proof_bytes,
            root_issuer_commitment,
        } => BearerDelegationSummary::StarkDelegation {
            proof_bytes_hash: hex32(blake3::hash(proof_bytes).as_bytes()),
            proof_bytes_len: proof_bytes.len(),
            root_issuer_commitment: hex32(root_issuer_commitment),
        },
    }
}

fn auth_required_str(p: &AuthRequired) -> &'static str {
    match p {
        AuthRequired::None => "none",
        AuthRequired::Signature => "signature",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
    }
}

// ---------------------------------------------------------------------------
// Sovereign witness payload
// ---------------------------------------------------------------------------

/// Structured rendering of a sovereign-witness verification event.
///
/// # Boundary discipline
///
/// Per `BOUNDARIES.md §2.6`, the witness cleartext (`cell_state`) is
/// cleartext-inside the cell owner. The observability layer is outside that
/// boundary. This payload deliberately omits:
///
/// - the cleartext cell state (`witness.cell_state`),
/// - field-level slot values,
/// - the cell's signing key bytes,
/// - the cell state commitment preimage.
///
/// It DOES surface:
///
/// - `cell_id` (already public — it's the routing identifier),
/// - `sequence` (already public — the replay nonce is observable on the wire),
/// - `has_stark_proof` (a single bit — leaks nothing more than the wire
///   shape already does),
/// - the public commitments (`old_commitment`, `new_commitment`,
///   `effects_hash`) — these are commitments, not preimages.
#[derive(Clone, Debug, Serialize)]
pub struct SovereignWitnessPayload {
    /// The sovereign cell id (hex).
    pub cell_id: String,
    /// Monotonic per-cell sequence number.
    pub sequence: u64,
    /// Whether the witness carried a STARK transition proof (the executor
    /// either verifies a proof or re-executes; this bit tells the Studio
    /// inspector which path was taken).
    pub has_stark_proof: bool,
    /// Pre-state commitment (hex).
    pub old_commitment: String,
    /// Post-state commitment (hex).
    pub new_commitment: String,
    /// Effects-hash binding declared by the witness (hex).
    pub effects_hash: String,
    /// Witness timestamp (informational; bound by signature). ISO-8601
    /// formatted to keep the Studio side uniform with the envelope.
    pub witness_timestamp: String,
}

impl SovereignWitnessPayload {
    /// Build the payload from a verified [`pyana_turn::SovereignCellWitness`].
    ///
    /// The caller has already verified the signature + sequence + commitment
    /// binding; this projection is the post-verification trace shape.
    pub fn from_witness(witness: &pyana_turn::SovereignCellWitness) -> Self {
        Self {
            cell_id: hex32(witness.cell_id.as_bytes()),
            sequence: witness.sequence,
            has_stark_proof: witness.transition_proof.is_some(),
            old_commitment: hex32(&witness.old_commitment),
            new_commitment: hex32(&witness.new_commitment),
            effects_hash: hex32(&witness.effects_hash),
            witness_timestamp: iso8601_from_millis(witness.timestamp * 1_000),
        }
    }
}

// ---------------------------------------------------------------------------
// State-constraint (slot caveat) payload
// ---------------------------------------------------------------------------

/// Structured rendering of a [`pyana_cell::program::StateConstraint`]
/// evaluation outcome.
///
/// # Boundary discipline
///
/// This payload surfaces the constraint *kind* string, the slot index(es) it
/// touches, the acceptance bit, and (on rejection) a structured reason
/// string. It does NOT emit the cleartext slot value the constraint
/// inspected — doing so would defeat `FieldVisibility::Committed`.
#[derive(Clone, Debug, Serialize)]
pub struct StateConstraintPayload {
    /// One of the 21 [`StateConstraint`] variant names (snake-case).
    pub constraint_kind: &'static str,
    /// The primary slot index the constraint touches. For multi-slot
    /// constraints (`SumEquals`, `SumEqualsAcross`, `BoundDelta`) this is
    /// the first slot in declaration order; see `extra_slot_indices` for
    /// the rest.
    pub slot_index: Option<u8>,
    /// Additional slot indices for multi-slot constraints. Empty for
    /// single-slot variants.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub extra_slot_indices: Vec<u8>,
    /// Whether the constraint accepted the transition.
    pub accepted: bool,
    /// Rejection reason (when `accepted == false`). Surfaces the
    /// `ProgramError` description; never includes raw slot values.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

impl StateConstraintPayload {
    /// Build the payload from a constraint and the program-evaluation result.
    pub fn from_evaluation(
        constraint: &pyana_cell::program::StateConstraint,
        accepted: bool,
        reason: Option<String>,
    ) -> Self {
        let (kind, slot, extra) = constraint_dissect(constraint);
        Self {
            constraint_kind: kind,
            slot_index: slot,
            extra_slot_indices: extra,
            accepted,
            reason,
        }
    }
}

/// Project a constraint into (kind-tag, primary slot, extra slots). The
/// kind-tag is stable and a Studio consumer can switch on it; primary
/// slot is `None` only for constraints that don't bind to a slot
/// (`SenderAuthorized`, `RateLimit`, `TemporalGate`).
fn constraint_dissect(
    constraint: &pyana_cell::program::StateConstraint,
) -> (&'static str, Option<u8>, Vec<u8>) {
    use pyana_cell::program::StateConstraint as SC;
    match constraint {
        SC::FieldEquals { index, .. } => ("field_equals", Some(*index), vec![]),
        SC::FieldGte { index, .. } => ("field_gte", Some(*index), vec![]),
        SC::FieldLte { index, .. } => ("field_lte", Some(*index), vec![]),
        SC::SumEquals { indices, .. } => {
            let mut extra = indices.clone();
            let primary = extra.first().copied();
            if !extra.is_empty() {
                extra.remove(0);
            }
            ("sum_equals", primary, extra)
        }
        SC::WriteOnce { index } => ("write_once", Some(*index), vec![]),
        SC::Immutable { index } => ("immutable", Some(*index), vec![]),
        SC::Monotonic { index } => ("monotonic", Some(*index), vec![]),
        SC::StrictMonotonic { index } => ("strict_monotonic", Some(*index), vec![]),
        SC::BoundedBy {
            index,
            witness_index,
        } => ("bounded_by", Some(*index), vec![*witness_index]),
        SC::FieldDelta { index, .. } => ("field_delta", Some(*index), vec![]),
        SC::FieldDeltaInRange { index, .. } => ("field_delta_in_range", Some(*index), vec![]),
        SC::FieldGteHeight { index, .. } => ("field_gte_height", Some(*index), vec![]),
        SC::FieldLteHeight { index, .. } => ("field_lte_height", Some(*index), vec![]),
        SC::SumEqualsAcross {
            input_fields,
            output_fields,
        } => {
            let mut extra: Vec<u8> = input_fields.iter().skip(1).copied().collect();
            extra.extend(output_fields.iter().copied());
            ("sum_equals_across", input_fields.first().copied(), extra)
        }
        SC::SenderAuthorized { .. } => ("sender_authorized", None, vec![]),
        SC::CapabilityUniqueness { cap_set_root_slot } => {
            ("capability_uniqueness", Some(*cap_set_root_slot), vec![])
        }
        SC::RateLimit { .. } => ("rate_limit", None, vec![]),
        SC::RateLimitBySum { slot_index, .. } => ("rate_limit_by_sum", Some(*slot_index), vec![]),
        SC::TemporalGate { .. } => ("temporal_gate", None, vec![]),
        SC::PreimageGate {
            commitment_index, ..
        } => ("preimage_gate", Some(*commitment_index), vec![]),
        SC::MonotonicSequence { seq_index } => ("monotonic_sequence", Some(*seq_index), vec![]),
        SC::AllowedTransitions { slot_index, .. } => {
            ("allowed_transitions", Some(*slot_index), vec![])
        }
        SC::TemporalPredicate { witness_index, .. } => {
            ("temporal_predicate", Some(*witness_index), vec![])
        }
        SC::BoundDelta {
            local_slot,
            peer_slot,
            ..
        } => ("bound_delta", Some(*local_slot), vec![*peer_slot]),
        SC::AnyOf { .. } => ("any_of", None, vec![]),
        SC::Custom { .. } => ("custom", None, vec![]),
    }
}

// ---------------------------------------------------------------------------
// Bilateral receipt payload
// ---------------------------------------------------------------------------

/// One bilateral receipt entry, as understood by γ.2 cross-cell binding.
/// Each Transfer / Grant / Introduce in a turn produces one of these per
/// affected cell side; the receiving end's view is the conjugate of the
/// sending end's view.
///
/// `transfer_id`, `peer_cell_id`, and `accumulator_root` are all hex
/// encodings of canonical `[BabyBear; 4]` packings (16 bytes raw, padded
/// to 32 bytes hex for uniformity).
#[derive(Clone, Debug, Serialize)]
pub struct BilateralReceiptPayload {
    /// Which γ.2 role this entry plays from the perspective of the
    /// envelope's `cell_id`. One of `outbound_transfer`, `inbound_transfer`,
    /// `outbound_grant`, `inbound_grant`, `intro_as_introducer`,
    /// `intro_as_recipient`, `intro_as_target`.
    pub direction: &'static str,
    /// Canonical 4-felt entry id (hex-packed; 4 × 4 bytes = 16 bytes).
    pub transfer_id: String,
    /// The peer cell on the other side of this bilateral edge.
    pub peer_cell_id: String,
    /// Running accumulator root AFTER absorbing this entry (4-felt, hex).
    pub accumulator_root: String,
    /// Optional amount (Transfer only). Surface-level: studio inspector
    /// renders Transfer entries differently from Grant/Introduce; this is
    /// the user-visible payload.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub amount: Option<u64>,
}

/// Per-cell roll-up of all bilateral entries in a turn — the seven-direction
/// `(count, root)` projection that the AIR's PI vector binds.
#[derive(Clone, Debug, Serialize)]
pub struct BilateralRollupPayload {
    pub counts: BilateralCountsView,
    pub roots: BilateralRootsView,
}

#[derive(Clone, Debug, Serialize)]
pub struct BilateralCountsView {
    pub outbound_transfer: u32,
    pub inbound_transfer: u32,
    pub outbound_grant: u32,
    pub inbound_grant: u32,
    pub intro_as_introducer: u32,
    pub intro_as_recipient: u32,
    pub intro_as_target: u32,
}

impl From<BilateralCounts> for BilateralCountsView {
    fn from(c: BilateralCounts) -> Self {
        Self {
            outbound_transfer: c.outbound_transfer,
            inbound_transfer: c.inbound_transfer,
            outbound_grant: c.outbound_grant,
            inbound_grant: c.inbound_grant,
            intro_as_introducer: c.intro_as_introducer,
            intro_as_recipient: c.intro_as_recipient,
            intro_as_target: c.intro_as_target,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct BilateralRootsView {
    pub outgoing_transfer: String,
    pub incoming_transfer: String,
    pub outgoing_grant: String,
    pub incoming_grant: String,
    pub intro_as_introducer: String,
    pub intro_as_recipient: String,
    pub intro_as_target: String,
}

impl From<BilateralRoots> for BilateralRootsView {
    fn from(r: BilateralRoots) -> Self {
        Self {
            outgoing_transfer: pack_felts(&r.outgoing_transfer),
            incoming_transfer: pack_felts(&r.incoming_transfer),
            outgoing_grant: pack_felts(&r.outgoing_grant),
            incoming_grant: pack_felts(&r.incoming_grant),
            intro_as_introducer: pack_felts(&r.intro_as_introducer),
            intro_as_recipient: pack_felts(&r.intro_as_recipient),
            intro_as_target: pack_felts(&r.intro_as_target),
        }
    }
}

/// Pack four `BabyBear` values as 16 raw bytes (LE per felt), hex-encoded.
/// Studio receives 32 hex chars per accumulator root.
pub fn pack_felts(felts: &[BabyBear; 4]) -> String {
    let mut out = String::with_capacity(32);
    for f in felts {
        let v = f.as_u32();
        for b in v.to_le_bytes() {
            out.push_str(&format!("{b:02x}"));
        }
    }
    out
}

/// Helper: render a TransferEntry as a [`BilateralReceiptPayload`] from the
/// outbound side (`from` cell). The `accumulator_root` argument is the
/// post-fold root for that direction.
pub fn transfer_entry_outbound(
    entry: &TransferEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "outbound_transfer",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.to.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: Some(entry.amount),
    }
}

/// Helper: render a TransferEntry from the inbound side (`to` cell).
pub fn transfer_entry_inbound(
    entry: &TransferEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "inbound_transfer",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.from.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: Some(entry.amount),
    }
}

/// Helper: render a GrantEntry, outbound side.
pub fn grant_entry_outbound(
    entry: &GrantEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "outbound_grant",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.to.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: None,
    }
}

/// Helper: render a GrantEntry, inbound side.
pub fn grant_entry_inbound(
    entry: &GrantEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "inbound_grant",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.from.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: None,
    }
}

/// Helper: render an IntroduceEntry from the introducer perspective.
pub fn intro_entry_introducer(
    entry: &IntroduceEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "intro_as_introducer",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.recipient.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: None,
    }
}

/// Helper: render an IntroduceEntry from the recipient perspective.
pub fn intro_entry_recipient(
    entry: &IntroduceEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "intro_as_recipient",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.introducer.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: None,
    }
}

/// Helper: render an IntroduceEntry from the target perspective.
pub fn intro_entry_target(
    entry: &IntroduceEntry,
    actor_nonce: u64,
    accumulator_root: &[BabyBear; 4],
) -> BilateralReceiptPayload {
    BilateralReceiptPayload {
        direction: "intro_as_target",
        transfer_id: pack_felts(&entry.id(actor_nonce)),
        peer_cell_id: hex32(entry.introducer.as_bytes()),
        accumulator_root: pack_felts(accumulator_root),
        amount: None,
    }
}

// ---------------------------------------------------------------------------
// Federation payload
// ---------------------------------------------------------------------------

/// Federation membership / attestation events. Stable variant tag is the
/// `event` field.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case", tag = "event")]
pub enum FederationPayload {
    /// A federation id was derived from a committee + epoch. Surfaces the
    /// algebraic binding (Lane D fix): `federation_id == BLAKE3(committee
    /// || epoch)`.
    IdDerived {
        federation_id: String,
        epoch: u64,
        threshold: u32,
        member_count: usize,
        /// Hex-encoded committee pubkeys, sorted lexicographically (this is
        /// the order the federation_id derivation uses).
        members: Vec<String>,
    },
    /// A member joined a federation (committee rotation). Carries the
    /// pre/post federation_id so a Studio timeline can stitch the
    /// rotation.
    MemberJoined {
        federation_id_before: String,
        federation_id_after: String,
        epoch_after: u64,
        member_pk: String,
    },
    /// A member left a federation (or was evicted).
    MemberLeft {
        federation_id_before: String,
        federation_id_after: String,
        epoch_after: u64,
        member_pk: String,
    },
    /// A federation produced a `ReceiptQc` attestation over a turn receipt
    /// or attested root. Surfaces the signing-message hash + signer count.
    Attestation {
        federation_id: String,
        epoch: u64,
        /// BLAKE3 hash of the bytes the committee signed.
        message_hash: String,
        /// Number of distinct signers (Ed25519 fallback) or the constant-
        /// size BLS aggregate marker (`1`).
        signer_count: u32,
        /// `bls` for `Aggregate`, `ed25519` for `Votes`, `mixed` if both.
        attestation_kind: &'static str,
    },
}

// ---------------------------------------------------------------------------
// Turn lifecycle payload
// ---------------------------------------------------------------------------

/// Turn lifecycle event. Stable variant tag is the `phase` field.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case", tag = "phase")]
pub enum TurnLifecyclePayload {
    /// The turn was submitted (pre-execution). Anchors all subsequent
    /// events with a `turn_hash` envelope.
    Submitted {
        nonce: u64,
        fee: u64,
        action_count: usize,
        valid_until: Option<i64>,
        previous_receipt_hash: Option<String>,
    },
    /// The executor accepted the turn. Surfaces the canonical receipt
    /// summary; the full receipt is shippable separately via its hash.
    Committed {
        receipt_hash: String,
        forest_hash: String,
        pre_state_hash: String,
        post_state_hash: String,
        effects_hash: String,
        timestamp: i64,
        action_count: usize,
        computrons_used: u64,
        finality: String,
    },
    /// The executor rejected the turn. Surfaces the reason; rejection
    /// reasons are public (they're the executor's error path).
    Rejected {
        reason: String,
        at_action: Option<usize>,
    },
    /// The turn expired before execution (valid_until passed).
    Expired,
    /// The turn is pending (e.g. awaiting a sovereign witness or a
    /// dependency).
    Pending { waiting_on: String },
}
