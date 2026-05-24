//! `pyana-observability` — Studio-shape structured trace events for the pyana
//! turn substrate.
//!
//! # Scope
//!
//! This crate emits typed, replay-friendly trace events covering:
//!
//! - **Authorization** — every `Authorization` variant
//!   (`Signature`, `Proof`, `Breadstuff`, `Bearer`, `Unchecked`,
//!   `CapTpDelivered`).
//! - **Sovereign witnesses** — verification events for
//!   `SovereignCellWitness`, surfacing `(cell_id, sequence,
//!   has_stark_proof)` without leaking cleartext cell state (per
//!   `BOUNDARIES.md` — the witness is cleartext-inside the cell owner only).
//! - **Slot caveats** — `StateConstraint` evaluation outcomes
//!   `(constraint_kind, slot_index, accepted, reason?)`.
//! - **γ.2 bilateral receipts** — `(transfer_id, peer_cell_id,
//!   accumulator_root)` per bilateral entry, plus per-cell roots/counts.
//! - **Federation events** — join / leave / attestation / id-derivation.
//! - **Turn lifecycle** — receipt summaries that anchor every other event in
//!   a turn-scoped timeline.
//!
//! # Replay friendliness
//!
//! Each [`TraceEvent`] is self-contained: it carries the schema version, a
//! monotonic sequence number, an ISO-8601 timestamp, the turn / cell /
//! federation context where applicable, and a structured payload. An
//! external tool may reconstruct a timeline from an event log alone, without
//! consulting any other state.
//!
//! # JSON shape (the wire format the Studio inspector consumes)
//!
//! Every event is a JSON object with three stable top-level keys:
//!
//! ```json
//! {
//!   "kind": "<discriminator>",
//!   "envelope": { "schema_version": 1, "seq": 0, "timestamp": "2026-05-24T...", ... },
//!   "payload": { ... variant-specific ... }
//! }
//! ```
//!
//! - `kind` is a stable string discriminator (e.g. `"authorization"`,
//!   `"sovereign_witness_verified"`, `"state_constraint_evaluated"`,
//!   `"bilateral_receipt"`, `"federation"`, `"turn_lifecycle"`).
//! - `envelope` contains the cross-cutting context: schema version, seq, ISO
//!   8601 timestamp, plus optional `turn_hash`, `actor`, `federation_id`,
//!   `cell_id` fields.
//! - `payload` is the variant body. See [`events`] for the exhaustive shape.
//!
//! All 32-byte values are emitted as lowercase hex (no `0x` prefix). Timestamps
//! are RFC 3339 / ISO 8601 strings in UTC with a millisecond precision.
//!
//! # Schema versioning
//!
//! The schema is versioned at [`SCHEMA_VERSION`]. The Studio consumer should
//! reject events whose `envelope.schema_version` exceeds its known max, and
//! must tolerate unknown fields within `payload` so additive variant payloads
//! roll forward cleanly.
//!
//! # Boundary discipline
//!
//! Per `BOUNDARIES.md`:
//!
//! - Sovereign-cell witness events emit `(cell_id, sequence,
//!   has_stark_proof)` only. They MUST NOT emit cleartext slot values,
//!   field bytes, or the cell state commitment preimage. The witness
//!   plaintext is cleartext-inside the cell owner; the observability layer
//!   is *outside* that boundary.
//! - Authorization events emit certificate hashes / public keys / nonces —
//!   never private signing keys, never bearer-cap delegation proof bytes
//!   (only their hash). The `Authorization::Proof` payload emits
//!   `proof_bytes_hash`, never `proof_bytes`.
//! - State-constraint events surface the constraint *kind* and the slot
//!   index, plus a structured rejection reason. They do NOT emit the slot's
//!   cleartext value (which would defeat `FieldVisibility::Committed`).
//!
//! These choices keep an event log shareable with parties who hold strictly
//! less authority than the cell owner.

pub mod emitter;
pub mod events;
pub mod schema;

pub use emitter::{Emitter, EventLog};
pub use events::{
    AuthorizationPayload, BilateralReceiptPayload, EventEnvelope, FederationPayload,
    SovereignWitnessPayload, StateConstraintPayload, TraceEvent, TraceEventKind,
    TurnLifecyclePayload,
};
pub use schema::{SCHEMA_NAME, SCHEMA_VERSION};
