//! # pyana-storage-templates
//!
//! Canonical cell-program reference templates for the storage
//! primitives migrated under `STORAGE-AS-CELL-PROGRAMS.md`. The
//! [`STORAGE-AS-CELL-PROGRAMS.md`] design names five reference
//! templates; this crate authors them as
//! [`pyana_app_framework::FactoryDescriptor`]s with operation-scoped
//! [`CellProgram::Cases`] state machines and signed [`Action`] turn
//! builders composed only of existing [`Effect`] variants.
//!
//! ## Why a crate, not five
//!
//! All five primitives share the same shape: a small slot layout, an
//! `Always` invariant case + one `MethodIs` case per operation,
//! `MonotonicSequence`/`Monotonic`/`Immutable`/`SenderAuthorized`
//! constraints drawn from the lifted [`StateConstraint`] vocabulary,
//! and a turn-builder API for each operation. Sharing one crate keeps
//! the patterns visually comparable (and tests cross-reference each
//! other's adversarial cases). Apps that consume one template
//! generally consume several, so a single dep is also ergonomically
//! correct.
//!
//! ## Modules
//!
//! - [`cap_inbox`] — `CapInboxTemplate` (per §3.1, more general than
//!   `starbridge-apps/subscription/`: deposit accounting, per-message
//!   ring commitment).
//! - [`programmable_queue`] — `ProgrammableQueueTemplate` (per §3.2,
//!   the canonical mapping; constraint set is *parameterized by the
//!   factory builder*).
//! - [`pubsub_topic`] — `PubSubTopicTemplate` (per §3.3, append-only
//!   log + subscriber cursors).
//! - [`blinded_queue`] — `BlindedQueueTemplate` (per §3.4, uses
//!   `WitnessedPredicate::Custom { vk_hash = BLINDED_QUEUE_VK }` —
//!   the only template carrying a custom verifier).
//! - [`relay_operator`] — `RelayOperatorTemplate` (per §3.5, DFA
//!   caveat for dispatch + `RateLimitBySum` for quota +
//!   `BoundedBy` for slash-on-dispute).
//!
//! ## What this crate retires
//!
//! Once these templates exist and are wired into starbridge-apps, the
//! operator-side primitives in `pyana_storage::{programmable, inbox,
//! pubsub, blinded, operator, relay}` are
//! `#[deprecated]`. The storage crate keeps the underlying data
//! structures (`MerkleQueue`, `commitment`, `wal`, …); only the
//! parallel enforcement loop disappears.
//!
//! ## Boundary contracts
//!
//! Per `BOUNDARIES.md` §5.1 each template documents its
//! cleartext-inside / commitment-inside / acceptance-inside /
//! out-of-band populations in module docs. The receipt-bound
//! transition story (per `turn::executor`) is shared: every operation
//! produces a [`TurnReceipt`] (and, for sovereign cells, a
//! `WitnessedReceipt`) binding `(old_commit, new_commit,
//! effects_hash)`.
//!
//! ## Companion docs
//!
//! - `STORAGE-AS-CELL-PROGRAMS.md` §§3.1-3.5 — the per-primitive
//!   reference designs this crate implements.
//! - `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT.md` — what each storage
//!   primitive does today (and what `Q4.2` says to lift).
//! - `SLOT-CAVEATS-DESIGN.md` / `SLOT-CAVEATS-EVALUATION.md` — the
//!   21-variant `StateConstraint` vocabulary used below.
//! - `PREDICATE-INVENTORY.md` §9 — confirms each primitive's
//!   predicate-kind needs (only BlindedQueue requires a new
//!   `WitnessedPredicate::Custom { vk_hash }` registration).
//! - `starbridge-apps/subscription/src/lib.rs` — the §3.1 proof of
//!   pattern; this crate mirrors its structure.
//!
//! [`STORAGE-AS-CELL-PROGRAMS.md`]: ../STORAGE-AS-CELL-PROGRAMS.md
//! [`TurnReceipt`]: pyana_app_framework

#![forbid(unsafe_code)]

pub mod blinded_queue;
pub mod cap_inbox;
pub mod programmable_queue;
pub mod pubsub_topic;
pub mod relay_operator;

use pyana_app_framework::FactoryDescriptor;

/// The full slice of canonical factory descriptors this crate
/// contributes. Useful for hosts that want to register every storage
/// template in one call.
///
/// Order: CapInbox, ProgrammableQueue (work-queue default),
/// PubSubTopic, BlindedQueue, RelayOperator. Mirrors §3 of
/// `STORAGE-AS-CELL-PROGRAMS.md`.
pub fn all_storage_template_descriptors() -> Vec<FactoryDescriptor> {
    vec![
        cap_inbox::cap_inbox_factory_descriptor(),
        programmable_queue::programmable_queue_factory_descriptor(),
        pubsub_topic::pubsub_topic_factory_descriptor(),
        blinded_queue::blinded_queue_factory_descriptor(),
        relay_operator::relay_operator_factory_descriptor(),
    ]
}

/// Hex-encode a 32-byte array — shared helper used by the per-template
/// inspector JSON descriptors. Keeps the same encoding as
/// `starbridge-apps/subscription/`'s `hex_encode`.
pub(crate) fn hex_encode(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Pack a little-endian u64 into the trailing 8 bytes of a 32-byte
/// field element (big-endian convention used across pyana cell state).
/// Shared helper for the templates' tests and field-constraint
/// builders.
pub(crate) fn u64_field(value: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn five_templates_present() {
        let all = all_storage_template_descriptors();
        assert_eq!(
            all.len(),
            5,
            "STORAGE-AS-CELL-PROGRAMS.md §3 lists five templates"
        );
    }

    #[test]
    fn descriptors_have_distinct_factory_vks() {
        let all = all_storage_template_descriptors();
        let mut seen: Vec<[u8; 32]> = Vec::new();
        for d in &all {
            assert!(
                !seen.contains(&d.factory_vk),
                "duplicate factory_vk across templates: {:?}",
                d.factory_vk
            );
            seen.push(d.factory_vk);
        }
    }

    #[test]
    fn descriptors_hash_deterministically() {
        let all_a = all_storage_template_descriptors();
        let all_b = all_storage_template_descriptors();
        for (a, b) in all_a.iter().zip(all_b.iter()) {
            assert_eq!(a.hash(), b.hash(), "descriptor must hash deterministically");
        }
    }
}
