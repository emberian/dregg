//! State-constraint AIR-teeth tests (Cav-Codex Block 3, per
//! SLOT-CAVEATS-DESIGN.md §4).
//!
//! Per the design doc, "executor-side default; AIR enforcement is
//! strong-soundness opt-in". Block 3 lands the **manifest binding** —
//! the executor projects each declared `StateConstraint` into a
//! fixed-size PI section (`SLOT_CAVEAT_MANIFEST`), and the verifier
//! re-evaluates the manifest against `state_before` / `state_after`
//! via [`dregg_circuit::effect_vm::verify_slot_caveat_manifest`].
//!
//! Tests here are **PI-layer** adversarial tests: they assert that
//! tampering with the manifest entries — flipping a type_tag, changing
//! a slot_index, swapping a param — surfaces as a verifier-side
//! rejection without touching the underlying STARK. AIR-row binding
//! (pinning state_before/state_after columns to the manifest entries
//! algebraically) lands in a follow-up commit; the remaining ignored
//! sketches below are the variants that still need membership gadgets.
//!
//! STARBRIDGE-FOLLOWUP-03 (2026-05-25): PI-layer (SLOT_CAVEAT_MANIFEST +
//! verify_*) for first-wave variants landed (per §5.3). Full teeth +
//! SenderAuthorized etc (needs swiss gadget + big-int) + row binding
//! BLOCKED ON HUMAN (circuit/ + cell/program + heavy cargo). Precise
//! cross-refs: SILVER-DEBT T2.11 + CAVEAT-LAYER-COVERAGE; cell/src/program.rs
//! BoundDeltaNotWired etc.
//!
//! Coverage: one positive + one tamper test per verifier-enforced scalar
//! variant. First-wave variants are the ones whose enforcement fits the AIR's
//! existing 4-byte field-element truncation: `Immutable`, `WriteOnce`,
//! `FieldDelta`, `MonotonicSequence`, `FieldEquals`, `TemporalGate`.
//! Scalar ordering variants (`Monotonic`, `StrictMonotonic`, `FieldGte`,
//! `FieldLte`) and singleton `AllowedTransitions` tables are enforced over
//! the verifier-visible 4-byte BabyBear slot view. Sender set-membership
//! gadgets remain `#[ignore]`'d sketches until those AIRs land.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{
    SlotCaveatEntry, extract_slot_caveat_manifest, verify_slot_caveat_manifest,
};
use dregg_circuit::field::BabyBear;

fn pi_with_manifest(entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::BASE_COUNT];
    let count = entries.len().min(pi::MAX_SLOT_CAVEATS);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count as u32);
    for (i, entry) in entries.iter().take(count).enumerate() {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

fn fields_with(slot: usize, value: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[slot] = BabyBear::new(value);
    f
}

// ─────────────────────────────────────────────────────────────────────
// Immutable
// ─────────────────────────────────────────────────────────────────────

#[test]
fn immutable_accepts_unchanged_slot() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        slot_index: 3,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(3, 42);
    let final_ = fields_with(3, 42);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(
        result.is_ok(),
        "honest unchanged slot must pass: {result:?}"
    );
}

#[test]
fn immutable_rejects_changed_slot() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        slot_index: 3,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(3, 42);
    let final_ = fields_with(3, 43);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(
        result.is_err(),
        "tampering with an Immutable slot must reject"
    );
}

// ─────────────────────────────────────────────────────────────────────
// WriteOnce
// ─────────────────────────────────────────────────────────────────────

#[test]
fn write_once_accepts_first_write() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
        slot_index: 5,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    // Initial: slot is zero. Final: slot is 99 (first write OK).
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(5, 99);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "first write must pass: {result:?}");
}

#[test]
fn write_once_accepts_unchanged() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
        slot_index: 5,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(5, 99);
    let final_ = fields_with(5, 99);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "unchanged write_once must pass: {result:?}");
}

#[test]
fn write_once_rejects_overwrite() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
        slot_index: 5,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(5, 99);
    let final_ = fields_with(5, 100);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "overwriting write_once must reject");
}

// ─────────────────────────────────────────────────────────────────────
// FieldDelta
// ─────────────────────────────────────────────────────────────────────

#[test]
fn field_delta_accepts_correct_delta() {
    let delta = BabyBear::new(7);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        slot_index: 1,
        params: [delta, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(1, 10);
    let final_ = fields_with(1, 17);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "honest delta must pass: {result:?}");
}

#[test]
fn field_delta_rejects_wrong_delta() {
    let delta = BabyBear::new(7);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        slot_index: 1,
        params: [delta, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(1, 10);
    let final_ = fields_with(1, 18); // off-by-one
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "wrong delta must reject");
}

// ─────────────────────────────────────────────────────────────────────
// MonotonicSequence
// ─────────────────────────────────────────────────────────────────────

#[test]
fn monotonic_sequence_accepts_increment_by_one() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
        slot_index: 2,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(2, 100);
    let final_ = fields_with(2, 101);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "increment-by-one must pass: {result:?}");
}

#[test]
fn monotonic_sequence_rejects_skip() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
        slot_index: 2,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(2, 100);
    let final_ = fields_with(2, 102); // skip-ahead
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "skip-ahead must reject");
}

// ─────────────────────────────────────────────────────────────────────
// FieldEquals
// ─────────────────────────────────────────────────────────────────────

#[test]
fn field_equals_accepts_matching_value() {
    let v = BabyBear::new(0xdead);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_EQUALS,
        slot_index: 4,
        params: [v, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(4, 0xdead);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "matching value must pass: {result:?}");
}

#[test]
fn field_equals_rejects_mismatch() {
    let v = BabyBear::new(0xdead);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_EQUALS,
        slot_index: 4,
        params: [v, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(4, 0xbeef);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "mismatch must reject");
}

// ─────────────────────────────────────────────────────────────────────
// TemporalGate
// ─────────────────────────────────────────────────────────────────────

#[test]
fn temporal_gate_accepts_in_range() {
    let nb = BabyBear::new(100);
    let na = BabyBear::new(200);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
        slot_index: 0,
        params: [nb, na, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 150);
    assert!(result.is_ok(), "in-range height must pass: {result:?}");
}

#[test]
fn temporal_gate_rejects_below_not_before() {
    let nb = BabyBear::new(100);
    let na = BabyBear::new(200);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
        slot_index: 0,
        params: [nb, na, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 50);
    assert!(result.is_err(), "below not_before must reject");
}

#[test]
fn temporal_gate_rejects_above_not_after() {
    let nb = BabyBear::new(100);
    let na = BabyBear::new(200);
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
        slot_index: 0,
        params: [nb, na, BabyBear::ZERO, BabyBear::ZERO],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 250);
    assert!(result.is_err(), "above not_after must reject");
}

// ─────────────────────────────────────────────────────────────────────
// Manifest hygiene: padding entries must be zero
// ─────────────────────────────────────────────────────────────────────

#[test]
fn padding_entries_must_be_zero() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        slot_index: 0,
        params: [BabyBear::ZERO; 4],
    };
    let mut public_inputs = pi_with_manifest(&[entry]);
    // Smuggle a nonzero value into the padding region.
    let pad_base = pi::SLOT_CAVEAT_MANIFEST_BASE + 1 * pi::SLOT_CAVEAT_ENTRY_SIZE;
    public_inputs[pad_base + 2] = BabyBear::new(42);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "smuggled padding must reject");
}

#[test]
fn unknown_type_tag_is_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: 999, // not a known SLOT_CAVEAT_TAG_*
        slot_index: 0,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "unknown type tag must reject");
}

#[test]
fn count_above_max_is_rejected() {
    let mut public_inputs = vec![BabyBear::ZERO; pi::BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(pi::MAX_SLOT_CAVEATS as u32 + 1);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "count above MAX must reject");
}

#[test]
fn slot_index_out_of_range_rejected() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        slot_index: 8, // slots are 0..=7
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "slot_index 8 (>= 8) must reject");
}

#[test]
fn extract_roundtrips_entries() {
    let entry_a = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        slot_index: 3,
        params: [BabyBear::ZERO; 4],
    };
    let entry_b = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        slot_index: 1,
        params: [
            BabyBear::new(5),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry_a, entry_b]);
    let extracted = extract_slot_caveat_manifest(&public_inputs);
    assert_eq!(extracted.len(), 2);
    assert_eq!(extracted[0], entry_a);
    assert_eq!(extracted[1], entry_b);
}

// ─────────────────────────────────────────────────────────────────────
// Scalar ordering variants over the verifier-visible 4-byte slot view.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn monotonic_accepts_non_decrease() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC,
        slot_index: 6,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(6, 42);
    let final_ = fields_with(6, 42);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "non-decrease must pass: {result:?}");
}

#[test]
fn monotonic_rejects_decrease() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC,
        slot_index: 6,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(6, 42);
    let final_ = fields_with(6, 41);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "decrease must reject");
}

#[test]
fn strict_monotonic_accepts_increase() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
        slot_index: 6,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(6, 42);
    let final_ = fields_with(6, 43);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "strict increase must pass: {result:?}");
}

#[test]
fn strict_monotonic_rejects_equal() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
        slot_index: 6,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(6, 42);
    let final_ = fields_with(6, 42);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "equal value must reject");
}

#[test]
fn field_gte_accepts_greater_or_equal() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_GTE,
        slot_index: 7,
        params: [
            BabyBear::new(100),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(7, 100);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "gte equal bound must pass: {result:?}");
}

#[test]
fn field_gte_rejects_less() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_GTE,
        slot_index: 7,
        params: [
            BabyBear::new(100),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(7, 99);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "value below lower bound must reject");
}

#[test]
fn field_lte_accepts_less_or_equal() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_LTE,
        slot_index: 7,
        params: [
            BabyBear::new(100),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(7, 100);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "lte equal bound must pass: {result:?}");
}

#[test]
fn field_lte_rejects_greater() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_LTE,
        slot_index: 7,
        params: [
            BabyBear::new(100),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = fields_with(7, 101);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "value above upper bound must reject");
}

// ─────────────────────────────────────────────────────────────────────
// Singleton AllowedTransitions over the verifier-visible 4-byte slot view.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn allowed_transitions_accepts_listed_pair() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
        slot_index: 7,
        params: [
            BabyBear::ONE,
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(7, 1);
    let final_ = fields_with(7, 2);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_ok(), "listed transition must pass: {result:?}");
}

#[test]
fn allowed_transitions_rejects_unlisted_pair() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
        slot_index: 7,
        params: [
            BabyBear::ONE,
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(7, 1);
    let final_ = fields_with(7, 3);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(result.is_err(), "unlisted transition must reject");
}

#[test]
fn allowed_transitions_rejects_unsupported_manifest_encoding() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
        slot_index: 7,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(7, 1);
    let final_ = fields_with(7, 2);
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(
        result.is_err(),
        "malformed AllowedTransitions manifest must reject"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Deferred — variants that need sender membership witness context.
// ─────────────────────────────────────────────────────────────────────

#[test]
#[ignore = "SenderAuthorized PublicRoot: needs sender identity plus Merkle-membership witness context"]
fn sender_authorized_accepts_member() {}

#[test]
#[ignore = "SenderAuthorized BlindedSet: needs sender identity plus blinded-set/non-revocation witness context"]
fn sender_authorized_blinded_accepts_non_revoked() {}
