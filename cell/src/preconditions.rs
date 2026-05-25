use serde::{Deserialize, Serialize};

use crate::predicate::WitnessedPredicate;
use crate::state::{CellState, FieldElement};

/// Preconditions that must hold for an action to be valid.
///
/// Per PREDICATE-INVENTORY §4.3 case 1, the duplicate-surface
/// `turn::preconditions::Precondition` enum has been folded into this
/// canonical struct via the [`Preconditions::builder`] entry-point and
/// [`PreconditionsBuilder`]. The clause-shaped surface lives here as
/// [`Precondition`]; the parallel `turn/src/preconditions.rs` module
/// no longer exists — userspace imports `pyana_cell::Precondition`
/// directly.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Preconditions {
    /// Assertions about the cell's current state.
    pub cell_state: Option<CellStatePrecondition>,
    /// Assertions about the network state.
    pub network: Option<NetworkPrecondition>,
    /// Time range during which this action is valid.
    pub valid_while: Option<TimeRange>,
    /// Witness-attached clauses (DFA-classified message, temporal
    /// predicate over chain, blinded-membership against a slot root,
    /// custom-AIR proof) per PREDICATE-INVENTORY §4.1. Each
    /// declaration names a verifier kind, a commitment, an input
    /// reference, and a witness-blob index. The executor resolves the
    /// input and proof at evaluation time and dispatches through the
    /// `WitnessedPredicateRegistry`.
    ///
    /// Empty by default — most actions today carry no witnessed
    /// preconditions. Adding clauses here is purely additive: a
    /// receiver that doesn't know the kind surfaces
    /// `WitnessedPredicateError::KindNotRegistered`, which the
    /// executor maps to a precondition rejection.
    #[serde(default)]
    pub witnessed: Vec<WitnessedPredicate>,
}

/// Assertions about a cell's state that must be true.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellStatePrecondition {
    /// The exact nonce that must be current.
    pub nonce: Option<u64>,
    /// Minimum cell nonce — the cell's nonce must be at least this value.
    ///
    /// Use this for "see-then-set" patterns that need monotonic nonce
    /// progression without pinning to an exact value (which would race
    /// against concurrent submitters).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_nonce: Option<u64>,
    /// Minimum computron balance required.
    pub min_balance: Option<u64>,
    /// Fields that must equal specific values: (slot_index, expected_value).
    pub field_equals: Vec<(usize, FieldElement)>,
    /// Assert that the cell's proved_state flag equals this value.
    pub proved_state: Option<bool>,
}

/// Assertions about the network/ledger state.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct NetworkPrecondition {
    /// Minimum block height.
    pub min_height: Option<u64>,
    /// Maximum block height.
    pub max_height: Option<u64>,
}

/// A time range (inclusive on both ends).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeRange {
    /// Start of the valid time window (unix timestamp, seconds).
    pub start: i64,
    /// End of the valid time window (unix timestamp, seconds).
    pub end: i64,
}

impl TimeRange {
    /// Create a new time range.
    pub fn new(start: i64, end: i64) -> Self {
        TimeRange { start, end }
    }

    /// Check if a given timestamp falls within this range.
    pub fn contains(&self, timestamp: i64) -> bool {
        timestamp >= self.start && timestamp <= self.end
    }
}

/// Context for evaluating network/time preconditions **and** cell-program
/// state constraints.
///
/// This is the **shared contextual-evaluation surface** between
/// [`Preconditions`] (per-Action, see-then-set guards) and
/// [`crate::program::StateConstraint`] (per-CellProgram-slot, perpetual
/// invariants). The two enforcement loops differ in scope and lifetime
/// (see `StateConstraint` rustdoc for the precise split), but they
/// **share** this context type so an executor builds it once per turn
/// step and passes it to both surfaces.
///
/// ### Lane G `EvalContext` consolidation
///
/// Slot caveats (Lane G in `SLOT-CAVEATS-DESIGN.md` / `-EVALUATION.md`)
/// originally proposed a separate `EvalContext` with
/// `{ current_height, current_epoch, sender, sender_epoch_count,
/// revealed_preimage }`. Per `SLOT-CAVEATS-EVALUATION.md` §7.3 open
/// question 1, those fields were folded into the **existing**
/// `pyana_cell::preconditions::EvalContext` instead of creating a
/// parallel `StateConstraintCtx`. The original
/// `{ block_height, timestamp }` fields are preserved; the additions
/// default to safe sentinels so older callers compile unchanged.
#[derive(Clone, Debug)]
pub struct EvalContext {
    /// Current block height (used by `NetworkPrecondition` and by
    /// `FieldGteHeight` / `FieldLteHeight` / `TemporalGate` /
    /// `RateLimit` slot caveats).
    pub block_height: u64,
    /// Current timestamp (unix seconds, used by `Preconditions::valid_while`).
    pub timestamp: i64,
    /// Current epoch number (used by `RateLimit` slot caveat).
    /// Defaults to `0` when callers do not supply one.
    pub current_epoch: u64,
    /// The acting party's public-key/identity. `None` for system turns
    /// (genesis, scheduled effects). Used by `SenderAuthorized` /
    /// `RateLimit` slot caveats.
    pub sender: Option<[u8; 32]>,
    /// Sender's mutation count this epoch (for `RateLimit`). Defaults
    /// to `0`.
    pub sender_epoch_count: u32,
    /// Preimage revealed by the action (for `PreimageGate`). `None`
    /// when the action carries no preimage.
    pub revealed_preimage: Option<[u8; 32]>,
}

impl EvalContext {
    /// Construct a minimal context with just `block_height` and `timestamp`.
    /// All other fields default to sentinel/empty values.
    pub fn minimal(block_height: u64, timestamp: i64) -> Self {
        Self {
            block_height,
            timestamp,
            current_epoch: 0,
            sender: None,
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }
}

impl Default for EvalContext {
    fn default() -> Self {
        Self::minimal(0, 0)
    }
}

/// A single ergonomic precondition clause.
///
/// Per PREDICATE-INVENTORY §4.3 case 1, this is the canonical home for
/// what was previously a duplicate enum at
/// `pyana_turn::preconditions::Precondition`. The turn-side module
/// no longer exists; userspace constructs preconditions via this enum
/// and [`Preconditions::builder`] directly.
///
/// The clause lowers onto the underlying [`Preconditions`] fields via
/// [`Precondition::apply_to`]. The verifier-side check lives in
/// [`Preconditions::evaluate`] / [`CellStatePrecondition::evaluate`]:
/// there is **one** evaluator, not two parallel ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Precondition {
    /// The cell's storage slot at `index` must equal `value`.
    SlotEquals { index: usize, value: FieldElement },
    /// The cell's storage slot at `index` must be zero (the all-zero
    /// `FieldElement`).
    SlotZero { index: usize },
    /// The cell's `nonce` must be at least `min`.
    NonceAtLeast(u64),
    /// A witness-attached predicate must verify against its registered
    /// kind. Per PREDICATE-INVENTORY §3 + §4.1.
    Witnessed(WitnessedPredicate),
}

/// Deprecated alias retained during the surface-collapse transition.
/// Prefer [`Precondition`].
#[deprecated(
    since = "next",
    note = "renamed to `Precondition` as the canonical clause name"
)]
pub type PreconditionClause = Precondition;

impl Precondition {
    /// Apply this clause onto a mutable [`Preconditions`].
    pub fn apply_to(&self, pre: &mut Preconditions) {
        match self {
            Precondition::SlotEquals { index, value } => {
                let cs = pre.cell_state.get_or_insert_with(Default::default);
                cs.field_equals.push((*index, *value));
            }
            Precondition::SlotZero { index } => {
                let cs = pre.cell_state.get_or_insert_with(Default::default);
                cs.field_equals.push((*index, [0u8; 32]));
            }
            Precondition::NonceAtLeast(n) => {
                let cs = pre.cell_state.get_or_insert_with(Default::default);
                cs.min_nonce = Some(match cs.min_nonce {
                    Some(prev) => prev.max(*n),
                    None => *n,
                });
            }
            Precondition::Witnessed(wp) => {
                pre.witnessed.push(wp.clone());
            }
        }
    }
}

/// Builder for [`Preconditions`].
#[derive(Default)]
pub struct PreconditionsBuilder {
    inner: Preconditions,
}

impl PreconditionsBuilder {
    /// Start with an empty Preconditions.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one clause.
    pub fn push(mut self, clause: Precondition) -> Self {
        clause.apply_to(&mut self.inner);
        self
    }

    /// Add many clauses.
    pub fn extend(mut self, clauses: &[Precondition]) -> Self {
        for c in clauses {
            c.apply_to(&mut self.inner);
        }
        self
    }

    /// Finalize.
    pub fn build(self) -> Preconditions {
        self.inner
    }
}

impl Preconditions {
    /// Entry-point for ergonomic clause-shaped construction. Replaces
    /// the deleted `pyana_turn::preconditions::build` / `extend`
    /// helpers from the pre-collapse era.
    pub fn builder() -> PreconditionsBuilder {
        PreconditionsBuilder::new()
    }

    /// Apply a slice of clauses to this `Preconditions` in place.
    pub fn extend_clauses(&mut self, clauses: &[Precondition]) {
        for c in clauses {
            c.apply_to(self);
        }
    }

    /// Compute a deterministic hash of these preconditions for inclusion in signing messages.
    ///
    /// Uses BLAKE3 over a canonical byte representation. Empty (default) preconditions
    /// use a domain-separated constant (not all-zeros) to prevent confusion with
    /// uninitialized data or hash collisions with other all-zero values.
    pub fn hash(&self) -> [u8; 32] {
        // Domain-separated constant for empty preconditions.
        if self.cell_state.is_none()
            && self.network.is_none()
            && self.valid_while.is_none()
            && self.witnessed.is_empty()
        {
            return blake3::derive_key("pyana-empty-preconditions-v1", b"");
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"preconditions-v1");
        // Cell state precondition
        if let Some(ref cs) = self.cell_state {
            hasher.update(b"\x01");
            if let Some(nonce) = cs.nonce {
                hasher.update(b"\x01");
                hasher.update(&nonce.to_le_bytes());
            } else {
                hasher.update(b"\x00");
            }
            if let Some(min_n) = cs.min_nonce {
                hasher.update(b"\x01");
                hasher.update(&min_n.to_le_bytes());
            } else {
                hasher.update(b"\x00");
            }
            if let Some(min_bal) = cs.min_balance {
                hasher.update(b"\x01");
                hasher.update(&min_bal.to_le_bytes());
            } else {
                hasher.update(b"\x00");
            }
            hasher.update(&(cs.field_equals.len() as u64).to_le_bytes());
            for &(index, ref value) in &cs.field_equals {
                hasher.update(&(index as u64).to_le_bytes());
                hasher.update(value);
            }
            if let Some(proved) = cs.proved_state {
                hasher.update(if proved { b"\x01" } else { b"\x00" });
            }
        } else {
            hasher.update(b"\x00");
        }
        // Network precondition
        if let Some(ref net) = self.network {
            hasher.update(b"\x01");
            hasher.update(&net.min_height.unwrap_or(0).to_le_bytes());
            hasher.update(&net.max_height.unwrap_or(u64::MAX).to_le_bytes());
        } else {
            hasher.update(b"\x00");
        }
        // Time range
        if let Some(ref tr) = self.valid_while {
            hasher.update(b"\x01");
            hasher.update(&tr.start.to_le_bytes());
            hasher.update(&tr.end.to_le_bytes());
        } else {
            hasher.update(b"\x00");
        }
        // Witnessed clauses: length-prefix the vector then domain-tag
        // each entry by kind discriminant + commitment + serialized
        // input_ref + proof_witness_index. Empty vec hashes the
        // length prefix (0u64) and contributes nothing else, so the
        // empty-witnessed shape is identical to the pre-§3 hash for
        // backcompat with serialized actions that did not carry the
        // field. (The all-empty fast path is taken above.)
        hasher.update(&(self.witnessed.len() as u64).to_le_bytes());
        for wp in &self.witnessed {
            // Postcard-encoded WitnessedPredicate is canonical given
            // the type's `Serialize` derive; length-prefix it.
            let bytes = postcard::to_allocvec(wp).unwrap_or_default();
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
        *hasher.finalize().as_bytes()
    }

    /// Evaluate all preconditions against the given cell state and context.
    /// Returns Ok(()) if all preconditions pass, or Err with a description of the failure.
    pub fn evaluate(&self, state: &CellState, ctx: &EvalContext) -> Result<(), PreconditionError> {
        if let Some(ref cell_pre) = self.cell_state {
            cell_pre.evaluate(state)?;
        }
        if let Some(ref net_pre) = self.network {
            net_pre.evaluate(ctx)?;
        }
        if let Some(ref time_range) = self.valid_while
            && !time_range.contains(ctx.timestamp)
        {
            return Err(PreconditionError::TimeOutOfRange {
                timestamp: ctx.timestamp,
                start: time_range.start,
                end: time_range.end,
            });
        }
        Ok(())
    }
}

impl CellStatePrecondition {
    /// Evaluate the cell state precondition.
    pub fn evaluate(&self, state: &CellState) -> Result<(), PreconditionError> {
        if let Some(expected_nonce) = self.nonce
            && state.nonce != expected_nonce
        {
            return Err(PreconditionError::NonceMismatch {
                expected: expected_nonce,
                actual: state.nonce,
            });
        }
        if let Some(min_n) = self.min_nonce
            && state.nonce < min_n
        {
            return Err(PreconditionError::NonceTooLow {
                required: min_n,
                actual: state.nonce,
            });
        }
        if let Some(min_bal) = self.min_balance
            && state.balance < min_bal
        {
            return Err(PreconditionError::InsufficientBalance {
                required: min_bal,
                actual: state.balance,
            });
        }
        for &(index, ref expected_value) in &self.field_equals {
            match state.get_field(index) {
                Some(actual) if actual == expected_value => {}
                Some(actual) => {
                    return Err(PreconditionError::FieldMismatch {
                        index,
                        expected: *expected_value,
                        actual: *actual,
                    });
                }
                None => {
                    return Err(PreconditionError::InvalidFieldIndex { index });
                }
            }
        }
        if let Some(expected_proved) = self.proved_state
            && state.proved_state != expected_proved
        {
            return Err(PreconditionError::ProvedStateMismatch {
                expected: expected_proved,
                actual: state.proved_state,
            });
        }
        Ok(())
    }
}

impl NetworkPrecondition {
    /// Evaluate the network precondition.
    pub fn evaluate(&self, ctx: &EvalContext) -> Result<(), PreconditionError> {
        if let Some(min_h) = self.min_height
            && ctx.block_height < min_h
        {
            return Err(PreconditionError::HeightTooLow {
                required: min_h,
                actual: ctx.block_height,
            });
        }
        if let Some(max_h) = self.max_height
            && ctx.block_height > max_h
        {
            return Err(PreconditionError::HeightTooHigh {
                max: max_h,
                actual: ctx.block_height,
            });
        }
        Ok(())
    }
}

/// Errors from precondition evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreconditionError {
    NonceMismatch {
        expected: u64,
        actual: u64,
    },
    NonceTooLow {
        required: u64,
        actual: u64,
    },
    InsufficientBalance {
        required: u64,
        actual: u64,
    },
    FieldMismatch {
        index: usize,
        expected: FieldElement,
        actual: FieldElement,
    },
    InvalidFieldIndex {
        index: usize,
    },
    HeightTooLow {
        required: u64,
        actual: u64,
    },
    HeightTooHigh {
        max: u64,
        actual: u64,
    },
    TimeOutOfRange {
        timestamp: i64,
        start: i64,
        end: i64,
    },
    ProvedStateMismatch {
        expected: bool,
        actual: bool,
    },
}

#[cfg(test)]
mod clause_tests {
    //! Clause-shaped construction tests (migrated from the deleted
    //! `pyana_turn::preconditions` module per PREDICATE-INVENTORY §4.3
    //! case 1). Verifies that `Precondition::{SlotEquals, SlotZero,
    //! NonceAtLeast, Witnessed}` lower correctly onto the canonical
    //! [`Preconditions`] fields and round-trip through
    //! [`Preconditions::evaluate`].
    use super::*;
    use crate::state::CellState;

    fn build(items: &[Precondition]) -> Preconditions {
        Preconditions::builder().extend(items).build()
    }

    fn state_with(nonce: u64, fields: &[(usize, FieldElement)]) -> CellState {
        let mut s = CellState::new(0);
        s.set_nonce(nonce);
        for &(i, v) in fields {
            assert!(s.set_field(i, v), "slot {i} must be within STATE_SLOTS");
        }
        s
    }

    fn ctx() -> EvalContext {
        EvalContext {
            block_height: 0,
            timestamp: 0,
            ..Default::default()
        }
    }

    #[test]
    fn slot_equals_pass_and_fail() {
        let value = [7u8; 32];
        let pre = build(&[Precondition::SlotEquals { index: 3, value }]);
        let state_ok = state_with(0, &[(3, value)]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_bad = state_with(0, &[(3, [9u8; 32])]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn slot_zero_rejects_nonzero() {
        let pre = build(&[Precondition::SlotZero { index: 5 }]);
        let state_ok = state_with(0, &[(5, [0u8; 32])]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_bad = state_with(0, &[(5, [1u8; 32])]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn nonce_at_least_pass_and_fail() {
        let pre = build(&[Precondition::NonceAtLeast(10)]);
        let state_ok = state_with(10, &[]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_ok2 = state_with(11, &[]);
        assert!(pre.evaluate(&state_ok2, &ctx()).is_ok());
        let state_bad = state_with(9, &[]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn multiple_preconditions_combine() {
        let value = [3u8; 32];
        let pre = build(&[
            Precondition::SlotEquals { index: 2, value },
            Precondition::SlotZero { index: 4 },
            Precondition::NonceAtLeast(5),
        ]);
        let state_ok = state_with(7, &[(2, value), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());

        // Fail on nonce
        let state_bad_nonce = state_with(3, &[(2, value), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_bad_nonce, &ctx()).is_err());

        // Fail on slot equals
        let state_bad_slot = state_with(7, &[(2, [9u8; 32]), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_bad_slot, &ctx()).is_err());
    }

    #[test]
    fn nonce_at_least_takes_max_when_repeated() {
        let pre = build(&[Precondition::NonceAtLeast(3), Precondition::NonceAtLeast(7)]);
        let cs = pre.cell_state.as_ref().expect("cell_state present");
        assert_eq!(cs.min_nonce, Some(7));
    }

    #[test]
    fn witnessed_clause_appends_to_witnessed_field() {
        use crate::predicate::{InputRef, WitnessedPredicate};
        let wp = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
        let pre = build(&[Precondition::Witnessed(wp.clone())]);
        assert_eq!(pre.witnessed.len(), 1);
        assert_eq!(pre.witnessed[0], wp);
    }

    #[test]
    fn preconditions_roundtrip_postcard() {
        // Round-trip the canonical Preconditions through postcard to
        // ensure the wire shape is stable across the
        // turn→cell collapse.
        let value = [11u8; 32];
        let pre = build(&[
            Precondition::SlotEquals { index: 1, value },
            Precondition::SlotZero { index: 2 },
            Precondition::NonceAtLeast(99),
        ]);
        let bytes = postcard::to_allocvec(&pre).expect("encode");
        eprintln!("preconditions bytes ({}): {:02x?}", bytes.len(), bytes);
        let decoded: Preconditions = postcard::from_bytes(&bytes).expect("decode");
        assert_eq!(pre, decoded);
        assert_eq!(pre.hash(), decoded.hash());

        // Malformed / edge-case inputs must be rejected.
        // Truncated bytes.
        assert!(
            postcard::from_bytes::<Preconditions>(&bytes[..bytes.len().saturating_sub(2)]).is_err(),
            "truncated preconditions must fail to decode"
        );
        // Invalid Option discriminant — the first byte is the
        // `cell_state` Option tag; postcard uses 0=None, 1=Some, so
        // 0xFF is structurally invalid and must be rejected.
        //
        // The previously-asserted negatives ("all-zero buffer" and
        // "extra trailing bytes") were both UNSOUND under postcard 1.x:
        //   - An all-zero buffer decodes to the canonical empty
        //     `Preconditions { None, None, None, vec![] }`, which is a
        //     legitimate value.
        //   - `postcard::from_bytes` (1.x) does not reject trailing
        //     bytes — see `take_from_bytes` for the trailing-data
        //     variant. The extra-trailing test only succeeded against
        //     a stricter pre-1.x decoder.
        // We assert what is actually invariant: a malformed
        // discriminant must produce a decode error.
        assert!(
            postcard::from_bytes::<Preconditions>(&[0xFFu8; 16]).is_err(),
            "invalid Option discriminant must fail to decode"
        );
    }
}
