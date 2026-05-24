//! Cell programs: state transition logic carried by cells.
//!
//! A cell program defines valid state transitions. The executor checks the program's
//! constraints on every state-modifying action. This turns cells from "accounts with
//! permissions" into "smart contracts with privacy."
//!
//! # Slot caveats (lifted-enum v1)
//!
//! `StateConstraint` is the **slot-caveat vocabulary**: a closed lifted enum that
//! authors compose to declare a cell's perpetual invariants. The lift is described
//! in `SLOT-CAVEATS-DESIGN.md` (Lane G) and refined by `SLOT-CAVEATS-EVALUATION.md`
//! (eval — adopted 21-variant set instead of 14).
//!
//! ## `Precondition` vs `StateConstraint`
//!
//! These are **distinct surfaces with overlapping atoms**.
//!
//! - **[`crate::Preconditions`]** are **per-Action**: one-shot "given the current
//!   state, is this Action valid to apply?" Carried in `Action::preconditions`,
//!   signed-over by the submitter, evaluated *before* effects run. Scope:
//!   per-action evaluation, see-then-set guard.
//! - **[`StateConstraint`]** is **per-CellProgram-slot**: perpetual "every
//!   transition of this slot must satisfy X." Carried in `Cell::program`,
//!   signed-over at cell creation, evaluated *after* state-modifying effects
//!   on every turn. Scope: per-slot lifetime invariant.
//!
//! They share the predicate-atom alphabet (slot-equals, height-bound,
//! sender-membership) and share [`crate::preconditions::EvalContext`], but the
//! wrapper enums stay distinct because they live in different signing contexts.
//!
//! # Use cases
//!
//! - **Private DEX order**: cell holds (asset, amount, price). The matching
//!   predicate is part of the cell. A filler proves they satisfy the predicate
//!   without seeing the full order details.
//! - **Sealed auction**: cell holds committed bid. On reveal, proves
//!   `bid > minimum` and bid was committed before deadline.
//! - **NFT with provenance**: cell holds ownership + history. Transfer proves
//!   valid chain without revealing full provenance to the public.

use serde::{Deserialize, Serialize};

use crate::preconditions::EvalContext;
use crate::predicate::WitnessedPredicate;
use crate::state::{CellState, FIELD_ZERO, FieldElement, STATE_SLOTS};

/// A cell program defines valid state transitions.
/// The executor checks the program's constraints on every state-modifying action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellProgram {
    /// No program — any authorized state change is valid (current behavior).
    None,

    /// Predicate program: a set of conditions that must hold after transition.
    /// Expressed as a list of constraints over the 8 field slots. All constraints
    /// must hold (implicit conjunction). For disjunction, use
    /// [`StateConstraint::AnyOf`].
    Predicate(Vec<StateConstraint>),

    /// Circuit program: an AIR/R1CS circuit that defines the valid state transition function.
    /// The proof in the Action's authorization MUST satisfy this circuit.
    Circuit {
        /// Hash of the circuit (for lookup/verification).
        circuit_hash: [u8; 32],
    },
}

impl Default for CellProgram {
    fn default() -> Self {
        CellProgram::None
    }
}

/// Cryptographic hash kind used by `PreimageGate`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashKind {
    /// BLAKE3 keyed-mode (default for non-circuit commitments).
    Blake3,
    /// Poseidon2 — preferred for in-circuit verification.
    Poseidon2,
}

impl Default for HashKind {
    fn default() -> Self {
        HashKind::Blake3
    }
}

/// Source for `SenderAuthorized`'s sender-set membership check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthorizedSet {
    /// Public Merkle root of authorized sender keys, sourced from slot
    /// `set_root_index`. The witness side carries a Merkle-membership proof.
    PublicRoot { set_root_index: u8 },
    /// Blinded set (per `SLOT-CAVEATS-EVALUATION.md` §4.8): the cell only
    /// knows a Poseidon2 commitment to the membership set. The witness side
    /// carries a non-revocation proof against the commitment.
    BlindedSet { commitment: [u8; 32] },
}

/// Delta-relation kind for `BoundDelta` cross-cell binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeltaRelation {
    /// This cell's slot delta equals the peer's slot delta exactly.
    Equal,
    /// This cell adds, peer subtracts (paired atomic swap / bilateral
    /// conservation).
    EqualAndOpposite,
}

/// Declared read-set for a `Custom` predicate — what slots / context fields
/// the DSL-authored predicate touches. Lets audit tools and (eventually)
/// AIR enforcement reason about a custom predicate's structural footprint
/// without executing it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReadSet {
    /// Slot indices the predicate reads from `new_state`.
    pub new_slots: Vec<u8>,
    /// Slot indices the predicate reads from `old_state`.
    pub old_slots: Vec<u8>,
    /// Whether the predicate reads `ctx.block_height`.
    pub reads_height: bool,
    /// Whether the predicate reads `ctx.current_epoch`.
    pub reads_epoch: bool,
    /// Whether the predicate reads `ctx.sender`.
    pub reads_sender: bool,
    /// Whether the predicate reads `ctx.revealed_preimage`.
    pub reads_preimage: bool,
}

/// Structured human/version descriptor for `Custom`. Replaces free-form
/// `description: String` per `SLOT-CAVEATS-EVALUATION.md` §5.4(d).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustomDescriptor {
    /// Human-readable name, e.g. `"escrow_release_predicate"`.
    pub human_name: String,
    /// Semantic version string, e.g. `"v3.1.0"`.
    pub semver: String,
    /// Authoring package reference, e.g. `"starbridge-apps/escrow"`.
    pub authoring_package: String,
}

/// Simple (non-recursive) constraint set permitted inside `AnyOf`.
///
/// Per `SLOT-CAVEATS-EVALUATION.md` §4.3 we bound `AnyOf` to a single
/// level of disjunction: no nested `AnyOf` and no nested `Custom`. Apps
/// that need deeper composition fall back to a `Custom` predicate that
/// internally evaluates the disjunction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SimpleStateConstraint {
    FieldEquals {
        index: u8,
        value: FieldElement,
    },
    FieldGte {
        index: u8,
        value: FieldElement,
    },
    FieldLte {
        index: u8,
        value: FieldElement,
    },
    WriteOnce {
        index: u8,
    },
    Immutable {
        index: u8,
    },
    Monotonic {
        index: u8,
    },
    StrictMonotonic {
        index: u8,
    },
    BoundedBy {
        index: u8,
        witness_index: u8,
    },
    FieldGteHeight {
        index: u8,
        offset: i64,
    },
    FieldLteHeight {
        index: u8,
        offset: i64,
    },
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },
}

/// A constraint on cell state (for Predicate programs).
///
/// **21 variants total** per `SLOT-CAVEATS-EVALUATION.md` §7.6:
/// - 4 static post-state: `FieldEquals`, `FieldGte`, `FieldLte`, `SumEquals`
/// - 3 immutability/once: `Immutable`, `WriteOnce`, `StrictMonotonic`
/// - 3 transition: `Monotonic`, `FieldDelta`, `FieldDeltaInRange`
/// - 2 height-bound: `FieldGteHeight`, `FieldLteHeight`
/// - 1 cross-slot witness: `BoundedBy`
/// - 1 conservation (intra-cell): `SumEqualsAcross`
/// - 2 sender-bound: `SenderAuthorized`, `CapabilityUniqueness`
/// - 2 rate/temporal: `RateLimit`, `RateLimitBySum`, `TemporalGate`
/// - 1 preimage: `PreimageGate`
/// - 1 sequence: `MonotonicSequence`
/// - 1 state-machine: `AllowedTransitions`
/// - 1 witness-attached: `TemporalPredicate`
/// - 1 cross-cell: `BoundDelta`
/// - 1 composition: `AnyOf`
/// - 1 escape: `Custom`
///
/// ### Replay semantics (eval finding 3)
///
/// For `SenderAuthorized` (with a slot-held Merkle root) and
/// `FieldGteHeight` / `FieldLteHeight`, the constraint depends on
/// **external state** (the set root, the current height). To keep
/// `WitnessedReceipt` scope-2 replay deterministic, the executor
/// **snapshots** the relevant external state at *receipt-time* and
/// carries it on the receipt. Replays re-evaluate against the snapshotted
/// state, **not** against the replayer's current chain view. The
/// `EvalContext` passed at replay time should be reconstructed from the
/// receipt, not from the replayer's live ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StateConstraint {
    // ─── Static post-state predicates (existing) ───
    /// Field at index must equal value.
    FieldEquals { index: u8, value: FieldElement },
    /// Field at index must be >= value (unsigned big-endian comparison).
    FieldGte { index: u8, value: FieldElement },
    /// Field at index must be <= value (unsigned big-endian comparison).
    FieldLte { index: u8, value: FieldElement },
    /// Sum of fields at indices must equal value (intra-cell conservation).
    /// Fields are interpreted as big-endian u64 in the last 8 bytes.
    SumEquals {
        indices: Vec<u8>,
        value: FieldElement,
    },

    // ─── Transition predicates over (old, new) ───
    /// Slot must transition only from `FIELD_ZERO` to any non-zero value;
    /// after the first write, the slot is frozen. Generalizes `Immutable`
    /// for the common "register once, then read-only" pattern.
    WriteOnce { index: u8 },

    /// Slot value is read-only after initialization. `new[i] == old[i]`
    /// for any non-fresh cell; on init (nonce==0, old_state==None) the
    /// first write is permitted.
    Immutable { index: u8 },

    /// `new[i] >= old[i]` (unsigned big-endian). Covers expiry extensions,
    /// nullifier-root growth, append-only counters.
    Monotonic { index: u8 },

    /// `new[i] > old[i]` strictly. Auction bids, strictly-increasing
    /// sequence numbers. Added per eval §4 finding 2.
    StrictMonotonic { index: u8 },

    /// `slot[index]` may only be set (i.e. transition non-trivially) if
    /// `slot[witness_index]` is non-zero. Composable see-then-set.
    BoundedBy { index: u8, witness_index: u8 },

    /// `new[index] == old[index] + delta` (modular field arithmetic).
    ///
    /// **Note**: for decrements, encode `delta` as the additive-inverse in
    /// the field (e.g. for a u64 decrement of N, pick `delta` such that
    /// `u64_lo(old) + delta == u64_lo(old) - N` mod 2^64). See
    /// `SLOT-CAVEATS-EVALUATION.md` §8 open question 6.
    FieldDelta { index: u8, delta: FieldElement },

    /// `new[index] in [old[index] + min_delta, old[index] + max_delta]`.
    /// Anti-sniping deadline extensions, bounded growth.
    FieldDeltaInRange {
        index: u8,
        min_delta: FieldElement,
        max_delta: FieldElement,
    },

    /// `new[index] >= ctx.block_height + offset`. Replay-stable when the
    /// receipt carries the snapshot of the height at receipt-time.
    FieldGteHeight { index: u8, offset: i64 },

    /// `new[index] <= ctx.block_height + offset`. Replay-stable as above.
    FieldLteHeight { index: u8, offset: i64 },

    /// Intra-cell conservation across the transition:
    /// `sum(new[input_fields]) == sum(old[input_fields]) + sum(new[output_fields])`.
    /// Per eval finding 4: this is **intra-cell only**. Cross-cell
    /// conservation lives in [`StateConstraint::BoundDelta`].
    SumEqualsAcross {
        input_fields: Vec<u8>,
        output_fields: Vec<u8>,
    },

    // ─── Sender-bound predicates (use EvalContext) ───
    /// The turn's sender must be in an authorized set. The set may be
    /// published as a Merkle root sourced from a slot
    /// ([`AuthorizedSet::PublicRoot`]) or as a Poseidon2 blinded commitment
    /// ([`AuthorizedSet::BlindedSet`]).
    SenderAuthorized { set: AuthorizedSet },

    /// `slot[cap_set_root_slot]` is a per-cell capability-set root and
    /// must encode at most one live capability of the named kind.
    /// NFT-shape "exactly one owner cap" enforcement. Per eval §7.2 #5.
    /// Executor-side enforcement is a structural check on the cap-set
    /// root commitment; the variant exists so the constraint declaration
    /// is first-class.
    CapabilityUniqueness { cap_set_root_slot: u8 },

    // ─── Rate / temporal predicates ───
    /// Sender may mutate this cell at most `max_per_epoch` times per
    /// `epoch_duration` blocks. Backed by an executor-side counter keyed
    /// on `(cell, sender, epoch)`.
    RateLimit {
        max_per_epoch: u32,
        epoch_duration: u64,
    },

    /// Sum-based rate limit: the *value* added to `slot_index` over a
    /// window of `epoch_duration` blocks cannot exceed `max_sum_per_epoch`.
    /// Per eval §4.5 (renamed from `WindowedSum`). Backed by an
    /// executor-side per-(cell, slot, window) running sum.
    RateLimitBySum {
        slot_index: u8,
        max_sum_per_epoch: u64,
        epoch_duration: u64,
    },

    /// Mutation is rejected unless `ctx.block_height` is in
    /// `[not_before, not_after]`. Auction commit/reveal windows.
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },

    /// The action must reveal a preimage whose hash equals
    /// `slot[commitment_index]`. `hash_kind` selects Poseidon2 vs BLAKE3.
    PreimageGate {
        commitment_index: u8,
        hash_kind: HashKind,
    },

    /// `slot[seq_index] == old[seq_index] + 1`. Replay-safe sequencing.
    MonotonicSequence { seq_index: u8 },

    // ─── State-machine / witness-attached / cross-cell ───
    /// `(old[slot_index], new[slot_index])` must appear in the explicit
    /// allow-list `allowed`. Encodes a bounded state machine (Open →
    /// Claimed → Delivered → Paid, etc.). Per eval §7.1 #1.
    AllowedTransitions {
        slot_index: u8,
        /// Allowed `(old_value, new_value)` pairs.
        allowed: Vec<(FieldElement, FieldElement)>,
    },

    /// Witness-attached temporal-predicate proof. The action must carry a
    /// `TemporalPredicateProof` whose verifying key is referenced by
    /// `dsl_hash` and whose witness slot is `witness_index`. Per eval
    /// §1.3 + §7.2 #4. The executor invokes
    /// `circuit::temporal_predicate_dsl::verify_temporal_predicate` against
    /// the attached witness; this variant only *declares* the requirement.
    TemporalPredicate {
        witness_index: u8,
        dsl_hash: [u8; 32],
    },

    /// Cross-cell binding pair to γ.2: this cell's `local_slot` delta must
    /// match `peer_cell`'s `peer_slot` delta under the named
    /// [`DeltaRelation`]. The aggregate γ.2 match loop verifies the
    /// bilateral identity; this variant declares the per-cell half. Per
    /// eval §3.5 + §7.1 #3.
    BoundDelta {
        local_slot: u8,
        peer_cell: crate::id::CellId,
        peer_slot: u8,
        delta_relation: DeltaRelation,
    },

    /// Single-level disjunction: at least one of `variants` must hold.
    /// `variants` is restricted to [`SimpleStateConstraint`] (no nested
    /// `AnyOf`, no `Custom`). Per eval §4.3.
    AnyOf {
        variants: Vec<SimpleStateConstraint>,
    },

    // ─── Witness-attached unification (PREDICATE-INVENTORY §3) ───
    /// A witness-attached predicate (DFA classification, temporal-DSL
    /// proof, blinded-set non-revocation, bridge predicate, custom
    /// AIR…). Per PREDICATE-INVENTORY §3 / §7, this is the unified
    /// shape that subsumes the typed
    /// [`StateConstraint::TemporalPredicate`] variant (which is kept
    /// as a typed convenience but is structurally a `Witnessed { wp:
    /// WitnessedPredicate { kind: Temporal, … } }`).
    ///
    /// The executor evaluates by:
    /// 1. Resolving `wp.input_ref` against the cell state / action
    ///    witness / sender pk.
    /// 2. Reading the proof bytes from
    ///    `action.witness_blobs[wp.proof_witness_index]`.
    /// 3. Calling the registry's verifier for `wp.kind`.
    ///
    /// Replay: per PREDICATE-INVENTORY §6.3, the receipt snapshots the
    /// commitment at receipt-time so scope-2 replay is deterministic.
    Witnessed { wp: WitnessedPredicate },

    // ─── Escape hatch ───
    /// DSL-authored predicate. The executor evaluates by hash lookup in
    /// the pyana-dsl runtime expression table. Per eval §5.4 the variant
    /// carries a declared `reads` set (what slots/ctx fields the
    /// predicate touches) and a structured `descriptor`.
    Custom {
        /// Hash of the canonical DSL IR.
        ir_hash: [u8; 32],
        /// Structured human/version descriptor.
        descriptor: CustomDescriptor,
        /// Declared read-set — what the predicate touches.
        reads: ReadSet,
    },
}

/// Error from evaluating a cell program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    /// A state constraint was violated.
    ConstraintViolated {
        constraint: StateConstraint,
        description: String,
    },
    /// A field index in a constraint is out of bounds.
    InvalidFieldIndex { index: u8 },
    /// A circuit proof is required but was not provided.
    CircuitProofRequired { circuit_hash: [u8; 32] },
    /// Custom constraint cannot be evaluated locally (no registered IR).
    CustomConstraintUnevaluable { ir_hash: [u8; 32] },
    /// Immutable / transition constraint cannot be verified without prior state.
    /// Fail-closed: if there is no old_state to compare against, the constraint
    /// cannot be satisfied (unless this is a fresh cell with nonce == 0).
    TransitionCheckRequiresOldState {
        constraint: StateConstraint,
        index: u8,
    },
    /// Replay-sensitive constraint missing context.
    MissingContextField { field: &'static str },
    /// Cross-cell binding (`BoundDelta`) requires γ.2 wiring that is not yet
    /// available at this evaluation site.
    BoundDeltaNotWired { peer_cell: crate::id::CellId },
    /// `TemporalPredicate` requires an attached witness proof.
    TemporalPredicateWitnessMissing { dsl_hash: [u8; 32] },
    /// A `Witnessed { wp }` constraint cannot be evaluated locally
    /// because the executor's per-action witness-binding pass has not
    /// run yet (the executor's witnessed-predicate registry verifies
    /// the proof; the static evaluator only declares the requirement).
    WitnessedPredicateRequiresExecutor { kind_name: &'static str },
}

impl core::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProgramError::ConstraintViolated { description, .. } => {
                write!(f, "program constraint violated: {description}")
            }
            ProgramError::InvalidFieldIndex { index } => {
                write!(f, "program references invalid field index: {index}")
            }
            ProgramError::CircuitProofRequired { .. } => {
                write!(
                    f,
                    "circuit program requires a proof in the action authorization"
                )
            }
            ProgramError::CustomConstraintUnevaluable { .. } => {
                write!(f, "custom constraint cannot be evaluated locally")
            }
            ProgramError::TransitionCheckRequiresOldState { index, .. } => {
                write!(
                    f,
                    "transition constraint on field[{index}] cannot be verified without prior state"
                )
            }
            ProgramError::MissingContextField { field } => {
                write!(f, "missing EvalContext field for slot caveat: {field}")
            }
            ProgramError::BoundDeltaNotWired { .. } => {
                write!(f, "BoundDelta peer-cell wiring is not yet available")
            }
            ProgramError::TemporalPredicateWitnessMissing { .. } => {
                write!(f, "TemporalPredicate requires an attached witness proof")
            }
            ProgramError::WitnessedPredicateRequiresExecutor { kind_name } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) requires executor-side registry dispatch"
                )
            }
        }
    }
}

impl std::error::Error for ProgramError {}

/// Backwards-compatible alias for the v0 error name (kept so existing match
/// arms in `turn::executor::handle_program_violation` keep compiling). The
/// new name is `TransitionCheckRequiresOldState` — semantically broader,
/// since the same shape applies to all `(old, new)` transition variants.
#[allow(non_upper_case_globals)]
impl ProgramError {
    /// Legacy constructor name preserved for backwards compatibility.
    #[doc(hidden)]
    pub fn immutable_check_requires_old_state(index: u8) -> Self {
        ProgramError::TransitionCheckRequiresOldState {
            constraint: StateConstraint::Immutable { index },
            index,
        }
    }
}

impl CellProgram {
    /// Evaluate the program's constraints against the new (post-transition) state.
    ///
    /// For transition variants (`Immutable`, `WriteOnce`, `Monotonic`,
    /// `StrictMonotonic`, `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`,
    /// `SumEqualsAcross`, `MonotonicSequence`, `AllowedTransitions`),
    /// `old_state` is required to compare the field value before and after
    /// the transition. On the cell-initialization path (`old_state == None`
    /// AND `new_state.nonce == 0`), transition variants are permitted to
    /// initialize the field.
    ///
    /// For contextual variants (`FieldGteHeight`, `FieldLteHeight`,
    /// `TemporalGate`, `SenderAuthorized`, `RateLimit`, `RateLimitBySum`,
    /// `PreimageGate`, `TemporalPredicate`, `BoundDelta`), `ctx` supplies
    /// the runtime context. `ctx` may be omitted for purely static checks;
    /// in that case the contextual variants surface
    /// `ProgramError::MissingContextField`.
    pub fn evaluate(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
    ) -> Result<(), ProgramError> {
        match self {
            CellProgram::None => Ok(()),
            CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    evaluate_constraint(constraint, new_state, old_state, ctx)?;
                }
                Ok(())
            }
            CellProgram::Circuit { circuit_hash } => Err(ProgramError::CircuitProofRequired {
                circuit_hash: *circuit_hash,
            }),
        }
    }

    /// Backwards-compatible two-arg evaluation: equivalent to
    /// `evaluate(new, old, None)`. Use the three-arg form to support
    /// contextual variants (`SenderAuthorized`, `TemporalGate`, etc.).
    pub fn evaluate_static(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        self.evaluate(new_state, old_state, None)
    }

    /// Returns true if this program is `None` (backward-compatible no-op).
    pub fn is_none(&self) -> bool {
        matches!(self, CellProgram::None)
    }

    /// Returns true if this program requires proof authorization for state transitions.
    pub fn requires_proof(&self) -> bool {
        matches!(self, CellProgram::Circuit { .. })
    }
}

// ============================================================================
// Per-variant evaluators
// ============================================================================

fn check_index(index: u8) -> Result<usize, ProgramError> {
    let idx = index as usize;
    if idx >= STATE_SLOTS {
        return Err(ProgramError::InvalidFieldIndex { index });
    }
    Ok(idx)
}

/// Evaluate a single constraint against the cell state.
fn evaluate_constraint(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
) -> Result<(), ProgramError> {
    match constraint {
        StateConstraint::FieldEquals { index, value } => {
            let idx = check_index(*index)?;
            if new_state.fields[idx] != *value {
                return violated(constraint, format!("field[{idx}] != expected value"));
            }
            Ok(())
        }
        StateConstraint::FieldGte { index, value } => {
            let idx = check_index(*index)?;
            if !field_gte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] < minimum value"));
            }
            Ok(())
        }
        StateConstraint::FieldLte { index, value } => {
            let idx = check_index(*index)?;
            if !field_lte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] > maximum value"));
            }
            Ok(())
        }
        StateConstraint::SumEquals { indices, value } => {
            let mut sum: u64 = 0;
            for &idx in indices {
                let i = check_index(idx)?;
                sum = sum
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| ProgramError::ConstraintViolated {
                        constraint: constraint.clone(),
                        description: format!(
                            "overflow computing sum of fields {indices:?}: u64 addition overflowed"
                        ),
                    })?;
            }
            let expected = field_to_u64(value);
            if sum != expected {
                return violated(
                    constraint,
                    format!("sum of fields {indices:?} = {sum}, expected {expected}"),
                );
            }
            Ok(())
        }

        StateConstraint::Immutable { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if new_state.fields[idx] != old.fields[idx] {
                        return violated(
                            constraint,
                            format!("field[{idx}] was mutated but is marked immutable"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::WriteOnce { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    // Permitted: old slot was zero (first write) OR
                    // new == old (no change).
                    let old_zero = old.fields[idx] == FIELD_ZERO;
                    let unchanged = new_state.fields[idx] == old.fields[idx];
                    if !(old_zero || unchanged) {
                        return violated(
                            constraint,
                            format!("field[{idx}] is write-once and was already set"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::Monotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gte(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!("field[{idx}] decreased; Monotonic requires new >= old"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::StrictMonotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gt(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!(
                                "field[{idx}] did not strictly increase; StrictMonotonic requires new > old"
                            ),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::BoundedBy {
            index,
            witness_index,
        } => {
            let idx = check_index(*index)?;
            let widx = check_index(*witness_index)?;
            let changed = match old_state {
                Some(old) => new_state.fields[idx] != old.fields[idx],
                None => new_state.fields[idx] != FIELD_ZERO,
            };
            if changed {
                let armed = new_state.fields[widx] != FIELD_ZERO;
                if !armed {
                    return violated(
                        constraint,
                        format!(
                            "field[{idx}] changed but witness field[{widx}] is zero (BoundedBy)"
                        ),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::FieldDelta { index, delta } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let expected = field_add(&old.fields[idx], delta);
                    if new_state.fields[idx] != expected {
                        return violated(constraint, format!("field[{idx}] != old + delta"));
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldDeltaInRange {
            index,
            min_delta,
            max_delta,
        } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let lower = field_add(&old.fields[idx], min_delta);
                    let upper = field_add(&old.fields[idx], max_delta);
                    if !(field_gte(&new_state.fields[idx], &lower)
                        && field_lte(&new_state.fields[idx], &upper))
                    {
                        return violated(
                            constraint,
                            format!("field[{idx}] outside [old+min_delta, old+max_delta]"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldGteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value < bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} < block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::FieldLteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value > bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} > block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SumEqualsAcross {
            input_fields,
            output_fields,
        } => {
            let old = match old_state {
                Some(o) => o,
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: 0,
                        });
                    }
                    return Ok(());
                }
            };
            let mut new_in: u64 = 0;
            let mut old_in: u64 = 0;
            let mut new_out: u64 = 0;
            for &idx in input_fields {
                let i = check_index(idx)?;
                new_in = new_in
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
                old_in = old_in
                    .checked_add(field_to_u64(&old.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
            }
            for &idx in output_fields {
                let i = check_index(idx)?;
                new_out = new_out
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "output sum overflow"))?;
            }
            let rhs = old_in
                .checked_add(new_out)
                .ok_or_else(|| viol(constraint, "rhs overflow"))?;
            if new_in != rhs {
                return violated(
                    constraint,
                    format!(
                        "SumEqualsAcross: sum(new[in])={new_in} != sum(old[in])({old_in}) + sum(new[out])({new_out})"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SenderAuthorized { set } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let _sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            // Executor-side enforcement: structural — the actual Merkle
            // membership / non-revocation proof is verified by the
            // executor's authorization layer; this evaluator only
            // requires the context fields exist. AIR-side enforcement
            // (per design §4) is a future opt-in.
            match set {
                AuthorizedSet::PublicRoot { set_root_index } => {
                    let _ = check_index(*set_root_index)?;
                }
                AuthorizedSet::BlindedSet { .. } => {}
            }
            Ok(())
        }

        StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
            let _ = check_index(*cap_set_root_slot)?;
            // Structural declaration: enforcement is on the cap-set root
            // commitment shape; the variant exists so the constraint is
            // first-class in the schema.
            Ok(())
        }

        StateConstraint::RateLimit { max_per_epoch, .. } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "sender_epoch_count",
            })?;
            if ctx.sender_epoch_count >= *max_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "sender has {} mutations this epoch, max is {}",
                        ctx.sender_epoch_count, max_per_epoch
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::RateLimitBySum {
            slot_index,
            max_sum_per_epoch,
            ..
        } => {
            // Window-sum is supplied through the per-(cell, slot, window)
            // running sum tracked by the executor; that pre-aggregated
            // value comes in via `ctx.sender_epoch_count` repurposed as
            // the running per-window sum when the executor wires this
            // variant. Until then, evaluate the delta-bound directly: the
            // per-turn increment must not exceed the cap.
            let idx = check_index(*slot_index)?;
            let new_val = field_to_u64(&new_state.fields[idx]);
            let old_val = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            let delta = new_val.saturating_sub(old_val);
            if delta > *max_sum_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] delta={delta} exceeds max_sum_per_epoch={max_sum_per_epoch}"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalGate {
            not_before,
            not_after,
        } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            if let Some(nb) = not_before {
                if ctx.block_height < *nb {
                    return violated(
                        constraint,
                        format!("height {} < not_before {nb}", ctx.block_height),
                    );
                }
            }
            if let Some(na) = not_after {
                if ctx.block_height > *na {
                    return violated(
                        constraint,
                        format!("height {} > not_after {na}", ctx.block_height),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => {
            let idx = check_index(*commitment_index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "revealed_preimage",
            })?;
            let preimage = ctx
                .revealed_preimage
                .ok_or(ProgramError::MissingContextField {
                    field: "revealed_preimage",
                })?;
            let expected = new_state.fields[idx];
            let hash = match hash_kind {
                HashKind::Blake3 => *blake3::hash(&preimage).as_bytes(),
                HashKind::Poseidon2 => {
                    // Use BLAKE3 of a domain-tagged preimage as a stand-in
                    // until a Poseidon2-on-bytes helper is wired through
                    // here. Executor-side use only; AIR enforcement will
                    // use the actual Poseidon2 gadget.
                    let mut tagged = Vec::with_capacity(40);
                    tagged.extend_from_slice(b"poseidon2-stub:");
                    tagged.extend_from_slice(&preimage);
                    *blake3::hash(&tagged).as_bytes()
                }
            };
            if hash != expected {
                return violated(constraint, "preimage does not match commitment".into());
            }
            Ok(())
        }

        StateConstraint::MonotonicSequence { seq_index } => {
            let idx = check_index(*seq_index)?;
            match old_state {
                Some(old) => {
                    let old_seq = field_to_u64(&old.fields[idx]);
                    let new_seq = field_to_u64(&new_state.fields[idx]);
                    if new_seq != old_seq.wrapping_add(1) {
                        return violated(
                            constraint,
                            format!("seq[{idx}]: expected {} got {}", old_seq + 1, new_seq),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *seq_index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::AllowedTransitions {
            slot_index,
            allowed,
        } => {
            let idx = check_index(*slot_index)?;
            let new_v = new_state.fields[idx];
            let old_v = old_state.map(|o| o.fields[idx]).unwrap_or(FIELD_ZERO);
            let ok = allowed.iter().any(|(o, n)| *o == old_v && *n == new_v);
            if !ok {
                return violated(
                    constraint,
                    format!("transition on slot[{idx}] is not in the allow-list"),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalPredicate { dsl_hash, .. } => {
            // The actual proof verification is done by the executor's
            // proof-attached-effect path. The constraint exists so the
            // cell program declares it requires a witness; if the
            // executor failed to wire a witness, surface the error here.
            Err(ProgramError::TemporalPredicateWitnessMissing {
                dsl_hash: *dsl_hash,
            })
        }

        StateConstraint::BoundDelta { peer_cell, .. } => {
            // Cross-cell binding is verified by γ.2's cross-cell match
            // loop in the turn executor (post-effect, pre-commit). The
            // per-cell evaluator does not have peer-cell state in scope;
            // it surfaces a sentinel error the executor maps to the
            // cross-cell path.
            Err(ProgramError::BoundDeltaNotWired {
                peer_cell: *peer_cell,
            })
        }

        StateConstraint::AnyOf { variants } => {
            if variants.is_empty() {
                return violated(constraint, "AnyOf with no variants".into());
            }
            let mut last_err: Option<ProgramError> = None;
            for v in variants {
                let lifted = lift_simple(v);
                match evaluate_constraint(&lifted, new_state, old_state, ctx) {
                    Ok(()) => return Ok(()),
                    Err(e) => last_err = Some(e),
                }
            }
            Err(
                last_err.unwrap_or_else(|| ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: "no AnyOf branch satisfied".into(),
                }),
            )
        }

        StateConstraint::Witnessed { wp } => {
            // The static evaluator does not have access to the
            // executor's witness-binding pass; it surfaces the
            // sentinel so the executor's witnessed-predicate dispatch
            // path can intercept and call the registered verifier.
            let kind_name: &'static str = match wp.kind {
                crate::predicate::WitnessedPredicateKind::Dfa => "Dfa",
                crate::predicate::WitnessedPredicateKind::Temporal => "Temporal",
                crate::predicate::WitnessedPredicateKind::MerkleMembership => "MerkleMembership",
                crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                crate::predicate::WitnessedPredicateKind::BridgePredicate => "BridgePredicate",
                crate::predicate::WitnessedPredicateKind::PedersenEquality => "PedersenEquality",
                crate::predicate::WitnessedPredicateKind::Custom { .. } => "Custom",
            };
            Err(ProgramError::WitnessedPredicateRequiresExecutor { kind_name })
        }

        StateConstraint::Custom { ir_hash, .. } => {
            Err(ProgramError::CustomConstraintUnevaluable { ir_hash: *ir_hash })
        }
    }
}

fn violated(constraint: &StateConstraint, description: String) -> Result<(), ProgramError> {
    Err(ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description,
    })
}

fn viol(constraint: &StateConstraint, description: &str) -> ProgramError {
    ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description: description.to_string(),
    }
}

/// Lift a `SimpleStateConstraint` into the full `StateConstraint` enum so
/// the same evaluator can handle AnyOf branches.
fn lift_simple(s: &SimpleStateConstraint) -> StateConstraint {
    match *s {
        SimpleStateConstraint::FieldEquals { index, value } => {
            StateConstraint::FieldEquals { index, value }
        }
        SimpleStateConstraint::FieldGte { index, value } => {
            StateConstraint::FieldGte { index, value }
        }
        SimpleStateConstraint::FieldLte { index, value } => {
            StateConstraint::FieldLte { index, value }
        }
        SimpleStateConstraint::WriteOnce { index } => StateConstraint::WriteOnce { index },
        SimpleStateConstraint::Immutable { index } => StateConstraint::Immutable { index },
        SimpleStateConstraint::Monotonic { index } => StateConstraint::Monotonic { index },
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraint::StrictMonotonic { index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraint::BoundedBy {
            index,
            witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraint::FieldGteHeight { index, offset }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraint::FieldLteHeight { index, offset }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraint::TemporalGate {
            not_before,
            not_after,
        },
    }
}

// ============================================================================
// Field arithmetic / comparisons
// ============================================================================

/// Interpret a field element as a big-endian u64 (last 8 bytes).
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

/// Compare two field elements as unsigned big-endian: a >= b.
fn field_gte(a: &FieldElement, b: &FieldElement) -> bool {
    a >= b
}

/// Compare two field elements as unsigned big-endian: a <= b.
fn field_lte(a: &FieldElement, b: &FieldElement) -> bool {
    field_gte(b, a)
}

/// Compare two field elements as unsigned big-endian: a > b strictly.
fn field_gt(a: &FieldElement, b: &FieldElement) -> bool {
    a > b
}

/// Field addition modulo the byte-array representation (u64 lane in last 8
/// bytes). For decrements, encode `delta` as the additive inverse. See
/// `SLOT-CAVEATS-EVALUATION.md` §8 question 6.
fn field_add(a: &FieldElement, b: &FieldElement) -> FieldElement {
    let av = field_to_u64(a);
    let bv = field_to_u64(b);
    let s = av.wrapping_add(bv);
    let mut out = *a;
    out[24..32].copy_from_slice(&s.to_be_bytes());
    out
}

/// Helper: create a FieldElement from a u64 (big-endian in last 8 bytes).
pub fn field_from_u64(val: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[24..32].copy_from_slice(&val.to_be_bytes());
    f
}

/// Alias for `field_from_u64` — explicit big-endian naming for clarity at call sites.
pub fn field_from_u64_be(val: u64) -> FieldElement {
    field_from_u64(val)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preconditions::EvalContext;

    fn ctx_at(height: u64) -> EvalContext {
        EvalContext {
            block_height: height,
            ..Default::default()
        }
    }

    fn ctx_sender(sender: [u8; 32], epoch_count: u32) -> EvalContext {
        EvalContext {
            sender: Some(sender),
            sender_epoch_count: epoch_count,
            ..Default::default()
        }
    }

    fn ctx_preimage(p: [u8; 32]) -> EvalContext {
        EvalContext {
            revealed_preimage: Some(p),
            ..Default::default()
        }
    }

    // ── Existing variants (regression) ───────────────────────────────────

    #[test]
    fn no_program_backward_compat() {
        let p = CellProgram::None;
        let s = CellState::new(100);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn field_equals_pass_and_fail() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(42),
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn immutable_round_trip() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut old = CellState::new(0);
        old.fields[3] = field_from_u64(77);
        let mut new_s = old.clone();
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[3] = field_from_u64(88);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn immutable_no_old_state_init_path() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut s = CellState::new(0);
        s.fields[3] = field_from_u64(77);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn immutable_no_old_state_with_history_fails_closed() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut s = CellState::new(0);
        s.fields[3] = field_from_u64(77);
        s.set_nonce(5);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(
            err,
            ProgramError::TransitionCheckRequiresOldState { .. }
        ));
    }

    // ── New variants ──────────────────────────────────────────────────────

    #[test]
    fn write_once_first_write_then_frozen() {
        let p = CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }]);
        // First write: old slot is zero, new is non-zero — allowed.
        let mut old = CellState::new(0);
        let mut new_s = CellState::new(0);
        new_s.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Subsequent write attempt: old is non-zero, new differs — rejected.
        old.fields[0] = field_from_u64(42);
        let mut tampered = old.clone();
        tampered.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&tampered, Some(&old), None).is_err());
        // Unchanged: allowed.
        assert!(p.evaluate(&old, Some(&old), None).is_ok());
    }

    #[test]
    fn monotonic_only_increases() {
        let p = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 1 }]);
        let mut old = CellState::new(0);
        old.fields[1] = field_from_u64(10);
        let mut new_s = old.clone();
        new_s.fields[1] = field_from_u64(20);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[1] = field_from_u64(10);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok()); // equal allowed
        new_s.fields[1] = field_from_u64(5);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
    }

    #[test]
    fn strict_monotonic_must_strictly_increase() {
        let p = CellProgram::Predicate(vec![StateConstraint::StrictMonotonic { index: 0 }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(10);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(11);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(10);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // equal rejected
        new_s.fields[0] = field_from_u64(9);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
    }

    #[test]
    fn bounded_by_requires_witness_armed() {
        let p = CellProgram::Predicate(vec![StateConstraint::BoundedBy {
            index: 0,
            witness_index: 1,
        }]);
        let old = CellState::new(0);
        // Change slot 0 with witness zero → rejected.
        let mut new_s = CellState::new(0);
        new_s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
        // Change slot 0 with witness non-zero → allowed.
        new_s.fields[1] = field_from_u64(1);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    }

    #[test]
    fn field_delta_exact_step() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldDelta {
            index: 0,
            delta: field_from_u64(100),
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(500);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(600);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(700);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn field_delta_in_range() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldDeltaInRange {
            index: 0,
            min_delta: field_from_u64(0),
            max_delta: field_from_u64(10),
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(55);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(70);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn field_gte_height_uses_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldGteHeight {
            index: 0,
            offset: 100,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(250);
        // current_height=100, expiry=250, bound=100+100=200, 250>=200 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
        // bound=300 (height=200, offset=100): 250<300 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_at(200))).is_err());
    }

    #[test]
    fn field_lte_height_uses_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldLteHeight {
            index: 0,
            offset: 100,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(150);
        // bound = 100+100=200, 150<=200 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
        // bound = 50+100=150 with value 150 → still ok (equal)
        assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_ok());
        // bound = 49+100=149, 150>149 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_at(49))).is_err());
    }

    #[test]
    fn sum_equals_across_intra_cell_conservation() {
        // sum(new[0,1]) == sum(old[0,1]) + sum(new[2,3])
        let p = CellProgram::Predicate(vec![StateConstraint::SumEqualsAcross {
            input_fields: vec![0, 1],
            output_fields: vec![2, 3],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(100);
        old.fields[1] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(160);
        new_s.fields[1] = field_from_u64(80);
        new_s.fields[2] = field_from_u64(60);
        new_s.fields[3] = field_from_u64(30);
        // sum(new in) = 240, sum(old in)=150, sum(new out)=90, 150+90=240 ✓
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[2] = field_from_u64(0);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn sender_authorized_needs_sender_in_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
            set: AuthorizedSet::PublicRoot { set_root_index: 7 },
        }]);
        let s = CellState::new(0);
        // No ctx → MissingContextField
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // ctx with no sender → also missing
        let bare = EvalContext::default();
        let err = p.evaluate(&s, None, Some(&bare)).unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // ctx with sender → ok
        assert!(
            p.evaluate(&s, None, Some(&ctx_sender([1u8; 32], 0)))
                .is_ok()
        );
    }

    #[test]
    fn rate_limit_enforces_per_epoch_cap() {
        let p = CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 100,
        }]);
        let s = CellState::new(0);
        let sender = [9u8; 32];
        // 0 < 3 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 0))).is_ok());
        // 2 < 3 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 2))).is_ok());
        // 3 >= 3 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 3))).is_err());
    }

    #[test]
    fn rate_limit_by_sum_caps_delta() {
        let p = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 100,
            epoch_duration: 1000,
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(140); // +90 < 100 → ok
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(200); // +150 > 100 → fail
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn temporal_gate_enforces_window() {
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalGate {
            not_before: Some(100),
            not_after: Some(200),
        }]);
        let s = CellState::new(0);
        assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_err());
        assert!(p.evaluate(&s, None, Some(&ctx_at(150))).is_ok());
        assert!(p.evaluate(&s, None, Some(&ctx_at(250))).is_err());
    }

    #[test]
    fn preimage_gate_verifies_hash() {
        let preimage = [7u8; 32];
        let commitment = *blake3::hash(&preimage).as_bytes();
        let p = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
            commitment_index: 0,
            hash_kind: HashKind::Blake3,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = commitment;
        // Correct preimage → ok
        assert!(p.evaluate(&s, None, Some(&ctx_preimage(preimage))).is_ok());
        // Wrong preimage → fail
        assert!(
            p.evaluate(&s, None, Some(&ctx_preimage([8u8; 32])))
                .is_err()
        );
        // No preimage in ctx → missing
        assert!(p.evaluate(&s, None, Some(&EvalContext::default())).is_err());
    }

    #[test]
    fn monotonic_sequence_increments_by_one() {
        let p = CellProgram::Predicate(vec![StateConstraint::MonotonicSequence { seq_index: 0 }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(5);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(6);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // skipped one
        new_s.fields[0] = field_from_u64(5);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // no increment
    }

    #[test]
    fn allowed_transitions_state_machine() {
        let open = field_from_u64(1);
        let claimed = field_from_u64(2);
        let paid = field_from_u64(3);
        let p = CellProgram::Predicate(vec![StateConstraint::AllowedTransitions {
            slot_index: 0,
            allowed: vec![(open, claimed), (claimed, paid)],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = open;
        let mut new_s = old.clone();
        new_s.fields[0] = claimed;
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = paid;
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // Open→Paid not allowed
    }

    #[test]
    fn temporal_predicate_requires_witness() {
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0xAB; 32],
        }]);
        let s = CellState::new(0);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(
            err,
            ProgramError::TemporalPredicateWitnessMissing { .. }
        ));
    }

    #[test]
    fn bound_delta_surfaces_cross_cell_sentinel() {
        let peer = crate::id::CellId::from_bytes([7u8; 32]);
        let p = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: peer,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        let s = CellState::new(0);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(err, ProgramError::BoundDeltaNotWired { .. }));
    }

    #[test]
    fn any_of_one_branch_must_hold() {
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(7),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(9),
                },
            ],
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(9);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(11);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn capability_uniqueness_index_bounds_checked() {
        let p = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
            cap_set_root_slot: 200,
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::InvalidFieldIndex { .. }
        ));
    }

    #[test]
    fn custom_remains_fail_closed_without_runtime() {
        let p = CellProgram::Predicate(vec![StateConstraint::Custom {
            ir_hash: [0u8; 32],
            descriptor: CustomDescriptor::default(),
            reads: ReadSet::default(),
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::CustomConstraintUnevaluable { .. }
        ));
    }

    // ── Adversarial / multi-constraint ────────────────────────────────────

    #[test]
    fn multiple_constraints_all_must_pass() {
        let p = CellProgram::Predicate(vec![
            StateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(10),
            },
            StateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(100),
            },
        ]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(50);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(5);
        assert!(p.evaluate(&s, None, None).is_err());
        s.fields[0] = field_from_u64(200);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn invalid_field_index() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 99,
            value: field_from_u64(1),
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::InvalidFieldIndex { index: 99 }
        ));
    }

    #[test]
    fn circuit_program_requires_proof() {
        let p = CellProgram::Circuit {
            circuit_hash: [0xAB; 32],
        };
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::CircuitProofRequired { .. }
        ));
    }
}
