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
use crate::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
    WitnessedPredicateRegistry,
};
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
    ///
    /// **Legacy shape** (Cav-Codex Block 4). Semantically equivalent to
    /// `Cases(vec![TransitionCase { guard: TransitionGuard::Always,
    /// constraints: <these> }])`. The shape is preserved during the
    /// substrate-correctness migration; new programs should prefer
    /// `Cases { .. }` since it can scope constraints to specific
    /// transitions (e.g. `send` vs `dequeue` on a `CapInbox`).
    Predicate(Vec<StateConstraint>),

    /// Operation-scoped cases (Cav-Codex Block 4). Each
    /// [`TransitionCase`] declares a guard naming which transitions it
    /// applies to and the constraints that must hold on those
    /// transitions. Multiple cases may match a single transition; all
    /// matching cases' constraints AND together.
    ///
    /// If **no** case matches a transition, the program **default-denies**
    /// (the action's effects on this cell are rejected). This means a
    /// `Cases([])` program rejects every transition; to allow arbitrary
    /// transitions add an `Always`-guarded case with no constraints.
    ///
    /// Use cases:
    /// - A `CapInbox` cell with separate cases for `send` (head advances
    ///   by 1, tail unchanged) and `dequeue` (tail advances by 1, head
    ///   unchanged).
    /// - A factory cell that allows mint-style transitions on one method
    ///   and burn-style on another.
    /// - A state-machine cell whose allowed transitions depend on the
    ///   action's method symbol.
    Cases(Vec<TransitionCase>),

    /// Circuit program: an AIR/R1CS circuit that defines the valid state transition function.
    /// The proof in the Action's authorization MUST satisfy this circuit.
    Circuit {
        /// Hash of the circuit (for lookup/verification).
        circuit_hash: [u8; 32],
    },
}

/// A single operation-scoped case in a [`CellProgram::Cases`] program.
///
/// Each case declares a *guard* (what transitions does this case apply
/// to?) and a *constraint list* (when this case applies, all these
/// constraints must hold).
///
/// Per Cav-Codex Block 4: when multiple cases match a single transition,
/// their constraints are ANDed together. When **no** case matches, the
/// program default-denies.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionCase {
    /// When does this case apply?
    pub guard: TransitionGuard,
    /// Constraints that must hold when the guard matches.
    pub constraints: Vec<StateConstraint>,
}

/// Guard for a [`TransitionCase`]: names which transitions a case
/// applies to.
///
/// Guards compose via `AnyOf` / `AllOf`. A transition matches a guard
/// when:
/// - `Always` — every transition (legacy `Predicate` shape lowers to
///   this).
/// - `MethodIs { method }` — the action's method symbol equals
///   `method`.
/// - `EffectKindIs { mask }` — at least one effect in the action's
///   effect list has its `effect_kind_mask()` intersecting `mask`.
/// - `SlotChanged { index }` — slot `index` of the cell's state changed
///   on this transition (`new[index] != old[index]`).
/// - `AnyOf` / `AllOf` — boolean composition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransitionGuard {
    /// Always matches; the case's constraints apply to every transition.
    /// Used to lift the legacy `Predicate(...)` shape into a single case.
    Always,
    /// Match when the action's method symbol equals `method` (the
    /// 32-byte BLAKE3 hash of the method name).
    MethodIs { method: [u8; 32] },
    /// Match when the action carries an effect whose
    /// `effect_kind_mask()` intersects `mask` (i.e. at least one effect
    /// is of a kind in the mask).
    EffectKindIs { mask: u32 },
    /// Match when `new_state[index] != old_state[index]` (slot `index`
    /// changed during this transition).
    SlotChanged { index: u8 },
    /// Disjunction — match if any child matches.
    AnyOf(Vec<TransitionGuard>),
    /// Conjunction — match if every child matches.
    AllOf(Vec<TransitionGuard>),
}

/// A single witness payload bound by index inside a [`WitnessBundle`].
///
/// Per Cav-Codex Block 3: identifies a kind-tag plus an opaque byte
/// payload. Concrete shapes live in `pyana_turn::action::WitnessKind /
/// WitnessBlob`; this cell-side mirror exists so the program evaluator
/// can dispatch witnesses without depending on the turn crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessKindTag {
    Preimage32,
    MerklePath,
    RateLimitCount,
    ProofBytes,
    Cleartext,
}

/// A view into an [`crate::Action`]-equivalent witness blob, kept
/// behind a borrowed slice to avoid copies through the evaluator.
#[derive(Clone, Copy, Debug)]
pub struct WitnessBlobView<'a> {
    pub kind: WitnessKindTag,
    pub bytes: &'a [u8],
}

/// A bundle of witness blobs the executor passes alongside the action
/// when evaluating a `CellProgram`.
#[derive(Clone, Copy, Debug, Default)]
pub struct WitnessBundle<'a> {
    /// The witness blobs the action carries (indexed).
    pub blobs: &'a [WitnessBlobView<'a>],
    /// Registered verifiers for witnessed-predicate dispatch.
    pub registry: Option<&'a WitnessedPredicateRegistry>,
}

impl<'a> WitnessBundle<'a> {
    pub fn empty() -> Self {
        Self {
            blobs: &[],
            registry: None,
        }
    }

    pub fn blob(&self, idx: usize) -> Option<&'a WitnessBlobView<'a>> {
        self.blobs.get(idx)
    }
}

/// Per-transition context evaluated against [`TransitionGuard`]s.
///
/// Built by the executor for each (cell, action) pair before evaluating
/// the cell's `CellProgram`. Holds the action-level signals (method,
/// effect mask, sender) plus the (old, new) state pair from which slot
/// deltas are derived.
#[derive(Clone, Debug)]
pub struct TransitionMeta {
    /// The action's method symbol (BLAKE3 hash of method name).
    pub method: [u8; 32],
    /// Bitwise-OR of every effect's `effect_kind_mask()`.
    pub effects_mask: u32,
}

impl TransitionMeta {
    /// Construct a context with explicit method and effects mask.
    pub fn new(method: [u8; 32], effects_mask: u32) -> Self {
        Self {
            method,
            effects_mask,
        }
    }
    /// A wildcard meta — matches `Always` only; useful for tests.
    pub fn wildcard() -> Self {
        Self {
            method: [0u8; 32],
            effects_mask: 0,
        }
    }
}

impl TransitionGuard {
    /// Evaluate this guard against a transition.
    pub fn matches(
        &self,
        meta: &TransitionMeta,
        old_state: Option<&CellState>,
        new_state: &CellState,
    ) -> bool {
        match self {
            TransitionGuard::Always => true,
            TransitionGuard::MethodIs { method } => meta.method == *method,
            TransitionGuard::EffectKindIs { mask } => meta.effects_mask & *mask != 0,
            TransitionGuard::SlotChanged { index } => {
                let idx = *index as usize;
                if idx >= STATE_SLOTS {
                    return false;
                }
                match old_state {
                    Some(old) => new_state.fields[idx] != old.fields[idx],
                    None => new_state.fields[idx] != FIELD_ZERO,
                }
            }
            TransitionGuard::AnyOf(children) => children
                .iter()
                .any(|g| g.matches(meta, old_state, new_state)),
            TransitionGuard::AllOf(children) => children
                .iter()
                .all(|g| g.matches(meta, old_state, new_state)),
        }
    }

    /// Returns `true` if this guard discriminates on the action's
    /// *method or effect dispatch* (i.e., is operation-binding rather
    /// than a pure state invariant).
    ///
    /// Cav-Codex Block 4 default-deny: when a `CellProgram::Cases` value
    /// has at least one operation-binding case, the executor must treat
    /// an action whose method matches *none* of them as
    /// `NoTransitionCaseMatched` — even if a separate `Always`-guarded
    /// invariants case still matches. Without this distinction the
    /// `Always` case silently absorbs unknown methods (and only the
    /// invariants get checked), which is exactly the
    /// `unknown_method_default_denied` shape the
    /// `starbridge-subscription` / `starbridge-governed-namespace` /
    /// `pyana-storage-templates::cap_inbox` tests assert against.
    pub fn is_method_dispatching(&self) -> bool {
        match self {
            TransitionGuard::Always => false,
            TransitionGuard::MethodIs { .. } => true,
            TransitionGuard::EffectKindIs { .. } => true,
            TransitionGuard::SlotChanged { .. } => false,
            TransitionGuard::AnyOf(children) | TransitionGuard::AllOf(children) => {
                children.iter().any(|g| g.is_method_dispatching())
            }
        }
    }
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
    /// Cross-app: senders authorized by holding a credential issued from a
    /// known identity-issuer cell against a pinned schema commitment.
    ///
    /// The witness side carries a `ProofBytes` blob whose contents are a
    /// `pyana_credentials::Presentation` (or its proof bytes) that the
    /// registered `WitnessedPredicateKind::BlindedSet` verifier accepts:
    /// the verifier reads the issuer cell's `REVOCATION_ROOT_SLOT` and
    /// `SCHEMA_COMMITMENT_SLOT` out-of-band, confirms the schema commitment
    /// matches `credential_schema_id`, and validates non-revocation
    /// against the issuer's published revocation root. The on-cell
    /// `commitment` baked here is `blake3("pyana-credential-set-v1" ||
    /// issuer_cell || credential_schema_id)` — a stable identifier
    /// derived from the (issuer, schema) pair so two distinct issuer
    /// cells (or two distinct schemas) produce distinct commitments
    /// and a verifier can dispatch deterministically.
    ///
    /// This variant is the substrate primitive that powers
    /// `starbridge-governed-namespace`'s credential-gated voting and
    /// `starbridge-nameservice`'s identity-attested tier — composing
    /// the identity app with namespace + nameservice without inventing
    /// a domain-specific `Effect::PresentCredential` or similar.
    CredentialSet {
        /// The identity-issuer cell ID (the cell whose
        /// `SCHEMA_COMMITMENT_SLOT` and `REVOCATION_ROOT_SLOT` the
        /// verifier reads out-of-band).
        issuer_cell: [u8; 32],
        /// The credential schema commitment the verifier insists matches
        /// the issuer cell's pinned schema. Mirrors
        /// `starbridge_identity::schema_commitment(&schema)`.
        credential_schema_id: [u8; 32],
    },
}

impl AuthorizedSet {
    /// Compute the stable 32-byte commitment under which a
    /// [`AuthorizedSet::CredentialSet`] dispatches to the
    /// `WitnessedPredicateKind::BlindedSet` verifier registered in the
    /// executor's `WitnessedPredicateRegistry`.
    ///
    /// `blake3_derive_key("pyana-credential-set-v1") || issuer_cell ||
    /// credential_schema_id`. Stable across builds; replay-safe across
    /// distinct (issuer, schema) pairs.
    ///
    /// Public so cross-app code (`starbridge-governed-namespace`'s
    /// credential-gated voting, `starbridge-nameservice`'s
    /// identity-attested tier, etc.) can reproduce the value the
    /// executor sees on dispatch without depending on the cell crate's
    /// private hashing routines.
    pub fn credential_set_commitment(
        issuer_cell: &[u8; 32],
        credential_schema_id: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-credential-set-v1");
        hasher.update(issuer_cell);
        hasher.update(credential_schema_id);
        *hasher.finalize().as_bytes()
    }
}

/// Source for [`StateConstraint::Renounced`]'s sender-non-membership
/// check. Mirrors [`AuthorizedSet`] but the predicate is *negative* —
/// the sender's identity must verifiably NOT be in the named sorted
/// leaf set. See `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RenouncedSet {
    /// Public Merkle root of the *unheld* sorted leaf set, sourced from
    /// slot `set_root_index`. The action's witness side carries a
    /// non-membership neighbor-witness proof against the root.
    PublicRoot { set_root_index: u8 },
    /// Blinded sorted-set commitment. The witness side carries a
    /// non-membership neighbor-witness against the commitment.
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
///
/// # Heyting fragment — `Not`
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 + §9.1.1, the predicate
/// algebra is lifted from a *distributive lattice* (conjunction via
/// `Vec`, disjunction via [`StateConstraint::AnyOf`]) to a *Heyting
/// algebra* by admitting a `Not` constructor. The inner is restricted
/// to a non-`Not` `SimpleStateConstraint` so the variant cannot nest
/// without bound (every Heyting-shaped predicate an app needs decomposes
/// into single-level negation + composition under `AnyOf` /
/// `Vec<StateConstraint>`).
///
/// Implication `P ⇒ Q` is derived rather than added as a variant:
/// `Implies(P, Q) == AnyOf(vec![Not(P), Q])`. See
/// [`SimpleStateConstraint::implies`] and
/// [`StateConstraint::implies`].
///
/// **Semantics under failure:** `Not` short-circuits on the *acceptance
/// bit* of the inner constraint. If the inner evaluator surfaces a
/// structural error (`MissingContextField`, `InvalidFieldIndex`,
/// `TransitionCheckRequiresOldState`, etc.) the `Not` evaluator
/// propagates the **error** rather than treating it as a rejection-to-
/// negate. This preserves fail-closed behavior — negating an unevaluable
/// predicate is itself unevaluable, not vacuously satisfied.
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
    /// Negation — accept iff the inner constraint *rejects*. Per
    /// `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 / §9.1.1: the missing
    /// initial-object / exponential operator that lifts the predicate
    /// algebra from distributive lattice to Heyting algebra.
    ///
    /// The inner is `Box<SimpleStateConstraint>` (not `StateConstraint`)
    /// so the variant cannot nest into the witness-attached / cross-cell
    /// shapes (`Witnessed`, `BoundDelta`, `Custom`, `TemporalPredicate`).
    /// Apps that need non-membership against a blinded set get it via
    /// the existing `circuit::non_membership` AIR through a `Custom`
    /// predicate; `Not` is the structural surface for the static /
    /// transition / contextual subset.
    ///
    /// **Acceptance:** `inner` evaluates to a structural error → `Not`
    /// surfaces the same error (fail-closed). `inner` evaluates to
    /// `Ok(())` (accept) → `Not` rejects. `inner` evaluates to
    /// `Err(ConstraintViolated)` (reject) → `Not` accepts.
    ///
    /// **Double-negation:** `Not(Not(c))` is *not* representable
    /// because the inner is unboxed `SimpleStateConstraint` (and `Not`
    /// itself is a `SimpleStateConstraint` variant). The plan
    /// deliberately blocks this; double-negation reduces to the original
    /// constraint definitionally and offers no expressive power.
    /// Re-using a wrapper for "obvious tautology" violates the
    /// short-circuit / fail-closed invariants above, so the type system
    /// shapes against it.
    Not(Box<SimpleStateConstraint>),
}

impl SimpleStateConstraint {
    /// Sugar: build `Implies(self, consequent)` as `AnyOf(Not(self),
    /// consequent)`. Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 the
    /// Heyting implication is derived rather than added as a new
    /// variant; this helper yields the canonical encoding so authors
    /// don't open-code it (and so the evaluator stays simple).
    ///
    /// Returns a `StateConstraint::AnyOf { variants }` rather than a
    /// `SimpleStateConstraint` because the conventional flattening
    /// lives at the outer enum (it composes naturally with the rest of
    /// the slot caveat list).
    pub fn implies(self, consequent: SimpleStateConstraint) -> StateConstraint {
        StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(self)), consequent],
        }
    }
}

impl StateConstraint {
    /// Sugar: `P ⇒ Q == AnyOf(Not(P), Q)` lifted into the outer enum.
    ///
    /// Restricts both sides to [`SimpleStateConstraint`] so the
    /// derived encoding nests inside the existing `AnyOf` shape (which
    /// per `SLOT-CAVEATS-EVALUATION.md` §4.3 only accepts simples).
    /// Apps wanting implication over witnessed / cross-cell predicates
    /// must go through a `Custom` predicate.
    pub fn implies(antecedent: SimpleStateConstraint, consequent: SimpleStateConstraint) -> Self {
        antecedent.implies(consequent)
    }
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

    /// **Categorical dual of [`Self::SenderAuthorized`]: proof of
    /// non-holding / non-membership.** A *renunciation* slot caveat —
    /// the action's sender must verifiably *NOT* be in the
    /// `set`'s sorted Merkle leaf set. Implemented as a typed shim
    /// that dispatches through the
    /// [`crate::predicate::WitnessedPredicateKind::NonMembership`]
    /// verifier in the registry, using the sender pk as the candidate
    /// input and the commitment carried in `set`.
    ///
    /// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2 / §9.2.1`:
    /// `Renunciation` is the initial-object dual of `Authorization`.
    /// `SenderAuthorized` says "I prove I have authority"; `Renounced`
    /// says "I prove I lack authority over THIS set." App drivers:
    /// *governance recusal* ("I attest I do not hold a conflicting-
    /// interest cap before voting"), *compliance attestation* ("the
    /// sender is not on the blacklist"), *revocation lookups* (the
    /// sender's identity is not in the revocation set), *selective
    /// non-disclosure* ("the sender is not in the under-18 set").
    ///
    /// The variant exists as a structurally separate slot caveat from
    /// `Witnessed { wp: WitnessedPredicate { kind: NonMembership, … } }`
    /// so audit tooling can clearly distinguish "this cell requires
    /// the sender to *be* in a set" (positive auth) from "this cell
    /// requires the sender to *not* be in a set" (renunciation). The
    /// underlying gadget is shared.
    ///
    /// Replay: like `SenderAuthorized`, replay is deterministic once
    /// the commitment (or its slot snapshot) is carried in the receipt.
    Renounced {
        /// The sorted-set commitment the sender must *not* be in.
        /// Either a slot-borne public root or a fixed blinded
        /// commitment (mirrors [`AuthorizedSet`]).
        set: RenouncedSet,
    },

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
    /// `CellProgram::Cases(_)` was evaluated against a transition where
    /// no case matched. Default-deny per Cav-Codex Block 4.
    NoTransitionCaseMatched,
    /// The witnessed-predicate registry returned a verifier rejection
    /// (proof was malformed or the verifier rejected the input).
    WitnessedPredicateRejected {
        kind_name: &'static str,
        reason: String,
    },
    /// `SenderAuthorized` requires a Merkle-membership witness blob but
    /// the action did not carry one at the expected index.
    SenderMembershipWitnessMissing,
    /// The action did not carry the `PreimageGate`'s expected preimage
    /// blob, or it was at the wrong witness index / wrong type.
    PreimageWitnessMissing,
    /// A `Custom { ir_hash }` predicate requires a registered custom
    /// program verifier; either the action did not carry a proof at
    /// the expected witness index or no verifier matched the
    /// declared vk hash.
    CustomProgramProofRejected { ir_hash: [u8; 32], reason: String },
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
            ProgramError::NoTransitionCaseMatched => {
                write!(
                    f,
                    "Cases program: no transition case matched the action — default-deny"
                )
            }
            ProgramError::WitnessedPredicateRejected { kind_name, reason } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) rejected by registered verifier: {reason}"
                )
            }
            ProgramError::SenderMembershipWitnessMissing => {
                write!(
                    f,
                    "SenderAuthorized requires a Merkle-membership witness blob; action did not carry one"
                )
            }
            ProgramError::PreimageWitnessMissing => {
                write!(
                    f,
                    "PreimageGate requires a 32-byte Preimage32 witness blob; action did not carry one"
                )
            }
            ProgramError::CustomProgramProofRejected { reason, .. } => {
                write!(f, "custom program proof rejected: {reason}")
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
        // Legacy entry-point: callers that don't have a TransitionMeta
        // fall through to a `wildcard` meta (matches only `Always`
        // guards). New `Cases` programs that depend on method or
        // effect-kind guards should use `evaluate_with_meta`.
        self.evaluate_with_meta(new_state, old_state, ctx, &TransitionMeta::wildcard())
    }

    /// Evaluate the program with a [`TransitionMeta`] in scope.
    ///
    /// Used by the executor for `Cases` programs: each case's guard is
    /// matched against the (cell, action) pair, and only the matching
    /// cases' constraints fire. When *no* case matches, the program
    /// default-denies; when multiple cases match, their constraints AND
    /// together.
    ///
    /// `Predicate(_)` and `None` programs are unaffected by `meta`
    /// (they ignore the action-level signals).
    pub fn evaluate_with_meta(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
    ) -> Result<(), ProgramError> {
        self.evaluate_full(new_state, old_state, ctx, meta, &WitnessBundle::empty())
    }

    /// Full-fat evaluation: per-transition context + witness bundle.
    ///
    /// Used by the executor (Cav-Codex Block 2) to dispatch witnessed
    /// predicates through a registered verifier, populate
    /// `SenderAuthorized` Merkle-membership witnesses, resolve
    /// `PreimageGate` reveals, and surface `Custom` predicate proofs.
    ///
    /// Callers without a witness bundle should use
    /// [`Self::evaluate_with_meta`] (which forwards an empty bundle);
    /// callers without action-level meta and without witnesses can use
    /// [`Self::evaluate`].
    pub fn evaluate_full(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
        witnesses: &WitnessBundle<'_>,
    ) -> Result<(), ProgramError> {
        match self {
            CellProgram::None => Ok(()),
            CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    evaluate_constraint_full(constraint, new_state, old_state, ctx, witnesses)?;
                }
                Ok(())
            }
            CellProgram::Cases(cases) => {
                // Track matches separately for invariant cases (Always /
                // SlotChanged) and operation-binding cases (MethodIs /
                // EffectKindIs / boolean composition over those).
                //
                // Cav-Codex Block 4 default-deny: if the program defines
                // at least one operation-binding case, an action whose
                // dispatch matches NONE of them is rejected as
                // `NoTransitionCaseMatched`, even when invariant cases
                // still match. Without this carve-out, an `Always`
                // invariants case silently absorbs unknown methods —
                // the executor would only ever enforce the universal
                // invariants on a `cipherclerk_drain_funds` symbol and
                // the program's whole purpose (operation discrimination)
                // would erode. See the
                // `unknown_method_default_denied` tests in
                // `starbridge-subscription`,
                // `starbridge-governed-namespace`, and
                // `pyana-storage-templates::cap_inbox_tests`.
                let mut any_matched = false;
                let mut any_dispatch_case = false;
                let mut any_dispatch_matched = false;
                for case in cases {
                    let is_dispatch = case.guard.is_method_dispatching();
                    if is_dispatch {
                        any_dispatch_case = true;
                    }
                    if case.guard.matches(meta, old_state, new_state) {
                        any_matched = true;
                        if is_dispatch {
                            any_dispatch_matched = true;
                        }
                        for constraint in &case.constraints {
                            evaluate_constraint_full(
                                constraint, new_state, old_state, ctx, witnesses,
                            )?;
                        }
                    }
                }
                if !any_matched {
                    // No case at all applied — pure default-deny.
                    return Err(ProgramError::NoTransitionCaseMatched);
                }
                if any_dispatch_case && !any_dispatch_matched {
                    // Program defines operation-binding cases but the
                    // action's dispatch matched none of them.
                    return Err(ProgramError::NoTransitionCaseMatched);
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

    /// Sugar: lift a list of constraints into a single `Always`-guarded
    /// case. Equivalent to `CellProgram::Predicate(constraints)` but
    /// uses the new `Cases` shape (so callers can mix in extra cases
    /// later without restructuring).
    pub fn always(constraints: Vec<StateConstraint>) -> Self {
        CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints,
        }])
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

/// Evaluate a single constraint with no witness bundle (legacy entry).
/// Forwards to [`evaluate_constraint_full`] with an empty bundle so
/// witness-dependent variants surface the same `WitnessedPredicateRequiresExecutor` /
/// `WitnessedPredicateWitnessMissing` sentinel as before.
///
/// Retained for backwards-compatibility with callers that hold a
/// constraint without a witness bundle; the `AnyOf` evaluator now goes
/// through [`evaluate_simple_constraint`] so the Heyting-fragment `Not`
/// short-circuit can fire.
#[allow(dead_code)]
fn evaluate_constraint(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
) -> Result<(), ProgramError> {
    evaluate_constraint_full(
        constraint,
        new_state,
        old_state,
        ctx,
        &WitnessBundle::empty(),
    )
}

/// Evaluate a single constraint against the cell state with a witness
/// bundle in scope (Cav-Codex Block 2). When the bundle carries a
/// matching witness for `SenderAuthorized`, `PreimageGate`,
/// `RateLimit`, `Witnessed`, `TemporalPredicate`, or `Custom`, the
/// evaluator dispatches to the registered verifier or uses the
/// witness payload directly. Otherwise it falls through to the
/// legacy fail-closed sentinel.
fn evaluate_constraint_full(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    witnesses: &WitnessBundle<'_>,
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
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            // Cav-Codex Block 2: enforce membership by dispatching to the
            // witnessed-predicate registry against the appropriate
            // commitment (slot root or blinded commitment). The action
            // MUST carry a `MerklePath` (PublicRoot) or `ProofBytes`
            // (BlindedSet) witness blob at the witness index encoded by
            // the cell program. For migration, we accept the *first*
            // `MerklePath`/`ProofBytes` witness blob the action carries
            // — the cell program does not yet bind a specific witness
            // index for `SenderAuthorized`.
            let (commitment, kind) = match set {
                AuthorizedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    (
                        new_state.fields[idx],
                        crate::predicate::WitnessedPredicateKind::MerkleMembership,
                    )
                }
                AuthorizedSet::BlindedSet { commitment } => (
                    *commitment,
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
                AuthorizedSet::CredentialSet {
                    issuer_cell,
                    credential_schema_id,
                } => (
                    AuthorizedSet::credential_set_commitment(issuer_cell, credential_schema_id),
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
            };
            // Require a witness blob and a registry. If neither is
            // present the constraint surfaces a structural sentinel so
            // tests / fail-closed callers can still match on the
            // `MissingContextField` shape, but real executor calls
            // MUST configure both.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // Find a witness blob with kind MerklePath / ProofBytes.
            let blob = witnesses
                .blobs
                .iter()
                .find(|b| {
                    matches!(
                        b.kind,
                        WitnessKindTag::MerklePath | WitnessKindTag::ProofBytes
                    )
                })
                .ok_or(ProgramError::SenderMembershipWitnessMissing)?;
            // Build a placeholder WitnessedPredicate to feed the registry.
            let wp = crate::predicate::WitnessedPredicate {
                kind,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: 0,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: match kind {
                        crate::predicate::WitnessedPredicateKind::MerkleMembership => {
                            "MerkleMembership"
                        }
                        crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                        _ => "Witnessed",
                    },
                    reason: e.to_string(),
                }
            })?;
            Ok(())
        }

        StateConstraint::Renounced { set } => {
            // Dual of SenderAuthorized: verify the sender is *not* in
            // the named sorted-leaf set by dispatching the
            // NonMembership verifier.
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let commitment = match set {
                RenouncedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    new_state.fields[idx]
                }
                RenouncedSet::BlindedSet { commitment } => *commitment,
            };
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // The non-membership neighbor witness is a ProofBytes blob
            // (96 bytes — see `NonMembershipNeighborProof`).
            let blob = witnesses
                .blobs
                .iter()
                .find(|b| b.kind == WitnessKindTag::ProofBytes)
                .ok_or(ProgramError::SenderMembershipWitnessMissing)?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::NonMembership,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: 0,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    reason: e.to_string(),
                }
            })?;
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
            // Prefer an executor-supplied count in `ctx.sender_epoch_count`
            // (Cav-Codex Block 2: the executor populates the per-cell-per-
            // sender counter slot). If unset (zero) AND the action carries
            // a `RateLimitCount` witness blob, use that as a fallback (a
            // self-attested counter that the action's signer commits to).
            let count = if ctx.sender_epoch_count > 0 {
                ctx.sender_epoch_count
            } else {
                witnesses
                    .blobs
                    .iter()
                    .find_map(|b| {
                        if b.kind == WitnessKindTag::RateLimitCount && b.bytes.len() == 4 {
                            let mut buf = [0u8; 4];
                            buf.copy_from_slice(b.bytes);
                            Some(u32::from_le_bytes(buf))
                        } else {
                            None
                        }
                    })
                    .unwrap_or(0)
            };
            if count >= *max_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "sender has {} mutations this epoch, max is {}",
                        count, max_per_epoch
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
            // Cav-Codex Block 2: prefer the witness blob over the
            // ctx-side preimage (the witness blob is the canonical
            // carrier). Fall back to `ctx.revealed_preimage` for
            // backwards compatibility with callers that haven't moved
            // to witness_blobs yet.
            let preimage = witnesses
                .blobs
                .iter()
                .find_map(|b| {
                    if b.kind == WitnessKindTag::Preimage32 && b.bytes.len() == 32 {
                        let mut buf = [0u8; 32];
                        buf.copy_from_slice(b.bytes);
                        Some(buf)
                    } else {
                        None
                    }
                })
                .or_else(|| ctx.and_then(|c| c.revealed_preimage))
                .ok_or(ProgramError::PreimageWitnessMissing)?;
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

        StateConstraint::TemporalPredicate {
            dsl_hash,
            witness_index,
        } => {
            // Cav-Codex Block 2: dispatch through the witnessed-predicate
            // registry using the `Temporal` kind. The witness_index
            // names which witness blob is the input; the proof bytes
            // live in the first `ProofBytes` witness blob the action
            // carries (alongside the input).
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::TemporalPredicateWitnessMissing {
                    dsl_hash: *dsl_hash,
                });
            };
            let input_blob = witnesses.blob(*witness_index as usize).ok_or(
                ProgramError::TemporalPredicateWitnessMissing {
                    dsl_hash: *dsl_hash,
                },
            )?;
            // The proof bytes ride on the next ProofBytes witness blob
            // after the input. (Apps that need a specific binding can
            // migrate to the typed `Witnessed { wp }` variant which
            // names the index explicitly.)
            let proof_blob = witnesses
                .blobs
                .iter()
                .find(|b| b.kind == WitnessKindTag::ProofBytes)
                .ok_or(ProgramError::TemporalPredicateWitnessMissing {
                    dsl_hash: *dsl_hash,
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Temporal,
                commitment: *dsl_hash,
                input_ref: InputRef::Witness {
                    index: *witness_index as usize,
                },
                proof_witness_index: 0,
            };
            let input = PredicateInput::Bytes(input_blob.bytes);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    reason: e.to_string(),
                }
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
                match evaluate_simple_constraint(v, new_state, old_state, ctx, witnesses) {
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
            let kind_name: &'static str = match wp.kind {
                crate::predicate::WitnessedPredicateKind::Dfa => "Dfa",
                crate::predicate::WitnessedPredicateKind::Temporal => "Temporal",
                crate::predicate::WitnessedPredicateKind::MerkleMembership => "MerkleMembership",
                crate::predicate::WitnessedPredicateKind::NonMembership => "NonMembership",
                crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                crate::predicate::WitnessedPredicateKind::BridgePredicate => "BridgePredicate",
                crate::predicate::WitnessedPredicateKind::PedersenEquality => "PedersenEquality",
                crate::predicate::WitnessedPredicateKind::Custom { .. } => "Custom",
            };
            // Cav-Codex Block 2: dispatch through the registry when one
            // is supplied. Resolve the InputRef to a PredicateInput and
            // read the proof bytes from `witnesses.blobs[wp.proof_witness_index]`.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::WitnessedPredicateRequiresExecutor { kind_name });
            };
            let proof_blob = witnesses.blob(wp.proof_witness_index).ok_or(
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: format!(
                        "witness_blobs has no entry at proof_witness_index {}",
                        wp.proof_witness_index
                    ),
                },
            )?;
            // Resolve input ref. For Slot we hand a 32-byte slot value;
            // for Witness we hand the bytes; for Sender we hand the
            // sender pk; for PublicInput we cannot synthesize without
            // the proof's PI vec (caller must use a more specialized
            // path); for SigningMessage we fall through to Bytes.
            //
            // For Sender we need to extend the lifetime of the sender
            // pk reference; we resolve the sender outside the match
            // so the &[u8; 32] borrow is valid for the call.
            let sender_ref: Option<&[u8; 32]> = match &wp.input_ref {
                InputRef::Sender => Some(
                    ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?
                        .sender
                        .as_ref()
                        .ok_or(ProgramError::MissingContextField { field: "sender" })?,
                ),
                _ => None,
            };
            let input: PredicateInput<'_> = match &wp.input_ref {
                InputRef::Slot { index } => {
                    let idx = check_index(*index)?;
                    PredicateInput::Slot(&new_state.fields[idx])
                }
                InputRef::Witness { index } => {
                    let b =
                        witnesses
                            .blob(*index)
                            .ok_or(ProgramError::WitnessedPredicateRejected {
                                kind_name,
                                reason: format!(
                                    "witness_blobs has no entry at input_ref index {index}"
                                ),
                            })?;
                    PredicateInput::Bytes(b.bytes)
                }
                InputRef::PublicInput { .. } => {
                    return Err(ProgramError::WitnessedPredicateRejected {
                        kind_name,
                        reason: "InputRef::PublicInput unsupported in cell-program evaluator"
                            .into(),
                    });
                }
                InputRef::Sender => PredicateInput::Sender(sender_ref.unwrap()),
                InputRef::SigningMessage => {
                    // Caller passes the signing message as a Cleartext
                    // blob; pick the first one.
                    let b = witnesses
                        .blobs
                        .iter()
                        .find(|b| b.kind == WitnessKindTag::Cleartext)
                        .ok_or(ProgramError::WitnessedPredicateRejected {
                            kind_name,
                            reason: "InputRef::SigningMessage needs a Cleartext witness blob"
                                .into(),
                        })?;
                    PredicateInput::Bytes(b.bytes)
                }
            };
            registry.verify(wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: e.to_string(),
                }
            })
        }

        StateConstraint::Custom { ir_hash, .. } => {
            // Cav-Codex Block 2: require an attached `custom_program_proof`
            // (a ProofBytes witness blob whose verifier is registered
            // against the declared `ir_hash` as a `Custom { vk_hash }`
            // kind). When no registry is supplied or no matching
            // verifier is registered, fall through to the legacy
            // fail-closed sentinel.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::CustomConstraintUnevaluable { ir_hash: *ir_hash });
            };
            let proof_blob = witnesses
                .blobs
                .iter()
                .find(|b| b.kind == WitnessKindTag::ProofBytes)
                .ok_or(ProgramError::CustomProgramProofRejected {
                    ir_hash: *ir_hash,
                    reason: "no ProofBytes witness blob carried for Custom predicate".into(),
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Custom { vk_hash: *ir_hash },
                commitment: *ir_hash,
                input_ref: InputRef::Slot { index: 0 },
                proof_witness_index: 0,
            };
            // Input: hand the entire new_state as Slot(0) reference;
            // custom verifiers are expected to fold whatever they need
            // out of the PI / proof itself.
            let input = PredicateInput::Slot(&new_state.fields[0]);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::CustomProgramProofRejected {
                    ir_hash: *ir_hash,
                    reason: match e {
                        WitnessedPredicateError::KindNotRegistered { .. } => {
                            format!("no verifier registered for ir_hash {:02x?}", ir_hash)
                        }
                        other => other.to_string(),
                    },
                }
            })
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

/// Lift a non-`Not` `SimpleStateConstraint` into the full
/// `StateConstraint` enum so the same evaluator can handle the lattice
/// of static / transition / contextual variants.
///
/// `Not` is *not* lifted: it has no corresponding `StateConstraint`
/// variant and is dispatched directly by
/// [`evaluate_simple_constraint`], which short-circuits on the inner
/// constraint's acceptance bit. Calling `lift_simple` on a `Not` is a
/// programming error and panics — callers must go through
/// [`evaluate_simple_constraint`] instead.
fn lift_simple(s: &SimpleStateConstraint) -> StateConstraint {
    match s {
        SimpleStateConstraint::FieldEquals { index, value } => StateConstraint::FieldEquals {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldGte { index, value } => StateConstraint::FieldGte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldLte { index, value } => StateConstraint::FieldLte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::WriteOnce { index } => StateConstraint::WriteOnce { index: *index },
        SimpleStateConstraint::Immutable { index } => StateConstraint::Immutable { index: *index },
        SimpleStateConstraint::Monotonic { index } => StateConstraint::Monotonic { index: *index },
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraint::StrictMonotonic { index: *index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraint::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraint::FieldGteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraint::FieldLteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraint::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        SimpleStateConstraint::Not(_) => {
            // The Heyting-fragment Not has no equivalent
            // StateConstraint variant — it is dispatched inline by
            // evaluate_simple_constraint. lift_simple must not be
            // called on a Not.
            panic!(
                "lift_simple invoked on SimpleStateConstraint::Not; \
                 route through evaluate_simple_constraint instead"
            );
        }
    }
}

/// Evaluate a `SimpleStateConstraint` directly — handles the Heyting
/// `Not` short-circuit inline, falls back to `lift_simple` +
/// `evaluate_constraint_full` for the lattice variants.
///
/// **Acceptance semantics for `Not`:**
/// - Inner `Ok(())` (inner accepts) → `Not` rejects (returns
///   `ConstraintViolated`).
/// - Inner `Err(ProgramError::ConstraintViolated { .. })` (inner
///   rejects on its own terms) → `Not` accepts (`Ok(())`).
/// - Inner returns any other error (`MissingContextField`,
///   `InvalidFieldIndex`, `TransitionCheckRequiresOldState`,
///   `WitnessedPredicateRequiresExecutor`, etc.) → `Not` propagates
///   the same error. This preserves the fail-closed contract: an
///   unevaluable predicate is unevaluable under negation, not
///   vacuously satisfied.
fn evaluate_simple_constraint(
    s: &SimpleStateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    witnesses: &WitnessBundle<'_>,
) -> Result<(), ProgramError> {
    match s {
        SimpleStateConstraint::Not(inner) => {
            let lifted_inner = lift_simple(inner);
            match evaluate_constraint_full(&lifted_inner, new_state, old_state, ctx, witnesses) {
                // Inner accepted ⇒ Not rejects.
                Ok(()) => Err(ProgramError::ConstraintViolated {
                    constraint: lifted_inner.clone(),
                    description: format!(
                        "Not({:?}): inner constraint accepted; negation rejects",
                        inner
                    ),
                }),
                // Inner rejected on its own terms ⇒ Not accepts.
                Err(ProgramError::ConstraintViolated { .. }) => Ok(()),
                // Inner unevaluable (missing ctx, bad index,
                // transition-needs-old-state, witness/registry
                // missing, …) ⇒ propagate, do NOT accept. Fail-closed.
                Err(other) => Err(other),
            }
        }
        other => {
            let lifted = lift_simple(other);
            evaluate_constraint_full(&lifted, new_state, old_state, ctx, witnesses)
        }
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
        // ctx with sender but no registry → SenderMembershipWitnessMissing
        // (the registry + witness blob are also required for full verification)
        let err = p
            .evaluate(&s, None, Some(&ctx_sender([1u8; 32], 0)))
            .unwrap_err();
        assert!(matches!(err, ProgramError::SenderMembershipWitnessMissing));
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

    // ── Heyting fragment — Not / Implies ─────────────────────────────────
    // CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.1 + §9.1.1.

    #[test]
    fn not_field_equals_accepts_when_field_differs() {
        // Not(FieldEquals(0, 7)) accepts when field[0] != 7.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(7),
                },
            ))],
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&s, None, None).is_ok());
        // and rejects when it matches.
        s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn not_write_once_permits_overwriting() {
        // The app-driver case: Not(WriteOnce(0)) flips WriteOnce's
        // semantics — overwriting is now permitted; *not* writing
        // (or writing for the first time) is rejected.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::WriteOnce { index: 0 },
            ))],
        }]);
        // Old slot non-zero, new differs ⇒ WriteOnce rejects ⇒ Not accepts.
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(42);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Old slot zero, new non-zero ⇒ WriteOnce accepts ⇒ Not rejects.
        let old_zero = CellState::new(0);
        let mut fresh = old_zero.clone();
        fresh.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&fresh, Some(&old_zero), None).is_err());
    }

    #[test]
    fn not_monotonic_permits_decrement() {
        // The app-driver case: Not(Monotonic(0)) accepts decrements;
        // rejects monotone non-decreases.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::Monotonic { index: 0 },
            ))],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        // Decrement — Monotonic rejects, Not accepts.
        new_s.fields[0] = field_from_u64(40);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Increase — Monotonic accepts, Not rejects.
        new_s.fields[0] = field_from_u64(60);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
        // Equal — Monotonic accepts (>=), Not rejects.
        new_s.fields[0] = field_from_u64(50);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn not_propagates_unevaluable_error() {
        // Not(Immutable(0)) with no old_state and nonce > 0:
        // inner Immutable surfaces TransitionCheckRequiresOldState; Not
        // propagates the same — fail-closed on unevaluable inputs.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::Immutable { index: 0 },
            ))],
        }]);
        let mut s = CellState::new(0);
        s.set_nonce(5);
        let err = p.evaluate(&s, None, None).unwrap_err();
        // The error surfaces *through* the AnyOf as the last-branch
        // error — and must NOT be a vacuous Ok. We assert non-Ok and
        // that the surfaced error is the transition-check shape.
        assert!(matches!(
            err,
            ProgramError::TransitionCheckRequiresOldState { .. }
                | ProgramError::ConstraintViolated { .. }
        ));
    }

    #[test]
    fn implies_accepts_when_antecedent_false() {
        // Implies(FieldEquals(0, 7), FieldEquals(1, 9)) — antecedent
        // false means the implication is vacuously satisfied; the
        // consequent need not hold.
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // field[0] != 7 ⇒ antecedent false ⇒ Implies accepts regardless of slot 1.
        s.fields[0] = field_from_u64(123);
        s.fields[1] = field_from_u64(0);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn implies_accepts_when_consequent_true() {
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // antecedent true AND consequent true — Implies accepts.
        s.fields[0] = field_from_u64(7);
        s.fields[1] = field_from_u64(9);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn implies_rejects_when_antecedent_true_consequent_false() {
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // antecedent true, consequent false ⇒ Implies rejects.
        s.fields[0] = field_from_u64(7);
        s.fields[1] = field_from_u64(0);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn implies_via_builder_method_equals_static_constructor() {
        let antec = SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        };
        let conseq = SimpleStateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(2),
        };
        let via_method = antec.clone().implies(conseq.clone());
        let via_static = StateConstraint::implies(antec, conseq);
        assert_eq!(via_method, via_static);
    }

    #[test]
    fn not_round_trips_serde() {
        let s = SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
            index: 3,
            value: field_from_u64(42),
        }));
        let bytes = postcard::to_allocvec(&s).expect("serialize");
        let back: SimpleStateConstraint = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(back, s);
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

    // ── Renunciation — Tier 2 §3.2 / §9.2.1 ──────────────────────────────

    #[test]
    fn renounced_accepts_legal_non_membership() {
        // Sender 0x05 is between lower=0x04 and upper=0x06 → not in
        // the set → renunciation accepts.
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof::new(
            &[0xAB; 32],
            [0x04u8; 32],
            [0x06u8; 32],
        );
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .expect("legal renunciation accepts");
    }

    #[test]
    fn renounced_rejects_when_prover_is_in_set() {
        // Adversarial: candidate == lower neighbor → the prover IS in
        // the set but is forging a renunciation. Must reject.
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof::new(
            &[0xAB; 32],
            [0x05u8; 32], // candidate matches lower → in set
            [0x06u8; 32],
        );
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        let err = p
            .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ));
    }

    #[test]
    fn renounced_rejects_forged_adjacency_tag() {
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof {
            lower: [0x04u8; 32],
            upper: [0x06u8; 32],
            adjacency_tag: [0u8; 32], // forged (zero != commitment-keyed tag)
        };
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        let err = p
            .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ));
    }

    #[test]
    fn renounced_requires_sender_in_ctx() {
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let bundle = WitnessBundle {
            blobs: &[],
            registry: Some(&registry),
        };
        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        // No ctx at all.
        let err = p
            .evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // Ctx without sender.
        let bare = EvalContext::default();
        let err = p
            .evaluate_full(&s, None, Some(&bare), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
    }

    #[test]
    fn renounced_public_root_reads_slot_commitment() {
        // PublicRoot variant pulls commitment from a state slot.
        let candidate = [0x05u8; 32];
        // Slot 3 carries the set root [0xCC; 32] (see below).
        let proof = crate::predicate::NonMembershipNeighborProof::new(
            &[0xCC; 32],
            [0x04u8; 32],
            [0x06u8; 32],
        );
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::PublicRoot { set_root_index: 3 },
        }]);
        let mut s = CellState::new(0);
        s.fields[3] = [0xCC; 32]; // set root from slot
        let ctx = ctx_sender(candidate, 0);
        p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .expect("legal renunciation via PublicRoot accepts");
    }
}
