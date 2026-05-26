//! TurnBuilder and ActionBuilder: ergonomic APIs for constructing turns.
//!
//! These builders provide a fluent interface for constructing turns and actions
//! without manually assembling all the nested structures.
//!
//! # Typestate-enforced authorization (P2.A)
//!
//! The redesigned `ActionBuilder<S>` carries a phantom state marker `S` that
//! tracks whether the builder has been authorized. Initial state `NeedsAuth`
//! has *no* `.build()` method; calling one of the four authorization
//! transitions below moves the builder into an `Authorized<Mode>` state where
//! `.build()` becomes available. `Authorization::Unchecked` is unrepresentable
//! through the builder; the only path to it is the loudly-named, test-only
//! [`ActionBuilder::new_unchecked_for_tests`] constructor.
//!
//! # The four authorization modes (P2.E)
//!
//! Every authorized [`ActionBuilder`] is in exactly one of four states, each
//! corresponding to a distinct production-grade authorization mode. They have
//! identical surface for adding effects / preconditions / args; they differ
//! only in *how the executor decides to honor the action*.
//!
//! | Mode          | Marker type        | Transition method                  | Authorization stored                             |
//! |---------------|--------------------|------------------------------------|--------------------------------------------------|
//! | Signed        | [`Signed`]         | [`ActionBuilder::signed_by`]       | [`Authorization::Signature`] (Ed25519 r, s)      |
//! | Proved        | [`Proved`]         | [`ActionBuilder::with_proof`]      | [`Authorization::Proof`] (STARK bytes + binding) |
//! | Breadstuff    | [`Breadstuff`]     | [`ActionBuilder::with_breadstuff`] | [`Authorization::Breadstuff`] (capability token) |
//! | Bearer        | [`Bearer`]         | [`ActionBuilder::bearer_via`]      | [`Authorization::Bearer`] (cap-delegation proof) |
//!
//! ## Signed (Ed25519)
//!
//! The most common mode: an Ed25519 signature over the action's canonical
//! bytes by the caller's primary key. Use when the caller is a cclerk-backed
//! identity that holds a long-lived key.
//!
//! ```
//! use pyana_turn::builder::ActionBuilder;
//! use pyana_cell::CellId;
//!
//! let caller = CellId::from_bytes([1u8; 32]);
//! let target = CellId::from_bytes([2u8; 32]);
//!
//! // 64-byte placeholder signature -- real callers feed a cclerk output.
//! let sig = [0u8; 64];
//!
//! let action = ActionBuilder::new(target, "transfer", caller)
//!     .signed_by(sig)
//!     .effect_transfer(caller, target, 100)
//!     .build();
//! assert_eq!(action.effects.len(), 1);
//! ```
//!
//! ## Proved (STARK / ZK)
//!
//! Carries an opaque proof and a `(bound_action, bound_resource)` pair that
//! the verifier checks the proof binds to. Use when the caller cannot or
//! does not want to reveal a key — e.g. private membership proofs, sovereign
//! cell self-attestations, capability-by-proof.
//!
//! ```
//! use pyana_turn::builder::ActionBuilder;
//! use pyana_cell::CellId;
//!
//! let caller = CellId::from_bytes([3u8; 32]);
//! let target = CellId::from_bytes([4u8; 32]);
//!
//! let proof_bytes = vec![0xAB; 16]; // opaque STARK / ZK bytes
//!
//! let action = ActionBuilder::new(target, "claim", caller)
//!     .with_proof(proof_bytes, "claim", "vault://main")
//!     .effect_emit_event(caller, "claimed", vec![])
//!     .build();
//! assert!(matches!(
//!     action.authorization,
//!     pyana_turn::action::Authorization::Proof { .. }
//! ));
//! ```
//!
//! ## Breadstuff (capability token)
//!
//! A 32-byte capability token (the "breadstuff" — Pyana's hash-anchored
//! bearer credential). The executor looks the token up in the target's
//! capability table and rejects if absent / revoked. Use for delegated
//! authority where the bearer holds nothing but the token bytes.
//!
//! ```
//! use pyana_turn::builder::ActionBuilder;
//! use pyana_cell::CellId;
//!
//! let caller = CellId::from_bytes([5u8; 32]);
//! let target = CellId::from_bytes([6u8; 32]);
//!
//! let token: [u8; 32] = [0xCD; 32]; // breadstuff hash
//!
//! let action = ActionBuilder::new(target, "ping", caller)
//!     .with_breadstuff(token)
//!     .effect_increment_nonce(target)
//!     .build();
//! assert!(matches!(
//!     action.authorization,
//!     pyana_turn::action::Authorization::Breadstuff(_)
//! ));
//! ```
//!
//! ## Bearer (one-shot delegation proof)
//!
//! Carries a [`BearerCapProof`] containing the delegation chain plus an
//! expiry. Unlike breadstuff, the proof itself encodes the delegation and
//! never persists in any c-list — it is ephemeral and verified inline. Use
//! when the delegator cannot pre-grant a capability slot (e.g. immediate
//! cross-federation introduction).
//!
//! ```
//! use pyana_turn::builder::ActionBuilder;
//! use pyana_turn::action::BearerCapProof;
//! use pyana_turn::action::DelegationProofData;
//! use pyana_cell::{CellId, AuthRequired};
//!
//! let caller = CellId::from_bytes([7u8; 32]);
//! let target = CellId::from_bytes([8u8; 32]);
//!
//! let proof = BearerCapProof {
//!     target,
//!     permissions: AuthRequired::Signature,
//!     delegation_proof: DelegationProofData::SignedDelegation {
//!         delegator_pk: [0xAA; 32],
//!         signature: [0u8; 64],
//!         bearer_pk: [0xBB; 32],
//!     },
//!     expires_at: 1_000_000,
//!     revocation_channel: None,
//!     allowed_effects: None,
//! };
//!
//! let action = ActionBuilder::new(target, "exercise", caller)
//!     .bearer_via(proof)
//!     .effect_emit_event(caller, "exercised", vec![])
//!     .build();
//! assert!(matches!(
//!     action.authorization,
//!     pyana_turn::action::Authorization::Bearer(_)
//! ));
//! ```
//!
//! # Escape hatch (tests only)
//!
//! [`ActionBuilder::new_unchecked_for_tests`] is the **sole** path that
//! produces `Authorization::Unchecked`. It is loudly named on purpose: any
//! call site is grep-visible (`new_unchecked_for_tests`) and the resulting
//! builder enters the [`UncheckedOptIn`] typestate — distinct from any of
//! the four production modes above, so reviewers spot it immediately.
//!
//! The CI guard `scripts/no-unchecked-auth.sh` (P2.F) enforces that
//! `Authorization::Unchecked` does **not** appear outside test code,
//! `new_unchecked_for_tests` call sites, and the [`UncheckedOptIn`] marker
//! variant itself. Production code paths in `app-framework/` and the apps
//! must construct one of the four authorized variants above.

use std::marker::PhantomData;

use pyana_cell::state::FieldElement;
use pyana_cell::{CapabilityRef, CellId, Preconditions};

use crate::action::{
    Action, Authorization, BearerCapProof, CommitmentMode, DelegationMode, Effect, Event,
    WitnessBlob, symbol,
};
use crate::forest::CallForest;
use crate::turn::Turn;

// ─── Typestate markers ────────────────────────────────────────────────────────

mod sealed {
    pub trait Sealed {}
}

/// Initial state: authorization has not been provided yet. `.build()` is
/// intentionally absent.
pub struct NeedsAuth;
impl sealed::Sealed for NeedsAuth {}

/// Signed authorization state (Ed25519).
pub struct Signed;
impl sealed::Sealed for Signed {}

/// ZK proof authorization state.
pub struct Proved;
impl sealed::Sealed for Proved {}

/// Breadstuff capability token authorization state.
pub struct Breadstuff;
impl sealed::Sealed for Breadstuff {}

/// Bearer-capability proof authorization state.
pub struct Bearer;
impl sealed::Sealed for Bearer {}

/// Unchecked authorization state. Reachable only through
/// [`ActionBuilder::new_unchecked_for_tests`].
pub struct UncheckedOptIn;
impl sealed::Sealed for UncheckedOptIn {}

/// Marker trait for "this builder has been authorized." Sealed —
/// `NeedsAuth` does *not* implement it, so `.build()` is unreachable
/// before authorization.
pub trait Authorized: sealed::Sealed {}
impl Authorized for Signed {}
impl Authorized for Proved {}
impl Authorized for Breadstuff {}
impl Authorized for Bearer {}
impl Authorized for UncheckedOptIn {}

// ─── TurnBuilder ──────────────────────────────────────────────────────────────

/// Builder for constructing a Turn step by step.
pub struct TurnBuilder {
    agent: CellId,
    nonce: u64,
    fee: u64,
    memo: Option<String>,
    valid_until: Option<i64>,
    previous_receipt_hash: Option<[u8; 32]>,
    /// Fully-built (authorized) root actions, with their child trees attached.
    actions: Vec<ActionWithChildren>,
    /// Per-action declared excess deltas, parallel to `actions` (for
    /// conservation derivation summing).
    declared_excesses: Vec<i64>,
    /// Crate-private legacy builders accumulated via the deprecated `.action()`
    /// method. Drained into `actions` at `.build()` time. No external callers
    /// remain; this field will be removed when `LegacyActionBuilder` is deleted.
    legacy_action_builders: Vec<LegacyActionBuilder>,
}

/// A built `Action` plus its already-built children. Internal to the builder
/// pipeline.
struct ActionWithChildren {
    action: Action,
    children: Vec<ActionWithChildren>,
}

impl ActionWithChildren {
    fn attach_to_forest(self, forest: &mut CallForest) {
        let tree = forest.add_root(self.action);
        for c in self.children {
            c.attach_to_tree(tree);
        }
    }

    fn attach_to_tree(self, tree: &mut crate::forest::CallTree) {
        let child_tree = tree.add_child(self.action);
        for c in self.children {
            c.attach_to_tree(child_tree);
        }
    }
}

impl TurnBuilder {
    /// Create a new TurnBuilder for the given agent and nonce.
    pub fn new(agent: CellId, nonce: u64) -> Self {
        TurnBuilder {
            agent,
            nonce,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            actions: Vec::new(),
            declared_excesses: Vec::new(),
            legacy_action_builders: Vec::new(),
        }
    }

    /// Set the `previous_receipt_hash` (P0-3): the agent's prior receipt hash.
    pub fn previous_receipt_hash(mut self, hash: [u8; 32]) -> Self {
        self.previous_receipt_hash = Some(hash);
        self
    }

    /// Set the `previous_receipt_hash` (chainable from `&mut self`).
    pub fn set_previous_receipt_hash(&mut self, hash: [u8; 32]) -> &mut Self {
        self.previous_receipt_hash = Some(hash);
        self
    }

    /// Add a fully-built (authorized) root-level action to this turn.
    ///
    /// This is the canonical entry point after the typestate migration: build
    /// an `ActionBuilder` to an `Authorized` state, call `.build()`, and pass
    /// the resulting `Action` here.
    pub fn add_action(&mut self, action: Action) -> &mut Self {
        let declared = action.balance_change.unwrap_or(0);
        self.actions.push(ActionWithChildren {
            action,
            children: Vec::new(),
        });
        self.declared_excesses.push(declared);
        self
    }

    /// Add a root-level action plus its (already-built) child actions.
    pub fn add_action_with_children(&mut self, action: Action, children: Vec<Action>) -> &mut Self {
        let declared = action.balance_change.unwrap_or(0);
        let children = children
            .into_iter()
            .map(|c| ActionWithChildren {
                action: c,
                children: Vec::new(),
            })
            .collect();
        self.actions.push(ActionWithChildren { action, children });
        self.declared_excesses.push(declared);
        self
    }

    /// Legacy entry point — all external callers have been migrated to
    /// [`TurnBuilder::add_action`]. This method and [`LegacyActionBuilder`]
    /// are now crate-private. Use `add_action` with a typestate
    /// [`ActionBuilder`] instead.
    #[deprecated(
        since = "0.0.0",
        note = "All callers migrated. Use add_action with ActionBuilder instead."
    )]
    pub(crate) fn action(&mut self, target: CellId, method: &str) -> &mut LegacyActionBuilder {
        self.legacy_action_builders
            .push(LegacyActionBuilder::new(target, method));
        self.legacy_action_builders.last_mut().unwrap()
    }

    /// Set the computron fee for this turn.
    pub fn fee(mut self, fee: u64) -> Self {
        self.fee = fee;
        self
    }

    /// Set the fee (chainable from &mut self).
    pub fn set_fee(&mut self, fee: u64) -> &mut Self {
        self.fee = fee;
        self
    }

    /// Set an optional memo.
    pub fn memo(mut self, memo: impl Into<String>) -> Self {
        self.memo = Some(memo.into());
        self
    }

    /// Set the memo (chainable from &mut self).
    pub fn set_memo(&mut self, memo: impl Into<String>) -> &mut Self {
        self.memo = Some(memo.into());
        self
    }

    /// Set the expiration timestamp.
    pub fn valid_until(mut self, ts: i64) -> Self {
        self.valid_until = Some(ts);
        self
    }

    /// Set the expiration timestamp (chainable from &mut self).
    pub fn set_valid_until(&mut self, ts: i64) -> &mut Self {
        self.valid_until = Some(ts);
        self
    }

    /// Build the Turn from the accumulated configuration.
    pub fn build(mut self) -> Turn {
        // Drain legacy builders into the canonical action list. Each legacy
        // action enters in its `UncheckedOptIn` state.
        for lab in std::mem::take(&mut self.legacy_action_builders) {
            let (action, children) = lab.into_action_and_children();
            let declared = action.balance_change.unwrap_or(0);
            let children = children
                .into_iter()
                .map(|c| ActionWithChildren {
                    action: c,
                    children: Vec::new(),
                })
                .collect();
            self.actions.push(ActionWithChildren { action, children });
            self.declared_excesses.push(declared);
        }

        let mut forest = CallForest::new();
        for awc in self.actions {
            awc.attach_to_forest(&mut forest);
        }

        Turn {
            agent: self.agent,
            nonce: self.nonce,
            call_forest: forest,
            fee: self.fee,
            memo: self.memo,
            valid_until: self.valid_until,
            previous_receipt_hash: self.previous_receipt_hash,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Validate that the excess of all balance_change deltas sums to zero.
    pub fn validate_excess(&self) -> Result<(), crate::error::TurnError> {
        let excess = self.compute_excess();
        if excess != 0 {
            Err(crate::error::TurnError::ExcessNotZero { excess })
        } else {
            Ok(())
        }
    }

    fn compute_excess(&self) -> i64 {
        // excess = -sum(balance_change_declared)
        let mut total: i64 = 0;
        for d in &self.declared_excesses {
            total = total.checked_sub(*d).unwrap_or(i64::MAX);
        }
        for lab in &self.legacy_action_builders {
            total = total.saturating_add(lab.compute_excess_recursive());
        }
        total
    }

}

// ─── ActionBuilder<S> — typestate-bearing builder ─────────────────────────────

/// Typestate-enforced builder for an `Action`.
///
/// The state parameter `S` tracks whether authorization has been supplied.
/// `ActionBuilder<NeedsAuth>` does **not** expose `.build()`; only a builder
/// in an `Authorized` state does.
pub struct ActionBuilder<S = NeedsAuth> {
    target: CellId,
    method: String,
    caller: CellId,
    args: Vec<FieldElement>,
    authorization: Option<Authorization>,
    preconditions: Preconditions,
    effects: Vec<Effect>,
    may_delegate: DelegationMode,
    commitment_mode: CommitmentMode,
    /// Optional declared balance excess. If unset, conservation will be
    /// derived from emitted effects at build time.
    declared_excess: Option<i64>,
    children: Vec<Action>,
    _state: PhantomData<S>,
}

impl ActionBuilder<NeedsAuth> {
    /// Create a new ActionBuilder targeting `target` on `caller`'s behalf,
    /// invoking `method`. The builder starts in the `NeedsAuth` state and
    /// has no `.build()` method until an authorization transition is
    /// performed.
    pub fn new(target: CellId, method: &str, caller: CellId) -> Self {
        ActionBuilder {
            target,
            method: method.to_string(),
            caller,
            args: Vec::new(),
            authorization: None,
            preconditions: Preconditions::default(),
            effects: Vec::new(),
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            declared_excess: None,
            children: Vec::new(),
            _state: PhantomData,
        }
    }

    /// Transition to the `Signed` authorization state with an Ed25519
    /// signature. Consumes self and returns an authorized builder.
    pub fn signed_by(self, sig: [u8; 64]) -> ActionBuilder<Signed> {
        let mut next = self.transition::<Signed>();
        next.authorization = Some(Authorization::from_sig_bytes(sig));
        next
    }

    /// Transition to the `Proved` state with a ZK proof and binding.
    pub fn with_proof(
        self,
        proof_bytes: Vec<u8>,
        bound_action: impl Into<String>,
        bound_resource: impl Into<String>,
    ) -> ActionBuilder<Proved> {
        let mut next = self.transition::<Proved>();
        next.authorization = Some(Authorization::Proof {
            proof_bytes,
            bound_action: bound_action.into(),
            bound_resource: bound_resource.into(),
        });
        next
    }

    /// Transition to the `Breadstuff` state with a capability token hash.
    pub fn with_breadstuff(self, token: [u8; 32]) -> ActionBuilder<Breadstuff> {
        let mut next = self.transition::<Breadstuff>();
        next.authorization = Some(Authorization::Breadstuff(token));
        next
    }

    /// Transition to the `Bearer` state with a bearer-cap proof.
    pub fn bearer_via(self, proof: BearerCapProof) -> ActionBuilder<Bearer> {
        let mut next = self.transition::<Bearer>();
        next.authorization = Some(Authorization::Bearer(proof));
        next
    }

    /// Loudly-named escape hatch that emits `Authorization::Unchecked`.
    /// Available exclusively for test scaffolding. Production code paths in
    /// `app-framework/src/` are forbidden by CI grep-guard from using this
    /// constructor.
    pub fn new_unchecked_for_tests(
        target: CellId,
        method: &str,
        caller: CellId,
    ) -> ActionBuilder<UncheckedOptIn> {
        let mut next = Self::new(target, method, caller).transition::<UncheckedOptIn>();
        next.authorization = Some(Authorization::Unchecked);
        next
    }

    /// Internal: cast the phantom type marker. The data is preserved.
    fn transition<T>(self) -> ActionBuilder<T> {
        ActionBuilder {
            target: self.target,
            method: self.method,
            caller: self.caller,
            args: self.args,
            authorization: self.authorization,
            preconditions: self.preconditions,
            effects: self.effects,
            may_delegate: self.may_delegate,
            commitment_mode: self.commitment_mode,
            declared_excess: self.declared_excess,
            children: self.children,
            _state: PhantomData,
        }
    }
}

// Common (state-agnostic) methods.
impl<S> ActionBuilder<S> {
    /// Add an argument to the action.
    pub fn arg(mut self, value: FieldElement) -> Self {
        self.args.push(value);
        self
    }

    /// Add an effect to this action.
    pub fn effect(mut self, effect: Effect) -> Self {
        self.effects.push(effect);
        self
    }

    /// Set the delegation mode for children.
    pub fn delegation(mut self, mode: DelegationMode) -> Self {
        self.may_delegate = mode;
        self
    }

    /// Set the commitment mode for this action.
    pub fn commitment_mode(mut self, mode: CommitmentMode) -> Self {
        self.commitment_mode = mode;
        self
    }

    /// Set a nonce precondition.
    pub fn require_nonce(mut self, nonce: u64) -> Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.nonce = Some(nonce);
        self
    }

    /// Set a minimum balance precondition.
    pub fn require_min_balance(mut self, min: u64) -> Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.min_balance = Some(min);
        self
    }

    /// Set a state field equality precondition.
    pub fn require_field_equals(mut self, index: usize, value: FieldElement) -> Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.field_equals.push((index, value));
        self
    }

    /// Set a proved_state precondition.
    pub fn require_proved_state(mut self, expected: bool) -> Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.proved_state = Some(expected);
        self
    }

    /// Set preconditions directly.
    pub fn preconditions(mut self, pre: Preconditions) -> Self {
        self.preconditions = pre;
        self
    }

    /// Declare an explicit balance excess for this action. When set, the
    /// builder will record this on the resulting `Action`'s `balance_change`
    /// field rather than deriving it from emitted effects.
    ///
    /// Use only for sovereign cells with legitimate unconserved deltas.
    pub fn with_declared_excess(mut self, excess: i64) -> Self {
        self.declared_excess = Some(excess);
        self
    }

    /// Attach a fully-built child action.
    pub fn add_child(mut self, child: Action) -> Self {
        self.children.push(child);
        self
    }

    /// The caller (issuer) of this action. Public read-only accessor for
    /// downstream consumers.
    pub fn caller(&self) -> CellId {
        self.caller
    }

    /// The current target of this action.
    pub fn target(&self) -> CellId {
        self.target
    }
}

// ─── Typed effect_* methods (P2.C) ────────────────────────────────────────────
//
// One method per existing `Effect` variant. The CapTP variants
// (ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff) are owned by P1
// and get their methods in a follow-up. `RegisterName` is not yet an
// Effect variant and lands in a follow-up commit too.
//
// All methods are state-agnostic (available on any `S`) and consume self,
// returning Self with the effect appended.
impl<S> ActionBuilder<S> {
    // §3.1 — Field & balance ---------------------------------------------------

    pub fn effect_set_field(mut self, cell: CellId, index: usize, value: FieldElement) -> Self {
        self.effects.push(Effect::SetField { cell, index, value });
        self
    }

    pub fn effect_transfer(mut self, from: CellId, to: CellId, amount: u64) -> Self {
        self.effects.push(Effect::Transfer { from, to, amount });
        self
    }

    pub fn effect_increment_nonce(mut self, cell: CellId) -> Self {
        self.effects.push(Effect::IncrementNonce { cell });
        self
    }

    // §3.2 — Capabilities ------------------------------------------------------

    pub fn effect_grant_capability(mut self, from: CellId, to: CellId, cap: CapabilityRef) -> Self {
        self.effects.push(Effect::GrantCapability { from, to, cap });
        self
    }

    pub fn effect_revoke_capability(mut self, cell: CellId, slot: u32) -> Self {
        self.effects.push(Effect::RevokeCapability { cell, slot });
        self
    }

    pub fn effect_introduce(
        mut self,
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        permissions: pyana_cell::AuthRequired,
    ) -> Self {
        self.effects.push(Effect::Introduce {
            introducer,
            recipient,
            target,
            permissions,
        });
        self
    }

    pub fn effect_exercise_via_capability(
        mut self,
        cap_slot: u32,
        inner_effects: Vec<Effect>,
    ) -> Self {
        self.effects.push(Effect::ExerciseViaCapability {
            cap_slot,
            inner_effects,
        });
        self
    }

    pub fn effect_pipelined_send(
        mut self,
        target: crate::eventual::EventualRef,
        action: Action,
    ) -> Self {
        self.effects.push(Effect::PipelinedSend {
            target,
            action: Box::new(action),
        });
        self
    }

    // §3.3 — Notes & seal-pairs ------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    pub fn effect_note_spend(
        mut self,
        nullifier: pyana_cell::Nullifier,
        note_tree_root: [u8; 32],
        value: u64,
        asset_type: u64,
        spending_proof: Vec<u8>,
        value_commitment: Option<[u8; 32]>,
    ) -> Self {
        self.effects.push(Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            spending_proof,
            value_commitment,
        });
        self
    }

    #[allow(clippy::too_many_arguments)]
    pub fn effect_note_create(
        mut self,
        commitment: pyana_cell::NoteCommitment,
        value: u64,
        asset_type: u64,
        encrypted_note: Vec<u8>,
        value_commitment: Option<[u8; 32]>,
        range_proof: Option<Vec<u8>>,
    ) -> Self {
        self.effects.push(Effect::NoteCreate {
            commitment,
            value,
            asset_type,
            encrypted_note,
            value_commitment,
            range_proof,
        });
        self
    }

    pub fn effect_create_seal_pair(
        mut self,
        sealer_holder: CellId,
        unsealer_holder: CellId,
    ) -> Self {
        self.effects.push(Effect::CreateSealPair {
            sealer_holder,
            unsealer_holder,
        });
        self
    }

    pub fn effect_seal(mut self, pair_id: [u8; 32], capability: CapabilityRef) -> Self {
        self.effects.push(Effect::Seal {
            pair_id,
            capability,
        });
        self
    }

    pub fn effect_unseal(mut self, sealed_box: pyana_cell::SealedBox, recipient: CellId) -> Self {
        self.effects.push(Effect::Unseal {
            sealed_box,
            recipient,
        });
        self
    }

    // §3.4 — Cell lifecycle ----------------------------------------------------

    pub fn effect_create_cell(
        mut self,
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: u64,
    ) -> Self {
        self.effects.push(Effect::CreateCell {
            public_key,
            token_id,
            balance,
        });
        self
    }

    pub fn effect_create_cell_from_factory(
        mut self,
        factory_vk: [u8; 32],
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        params: pyana_cell::FactoryCreationParams,
    ) -> Self {
        self.effects.push(Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        });
        self
    }

    pub fn effect_make_sovereign(mut self, cell: CellId) -> Self {
        self.effects.push(Effect::MakeSovereign { cell });
        self
    }

    pub fn effect_set_permissions(
        mut self,
        cell: CellId,
        new_permissions: pyana_cell::Permissions,
    ) -> Self {
        self.effects.push(Effect::SetPermissions {
            cell,
            new_permissions,
        });
        self
    }

    pub fn effect_set_verification_key(
        mut self,
        cell: CellId,
        new_vk: Option<pyana_cell::VerificationKey>,
    ) -> Self {
        self.effects
            .push(Effect::SetVerificationKey { cell, new_vk });
        self
    }

    // §3.5 — Delegation --------------------------------------------------------

    pub fn effect_spawn_with_delegation(
        mut self,
        child_public_key: [u8; 32],
        child_token_id: [u8; 32],
        max_staleness: u64,
    ) -> Self {
        self.effects.push(Effect::SpawnWithDelegation {
            child_public_key,
            child_token_id,
            max_staleness,
        });
        self
    }

    pub fn effect_refresh_delegation(mut self) -> Self {
        self.effects.push(Effect::RefreshDelegation);
        self
    }

    pub fn effect_revoke_delegation(mut self, child: CellId) -> Self {
        self.effects.push(Effect::RevokeDelegation { child });
        self
    }

    // §3.6 — Bridge ------------------------------------------------------------

    pub fn effect_bridge_mint(
        mut self,
        portable_proof: pyana_cell::note_bridge::PortableNoteProof,
    ) -> Self {
        self.effects.push(Effect::BridgeMint { portable_proof });
        self
    }

    #[allow(clippy::too_many_arguments)]
    pub fn effect_bridge_lock(
        mut self,
        nullifier: [u8; 32],
        destination: [u8; 32],
        value: u64,
        asset_type: u64,
        timeout_height: u64,
        spending_proof: Vec<u8>,
    ) -> Self {
        self.effects.push(Effect::BridgeLock {
            nullifier,
            destination,
            value,
            asset_type,
            timeout_height,
            spending_proof,
        });
        self
    }

    pub fn effect_bridge_finalize(
        mut self,
        nullifier: [u8; 32],
        receipt: pyana_cell::note_bridge::BridgeReceipt,
    ) -> Self {
        self.effects
            .push(Effect::BridgeFinalize { nullifier, receipt });
        self
    }

    pub fn effect_bridge_cancel(mut self, nullifier: [u8; 32]) -> Self {
        self.effects.push(Effect::BridgeCancel { nullifier });
        self
    }

    // §3.7 — Obligations -------------------------------------------------------

    pub fn effect_create_obligation(
        mut self,
        beneficiary: CellId,
        condition: crate::conditional::ProofCondition,
        deadline_height: u64,
        stake: pyana_cell::NoteCommitment,
        stake_amount: u64,
    ) -> Self {
        self.effects.push(Effect::CreateObligation {
            beneficiary,
            condition,
            deadline_height,
            stake,
            stake_amount,
        });
        self
    }

    pub fn effect_fulfill_obligation(
        mut self,
        obligation_id: [u8; 32],
        proof: crate::conditional::ConditionProof,
    ) -> Self {
        self.effects.push(Effect::FulfillObligation {
            obligation_id,
            proof,
        });
        self
    }

    pub fn effect_slash_obligation(mut self, obligation_id: [u8; 32]) -> Self {
        self.effects.push(Effect::SlashObligation { obligation_id });
        self
    }

    // §3.8 — Escrow ------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    pub fn effect_create_escrow(
        mut self,
        cell: CellId,
        recipient: CellId,
        amount: u64,
        condition: crate::escrow::EscrowCondition,
        timeout_height: u64,
        escrow_id: [u8; 32],
    ) -> Self {
        self.effects.push(Effect::CreateEscrow {
            cell,
            recipient,
            amount,
            condition,
            timeout_height,
            escrow_id,
        });
        self
    }

    pub fn effect_release_escrow(mut self, escrow_id: [u8; 32], proof: Option<Vec<u8>>) -> Self {
        self.effects
            .push(Effect::ReleaseEscrow { escrow_id, proof });
        self
    }

    pub fn effect_refund_escrow(mut self, escrow_id: [u8; 32]) -> Self {
        self.effects.push(Effect::RefundEscrow { escrow_id });
        self
    }

    #[allow(clippy::too_many_arguments)]
    pub fn effect_create_committed_escrow(
        mut self,
        creator_commitment: [u8; 32],
        recipient_commitment: [u8; 32],
        value_commitment: pyana_cell::ValueCommitmentBytes,
        condition_commitment: [u8; 32],
        timeout_height: u64,
        escrow_id: [u8; 32],
        range_proof: Vec<u8>,
        amount: u64,
    ) -> Self {
        self.effects.push(Effect::CreateCommittedEscrow {
            creator_commitment,
            recipient_commitment,
            value_commitment,
            condition_commitment,
            timeout_height,
            escrow_id,
            range_proof,
            amount,
        });
        self
    }

    pub fn effect_release_committed_escrow(
        mut self,
        escrow_id: [u8; 32],
        claim_auth: crate::escrow::EscrowClaimAuth,
        recipient: CellId,
    ) -> Self {
        self.effects.push(Effect::ReleaseCommittedEscrow {
            escrow_id,
            claim_auth,
            recipient,
        });
        self
    }

    pub fn effect_refund_committed_escrow(
        mut self,
        escrow_id: [u8; 32],
        claim_auth: crate::escrow::EscrowClaimAuth,
        creator: CellId,
    ) -> Self {
        self.effects.push(Effect::RefundCommittedEscrow {
            escrow_id,
            claim_auth,
            creator,
        });
        self
    }

    // §3.9 — Events ------------------------------------------------------------

    pub fn effect_emit_event(mut self, cell: CellId, topic: &str, data: Vec<FieldElement>) -> Self {
        self.effects.push(Effect::EmitEvent {
            cell,
            event: Event::new(symbol(topic), data),
        });
        self
    }

    // §3.10 — Queues -----------------------------------------------------------

    pub fn effect_queue_allocate(mut self, capacity: u64, program_vk: Option<[u8; 32]>) -> Self {
        self.effects.push(Effect::QueueAllocate {
            capacity,
            program_vk,
        });
        self
    }

    pub fn effect_queue_enqueue(
        mut self,
        queue: CellId,
        message_hash: [u8; 32],
        deposit: u64,
    ) -> Self {
        self.effects.push(Effect::QueueEnqueue {
            queue,
            message_hash,
            deposit,
        });
        self
    }

    pub fn effect_queue_dequeue(mut self, queue: CellId) -> Self {
        self.effects.push(Effect::QueueDequeue { queue });
        self
    }

    pub fn effect_queue_resize(mut self, queue: CellId, new_capacity: u64) -> Self {
        self.effects.push(Effect::QueueResize {
            queue,
            new_capacity,
        });
        self
    }

    pub fn effect_queue_atomic_tx(mut self, operations: Vec<crate::action::QueueTxOp>) -> Self {
        self.effects.push(Effect::QueueAtomicTx { operations });
        self
    }

    pub fn effect_queue_pipeline_step(
        mut self,
        pipeline_id: [u8; 32],
        source: CellId,
        sinks: Vec<CellId>,
    ) -> Self {
        self.effects.push(Effect::QueuePipelineStep {
            pipeline_id,
            source,
            sinks,
        });
        self
    }
}

// `.build()` is only available in an `Authorized` state.
impl<S: Authorized> ActionBuilder<S> {
    /// Finalize the builder into an `Action`. Only available once
    /// authorization has been provided.
    pub fn build(self) -> Action {
        let authorization = self
            .authorization
            .expect("authorization guaranteed by Authorized typestate");

        // `balance_change` is an opt-in sovereign-cell excess declaration. The
        // executor applies it directly to `action.target`'s balance (P0-7
        // Mina-style excess tracking), which is meaningful only when the
        // caller has explicit cross-cell-conservation accounting to do — not
        // for ordinary `Transfer` effects (those move balance themselves; an
        // auto-derived `balance_change` would double-debit). Callers that need
        // the excess slot opt in via `with_declared_excess(delta)`.
        let balance_change = self.declared_excess;

        Action {
            target: self.target,
            method: symbol(&self.method),
            args: self.args,
            authorization,
            preconditions: self.preconditions,
            effects: self.effects,
            may_delegate: self.may_delegate,
            commitment_mode: self.commitment_mode,
            balance_change,
            witness_blobs: vec![],
        }
    }

    /// Finalize and consume the children too — returns `(root, children)`.
    pub fn build_with_children(self) -> (Action, Vec<Action>) {
        let children = self.children.clone();
        let action = self.build();
        (action, children)
    }
}

// ─── Legacy ActionBuilder (compat) ────────────────────────────────────────────

/// Legacy `&mut self`-chain builder, preserved for migration scaffolding.
///
/// New code should use the typestate [`ActionBuilder`] directly. This type
/// always produces actions with `Authorization::Unchecked` and is intended
/// only for tests/benches that have not yet been migrated.
///
/// All external call sites have been migrated to [`ActionBuilder`]. This type
/// is now crate-private; it will be deleted in a follow-up cleanup once
/// `TurnBuilder::action()` and `TurnBuilder::legacy_action_builders` are
/// fully excised.
pub(crate) struct LegacyActionBuilder {
    target: CellId,
    method: String,
    args: Vec<FieldElement>,
    authorization: Authorization,
    preconditions: Preconditions,
    effects: Vec<Effect>,
    may_delegate: DelegationMode,
    commitment_mode: CommitmentMode,
    balance_change: Option<i64>,
    witness_blobs: Vec<WitnessBlob>,
    children: Vec<LegacyActionBuilder>,
}

impl LegacyActionBuilder {
    /// Internal constructor used by `TurnBuilder::action()`.
    fn new(target: CellId, method: &str) -> Self {
        LegacyActionBuilder {
            target,
            method: method.to_string(),
            args: Vec::new(),
            // NOTE: This intentionally defaults to `Unchecked`. The
            // typestate-bearing path (`turn::builder::ActionBuilder`) cannot
            // reach this state without the loud
            // `new_unchecked_for_tests` constructor. This legacy path is for
            // tests/benches only; CI grep-guards production code paths.
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: Vec::new(),
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
            children: Vec::new(),
        }
    }

    /// Add an argument to the action.
    pub fn arg(&mut self, value: FieldElement) -> &mut Self {
        self.args.push(value);
        self
    }

    /// Set the authorization to a signature.
    pub fn authorize_signature(&mut self, sig: [u8; 64]) -> &mut Self {
        self.authorization = Authorization::from_sig_bytes(sig);
        self
    }

    /// Set the authorization to a ZK proof with its bound (action, resource) pair.
    pub fn authorize_proof(
        &mut self,
        proof: Vec<u8>,
        bound_action: impl Into<String>,
        bound_resource: impl Into<String>,
    ) -> &mut Self {
        self.authorization = Authorization::Proof {
            proof_bytes: proof,
            bound_action: bound_action.into(),
            bound_resource: bound_resource.into(),
        };
        self
    }

    /// Set the authorization to a breadstuff capability token.
    pub fn authorize_breadstuff(&mut self, token: [u8; 32]) -> &mut Self {
        self.authorization = Authorization::Breadstuff(token);
        self
    }

    /// Add an effect to this action.
    pub fn effect(&mut self, effect: Effect) -> &mut Self {
        self.effects.push(effect);
        self
    }

    /// Set the delegation mode for children.
    pub fn delegation(&mut self, mode: DelegationMode) -> &mut Self {
        self.may_delegate = mode;
        self
    }

    /// Set a nonce precondition.
    pub fn require_nonce(&mut self, nonce: u64) -> &mut Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.nonce = Some(nonce);
        self
    }

    /// Set a minimum balance precondition.
    pub fn require_min_balance(&mut self, min: u64) -> &mut Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.min_balance = Some(min);
        self
    }

    /// Set a state field equality precondition.
    pub fn require_field_equals(&mut self, index: usize, value: FieldElement) -> &mut Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.field_equals.push((index, value));
        self
    }

    /// Set a proved_state precondition.
    pub fn require_proved_state(&mut self, expected: bool) -> &mut Self {
        let cell_pre = self
            .preconditions
            .cell_state
            .get_or_insert_with(Default::default);
        cell_pre.proved_state = Some(expected);
        self
    }

    /// Set preconditions directly.
    pub fn preconditions(&mut self, pre: Preconditions) -> &mut Self {
        self.preconditions = pre;
        self
    }

    /// Add a child action.
    pub fn child(&mut self, target: CellId, method: &str) -> &mut LegacyActionBuilder {
        self.children.push(LegacyActionBuilder::new(target, method));
        self.children.last_mut().unwrap()
    }

    /// Set the commitment mode for this action.
    pub fn commitment_mode(&mut self, mode: CommitmentMode) -> &mut Self {
        self.commitment_mode = mode;
        self
    }

    /// Set a signed balance change for this action (Mina-style excess tracking).
    pub fn balance_change(&mut self, delta: i64) -> &mut Self {
        self.balance_change = Some(delta);
        self
    }

    fn build_action(&self) -> Action {
        Action {
            target: self.target,
            method: symbol(&self.method),
            args: self.args.clone(),
            authorization: self.authorization.clone(),
            preconditions: self.preconditions.clone(),
            effects: self.effects.clone(),
            may_delegate: self.may_delegate,
            commitment_mode: self.commitment_mode,
            balance_change: self.balance_change,
            witness_blobs: vec![],
        }
    }

    fn into_action_and_children(self) -> (Action, Vec<Action>) {
        let action = self.build_action();
        let children = self
            .children
            .into_iter()
            .map(|c| c.build_action())
            .collect();
        (action, children)
    }

    fn compute_excess_recursive(&self) -> i64 {
        let mut total: i64 = 0;
        if let Some(delta) = self.balance_change {
            total = total.saturating_sub(delta);
        }
        for child in &self.children {
            total = total.saturating_add(child.compute_excess_recursive());
        }
        total
    }
}

/// Convenience functions for building common effect types on the legacy
/// builder. Maintained for test scaffolding.
impl LegacyActionBuilder {
    pub fn set_field(&mut self, cell: CellId, index: usize, value: FieldElement) -> &mut Self {
        self.effects.push(Effect::SetField { cell, index, value });
        self
    }

    pub fn transfer(&mut self, from: CellId, to: CellId, amount: u64) -> &mut Self {
        self.effects.push(Effect::Transfer { from, to, amount });
        self
    }

    pub fn increment_nonce(&mut self, cell: CellId) -> &mut Self {
        self.effects.push(Effect::IncrementNonce { cell });
        self
    }

    pub fn emit_event(&mut self, cell: CellId, topic: &str, data: Vec<FieldElement>) -> &mut Self {
        self.effects.push(Effect::EmitEvent {
            cell,
            event: Event::new(symbol(topic), data),
        });
        self
    }

    pub fn grant_capability(&mut self, from: CellId, to: CellId, cap: CapabilityRef) -> &mut Self {
        self.effects.push(Effect::GrantCapability { from, to, cap });
        self
    }

    pub fn revoke_capability(&mut self, cell: CellId, slot: u32) -> &mut Self {
        self.effects.push(Effect::RevokeCapability { cell, slot });
        self
    }

    pub fn create_cell(
        &mut self,
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: u64,
    ) -> &mut Self {
        self.effects.push(Effect::CreateCell {
            public_key,
            token_id,
            balance,
        });
        self
    }

    pub fn set_permissions(
        &mut self,
        cell: CellId,
        new_permissions: pyana_cell::Permissions,
    ) -> &mut Self {
        self.effects.push(Effect::SetPermissions {
            cell,
            new_permissions,
        });
        self
    }

    pub fn set_verification_key(
        &mut self,
        cell: CellId,
        new_vk: Option<pyana_cell::VerificationKey>,
    ) -> &mut Self {
        self.effects
            .push(Effect::SetVerificationKey { cell, new_vk });
        self
    }

    pub fn introduce(
        &mut self,
        introducer: CellId,
        recipient: CellId,
        target: CellId,
        permissions: pyana_cell::AuthRequired,
    ) -> &mut Self {
        self.effects.push(Effect::Introduce {
            introducer,
            recipient,
            target,
            permissions,
        });
        self
    }
}
