//! TurnExecutor: applies a turn to a ledger with full atomicity.
//!
//! # Trust Model
//!
//! This module operates at the **EXECUTOR-TRUSTED** trust level.
//!
//! - **Soundness**: Correct state transitions are guaranteed IF all federation members
//!   execute the same turns in the same order and reach consensus on the resulting state.
//!   A compromised executor can produce incorrect state that other honest members will
//!   reject during replication.
//! - **Assumptions**: At least 2f+1 honest federation members (BFT assumption). The
//!   executor correctly implements the turn semantics, precondition checks, and effect
//!   application. External parties trust the federation as a whole.
//! - **Verifiable by**: Other federation members via state replication. External parties
//!   trust the federation's attested root (not individually verifiable without re-execution).
//!
//! ## Trust-Critical Functions
//!
//! The following functions are trust-critical and are annotated individually:
//! - `execute()` — atomically applies a turn; if compromised, state diverges from consensus
//! - `verify_authorization()` — gates all state mutations; bypass = unauthorized writes
//! - `apply_effect()` — mutates ledger state; incorrect application = balance corruption
//! - `verify_and_commit_proof()` — bridges trustless (STARK) to executor; bypass = forged sovereign state
//! - `check_preconditions()` — temporal and state guards; bypass = expired/invalid actions succeed
//!
//! ## Path to Trustless
//!
//! Phase 3 (proof-carrying sovereign turns) already moves sovereign cells to the
//! trustless level: the executor merely verifies a STARK proof and updates a commitment.
//! The remaining executor-trusted path (Phase 2: classical call-forest execution) will
//! transition to trustless once the Effect VM circuit covers all effect types, allowing
//! every turn to carry a proof.
//!
//! The executor walks the call forest depth-first, checking preconditions,
//! verifying authorization, applying effects, and metering computrons at each step.
//! If any action fails, ALL effects are rolled back via journal replay (atomicity guarantee).

use std::collections::HashMap;
use std::sync::Mutex;

#[allow(unused_imports)]
use tracing::info;

use dregg_cell::{
    AuthRequired, Cell, CellId, CellStateDelta, FIELD_ZERO, FieldElement, Ledger, LedgerDelta,
    RevocationChannelSet,
    note::NoteError,
    nullifier_set::NullifierSet,
    preconditions::EvalContext,
    predicate::{InputRef, PredicateInput, WitnessedPredicateError, WitnessedPredicateKind},
    state::STATE_SLOTS,
};
use dregg_cell_crypto::{
    BulletproofRangeProof, ValueCommitment, ValueCommitmentBytes, note_bridge::BridgedNullifierSet,
};
use dregg_types::AttestedRoot;
use ed25519_dalek::{Signature, VerifyingKey};

use crate::action::{Action, Authorization, DelegationMode, Effect, Event};
use crate::budget_gate::BudgetGate;
use crate::error::TurnError;
use crate::forest::CallTree;
use crate::journal::{JournalEntry, LedgerJournal};
use crate::routing::RoutingDirective;
use crate::turn::{EmittedEvent, Turn, TurnReceipt, TurnResult};

use dregg_dsl_runtime::ProgramRegistry;

pub type RateLimitCounterKey = (CellId, [u8; 32], u64);
pub type RateLimitSumKey = (CellId, u8, u64);

/// Whether a single `Effect` is a `Burn`, recursing into
/// `ExerciseViaCapability::inner_effects`. Powers `was_burn` disclosure.
fn effect_is_burn(e: &Effect) -> bool {
    match e {
        Effect::Burn { .. } => true,
        Effect::ExerciseViaCapability { inner_effects, .. } => {
            inner_effects.iter().any(effect_is_burn)
        }
        _ => false,
    }
}

/// Recursive: does any action in this tree carry an `Effect::Burn`?
fn tree_has_burn_effect(t: &crate::forest::CallTree) -> bool {
    if t.action.effects.iter().any(effect_is_burn) {
        return true;
    }
    t.children.iter().any(tree_has_burn_effect)
}

/// Human-readable name of a `WitnessedPredicateKind` for diagnostic
/// error messages (used by `TurnError::AuthModeNotRegistered`).
fn predicate_kind_name(kind: WitnessedPredicateKind) -> String {
    match kind {
        WitnessedPredicateKind::Dfa => "Dfa".into(),
        WitnessedPredicateKind::Temporal => "Temporal".into(),
        WitnessedPredicateKind::MerkleMembership => "MerkleMembership".into(),
        WitnessedPredicateKind::NonMembership => "NonMembership".into(),
        WitnessedPredicateKind::BlindedSet => "BlindedSet".into(),
        WitnessedPredicateKind::BridgePredicate => "BridgePredicate".into(),
        WitnessedPredicateKind::PedersenEquality => "PedersenEquality".into(),
        WitnessedPredicateKind::Custom { .. } => "Custom".into(),
    }
}

/// 32-byte vk_hash for `WitnessedPredicateKind::Custom { vk_hash }`;
/// zeroed for built-in kinds (the built-in identity is in the name).
fn predicate_kind_vk_hash(kind: WitnessedPredicateKind) -> [u8; 32] {
    match kind {
        WitnessedPredicateKind::Custom { vk_hash } => vk_hash,
        _ => [0u8; 32],
    }
}

/// Estimate the metering cost of a single [`Authorization`] variant.
///
/// Recurses into [`Authorization::OneOf`]'s candidates and returns the
/// maximum cost (pessimistic upper bound so a malicious chooser can't
/// sneak a cheaper-than-actual candidate through the meter).
fn estimate_authorization_cost(auth: &Authorization, costs: &ComputronCosts) -> u64 {
    match auth {
        Authorization::Signature(_, _) => costs.signature_verify,
        Authorization::Proof { .. } => costs.proof_verify,
        Authorization::Breadstuff(_) => costs.signature_verify / 2,
        Authorization::Bearer(_) => costs.signature_verify,
        Authorization::Unchecked => 0,
        Authorization::CapTpDelivered { .. } => costs.signature_verify.saturating_mul(2),
        Authorization::Custom { .. } => costs.proof_verify,
        Authorization::OneOf { candidates, .. } => candidates
            .iter()
            .map(|c| estimate_authorization_cost(c, costs))
            .max()
            .unwrap_or(0),
        // Stealth: one Ed25519 verify + one point addition; meter as a
        // signature verify.
        Authorization::Stealth { .. } => costs.signature_verify,
        // Token: a biscuit/macaroon cryptographic verify + Datalog/caveat
        // evaluation; meter as a proof verify (it is the heaviest auth path).
        Authorization::Token { .. } => costs.proof_verify,
    }
}

/// Cav-Codex Block 3: project a cell-program's declared
/// `StateConstraint` list into the Effect-VM slot-caveat manifest
/// (the (count, entries[]) PI surface that
/// `dregg_circuit::effect_vm::verify_slot_caveat_manifest` will
/// re-evaluate).
///
/// Returns `(count, manifest)` where `count <= MAX_SLOT_CAVEATS` and
/// `manifest[..count]` carries one entry per binding-eligible
/// constraint. Constraints whose AIR teeth aren't yet implemented
/// (Custom, Witnessed, BoundDelta, FieldGteHeight, FieldLteHeight,
/// FieldDeltaInRange, RateLimit, RateLimitBySum, BoundedBy,
/// PreimageGate, multi-pair AllowedTransitions, AnyOf, SumEqualsAcross,
/// SumEquals, CapabilityUniqueness, TemporalPredicate)
/// are skipped at projection time; they still evaluate
/// executor-side, but the proof carries no manifest entry that
/// binds them — see `SLOT-CAVEATS-DESIGN.md` §4 ("AIR enforcement is
/// strong-soundness opt-in").
pub fn project_slot_caveat_manifest(
    constraints: &[dregg_cell::StateConstraint],
) -> (
    u32,
    [dregg_circuit::effect_vm::SlotCaveatEntry; dregg_circuit::effect_vm::pi::MAX_SLOT_CAVEATS],
) {
    use dregg_circuit::effect_vm::SlotCaveatEntry;
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::field::BabyBear;

    let mut entries = [SlotCaveatEntry::zero(); pi::MAX_SLOT_CAVEATS];
    let mut count: usize = 0;

    /// Project a 32-byte field-element to a BabyBear via the
    /// low-4-bytes path used everywhere else by the Effect VM's
    /// state column truncation.
    fn fe_to_bb(fe: &[u8; 32]) -> BabyBear {
        let mut buf = [0u8; 4];
        buf.copy_from_slice(&fe[0..4]);
        BabyBear::new(u32::from_le_bytes(buf))
    }

    for c in constraints {
        if count >= pi::MAX_SLOT_CAVEATS {
            break;
        }
        let entry = match c {
            dregg_cell::StateConstraint::Immutable { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_IMMUTABLE,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::WriteOnce { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::FieldDelta { index, delta } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
                slot_index: *index,
                params: [
                    fe_to_bb(delta),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::MonotonicSequence { seq_index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
                slot_index: *seq_index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::FieldEquals { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_EQUALS,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::FieldGte { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_GTE,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::FieldLte { index, value } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_FIELD_LTE,
                slot_index: *index,
                params: [
                    fe_to_bb(value),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            dregg_cell::StateConstraint::Monotonic { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::StrictMonotonic { index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
                slot_index: *index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::TemporalGate {
                not_before,
                not_after,
            } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
                // TemporalGate is cell-scoped, not slot-scoped — store
                // slot_index = 0 sentinel; the verifier never reads it.
                slot_index: 0,
                params: [
                    BabyBear::new((not_before.unwrap_or(0) & 0x7FFF_FFFF) as u32),
                    BabyBear::new((not_after.unwrap_or(0) & 0x7FFF_FFFF) as u32),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            // Register-reading temporal atoms (the proven `TemporalAlgebra`
            // family, now AIR-projected). The re-evaluation reads the PRE-state
            // slot view (`initial_fields[slot]`), matching the executor's
            // committed-pre-state register read and the Lean atom semantics.
            dregg_cell::StateConstraint::RateBound { counter_index, k } => {
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_RATE_BOUND,
                    slot_index: *counter_index,
                    params: [
                        BabyBear::new((*k & 0x7FFF_FFFF) as u32),
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                    ],
                })
            }
            // Height-only: lower to the deployed `TemporalGate` AIR teeth
            // (not_before = staged_at + period; cell-scoped, slot 0).
            dregg_cell::StateConstraint::CooledSince { staged_at, period } => {
                let boundary = staged_at.saturating_add(*period);
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
                    slot_index: 0,
                    params: [
                        BabyBear::new((boundary & 0x7FFF_FFFF) as u32),
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                    ],
                })
            }
            dregg_cell::StateConstraint::UntilEvent { flag_index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_UNTIL_EVENT,
                slot_index: *flag_index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::SinceEvent { flag_index } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_SINCE_EVENT,
                slot_index: *flag_index,
                params: [BabyBear::ZERO; 4],
            }),
            dregg_cell::StateConstraint::ChallengeWindow {
                challenge_index,
                staged_at,
                period,
            } => {
                let boundary = staged_at.saturating_add(*period);
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_CHALLENGE_WINDOW,
                    slot_index: *challenge_index,
                    params: [
                        BabyBear::new((boundary & 0x7FFF_FFFF) as u32),
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                        BabyBear::ZERO,
                    ],
                })
            }
            dregg_cell::StateConstraint::SenderAuthorized { set } => {
                let slot_index = match set {
                    dregg_cell::program::AuthorizedSet::PublicRoot { set_root_index } => {
                        *set_root_index
                    }
                    dregg_cell::program::AuthorizedSet::BlindedSet { .. } => 0,
                    // CredentialSet dispatches via the BlindedSet verifier
                    // off-chain (see AuthorizedSet::credential_set_commitment).
                    // No public-slot root to index — use 0 as the
                    // "no-slot" sentinel like BlindedSet.
                    dregg_cell::program::AuthorizedSet::CredentialSet { .. } => 0,
                };
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_SENDER_AUTHORIZED,
                    slot_index,
                    params: [BabyBear::ZERO; 4],
                })
            }
            dregg_cell::StateConstraint::AllowedTransitions {
                slot_index,
                allowed,
            } if allowed.len() == 1 => {
                let (old_v, new_v) = &allowed[0];
                Some(SlotCaveatEntry {
                    type_tag: pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
                    slot_index: *slot_index,
                    params: [
                        BabyBear::ONE,
                        fe_to_bb(old_v),
                        fe_to_bb(new_v),
                        BabyBear::ZERO,
                    ],
                })
            }
            dregg_cell::StateConstraint::AllowedTransitions { .. } => None,
            // The sealed-escrow atomic-swap gate (the Lean `SettleGate`,
            // `metatheory/Dregg2/Deos/SealedEscrow.lean` §6 — the staged weld,
            // `docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`). A SINGLE entry reading
            // BOTH leg slots: slot_index = leg A's status slot, p0 = leg B's
            // status slot. The verifier re-evaluates the atomic both-or-none
            // transition (both Deposited before, both Consumed after) off-AIR
            // against the bound state_before/state_after views — VK UNCHANGED,
            // exactly like the temporal tags 13–16. Additive + gated by a cell
            // DECLARING the caveat, so it is dead-by-default until a cell opts in
            // at the sealed-escrow verifier epoch (no deployed cell declares it).
            dregg_cell::StateConstraint::SettleEscrow {
                leg_a_index,
                leg_b_index,
            } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
                slot_index: *leg_a_index,
                params: [
                    BabyBear::new(*leg_b_index as u32),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            // The standing-obligation per-period discharge gate (the Lean
            // `DischargeGate`, `metatheory/Dregg2/Deos/StandingObligation.lean` §6b —
            // the staged weld, `docs/deos/DISCHARGE-OBLIGATION-WELD-DESIGN.md`). A
            // SINGLE entry: slot_index = the `next_due` cursor slot, p0 = due-block
            // slot, p1 = discharged-total slot, p2 = period, p3 = amount. The verifier
            // re-evaluates the schedule shape (due ∧ cursor advanced one period ∧
            // total advanced by the exact amount) off-AIR against the bound
            // state_before/state_after views — VK UNCHANGED, exactly like the temporal
            // tags 13–16 and the sealed-escrow tag 17. Additive + gated by a cell
            // DECLARING the caveat, so it is dead-by-default until a cell opts in at
            // the standing-obligation verifier epoch (no deployed cell declares it).
            dregg_cell::StateConstraint::DischargeObligation {
                cursor_slot,
                due_slot,
                amount_slot,
                period,
                amount,
            } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
                slot_index: *cursor_slot,
                params: [
                    BabyBear::new(*due_slot as u32),
                    BabyBear::new(*amount_slot as u32),
                    BabyBear::new(*period),
                    BabyBear::new(*amount),
                ],
            }),
            // The share-vault no-dilution deposit gate (the Lean `VaultDepositGate`,
            // `metatheory/Dregg2/Deos/Vault.lean` §6b — the staged weld,
            // `docs/deos/VAULT-DEPOSIT-WELD-DESIGN.md`). A SINGLE entry: slot_index =
            // the `total_assets` counter slot, p0 = the `total_shares` counter slot.
            // The verifier re-evaluates the no-dilution shape (assets advance by a
            // positive deposit ∧ shares advance by a positive mint ∧ no existing holder
            // diluted) off-AIR against the bound state_before/state_after views — the
            // deposit `d` and minted `m` are the across-transition slot deltas, so no
            // per-deposit constant is needed. VK UNCHANGED, exactly like the temporal
            // tags 13–16, the sealed-escrow tag 17, and the standing-obligation tag 18.
            // Additive + gated by a cell DECLARING the caveat, so it is dead-by-default
            // until a cell opts in at the share-vault verifier epoch (no deployed cell
            // declares it).
            dregg_cell::StateConstraint::VaultDeposit {
                assets_slot,
                shares_slot,
            } => Some(SlotCaveatEntry {
                type_tag: pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
                slot_index: *assets_slot,
                params: [
                    BabyBear::new(*shares_slot as u32),
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                    BabyBear::ZERO,
                ],
            }),
            // Deferred — no AIR teeth in Block 3 first wave.
            dregg_cell::StateConstraint::SumEquals { .. }
            | dregg_cell::StateConstraint::FieldLteField { .. }
            // Record-level relational caveat (cross-slot `new[i] <= new[o] +
            // delta`) is enforced by the scalar post-state evaluator, not via a
            // per-slot AIR projection — deferred like the other record-level
            // relational atoms above.
            | dregg_cell::StateConstraint::FieldLteOther { .. }
            | dregg_cell::StateConstraint::BoundedBy { .. }
            | dregg_cell::StateConstraint::FieldDeltaInRange { .. }
            | dregg_cell::StateConstraint::FieldGteHeight { .. }
            | dregg_cell::StateConstraint::FieldLteHeight { .. }
            | dregg_cell::StateConstraint::SumEqualsAcross { .. }
            | dregg_cell::StateConstraint::CapabilityUniqueness { .. }
            | dregg_cell::StateConstraint::RateLimit { .. }
            | dregg_cell::StateConstraint::RateLimitBySum { .. }
            | dregg_cell::StateConstraint::PreimageGate { .. }
            // `KeyRotationGate` (pre-rotation) is executor-enforced like
            // `PreimageGate`; no AIR projection yet (the preimage exhibit
            // reads the OLD digest register — a future row-bound gadget
            // pins (state_before.fields[d], state_after.fields[d])).
            | dregg_cell::StateConstraint::KeyRotationGate { .. }
            | dregg_cell::StateConstraint::TemporalPredicate { .. }
            | dregg_cell::StateConstraint::BoundDelta { .. }
            | dregg_cell::StateConstraint::AnyOf { .. }
            | dregg_cell::StateConstraint::Witnessed { .. }
            // `Renounced` is the categorical dual of SenderAuthorized
            // (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2). No AIR projection
            // in Block-3 first wave; the witness side is checked by the
            // `WitnessedPredicateRegistry` NonMembership verifier.
            | dregg_cell::StateConstraint::Renounced { .. }
            // Predicate-language extensions (MemberOf/PrefixOf/InRangeTwoSided/
            // DeltaBounded/AffineLe/AffineEq/Reachable/AllOf) have no SlotCaveat
            // AIR projection in this first wave — deferred like the others above.
            | dregg_cell::StateConstraint::MemberOf { .. }
            | dregg_cell::StateConstraint::PrefixOf { .. }
            | dregg_cell::StateConstraint::InRangeTwoSided { .. }
            | dregg_cell::StateConstraint::DeltaBounded { .. }
            | dregg_cell::StateConstraint::AffineLe { .. }
            | dregg_cell::StateConstraint::AffineEq { .. }
            | dregg_cell::StateConstraint::Reachable { .. }
            | dregg_cell::StateConstraint::AllOf { .. }
            | dregg_cell::StateConstraint::Custom { .. }
            // Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3): sender +
            // own-balance reads. The sender pk and the sealed balance are
            // not state-column data in the current AIR layout, so these
            // stay executor-enforced (no SlotCaveat projection) until the
            // context columns land (layout rotation, doc §6).
            | dregg_cell::StateConstraint::SenderIs { .. }
            | dregg_cell::StateConstraint::SenderInSlot { .. }
            | dregg_cell::StateConstraint::BalanceGte { .. }
            | dregg_cell::StateConstraint::BalanceLte { .. }
            // Heap-keyed / collection atoms bind heap keys or a collection
            // run, not a u8 register slot — executor-enforced by the scalar
            // evaluator; no SlotCaveat AIR projection.
            | dregg_cell::StateConstraint::HeapField { .. }
            // CollectionAggregate opens an element run in the heap and
            // evaluates a CollPred aggregate — no AIR slot projection.
            | dregg_cell::StateConstraint::CollectionAggregate { .. }
            // FieldsCollectionAggregate opens an element run in the
            // executor-reachable user-field map (`fields_map`) and evaluates
            // a CollPred aggregate — executor-enforced by the scalar
            // evaluator; the map tail commits via `fields_root`, not a u8
            // register-slot SlotCaveat AIR column.
            | dregg_cell::StateConstraint::FieldsCollectionAggregate { .. }
            // The delegation_epoch tie reads the sealed per-cell counter
            // (`TransitionMeta::delegation_epoch`), not a state column in
            // the current AIR layout — executor-enforced like the other
            // context atoms until the context columns land.
            | dregg_cell::StateConstraint::DelegationEpochEquals { .. }
            // CountGe opens a witness-exhibited set against a slot
            // commitment — witness-side enforcement (the scalar evaluator
            // + the unique Cleartext blob), no SlotCaveat AIR projection.
            | dregg_cell::StateConstraint::CountGe { .. }
            // Predicate / balance-delta atoms (SenderMemberOf membership;
            // BalanceDeltaLte/Gte + AffineDeltaLe over the sealed signed
            // balance) bind no state-column register slot — executor-enforced
            // by the scalar evaluator, no SlotCaveat AIR projection in this
            // wave (deferred like the AffineLe/AffineEq / BalanceGte/Lte atoms
            // above).
            | dregg_cell::StateConstraint::SenderMemberOf { .. }
            | dregg_cell::StateConstraint::BalanceDeltaLte { .. }
            | dregg_cell::StateConstraint::BalanceDeltaGte { .. }
            | dregg_cell::StateConstraint::AffineDeltaLe { .. }
            // Cross-cell observed-root tie (`local[i] == peer[j]` at the peer's
            // finalized root): reads ANOTHER cell's state, not a register slot
            // in this cell's AIR — witness/executor-enforced against the
            // supplied finalized roots (fails closed when absent), no SlotCaveat
            // AIR projection in this wave (deferred like the other cross-cell
            // relational atoms above).
            | dregg_cell::StateConstraint::ObservedFieldEquals { .. }
            // Witnessed branches under ⊔ (CELL-PROGRAM-LANGUAGE.md §11.3): the
            // disjunction carries witnessed cross-cell + context-reading
            // branches, none of which project to a single register slot in this
            // wave — executor-enforced by the scalar evaluator (each branch
            // calls the evaluator the executor already owns), no SlotCaveat AIR
            // projection (deferred like `AnyOf` / `ObservedFieldEquals`).
            | dregg_cell::StateConstraint::AnyOfBound { .. }
            // Typed dig/sym field atoms (PredAlgebra typed leaves). In the
            // untyped 8-slot substrate `SymEq`/`SymMemberOf` read the u64 lane
            // (the `MemberOf` path) and `DigEq` is the full-field compare (the
            // `FieldEquals` path) — but the lanes they coincide with (`MemberOf`,
            // `FieldLteField`) are themselves NOT SlotCaveat-projected in this
            // wave (they are `=> None` above, scalar-evaluator-enforced). So the
            // typed atoms join them: no per-slot SlotCaveat AIR projection,
            // executor-enforced by the scalar evaluator (cell/program.rs already
            // owns their arms). `DigFieldEq` (cross-slot full-digest equality)
            // is likewise scalar-enforced — its untyped sibling `FieldLteField`
            // is `None` here, and a cross-slot tie binds two registers, not the
            // single `slot_index` a SlotCaveatEntry carries.
            | dregg_cell::StateConstraint::SymEq { .. }
            | dregg_cell::StateConstraint::SymMemberOf { .. }
            | dregg_cell::StateConstraint::DigEq { .. }
            | dregg_cell::StateConstraint::DigFieldEq { .. }
            // Root-bound clearance-graph dominance: binds the actor-label slot
            // AND the committed-root slot, walks a graph carried in the program
            // body, and verifies the carried graph commits to the stored root.
            // Two-slot + data-bearing — no single-`slot_index` SlotCaveat AIR
            // projection in this wave; scalar-evaluator-enforced (cell/program.rs
            // owns its arm), like `Reachable` / `AnyOfBound` above.
            | dregg_cell::StateConstraint::ClearanceDominates { .. } => None,
        };
        if let Some(e) = entry {
            entries[count] = e;
            count += 1;
        }
    }
    (count as u32, entries)
}

/// **The REQUIRED-TAG re-derivation (constraint-binding weld, the soundness core).**
/// The capacity caveat tags a cell's declared constraint-set REQUIRES — the Rust
/// twin of the Lean `Dregg2.Deos.ConstraintBinding.requiredTags`. A capacity
/// `StateConstraint` (`SettleEscrow` / `DischargeObligation` / `VaultDeposit`) is a
/// JOINT invariant whose manifest entry MUST be present for a turn on the cell to be
/// sound (omitting it would leave the atomicity / on-schedule / no-dilution gate
/// unchecked). This returns those required tags so a verifier can DEMAND coverage
/// (`dregg_circuit::effect_vm::verify_slot_caveat_coverage`).
///
/// Because a cell's declared `state_constraints` are bound into committed state
/// (`dregg_cell::commitment::compute_authority_digest_felt` folds `cell.program` —
/// hence these constraints — into the `B_AUTHORITY_DIGEST` limb of the ~124-bit wide
/// commit a light client binds), re-deriving the required tags from the COMMITTED
/// declaration and demanding coverage makes the gate omission-proof: a forger cannot
/// drop the entry (coverage fails) nor swap in a hollow declaration (it would have to
/// match the committed authority digest — the Lean `DeclCommitBinds` floor). Only the
/// JOINT capacity gates are required here; the per-slot caveats are independently
/// re-evaluated by `verify_slot_caveat_manifest` when present and need no coverage
/// floor. STAGED: this is the re-derivation a future `verify_full_turn_bound` arm
/// consumes; no deployed cell declares a capacity caveat yet. See
/// `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`.
pub fn required_capacity_caveat_tags(constraints: &[dregg_cell::StateConstraint]) -> Vec<u32> {
    use dregg_circuit::effect_vm::pi;
    let mut tags = Vec::new();
    for c in constraints {
        let tag = match c {
            dregg_cell::StateConstraint::SettleEscrow { .. } => {
                Some(pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW)
            }
            dregg_cell::StateConstraint::DischargeObligation { .. } => {
                Some(pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION)
            }
            dregg_cell::StateConstraint::VaultDeposit { .. } => {
                Some(pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT)
            }
            _ => None,
        };
        if let Some(t) = tag
            && !tags.contains(&t)
        {
            tags.push(t);
        }
    }
    tags
}

/// Whether note effects in a turn use Pedersen value commitments or cleartext values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NoteCommitmentMode {
    /// No note effects present in the turn.
    Empty,
    /// All note effects use cleartext values (legacy path).
    Cleartext,
    /// All note effects carry Pedersen value commitments (committed path).
    Committed,
    /// Some notes have commitments, some don't -- invalid (rejected).
    Mixed,
}

/// Trait for verifying ZK proofs. Implementations provide circuit-specific verification.
///
/// The executor is fail-closed: if no ProofVerifier is configured and a cell requires
/// proof authorization, the action is rejected.
pub trait ProofVerifier: Send + Sync {
    /// Verify a proof against public inputs and a verification key.
    ///
    /// Returns true if the proof is valid for the given public inputs and verification key.
    fn verify(&self, proof: &[u8], action: &str, resource: &str, vk: &[u8]) -> bool;
}

mod costs;
pub use costs::ComputronCosts;

// =============================================================================
// Cell Migration Two-Phase Commit
// =============================================================================

mod migration;
pub use migration::{CellMigrationManager, MigrationCancelReason, MigrationError, MigrationState};

/// Real STARK-backed MerkleMembership predicate verifier (SenderAuthorized AIR
/// teeth). Lives here (not in `cell/`) because it depends on `dregg-circuit`.
pub mod membership_verifier;
pub use membership_verifier::{
    BridgePredicatePolicyAuthority, BridgePredicateRequirement, BridgePredicateStarkVerifier,
    DslCircuitDfaVerifier, MerkleMembershipStarkVerifier, StaticBridgePredicatePolicy,
    bridge_predicate_commitment_bytes, bridge_predicate_proof_bytes,
    bridge_predicate_range_proof_bytes, prove_dfa_transition, registry_with_real_sender_membership,
    registry_with_real_verifiers, registry_with_real_verifiers_full, single_member_authorized_root,
    single_member_membership_proof,
};
#[cfg(feature = "threshold-sig")]
pub use membership_verifier::{
    StaticThresholdSigPolicy, ThresholdSigCommittee, ThresholdSigPolicyAuthority,
    ThresholdSigVerifier, register_threshold_sig_verifier, threshold_sig_proof_bytes,
};

/// The turn executor: applies turns to a ledger atomically.
mod effect_vm_bridge;
pub use effect_vm_bridge::convert_turn_effects_to_vm;
pub struct TurnExecutor {
    /// Cost configuration for computron metering.
    pub costs: ComputronCosts,
    /// Program registry for custom cell programs (smart contract runtime).
    /// When a sovereign cell has a `verification_key_hash` set, the executor
    /// looks up the deployed program here and verifies proofs against it.
    /// Falls back to `EffectVmAir` if no program is found.
    pub program_registry: ProgramRegistry,
    /// Current timestamp for precondition evaluation.
    pub current_timestamp: i64,
    /// Current block height for precondition evaluation.
    pub block_height: u64,
    /// Per-(cell, sender, epoch) mutation counts for `StateConstraint::RateLimit`.
    ///
    /// This is executor-local consensus state: it is updated only after a turn
    /// commits, and read while building `EvalContext` for the next turn.
    pub rate_limit_counters: Mutex<HashMap<RateLimitCounterKey, u32>>,
    /// Per-(cell, slot, window) running positive deltas for `RateLimitBySum`.
    pub rate_limit_sum_counters: Mutex<HashMap<RateLimitSumKey, u64>>,
    /// Optional ZK proof verifier. If None and a cell requires proof auth, the action is rejected.
    pub proof_verifier: Option<Box<dyn ProofVerifier>>,
    /// Optional budget gate (Stingray bounded counter).
    /// When present, the executor checks the silo's local budget slice before executing
    /// each turn. If the slice cannot cover the turn fee, the turn is rejected with
    /// `TurnError::BudgetExhausted`. On turn failure, the debit is refunded (fast unlock).
    ///
    /// Designed for single-silo-single-thread execution, but uses `Mutex` for interior
    /// mutability to remain sound under concurrent access (future-proofing for async
    /// execution or parallel turn processing).
    pub budget_gate: Option<Mutex<BudgetGate>>,
    /// Trusted federation roots for cross-federation note bridging.
    /// When a BridgeMint effect is processed, the portable proof's source root
    /// must be in this set. Empty = no cross-federation bridges accepted.
    pub trusted_federation_roots: Vec<AttestedRoot>,
    /// This federation's identity (genesis root hash or configured ID).
    /// Prevents cross-federation double-spend via destination binding.
    pub local_federation_id: [u8; 32],
    /// Bridged nullifier set: tracks nullifiers from OTHER federations that have
    /// been bridged into this one. Prevents the same note from being bridged twice.
    pub bridged_nullifiers: Mutex<BridgedNullifierSet>,
    /// Production note-spend nullifier set: tracks every nullifier published by a
    /// successful `Effect::NoteSpend` in this federation. Append-only with
    /// double-spend rejection (`NullifierSet::insert` errors on re-insert).
    /// Rolled back via `JournalEntry::NoteNullifierInserted` if the turn fails
    /// after the insert.
    ///
    /// This is the production-side complement to `bridged_nullifiers` (which
    /// tracks *inbound* cross-federation bridges) — `note_nullifiers` tracks
    /// *local* spends. Together they form the permanent ledger gate that
    /// `Checkpoint::nullifier_set_root` commits to.
    pub note_nullifiers: Mutex<NullifierSet>,
    /// REACTIVE registry (Track 2): the executor's promise-hole store. An
    /// `Effect::Promise`/`Effect::Notify` deposits a kernel-backed pending entry
    /// (the standing commitment / wake) here; an `Effect::React` discharges it.
    ///
    /// The ONE-SHOT spend of a hole is NOT enforced here — it is enforced by the
    /// production `note_nullifiers` set: the hole's id IS the nullifier React
    /// spends, so react-twice (or a replayed hole-id) is rejected by the same
    /// double-spend gate `NoteSpend` rides. This registry holds the wake turn so
    /// the resolution produces a GENUINE receipt over the resolved turn (the
    /// registry's own removal is a second, redundant tooth).
    pub reactive_registry: Mutex<crate::pending::PendingTurnRegistry>,
    /// Trusted Ed25519 public keys for destination federation receipt verification.
    /// Used during BridgeFinalize to validate that the receipt was signed by a
    /// legitimate destination federation.
    pub trusted_destination_keys: Vec<[u8; 32]>,
    /// Block proposer cell (receives 50% of fees). If None, fees are 100% burned.
    pub proposer_cell: Option<CellId>,
    /// Federation treasury cell (receives 30% of fees). If None, that share is burned.
    pub treasury_cell: Option<CellId>,
    /// THE EPOCH §5 ("fees as moves"): the FEE WELL cell. When configured,
    /// every fee share that would previously have been BURNED (the 20%
    /// remainder, rounding dust, and any unconfigured proposer/treasury
    /// share) is instead MOVED here, so a committed turn's value delta is
    /// exactly zero and the deployed chain stays inside guarantee B's
    /// hypotheses (`reachable_total_zero`). Genesis always configures this;
    /// `None` retains the legacy burn-without-credit semantics (pre-epoch
    /// tests only — the deployed chain never runs with `None`).
    pub fee_well_cell: Option<CellId>,
    /// THE EPOCH §5 ("mint/burn as issuer-moves"): asset (`token_id`) →
    /// ISSUER WELL cell. A runtime `Effect::Burn` whose target's asset has a
    /// registered well is executed as a MOVE target→well (the well, carrying
    /// −supply, is credited toward zero), exactly the Lean `burnA` dispatch;
    /// an unregistered asset retains the legacy non-conserving burn. Genesis
    /// registers the devnet issuer well.
    pub issuer_wells: HashMap<[u8; 32], CellId>,
    /// Maximum lifetime (in blocks) for capabilities introduced via three-party
    /// introduction. After `current_height + max_introduction_lifetime`, the routing
    /// directive expires and the introduced capability becomes stale.
    /// Default: 1000 blocks.
    pub max_introduction_lifetime: u64,
    /// Optional revocation channel set. When present, capability exercises and
    /// delegation access checks verify that gated capabilities haven't been revoked
    /// via their associated channel.
    pub revocation_channels: Option<RevocationChannelSet>,
    /// Cell migration manager: tracks cells that are being migrated to other federations.
    /// Uses a two-phase commit protocol with timeout-based cancellation to prevent
    /// cells from being lost during network partitions.
    pub cell_migrations: Mutex<CellMigrationManager>,
    /// Factory registry: deployed factory descriptors and per-epoch creation counts.
    /// When a `CreateCellFromFactory` effect is processed, the factory's constraints
    /// are validated and budget is checked/recorded.
    /// Uses `RefCell` for interior mutability: `apply_effect` takes `&self` but
    /// factory validation needs `&mut` for recording budget usage.
    pub factory_registry: std::cell::RefCell<dregg_cell::FactoryRegistry>,
    /// Optional epoch minter for computron supply management.
    ///
    /// When configured, the executor calls `maybe_mint()` at each block to
    /// check for epoch boundaries and credit the treasury with newly minted
    /// computrons. This prevents the deflationary death spiral where all
    /// computrons are eventually burned.
    ///
    /// Uses `RefCell` for interior mutability since minting is called from
    /// within the execute path which takes `&self`.
    pub epoch_minter: Option<std::cell::RefCell<crate::economics::EpochMinter>>,
    /// Per-agent last receipt hash (P0-3 fix).
    ///
    /// On every successful turn commit, the agent's entry is set to the
    /// resulting receipt's `receipt_hash()`. Subsequent turns from the same
    /// agent must set `turn.previous_receipt_hash` to this value or be
    /// rejected with `TurnError::ReceiptChainMismatch`. An entry with no
    /// value means the agent has no committed turns and must submit with
    /// `previous_receipt_hash: None` (a "genesis" turn for that agent).
    ///
    /// Off-chain `verify::verify_receipt_chain` already enforces this when it
    /// has access to the full chain. This field enforces the same property
    /// AT WRITE TIME, removing the cipherclerk's ability to silently break the
    /// chain by submitting every turn as if it were genesis.
    pub last_receipt_hash: Mutex<HashMap<CellId, [u8; 32]>>,
    /// Per-cell PROVENANCE chain heads — the head of each cell's own receipt
    /// history (every turn that TOUCHED the cell, agent or not). Distinct from the
    /// authority chain `last_receipt_hash` above, which gates a turn's
    /// `previous_receipt_hash` and advances ONLY for the submitting agent: a
    /// merely-touched cell gets a walkable per-cell receipt chain here without its
    /// head locking that cell's next authored turn to a causal edge it never made.
    pub per_cell_receipt_head: Mutex<HashMap<CellId, [u8; 32]>>,
    /// **The last committed turn's exact write-set** — every cell whose serialized
    /// state that turn mutated, captured from the execution journal
    /// ([`crate::journal::LedgerJournal::touched_cells`]) on the success path. A
    /// durable consumer that reconstructs post-state from a per-turn change-set
    /// (the redb commit-log overlay) reads this instead of re-deriving the set
    /// syntactically from the input turn — the syntactic walk misses cells an
    /// effect resolves at runtime (a burn's well, a create's newborn, a factory
    /// birth), which silently corrupts a recovered image (CORE-AUDIT.md finding 1).
    /// Overwritten on every committed turn; empty until the first commit.
    pub last_write_set: Mutex<Vec<CellId>>,
    /// Optional X25519 keypair used to decrypt `EncryptedTurn` submissions.
    ///
    /// When set, callers may submit privacy-preserving `EncryptedTurn`
    /// envelopes via `execute_encrypted_turn`; the executor performs DH with
    /// its static secret and the sender's ephemeral public key, derives the
    /// ChaCha20-Poly1305 key, decrypts the turn body, and dispatches to the
    /// standard `execute` path. Without this key, `execute_encrypted_turn`
    /// rejects with `NoDecryptionKey` — i.e. the executor does not support
    /// the privacy path.
    ///
    /// The tuple is `(secret, public)` so callers don't need to recompute the
    /// public key on every decrypt. Senders bind their ciphertext to the
    /// `public` half via X25519 DH; the `secret` half is the long-term
    /// unsealer.
    pub turn_decryption_keypair: Option<([u8; 32], [u8; 32])>,
    /// When set, the encrypted-turn admission path
    /// ([`Self::execute_encrypted_turn`] / [`Self::apply_encrypted_turn`])
    /// requires the envelope's `TurnValidityProof` to verify
    /// ([`crate::encrypted::EncryptedTurn::verify_stark`]) BEFORE the turn is
    /// decrypted and ordered — closing the fee-DoS hole where an unproven
    /// encrypted blob consumes an ordering slot.
    ///
    /// FAIL-CLOSED when on: because the validity-proof *producer* is not yet
    /// wired (every envelope ships `proof_bytes = vec![]`), enabling this flag
    /// currently rejects ALL encrypted turns via `InvalidValidityProof`. It is
    /// therefore OFF by default (additive: the existing decrypt round-trips and
    /// SDK callers, which build placeholder proofs, keep working). A node that
    /// wants to refuse unproven encrypted submissions sets this; once a real
    /// prover lands, `verify_stark` checks the proof instead of emptiness and
    /// this becomes the always-on production gate.
    pub require_validity_proof: bool,
    /// Optional 32-byte Ed25519 signing key seed used to populate
    /// `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// When set, the executor signs each receipt's `receipt_hash()` and
    /// embeds the 64-byte signature in `receipt.executor_signature`. This is
    /// R-4 of `EFFECT-VM-SHAPE-A.md`: previously the field existed but was
    /// never populated, so the federation-exit path could not actually
    /// authenticate receipts as having come from a known executor.
    ///
    /// `None` reproduces the legacy behavior (receipts ship with
    /// `executor_signature = None`); existing chain-verification code
    /// (`verify_receipt_chain_with_keys`) treats absent signatures as a
    /// best-effort property, so the field is opt-in.
    pub executor_signing_key: Option<[u8; 32]>,
    /// Witnessed-predicate registry (Cav-Codex Block 2 + Block 3.5).
    ///
    /// Slot-caveat variants that need verifier dispatch
    /// (`StateConstraint::Witnessed`, `TemporalPredicate`,
    /// `SenderAuthorized { BlindedSet }`, `Custom`), `Preconditions::witnessed`
    /// clauses, and `CapabilityCaveat::Witnessed` exercise sites all
    /// route through this registry to verify proof bytes from the
    /// action's `witness_blobs`.
    ///
    /// Defaults to [`registry_with_real_verifiers`] on every
    /// `TurnExecutor` constructor. `dregg-turn` links `dregg-circuit`
    /// and OWNS the real STARK-backed verifiers (in
    /// `executor::membership_verifier`), so the sensible default here is
    /// the *real* registry — NOT `dregg_cell`'s `default_builtins`. The
    /// cell crate's `default_builtins` fails MerkleMembership /
    /// NonMembership / BlindedSet / PedersenEquality closed *only*
    /// because cell must not link `dregg-circuit` (dependency cycle); at
    /// the `turn` layer that constraint is gone, so a bare
    /// `TurnExecutor::new()` enforces those four with genuine
    /// cryptographic verifiers: it ADMITS a valid membership proof and
    /// REJECTS a forged one at the STARK level.
    ///
    /// The three kinds that need host-trusted policy context —
    /// `Dfa` (a deployed `ProgramRegistry`), `Temporal` (a
    /// `TemporalPolicyAuthority`), and `BridgePredicate` (a
    /// `BridgePredicatePolicyAuthority`) — DELIBERATELY remain
    /// fail-closed in this default: there is no safe context-free value
    /// for them (auto-accepting would let a prover pick the policy), so
    /// they must be installed explicitly via
    /// [`registry_with_real_verifiers_full`] +
    /// [`Self::set_witnessed_registry`]. The default therefore raises the
    /// floor (real crypto wherever it is context-free) without lowering
    /// any ceiling (the genuinely host-dependent kinds stay closed until
    /// the host wires their authorities).
    ///
    /// Hosts that need a different surface call `set_witnessed_registry`
    /// with their own registry (e.g. `default_builtins()` for a
    /// plumbing-only test that wants every crypto kind stubbed-closed, or
    /// `with_stubs()` for the legacy permissive playground). `None` is
    /// *legal* — it disables dispatch and reverts to the legacy sentinel
    /// surface — but nothing inside `turn` constructs an executor that
    /// way anymore.
    pub witnessed_registry: Option<dregg_cell::WitnessedPredicateRegistry>,
    /// Optional custom-effect verifier registry, parallel structure to
    /// [`dregg_cell::WitnessedPredicateRegistry`] but keyed on the
    /// `Effect::Custom` vk_hash. The proof-carrying turn path consults
    /// this registry **before** falling back to the program registry,
    /// so app-side custom effects (whose canonical bytes are not
    /// `CellProgram`s) can be dispatched through a unified surface
    /// (per `VK-AS-RE-EXECUTION-RECIPE.md` §2.4).
    ///
    /// Absent: the executor uses the existing program-registry path
    /// (legacy DSL-authored cells).
    pub custom_effect_registry: Option<dregg_cell::CustomEffectRegistry>,
    /// Per-turn buffer of CONSUMED-capability witnesses captured at the
    /// authorization sites (cap Phase C — `authorize.rs`
    /// `record_consumed_cap_witness`). Cleared at the start of each turn
    /// (`execute_without_shadow` / `execute_mixed_atomic`) and drained into
    /// `TurnReceipt::consumed_capabilities` at finalize
    /// (`take_consumed_cap_witnesses`). `Mutex` for the same interior-
    /// mutability reason as the other executor side-tables (`&self`
    /// execution path).
    pub consumed_cap_witnesses: Mutex<Vec<crate::turn::ConsumedCapWitness>>,
    /// THE EXECUTOR-STATE BRIDGE flag (`docs/UNIVERSAL-MAP-ROTATION.md` §2.3 — the
    /// universal-memory witness lane, recursion-gated like the umem circuit leg): when
    /// set, `execute()` snapshots the universal-map projection (`crate::umem`) around
    /// the forest journal window and emits the turn's Blum op trace into
    /// [`Self::last_umem_witness`]. ON by default (the umem VK EPOCH — G4): the deployed
    /// executor observes the universal-memory boundary alongside the welded proving path.
    /// This is the OBSERVATION bridge, distinct from the producer weld toggle
    /// (`cipherclerk::umem_weld_staged_enabled`) and the executor verify's `require_welded`.
    pub umem_witness_enabled: std::sync::atomic::AtomicBool,
    /// The most recent turn's universal-memory witness (pre/post projections + the
    /// Blum write trace whose fold connects them), or the emitter's refusal. `None`
    /// until a turn commits with [`Self::umem_witness_enabled`] set.
    pub last_umem_witness: Mutex<Option<Result<crate::umem::UmemTurnWitness, String>>>,
    /// THE MID-FOREST YIELD POINT (`crate::continuation`; Lean twin
    /// `Dregg2/Exec/Continuation.midturn_split`). When set to a journal-prefix LENGTH
    /// `k` (the default sentinel `u64::MAX` = OFF), the live forest walk
    /// (`execute_tree`'s depth-first effect loop) checkpoints the FIRST time its journal
    /// reaches `k` entries — snapshotting `project_executor_state(ledger)` BETWEEN two
    /// effects into [`Self::last_umem_yield`]. This is the live mid-flight capture the
    /// continuations lane needs (vs. the post-commit whole-turn trace cut). It is
    /// recursion-gated by [`Self::umem_witness_enabled`] (the yield only fires when the
    /// umem witness lane is on) so the live proving path is untouched. ATOMICITY: a yield
    /// is an OBSERVATION only — it never short-circuits the walk or emits a receipt; the
    /// turn still commits or rolls back as a whole. See the module banner of
    /// `crate::continuation` for the precise receipt-boundary honesty.
    pub umem_yield_at: std::sync::atomic::AtomicU64,
    /// The mid-flight executor-state projection captured at the [`Self::umem_yield_at`]
    /// journal boundary (the live snapshot taken BETWEEN two effects). `None` until a
    /// yield fires. Paired with [`Self::last_umem_witness`]'s pre-projection + journal
    /// prefix, this is the captured boundary a [`crate::continuation::Continuation`]
    /// suspends into.
    pub last_umem_yield: Mutex<Option<crate::umem::UProjection>>,
    /// THE WITNESS MODE (SYMBOLIC EXECUTION — `crate::collapse`). `0` = Full
    /// (the correct default: materialize every per-turn Merkle witness), `1` =
    /// Symbolic (apply the full state transition but DEFER witness
    /// materialization — skip `Ledger::root()`, stamp the receipt's state-hash
    /// fields with the deferred sentinel). This selects ONLY whether witnesses
    /// are materialized eagerly; it never changes which turns are admitted
    /// (every legality gate runs identically in both modes). An `AtomicU8` so a
    /// `&self` execute path reads it cheaply and a `&self` caller can flip it.
    pub witness_mode: std::sync::atomic::AtomicU8,
    /// THE VERIFIED-LEAN SHADOW SEAM (dependency inversion — `crate::shadow`). The
    /// production execute path drives the differential observer + the strict-veto
    /// rejection authority through this trait object so `dregg-turn` never links
    /// `libdregg_lean.a` directly. A native node injects
    /// `dregg_exec_lean::LeanShadowObserver` (via [`Self::with_shadow_observer`]); every
    /// other construction defaults to [`crate::shadow::NoOpShadowObserver`] — no shadow,
    /// no veto — which is the visible wasm / no-FFI platform fact.
    pub shadow_observer: std::sync::Arc<dyn crate::shadow::ShadowObserver>,
}

impl TurnExecutor {
    /// Create a new executor with the given cost configuration.
    pub fn new(costs: ComputronCosts) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            rate_limit_counters: Mutex::new(HashMap::new()),
            rate_limit_sum_counters: Mutex::new(HashMap::new()),
            proof_verifier: None,
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            reactive_registry: Mutex::new(crate::pending::PendingTurnRegistry::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            fee_well_cell: None,
            issuer_wells: HashMap::new(),
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            last_receipt_hash: Mutex::new(HashMap::new()),
            per_cell_receipt_head: Mutex::new(HashMap::new()),
            last_write_set: Mutex::new(Vec::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            require_validity_proof: false,
            witnessed_registry: Some(membership_verifier::registry_with_real_verifiers()),
            custom_effect_registry: None,
            consumed_cap_witnesses: Mutex::new(Vec::new()),
            umem_witness_enabled: std::sync::atomic::AtomicBool::new(true),
            last_umem_witness: Mutex::new(None),
            umem_yield_at: std::sync::atomic::AtomicU64::new(u64::MAX),
            last_umem_yield: Mutex::new(None),
            witness_mode: std::sync::atomic::AtomicU8::new(0),
            shadow_observer: std::sync::Arc::new(crate::shadow::NoOpShadowObserver),
        }
    }

    /// Inject the verified-Lean shadow/gate observer (dependency inversion — `crate::shadow`).
    ///
    /// A native node calls this with `dregg_exec_lean::LeanShadowObserver` so the production
    /// execute path runs the differential + the strict-veto rejection authority. Without it the
    /// executor keeps the default [`crate::shadow::NoOpShadowObserver`] (no shadow, no veto) — the
    /// visible wasm / no-FFI platform fact.
    pub fn with_shadow_observer(
        mut self,
        observer: std::sync::Arc<dyn crate::shadow::ShadowObserver>,
    ) -> Self {
        self.shadow_observer = observer;
        self
    }

    /// Create a new executor with a budget gate (Stingray bounded counter).
    ///
    /// When a budget gate is set, the executor checks the silo's local budget
    /// slice before executing each turn. If the slice cannot cover the turn fee,
    /// the turn is rejected with `TurnError::BudgetExhausted`.
    pub fn with_budget_gate(costs: ComputronCosts, gate: BudgetGate) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            rate_limit_counters: Mutex::new(HashMap::new()),
            rate_limit_sum_counters: Mutex::new(HashMap::new()),
            proof_verifier: None,
            budget_gate: Some(Mutex::new(gate)),
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            reactive_registry: Mutex::new(crate::pending::PendingTurnRegistry::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            fee_well_cell: None,
            issuer_wells: HashMap::new(),
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            last_receipt_hash: Mutex::new(HashMap::new()),
            per_cell_receipt_head: Mutex::new(HashMap::new()),
            last_write_set: Mutex::new(Vec::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            require_validity_proof: false,
            witnessed_registry: Some(membership_verifier::registry_with_real_verifiers()),
            custom_effect_registry: None,
            consumed_cap_witnesses: Mutex::new(Vec::new()),
            umem_witness_enabled: std::sync::atomic::AtomicBool::new(true),
            last_umem_witness: Mutex::new(None),
            umem_yield_at: std::sync::atomic::AtomicU64::new(u64::MAX),
            last_umem_yield: Mutex::new(None),
            witness_mode: std::sync::atomic::AtomicU8::new(0),
            shadow_observer: std::sync::Arc::new(crate::shadow::NoOpShadowObserver),
        }
    }

    /// Create a new executor with a proof verifier.
    pub fn with_proof_verifier(costs: ComputronCosts, verifier: Box<dyn ProofVerifier>) -> Self {
        TurnExecutor {
            costs,
            program_registry: ProgramRegistry::new(),
            current_timestamp: 0,
            block_height: 0,
            rate_limit_counters: Mutex::new(HashMap::new()),
            rate_limit_sum_counters: Mutex::new(HashMap::new()),
            proof_verifier: Some(verifier),
            budget_gate: None,
            trusted_federation_roots: Vec::new(),
            local_federation_id: [0u8; 32],
            bridged_nullifiers: Mutex::new(BridgedNullifierSet::new()),
            note_nullifiers: Mutex::new(NullifierSet::new()),
            reactive_registry: Mutex::new(crate::pending::PendingTurnRegistry::new()),
            trusted_destination_keys: Vec::new(),
            proposer_cell: None,
            fee_well_cell: None,
            issuer_wells: HashMap::new(),
            treasury_cell: None,
            max_introduction_lifetime: 1000,
            revocation_channels: None,
            cell_migrations: Mutex::new(CellMigrationManager::new()),
            factory_registry: std::cell::RefCell::new(dregg_cell::FactoryRegistry::new()),
            epoch_minter: None,
            last_receipt_hash: Mutex::new(HashMap::new()),
            per_cell_receipt_head: Mutex::new(HashMap::new()),
            last_write_set: Mutex::new(Vec::new()),
            executor_signing_key: None,
            turn_decryption_keypair: None,
            require_validity_proof: false,
            witnessed_registry: Some(membership_verifier::registry_with_real_verifiers()),
            custom_effect_registry: None,
            consumed_cap_witnesses: Mutex::new(Vec::new()),
            umem_witness_enabled: std::sync::atomic::AtomicBool::new(true),
            last_umem_witness: Mutex::new(None),
            umem_yield_at: std::sync::atomic::AtomicU64::new(u64::MAX),
            last_umem_yield: Mutex::new(None),
            witness_mode: std::sync::atomic::AtomicU8::new(0),
            shadow_observer: std::sync::Arc::new(crate::shadow::NoOpShadowObserver),
        }
    }

    /// Set the budget gate.
    pub fn set_budget_gate(&mut self, gate: BudgetGate) {
        self.budget_gate = Some(Mutex::new(gate));
    }

    /// Set the proof verifier.
    pub fn set_proof_verifier(&mut self, verifier: Box<dyn ProofVerifier>) {
        self.proof_verifier = Some(verifier);
    }

    /// Equip the executor with an Ed25519 signing key (32-byte seed) used to
    /// populate `TurnReceipt::executor_signature` on every committed receipt.
    ///
    /// This is R-4 of `EFFECT-VM-SHAPE-A.md`. Until this builder is invoked,
    /// receipts ship with `executor_signature: None` (the legacy behavior);
    /// once set, every receipt produced by this executor — both the proof-
    /// carrying fast path and the standard execution path — is signed with
    /// the given key over the receipt's canonical `receipt_hash()`.
    ///
    /// Verification: `turn::verify::verify_receipt_chain_with_keys` walks the
    /// chain and accepts a receipt only if its `executor_signature` (when
    /// present) verifies against one of the caller-supplied executor public
    /// keys.
    pub fn with_executor_signing_key(mut self, signing_key_seed: [u8; 32]) -> Self {
        self.executor_signing_key = Some(signing_key_seed);
        self
    }

    /// Set the executor signing key after construction.
    pub fn set_executor_signing_key(&mut self, signing_key_seed: [u8; 32]) {
        self.executor_signing_key = Some(signing_key_seed);
    }

    /// Equip the executor with an X25519 keypair so it can decrypt
    /// `EncryptedTurn` submissions.
    ///
    /// `secret` is the 32-byte X25519 static secret (the unsealer);
    /// the public key is derived from it. After this call, callers may
    /// invoke `execute_encrypted_turn` and pass `EncryptedTurn` envelopes
    /// that bind to `public`. Without this key, the executor cannot
    /// participate in the privacy path.
    pub fn with_turn_decryption_secret(mut self, secret: [u8; 32]) -> Self {
        let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        self.turn_decryption_keypair = Some((secret, *public.as_bytes()));
        self
    }

    /// Set the X25519 turn-decryption secret after construction.
    pub fn set_turn_decryption_secret(&mut self, secret: [u8; 32]) {
        let public = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(secret));
        self.turn_decryption_keypair = Some((secret, *public.as_bytes()));
    }

    /// Require that encrypted-turn submissions carry a verifiable
    /// `TurnValidityProof` before being decrypted/ordered (see
    /// [`Self::require_validity_proof`]). FAIL-CLOSED while the validity-proof
    /// producer is unwired: turning this on rejects every encrypted turn (empty
    /// `proof_bytes`) via `InvalidValidityProof`, which is the correct stance
    /// for a node that must not let unproven encrypted blobs consume ordering
    /// slots. Builder form.
    pub fn with_require_validity_proof(mut self, require: bool) -> Self {
        self.require_validity_proof = require;
        self
    }

    /// Set [`Self::require_validity_proof`] after construction.
    pub fn set_require_validity_proof(&mut self, require: bool) {
        self.require_validity_proof = require;
    }

    /// Cav-Codex Block 2: equip the executor with a witnessed-predicate
    /// registry. Programs that declare `Witnessed` / `TemporalPredicate` /
    /// `Custom` / `SenderAuthorized { BlindedSet }` slot caveats will
    /// dispatch through this registry to verify proof bytes carried in
    /// the action's `witness_blobs`.
    pub fn with_witnessed_registry(
        mut self,
        registry: dregg_cell::WitnessedPredicateRegistry,
    ) -> Self {
        self.witnessed_registry = Some(registry);
        self
    }
    /// Set the witnessed-predicate registry after construction.
    pub fn set_witnessed_registry(&mut self, registry: dregg_cell::WitnessedPredicateRegistry) {
        self.witnessed_registry = Some(registry);
    }

    /// Set the [`Effect::Custom`] verifier registry after construction.
    ///
    /// When set, the proof-carrying turn path consults this registry
    /// **before** falling back to `program_registry`, so app-defined
    /// custom effects (whose canonical bytes are not `CellProgram`s)
    /// can be dispatched through a unified surface.
    pub fn set_custom_effect_registry(&mut self, registry: dregg_cell::CustomEffectRegistry) {
        self.custom_effect_registry = Some(registry);
    }

    /// Return the X25519 public key callers should encrypt to (if set).
    pub fn turn_decryption_public(&self) -> Option<[u8; 32]> {
        self.turn_decryption_keypair.map(|(_, pub_key)| pub_key)
    }

    /// Decrypt and execute an `EncryptedTurn` envelope.
    ///
    /// This is the production wiring for the privacy-preserving turn path
    /// (AUDIT-privacy.md §11.2: previously `EncryptedTurn` was exported but
    /// never consumed by the executor). Flow:
    ///
    /// 1. Verify the envelope's metadata (agent/conflict-set/turn-commitment
    ///    bindings via `EncryptedTurn::verify_metadata`).
    /// 2. Decrypt the ciphertext using the executor's static X25519 secret +
    ///    the sender's ephemeral public key. The decrypt path also re-checks
    ///    the turn commitment over the recovered plaintext.
    /// 3. Dispatch the recovered `Turn` to the standard `execute` path.
    ///
    /// The executor must have been configured with
    /// `with_turn_decryption_secret`; otherwise this returns a `Rejected`
    /// result.
    ///
    /// SECURITY: The agent in the recovered turn MUST match the envelope's
    /// claimed `agent` field. A mismatch is treated as a Byzantine submission
    /// and the turn is rejected. This binds the public-side fee/nonce
    /// preflight to the actual turn body.
    pub fn execute_encrypted_turn(
        &self,
        encrypted: &crate::encrypted::EncryptedTurn,
        ledger: &mut Ledger,
    ) -> TurnResult {
        // 1. Metadata consistency check (agent/conflict-set/turn-commitment
        //    bindings inside the validity proof's public inputs).
        if let Err(e) = encrypted.verify_metadata() {
            return TurnResult::Rejected {
                reason: TurnError::InvalidEffect {
                    reason: format!("encrypted turn metadata invalid: {:?}", e),
                },
                at_action: vec![],
            };
        }

        // 1b. Validity-proof (STARK) gate, when required. Closes the fee-DoS
        //     hole: an unproven encrypted blob must not be decrypted/ordered.
        //     FAIL-CLOSED while the producer is unwired (verify_stark rejects
        //     empty proof_bytes). OFF by default — see `require_validity_proof`.
        if self.require_validity_proof {
            if let Err(e) = encrypted.verify_stark() {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("encrypted turn validity proof invalid: {:?}", e),
                    },
                    at_action: vec![],
                };
            }
        }

        // 2. Decrypt with the executor's X25519 secret.
        let (secret, public) = match self.turn_decryption_keypair {
            Some(kp) => kp,
            None => {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: "executor has no turn_decryption_keypair configured; \
                                 EncryptedTurn cannot be processed"
                            .to_string(),
                    },
                    at_action: vec![],
                };
            }
        };
        let turn = match encrypted.decrypt_for_executor(&secret, &public) {
            Ok(t) => t,
            Err(e) => {
                return TurnResult::Rejected {
                    reason: TurnError::InvalidEffect {
                        reason: format!("encrypted turn decryption failed: {:?}", e),
                    },
                    at_action: vec![],
                };
            }
        };

        // 3. Agent binding: the decrypted turn's agent must equal the
        //    cleartext-side `agent` field. Otherwise the validity-proof's
        //    fee/nonce preflight was done against a different agent than
        //    the one the executor would now charge.
        if turn.agent != encrypted.agent {
            return TurnResult::Rejected {
                reason: TurnError::InvalidEffect {
                    reason: "encrypted turn agent mismatch: decrypted turn.agent != envelope.agent"
                        .to_string(),
                },
                at_action: vec![],
            };
        }

        // 4. Dispatch to the standard execution path. All the usual
        //    nullifier-set, ledger, and conservation gates apply.
        //
        // BOUNDARIES.md §5: flip the `was_encrypted` bit on the receipt
        // (cleartext-inside the executor; bound into `receipt_hash` and
        // the executor signature). External observers see only that
        // some receipt was produced via the privacy path — nothing about
        // the inner turn's content leaks through this flag.
        let result = self.execute(&turn, ledger);
        match result {
            TurnResult::Committed {
                ledger_delta,
                mut receipt,
                computrons_used,
            } => {
                receipt.was_encrypted = true;
                // Re-sign so the executor signature covers the new bit.
                // (The signature's canonical message doesn't currently include
                // `was_encrypted`, but `receipt_hash` does — and any downstream
                // verifier that recomputes `receipt_hash` would fail without
                // this resign step.)
                receipt.executor_signature = self.maybe_sign_receipt(&receipt);
                // Rebind the per-agent chain head to the post-flip hash.
                self.record_receipt_hash(receipt.agent, receipt.receipt_hash());
                TurnResult::Committed {
                    ledger_delta,
                    receipt,
                    computrons_used,
                }
            }
            other => other,
        }
    }

    /// **Canonical** encrypted-turn entry point (AUDIT-privacy.md §11.2):
    /// decrypt an `EncryptedTurn` with the supplied X25519 unsealer secret,
    /// recover the underlying `Turn`, apply it through the normal executor,
    /// and return the `TurnReceipt` (with `was_encrypted = true`).
    ///
    /// This is the production wiring node-level callers (HTTP / MCP) hit
    /// when forwarding an `EncryptedTurn` envelope. Unlike
    /// [`Self::execute_encrypted_turn`] (which mutates the executor's
    /// `turn_decryption_keypair`), this method accepts the sealer secret
    /// explicitly — useful when the secret is held in an HSM-style wrapper
    /// or when a single executor process serves multiple sealer pairs.
    ///
    /// The `sealer_secret` is the 32-byte X25519 static secret (`unsealer_secret`
    /// in `cell/src/seal.rs` terminology). The public key is recomputed from it
    /// so the decrypt path can verify the BLAKE3-key-derivation salt.
    ///
    /// # Errors
    ///
    /// Returns `TurnError::InvalidEffect { reason }` when:
    /// - the envelope's metadata fails self-consistency (`verify_metadata`),
    /// - decryption fails (wrong key / tampered ciphertext → Poly1305 MAC fail),
    /// - the decrypted `turn.agent` does not match `envelope.agent` (binding
    ///   the public-side fee/nonce preflight to the actual turn body), or
    /// - the inner turn was rejected by `execute` (insufficient fee, replayed
    ///   nullifier, broken receipt chain, etc.).
    pub fn apply_encrypted_turn(
        &self,
        encrypted: &crate::encrypted::EncryptedTurn,
        sealer_secret: &[u8; 32],
        ledger: &mut Ledger,
    ) -> Result<TurnReceipt, TurnError> {
        // 1. Metadata consistency.
        encrypted
            .verify_metadata()
            .map_err(|e| TurnError::InvalidEffect {
                reason: format!("encrypted turn metadata invalid: {:?}", e),
            })?;

        // 1b. Validity-proof (STARK) gate, when required (see
        //     `execute_encrypted_turn` for the rationale; fail-closed fee-DoS
        //     gate, OFF by default).
        if self.require_validity_proof {
            encrypted
                .verify_stark()
                .map_err(|e| TurnError::InvalidEffect {
                    reason: format!("encrypted turn validity proof invalid: {:?}", e),
                })?;
        }

        // 2. Recompute the public key from the secret and decrypt.
        let public = {
            let pk =
                x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(*sealer_secret));
            *pk.as_bytes()
        };
        let turn = encrypted
            .decrypt_for_executor(sealer_secret, &public)
            .map_err(|e| TurnError::InvalidEffect {
                reason: format!("encrypted turn decryption failed: {:?}", e),
            })?;

        // 3. Agent binding: the cleartext envelope.agent (used by the
        //    federation for fee/nonce preflight) must equal the inner
        //    turn.agent the executor would actually charge.
        if turn.agent != encrypted.agent {
            return Err(TurnError::InvalidEffect {
                reason: "encrypted turn agent mismatch: decrypted turn.agent != envelope.agent"
                    .to_string(),
            });
        }

        // 4. Apply through the standard execute path.
        match self.execute(&turn, ledger) {
            TurnResult::Committed { mut receipt, .. } => {
                receipt.was_encrypted = true;
                receipt.executor_signature = self.maybe_sign_receipt(&receipt);
                // Rebind the per-agent chain head to the post-flip hash so
                // the next turn's `previous_receipt_hash` check uses the
                // committed value.
                self.record_receipt_hash(receipt.agent, receipt.receipt_hash());
                Ok(receipt)
            }
            TurnResult::Rejected { reason, .. } => Err(reason),
            TurnResult::Expired => Err(TurnError::InvalidEffect {
                reason: "encrypted turn expired before application".to_string(),
            }),
            TurnResult::Pending => Err(TurnError::InvalidEffect {
                reason: "encrypted turn returned Pending (conditional encrypted turns \
                         are out of scope for apply_encrypted_turn)"
                    .to_string(),
            }),
        }
    }

    /// Sign `receipt.receipt_hash()` with the executor's signing key if one
    /// is configured, returning the 64-byte signature bytes for embedding in
    /// `receipt.executor_signature`. Returns `None` when no key is set —
    /// callers should leave `executor_signature` as `None` in that case.
    fn maybe_sign_receipt(&self, receipt: &TurnReceipt) -> Option<Vec<u8>> {
        let seed = self.executor_signing_key.as_ref()?;
        let sk = ed25519_dalek::SigningKey::from_bytes(seed);
        // Stage 9 R-4: sign the canonical narrow message
        // (`executor-receipt-sig-v1:` || turn_hash || pre_state || post_state ||
        // timestamp), not the broader `receipt_hash()`. This keeps the
        // executor's claim recoverable by downstream verifiers that do not yet
        // understand the v2 receipt's auxiliary fields (routing directives,
        // derivation records, emitted events, finality). See
        // `TurnReceipt::canonical_executor_signed_message`.
        let msg = receipt.canonical_executor_signed_message();
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg);
        Some(sig.to_bytes().to_vec())
    }

    /// Set the current timestamp (used for expiration and precondition checks).
    ///
    /// P2-2: rejects backwards timestamp updates. The executor's clock must be
    /// monotonically non-decreasing; a stuck/backward clock allows expired
    /// turns to succeed and breaks `valid_until` enforcement. Backward-stepping
    /// `ts` values are silently ignored (no-op).
    pub fn set_timestamp(&mut self, ts: i64) {
        if ts >= self.current_timestamp {
            self.current_timestamp = ts;
        }
        // else: silently ignore (do not allow time to go backwards).
    }

    /// The current [`crate::collapse::WitnessMode`] (Full by default).
    pub fn witness_mode(&self) -> crate::collapse::WitnessMode {
        crate::collapse::WitnessMode::from_u8(
            self.witness_mode.load(std::sync::atomic::Ordering::Relaxed),
        )
    }

    /// Set the witness mode. `&self` (atomic) so a caller holding a shared ref
    /// can flip it — e.g. enter [`WitnessMode::Symbolic`](crate::collapse::WitnessMode)
    /// for a burst of local turns, then back to `Full`.
    ///
    /// This selects ONLY whether per-turn Merkle witnesses materialize; it never
    /// changes which turns are admitted (every legality gate runs identically in
    /// both modes). In `Symbolic`, a committed receipt carries the deferred
    /// sentinel state-hash ([`crate::collapse::DEFERRED_STATE_HASH`]) and is
    /// local-only until [`crate::collapse::collapse`] materializes its witness.
    pub fn set_witness_mode(&self, mode: crate::collapse::WitnessMode) {
        self.witness_mode
            .store(mode.as_u8(), std::sync::atomic::Ordering::Relaxed);
    }

    /// `true` iff the executor is currently in
    /// [`WitnessMode::Symbolic`](crate::collapse::WitnessMode).
    pub fn is_symbolic(&self) -> bool {
        self.witness_mode().is_symbolic()
    }

    /// Get the per-agent last-known receipt hash, if any (P0-3 fix).
    ///
    /// Used by callers that need to construct a turn with the correct
    /// `previous_receipt_hash` value. Returns `None` if the agent has no
    /// committed turns on this executor.
    pub fn get_last_receipt_hash(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied()
    }

    /// **The last committed turn's exact write-set** — the cells whose serialized
    /// state that turn mutated, captured from the execution journal (see
    /// [`crate::journal::LedgerJournal::touched_cells`] and the field docs on
    /// [`Self::last_write_set`]). A durable consumer that rebuilds post-state from
    /// a per-turn change-set reads this (COMPLETE by construction) instead of a
    /// syntactic input-turn walk (which misses runtime-resolved cells). Empty
    /// before the first committed turn.
    pub fn last_write_set(&self) -> Vec<CellId> {
        self.last_write_set
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone()
    }

    /// Seed the receipt-chain head for an agent (for state recovery / loading).
    ///
    /// Use this when an executor is started against a ledger that already has
    /// history (e.g. after restart) so the receipt-chain check reflects the
    /// actual prior state. Without seeding, the first turn from an agent with
    /// pre-existing history would be rejected as `ReceiptChainMismatch`.
    pub fn set_last_receipt_hash(&self, agent: CellId, hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, hash);
    }

    /// Clear the per-agent receipt-chain head (for tests and resets).
    pub fn reset_receipt_chain(&self) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
    }

    /// Check whether a cell is frozen for migration (P0-4 fix).
    ///
    /// Returns `Err(TurnError::CellFrozen { cell })` if the cell is in
    /// `MigrationState::Frozen` or `AwaitingReceipt`; `Ok(())` otherwise.
    /// Called near the top of every turn-execution path that mutates state.
    fn check_not_frozen(&self, cell: &CellId) -> Result<(), TurnError> {
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(cell)
        {
            Err(TurnError::CellFrozen { cell: *cell })
        } else {
            Ok(())
        }
    }

    /// Verify the agent's `previous_receipt_hash` matches the executor's
    /// stored head for that agent (P0-3 fix).
    fn check_previous_receipt_hash(
        &self,
        agent: &CellId,
        claimed: Option<[u8; 32]>,
    ) -> Result<(), TurnError> {
        let stored = self
            .last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(agent)
            .copied();
        if stored == claimed {
            Ok(())
        } else {
            Err(TurnError::ReceiptChainMismatch {
                expected: stored,
                got: claimed,
            })
        }
    }

    /// Record a receipt as the new chain-head for the agent.
    fn record_receipt_hash(&self, agent: CellId, receipt_hash: [u8; 32]) {
        self.last_receipt_hash
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(agent, receipt_hash);
    }

    /// The per-cell PROVENANCE chain head — `build_atomic_per_cell_receipt`'s
    /// `previous_receipt_hash` source + any per-cell receipt-history walk. Advances
    /// for every touched cell, unlike `last_receipt_hash` (agent-only authority).
    fn get_per_cell_head(&self, cell: &CellId) -> Option<[u8; 32]> {
        self.per_cell_receipt_head
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(cell)
            .copied()
    }

    /// Advance a cell's per-cell provenance chain head (every touched cell).
    fn record_per_cell_head(&self, cell: CellId, receipt_hash: [u8; 32]) {
        self.per_cell_receipt_head
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(cell, receipt_hash);
    }

    /// Set the current block height (used for network preconditions).
    pub fn set_block_height(&mut self, height: u64) {
        self.block_height = height;
    }

    /// Set the block proposer cell (receives 50% of fees).
    ///
    /// When set, 50% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the proposer share is burned instead.
    pub fn set_proposer_cell(&mut self, cell_id: CellId) {
        self.proposer_cell = Some(cell_id);
    }

    /// Set the federation treasury cell (receives 30% of fees).
    ///
    /// When set, 30% of each turn's fee is credited to this cell's balance
    /// after successful execution. If the cell does not exist in the ledger at
    /// execution time, the treasury share is burned instead.
    pub fn set_treasury_cell(&mut self, cell_id: CellId) {
        self.treasury_cell = Some(cell_id);
    }

    /// THE EPOCH §5 ("fees as moves"): set the FEE WELL cell. Every fee
    /// share that would otherwise be burned (the 20% remainder, rounding
    /// dust, unconfigured proposer/treasury shares, and the whole fee on the
    /// atomic paths) is MOVED here instead, making every committed turn's
    /// value delta exactly zero. Genesis configures this on the deployed
    /// chain.
    pub fn set_fee_well_cell(&mut self, cell_id: CellId) {
        self.fee_well_cell = Some(cell_id);
    }

    /// THE EPOCH §5 ("burn as issuer-move"): register the ISSUER WELL cell
    /// for an asset (`token_id`). A `Burn` targeting a cell of this asset is
    /// executed as a MOVE target→well — the well, carrying −supply, is
    /// credited back toward zero (the Lean `burnA` dispatch) — so burn stops
    /// being a non-conserving verb for registered assets.
    pub fn register_issuer_well(&mut self, token_id: [u8; 32], well: CellId) {
        self.issuer_wells.insert(token_id, well);
    }

    /// Deterministically derive the ISSUER WELL cell for an asset (`token_id`),
    /// generalizing the genesis default-asset well (`node/src/genesis.rs`) to
    /// EVERY asset. The well's signing key is a domain-separated derivation
    /// over the asset, and its id is the ordinary content-addressed
    /// `CellId::derive_raw(pubkey, token_id)` — so the well is a real signed
    /// cell in the SAME asset class as its holders (its `token_id` matches), a
    /// negative-capable `−supply` account.
    ///
    /// SUPPLY-MODEL Stage 1 (`docs/SUPPLY-MODEL.md`): this is the lazy
    /// per-asset well that makes burn a CONSERVING move (holder→well) for any
    /// asset, not just the registered default — closing the
    /// non-conserving-`destroy` hole. The genesis well registration (via
    /// [`register_issuer_well`](Self::register_issuer_well)) still takes
    /// precedence as an explicit override; this derivation is the fallback for
    /// assets with no registered well.
    pub(super) fn derive_issuer_well(token_id: &[u8; 32]) -> ([u8; 32], CellId) {
        // Domain-separated key over the asset id. Distinct domain from the
        // genesis devnet well so a lazily-derived well never collides with the
        // genesis-registered one (which uses `dregg-devnet-issuer-well-key-v1`
        // over `b"genesis"` and is supplied explicitly via the override map).
        let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
        let well_id = CellId::derive_raw(&well_pubkey, token_id);
        (well_pubkey, well_id)
    }

    /// Resolve the ISSUER WELL for a cell's asset (`token_id`): the explicitly
    /// registered well if one exists (genesis override), else the deterministic
    /// lazily-derived per-asset well. Returns `None` only when the cell itself
    /// is absent from the ledger (no asset to resolve).
    ///
    /// SUPPLY-MODEL Stage 1: EVERY asset now resolves a well, so a burn is
    /// always a conserving holder→well move — the bare-debit (`Σδ≠0`) path is
    /// retired.
    pub(super) fn issuer_well_for(&self, ledger: &Ledger, cell: &CellId) -> Option<CellId> {
        let token_id = *ledger.get(cell)?.token_id();
        Some(
            self.issuer_wells
                .get(&token_id)
                .copied()
                .unwrap_or_else(|| Self::derive_issuer_well(&token_id).1),
        )
    }

    /// Configure epoch-based computron minting to prevent deflationary deadlock.
    ///
    /// When set, the executor will mint new computrons to the treasury cell at
    /// epoch boundaries. Call [`apply_epoch_minting`](Self::apply_epoch_minting)
    /// at each block to trigger minting when appropriate.
    ///
    /// # Arguments
    ///
    /// * `minter` - The configured epoch minter with policy parameters.
    pub fn set_epoch_minter(&mut self, minter: crate::economics::EpochMinter) {
        self.epoch_minter = Some(std::cell::RefCell::new(minter));
    }

    /// Apply epoch-based minting if the current block height crosses an epoch boundary.
    ///
    /// Call this once per block (typically at block start, before processing turns).
    /// Returns `Some(MintResult)` if computrons were minted, `None` otherwise.
    ///
    /// This prevents the deflationary death spiral: since 20% of every fee is
    /// burned and no new supply is created, the system would eventually run out
    /// of computrons. Epoch minting provides controlled issuance to the treasury,
    /// which distributes via governance (staking rewards, grants, fee subsidies).
    pub fn apply_epoch_minting(
        &self,
        ledger: &mut dregg_cell::Ledger,
    ) -> Option<crate::economics::MintResult> {
        let minter_cell = self.epoch_minter.as_ref()?;
        let mut minter = minter_cell.borrow_mut();
        minter.maybe_mint(ledger, self.block_height)
    }

    /// Execute a conditional turn by first resolving its condition.
    ///
    /// This checks:
    /// 1. Whether the timeout has been exceeded (returns `TurnResult::Expired`)
    /// 2. Whether the proof satisfies the condition
    /// 3. If satisfied, executes the underlying turn normally
    ///
    /// No fee is charged if the turn expires or the condition is not met.
    pub fn execute_conditional(
        &self,
        conditional: &crate::conditional::ConditionalTurn,
        proof: &crate::conditional::ConditionProof,
        current_height: u64,
        trusted_roots: &[crate::conditional::TrustedRoot],
        max_root_age: u64,
        used_proof_hashes: &mut std::collections::HashSet<[u8; 32]>,
        ledger: &mut Ledger,
    ) -> TurnResult {
        // Check timeout.
        if current_height > conditional.timeout_height {
            return TurnResult::Expired;
        }

        // Resolve condition.
        match crate::conditional::resolve_condition(
            &conditional.condition,
            proof,
            current_height,
            conditional.timeout_height,
            trusted_roots,
            max_root_age,
            used_proof_hashes,
            &self.trusted_destination_keys,
        ) {
            crate::conditional::ConditionalResult::Resolved => {
                let result = self.execute(&conditional.turn, ledger);
                // On successful execution, refund the conditional deposit to the agent.
                if let TurnResult::Committed { .. } = &result {
                    if conditional.deposit_amount > 0 {
                        if let Some(cell) = ledger.get_mut(&conditional.turn.agent) {
                            // Overflow-checked credit (signed balances).
                            let _ = cell.state.credit_balance(conditional.deposit_amount);
                        }
                    }
                }
                result
            }
            crate::conditional::ConditionalResult::Expired => TurnResult::Expired,
            crate::conditional::ConditionalResult::Pending => TurnResult::Pending,
            crate::conditional::ConditionalResult::InvalidProof(e) => TurnResult::Rejected {
                reason: TurnError::ConditionNotMet(e),
                at_action: vec![],
            },
        }
    }

    /// Set the trusted federation roots for cross-federation note bridging.
    ///
    /// Only portable note proofs whose source_root matches one of these roots
    /// will be accepted. Call this to configure which remote federations this
    /// executor trusts for bridge mints.
    pub fn set_trusted_federation_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.trusted_federation_roots = roots;
    }

    /// Add a single trusted federation root.
    pub fn add_trusted_federation_root(&mut self, root: AttestedRoot) {
        self.trusted_federation_roots.push(root);
    }

    /// Set the local federation identity for cross-federation bridge verification.
    pub fn set_local_federation_id(&mut self, id: [u8; 32]) {
        self.local_federation_id = id;
    }

    /// Set the trusted destination federation keys for bridge receipt verification.
    ///
    /// These Ed25519 public keys are used during BridgeFinalize to verify that a
    /// receipt was signed by a legitimate destination federation.
    pub fn set_trusted_destination_keys(&mut self, keys: Vec<[u8; 32]>) {
        self.trusted_destination_keys = keys;
    }

    // ─── Unified Lace Aliases ──────────────────────────────────────────────
    //
    // In the unified blocklace model, a "federation" is a reference group (GroupId).
    // These aliases provide forward-compatible naming.

    /// Alias for [`set_trusted_federation_roots`](Self::set_trusted_federation_roots).
    /// In the unified lace model, "federation roots" are "group roots".
    pub fn set_trusted_group_roots(&mut self, roots: Vec<AttestedRoot>) {
        self.set_trusted_federation_roots(roots);
    }

    /// Alias for [`add_trusted_federation_root`](Self::add_trusted_federation_root).
    pub fn add_trusted_group_root(&mut self, root: AttestedRoot) {
        self.add_trusted_federation_root(root);
    }

    /// Alias for [`set_local_federation_id`](Self::set_local_federation_id).
    /// In the unified lace model, the "local federation ID" is the local group ID.
    pub fn set_local_group_id(&mut self, id: [u8; 32]) {
        self.set_local_federation_id(id);
    }

    /// Add a single trusted destination federation key.
    pub fn add_trusted_destination_key(&mut self, key: [u8; 32]) {
        self.trusted_destination_keys.push(key);
    }

    /// Set the revocation channel set for capability exercise checks.
    ///
    /// When present, the executor verifies that capabilities used via
    /// `ExerciseViaCapability` and delegation access checks are not gated
    /// by a tripped revocation channel.
    pub fn set_revocation_channels(&mut self, channels: RevocationChannelSet) {
        self.revocation_channels = Some(channels);
    }

    /// Set the program registry for custom cell program verification.
    ///
    /// When a sovereign cell has a `verification_key_hash` in its registration,
    /// proof-carrying turns are verified against the deployed program instead of
    /// the default `EffectVmAir`.
    pub fn set_program_registry(&mut self, registry: ProgramRegistry) {
        self.program_registry = registry;
    }

    /// Get a mutable reference to the program registry (for deploying programs).
    pub fn program_registry_mut(&mut self) -> &mut ProgramRegistry {
        &mut self.program_registry
    }

    /// Get a mutable reference to the factory registry (for deploying factories).
    pub fn factory_registry_mut(&mut self) -> std::cell::RefMut<'_, dregg_cell::FactoryRegistry> {
        self.factory_registry.borrow_mut()
    }

    /// Deploy a factory into the executor's registry.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        self.factory_registry.borrow_mut().deploy(descriptor)
    }
}

// ─── Decomposed Implementation Modules ──────────────────────────────────────

mod apply;
mod authorize;
mod execute;
mod execute_tree;
mod finalize;
mod proof_verify;

// Concurrency-safe committed bridge mirror-ledger (`bridge_ledger.rs`):
// `lock_id`-as-nullifier + a committed supply cell, gated inside one atomic
// mint, closing the multi-relayer double-mint gap.
pub mod bridge_ledger;
pub use bridge_ledger::{
    BridgeEscrowReceipt, BridgeEscrowRecord, BridgeMintError, BridgeMintReceipt, BridgeMintRequest,
    escrow_nullifier_for, new_mirror_ledger_cell, read_supply,
};

// MEASUREMENT-ONLY: env-gated (`DREGG_TURN_PROFILE=1`) per-turn phase profiler.
mod turn_profile;
pub use proof_verify::{SovereignCohortChain, SovereignCohortLeg};
pub use turn_profile::dump as turn_profile_dump;

// ─── Pipeline Execution ──────────────────────────────────────────────────────

mod pipeline;
pub use pipeline::{
    ResolutionTable, execute_pipeline, execute_pipeline_result, resolve_eventual_ref,
    resolve_output_ref,
};

mod atomic;
pub use atomic::{
    AtomicProofEntry, AtomicSovereignTurn, AtomicTurnError, MixedAtomicResult, MixedAtomicTurn,
};
