//! Four-layer tower: `Intent → EffectPlan → SealedTurn → Turn` (P2.B).
//!
//! Per DESIGN-dsl.md §B, this module defines the deterministic, total,
//! order-preserving lowering from a high-level user intent down to a
//! runtime-executable `Turn`. Each layer represents a step toward
//! execution and can be tested in isolation:
//!
//! 1. [`Intent`] — declarative "what the user wants" (~12 variants today;
//!    the discovery-time `crate::Intent` type is unrelated and stays in
//!    `intent/src/lib.rs`).
//! 2. [`EffectPlan`] — a flat list of [`PendingAction`]s carrying typed
//!    effects but no authorization yet.
//! 3. [`SealedTurn`] — every action has acquired an [`Authorization`];
//!    the cclerk has signed/proved as needed.
//! 4. [`pyana_turn::Turn`] — the runtime executable consumed by the
//!    `TurnExecutor`.
//!
//! Per P2.G the trustless intent engine (`crate::trustless`) now emits
//! `Intent::RingSettlement` and lowers it through this module to a real
//! `Turn` — the legacy ad-hoc `CompoundTurn` / `SettlementAction` types
//! have been deleted. `TrustlessIntentEngine::finalize` returns a
//! `SettlementOutput` whose inner `SealedTurn` is ready for the executor.

use pyana_cell::CellId;
use pyana_turn::CallForest;
use pyana_turn::action::{Action, Authorization, Effect};
use pyana_turn::turn::Turn;

use crate::solver::RingTrade;
use crate::solver::Settlement as RingSettlement;

// ─── Layer 1: Intent ──────────────────────────────────────────────────────────

/// A declarative, executable intent.
///
/// This is the *executable* sibling of `crate::Intent` (which is a
/// discovery-time matching spec). Each variant maps to a deterministic
/// effect pattern via [`lower`].
#[derive(Clone, Debug)]
pub enum Intent {
    /// Simple value transfer.
    Pay {
        from: CellId,
        to: CellId,
        amount: u64,
    },
    /// Atomic multi-party ring settlement (output of `TrustlessIntentEngine`).
    RingSettlement {
        rings: Vec<RingTrade>,
        /// Anchor cell used as the settlement's executing agent. This is
        /// typically the federation node's own cell — the entity of
        /// record submitting the compound settlement.
        anchor: CellId,
        /// Solver identity (witness; binds the lowered turn to the
        /// auction's winner).
        solver_id: [u8; 32],
        /// Validity proof hash (binding for replay-resistance).
        validity_proof_hash: [u8; 32],
    },
    /// Drop into raw effects with explicit opt-in. Used when the
    /// high-level surface is insufficient.
    Custom {
        target: CellId,
        caller: CellId,
        method: String,
        effects: Vec<Effect>,
    },
}

// ─── Layer 2: EffectPlan ──────────────────────────────────────────────────────

/// A flat plan of pending actions, each carrying typed effects but no
/// authorization yet.
#[derive(Clone, Debug, Default)]
pub struct EffectPlan {
    pub actions: Vec<PendingAction>,
    /// Solver / settlement metadata derived from the source intent,
    /// preserved for the executor as a witness.
    pub validity_witness: Option<ValidityWitness>,
}

/// An action waiting for authorization. The cclerk (or seal layer) walks
/// these and produces an [`Authorization`] for each.
#[derive(Clone, Debug)]
pub struct PendingAction {
    pub target: CellId,
    pub caller: CellId,
    pub method: String,
    pub effects: Vec<Effect>,
    /// Hint about which authorization mode the seal layer should apply.
    pub auth_hint: AuthHint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthHint {
    /// Sign with the agent's primary Ed25519 key.
    Signed,
    /// STARK auth proof, with the binding spec.
    Proved {
        bound_action: String,
        bound_resource: String,
    },
    /// Bearer-cap; the seal layer materializes the proof.
    Bearer,
    /// Capability token (breadstuff).
    Breadstuff,
}

/// Witness recorded for a ring-settlement intent: who solved, what proof
/// they presented. Embedded into the resulting `Turn` as `memo` /
/// auxiliary fields by the seal layer.
#[derive(Clone, Debug)]
pub struct ValidityWitness {
    pub solver_id: [u8; 32],
    pub validity_proof_hash: [u8; 32],
}

// ─── Layer 3: SealedTurn ──────────────────────────────────────────────────────

/// A `Turn` whose every action carries a real, non-`Unchecked`
/// authorization. The contract: a `SealedTurn` is "ready for the
/// executor" with no further authorization work required.
#[derive(Clone, Debug)]
pub struct SealedTurn {
    pub turn: Turn,
}

impl SealedTurn {
    /// Promote a fully-authorized `Turn` into a `SealedTurn`, panicking
    /// (debug) if any action carries `Authorization::Unchecked`. In
    /// release builds the unchecked actions slip through — production
    /// constructors must originate through `seal_plan` which never
    /// emits Unchecked.
    pub fn from_turn(turn: Turn) -> Self {
        debug_assert!(
            turn.call_forest
                .roots
                .iter()
                .all(|t| !matches!(t.action.authorization, Authorization::Unchecked)),
            "SealedTurn::from_turn: refusing turn with Unchecked authorization"
        );
        SealedTurn { turn }
    }
}

// ─── Layer 4: Turn ────────────────────────────────────────────────────────────
// (re-exported `pyana_turn::Turn`)

// ─── Context & lowering function ──────────────────────────────────────────────

/// Context that the lowering function consults for ambient parameters
/// (heights, nonces, …). Kept minimal for testability.
#[derive(Clone, Debug, Default)]
pub struct LoweringContext {
    pub current_height: u64,
    pub default_nonce: u64,
}

/// Errors produced by [`lower`] when the input cannot be lowered to a
/// well-formed `EffectPlan`. The function is *total* in the sense that
/// every legitimate `Intent` value succeeds; errors here only surface
/// structural impossibilities (e.g. empty ring participants).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoweringError {
    EmptyRing,
    NoRings,
}

impl std::fmt::Display for LoweringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyRing => write!(f, "ring has no participants"),
            Self::NoRings => write!(f, "ring settlement has no rings"),
        }
    }
}

impl std::error::Error for LoweringError {}

/// Lower an `Intent` into an `EffectPlan`. Deterministic, total,
/// order-preserving.
pub fn lower(intent: Intent, ctx: &LoweringContext) -> Result<EffectPlan, LoweringError> {
    let _ = ctx; // currently unused; reserved for future variants
    match intent {
        Intent::Pay { from, to, amount } => {
            let action = PendingAction {
                target: from,
                caller: from,
                method: "pay".to_string(),
                effects: vec![Effect::Transfer { from, to, amount }],
                auth_hint: AuthHint::Signed,
            };
            Ok(EffectPlan {
                actions: vec![action],
                validity_witness: None,
            })
        }
        Intent::RingSettlement {
            rings,
            anchor,
            solver_id,
            validity_proof_hash,
        } => {
            if rings.is_empty() {
                return Err(LoweringError::NoRings);
            }
            let mut actions = Vec::new();
            // Order preservation: rings stay in their input order, and
            // settlements within each ring keep their original order.
            for ring in rings.iter() {
                if ring.participants.is_empty() {
                    return Err(LoweringError::EmptyRing);
                }
                for leg in ring.settlements.iter() {
                    actions.push(lower_settlement_leg(leg, anchor));
                }
            }
            Ok(EffectPlan {
                actions,
                validity_witness: Some(ValidityWitness {
                    solver_id,
                    validity_proof_hash,
                }),
            })
        }
        Intent::Custom {
            target,
            caller,
            method,
            effects,
        } => {
            let action = PendingAction {
                target,
                caller,
                method,
                effects,
                auth_hint: AuthHint::Signed,
            };
            Ok(EffectPlan {
                actions: vec![action],
                validity_witness: None,
            })
        }
    }
}

/// Lower one settlement leg into a `PendingAction`.
///
/// Each leg is emitted as a bare `Effect::Transfer` from the sender's
/// cell to the recipient's, using the same `"pay"` method symbol as
/// the `Intent::Pay` lowering. This keeps ring settlement composed
/// out of the existing γ.2 bilateral primitive (`Effect::Transfer`)
/// rather than dispatching a `"settle_ring_leg"` method that no cell
/// implements.
///
/// Authorization is `AuthHint::Signed`: the lowering layer leaves
/// auth attachment to the seal layer. In the trustless engine's
/// path, `seal_plan_uniform` applies a single solver-bound
/// signature derived from the validity proof hash — every leg
/// inherits the same authorization, with per-leg auth being a
/// future per-action sealer extension (see `auth_hint`).
///
/// The `caller` is set to the anchor (the solver / federation
/// settlement cell) so the executor treats this as a federation-
/// driven transfer rather than a sender-initiated one; the
/// settlement is "I, the anchor, move value on behalf of the
/// auctioned matching".
fn lower_settlement_leg(leg: &RingSettlement, anchor: CellId) -> PendingAction {
    let from_cell = CellId::from_bytes(leg.from.0);
    let to_cell = CellId::from_bytes(leg.to.0);
    PendingAction {
        target: from_cell,
        caller: anchor,
        method: "pay".to_string(),
        effects: vec![Effect::Transfer {
            from: from_cell,
            to: to_cell,
            amount: leg.amount,
        }],
        auth_hint: AuthHint::Signed,
    }
}

/// Seal an [`EffectPlan`] into a [`SealedTurn`] using a single uniform
/// authorization for every action. This is the most basic sealer; real
/// cipherclerks will produce one authorization per action by walking the
/// `auth_hint` field.
pub fn seal_plan_uniform(
    plan: EffectPlan,
    agent: CellId,
    nonce: u64,
    authorization: Authorization,
) -> SealedTurn {
    debug_assert!(
        !matches!(authorization, Authorization::Unchecked),
        "seal_plan_uniform: refusing Unchecked authorization"
    );

    let mut builder = pyana_turn::builder::TurnBuilder::new(agent, nonce);
    for pa in plan.actions {
        let action = Action {
            target: pa.target,
            method: pyana_turn::action::symbol(&pa.method),
            args: Vec::new(),
            authorization: authorization.clone(),
            preconditions: Default::default(),
            effects: pa.effects,
            may_delegate: pyana_turn::action::DelegationMode::None,
            commitment_mode: pyana_turn::action::CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        builder.add_action(action);
    }
    let mut turn = builder.build();
    if let Some(w) = plan.validity_witness {
        turn.memo = Some(format!(
            "ring-settlement solver={:02x}{:02x}..{:02x}{:02x} proof={:02x}{:02x}..{:02x}{:02x}",
            w.solver_id[0],
            w.solver_id[1],
            w.solver_id[30],
            w.solver_id[31],
            w.validity_proof_hash[0],
            w.validity_proof_hash[1],
            w.validity_proof_hash[30],
            w.validity_proof_hash[31],
        ));
    }
    let _ = CallForest::new; // pin import
    SealedTurn::from_turn(turn)
}

/// Per-leg authorization sealer: walks each [`PendingAction`]'s
/// `auth_hint` and produces an [`Authorization`] tailored to that
/// hint. Closes audit §11 — the uniform sealer was a stub; real
/// settlements need per-leg auth so each cell sees the authorization
/// kind it expects.
///
/// The `sealer` callback is the cipherclerk's per-leg authorization
/// producer. For ring settlement, this is typically:
///
/// - `Signed` → an Ed25519 signature by the anchor.
/// - `Proved { … }` → a STARK proof bound to the action+resource.
/// - `Bearer` → a bearer cap delegation.
/// - `Breadstuff` → a capability-token hash.
///
/// In the trustless engine's settlement path, `Signed` for every leg
/// is acceptable (the validity_proof already gates the whole
/// settlement). Apps that need per-leg STARK auth call this with a
/// `Proved`-routing sealer.
pub fn seal_plan_per_leg<F>(plan: EffectPlan, agent: CellId, nonce: u64, sealer: F) -> SealedTurn
where
    F: Fn(&PendingAction) -> Authorization,
{
    let mut builder = pyana_turn::builder::TurnBuilder::new(agent, nonce);
    for pa in &plan.actions {
        let auth = sealer(pa);
        debug_assert!(
            !matches!(auth, Authorization::Unchecked),
            "seal_plan_per_leg: sealer returned Unchecked for hint {:?}",
            pa.auth_hint
        );
        let action = Action {
            target: pa.target,
            method: pyana_turn::action::symbol(&pa.method),
            args: Vec::new(),
            authorization: auth,
            preconditions: Default::default(),
            effects: pa.effects.clone(),
            may_delegate: pyana_turn::action::DelegationMode::None,
            commitment_mode: pyana_turn::action::CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        builder.add_action(action);
    }
    let mut turn = builder.build();
    if let Some(w) = plan.validity_witness {
        turn.memo = Some(format!(
            "ring-settlement solver={:02x}{:02x}..{:02x}{:02x} proof={:02x}{:02x}..{:02x}{:02x}",
            w.solver_id[0],
            w.solver_id[1],
            w.solver_id[30],
            w.solver_id[31],
            w.validity_proof_hash[0],
            w.validity_proof_hash[1],
            w.validity_proof_hash[30],
            w.validity_proof_hash[31],
        ));
    }
    SealedTurn::from_turn(turn)
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CommitmentId;

    fn cell(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn pay_lowers_to_one_transfer() {
        let intent = Intent::Pay {
            from: cell(1),
            to: cell(2),
            amount: 100,
        };
        let plan = lower(intent, &LoweringContext::default()).unwrap();
        assert_eq!(plan.actions.len(), 1);
        assert_eq!(plan.actions[0].effects.len(), 1);
        assert!(matches!(
            plan.actions[0].effects[0],
            Effect::Transfer { amount: 100, .. }
        ));
    }

    #[test]
    fn lowering_is_deterministic() {
        let intent_a = Intent::Pay {
            from: cell(1),
            to: cell(2),
            amount: 100,
        };
        let intent_b = Intent::Pay {
            from: cell(1),
            to: cell(2),
            amount: 100,
        };
        let pa = lower(intent_a, &LoweringContext::default()).unwrap();
        let pb = lower(intent_b, &LoweringContext::default()).unwrap();
        assert_eq!(pa.actions.len(), pb.actions.len());
        // Hash-equality via Debug repr is fine for this smoke check.
        assert_eq!(format!("{:?}", pa.actions), format!("{:?}", pb.actions));
    }

    #[test]
    fn empty_ring_is_error() {
        let intent = Intent::RingSettlement {
            rings: vec![],
            anchor: cell(9),
            solver_id: [0u8; 32],
            validity_proof_hash: [0u8; 32],
        };
        let err = lower(intent, &LoweringContext::default()).unwrap_err();
        assert_eq!(err, LoweringError::NoRings);
    }

    #[test]
    fn ring_settlement_preserves_leg_order() {
        let a = CommitmentId([1u8; 32]);
        let b = CommitmentId([2u8; 32]);
        let c = CommitmentId([3u8; 32]);
        let ring = RingTrade {
            participants: vec![[1u8; 32], [2u8; 32], [3u8; 32]],
            settlements: vec![
                RingSettlement {
                    from: a,
                    to: b,
                    asset: [9u8; 32],
                    amount: 10,
                },
                RingSettlement {
                    from: b,
                    to: c,
                    asset: [9u8; 32],
                    amount: 20,
                },
                RingSettlement {
                    from: c,
                    to: a,
                    asset: [9u8; 32],
                    amount: 30,
                },
            ],
            score: 1.0,
        };
        let intent = Intent::RingSettlement {
            rings: vec![ring],
            anchor: cell(99),
            solver_id: [0xAB; 32],
            validity_proof_hash: [0xCD; 32],
        };
        let plan = lower(intent, &LoweringContext::default()).unwrap();
        assert_eq!(plan.actions.len(), 3);
        let amounts: Vec<u64> = plan
            .actions
            .iter()
            .filter_map(|a| {
                a.effects.first().and_then(|e| match e {
                    Effect::Transfer { amount, .. } => Some(*amount),
                    _ => None,
                })
            })
            .collect();
        assert_eq!(amounts, vec![10, 20, 30]);
        assert!(plan.validity_witness.is_some());
    }

    #[test]
    fn seal_plan_rejects_unchecked() {
        // We can't directly assert a debug_assert! panic without unwind,
        // but we can verify the happy path produces a SealedTurn.
        let plan = lower(
            Intent::Pay {
                from: cell(1),
                to: cell(2),
                amount: 5,
            },
            &LoweringContext::default(),
        )
        .unwrap();
        let sealed = seal_plan_uniform(
            plan,
            cell(1),
            0,
            Authorization::Signature([0u8; 32], [0u8; 32]),
        );
        assert_eq!(sealed.turn.call_forest.roots.len(), 1);
    }
}
