//! Faceted capabilities: E-language restricted object views.
//!
//! In E, a facet is a restricted view of an object that only exposes a subset
//! of the object's interface. In pyana, this is implemented as a bitmask on a
//! capability: when exercising a capability via `ExerciseViaCapability`, the
//! executor checks that every inner effect's kind is permitted by the
//! capability's facet mask.
//!
//! # Design
//!
//! Each effect type maps to a single bit in the mask. A capability with
//! `allowed_effects = Some(mask)` restricts the holder to only those effect
//! types whose bit is set. `None` or `Some(EFFECT_ALL)` means unrestricted.
//!
//! Facets compose with attenuation: when delegating a faceted capability, the
//! child's mask must be a subset (bitwise) of the parent's mask. This enforces
//! the E invariant that authority can only be narrowed, never amplified.
//!
//! # Predefined Facets
//!
//! - `FACET_READ_ONLY`: Only emit events (observation without mutation)
//! - `FACET_TRANSFER_ONLY`: Only send value from the target cell
//! - `FACET_STATE_WRITER`: Set fields + emit events
//! - `FACET_ADMIN`: Permission and key management only

use serde::{Deserialize, Serialize};

use crate::id::CellId;

/// Bitmask identifying which effect types a faceted capability permits.
pub type EffectMask = u32;

// ─── Effect kind bits ────────────────────────────────────────────────────────
// Each bit corresponds to a category of effects that can be independently permitted.

pub const EFFECT_SET_FIELD: EffectMask = 1 << 0;
pub const EFFECT_TRANSFER: EffectMask = 1 << 1;
pub const EFFECT_GRANT_CAPABILITY: EffectMask = 1 << 2;
pub const EFFECT_REVOKE_CAPABILITY: EffectMask = 1 << 3;
pub const EFFECT_EMIT_EVENT: EffectMask = 1 << 4;
pub const EFFECT_INCREMENT_NONCE: EffectMask = 1 << 5;
pub const EFFECT_CREATE_CELL: EffectMask = 1 << 6;
pub const EFFECT_SET_PERMISSIONS: EffectMask = 1 << 7;
pub const EFFECT_SET_VERIFICATION_KEY: EffectMask = 1 << 8;
pub const EFFECT_NOTE_SPEND: EffectMask = 1 << 9;
pub const EFFECT_NOTE_CREATE: EffectMask = 1 << 10;
pub const EFFECT_SEAL_OPS: EffectMask = 1 << 11;
pub const EFFECT_BRIDGE_OPS: EffectMask = 1 << 12;
pub const EFFECT_INTRODUCE: EffectMask = 1 << 13;
pub const EFFECT_OBLIGATION_OPS: EffectMask = 1 << 14;
pub const EFFECT_ESCROW_OPS: EffectMask = 1 << 15;
pub const EFFECT_DELEGATION_OPS: EffectMask = 1 << 16;
pub const EFFECT_SOVEREIGN_OPS: EffectMask = 1 << 17;
pub const EFFECT_QUEUE_OPS: EffectMask = 1 << 18;

/// All effect kinds permitted (equivalent to no restriction).
pub const EFFECT_ALL: EffectMask = 0xFFFF_FFFF;

// ─── Predefined facet masks ─────────────────────────────────────────────────

/// Read-only facet: only allows emitting events (observation without mutation).
pub const FACET_READ_ONLY: EffectMask = EFFECT_EMIT_EVENT;

/// Transfer-only facet: only allows sending value from the target cell.
pub const FACET_TRANSFER_ONLY: EffectMask = EFFECT_TRANSFER;

/// State-writer facet: allows setting fields and emitting events.
pub const FACET_STATE_WRITER: EffectMask = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;

/// Admin facet: allows permission and key management.
pub const FACET_ADMIN: EffectMask = EFFECT_SET_PERMISSIONS | EFFECT_SET_VERIFICATION_KEY;

/// Full delegation facet: grant/revoke capabilities + introduce.
pub const FACET_DELEGATOR: EffectMask =
    EFFECT_GRANT_CAPABILITY | EFFECT_REVOKE_CAPABILITY | EFFECT_INTRODUCE;

// ─── Facet validation ───────────────────────────────────────────────────────

/// Check whether `child_mask` is a valid attenuation of `parent_mask`.
///
/// Returns true if the child mask is a subset of the parent mask (no bits
/// enabled that the parent doesn't have). This enforces the E invariant:
/// facets can only restrict, never amplify.
pub fn is_facet_attenuation(parent_mask: EffectMask, child_mask: EffectMask) -> bool {
    child_mask & parent_mask == child_mask
}

/// Check whether a specific effect kind bit is permitted by a mask.
///
/// If `mask` is `None` or `EFFECT_ALL`, all effects are permitted.
pub fn is_effect_permitted(mask: Option<EffectMask>, effect_bit: EffectMask) -> bool {
    match mask {
        None => true,
        Some(0) => true, // zero mask = unrestricted (backward compat)
        Some(m) => effect_bit & m != 0,
    }
}

/// Human-readable description of which effect kinds are permitted by a mask.
pub fn describe_mask(mask: EffectMask) -> Vec<&'static str> {
    let mut names = Vec::new();
    if mask & EFFECT_SET_FIELD != 0 {
        names.push("SetField");
    }
    if mask & EFFECT_TRANSFER != 0 {
        names.push("Transfer");
    }
    if mask & EFFECT_GRANT_CAPABILITY != 0 {
        names.push("GrantCapability");
    }
    if mask & EFFECT_REVOKE_CAPABILITY != 0 {
        names.push("RevokeCapability");
    }
    if mask & EFFECT_EMIT_EVENT != 0 {
        names.push("EmitEvent");
    }
    if mask & EFFECT_INCREMENT_NONCE != 0 {
        names.push("IncrementNonce");
    }
    if mask & EFFECT_CREATE_CELL != 0 {
        names.push("CreateCell");
    }
    if mask & EFFECT_SET_PERMISSIONS != 0 {
        names.push("SetPermissions");
    }
    if mask & EFFECT_SET_VERIFICATION_KEY != 0 {
        names.push("SetVerificationKey");
    }
    if mask & EFFECT_NOTE_SPEND != 0 {
        names.push("NoteSpend");
    }
    if mask & EFFECT_NOTE_CREATE != 0 {
        names.push("NoteCreate");
    }
    if mask & EFFECT_SEAL_OPS != 0 {
        names.push("SealOps");
    }
    if mask & EFFECT_BRIDGE_OPS != 0 {
        names.push("BridgeOps");
    }
    if mask & EFFECT_INTRODUCE != 0 {
        names.push("Introduce");
    }
    if mask & EFFECT_OBLIGATION_OPS != 0 {
        names.push("ObligationOps");
    }
    if mask & EFFECT_ESCROW_OPS != 0 {
        names.push("EscrowOps");
    }
    if mask & EFFECT_DELEGATION_OPS != 0 {
        names.push("DelegationOps");
    }
    if mask & EFFECT_SOVEREIGN_OPS != 0 {
        names.push("SovereignOps");
    }
    names
}

// ─── Extended Facets (parameterized constraints) ───────────────────────────────

/// Extended facet with parameterized constraints beyond the type-level bitmask.
///
/// While [`EffectMask`] restricts which effect TYPES are permitted (e.g., "can Transfer"),
/// [`ExtendedFacet`] adds fine-grained constraints (e.g., "can Transfer up to 100",
/// "can only Transfer to cell X", "max 5 transfers per epoch").
///
/// This implements the principle of least authority more precisely: a facet can
/// express exactly the minimum permissions needed for a delegated capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExtendedFacet {
    /// Base effect type mask (existing coarse-grained restriction).
    pub effect_mask: EffectMask,
    /// Optional per-effect constraints that further restrict permitted operations.
    /// If empty, only the effect_mask is enforced (backward compatible).
    pub constraints: Vec<FacetConstraint>,
}

impl ExtendedFacet {
    /// Create an extended facet from a base mask with no additional constraints.
    pub fn from_mask(mask: EffectMask) -> Self {
        Self {
            effect_mask: mask,
            constraints: Vec::new(),
        }
    }

    /// Create an extended facet with the given mask and constraints.
    pub fn new(mask: EffectMask, constraints: Vec<FacetConstraint>) -> Self {
        Self {
            effect_mask: mask,
            constraints,
        }
    }

    /// Check whether a specific effect is permitted by both the mask AND all constraints.
    ///
    /// Returns `Ok(())` if permitted, or `Err(reason)` describing which constraint was violated.
    pub fn check_effect(
        &self,
        effect_bit: EffectMask,
        context: &EffectContext,
    ) -> Result<(), FacetViolation> {
        // First check the base mask.
        if !is_effect_permitted(Some(self.effect_mask), effect_bit) {
            return Err(FacetViolation::EffectTypeNotPermitted {
                effect_bit,
                mask: self.effect_mask,
            });
        }

        // Then check each constraint.
        for constraint in &self.constraints {
            constraint.check(context)?;
        }

        Ok(())
    }

    /// Check whether this extended facet is a valid attenuation of a parent.
    ///
    /// The child must have a subset mask AND equal or tighter constraints.
    pub fn is_attenuation_of(&self, parent: &ExtendedFacet) -> bool {
        // Mask must be a subset.
        if !is_facet_attenuation(parent.effect_mask, self.effect_mask) {
            return false;
        }
        // All parent constraints must be present in the child (or tighter).
        // For now, we require the child to include at least all parent constraints.
        // A more sophisticated implementation would compare constraint semantics.
        for parent_constraint in &parent.constraints {
            if !self
                .constraints
                .iter()
                .any(|c| c.is_at_least_as_tight(parent_constraint))
            {
                return false;
            }
        }
        true
    }
}

/// Parameterized constraints that further restrict a faceted capability.
///
/// Each constraint type narrows what an effect can do beyond the binary
/// "allowed/not-allowed" of the EffectMask.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FacetConstraint {
    /// Maximum transfer amount per turn (caps a single turn's total outflow).
    MaxTransferAmount(u64),

    /// The holder can only target specific cells (allowlist).
    /// Empty means "no targets allowed" (deny-all for targeting).
    AllowedTargets(Vec<CellId>),

    /// Rate limit: maximum N operations of the gated type per epoch.
    /// The executor tracks the current count and resets per epoch.
    RateLimit {
        /// Maximum operations per epoch.
        max_per_epoch: u32,
        /// Current epoch's operation count (mutable at runtime).
        current_epoch_count: u32,
    },

    /// Total lifetime spend cap. Once `remaining` reaches 0, the capability
    /// can no longer authorize transfers (even if the mask permits them).
    Budget {
        /// Remaining budget in computrons. Decremented on each use.
        remaining: u64,
    },
}

impl FacetConstraint {
    /// Check whether this constraint permits the given effect context.
    pub fn check(&self, context: &EffectContext) -> Result<(), FacetViolation> {
        match self {
            FacetConstraint::MaxTransferAmount(max) => {
                if let Some(amount) = context.transfer_amount {
                    if amount > *max {
                        return Err(FacetViolation::TransferAmountExceeded { amount, max: *max });
                    }
                }
                Ok(())
            }
            FacetConstraint::AllowedTargets(targets) => {
                if let Some(target) = &context.target_cell {
                    if !targets.contains(target) {
                        return Err(FacetViolation::TargetNotAllowed { target: *target });
                    }
                }
                Ok(())
            }
            FacetConstraint::RateLimit {
                max_per_epoch,
                current_epoch_count,
            } => {
                if *current_epoch_count >= *max_per_epoch {
                    return Err(FacetViolation::RateLimitExceeded {
                        max: *max_per_epoch,
                        current: *current_epoch_count,
                    });
                }
                Ok(())
            }
            FacetConstraint::Budget { remaining } => {
                let amount = context.transfer_amount.unwrap_or(0);
                if amount > *remaining {
                    return Err(FacetViolation::BudgetExhausted {
                        requested: amount,
                        remaining: *remaining,
                    });
                }
                Ok(())
            }
        }
    }

    /// Check whether this constraint is at least as tight as another.
    ///
    /// Used for attenuation validation: a child facet must not be more permissive
    /// than its parent for any constraint.
    pub fn is_at_least_as_tight(&self, other: &FacetConstraint) -> bool {
        match (self, other) {
            (FacetConstraint::MaxTransferAmount(a), FacetConstraint::MaxTransferAmount(b)) => {
                a <= b
            }
            (FacetConstraint::AllowedTargets(a), FacetConstraint::AllowedTargets(b)) => {
                // a must be a subset of b (tighter = fewer allowed targets)
                a.iter().all(|t| b.contains(t))
            }
            (
                FacetConstraint::RateLimit {
                    max_per_epoch: a, ..
                },
                FacetConstraint::RateLimit {
                    max_per_epoch: b, ..
                },
            ) => a <= b,
            (
                FacetConstraint::Budget { remaining: a },
                FacetConstraint::Budget { remaining: b },
            ) => a <= b,
            // Different constraint types: not comparable, treat as "at least as tight"
            // only if types match.
            _ => false,
        }
    }
}

/// Context passed to facet constraint checks during effect evaluation.
///
/// Populated by the executor from the effect being applied.
#[derive(Clone, Debug, Default)]
pub struct EffectContext {
    /// The transfer amount (if this is a transfer effect).
    pub transfer_amount: Option<u64>,
    /// The target cell (if this effect targets a specific cell).
    pub target_cell: Option<CellId>,
    /// The effect type bit (which effect kind is being executed).
    pub effect_bit: EffectMask,
}

/// Describes why a facet constraint was violated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FacetViolation {
    /// The effect type is not permitted by the base mask.
    EffectTypeNotPermitted {
        effect_bit: EffectMask,
        mask: EffectMask,
    },
    /// Transfer amount exceeds the MaxTransferAmount constraint.
    TransferAmountExceeded { amount: u64, max: u64 },
    /// Target cell is not in the AllowedTargets list.
    TargetNotAllowed { target: CellId },
    /// Rate limit exceeded for the current epoch.
    RateLimitExceeded { max: u32, current: u32 },
    /// Lifetime budget exhausted.
    BudgetExhausted { requested: u64, remaining: u64 },
}

impl std::fmt::Display for FacetViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EffectTypeNotPermitted { effect_bit, mask } => {
                write!(
                    f,
                    "effect type 0x{:x} not permitted by mask 0x{:x}",
                    effect_bit, mask
                )
            }
            Self::TransferAmountExceeded { amount, max } => {
                write!(f, "transfer amount {} exceeds max {}", amount, max)
            }
            Self::TargetNotAllowed { target } => {
                write!(f, "target cell {:?} not in allowed targets", target)
            }
            Self::RateLimitExceeded { max, current } => {
                write!(f, "rate limit exceeded: {}/{} per epoch", current, max)
            }
            Self::BudgetExhausted {
                requested,
                remaining,
            } => {
                write!(
                    f,
                    "budget exhausted: requested {} but only {} remaining",
                    requested, remaining
                )
            }
        }
    }
}

impl std::error::Error for FacetViolation {}

/// A builder for constructing facet masks using a fluent API.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FacetBuilder {
    mask: EffectMask,
}

impl FacetBuilder {
    pub fn new() -> Self {
        Self { mask: 0 }
    }

    /// Start from an existing mask.
    pub fn from_mask(mask: EffectMask) -> Self {
        Self { mask }
    }

    /// Allow setting state fields.
    pub fn allow_set_field(mut self) -> Self {
        self.mask |= EFFECT_SET_FIELD;
        self
    }

    /// Allow transferring value.
    pub fn allow_transfer(mut self) -> Self {
        self.mask |= EFFECT_TRANSFER;
        self
    }

    /// Allow granting capabilities.
    pub fn allow_grant_capability(mut self) -> Self {
        self.mask |= EFFECT_GRANT_CAPABILITY;
        self
    }

    /// Allow revoking capabilities.
    pub fn allow_revoke_capability(mut self) -> Self {
        self.mask |= EFFECT_REVOKE_CAPABILITY;
        self
    }

    /// Allow emitting events.
    pub fn allow_emit_event(mut self) -> Self {
        self.mask |= EFFECT_EMIT_EVENT;
        self
    }

    /// Allow incrementing nonce.
    pub fn allow_increment_nonce(mut self) -> Self {
        self.mask |= EFFECT_INCREMENT_NONCE;
        self
    }

    /// Allow creating cells.
    pub fn allow_create_cell(mut self) -> Self {
        self.mask |= EFFECT_CREATE_CELL;
        self
    }

    /// Allow setting permissions.
    pub fn allow_set_permissions(mut self) -> Self {
        self.mask |= EFFECT_SET_PERMISSIONS;
        self
    }

    /// Allow setting verification key.
    pub fn allow_set_verification_key(mut self) -> Self {
        self.mask |= EFFECT_SET_VERIFICATION_KEY;
        self
    }

    /// Build the final mask.
    pub fn build(self) -> EffectMask {
        self.mask
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_facet_attenuation_subset() {
        let parent = EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT;
        let child = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
        assert!(is_facet_attenuation(parent, child));
    }

    #[test]
    fn test_facet_attenuation_amplification_denied() {
        let parent = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
        let child = EFFECT_SET_FIELD | EFFECT_TRANSFER; // TRANSFER not in parent
        assert!(!is_facet_attenuation(parent, child));
    }

    #[test]
    fn test_facet_attenuation_same_is_ok() {
        let mask = FACET_STATE_WRITER;
        assert!(is_facet_attenuation(mask, mask));
    }

    #[test]
    fn test_facet_all_permits_everything() {
        assert!(is_facet_attenuation(EFFECT_ALL, FACET_ADMIN));
        assert!(is_facet_attenuation(EFFECT_ALL, FACET_READ_ONLY));
        assert!(is_facet_attenuation(EFFECT_ALL, EFFECT_ALL));
    }

    #[test]
    fn test_effect_permitted_none_allows_all() {
        assert!(is_effect_permitted(None, EFFECT_SET_FIELD));
        assert!(is_effect_permitted(None, EFFECT_TRANSFER));
        assert!(is_effect_permitted(None, EFFECT_SOVEREIGN_OPS));
    }

    #[test]
    fn test_effect_permitted_mask_restricts() {
        let mask = FACET_TRANSFER_ONLY;
        assert!(is_effect_permitted(Some(mask), EFFECT_TRANSFER));
        assert!(!is_effect_permitted(Some(mask), EFFECT_SET_FIELD));
        assert!(!is_effect_permitted(Some(mask), EFFECT_SET_PERMISSIONS));
    }

    #[test]
    fn test_facet_builder() {
        let mask = FacetBuilder::new()
            .allow_set_field()
            .allow_emit_event()
            .build();
        assert_eq!(mask, FACET_STATE_WRITER);
    }

    #[test]
    fn test_describe_mask() {
        let names = describe_mask(FACET_STATE_WRITER);
        assert!(names.contains(&"SetField"));
        assert!(names.contains(&"EmitEvent"));
        assert!(!names.contains(&"Transfer"));
    }

    // ─── Extended Facet tests ───────────────────────────────────────────────

    #[test]
    fn test_extended_facet_max_transfer_amount() {
        let facet = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::MaxTransferAmount(100)],
        );

        // Allowed: transfer 50 <= 100
        let ctx = EffectContext {
            transfer_amount: Some(50),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_ok());

        // Denied: transfer 200 > 100
        let ctx = EffectContext {
            transfer_amount: Some(200),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_err());
    }

    #[test]
    fn test_extended_facet_allowed_targets() {
        let target_a = CellId::derive_raw(&[1; 32], &[2; 32]);
        let target_b = CellId::derive_raw(&[3; 32], &[4; 32]);
        let target_c = CellId::derive_raw(&[5; 32], &[6; 32]);

        let facet = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::AllowedTargets(vec![target_a, target_b])],
        );

        // Allowed target
        let ctx = EffectContext {
            target_cell: Some(target_a),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_ok());

        // Denied target
        let ctx = EffectContext {
            target_cell: Some(target_c),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_err());
    }

    #[test]
    fn test_extended_facet_rate_limit() {
        let facet = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::RateLimit {
                max_per_epoch: 3,
                current_epoch_count: 2,
            }],
        );
        let ctx = EffectContext::default();
        // 2 < 3: allowed
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_ok());

        let facet_exhausted = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::RateLimit {
                max_per_epoch: 3,
                current_epoch_count: 3,
            }],
        );
        // 3 >= 3: denied
        assert!(facet_exhausted.check_effect(EFFECT_TRANSFER, &ctx).is_err());
    }

    #[test]
    fn test_extended_facet_budget() {
        let facet = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::Budget { remaining: 500 }],
        );

        let ctx = EffectContext {
            transfer_amount: Some(300),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_ok());

        let ctx = EffectContext {
            transfer_amount: Some(600),
            effect_bit: EFFECT_TRANSFER,
            ..Default::default()
        };
        assert!(facet.check_effect(EFFECT_TRANSFER, &ctx).is_err());
    }

    #[test]
    fn test_extended_facet_attenuation() {
        let parent = ExtendedFacet::new(
            EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
            vec![FacetConstraint::MaxTransferAmount(1000)],
        );

        // Valid attenuation: subset mask + tighter constraint
        let child = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::MaxTransferAmount(500)],
        );
        assert!(child.is_attenuation_of(&parent));

        // Invalid: child has higher max than parent
        let invalid_child = ExtendedFacet::new(
            EFFECT_TRANSFER,
            vec![FacetConstraint::MaxTransferAmount(2000)],
        );
        assert!(!invalid_child.is_attenuation_of(&parent));

        // Invalid: child has effect not in parent mask
        let invalid_mask = ExtendedFacet::new(
            EFFECT_TRANSFER | EFFECT_SET_FIELD,
            vec![FacetConstraint::MaxTransferAmount(500)],
        );
        assert!(!invalid_mask.is_attenuation_of(&parent));
    }
}
