//! Partial fill support for AMM/DEX-style intents.
//!
//! This module implements the logic for matching and fulfilling intents that
//! accept partial fills. A partial fill occurs when a capability can satisfy
//! some but not all of an intent's requested quantity.
//!
//! # Flow
//!
//! 1. Intent is posted with `FillConstraints { min: 10, max: 100, fill_or_kill: false }`
//! 2. A matcher finds a capability that can provide 40 units (between min and max)
//! 3. A `PartialFillResult` is produced with `filled_amount: 40, remaining: 60`
//! 4. A residual intent is created for the remaining 60 units (same spec, reduced quantity)
//! 5. The residual intent can be matched by other capabilities later
//!
//! # Privacy
//!
//! Partial fills do not degrade the privacy model. The residual intent is a new
//! intent with its own ID. The link between the original and residual is only
//! visible to the creator (via `remaining_after_fill`).

use crate::fulfillment::{FulfillOptions, Fulfillment, FulfillmentError, fulfill};
use crate::matcher::HeldCapability;
use crate::{
    CommitmentId, FillConstraints, Intent, Match,
};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Result of a partial fill operation.
#[derive(Clone, Debug)]
pub struct PartialFillResult {
    /// How much was filled in this operation.
    pub filled_amount: u64,
    /// How much remains to be filled.
    pub remaining_amount: u64,
    /// The residual intent for the remaining amount, if any.
    /// `None` if the fill was complete (filled_amount == max_fill_amount) or
    /// if the intent was fill_or_kill.
    pub residual_intent: Option<Intent>,
    /// The fulfillment result for the filled portion.
    pub fulfillment: Fulfillment,
}

/// Errors specific to partial fill operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PartialFillError {
    /// The available amount is below the intent's minimum fill amount.
    BelowMinimum { available: u64, minimum: u64 },
    /// The intent is fill-or-kill but only a partial amount is available.
    FillOrKillRejected { available: u64, required: u64 },
    /// The intent has no fill constraints (use regular fulfillment).
    NoFillConstraints,
    /// The fill constraints are invalid.
    InvalidConstraints(String),
    /// Underlying fulfillment error.
    Fulfillment(FulfillmentError),
}

impl std::fmt::Display for PartialFillError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BelowMinimum { available, minimum } => {
                write!(
                    f,
                    "available amount {} is below minimum fill amount {}",
                    available, minimum
                )
            }
            Self::FillOrKillRejected {
                available,
                required,
            } => {
                write!(
                    f,
                    "fill-or-kill: available {} < required {} (must fill entirely or not at all)",
                    available, required
                )
            }
            Self::NoFillConstraints => {
                write!(f, "intent has no fill constraints; use regular fulfillment")
            }
            Self::InvalidConstraints(msg) => {
                write!(f, "invalid fill constraints: {}", msg)
            }
            Self::Fulfillment(e) => write!(f, "fulfillment error: {}", e),
        }
    }
}

// ---------------------------------------------------------------------------
// Matching with partial fill awareness
// ---------------------------------------------------------------------------

/// Check whether a given fill amount is acceptable for an intent's fill constraints.
///
/// Returns `Ok(effective_amount)` where `effective_amount` is clamped to `max_fill_amount`,
/// or an error if the amount is unacceptable.
pub fn check_fill_amount(
    constraints: &FillConstraints,
    available_amount: u64,
) -> Result<u64, PartialFillError> {
    // SECURITY: Reject zero min_fill_amount -- allows zero-value fills that bypass
    // economic constraints.
    if constraints.min_fill_amount == 0 {
        return Err(PartialFillError::InvalidConstraints(
            "min_fill_amount must be > 0".into(),
        ));
    }

    // SECURITY: min must not exceed max
    if constraints.min_fill_amount > constraints.max_fill_amount {
        return Err(PartialFillError::InvalidConstraints(format!(
            "min_fill_amount ({}) must be <= max_fill_amount ({})",
            constraints.min_fill_amount, constraints.max_fill_amount
        )));
    }

    // Fill-or-kill: must satisfy the full max amount
    if constraints.fill_or_kill {
        if available_amount < constraints.max_fill_amount {
            return Err(PartialFillError::FillOrKillRejected {
                available: available_amount,
                required: constraints.max_fill_amount,
            });
        }
        return Ok(constraints.max_fill_amount);
    }

    // Check minimum
    if available_amount < constraints.min_fill_amount {
        return Err(PartialFillError::BelowMinimum {
            available: available_amount,
            minimum: constraints.min_fill_amount,
        });
    }

    // Clamp to max
    Ok(available_amount.min(constraints.max_fill_amount))
}

/// Score a partial fill: closer to max = better score.
///
/// Returns a value in [0.0, 1.0] where 1.0 means full fill.
pub fn fill_score(constraints: &FillConstraints, fill_amount: u64) -> f64 {
    if constraints.max_fill_amount == 0 {
        return 0.0;
    }
    (fill_amount as f64) / (constraints.max_fill_amount as f64)
}

// ---------------------------------------------------------------------------
// Residual intent creation
// ---------------------------------------------------------------------------

/// Create a residual intent for the remaining unfilled amount after a partial fill.
///
/// The residual intent:
/// - Has the same MatchSpec and constraints as the original
/// - Has a new content-addressed ID (different fill constraints)
/// - Has `min_fill_amount` clamped to not exceed the remaining amount
/// - Links back to the original via `remaining_after_fill`
pub fn create_residual_intent(original: &Intent, filled_amount: u64) -> Option<Intent> {
    let constraints = original.fill_constraints.as_ref()?;

    // If fill-or-kill, no residual (should have been fully filled or rejected)
    if constraints.fill_or_kill {
        return None;
    }

    let remaining = constraints.max_fill_amount.saturating_sub(filled_amount);
    if remaining == 0 {
        return None;
    }

    // The residual's min_fill_amount should not exceed the remaining amount
    let residual_min = constraints.min_fill_amount.min(remaining);

    let residual_constraints = FillConstraints {
        min_fill_amount: residual_min,
        max_fill_amount: remaining,
        fill_or_kill: false,
        remaining_after_fill: None, // will be set if this residual is also partially filled
    };

    let residual = Intent::new_with_fill(
        original.kind,
        original.matcher.clone(),
        original.creator,
        original.expiry,
        original.stake_proof.clone(),
        residual_constraints,
    );

    Some(residual)
}

// ---------------------------------------------------------------------------
// Execute partial fill
// ---------------------------------------------------------------------------

/// Execute a partial fill for an intent.
///
/// This function:
/// 1. Validates the fill amount against constraints
/// 2. Creates the fulfillment for the partial amount
/// 3. If not fill-or-kill and not fully filled, creates a residual intent
/// 4. Returns the composite result
///
/// # Arguments
///
/// * `intent` - The intent being partially filled (must have fill_constraints)
/// * `matched` - The match result from the matcher
/// * `source_token` - The token being used to fulfill
/// * `our_commitment` - The fulfiller's anonymous commitment
/// * `available_amount` - How much the capability can provide
/// * `options` - Fulfillment options (mode, keys, etc.)
pub fn execute_partial_fill(
    intent: &Intent,
    matched: &Match,
    source_token: &HeldCapability,
    our_commitment: CommitmentId,
    available_amount: u64,
    options: &FulfillOptions,
) -> Result<PartialFillResult, PartialFillError> {
    let constraints = intent
        .fill_constraints
        .as_ref()
        .ok_or(PartialFillError::NoFillConstraints)?;

    // Validate and compute effective fill amount
    let effective_amount = check_fill_amount(constraints, available_amount)?;

    // Create the fulfillment for the filled portion
    let fulfillment = fulfill(intent, matched, source_token, our_commitment, options)
        .map_err(PartialFillError::Fulfillment)?;

    // Determine remaining and create residual if needed
    let remaining_amount = constraints.max_fill_amount.saturating_sub(effective_amount);
    let residual_intent = if remaining_amount > 0 && !constraints.fill_or_kill {
        create_residual_intent(intent, effective_amount)
    } else {
        None
    };

    Ok(PartialFillResult {
        filled_amount: effective_amount,
        remaining_amount,
        residual_intent,
        fulfillment,
    })
}

// ---------------------------------------------------------------------------
// Cumulative fill tracking
// ---------------------------------------------------------------------------

/// Tracker for accumulating multiple partial fills against a single original intent.
#[derive(Clone, Debug)]
pub struct CumulativeFillTracker {
    /// The original intent ID.
    pub original_intent_id: IntentId,
    /// Total amount filled across all partial fills so far.
    pub total_filled: u64,
    /// The maximum fill amount from the original intent.
    pub max_fill_amount: u64,
    /// IDs of all partial fill intents (original + residuals).
    pub fill_chain: Vec<IntentId>,
}

/// Type alias reexported locally.
type IntentId = [u8; 32];

impl CumulativeFillTracker {
    /// Create a new tracker for an intent.
    pub fn new(intent: &Intent) -> Option<Self> {
        let constraints = intent.fill_constraints.as_ref()?;
        Some(Self {
            original_intent_id: intent.id,
            total_filled: 0,
            max_fill_amount: constraints.max_fill_amount,
            fill_chain: vec![intent.id],
        })
    }

    /// Record a partial fill. Returns true if the intent is now fully filled.
    pub fn record_fill(&mut self, result: &PartialFillResult) -> bool {
        self.total_filled += result.filled_amount;
        if let Some(ref residual) = result.residual_intent {
            self.fill_chain.push(residual.id);
        }
        self.is_complete()
    }

    /// Check if the cumulative fills have reached the max amount.
    pub fn is_complete(&self) -> bool {
        self.total_filled >= self.max_fill_amount
    }

    /// How much remains to be filled.
    pub fn remaining(&self) -> u64 {
        self.max_fill_amount.saturating_sub(self.total_filled)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matcher::Sensitivity;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec, VerificationMode};

    fn make_fill_intent(min: u64, max: u64, fill_or_kill: bool) -> Intent {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("transfer".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let constraints = FillConstraints {
            min_fill_amount: min,
            max_fill_amount: max,
            fill_or_kill,
            remaining_after_fill: None,
        };
        Intent::new_with_fill(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX,
            None,
            constraints,
        )
    }

    fn make_source_token() -> HeldCapability {
        HeldCapability {
            token_id: "tok_amm".into(),
            actions: vec!["transfer".into()],
            resource: "*".into(),
            app_id: None,
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: None,
            budget: None,
            sensitivity: Sensitivity::Normal,
        }
    }

    fn make_match(intent: &Intent) -> Match {
        Match {
            intent_id: intent.id,
            satisfier: CommitmentId([0xBB; 32]),
            proof: None,
            mode: VerificationMode::Trusted,
        }
    }

    fn make_options() -> FulfillOptions {
        FulfillOptions {
            mode: VerificationMode::Trusted,
            root_key: Some([0x42; 32]),
            ..Default::default()
        }
    }

    // =========================================================================
    // check_fill_amount tests
    // =========================================================================

    #[test]
    fn test_partial_fill_full_amount_accepted() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        // Available == max: full fill
        let result = check_fill_amount(&constraints, 100);
        assert_eq!(result.unwrap(), 100);
    }

    #[test]
    fn test_partial_fill_above_max_clamped() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        // Available > max: clamped to max
        let result = check_fill_amount(&constraints, 200);
        assert_eq!(result.unwrap(), 100);
    }

    #[test]
    fn test_partial_fill_between_min_and_max() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        // Available between min and max: partial fill accepted
        let result = check_fill_amount(&constraints, 50);
        assert_eq!(result.unwrap(), 50);
    }

    #[test]
    fn test_partial_fill_below_minimum_rejected() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        // Available < min: rejected
        let result = check_fill_amount(&constraints, 5);
        assert!(matches!(
            result,
            Err(PartialFillError::BelowMinimum {
                available: 5,
                minimum: 10
            })
        ));
    }

    #[test]
    fn test_partial_fill_fill_or_kill_full_accepted() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: true,
            remaining_after_fill: None,
        };
        // Fill-or-kill with full amount: accepted
        let result = check_fill_amount(&constraints, 100);
        assert_eq!(result.unwrap(), 100);
    }

    #[test]
    fn test_partial_fill_fill_or_kill_partial_rejected() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: true,
            remaining_after_fill: None,
        };
        // Fill-or-kill with partial: rejected even if above min
        let result = check_fill_amount(&constraints, 50);
        assert!(matches!(
            result,
            Err(PartialFillError::FillOrKillRejected {
                available: 50,
                required: 100
            })
        ));
    }

    #[test]
    fn test_partial_fill_fill_or_kill_above_max_accepted() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: true,
            remaining_after_fill: None,
        };
        // Fill-or-kill with more than enough: accepted at max
        let result = check_fill_amount(&constraints, 200);
        assert_eq!(result.unwrap(), 100);
    }

    // =========================================================================
    // fill_score tests
    // =========================================================================

    #[test]
    fn test_partial_fill_score_full() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        let score = fill_score(&constraints, 100);
        assert!((score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_partial_fill_score_half() {
        let constraints = FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        let score = fill_score(&constraints, 50);
        assert!((score - 0.5).abs() < f64::EPSILON);
    }

    // =========================================================================
    // Residual intent creation tests
    // =========================================================================

    #[test]
    fn test_partial_fill_residual_created_on_partial() {
        let intent = make_fill_intent(10, 100, false);
        let residual = create_residual_intent(&intent, 40);
        assert!(residual.is_some());

        let r = residual.unwrap();
        let rc = r.fill_constraints.as_ref().unwrap();
        assert_eq!(rc.max_fill_amount, 60); // 100 - 40
        assert_eq!(rc.min_fill_amount, 10); // same as original (still fits)
        assert!(!rc.fill_or_kill);
        assert_ne!(r.id, intent.id); // different intent
    }

    #[test]
    fn test_partial_fill_residual_min_clamped() {
        // If remaining < original min, clamp min to remaining
        let intent = make_fill_intent(50, 100, false);
        let residual = create_residual_intent(&intent, 70);
        assert!(residual.is_some());

        let r = residual.unwrap();
        let rc = r.fill_constraints.as_ref().unwrap();
        assert_eq!(rc.max_fill_amount, 30); // 100 - 70
        assert_eq!(rc.min_fill_amount, 30); // clamped: min(50, 30) = 30
    }

    #[test]
    fn test_partial_fill_no_residual_on_full_fill() {
        let intent = make_fill_intent(10, 100, false);
        let residual = create_residual_intent(&intent, 100);
        assert!(residual.is_none());
    }

    #[test]
    fn test_partial_fill_no_residual_on_fill_or_kill() {
        let intent = make_fill_intent(10, 100, true);
        let residual = create_residual_intent(&intent, 50);
        assert!(residual.is_none()); // fill_or_kill never produces residuals
    }

    // =========================================================================
    // execute_partial_fill tests
    // =========================================================================

    #[test]
    fn test_partial_fill_execute_full_fill() {
        let intent = make_fill_intent(10, 100, false);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 100, &options);
        assert!(result.is_ok());

        let pf = result.unwrap();
        assert_eq!(pf.filled_amount, 100);
        assert_eq!(pf.remaining_amount, 0);
        assert!(pf.residual_intent.is_none()); // fully filled, no residual
    }

    #[test]
    fn test_partial_fill_execute_partial_produces_residual() {
        let intent = make_fill_intent(10, 100, false);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 40, &options);
        assert!(result.is_ok());

        let pf = result.unwrap();
        assert_eq!(pf.filled_amount, 40);
        assert_eq!(pf.remaining_amount, 60);
        assert!(pf.residual_intent.is_some());

        let residual = pf.residual_intent.unwrap();
        let rc = residual.fill_constraints.as_ref().unwrap();
        assert_eq!(rc.max_fill_amount, 60);
    }

    #[test]
    fn test_partial_fill_execute_below_min_rejected() {
        let intent = make_fill_intent(10, 100, false);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 5, &options);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PartialFillError::BelowMinimum { .. }
        ));
    }

    #[test]
    fn test_partial_fill_execute_fill_or_kill_partial_rejected() {
        let intent = make_fill_intent(10, 100, true);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 50, &options);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PartialFillError::FillOrKillRejected { .. }
        ));
    }

    #[test]
    fn test_partial_fill_execute_fill_or_kill_full_accepted() {
        let intent = make_fill_intent(10, 100, true);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 100, &options);
        assert!(result.is_ok());

        let pf = result.unwrap();
        assert_eq!(pf.filled_amount, 100);
        assert_eq!(pf.remaining_amount, 0);
        assert!(pf.residual_intent.is_none());
    }

    // =========================================================================
    // Cumulative fill tracker tests
    // =========================================================================

    #[test]
    fn test_partial_fill_cumulative_tracker_multiple_fills() {
        let intent = make_fill_intent(10, 100, false);
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let mut tracker = CumulativeFillTracker::new(&intent).unwrap();
        assert_eq!(tracker.remaining(), 100);
        assert!(!tracker.is_complete());

        // First partial fill: 30 units
        let result1 =
            execute_partial_fill(&intent, &matched, &token, our_id, 30, &options).unwrap();
        assert_eq!(result1.filled_amount, 30);
        let complete = tracker.record_fill(&result1);
        assert!(!complete);
        assert_eq!(tracker.total_filled, 30);
        assert_eq!(tracker.remaining(), 70);

        // Second partial fill against the residual: 40 units
        let residual1 = result1.residual_intent.unwrap();
        let matched2 = make_match(&residual1);
        let result2 =
            execute_partial_fill(&residual1, &matched2, &token, our_id, 40, &options).unwrap();
        assert_eq!(result2.filled_amount, 40);
        let complete = tracker.record_fill(&result2);
        assert!(!complete);
        assert_eq!(tracker.total_filled, 70);
        assert_eq!(tracker.remaining(), 30);

        // Third partial fill against the second residual: 30 units (completes it)
        let residual2 = result2.residual_intent.unwrap();
        let matched3 = make_match(&residual2);
        let result3 =
            execute_partial_fill(&residual2, &matched3, &token, our_id, 30, &options).unwrap();
        assert_eq!(result3.filled_amount, 30);
        assert_eq!(result3.remaining_amount, 0);
        assert!(result3.residual_intent.is_none());
        let complete = tracker.record_fill(&result3);
        assert!(complete);
        assert_eq!(tracker.total_filled, 100);
        assert_eq!(tracker.remaining(), 0);

        // The fill chain should have original + 2 residuals
        assert_eq!(tracker.fill_chain.len(), 3);
    }

    #[test]
    fn test_partial_fill_no_constraints_returns_error() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("transfer".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        // Intent without fill constraints
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX,
            None,
        );
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 50, &options);
        assert!(matches!(
            result.unwrap_err(),
            PartialFillError::NoFillConstraints
        ));
    }

    // =========================================================================
    // SECURITY: Zero fill amount and min>max validation tests
    // =========================================================================

    #[test]
    fn test_zero_min_fill_amount_rejected_at_check() {
        // ADVERSARIAL: Attacker tries to create fill constraints with min=0,
        // allowing zero-value fills that bypass economic constraints.
        let constraints = FillConstraints {
            min_fill_amount: 0,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        let result = check_fill_amount(&constraints, 50);
        assert!(
            matches!(result, Err(PartialFillError::InvalidConstraints(_))),
            "min_fill_amount=0 must be rejected at check_fill_amount, got: {:?}",
            result
        );
    }

    #[test]
    fn test_min_exceeds_max_rejected_at_check() {
        // ADVERSARIAL: min > max should never be accepted.
        let constraints = FillConstraints {
            min_fill_amount: 200,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        let result = check_fill_amount(&constraints, 150);
        assert!(
            matches!(result, Err(PartialFillError::InvalidConstraints(_))),
            "min > max must be rejected at check_fill_amount, got: {:?}",
            result
        );
    }

    #[test]
    fn test_zero_min_fill_amount_rejected_in_execute() {
        // ADVERSARIAL: Even if somehow FillConstraints with min=0 makes it past
        // creation, execute_partial_fill must reject it.
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("transfer".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let constraints = FillConstraints {
            min_fill_amount: 0,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
        };
        let intent = Intent::new_with_fill(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            u64::MAX,
            None,
            constraints,
        );
        let matched = make_match(&intent);
        let token = make_source_token();
        let our_id = CommitmentId([0xBB; 32]);
        let options = make_options();

        let result = execute_partial_fill(&intent, &matched, &token, our_id, 50, &options);
        assert!(
            matches!(result, Err(PartialFillError::InvalidConstraints(_))),
            "zero min_fill_amount must be rejected in execute_partial_fill, got: {:?}",
            result
        );
    }
}
