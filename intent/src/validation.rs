//! Input validation for intents.
//!
//! Prevents spam and denial-of-service by enforcing size limits on intent fields.
//! All validation runs before storing or propagating an intent.

use crate::{Constraint, Intent};

/// Maximum recursion depth for compound specs.
pub const MAX_COMPOUND_DEPTH: usize = 3;

/// Maximum total sub-specs in a compound intent.
pub const MAX_COMPOUND_SPECS: usize = 10;

/// Maximum number of action patterns per intent.
pub const MAX_ACTIONS: usize = 64;

/// Maximum number of constraints per intent.
pub const MAX_CONSTRAINTS: usize = 64;

/// Maximum length of any string field in an intent (action names, resource patterns, etc.).
pub const MAX_STRING_LEN: usize = 256;

/// Maximum length of a resource pattern.
pub const MAX_RESOURCE_PATTERN_LEN: usize = 256;

/// Maximum number of predicate requirements attached to an intent.
///
/// Predicate requirements drive STARK predicate-proof verification at
/// fulfillment time; an unbounded list lets a malicious poster force
/// fulfillers to run arbitrarily many proofs.
pub const MAX_PREDICATE_REQUIREMENTS: usize = 16;

/// Maximum length of any predicate field string (attribute, predicate type).
pub const MAX_PREDICATE_STRING_LEN: usize = 128;

/// Allowed predicate types — keep aligned with `verify_predicate_requirement`
/// in `intent::fulfillment`. Anything outside this set will fail to verify
/// anyway, so we reject at intake.
const ALLOWED_PREDICATE_TYPES: &[&str] = &["gte", "lte", "gt", "lt", "neq", "eq", "in_range"];

/// Validation errors for intent fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValidationError {
    /// Too many action patterns.
    TooManyActions { count: usize, max: usize },
    /// Too many constraints.
    TooManyConstraints { count: usize, max: usize },
    /// An action string exceeds the maximum length.
    ActionStringTooLong { len: usize, max: usize },
    /// A resource string exceeds the maximum length.
    ResourceStringTooLong { len: usize, max: usize },
    /// The resource pattern is too long.
    ResourcePatternTooLong { len: usize, max: usize },
    /// A constraint string value exceeds the maximum length.
    ConstraintStringTooLong { len: usize, max: usize },
    /// Compound spec nesting exceeds the maximum depth.
    CompoundTooDeep { depth: usize, max: usize },
    /// Too many total sub-specs in compound intent.
    TooManyCompoundSpecs { count: usize, max: usize },
    /// min_budget is zero, which allows free fulfillment (must be > 0 or None).
    ZeroBudget,
    /// Fill constraints are invalid.
    InvalidFillConstraints(String),
    /// Too many predicate requirements attached.
    TooManyPredicateRequirements { count: usize, max: usize },
    /// A predicate field string exceeds the maximum length.
    PredicateStringTooLong { len: usize, max: usize },
    /// Predicate type is not in the supported set.
    UnknownPredicateType(String),
    /// `in_range` predicate must have `upper_bound` set and `>= threshold`.
    InvalidPredicateRange {
        threshold: u64,
        upper_bound: Option<u64>,
    },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyActions { count, max } => {
                write!(f, "too many actions: {count} exceeds max {max}")
            }
            Self::TooManyConstraints { count, max } => {
                write!(f, "too many constraints: {count} exceeds max {max}")
            }
            Self::ActionStringTooLong { len, max } => {
                write!(f, "action string too long: {len} exceeds max {max}")
            }
            Self::ResourceStringTooLong { len, max } => {
                write!(f, "resource string too long: {len} exceeds max {max}")
            }
            Self::ResourcePatternTooLong { len, max } => {
                write!(f, "resource pattern too long: {len} exceeds max {max}")
            }
            Self::ConstraintStringTooLong { len, max } => {
                write!(f, "constraint string too long: {len} exceeds max {max}")
            }
            Self::CompoundTooDeep { depth, max } => {
                write!(f, "compound spec too deep: depth {depth} exceeds max {max}")
            }
            Self::TooManyCompoundSpecs { count, max } => {
                write!(f, "too many compound sub-specs: {count} exceeds max {max}")
            }
            Self::ZeroBudget => {
                write!(
                    f,
                    "min_budget must be > 0 (use None to omit budget constraint)"
                )
            }
            Self::InvalidFillConstraints(msg) => {
                write!(f, "invalid fill constraints: {msg}")
            }
            Self::TooManyPredicateRequirements { count, max } => {
                write!(
                    f,
                    "too many predicate requirements: {count} exceeds max {max}"
                )
            }
            Self::PredicateStringTooLong { len, max } => {
                write!(f, "predicate string too long: {len} exceeds max {max}")
            }
            Self::UnknownPredicateType(t) => {
                write!(f, "unknown predicate type: {t}")
            }
            Self::InvalidPredicateRange {
                threshold,
                upper_bound,
            } => {
                write!(
                    f,
                    "invalid in_range bounds: threshold={threshold}, upper_bound={upper_bound:?}"
                )
            }
        }
    }
}

impl std::error::Error for ValidationError {}

/// Validate an intent's fields against size limits.
///
/// Returns `Ok(())` if the intent passes all validation checks, or the first
/// validation error found.
pub fn validate_intent(intent: &Intent) -> Result<(), ValidationError> {
    let spec = &intent.matcher;

    // Check action count
    if spec.actions.len() > MAX_ACTIONS {
        return Err(ValidationError::TooManyActions {
            count: spec.actions.len(),
            max: MAX_ACTIONS,
        });
    }

    // Check constraint count
    if spec.constraints.len() > MAX_CONSTRAINTS {
        return Err(ValidationError::TooManyConstraints {
            count: spec.constraints.len(),
            max: MAX_CONSTRAINTS,
        });
    }

    // Check action string lengths
    for pattern in &spec.actions {
        if let Some(ref action) = pattern.action {
            if action.len() > MAX_STRING_LEN {
                return Err(ValidationError::ActionStringTooLong {
                    len: action.len(),
                    max: MAX_STRING_LEN,
                });
            }
        }
        if let Some(ref resource) = pattern.resource {
            if resource.len() > MAX_STRING_LEN {
                return Err(ValidationError::ResourceStringTooLong {
                    len: resource.len(),
                    max: MAX_STRING_LEN,
                });
            }
        }
    }

    // Check resource pattern length
    if let Some(ref pattern) = spec.resource_pattern {
        if pattern.len() > MAX_RESOURCE_PATTERN_LEN {
            return Err(ValidationError::ResourcePatternTooLong {
                len: pattern.len(),
                max: MAX_RESOURCE_PATTERN_LEN,
            });
        }
    }

    // Check constraint string lengths
    for constraint in &spec.constraints {
        let len = constraint_string_len(constraint);
        if len > MAX_STRING_LEN {
            return Err(ValidationError::ConstraintStringTooLong {
                len,
                max: MAX_STRING_LEN,
            });
        }
    }

    // Check compound spec limits (issue #6: recursion limit)
    if let Some(compound) = &spec.compound {
        validate_compound_depth(compound, 1)?;
    }

    // SECURITY: Reject min_budget of 0 -- a zero-budget intent allows free
    // fulfillment. If no budget constraint is needed, use None instead.
    if spec.min_budget == Some(0) {
        return Err(ValidationError::ZeroBudget);
    }

    // SECURITY: Validate fill constraints invariants
    if let Some(fc) = &intent.fill_constraints {
        if fc.min_fill_amount == 0 {
            return Err(ValidationError::InvalidFillConstraints(
                "min_fill_amount must be > 0".into(),
            ));
        }
        if fc.min_fill_amount > fc.max_fill_amount {
            return Err(ValidationError::InvalidFillConstraints(format!(
                "min_fill_amount ({}) must be <= max_fill_amount ({})",
                fc.min_fill_amount, fc.max_fill_amount
            )));
        }
    }

    // SECURITY: Validate predicate requirements. Previously these were
    // unvalidated; a malicious poster could attach unbounded predicate
    // proofs and force fulfillers to verify each one.
    if spec.predicate_requirements.len() > MAX_PREDICATE_REQUIREMENTS {
        return Err(ValidationError::TooManyPredicateRequirements {
            count: spec.predicate_requirements.len(),
            max: MAX_PREDICATE_REQUIREMENTS,
        });
    }
    for req in &spec.predicate_requirements {
        if req.attribute.len() > MAX_PREDICATE_STRING_LEN {
            return Err(ValidationError::PredicateStringTooLong {
                len: req.attribute.len(),
                max: MAX_PREDICATE_STRING_LEN,
            });
        }
        if req.predicate_type.len() > MAX_PREDICATE_STRING_LEN {
            return Err(ValidationError::PredicateStringTooLong {
                len: req.predicate_type.len(),
                max: MAX_PREDICATE_STRING_LEN,
            });
        }
        if !ALLOWED_PREDICATE_TYPES.contains(&req.predicate_type.as_str()) {
            return Err(ValidationError::UnknownPredicateType(
                req.predicate_type.clone(),
            ));
        }
        if req.predicate_type == "in_range" {
            let upper = req.upper_bound;
            match upper {
                Some(u) if u >= req.threshold => {}
                _ => {
                    return Err(ValidationError::InvalidPredicateRange {
                        threshold: req.threshold,
                        upper_bound: upper,
                    });
                }
            }
        }
    }

    Ok(())
}

/// Recursively validate compound spec depth and total count.
fn validate_compound_depth(
    specs: &[crate::MatchSpec],
    current_depth: usize,
) -> Result<(), ValidationError> {
    if current_depth > MAX_COMPOUND_DEPTH {
        return Err(ValidationError::CompoundTooDeep {
            depth: current_depth,
            max: MAX_COMPOUND_DEPTH,
        });
    }
    if specs.len() > MAX_COMPOUND_SPECS {
        return Err(ValidationError::TooManyCompoundSpecs {
            count: specs.len(),
            max: MAX_COMPOUND_SPECS,
        });
    }
    for sub_spec in specs {
        if let Some(nested) = &sub_spec.compound {
            validate_compound_depth(nested, current_depth + 1)?;
        }
    }
    Ok(())
}

/// Get the length of the longest string in a constraint.
fn constraint_string_len(constraint: &Constraint) -> usize {
    match constraint {
        Constraint::AppId(s) => s.len(),
        Constraint::Service(s) => s.len(),
        Constraint::UserId(s) => s.len(),
        Constraint::NotExpiredAt(_) => 0,
        Constraint::Feature(s) => s.len(),
        Constraint::OAuthProvider(s) => s.len(),
        Constraint::Custom { predicate, value } => predicate.len().max(value.len()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec};

    fn make_valid_intent() -> Intent {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: Some("documents/*".into()),
            }],
            constraints: vec![Constraint::AppId("myapp".into())],
            min_budget: None,
            resource_pattern: Some("documents/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None)
    }

    #[test]
    fn test_valid_intent_passes() {
        let intent = make_valid_intent();
        assert!(validate_intent(&intent).is_ok());
    }

    #[test]
    fn test_too_many_actions_rejected() {
        let actions: Vec<ActionPattern> = (0..65)
            .map(|i| ActionPattern {
                action: Some(format!("action_{i}")),
                resource: None,
            })
            .collect();
        let spec = MatchSpec {
            actions,
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(matches!(
            err,
            ValidationError::TooManyActions { count: 65, max: 64 }
        ));
    }

    #[test]
    fn test_too_many_constraints_rejected() {
        let constraints: Vec<Constraint> = (0..65)
            .map(|i| Constraint::Feature(format!("feat_{i}")))
            .collect();
        let spec = MatchSpec {
            actions: vec![],
            constraints,
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(matches!(
            err,
            ValidationError::TooManyConstraints { count: 65, max: 64 }
        ));
    }

    #[test]
    fn test_long_action_string_rejected() {
        let long_string = "x".repeat(257);
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some(long_string),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(matches!(err, ValidationError::ActionStringTooLong { .. }));
    }

    #[test]
    fn test_long_resource_pattern_rejected() {
        let long_pattern = "x".repeat(257);
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: Some(long_pattern),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(matches!(
            err,
            ValidationError::ResourcePatternTooLong { .. }
        ));
    }

    #[test]
    fn test_long_constraint_string_rejected() {
        let long_string = "x".repeat(257);
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![Constraint::AppId(long_string)],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(matches!(
            err,
            ValidationError::ConstraintStringTooLong { .. }
        ));
    }

    #[test]
    fn test_exactly_at_limit_passes() {
        let max_string = "x".repeat(256);
        let actions: Vec<ActionPattern> = (0..64)
            .map(|_| ActionPattern {
                action: Some("a".into()),
                resource: None,
            })
            .collect();
        let constraints: Vec<Constraint> =
            (0..64).map(|_| Constraint::Feature("f".into())).collect();
        let spec = MatchSpec {
            actions,
            constraints,
            min_budget: None,
            resource_pattern: Some(max_string),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        assert!(validate_intent(&intent).is_ok());
    }

    // =========================================================================
    // SECURITY: Budget and fill constraint validation tests
    // =========================================================================

    #[test]
    fn test_zero_budget_rejected() {
        // ADVERSARIAL: An attacker creates an intent with min_budget=0 to get
        // free fulfillment. This must be rejected.
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("execute".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(0), // ATTACK: zero budget = free fulfillment
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        let err = validate_intent(&intent).unwrap_err();
        assert!(
            matches!(err, ValidationError::ZeroBudget),
            "min_budget=0 must be rejected, got: {:?}",
            err
        );
    }

    #[test]
    fn test_nonzero_budget_accepted() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("execute".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: Some(1), // minimum acceptable
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        assert!(validate_intent(&intent).is_ok());
    }

    #[test]
    fn test_none_budget_accepted() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None, // no budget constraint -- acceptable
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        assert!(validate_intent(&intent).is_ok());
    }

    #[test]
    fn test_zero_min_fill_amount_rejected() {
        // ADVERSARIAL: An attacker creates fill constraints with min=0, allowing
        // zero-value fills that bypass economic requirements.
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
        let constraints = crate::FillConstraints {
            min_fill_amount: 0, // ATTACK: zero min allows zero-value fills
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
            generation: 0,
        };
        let intent = Intent::new_with_fill(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            9999,
            None,
            constraints,
        );
        let err = validate_intent(&intent).unwrap_err();
        assert!(
            matches!(err, ValidationError::InvalidFillConstraints(_)),
            "min_fill_amount=0 must be rejected, got: {:?}",
            err
        );
    }

    #[test]
    fn test_min_exceeds_max_fill_rejected() {
        // ADVERSARIAL: min > max is an invalid state that could cause logic errors.
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
        let constraints = crate::FillConstraints {
            min_fill_amount: 200, // ATTACK: min > max
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
            generation: 0,
        };
        let intent = Intent::new_with_fill(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            9999,
            None,
            constraints,
        );
        let err = validate_intent(&intent).unwrap_err();
        assert!(
            matches!(err, ValidationError::InvalidFillConstraints(_)),
            "min > max must be rejected, got: {:?}",
            err
        );
    }

    #[test]
    fn test_valid_fill_constraints_accepted() {
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
        let constraints = crate::FillConstraints {
            min_fill_amount: 10,
            max_fill_amount: 100,
            fill_or_kill: false,
            remaining_after_fill: None,
            generation: 0,
        };
        let intent = Intent::new_with_fill(
            IntentKind::Need,
            spec,
            CommitmentId([0xAA; 32]),
            9999,
            None,
            constraints,
        );
        assert!(validate_intent(&intent).is_ok());
    }

    // -------------------------------------------------------------------
    // Predicate requirement validation
    // -------------------------------------------------------------------

    fn pred(attribute: &str, ptype: &str, threshold: u64) -> crate::PredicateRequirement {
        crate::PredicateRequirement {
            attribute: attribute.into(),
            predicate_type: ptype.into(),
            threshold,
            upper_bound: None,
            state_root_freshness: 100,
        }
    }

    #[test]
    fn test_too_many_predicate_requirements_rejected() {
        let mut intent = make_valid_intent();
        intent.matcher.predicate_requirements = (0..(MAX_PREDICATE_REQUIREMENTS + 1))
            .map(|i| pred(&format!("attr_{i}"), "gte", 1))
            .collect();
        assert!(matches!(
            validate_intent(&intent),
            Err(ValidationError::TooManyPredicateRequirements { .. })
        ));
    }

    #[test]
    fn test_predicate_string_length_capped() {
        let mut intent = make_valid_intent();
        let long_name = "x".repeat(MAX_PREDICATE_STRING_LEN + 1);
        intent.matcher.predicate_requirements = vec![pred(&long_name, "gte", 1)];
        assert!(matches!(
            validate_intent(&intent),
            Err(ValidationError::PredicateStringTooLong { .. })
        ));
    }

    #[test]
    fn test_unknown_predicate_type_rejected() {
        let mut intent = make_valid_intent();
        intent.matcher.predicate_requirements = vec![pred("balance", "bogus_op", 100)];
        assert!(matches!(
            validate_intent(&intent),
            Err(ValidationError::UnknownPredicateType(_))
        ));
    }

    #[test]
    fn test_in_range_without_upper_bound_rejected() {
        let mut intent = make_valid_intent();
        // in_range with no upper_bound is structurally invalid.
        intent.matcher.predicate_requirements = vec![pred("balance", "in_range", 100)];
        assert!(matches!(
            validate_intent(&intent),
            Err(ValidationError::InvalidPredicateRange { .. })
        ));
    }

    #[test]
    fn test_in_range_with_valid_bounds_accepted() {
        let mut intent = make_valid_intent();
        intent.matcher.predicate_requirements = vec![crate::PredicateRequirement {
            attribute: "balance".into(),
            predicate_type: "in_range".into(),
            threshold: 100,
            upper_bound: Some(500),
            state_root_freshness: 100,
        }];
        assert!(validate_intent(&intent).is_ok());
    }
}
