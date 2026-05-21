//! Input validation for intents.
//!
//! Prevents spam and denial-of-service by enforcing size limits on intent fields.
//! All validation runs before storing or propagating an intent.

use crate::{Constraint, Intent};

/// Maximum number of action patterns per intent.
pub const MAX_ACTIONS: usize = 64;

/// Maximum number of constraints per intent.
pub const MAX_CONSTRAINTS: usize = 64;

/// Maximum length of any string field in an intent (action names, resource patterns, etc.).
pub const MAX_STRING_LEN: usize = 256;

/// Maximum length of a resource pattern.
pub const MAX_RESOURCE_PATTERN_LEN: usize = 256;

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
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0xAA; 32]), 9999, None);
        assert!(validate_intent(&intent).is_ok());
    }
}
