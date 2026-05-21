//! Standalone trace verification.
//!
//! Verifies that a derivation trace is valid WITHOUT re-running evaluation.
//! This is the function that a ZK verifier circuit would replicate.

use crate::check;
use crate::eval::{Evaluator, predicates};
use crate::types::*;

/// Verify that an authorization trace is valid given the base facts and rules.
///
/// Checks performed for each derivation step:
/// 1. The rule ID references a valid rule.
/// 2. The substitution unifies with each body atom against the referenced fact.
/// 3. Each referenced body fact exists in the fact set at that point.
/// 4. All constraint checks pass under the substitution.
/// 5. The derived fact matches the rule head under the substitution.
/// 6. The final conclusion is consistent with the derived facts.
///
/// This does NOT verify completeness (that no other conclusion was possible),
/// only soundness (that the claimed derivation is valid).
pub fn verify_trace(facts: &[Fact], rules: &[Rule], trace: &AuthorizationTrace) -> bool {
    // Build up the fact set as we verify each step
    let mut known_facts: Vec<Fact> = facts.to_vec();

    // Inject request facts (same as the evaluator does)
    Evaluator::inject_request_facts(&mut known_facts, &trace.request);

    // Verify each derivation step
    for step in &trace.steps {
        if !verify_step(step, &known_facts, rules) {
            return false;
        }
        // Add the derived fact to our known set
        known_facts.push(step.derived_fact.clone());
    }

    // Verify the conclusion is consistent
    verify_conclusion(&known_facts, &trace.steps, &trace.conclusion)
}

/// Verify a single derivation step.
fn verify_step(step: &DerivationStep, known_facts: &[Fact], rules: &[Rule]) -> bool {
    // 1. Find the rule
    let Some(rule) = rules.iter().find(|r| r.id == step.rule_id) else {
        return false;
    };

    // 2. Check body atom count matches indices count
    if step.body_fact_indices.len() != rule.body.len() {
        return false;
    }

    // 3. For each body atom, verify the referenced fact exists and unifies
    let mut reconstructed_subst = Substitution::empty();

    for (body_atom, &fact_idx) in rule.body.iter().zip(step.body_fact_indices.iter()) {
        // Check the fact index is valid
        if fact_idx >= known_facts.len() {
            return false;
        }

        let fact = &known_facts[fact_idx];

        // Try to unify this body atom with the fact
        let Some(new_subst) =
            Evaluator::unify_atom_with_fact(body_atom, fact, &reconstructed_subst)
        else {
            return false;
        };
        reconstructed_subst = new_subst;
    }

    // 4. Verify the claimed substitution is consistent with what we reconstructed.
    if !substitutions_consistent(&step.substitution, &reconstructed_subst) {
        return false;
    }

    // 5. Check constraints pass
    if !rule
        .checks
        .iter()
        .all(|c| check::eval_check(c, &step.substitution))
    {
        return false;
    }

    // 6. Verify the derived fact matches the head under substitution
    let expected_atom = step.substitution.apply_atom(&rule.head);
    if expected_atom.predicate != step.derived_fact.predicate {
        return false;
    }
    if expected_atom.terms != step.derived_fact.terms {
        return false;
    }

    // 7. Verify the derived fact is ground
    if step
        .derived_fact
        .terms
        .iter()
        .any(|t| matches!(t, Term::Var(_)))
    {
        return false;
    }

    true
}

/// Check that two substitutions are consistent (no conflicting bindings)
/// and the claimed substitution does not contain extra unbound variables
/// that don't appear in the rule's body or head.
fn substitutions_consistent(claimed: &Substitution, reconstructed: &Substitution) -> bool {
    // All reconstructed bindings must match claimed bindings
    for (var, term) in &reconstructed.bindings {
        if let Some(claimed_term) = claimed.get(*var) {
            if claimed_term != term {
                return false;
            }
        }
    }
    // Reject extra variables in claimed substitution that were never bound
    // during reconstruction (i.e., variables not referenced by any body atom).
    for (var, _) in &claimed.bindings {
        if reconstructed.get(*var).is_none() {
            return false;
        }
    }
    true
}

/// Verify the conclusion is consistent with the derived facts.
///
/// A Deny conclusion is valid if:
/// - An explicit `deny` fact was derived (deny overrides allow), OR
/// - No `allow` fact exists in facts or steps.
///
/// An Allow conclusion is valid if:
/// - No `deny` fact was derived (deny always wins), AND
/// - An `allow` fact exists derived by the claimed rule.
fn verify_conclusion(facts: &[Fact], steps: &[DerivationStep], conclusion: &Conclusion) -> bool {
    let allow_pred = predicates::allow();
    let deny_pred = predicates::deny();

    // Check if any deny fact was derived or exists in base facts
    let has_deny = steps.iter().any(|s| s.derived_fact.predicate == deny_pred)
        || facts.iter().any(|f| f.predicate == deny_pred);

    match conclusion {
        Conclusion::Allow { policy_rule_id } => {
            // Deny always overrides allow — an Allow conclusion is invalid if deny exists
            if has_deny {
                return false;
            }
            // There must be an allow fact derived by the claimed rule
            let has_allow_in_steps = steps
                .iter()
                .any(|s| s.derived_fact.predicate == allow_pred && s.rule_id == *policy_rule_id);
            let has_allow_in_base =
                facts.iter().any(|f| f.predicate == allow_pred) && *policy_rule_id == 0;
            has_allow_in_steps || has_allow_in_base
        }
        Conclusion::Deny => {
            // Deny is valid if: explicit deny was derived, OR no allow exists
            if has_deny {
                return true;
            }
            let no_allow_in_facts = !facts.iter().any(|f| f.predicate == allow_pred);
            let no_allow_in_steps = !steps.iter().any(|s| s.derived_fact.predicate == allow_pred);
            no_allow_in_facts && no_allow_in_steps
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol_from_str;

    #[test]
    fn test_verify_empty_trace_deny() {
        let facts = vec![Fact::new(
            symbol_from_str("user"),
            vec![Term::Const(symbol_from_str("alice"))],
        )];
        let rules = vec![];
        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: Some(symbol_from_str("read")),
                features: vec![],
                user_id: Some(symbol_from_str("alice")),
                now: 1000,
            },
            steps: vec![],
            conclusion: Conclusion::Deny,
        };

        assert!(verify_trace(&facts, &rules, &trace));
    }

    #[test]
    fn test_verify_invalid_allow_conclusion() {
        let facts = vec![];
        let rules = vec![];
        // Claim allow but no allow fact exists
        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: Some(symbol_from_str("read")),
                features: vec![],
                user_id: None,
                now: 1000,
            },
            steps: vec![],
            conclusion: Conclusion::Allow { policy_rule_id: 1 },
        };

        assert!(!verify_trace(&facts, &rules, &trace));
    }

    #[test]
    fn test_verify_invalid_fact_index() {
        let rules = vec![Rule {
            id: 1,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![Atom {
                predicate: symbol_from_str("app"),
                terms: vec![Term::Var(0)],
            }],
            checks: vec![],
        }];

        let trace = AuthorizationTrace {
            request: AuthorizationRequest {
                app_id: None,
                service: None,
                action: None,
                features: vec![],
                user_id: None,
                now: 1000,
            },
            steps: vec![DerivationStep {
                rule_id: 1,
                substitution: Substitution::empty()
                    .extend(0, Term::Const(symbol_from_str("myapp")))
                    .unwrap(),
                body_fact_indices: vec![999], // invalid index
                derived_fact: Fact::new(symbol_from_str("allow"), vec![]),
            }],
            conclusion: Conclusion::Allow { policy_rule_id: 1 },
        };

        assert!(!verify_trace(&[], &rules, &trace));
    }
}
