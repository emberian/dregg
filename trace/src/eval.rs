//! Bottom-up Datalog evaluator with derivation trace recording.

use crate::check;
use crate::types::*;

/// The reference evaluator for the pyana authorization system.
///
/// Given a set of base facts and rules, the evaluator performs bottom-up (forward-chaining)
/// Datalog evaluation, recording every derivation step. It then checks if any "allow"
/// policy fires for the given request.
#[derive(Debug, Clone)]
pub struct Evaluator {
    /// The current set of known facts (base facts + derived facts).
    pub facts: Vec<Fact>,
    /// The rules to apply.
    pub rules: Vec<Rule>,
}

/// Well-known predicate symbols used by the evaluator.
pub mod predicates {
    use crate::types::{Symbol, symbol_from_str};

    pub fn allow() -> Symbol {
        symbol_from_str("allow")
    }

    pub fn deny() -> Symbol {
        symbol_from_str("deny")
    }

    pub fn request_app() -> Symbol {
        symbol_from_str("request_app")
    }

    pub fn request_service() -> Symbol {
        symbol_from_str("request_service")
    }

    pub fn request_action() -> Symbol {
        symbol_from_str("request_action")
    }

    pub fn request_feature() -> Symbol {
        symbol_from_str("request_feature")
    }

    pub fn request_user() -> Symbol {
        symbol_from_str("request_user")
    }

    pub fn request_time() -> Symbol {
        symbol_from_str("request_time")
    }
}

impl Evaluator {
    /// Create a new evaluator with the given base facts and rules.
    pub fn new(facts: Vec<Fact>, rules: Vec<Rule>) -> Self {
        Self { facts, rules }
    }

    /// Maximum number of evaluation rounds before the evaluator terminates.
    /// This prevents unbounded computation from pathological rule sets.
    const MAX_EVAL_ROUNDS: usize = 1000;

    /// Evaluate an authorization request, producing a complete derivation trace.
    ///
    /// The evaluation proceeds as follows:
    /// 1. Inject request facts (request_app, request_service, request_action, etc.)
    /// 2. Run bottom-up evaluation to fixpoint, recording each derivation step
    /// 3. Check if any `allow(...)` fact was derived
    /// 4. If so, conclude Allow with the rule that produced it; otherwise Deny
    ///
    /// The evaluation is bounded to [`Self::MAX_EVAL_ROUNDS`] iterations. If
    /// the bound is reached without achieving fixpoint, evaluation terminates
    /// and the current state is used (typically resulting in Deny).
    pub fn evaluate(&self, request: &AuthorizationRequest) -> AuthorizationTrace {
        let mut facts = self.facts.clone();
        let mut steps: Vec<DerivationStep> = Vec::new();

        // Inject request facts
        Self::inject_request_facts(&mut facts, request);

        // Bottom-up evaluation to fixpoint (bounded)
        let mut round = 0;
        loop {
            if round >= Self::MAX_EVAL_ROUNDS {
                break;
            }
            let new_steps = Self::derive_one_round(&self.rules, &facts);
            if new_steps.is_empty() {
                break;
            }
            for step in &new_steps {
                facts.push(step.derived_fact.clone());
            }
            steps.extend(new_steps);
            round += 1;
        }

        // Check for allow conclusions
        let conclusion = Self::find_conclusion(&facts, &steps);

        AuthorizationTrace {
            request: request.clone(),
            steps,
            conclusion,
        }
    }

    /// Inject facts representing the authorization request into the fact set.
    pub(crate) fn inject_request_facts(facts: &mut Vec<Fact>, request: &AuthorizationRequest) {
        if let Some(app_id) = &request.app_id {
            facts.push(Fact::new(
                predicates::request_app(),
                vec![Term::Const(*app_id)],
            ));
        }
        if let Some(service) = &request.service {
            facts.push(Fact::new(
                predicates::request_service(),
                vec![Term::Const(*service)],
            ));
        }
        if let Some(action) = &request.action {
            facts.push(Fact::new(
                predicates::request_action(),
                vec![Term::Const(*action)],
            ));
        }
        for feature in &request.features {
            facts.push(Fact::new(
                predicates::request_feature(),
                vec![Term::Const(*feature)],
            ));
        }
        if let Some(user_id) = &request.user_id {
            facts.push(Fact::new(
                predicates::request_user(),
                vec![Term::Const(*user_id)],
            ));
        }
        facts.push(Fact::new(
            predicates::request_time(),
            vec![Term::Int(request.now)],
        ));
    }

    /// Run one round of rule application, returning newly derived facts.
    fn derive_one_round(rules: &[Rule], facts: &[Fact]) -> Vec<DerivationStep> {
        let mut new_steps = Vec::new();

        for rule in rules {
            // Find all valid substitutions for this rule's body
            let substitutions = Self::find_all_substitutions(rule, facts);

            for (subst, body_indices) in substitutions {
                // Check constraints
                if !rule.checks.iter().all(|c| check::eval_check(c, &subst)) {
                    continue;
                }

                // Derive the head fact under this substitution
                let derived_atom = subst.apply_atom(&rule.head);

                // Ensure the derived fact is ground
                if derived_atom.terms.iter().any(|t| matches!(t, Term::Var(_))) {
                    continue;
                }

                let derived_fact = Fact {
                    predicate: derived_atom.predicate,
                    terms: derived_atom.terms,
                };

                // Only add if this fact is new
                if !facts.contains(&derived_fact)
                    && !new_steps
                        .iter()
                        .any(|s: &DerivationStep| s.derived_fact == derived_fact)
                {
                    new_steps.push(DerivationStep {
                        rule_id: rule.id,
                        substitution: subst,
                        body_fact_indices: body_indices,
                        derived_fact,
                    });
                }
            }
        }

        new_steps
    }

    /// Find all substitutions that satisfy all body atoms of a rule.
    /// Returns pairs of (substitution, body_fact_indices).
    fn find_all_substitutions(rule: &Rule, facts: &[Fact]) -> Vec<(Substitution, Vec<usize>)> {
        if rule.body.is_empty() {
            // A rule with no body always fires (unconditional).
            return vec![(Substitution::empty(), vec![])];
        }

        // Start with empty substitution and try to match each body atom in sequence
        let mut candidates: Vec<(Substitution, Vec<usize>)> =
            vec![(Substitution::empty(), Vec::new())];

        for body_atom in &rule.body {
            let mut next_candidates = Vec::new();

            for (subst, indices) in &candidates {
                // Try to unify this body atom with each fact
                for (fact_idx, fact) in facts.iter().enumerate() {
                    if let Some(new_subst) = Self::unify_atom_with_fact(body_atom, fact, subst) {
                        let mut new_indices = indices.clone();
                        new_indices.push(fact_idx);
                        next_candidates.push((new_subst, new_indices));
                    }
                }
            }

            candidates = next_candidates;
            if candidates.is_empty() {
                break;
            }
        }

        candidates
    }

    /// Try to unify an atom pattern with a concrete fact under the given substitution.
    /// Returns an extended substitution if successful, or `None` if unification fails.
    pub(crate) fn unify_atom_with_fact(
        atom: &Atom,
        fact: &Fact,
        subst: &Substitution,
    ) -> Option<Substitution> {
        // Predicates must match
        if atom.predicate != fact.predicate {
            return None;
        }

        // Arity must match
        if atom.terms.len() != fact.terms.len() {
            return None;
        }

        let mut current = subst.clone();

        for (atom_term, fact_term) in atom.terms.iter().zip(fact.terms.iter()) {
            let resolved = current.apply_term(atom_term);
            match &resolved {
                Term::Var(v) => {
                    // Try to bind this variable
                    current = current.extend(*v, fact_term.clone())?;
                }
                Term::Const(c) => {
                    // Must match exactly
                    match fact_term {
                        Term::Const(fc) if fc == c => {}
                        _ => return None,
                    }
                }
                Term::Int(i) => {
                    // Must match exactly
                    match fact_term {
                        Term::Int(fi) if fi == i => {}
                        _ => return None,
                    }
                }
            }
        }

        Some(current)
    }

    /// Determine the conclusion by scanning derived facts for allow/deny.
    ///
    /// If any `deny` fact was derived, the conclusion is always Deny regardless
    /// of whether `allow` was also derived. Deny takes precedence over allow.
    fn find_conclusion(facts: &[Fact], steps: &[DerivationStep]) -> Conclusion {
        let allow_pred = predicates::allow();
        let deny_pred = predicates::deny();

        // Check for explicit deny first — deny always wins over allow.
        for step in steps {
            if step.derived_fact.predicate == deny_pred {
                return Conclusion::Deny;
            }
        }
        for fact in facts {
            if fact.predicate == deny_pred {
                return Conclusion::Deny;
            }
        }

        // Look for any allow fact — return the rule that derived it
        for step in steps {
            if step.derived_fact.predicate == allow_pred {
                return Conclusion::Allow {
                    policy_rule_id: step.rule_id,
                };
            }
        }

        // Check base facts too (though unusual)
        for fact in facts {
            if fact.predicate == allow_pred {
                // No associated rule for base facts, use 0
                return Conclusion::Allow { policy_rule_id: 0 };
            }
        }

        Conclusion::Deny
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol_from_str;

    #[test]
    fn test_unify_simple() {
        let atom = Atom {
            predicate: symbol_from_str("app"),
            terms: vec![Term::Var(0), Term::Var(1)],
        };
        let fact = Fact::new(
            symbol_from_str("app"),
            vec![
                Term::Const(symbol_from_str("myapp")),
                Term::Const(symbol_from_str("read")),
            ],
        );

        let result = Evaluator::unify_atom_with_fact(&atom, &fact, &Substitution::empty());
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get(0), Some(&Term::Const(symbol_from_str("myapp"))));
        assert_eq!(subst.get(1), Some(&Term::Const(symbol_from_str("read"))));
    }

    #[test]
    fn test_unify_mismatch_predicate() {
        let atom = Atom {
            predicate: symbol_from_str("app"),
            terms: vec![Term::Const(symbol_from_str("myapp"))],
        };
        let fact = Fact::new(
            symbol_from_str("service"),
            vec![Term::Const(symbol_from_str("myapp"))],
        );

        let result = Evaluator::unify_atom_with_fact(&atom, &fact, &Substitution::empty());
        assert!(result.is_none());
    }

    #[test]
    fn test_unify_mismatch_const() {
        let atom = Atom {
            predicate: symbol_from_str("app"),
            terms: vec![Term::Const(symbol_from_str("myapp"))],
        };
        let fact = Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("other"))],
        );

        let result = Evaluator::unify_atom_with_fact(&atom, &fact, &Substitution::empty());
        assert!(result.is_none());
    }

    #[test]
    fn test_unify_with_existing_binding() {
        let atom = Atom {
            predicate: symbol_from_str("app"),
            terms: vec![Term::Var(0)],
        };
        let fact = Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        );

        // Pre-bind var 0 to "myapp" — should still unify
        let subst = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("myapp")))
            .unwrap();
        let result = Evaluator::unify_atom_with_fact(&atom, &fact, &subst);
        assert!(result.is_some());

        // Pre-bind var 0 to "other" — should fail
        let subst2 = Substitution::empty()
            .extend(0, Term::Const(symbol_from_str("other")))
            .unwrap();
        let result2 = Evaluator::unify_atom_with_fact(&atom, &fact, &subst2);
        assert!(result2.is_none());
    }

    #[test]
    fn test_simple_derivation() {
        // Rule: allow() :- app($x), request_app($x).
        let rule = Rule {
            id: 1,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        };

        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];

        let eval = Evaluator::new(facts, vec![rule]);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str("myapp")),
            service: None,
            action: None,
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });
        assert_eq!(trace.steps.len(), 1);
    }

    #[test]
    fn test_no_matching_rule_denies() {
        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![Term::Const(symbol_from_str("myapp"))],
        )];

        let eval = Evaluator::new(facts, vec![]);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str("other")),
            service: None,
            action: None,
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(trace.conclusion, Conclusion::Deny);
        assert!(trace.steps.is_empty());
    }
}
