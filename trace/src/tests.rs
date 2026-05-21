//! Integration tests for the pyana-trace crate.

use crate::eval::Evaluator;
use crate::policy::{minimal_policy, rule_ids, time_bounded_policy};
use crate::types::*;
use crate::verify::verify_trace;

// =============================================================================
// Helper functions
// =============================================================================

fn sym(s: &str) -> Symbol {
    symbol_from_str(s)
}

/// Raw symbol from literal bytes (zero-padded). Used for backward-compat
/// tests of the deprecated `Contains` check, which requires the literal
/// byte representation for substring matching.
fn raw_sym(s: &str) -> Symbol {
    symbol_from_bytes(s.as_bytes())
}

/// App fact for Contains-based policy tests.
/// Uses hashed predicates (to match minimal_policy rules) but raw byte
/// terms for app_id and actions (so Contains substring matching works).
fn app_fact(app_id: &str, actions: &str) -> Fact {
    Fact::new(
        sym("app"),
        vec![Term::Const(raw_sym(app_id)), Term::Const(raw_sym(actions))],
    )
}

/// Service fact for Contains-based policy tests.
fn service_fact(svc: &str, actions: &str) -> Fact {
    Fact::new(
        sym("service"),
        vec![Term::Const(raw_sym(svc)), Term::Const(raw_sym(actions))],
    )
}

fn unrestricted_fact() -> Fact {
    Fact::new(sym("unrestricted"), vec![Term::Int(1)])
}

fn valid_until_fact(expiry: i64) -> Fact {
    Fact::new(sym("valid_until"), vec![Term::Int(expiry)])
}

/// Make a request using raw byte symbols (for Contains-based policy tests).
/// The terms must match the raw_sym encoding used in app_fact/service_fact.
fn make_request(
    app_id: Option<&str>,
    service: Option<&str>,
    action: Option<&str>,
    now: i64,
) -> AuthorizationRequest {
    AuthorizationRequest {
        app_id: app_id.map(raw_sym),
        service: service.map(raw_sym),
        action: action.map(raw_sym),
        features: vec![],
        user_id: None,
        now,
    }
}

/// Make a request using hashed symbols (for MemberOf/custom rule tests
/// that don't use Contains substring matching).
fn make_hashed_request(
    app_id: Option<&str>,
    service: Option<&str>,
    action: Option<&str>,
    now: i64,
) -> AuthorizationRequest {
    AuthorizationRequest {
        app_id: app_id.map(sym),
        service: service.map(sym),
        action: action.map(sym),
        features: vec![],
        user_id: None,
        now,
    }
}

// =============================================================================
// Simple authorization tests
// =============================================================================

#[test]
fn test_app_action_allow() {
    let rules = minimal_policy();
    let facts = vec![app_fact("dashboard", "read,write,delete")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("dashboard"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(!trace.steps.is_empty());

    // Verify the trace
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_app_action_allow_write() {
    let rules = minimal_policy();
    let facts = vec![app_fact("dashboard", "read,write,delete")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("dashboard"), None, Some("write"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_service_action_allow() {
    let rules = minimal_policy();
    let facts = vec![service_fact("storage", "upload,download")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(None, Some("storage"), Some("upload"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::SERVICE_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_unrestricted_allow() {
    let rules = minimal_policy();
    let facts = vec![unrestricted_fact()];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(None, None, Some("anything_at_all"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::UNRESTRICTED,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Denial tests
// =============================================================================

#[test]
fn test_deny_wrong_app() {
    let rules = minimal_policy();
    let facts = vec![app_fact("dashboard", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("admin"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(trace.steps.is_empty());
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_deny_wrong_action() {
    let rules = minimal_policy();
    let facts = vec![app_fact("dashboard", "read")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("dashboard"), None, Some("delete"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_deny_no_facts() {
    let rules = minimal_policy();
    let facts = vec![];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("dashboard"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_deny_no_rules() {
    let facts = vec![app_fact("dashboard", "read")];
    let rules = vec![];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("dashboard"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_deny_unrestricted_but_no_action() {
    let rules = minimal_policy();
    let facts = vec![unrestricted_fact()];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    // No action in request — the unrestricted rule requires request_action to exist
    let request = make_request(None, None, None, 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Multi-step derivation tests
// =============================================================================

#[test]
fn test_multi_step_derived_facts() {
    // Set up a scenario with intermediate derived facts.
    // Rule A: derived_access($app) :- app($app, $actions), has_role($role), role_grant($role, $app)
    // Rule B: allow() :- derived_access($app), request_app($app), request_action($act)
    let rule_a = Rule {
        id: 100,
        head: Atom {
            predicate: sym("derived_access"),
            terms: vec![Term::Var(0)],
        },
        body: vec![
            Atom {
                predicate: sym("app"),
                terms: vec![Term::Var(0), Term::Var(1)],
            },
            Atom {
                predicate: sym("has_role"),
                terms: vec![Term::Var(2)],
            },
            Atom {
                predicate: sym("role_grant"),
                terms: vec![Term::Var(2), Term::Var(0)],
            },
        ],
        checks: vec![],
    };

    let rule_b = Rule {
        id: 101,
        head: Atom {
            predicate: sym("allow"),
            terms: vec![],
        },
        body: vec![
            Atom {
                predicate: sym("derived_access"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: sym("request_app"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: sym("request_action"),
                terms: vec![Term::Var(1)],
            },
        ],
        checks: vec![],
    };

    let facts = vec![
        Fact::new(
            sym("app"),
            vec![Term::Const(sym("dashboard")), Term::Const(sym("read,write"))],
        ),
        Fact::new(sym("has_role"), vec![Term::Const(sym("admin"))]),
        Fact::new(
            sym("role_grant"),
            vec![Term::Const(sym("admin")), Term::Const(sym("dashboard"))],
        ),
    ];

    let rules = vec![rule_a, rule_b];
    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_hashed_request(Some("dashboard"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);

    // Should have 2 steps: first derives derived_access(dashboard), then allow()
    assert_eq!(trace.steps.len(), 2);
    assert_eq!(trace.steps[0].rule_id, 100);
    assert_eq!(trace.steps[0].derived_fact.predicate, sym("derived_access"));
    assert_eq!(trace.steps[1].rule_id, 101);
    assert_eq!(trace.steps[1].derived_fact.predicate, sym("allow"));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: 101,
        }
    );

    // Verify the trace
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_transitive_derivation() {
    // Rule: can_access($x) :- can_access($y), delegates($y, $x)
    // Rule: allow() :- can_access($app), request_app($app)
    let rules = vec![
        Rule {
            id: 200,
            head: Atom {
                predicate: sym("can_access"),
                terms: vec![Term::Var(1)],
            },
            body: vec![
                Atom {
                    predicate: sym("can_access"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: sym("delegates"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
            ],
            checks: vec![],
        },
        Rule {
            id: 201,
            head: Atom {
                predicate: sym("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: sym("can_access"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: sym("request_app"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        },
    ];

    let facts = vec![
        // Base: can_access(A)
        Fact::new(sym("can_access"), vec![Term::Const(sym("A"))]),
        // A delegates to B
        Fact::new(
            sym("delegates"),
            vec![Term::Const(sym("A")), Term::Const(sym("B"))],
        ),
        // B delegates to C
        Fact::new(
            sym("delegates"),
            vec![Term::Const(sym("B")), Term::Const(sym("C"))],
        ),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_hashed_request(Some("C"), None, None, 1000);

    let trace = eval.evaluate(&request);

    // Should derive: can_access(B), can_access(C), allow()
    assert_eq!(trace.steps.len(), 3);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: 201,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Time-bounded tests
// =============================================================================

#[test]
fn test_time_bounded_allow_before_expiry() {
    let rules = time_bounded_policy();
    let facts = vec![
        app_fact("api", "read,write"),
        valid_until_fact(2_000_000_000), // expires far in the future
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION_TIME_BOUNDED,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_time_bounded_deny_after_expiry() {
    let rules = time_bounded_policy();
    let facts = vec![
        app_fact("api", "read,write"),
        valid_until_fact(1_600_000_000), // already expired
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    // The time_bounded_policy correctly binds request_time via body atom
    // request_time(Var(4)). Since now (1_700_000_000) > valid_until (1_600_000_000),
    // the LessThan(Var(4), Var(3)) check fails and the rule does not fire.
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Trace verification tests
// =============================================================================

#[test]
fn test_verify_valid_trace() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_tampered_derived_fact() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Tamper with the derived fact
    if let Some(step) = trace.steps.last_mut() {
        step.derived_fact = Fact::new(sym("hacked"), vec![]);
    }

    // Verification should fail (derived fact doesn't match head under substitution)
    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_tampered_substitution() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Tamper with the substitution — change the app binding
    if let Some(step) = trace.steps.first_mut() {
        step.substitution = Substitution::empty()
            .extend(0, Term::Const(sym("evil_app")))
            .unwrap()
            .extend(1, Term::Const(sym("read,write")))
            .unwrap()
            .extend(2, Term::Const(sym("read")))
            .unwrap();
    }

    // Verification should fail (substitution doesn't match the body facts)
    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_tampered_body_indices() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write"), app_fact("other", "delete")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Tamper with body fact indices — point to a different fact
    if let Some(step) = trace.steps.first_mut() {
        if !step.body_fact_indices.is_empty() {
            step.body_fact_indices[0] = 1; // point to "other" app instead
        }
    }

    // Verification should fail
    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_tampered_conclusion_allow_to_deny() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Tamper: claim deny even though allow was derived
    trace.conclusion = Conclusion::Deny;

    // Verification should fail (allow fact exists but conclusion says deny)
    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_tampered_conclusion_deny_to_allow() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read")]; // only read

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("delete"), 1000); // denied

    let mut trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);

    // Tamper: claim allow
    trace.conclusion = Conclusion::Allow { policy_rule_id: 1 };

    // Verification should fail (no allow fact was derived)
    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_invalid_rule_id() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);

    // Tamper: change the rule_id to a nonexistent rule
    if let Some(step) = trace.steps.first_mut() {
        step.rule_id = 999;
    }

    assert!(!verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_verify_out_of_bounds_fact_index() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let mut trace = eval.evaluate(&request);

    // Tamper: set a body fact index out of bounds
    if let Some(step) = trace.steps.first_mut() {
        if !step.body_fact_indices.is_empty() {
            step.body_fact_indices[0] = 9999;
        }
    }

    assert!(!verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Standard policy set tests
// =============================================================================

#[test]
fn test_standard_policy_app_read() {
    let rules = minimal_policy();
    let facts = vec![app_fact("billing", "read,list")];

    let eval = Evaluator::new(facts.clone(), rules.clone());

    // Should allow "read"
    let trace = eval.evaluate(&make_request(Some("billing"), None, Some("read"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));

    // Should allow "list"
    let trace = eval.evaluate(&make_request(Some("billing"), None, Some("list"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));

    // Should deny "write"
    let trace = eval.evaluate(&make_request(Some("billing"), None, Some("write"), 1000));
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_standard_policy_service_scope() {
    let rules = minimal_policy();
    let facts = vec![service_fact("s3", "get,put,list")];

    let eval = Evaluator::new(facts.clone(), rules.clone());

    let trace = eval.evaluate(&make_request(None, Some("s3"), Some("put"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::SERVICE_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_standard_policy_multiple_apps() {
    let rules = minimal_policy();
    let facts = vec![
        app_fact("dashboard", "read,write"),
        app_fact("admin", "read,write,delete,manage"),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());

    // dashboard + read = allow
    let trace = eval.evaluate(&make_request(Some("dashboard"), None, Some("read"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));

    // dashboard + delete = deny (only admin has delete)
    let trace = eval.evaluate(&make_request(Some("dashboard"), None, Some("delete"), 1000));
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));

    // admin + manage = allow
    let trace = eval.evaluate(&make_request(Some("admin"), None, Some("manage"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_standard_policy_combined_app_and_service() {
    let rules = minimal_policy();
    let facts = vec![
        app_fact("myapp", "read"),
        service_fact("compute", "launch,terminate"),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());

    // App match
    let trace = eval.evaluate(&make_request(Some("myapp"), None, Some("read"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));

    // Service match
    let trace = eval.evaluate(&make_request(None, Some("compute"), Some("launch"), 1000));
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::SERVICE_ACTION,
        }
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_empty_request() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: None,
        service: None,
        action: None,
        features: vec![],
        user_id: None,
        now: 0,
    };

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_substitution_extend_conflict() {
    let subst = Substitution::empty()
        .extend(0, Term::Const(sym("hello")))
        .unwrap();

    // Same binding is fine
    let same = subst.extend(0, Term::Const(sym("hello")));
    assert!(same.is_some());

    // Different binding conflicts
    let conflict = subst.extend(0, Term::Const(sym("world")));
    assert!(conflict.is_none());
}

#[test]
fn test_fact_ground_assertion() {
    // Facts with variables should be caught in debug mode
    let fact = Fact {
        predicate: sym("test"),
        terms: vec![Term::Const(sym("hello"))],
    };
    assert_eq!(fact.terms.len(), 1);
}

#[test]
fn test_symbol_from_str_deterministic() {
    let s1 = sym("hi");
    let s2 = sym("hi");
    assert_eq!(s1, s2);
}

#[test]
fn test_symbol_from_str_different_inputs() {
    let s1 = sym("hi");
    let s2 = sym("hello");
    assert_ne!(s1, s2);
}

#[test]
fn test_symbol_from_str_long_strings_no_collision() {
    // Two strings sharing a 32-byte prefix must produce different symbols
    // (the old truncation-based impl would have produced identical symbols)
    let a = "this_is_a_32_byte_prefix_exactly_AAAA";
    let b = "this_is_a_32_byte_prefix_exactly_BBBB";
    assert_ne!(sym(a), sym(b));
}

#[test]
fn test_multiple_rules_first_match_wins() {
    // Both app-action and unrestricted could fire. The first derivation wins.
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read"), unrestricted_fact()];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    // Should allow (either rule 1 or rule 3 fires first)
    match trace.conclusion {
        Conclusion::Allow { policy_rule_id } => {
            assert!(
                policy_rule_id == rule_ids::APP_ACTION || policy_rule_id == rule_ids::UNRESTRICTED
            );
        }
        Conclusion::Deny => panic!("expected Allow"),
    }
    assert!(verify_trace(&facts, &rules, &trace));
}

#[test]
fn test_fixpoint_terminates() {
    // Ensure evaluation terminates even with self-referential rules
    // Rule: foo($x) :- bar($x)
    // Rule: bar($x) :- foo($x)
    // Base: foo(a)
    // Should derive bar(a) and then stop (fixpoint reached, no new facts).
    let rules = vec![
        Rule {
            id: 1,
            head: Atom {
                predicate: sym("bar"),
                terms: vec![Term::Var(0)],
            },
            body: vec![Atom {
                predicate: sym("foo"),
                terms: vec![Term::Var(0)],
            }],
            checks: vec![],
        },
        Rule {
            id: 2,
            head: Atom {
                predicate: sym("foo"),
                terms: vec![Term::Var(0)],
            },
            body: vec![Atom {
                predicate: sym("bar"),
                terms: vec![Term::Var(0)],
            }],
            checks: vec![],
        },
    ];
    let facts = vec![Fact::new(sym("foo"), vec![Term::Const(sym("a"))])];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(None, None, None, 0);

    let trace = eval.evaluate(&request);
    // Should terminate with bar(a) derived, but no allow
    assert_eq!(trace.conclusion, Conclusion::Deny);
    // Should have derived bar(a) and attempted foo(a) again (but it already exists)
    assert!(
        trace
            .steps
            .iter()
            .any(|s| s.derived_fact == Fact::new(sym("bar"), vec![Term::Const(sym("a"))]))
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

// =============================================================================
// Serialization tests
// =============================================================================

#[test]
fn test_trace_serialization_roundtrip() {
    let rules = minimal_policy();
    let facts = vec![app_fact("myapp", "read,write")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("myapp"), None, Some("read"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 1 });

    // Serialize to JSON
    let json = serde_json::to_string(&trace).expect("serialize");
    // Deserialize back
    let restored: AuthorizationTrace = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(trace, restored);
    // Verify the restored trace
    assert!(verify_trace(&facts, &rules, &restored));
}

#[test]
fn test_rule_serialization() {
    let rules = minimal_policy();
    let json = serde_json::to_string(&rules).expect("serialize rules");
    let restored: Vec<Rule> = serde_json::from_str(&json).expect("deserialize rules");
    assert_eq!(rules, restored);
}

// =============================================================================
// Constraint check integration tests
// =============================================================================

#[test]
fn test_rule_with_equality_check() {
    // Rule: allow() :- user($uid), request_user($uid), user_status($uid, $status)
    //   check: $status == "active"
    let rules = vec![Rule {
        id: 50,
        head: Atom {
            predicate: sym("allow"),
            terms: vec![],
        },
        body: vec![
            Atom {
                predicate: sym("user"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: sym("request_user"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: sym("user_status"),
                terms: vec![Term::Var(0), Term::Var(1)],
            },
        ],
        checks: vec![Check::Equal(Term::Var(1), Term::Const(sym("active")))],
    }];

    // Active user
    let facts = vec![
        Fact::new(sym("user"), vec![Term::Const(sym("alice"))]),
        Fact::new(
            sym("user_status"),
            vec![Term::Const(sym("alice")), Term::Const(sym("active"))],
        ),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = AuthorizationRequest {
        app_id: None,
        service: None,
        action: None,
        features: vec![],
        user_id: Some(sym("alice")),
        now: 1000,
    };

    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 50 });
    assert!(verify_trace(&facts, &rules, &trace));

    // Suspended user
    let facts_suspended = vec![
        Fact::new(sym("user"), vec![Term::Const(sym("bob"))]),
        Fact::new(
            sym("user_status"),
            vec![Term::Const(sym("bob")), Term::Const(sym("suspended"))],
        ),
    ];

    let eval2 = Evaluator::new(facts_suspended.clone(), rules.clone());
    let request2 = AuthorizationRequest {
        app_id: None,
        service: None,
        action: None,
        features: vec![],
        user_id: Some(sym("bob")),
        now: 1000,
    };

    let trace2 = eval2.evaluate(&request2);
    assert_eq!(trace2.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts_suspended, &rules, &trace2));
}

#[test]
fn test_rule_with_greater_than_check() {
    // Rule: allow() :- request_action($act), reputation($score)
    //   check: $score > 100
    let rules = vec![Rule {
        id: 60,
        head: Atom {
            predicate: sym("allow"),
            terms: vec![],
        },
        body: vec![
            Atom {
                predicate: sym("request_action"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: sym("reputation"),
                terms: vec![Term::Var(1)],
            },
        ],
        checks: vec![Check::GreaterThan(Term::Var(1), Term::Int(100))],
    }];

    // High reputation
    let facts = vec![Fact::new(sym("reputation"), vec![Term::Int(500)])];
    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(None, None, Some("post"), 1000);
    let trace = eval.evaluate(&request);
    assert_eq!(trace.conclusion, Conclusion::Allow { policy_rule_id: 60 });
    assert!(verify_trace(&facts, &rules, &trace));

    // Low reputation
    let facts_low = vec![Fact::new(sym("reputation"), vec![Term::Int(50)])];
    let eval2 = Evaluator::new(facts_low.clone(), rules.clone());
    let trace2 = eval2.evaluate(&request);
    assert_eq!(trace2.conclusion, Conclusion::Deny);
    assert!(verify_trace(&facts_low, &rules, &trace2));
}

// =============================================================================
// Bug fix verification tests
// =============================================================================

/// Bug 1/2 fix: Verify that time-bounded rules in legacy_policy correctly bind
/// request_time and enforce expiry. Previously, Rules 10/11 had no request_time
/// body atom and no LessThan check, making them ignore token expiry entirely.
///
/// We test with ONLY the time-bounded rule (isolating it from Rule 1 which
/// would fire regardless of time). This proves the rule itself works.
#[test]
#[allow(deprecated)]
fn test_legacy_time_bounded_denies_after_expiry() {
    use crate::policy::legacy_policy;

    // Extract only the time-bounded rule to test it in isolation
    let rules: Vec<_> = legacy_policy()
        .into_iter()
        .filter(|r| r.id == rule_ids::APP_ACTION_TIME_BOUNDED)
        .collect();
    assert_eq!(
        rules.len(),
        1,
        "Should have exactly one time-bounded app rule"
    );

    let facts = vec![
        app_fact("api", "read,write"),
        valid_until_fact(1_600_000_000), // already expired
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    // Request at time AFTER expiry
    let request = make_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    // Rule 10 must NOT fire (time check fails: 1_700_000_000 < 1_600_000_000 is false)
    assert_eq!(
        trace.conclusion,
        Conclusion::Deny,
        "BUG FIX: time-bounded rule must deny after token expiry"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 1/2 fix: Verify that time-bounded rules allow access BEFORE expiry.
#[test]
#[allow(deprecated)]
fn test_legacy_time_bounded_allows_before_expiry() {
    use crate::policy::legacy_policy;

    // Extract only the time-bounded rule to test it in isolation
    let rules: Vec<_> = legacy_policy()
        .into_iter()
        .filter(|r| r.id == rule_ids::APP_ACTION_TIME_BOUNDED)
        .collect();

    let facts = vec![
        app_fact("api", "read,write"),
        valid_until_fact(2_000_000_000), // expires far in the future
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    // Rule 10 fires because time is before expiry AND action matches
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION_TIME_BOUNDED,
        },
        "BUG FIX: time-bounded rule must fire when token is not yet expired"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 2 fix: Verify time expiry in the new standard_policy (secure, MemberOf-based).
/// Isolates the time-bounded rule to prove it correctly denies expired tokens.
#[test]
fn test_standard_policy_time_bounded_denies_after_expiry() {
    use crate::policy::standard_policy;

    // Extract only the time-bounded rule to test in isolation
    let rules: Vec<_> = standard_policy()
        .into_iter()
        .filter(|r| r.id == rule_ids::APP_ACTION_TIME_BOUNDED)
        .collect();
    assert_eq!(rules.len(), 1);

    let facts = vec![
        // Per-action facts (secure model)
        Fact::new(
            sym("action_allowed"),
            vec![Term::Const(sym("api")), Term::Const(sym("read"))],
        ),
        valid_until_fact(1_600_000_000), // already expired
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_hashed_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    // Time-bounded rule must NOT fire — token is expired
    assert_eq!(
        trace.conclusion,
        Conclusion::Deny,
        "Time-bounded rule must deny after expiry (request_time >= valid_until)"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 2 fix: Verify time-bounded rule fires before expiry in standard_policy.
#[test]
fn test_standard_policy_time_bounded_allows_before_expiry() {
    use crate::policy::standard_policy;

    // Extract only the time-bounded rule to test in isolation
    let rules: Vec<_> = standard_policy()
        .into_iter()
        .filter(|r| r.id == rule_ids::APP_ACTION_TIME_BOUNDED)
        .collect();

    let facts = vec![
        Fact::new(
            sym("action_allowed"),
            vec![Term::Const(sym("api")), Term::Const(sym("read"))],
        ),
        valid_until_fact(2_000_000_000), // far future
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_hashed_request(Some("api"), None, Some("read"), 1_700_000_000);

    let trace = eval.evaluate(&request);
    // Time-bounded rule fires: action matches AND time < expiry
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION_TIME_BOUNDED,
        },
        "Time-bounded rule must fire when token is not yet expired"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 3 fix: Verify that "threadwrite" does NOT match "write" in the new
/// standard_policy. The old Contains-based policy had a substring vulnerability.
#[test]
fn test_standard_policy_no_substring_vulnerability() {
    use crate::policy::standard_policy;

    let rules = standard_policy();
    // Only "write" is allowed for "my-app" (as a per-action fact).
    let facts = vec![Fact::new(
        sym("action_allowed"),
        vec![Term::Const(sym("my-app")), Term::Const(sym("write"))],
    )];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    // Request "threadwrite" — must NOT match "write" in the secure policy.
    let request = make_hashed_request(Some("my-app"), None, Some("threadwrite"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Deny,
        "SECURITY: 'threadwrite' must NOT match 'write' in standard_policy (MemberOf-based)"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 3 fix: Verify standard_policy correctly allows exact action match.
#[test]
fn test_standard_policy_exact_action_match() {
    use crate::policy::standard_policy;

    let rules = standard_policy();
    let facts = vec![
        Fact::new(
            sym("action_allowed"),
            vec![Term::Const(sym("my-app")), Term::Const(sym("write"))],
        ),
        Fact::new(
            sym("action_allowed"),
            vec![Term::Const(sym("my-app")), Term::Const(sym("read"))],
        ),
    ];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    let request = make_hashed_request(Some("my-app"), None, Some("write"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION_SECURE,
        },
        "Exact action match must be allowed in standard_policy"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}

/// Bug 3 fix: Contrast with legacy policy showing the vulnerability still exists there.
#[test]
#[allow(deprecated)]
fn test_legacy_policy_substring_vulnerability_still_exists() {
    use crate::policy::legacy_policy;

    let rules = legacy_policy();
    // The app has action string "threadwrite" which contains "write" as substring.
    let facts = vec![app_fact("my-app", "threadwrite")];

    let eval = Evaluator::new(facts.clone(), rules.clone());
    // Request "write" — incorrectly matches via substring in legacy policy.
    let request = make_request(Some("my-app"), None, Some("write"), 1000);

    let trace = eval.evaluate(&request);
    assert_eq!(
        trace.conclusion,
        Conclusion::Allow {
            policy_rule_id: rule_ids::APP_ACTION,
        },
        "KNOWN VULNERABILITY: legacy_policy allows substring matches"
    );
    assert!(verify_trace(&facts, &rules, &trace));
}
