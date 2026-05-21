//! Standard policy set for the pyana authorization model.
//!
//! Provides pre-built rules matching the pyana authorization semantics:
//! - App-scoped access: allow if the request app has the requested action
//! - Service-scoped access: allow if the request service has the requested action
//! - Unrestricted access: allow if the token grants unrestricted access
//! - Default deny: if no allow fires, deny

use crate::types::*;

/// Standard policy rule IDs.
pub mod rule_ids {
    /// allow if app($app, $actions), request_app($app), request_action($act), $actions.contains($act)
    pub const APP_ACTION: u32 = 1;
    /// allow if service($svc, $actions), request_service($svc), request_action($act), $actions.contains($act)
    pub const SERVICE_ACTION: u32 = 2;
    /// allow if unrestricted(true), request_action($act)
    pub const UNRESTRICTED: u32 = 3;
    /// allow if app($app, $actions), request_app($app) [no action constraint]
    pub const APP_ANY_ACTION: u32 = 4;
    /// allow if service($svc, $actions), request_service($svc) [no action constraint]
    pub const SERVICE_ANY_ACTION: u32 = 5;
    /// Time-bounded: allow if app($app, $actions), request_app($app), request_action($act),
    ///   $actions.contains($act), valid_until($exp), request_time($t), $t < $exp
    pub const APP_ACTION_TIME_BOUNDED: u32 = 10;
    /// Time-bounded service: similar to above for services
    pub const SERVICE_ACTION_TIME_BOUNDED: u32 = 11;
    /// budget_ok(B) :- budget_remaining(B, R), request_cost(C), R >= C
    pub const BUDGET_OK: u32 = 20;
    /// deny :- budget_enrolled(B), NOT budget_ok(B) — modeled as explicit deny derivation
    /// (In practice, absence of budget_ok blocks the allow rules via a guard.)
    pub const BUDGET_DENY: u32 = 21;
    /// not_revoked_ok(T) :- not_revoked(T)
    pub const REVOCATION_OK: u32 = 30;
    /// deny :- revocable(T), NOT not_revoked(T)
    pub const REVOCATION_DENY: u32 = 31;
    /// SECURE: allow if action_allowed($app, $act_hash), request_app($app), request_action($act_hash)
    ///   check: MemberOf($act_hash, $act_hash)  [belt-and-suspenders: unification already guarantees this]
    pub const APP_ACTION_SECURE: u32 = 40;
    /// SECURE: allow if svc_action_allowed($svc, $act_hash), request_service($svc), request_action($act_hash)
    ///   check: MemberOf($act_hash, $act_hash)
    pub const SERVICE_ACTION_SECURE: u32 = 41;
}

/// Returns the standard pyana authorization policy rule set.
///
/// This is the **secure** policy that uses exact hash matching (`MemberOf`)
/// instead of substring matching (`Contains`). It expects per-action facts:
///
/// - `action_allowed(app_id, action)` — one fact per allowed action per app
/// - `svc_action_allowed(service_id, action)` — one fact per allowed action per service
///
/// Rules included:
/// - **App + Action (secure)**: MemberOf-based exact action matching
/// - **Service + Action (secure)**: Same for services
/// - **Unrestricted**: If `unrestricted(true)` exists, allow any action
/// - **Time-bounded app + action**: Checks expiry via `request_time < valid_until`
/// - **Time-bounded service + action**: Same for services
/// - **Budget**: Derives `budget_ok` or `deny` based on remaining budget vs cost
/// - **Revocation**: Derives `deny` if token is revoked
///
/// For backward compatibility with comma-separated action facts, see [`legacy_policy()`].
pub fn standard_policy() -> Vec<Rule> {
    let mut rules = vec![
        // Rule 40: allow if action_allowed($app, $act), request_app($app), request_action($act)
        //   check: MemberOf($act, $act) [explicit equality for ZK]
        Rule {
            id: rule_ids::APP_ACTION_SECURE,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $app, $act
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)], // $app
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act (must unify with action_allowed)
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)), // explicit equality for ZK
            ],
        },
        // Rule 41: allow if svc_action_allowed($svc, $act), request_service($svc), request_action($act)
        Rule {
            id: rule_ids::SERVICE_ACTION_SECURE,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("svc_action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $svc, $act
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)], // $svc
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)), // explicit equality for ZK
            ],
        },
        // Rule 3: allow if unrestricted(true), request_action($act)
        Rule {
            id: rule_ids::UNRESTRICTED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("unrestricted"),
                    terms: vec![Term::Int(1)], // true encoded as 1
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(0)], // $act (ensures there IS an action)
                },
            ],
            checks: vec![],
        },
        // Rule 10: Time-bounded app + action (secure)
        // allow if action_allowed($app, $act), request_app($app), request_action($act),
        //          valid_until($exp), request_time($t)
        //   checks: MemberOf($act, $act), $t < $exp
        Rule {
            id: rule_ids::APP_ACTION_TIME_BOUNDED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $app, $act
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)], // $app
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act
                },
                Atom {
                    predicate: symbol_from_str("valid_until"),
                    terms: vec![Term::Var(2)], // $exp
                },
                Atom {
                    predicate: symbol_from_str("request_time"),
                    terms: vec![Term::Var(3)], // $t
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)),
                Check::LessThan(Term::Var(3), Term::Var(2)), // $t < $exp
            ],
        },
        // Rule 11: Time-bounded service + action (secure)
        Rule {
            id: rule_ids::SERVICE_ACTION_TIME_BOUNDED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("svc_action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $svc, $act
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)], // $svc
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act
                },
                Atom {
                    predicate: symbol_from_str("valid_until"),
                    terms: vec![Term::Var(2)], // $exp
                },
                Atom {
                    predicate: symbol_from_str("request_time"),
                    terms: vec![Term::Var(3)], // $t
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)),
                Check::LessThan(Term::Var(3), Term::Var(2)), // $t < $exp
            ],
        },
    ];

    // Add budget and revocation rules
    rules.extend(budget_revocation_rules());
    rules
}

/// Returns the legacy pyana authorization policy rule set.
///
/// **DEPRECATED**: This policy uses `Contains` (substring matching) for action checking,
/// which is vulnerable to collisions (e.g. "threadwrite" matches "write"). Use
/// [`standard_policy()`] instead, which uses exact hash matching via `MemberOf`.
///
/// This legacy policy expects comma-separated action strings in facts:
/// - `app(app_id, "read,write,delete")` — actions as a comma-separated string
/// - `service(service_id, "read,write")` — same for services
///
/// Retained for backward compatibility with existing serialized tokens.
#[deprecated(note = "Use standard_policy() which uses MemberOf for secure action matching")]
pub fn legacy_policy() -> Vec<Rule> {
    let mut rules = vec![
        // Rule 1: allow if app($app, $actions), request_app($app), request_action($act), $actions.contains($act)
        Rule {
            id: rule_ids::APP_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $app, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)], // $app
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)], // $act
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(1), Term::Var(2)), // $actions.contains($act)
            ],
        },
        // Rule 2: allow if service($svc, $actions), request_service($svc), request_action($act), $actions.contains($act)
        Rule {
            id: rule_ids::SERVICE_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("service"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $svc, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)], // $svc
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)], // $act
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(1), Term::Var(2)), // $actions.contains($act)
            ],
        },
        // Rule 3: allow if unrestricted(true), request_action($act)
        Rule {
            id: rule_ids::UNRESTRICTED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("unrestricted"),
                    terms: vec![Term::Int(1)], // true encoded as 1
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(0)], // $act (ensures there IS an action)
                },
            ],
            checks: vec![],
        },
        // Rule 4: allow if app($app, $actions), request_app($app) [no action required]
        Rule {
            id: rule_ids::APP_ANY_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $app, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)], // $app
                },
                Atom {
                    predicate: symbol_from_str("no_action_required"),
                    terms: vec![Term::Int(1)],
                },
            ],
            checks: vec![],
        },
        // Rule 5: allow if service($svc, $actions), request_service($svc) [no action required]
        Rule {
            id: rule_ids::SERVICE_ANY_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("service"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $svc, $actions
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)], // $svc
                },
                Atom {
                    predicate: symbol_from_str("no_action_required"),
                    terms: vec![Term::Int(1)],
                },
            ],
            checks: vec![],
        },
        // Rule 10: Time-bounded app + action
        // allow if app($app, $actions), request_app($app), request_action($act),
        //          valid_until($exp), request_time($t)
        //   checks: $actions.contains($act), $t < $exp
        Rule {
            id: rule_ids::APP_ACTION_TIME_BOUNDED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)],
                },
                Atom {
                    predicate: symbol_from_str("valid_until"),
                    terms: vec![Term::Var(3)],
                },
                Atom {
                    predicate: symbol_from_str("request_time"),
                    terms: vec![Term::Var(4)],
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(1), Term::Var(2)),
                Check::LessThan(Term::Var(4), Term::Var(3)), // $t < $exp
            ],
        },
        // Rule 11: Time-bounded service + action (same pattern)
        Rule {
            id: rule_ids::SERVICE_ACTION_TIME_BOUNDED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("service"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)],
                },
                Atom {
                    predicate: symbol_from_str("valid_until"),
                    terms: vec![Term::Var(3)],
                },
                Atom {
                    predicate: symbol_from_str("request_time"),
                    terms: vec![Term::Var(4)],
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(1), Term::Var(2)),
                Check::LessThan(Term::Var(4), Term::Var(3)), // $t < $exp
            ],
        },
    ];

    // Add budget and revocation rules
    rules.extend(budget_revocation_rules());
    rules
}

/// Budget and revocation rules shared between standard and legacy policies.
fn budget_revocation_rules() -> Vec<Rule> {
    vec![
        // Rule 20: budget_ok(B) :- budget_remaining(B, R), request_cost(C), R >= C
        Rule {
            id: rule_ids::BUDGET_OK,
            head: Atom {
                predicate: symbol_from_str("budget_ok"),
                terms: vec![Term::Var(0)], // $B
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("budget_remaining"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $B, $R
                },
                Atom {
                    predicate: symbol_from_str("request_cost"),
                    terms: vec![Term::Var(2)], // $C
                },
            ],
            checks: vec![
                Check::GreaterThanOrEqual(Term::Var(1), Term::Var(2)), // $R >= $C
            ],
        },
        // Rule 21: deny :- budget_remaining(B, R), request_cost(C), C > R
        Rule {
            id: rule_ids::BUDGET_DENY,
            head: Atom {
                predicate: symbol_from_str("deny"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("budget_remaining"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $B, $R
                },
                Atom {
                    predicate: symbol_from_str("request_cost"),
                    terms: vec![Term::Var(2)], // $C
                },
            ],
            checks: vec![
                Check::GreaterThan(Term::Var(2), Term::Var(1)), // $C > $R (insufficient budget)
            ],
        },
        // Rule 30: not_revoked_ok(T) :- not_revoked(T)
        Rule {
            id: rule_ids::REVOCATION_OK,
            head: Atom {
                predicate: symbol_from_str("not_revoked_ok"),
                terms: vec![Term::Var(0)],
            },
            body: vec![Atom {
                predicate: symbol_from_str("not_revoked"),
                terms: vec![Term::Var(0)],
            }],
            checks: vec![],
        },
        // Rule 31: deny :- revocable(T), revoked(T)
        Rule {
            id: rule_ids::REVOCATION_DENY,
            head: Atom {
                predicate: symbol_from_str("deny"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("revocable"),
                    terms: vec![Term::Var(0)], // $T
                },
                Atom {
                    predicate: symbol_from_str("revoked"),
                    terms: vec![Term::Var(0)], // $T (matching — token IS revoked)
                },
            ],
            checks: vec![],
        },
    ]
}

/// Create a minimal policy with just app-action and unrestricted rules.
/// Useful for testing.
pub fn minimal_policy() -> Vec<Rule> {
    vec![
        // Rule 1: allow if app($app, $actions), request_app($app), request_action($act), $actions.contains($act)
        Rule {
            id: rule_ids::APP_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)],
                },
            ],
            checks: vec![Check::Contains(Term::Var(1), Term::Var(2))],
        },
        // Rule 2: allow if service($svc, $actions), request_service($svc), request_action($act), $actions.contains($act)
        Rule {
            id: rule_ids::SERVICE_ACTION,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("service"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)],
                },
            ],
            checks: vec![Check::Contains(Term::Var(1), Term::Var(2))],
        },
        // Rule 3: allow if unrestricted(true), request_action($act)
        Rule {
            id: rule_ids::UNRESTRICTED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("unrestricted"),
                    terms: vec![Term::Int(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        },
    ]
}

/// Create a time-bounded policy that checks token expiry.
///
/// This variant uses 5 body atoms (exceeding the ZK circuit's 4-atom limit).
/// In production, the time-bounded check would be split across two rules
/// (an intermediate derivation). This is the reference semantics.
pub fn time_bounded_policy() -> Vec<Rule> {
    vec![
        // allow if app($app, $actions), request_app($app), request_action($act),
        //          valid_until($exp), request_time($t)
        //   checks: $actions.contains($act), $t < $exp
        Rule {
            id: rule_ids::APP_ACTION_TIME_BOUNDED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("app"),
                    terms: vec![Term::Var(0), Term::Var(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(2)],
                },
                Atom {
                    predicate: symbol_from_str("valid_until"),
                    terms: vec![Term::Var(3)],
                },
                Atom {
                    predicate: symbol_from_str("request_time"),
                    terms: vec![Term::Var(4)],
                },
            ],
            checks: vec![
                Check::Contains(Term::Var(1), Term::Var(2)),
                Check::LessThan(Term::Var(4), Term::Var(3)),
            ],
        },
    ]
}

/// Secure policy set using hash-based action membership instead of substring matching.
///
/// This policy replaces `Check::Contains` (substring) with `Check::MemberOf` (exact
/// hash equality). It expects per-action facts:
///
/// - `action_allowed(app_id, action_hash)` — one fact per allowed action per app
/// - `svc_action_allowed(service_id, action_hash)` — one fact per allowed action per service
///
/// The request's action is also stored as a hash in `request_action(action_hash)`.
///
/// This eliminates the substring vulnerability where e.g. "threadwrite" could match "write".
pub fn secure_policy() -> Vec<Rule> {
    vec![
        // Rule 40: allow if action_allowed($app, $act), request_app($app), request_action($act)
        //   check: MemberOf($act, $act) [redundant with unification, but explicit for ZK circuit]
        Rule {
            id: rule_ids::APP_ACTION_SECURE,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $app, $act_hash
                },
                Atom {
                    predicate: symbol_from_str("request_app"),
                    terms: vec![Term::Var(0)], // $app
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act_hash (must unify with action_allowed)
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)), // explicit equality for ZK
            ],
        },
        // Rule 41: allow if svc_action_allowed($svc, $act), request_service($svc), request_action($act)
        Rule {
            id: rule_ids::SERVICE_ACTION_SECURE,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("svc_action_allowed"),
                    terms: vec![Term::Var(0), Term::Var(1)], // $svc, $act_hash
                },
                Atom {
                    predicate: symbol_from_str("request_service"),
                    terms: vec![Term::Var(0)], // $svc
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(1)], // $act_hash
                },
            ],
            checks: vec![
                Check::MemberOf(Term::Var(1), Term::Var(1)), // explicit equality for ZK
            ],
        },
        // Rule 3 (UNRESTRICTED) — same as standard, included for completeness
        Rule {
            id: rule_ids::UNRESTRICTED,
            head: Atom {
                predicate: symbol_from_str("allow"),
                terms: vec![],
            },
            body: vec![
                Atom {
                    predicate: symbol_from_str("unrestricted"),
                    terms: vec![Term::Int(1)],
                },
                Atom {
                    predicate: symbol_from_str("request_action"),
                    terms: vec![Term::Var(0)],
                },
            ],
            checks: vec![],
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::Evaluator;

    #[test]
    fn test_standard_policy_has_expected_rules() {
        let rules = standard_policy();
        assert!(rules.len() >= 5);

        // Check rule IDs are present (secure MemberOf-based rules)
        assert!(rules.iter().any(|r| r.id == rule_ids::APP_ACTION_SECURE));
        assert!(
            rules
                .iter()
                .any(|r| r.id == rule_ids::SERVICE_ACTION_SECURE)
        );
        assert!(rules.iter().any(|r| r.id == rule_ids::UNRESTRICTED));
        // Budget and revocation rules
        assert!(rules.iter().any(|r| r.id == rule_ids::BUDGET_OK));
        assert!(rules.iter().any(|r| r.id == rule_ids::BUDGET_DENY));
        assert!(rules.iter().any(|r| r.id == rule_ids::REVOCATION_OK));
        assert!(rules.iter().any(|r| r.id == rule_ids::REVOCATION_DENY));
        // Time-bounded rules
        assert!(
            rules
                .iter()
                .any(|r| r.id == rule_ids::APP_ACTION_TIME_BOUNDED)
        );
        assert!(
            rules
                .iter()
                .any(|r| r.id == rule_ids::SERVICE_ACTION_TIME_BOUNDED)
        );
    }

    #[test]
    #[allow(deprecated)]
    fn test_legacy_policy_has_expected_rules() {
        let rules = legacy_policy();
        assert!(rules.len() >= 5);

        // Check rule IDs are present (Contains-based rules)
        assert!(rules.iter().any(|r| r.id == rule_ids::APP_ACTION));
        assert!(rules.iter().any(|r| r.id == rule_ids::SERVICE_ACTION));
        assert!(rules.iter().any(|r| r.id == rule_ids::UNRESTRICTED));
    }

    #[test]
    fn test_minimal_policy_app_action_allow() {
        let rules = minimal_policy();
        // Use symbol_from_bytes for terms so Contains (substring) check works
        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![
                Term::Const(symbol_from_bytes(b"dashboard")),
                Term::Const(symbol_from_bytes(b"read,write")),
            ],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_bytes(b"dashboard")),
            service: None,
            action: Some(symbol_from_bytes(b"read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::APP_ACTION,
            }
        );
    }

    #[test]
    fn test_minimal_policy_app_action_deny() {
        let rules = minimal_policy();
        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![
                Term::Const(symbol_from_bytes(b"dashboard")),
                Term::Const(symbol_from_bytes(b"read")),
            ],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_bytes(b"dashboard")),
            service: None,
            action: Some(symbol_from_bytes(b"delete")), // not in actions
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(trace.conclusion, Conclusion::Deny);
    }

    #[test]
    fn test_minimal_policy_unrestricted() {
        let rules = minimal_policy();
        let facts = vec![Fact::new(
            symbol_from_str("unrestricted"),
            vec![Term::Int(1)],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_bytes(b"anything")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::UNRESTRICTED,
            }
        );
    }

    #[test]
    fn test_budget_ok_rule_allows() {
        // budget_remaining("b1", 50), request_cost(10) => budget_ok("b1") derived
        let rules = standard_policy();
        let facts = vec![
            Fact::new(
                symbol_from_str("budget_remaining"),
                vec![Term::Const(symbol_from_str("b1")), Term::Int(50)],
            ),
            Fact::new(symbol_from_str("request_cost"), vec![Term::Int(10)]),
            // Also need an allow rule to fire — use unrestricted
            Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
        ];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        // budget_ok should be derived (rule 20), and allow should fire
        assert!(trace.steps.iter().any(|s| s.rule_id == rule_ids::BUDGET_OK));
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::UNRESTRICTED
            }
        );
    }

    #[test]
    fn test_budget_deny_rule_fires() {
        // budget_remaining("b1", 5), request_cost(10) => deny derived (cost > remaining)
        let rules = standard_policy();
        let facts = vec![
            Fact::new(
                symbol_from_str("budget_remaining"),
                vec![Term::Const(symbol_from_str("b1")), Term::Int(5)],
            ),
            Fact::new(symbol_from_str("request_cost"), vec![Term::Int(10)]),
            Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
        ];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        // deny should be derived by rule 21
        assert!(
            trace
                .steps
                .iter()
                .any(|s| s.rule_id == rule_ids::BUDGET_DENY)
        );
        // Note: the evaluator still returns Allow because the deny fact doesn't block
        // allow derivation in pure Datalog. The bridge layer checks for deny facts explicitly.
    }

    #[test]
    fn test_revocation_deny_rule_fires() {
        // revocable("t1"), revoked("t1") => deny derived
        let rules = standard_policy();
        let facts = vec![
            Fact::new(
                symbol_from_str("revocable"),
                vec![Term::Const(symbol_from_str("t1"))],
            ),
            Fact::new(
                symbol_from_str("revoked"),
                vec![Term::Const(symbol_from_str("t1"))],
            ),
            Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
        ];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        // deny should be derived by rule 31
        assert!(
            trace
                .steps
                .iter()
                .any(|s| s.rule_id == rule_ids::REVOCATION_DENY)
        );
    }

    #[test]
    fn test_not_revoked_ok_rule_fires() {
        // not_revoked("t1") => not_revoked_ok("t1") derived
        let rules = standard_policy();
        let facts = vec![
            Fact::new(
                symbol_from_str("not_revoked"),
                vec![Term::Const(symbol_from_str("t1"))],
            ),
            Fact::new(symbol_from_str("unrestricted"), vec![Term::Int(1)]),
        ];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        // not_revoked_ok should be derived by rule 30
        assert!(
            trace
                .steps
                .iter()
                .any(|s| s.rule_id == rule_ids::REVOCATION_OK)
        );
    }

    // ======================================================================
    // Secure policy tests (hash-based action membership)
    // ======================================================================

    #[test]
    fn test_secure_policy_app_action_allow() {
        let rules = secure_policy();
        // Emit per-action facts: action_allowed("dashboard", "read")
        let facts = vec![
            Fact::new(
                symbol_from_str("action_allowed"),
                vec![
                    Term::Const(symbol_from_str("dashboard")),
                    Term::Const(symbol_from_str("read")),
                ],
            ),
            Fact::new(
                symbol_from_str("action_allowed"),
                vec![
                    Term::Const(symbol_from_str("dashboard")),
                    Term::Const(symbol_from_str("write")),
                ],
            ),
        ];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str("dashboard")),
            service: None,
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::APP_ACTION_SECURE,
            }
        );
    }

    #[test]
    fn test_secure_policy_app_action_deny_wrong_action() {
        let rules = secure_policy();
        let facts = vec![
            Fact::new(
                symbol_from_str("action_allowed"),
                vec![
                    Term::Const(symbol_from_str("dashboard")),
                    Term::Const(symbol_from_str("read")),
                ],
            ),
            Fact::new(
                symbol_from_str("action_allowed"),
                vec![
                    Term::Const(symbol_from_str("dashboard")),
                    Term::Const(symbol_from_str("write")),
                ],
            ),
        ];

        let eval = Evaluator::new(facts, rules);
        // Request "delete" — not in the action set, so denied.
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str("dashboard")),
            service: None,
            action: Some(symbol_from_str("delete")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(trace.conclusion, Conclusion::Deny);
    }

    #[test]
    fn test_secure_policy_no_substring_vulnerability() {
        let rules = secure_policy();
        // Only "write" is allowed for "my-app".
        let facts = vec![Fact::new(
            symbol_from_str("action_allowed"),
            vec![
                Term::Const(symbol_from_str("my-app")),
                Term::Const(symbol_from_str("write")),
            ],
        )];

        let eval = Evaluator::new(facts, rules);
        // Request "threadwrite" — must NOT match "write" in the secure policy.
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_str("my-app")),
            service: None,
            action: Some(symbol_from_str("threadwrite")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Deny,
            "SECURITY: 'threadwrite' must NOT match 'write' in the secure policy"
        );
    }

    #[test]
    fn test_secure_policy_service_action_allow() {
        let rules = secure_policy();
        let facts = vec![Fact::new(
            symbol_from_str("svc_action_allowed"),
            vec![
                Term::Const(symbol_from_str("http")),
                Term::Const(symbol_from_str("read")),
            ],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: Some(symbol_from_str("http")),
            action: Some(symbol_from_str("read")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::SERVICE_ACTION_SECURE,
            }
        );
    }

    #[test]
    fn test_secure_policy_unrestricted() {
        let rules = secure_policy();
        let facts = vec![Fact::new(
            symbol_from_str("unrestricted"),
            vec![Term::Int(1)],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: None,
            service: None,
            action: Some(symbol_from_str("anything")),
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::UNRESTRICTED,
            }
        );
    }

    /// Demonstrates the old vulnerability: with the legacy Contains check,
    /// "threadwrite" contains "write" as a substring so it incorrectly allows.
    #[test]
    fn test_old_contains_vulnerability_demonstration() {
        let rules = minimal_policy(); // uses Contains (substring)
        // Use symbol_from_bytes for terms so Contains (substring) works
        let facts = vec![Fact::new(
            symbol_from_str("app"),
            vec![
                Term::Const(symbol_from_bytes(b"my-app")),
                // "threadwrite" contains "write" as a substring!
                Term::Const(symbol_from_bytes(b"threadwrite")),
            ],
        )];

        let eval = Evaluator::new(facts, rules);
        let request = AuthorizationRequest {
            app_id: Some(symbol_from_bytes(b"my-app")),
            service: None,
            action: Some(symbol_from_bytes(b"write")), // "write" is a substring of "threadwrite"
            features: vec![],
            user_id: None,
            now: 1000,
        };

        let trace = eval.evaluate(&request);
        // This INCORRECTLY allows because "threadwrite".contains("write") == true.
        // This demonstrates the security vulnerability that secure_policy fixes.
        assert_eq!(
            trace.conclusion,
            Conclusion::Allow {
                policy_rule_id: rule_ids::APP_ACTION,
            },
            "OLD VULNERABILITY: substring matching allows 'write' to match 'threadwrite'"
        );
    }
}
