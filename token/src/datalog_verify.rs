//! Canonical Datalog-based token verification.
//!
//! This module provides the SOLE ground-truth verification semantics for pyana
//! tokens. The flow is:
//!
//! ```text
//! Token -> decode caveats -> compile to FactSet -> Datalog evaluation -> Allow/Deny
//! ```
//!
//! Two modes of the SAME semantics:
//! - **Trusted mode**: Run Datalog locally (~8us), trust the result.
//! - **Trustless mode**: Prove the Datalog evaluation in a STARK, verify the proof.
//!
//! This replaces the imperative `verify_caveats` function as the canonical
//! authorization evaluator.

use pyana_commit::{FieldElement, SymbolTable, TokenState};
use pyana_trace::{
    AuthorizationRequest as TraceRequest, AuthorizationTrace, Conclusion, Evaluator,
    Fact as TraceFact, Rule, Term, symbol_from_str,
};

use crate::error::TokenError;
use crate::factset::caveat_set_to_factset;
use crate::format::TokenFormat;
use crate::pyana_caveats;
use crate::traits::{AuthRequest, Capability, TokenClearance};

use pyana_macaroon::caveat::CaveatSet;

/// Result of Datalog verification, including the derivation trace for
/// potential STARK proving in trustless mode.
pub struct DatalogVerifyResult {
    /// The token clearance (capabilities, expiry, subject).
    pub clearance: TokenClearance,
    /// The full derivation trace (for STARK proof generation in trustless mode).
    pub trace: AuthorizationTrace,
}

/// Verify a token's caveats using Datalog evaluation (canonical semantics).
///
/// This is the ground-truth verifier. It:
/// 1. Runs pre-evaluation deny checks (time, org, user, machine, etc.)
/// 2. Decodes the caveat set into a FactSet
/// 3. Converts the FactSet to trace-format facts
/// 4. Runs the Datalog evaluator with standard + extended policy
/// 5. Returns Allow/Deny with a derivation trace
///
/// The derivation trace can be fed into the STARK prover for trustless verification.
///
/// **Security**: This function always runs deny checks before Datalog evaluation.
/// There is no public entry point that bypasses deny checks.
pub fn verify_token_datalog(
    caveat_set: &CaveatSet,
    request: &AuthRequest,
) -> Result<DatalogVerifyResult, TokenError> {
    // Phase 0: Run pre-evaluation deny checks (time, org, user, machine, etc.)
    // These MUST run before any Datalog evaluation to prevent bypasses.
    pre_evaluation_deny_checks(caveat_set, request)?;

    // 1. Decode caveats to FactSet + SymbolTable
    let (factset, symbols) = caveat_set_to_factset(caveat_set)?;

    // 2. Build TokenState from FactSet
    let mut state = TokenState::new();
    for fact in factset.iter() {
        state.add_fact(*fact);
    }

    if state.is_empty() {
        return Err(TokenError::Denied(
            "token state is empty (no facts to evaluate)".into(),
        ));
    }

    // 2b. Determine token dimensions from user-supplied facts.
    let has_app_facts = state
        .all_facts()
        .iter()
        .any(|f| symbols.resolve(f.predicate) == Some("app"));
    let has_service_facts = state
        .all_facts()
        .iter()
        .any(|f| symbols.resolve(f.predicate) == Some("service"));
    let has_valid_until = state
        .all_facts()
        .iter()
        .any(|f| symbols.resolve(f.predicate) == Some("valid_until"));
    let has_valid_after = state
        .all_facts()
        .iter()
        .any(|f| symbols.resolve(f.predicate) == Some("valid_after"));

    // 2c. Extract temporal values from the factset BEFORE filtering.
    // Since valid_until and valid_after are now reserved predicates (Issue #6),
    // they will be filtered out by committed_facts_to_trace. We extract them here
    // and inject them as engine-controlled facts in step 3b.
    let mut valid_until_values: Vec<i64> = Vec::new();
    let mut valid_after_values: Vec<i64> = Vec::new();
    for fact in state.all_facts() {
        if symbols.resolve(fact.predicate) == Some("valid_until") {
            if let Some(val) = field_element_to_int(&fact.terms[0]) {
                valid_until_values.push(val);
            }
        }
        if symbols.resolve(fact.predicate) == Some("valid_after") {
            if let Some(val) = field_element_to_int(&fact.terms[0]) {
                valid_after_values.push(val);
            }
        }
    }

    // 3. Convert committed facts to trace-format facts.
    // This filters out reserved predicates to prevent policy injection attacks.
    let mut trace_facts = committed_facts_to_trace(&state, &symbols);

    // 3b. Inject engine-controlled facts AFTER user facts are converted and filtered.
    // These are added directly to trace_facts (not to state) so they cannot be
    // spoofed by user-supplied caveats with reserved predicate names.
    if !has_app_facts && !has_service_facts {
        // Token has no app/service dimensional facts -- inject unrestricted(1)
        // so the unrestricted rules can fire.
        trace_facts.push(TraceFact::new(
            symbol_from_str("unrestricted"),
            vec![Term::Int(1)],
        ));
    }

    if !has_valid_until && !has_valid_after {
        // Token has no time bound -- inject no_time_bound(1) so Rule 3 can
        // distinguish truly unbounded tokens from time-bounded ones.
        // A token with valid_after but no valid_until is still time-bounded
        // and must go through a time-checking rule.
        trace_facts.push(TraceFact::new(
            symbol_from_str("no_time_bound"),
            vec![Term::Int(1)],
        ));
    }

    if !has_valid_after {
        // Token has no valid_after constraint -- inject no_valid_after(1) so
        // Rules 10/11/12 (valid_until-only) can distinguish from tokens that
        // also have a valid_after constraint. Without this guard, a token with
        // both valid_after and valid_until could match Rules 10/11/12 and bypass
        // the not-before check entirely.
        trace_facts.push(TraceFact::new(
            symbol_from_str("no_valid_after"),
            vec![Term::Int(1)],
        ));
    }

    // 3c. Inject temporal facts as engine-controlled facts.
    // These were extracted from the factset before filtering (step 2c) and are
    // injected here so they CANNOT be spoofed by user-supplied facts with reserved names.
    for val in &valid_until_values {
        trace_facts.push(TraceFact::new(
            symbol_from_str("valid_until"),
            vec![Term::Int(*val)],
        ));
    }
    for val in &valid_after_values {
        trace_facts.push(TraceFact::new(
            symbol_from_str("valid_after"),
            vec![Term::Int(*val)],
        ));
    }

    // 4. Convert AuthRequest to trace format
    let trace_request = auth_request_to_trace(request)?;

    // 5. Get the full policy set (standard + extended for all caveat types)
    let rules = full_policy();

    // 6. Run the evaluator
    let evaluator = Evaluator::new(trace_facts, rules);
    let trace = evaluator.evaluate(&trace_request);

    // 7. Interpret conclusion
    match &trace.conclusion {
        Conclusion::Allow { policy_rule_id } => {
            // Build capabilities from the caveats (same logic as verify_caveats)
            let capabilities = extract_capabilities(caveat_set);
            let (expires_at, subject) = extract_metadata(caveat_set);

            Ok(DatalogVerifyResult {
                clearance: TokenClearance {
                    matched_policy: Some(format!("datalog_rule_{}", policy_rule_id)),
                    capabilities,
                    format: TokenFormat::Macaroon,
                    expires_at,
                    subject,
                },
                trace,
            })
        }
        Conclusion::Deny => {
            // Check for specific denial reasons
            let reason = diagnose_denial(caveat_set, request);
            Err(TokenError::Denied(reason))
        }
    }
}

/// Verify with just the clearance result (no trace). Convenience wrapper
/// for the common trusted-mode case.
///
/// This is `pub(crate)` because external callers should use either:
/// - `verify_token_datalog_full()` for the complete verification path, or
/// - `verify_token_datalog()` for the trace-producing path (which includes deny checks).
pub(crate) fn verify_token_datalog_trusted(
    caveat_set: &CaveatSet,
    request: &AuthRequest,
) -> Result<TokenClearance, TokenError> {
    verify_token_datalog(caveat_set, request).map(|r| r.clearance)
}

// ============================================================================
// Policy rules (extended from standard_policy to cover all caveat types)
// ============================================================================

/// Rule IDs for the extended policy set.
pub mod rule_ids {
    pub const APP_ACTION: u32 = 1;
    pub const SERVICE_ACTION: u32 = 2;
    pub const UNRESTRICTED: u32 = 3;
    pub const APP_ANY_ACTION: u32 = 4;
    pub const SERVICE_ANY_ACTION: u32 = 5;
    // Extended rules for dimensions not covered by standard policy
    pub const CONFINE_USER: u32 = 20;
    pub const OAUTH_PROVIDER: u32 = 21;
    pub const OAUTH_SCOPE: u32 = 22;
    pub const FROM_MACHINE: u32 = 23;
    pub const COMMAND: u32 = 24;
    pub const ORGANIZATION: u32 = 25;
    pub const FEATURE: u32 = 26;
    // Time-bounded variants (valid_until only)
    pub const APP_ACTION_TIME_BOUNDED: u32 = 10;
    pub const SERVICE_ACTION_TIME_BOUNDED: u32 = 11;
    pub const UNRESTRICTED_TIME_BOUNDED: u32 = 12;
    // Time-bounded variants (valid_after only, no valid_until)
    pub const APP_ACTION_NOT_BEFORE: u32 = 13;
    pub const SERVICE_ACTION_NOT_BEFORE: u32 = 14;
    pub const UNRESTRICTED_NOT_BEFORE: u32 = 15;
    // Time-bounded variants (both valid_after AND valid_until)
    pub const APP_ACTION_FULL_WINDOW: u32 = 16;
    pub const SERVICE_ACTION_FULL_WINDOW: u32 = 17;
    pub const UNRESTRICTED_FULL_WINDOW: u32 = 18;
}

/// Returns the full pyana authorization policy rule set.
///
/// This extends the standard policy with rules for every caveat dimension.
/// The Datalog rules handle POSITIVE authorization only:
///
/// - Restricted dimensions require matching (app/service + action).
/// - Time bounds are checked via LessThan/GreaterThan checks.
/// - Rule 3 (unrestricted) fires ONLY for tokens with an explicit `unrestricted(1)` fact.
///
/// Least-privilege enforcement (missing dimension = DENY) is handled BEFORE
/// Datalog evaluation in `verify_token_datalog_full()`. The Datalog engine
/// only runs when we already know the request targets a dimension the token
/// explicitly grants.
fn full_policy() -> Vec<Rule> {
    use pyana_trace::{Atom, Check};

    let mut rules = Vec::new();

    // === Core access rules (secure, MemberOf-based) ===

    // Rule 1: allow if action_allowed($app, $act), request_app($app), request_action($act)
    //   check: MemberOf($act, $act) [explicit equality for ZK path]
    rules.push(Rule {
        id: rule_ids::APP_ACTION,
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
        checks: vec![Check::MemberOf(Term::Var(1), Term::Var(1))],
    });

    // Rule 2: allow if svc_action_allowed($svc, $act), request_service($svc), request_action($act)
    //   check: MemberOf($act, $act) [explicit equality for ZK path]
    rules.push(Rule {
        id: rule_ids::SERVICE_ACTION,
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
                terms: vec![Term::Var(1)], // $act (must unify with svc_action_allowed)
            },
        ],
        checks: vec![Check::MemberOf(Term::Var(1), Term::Var(1))],
    });

    // Rule 3: allow if unrestricted(1) AND no valid_until fact exists.
    // This rule ONLY fires for truly unbounded tokens (no time caveat at all).
    // Time-bounded unrestricted tokens MUST go through Rule 12, which enforces
    // the time check. Without this guard, an expired time-bounded token could
    // match Rule 3 and bypass expiry enforcement.
    rules.push(Rule {
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
                predicate: symbol_from_str("no_time_bound"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![],
    });

    // Rule 4: allow if action_allowed($app, $any_act), request_app($app), no_action_required(1)
    // (the existence of any action_allowed fact for this app is sufficient)
    rules.push(Rule {
        id: rule_ids::APP_ANY_ACTION,
        head: Atom {
            predicate: symbol_from_str("allow"),
            terms: vec![],
        },
        body: vec![
            Atom {
                predicate: symbol_from_str("action_allowed"),
                terms: vec![Term::Var(0), Term::Var(1)], // $app, $any_act
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
    });

    // Rule 5: allow if svc_action_allowed($svc, $any_act), request_service($svc), no_action_required(1)
    rules.push(Rule {
        id: rule_ids::SERVICE_ANY_ACTION,
        head: Atom {
            predicate: symbol_from_str("allow"),
            terms: vec![],
        },
        body: vec![
            Atom {
                predicate: symbol_from_str("svc_action_allowed"),
                terms: vec![Term::Var(0), Term::Var(1)], // $svc, $any_act
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
    });

    // Rule 10: Time-bounded app + action (valid_until only, no valid_after)
    // allow if action_allowed($app, $act), request_app($app), request_action($act),
    //          valid_until($exp), request_time($t), no_valid_after(1)
    //   checks: MemberOf($act, $act), $t < $exp
    rules.push(Rule {
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
            Atom {
                predicate: symbol_from_str("no_valid_after"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::LessThan(Term::Var(3), Term::Var(2)), // $t < $exp
        ],
    });

    // Rule 11: Time-bounded service + action (valid_until only, no valid_after)
    rules.push(Rule {
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
            Atom {
                predicate: symbol_from_str("no_valid_after"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::LessThan(Term::Var(3), Term::Var(2)), // $t < $exp
        ],
    });

    // Rule 12: Unrestricted with valid_until only (no valid_after)
    rules.push(Rule {
        id: rule_ids::UNRESTRICTED_TIME_BOUNDED,
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
                predicate: symbol_from_str("valid_until"),
                terms: vec![Term::Var(0)],
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(1)],
            },
            Atom {
                predicate: symbol_from_str("no_valid_after"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![
            Check::LessThan(Term::Var(1), Term::Var(0)), // $t < $exp
        ],
    });

    // === valid_after (not_before) rules ===
    //
    // These rules enforce the `valid_after` temporal constraint. Without them,
    // a malicious prover could generate a STARK proof authorizing a token that
    // hasn't activated yet, because the valid_after facts were injected into
    // the trace but never consumed by any rule.

    // Rule 13: App + action with valid_after only (no valid_until)
    // allow if action_allowed($app, $act), request_app($app), request_action($act),
    //          valid_after($nb), request_time($t)
    //   checks: MemberOf($act, $act), $t >= $nb
    rules.push(Rule {
        id: rule_ids::APP_ACTION_NOT_BEFORE,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(2)], // $nb
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(3)], // $t
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::GreaterThanOrEqual(Term::Var(3), Term::Var(2)), // $t >= $nb
        ],
    });

    // Rule 14: Service + action with valid_after only (no valid_until)
    rules.push(Rule {
        id: rule_ids::SERVICE_ACTION_NOT_BEFORE,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(2)], // $nb
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(3)], // $t
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::GreaterThanOrEqual(Term::Var(3), Term::Var(2)), // $t >= $nb
        ],
    });

    // Rule 15: Unrestricted with valid_after only (no valid_until)
    rules.push(Rule {
        id: rule_ids::UNRESTRICTED_NOT_BEFORE,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(0)], // $nb
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(1)], // $t
            },
        ],
        checks: vec![
            Check::GreaterThanOrEqual(Term::Var(1), Term::Var(0)), // $t >= $nb
        ],
    });

    // Rule 16: App + action with BOTH valid_after AND valid_until (full window)
    // allow if action_allowed($app, $act), request_app($app), request_action($act),
    //          valid_after($nb), valid_until($exp), request_time($t)
    //   checks: MemberOf($act, $act), $t >= $nb, $t < $exp
    rules.push(Rule {
        id: rule_ids::APP_ACTION_FULL_WINDOW,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(2)], // $nb
            },
            Atom {
                predicate: symbol_from_str("valid_until"),
                terms: vec![Term::Var(3)], // $exp
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(4)], // $t
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::GreaterThanOrEqual(Term::Var(4), Term::Var(2)), // $t >= $nb
            Check::LessThan(Term::Var(4), Term::Var(3)),           // $t < $exp
        ],
    });

    // Rule 17: Service + action with BOTH valid_after AND valid_until (full window)
    rules.push(Rule {
        id: rule_ids::SERVICE_ACTION_FULL_WINDOW,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(2)], // $nb
            },
            Atom {
                predicate: symbol_from_str("valid_until"),
                terms: vec![Term::Var(3)], // $exp
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(4)], // $t
            },
        ],
        checks: vec![
            Check::MemberOf(Term::Var(1), Term::Var(1)),
            Check::GreaterThanOrEqual(Term::Var(4), Term::Var(2)), // $t >= $nb
            Check::LessThan(Term::Var(4), Term::Var(3)),           // $t < $exp
        ],
    });

    // Rule 18: Unrestricted with BOTH valid_after AND valid_until (full window)
    rules.push(Rule {
        id: rule_ids::UNRESTRICTED_FULL_WINDOW,
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
                predicate: symbol_from_str("valid_after"),
                terms: vec![Term::Var(0)], // $nb
            },
            Atom {
                predicate: symbol_from_str("valid_until"),
                terms: vec![Term::Var(1)], // $exp
            },
            Atom {
                predicate: symbol_from_str("request_time"),
                terms: vec![Term::Var(2)], // $t
            },
        ],
        checks: vec![
            Check::GreaterThanOrEqual(Term::Var(2), Term::Var(0)), // $t >= $nb
            Check::LessThan(Term::Var(2), Term::Var(1)),           // $t < $exp
        ],
    });

    rules
}

// ============================================================================
// Internal conversion helpers
// ============================================================================

/// Predicate names reserved by the policy engine.
///
/// These predicates have special semantics in the Datalog evaluation and MUST NOT
/// be injectable from token facts. If a committed fact uses one of these predicates,
/// it could bypass authorization logic (e.g., injecting `allow()` or `unrestricted(1)`
/// directly into the fact set).
const RESERVED_PREDICATES: &[&str] = &[
    "allow",
    "deny",
    "request_app",
    "request_service",
    "request_action",
    "request_time",
    "no_action_required",
    "unrestricted",
    "no_time_bound",
    "action_allowed",
    "svc_action_allowed",
    // Issue #6: Temporal predicates must be reserved to prevent injection attacks.
    // A malicious prover/attenuator could inject valid_until/valid_after facts to
    // bypass temporal constraints (e.g., inject valid_until(far_future) to extend
    // an expired token, or omit valid_after to bypass not-before checks).
    "valid_until",
    "valid_after",
    "no_valid_after",
];

/// Convert committed facts (FieldElement-based) to trace-format facts (Symbol-based).
///
/// App and service facts are expanded into per-action facts for the secure
/// MemberOf-based policy:
/// - `app(id, "rw")` -> `action_allowed(id, "r")`, `action_allowed(id, "w")`
/// - `service(name, "rw")` -> `svc_action_allowed(name, "r")`, `svc_action_allowed(name, "w")`
///
/// Facts with reserved predicate names are rejected to prevent policy injection attacks.
fn committed_facts_to_trace(state: &TokenState, symbols: &SymbolTable) -> Vec<TraceFact> {
    use pyana_macaroon::action::Action;

    let mut trace_facts = Vec::new();

    for fact in state.all_facts() {
        let pred_name = symbols.resolve(fact.predicate);
        let pred_symbol = if let Some(name) = pred_name {
            symbol_from_str(name)
        } else {
            fact.predicate.0
        };

        // SECURITY: Reject facts with reserved predicate names.
        // A malicious token could try to inject `allow()`, `unrestricted(1)`, or
        // `request_app(X)` directly into the fact set to bypass policy evaluation.
        if let Some(name) = pred_name {
            if RESERVED_PREDICATES.contains(&name) {
                // Skip reserved predicates silently -- they are injected by the
                // engine itself (unrestricted, no_time_bound) or derived by rules
                // (allow, action_allowed, svc_action_allowed). User-supplied facts
                // must never use these names.
                continue;
            }
        }

        // Expand app facts into per-action facts
        if pred_name == Some("app") {
            let id_term = resolve_term(&fact.terms[0], symbols);
            let actions_str = symbols.resolve(fact.terms[1]).unwrap_or("");
            let action_set = Action::parse(actions_str);
            let action_allowed_pred = symbol_from_str("action_allowed");

            for action_char in ["r", "w", "c", "d", "C"] {
                let single = Action::parse(action_char);
                if action_set.contains(single) {
                    trace_facts.push(TraceFact::new(
                        action_allowed_pred,
                        vec![id_term.clone(), Term::Const(symbol_from_str(action_char))],
                    ));
                }
            }
            continue;
        }

        // Expand service facts into per-action facts
        if pred_name == Some("service") {
            let id_term = resolve_term(&fact.terms[0], symbols);
            let actions_str = symbols.resolve(fact.terms[1]).unwrap_or("");
            let action_set = Action::parse(actions_str);
            let svc_action_allowed_pred = symbol_from_str("svc_action_allowed");

            for action_char in ["r", "w", "c", "d", "C"] {
                let single = Action::parse(action_char);
                if action_set.contains(single) {
                    trace_facts.push(TraceFact::new(
                        svc_action_allowed_pred,
                        vec![id_term.clone(), Term::Const(symbol_from_str(action_char))],
                    ));
                }
            }
            continue;
        }

        // All other facts: convert directly
        let mut terms = Vec::new();
        for term_fe in &fact.terms {
            if term_fe.is_zero() {
                break;
            }
            terms.push(resolve_term(term_fe, symbols));
        }

        trace_facts.push(TraceFact::new(pred_symbol, terms));
    }

    trace_facts
}

/// Resolve a single FieldElement term into a trace Term.
fn resolve_term(fe: &FieldElement, symbols: &SymbolTable) -> Term {
    if let Some(name) = symbols.resolve(*fe) {
        Term::Const(symbol_from_str(name))
    } else if let Some(int_val) = field_element_to_int(fe) {
        Term::Int(int_val)
    } else {
        Term::Const(fe.0)
    }
}

/// Try to interpret a `FieldElement` as a small integer.
fn field_element_to_int(fe: &FieldElement) -> Option<i64> {
    let bytes = &fe.0;
    if bytes[0..24].iter().all(|&b| b == 0) {
        let val = u64::from_be_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]);
        return Some(val as i64);
    }
    None
}

/// Convert a `token::AuthRequest` to a `trace::AuthorizationRequest`.
fn auth_request_to_trace(request: &AuthRequest) -> Result<TraceRequest, TokenError> {
    let app_id = request.app_id.as_deref().map(symbol_from_str);
    let service = request.service.as_deref().map(symbol_from_str);
    let action = request.action.as_deref().map(symbol_from_str);
    let features: Vec<[u8; 32]> = request
        .features
        .iter()
        .map(|f| symbol_from_str(f))
        .collect();
    let user_id = request.user_id.as_deref().map(symbol_from_str);

    let now = request.now.unwrap_or_else(|| {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    });

    Ok(TraceRequest {
        app_id,
        service,
        action,
        features,
        user_id,
        now,
    })
}

// ============================================================================
// Capability extraction (from caveats, mirrors verify_caveats output)
// ============================================================================

/// Extract capabilities from a caveat set for the clearance result.
///
/// This produces the same capability list as `verify_caveats` but without
/// performing any authorization logic (that's done by Datalog).
fn extract_capabilities(caveat_set: &CaveatSet) -> Vec<Capability> {
    let mut capabilities = Vec::new();

    for wc in caveat_set.first_party_caveats() {
        match pyana_caveats::decode_grant(&wc) {
            Ok(pyana_caveats::PyanaGrant::App { id, actions }) => {
                capabilities.push(Capability {
                    resource_type: "app".into(),
                    resource_id: id,
                    actions: actions.to_string(),
                });
            }
            Ok(pyana_caveats::PyanaGrant::Service { name, actions }) => {
                capabilities.push(Capability {
                    resource_type: "service".into(),
                    resource_id: name,
                    actions: actions.to_string(),
                });
            }
            Ok(pyana_caveats::PyanaGrant::Feature(name)) => {
                capabilities.push(Capability {
                    resource_type: "feature".into(),
                    resource_id: name,
                    actions: "*".into(),
                });
            }
            Ok(pyana_caveats::PyanaGrant::OAuthProvider(p)) => {
                capabilities.push(Capability {
                    resource_type: "oauth_provider".into(),
                    resource_id: p,
                    actions: "*".into(),
                });
            }
            Ok(pyana_caveats::PyanaGrant::OAuthScope(s)) => {
                capabilities.push(Capability {
                    resource_type: "oauth_scope".into(),
                    resource_id: s,
                    actions: "*".into(),
                });
            }
            _ => {}
        }
    }

    capabilities
}

/// Extract metadata (expires_at, subject) from a caveat set.
fn extract_metadata(caveat_set: &CaveatSet) -> (Option<i64>, Option<String>) {
    let mut expires_at: Option<i64> = None;
    let mut subject: Option<String> = None;

    for wc in caveat_set.first_party_caveats() {
        match pyana_caveats::decode_grant(&wc) {
            Ok(pyana_caveats::PyanaGrant::ValidityWindow { not_after, .. }) => {
                if let Some(na) = not_after {
                    expires_at = Some(match expires_at {
                        Some(existing) => existing.min(na),
                        None => na,
                    });
                }
            }
            Ok(pyana_caveats::PyanaGrant::ConfineUser(uid)) => {
                if subject.is_none() {
                    subject = Some(uid);
                }
            }
            _ => {}
        }
    }

    (expires_at, subject)
}

/// Diagnose why authorization was denied, producing a human-readable reason.
///
/// This performs a lightweight analysis of the caveats vs the request to
/// produce specific error messages (matching the old `verify_caveats` behavior).
fn diagnose_denial(caveat_set: &CaveatSet, request: &AuthRequest) -> String {
    use pyana_macaroon::action::Action;

    let mut apps: Vec<(String, Action)> = Vec::new();
    let mut services: Vec<(String, Action)> = Vec::new();
    let mut features: Vec<String> = Vec::new();
    let mut confined_users: Vec<String> = Vec::new();
    let mut oauth_providers: Vec<String> = Vec::new();
    let mut oauth_scopes: Vec<String> = Vec::new();
    let mut machines: Vec<String> = Vec::new();
    let mut commands: Vec<String> = Vec::new();
    let mut orgs: Vec<u64> = Vec::new();
    let mut validity_windows: Vec<(Option<i64>, Option<i64>)> = Vec::new();

    for wc in caveat_set.first_party_caveats() {
        match pyana_caveats::decode_grant(&wc) {
            Ok(pyana_caveats::PyanaGrant::App { id, actions }) => apps.push((id, actions)),
            Ok(pyana_caveats::PyanaGrant::Service { name, actions }) => {
                services.push((name, actions))
            }
            Ok(pyana_caveats::PyanaGrant::Feature(name)) => features.push(name),
            Ok(pyana_caveats::PyanaGrant::ConfineUser(uid)) => confined_users.push(uid),
            Ok(pyana_caveats::PyanaGrant::OAuthProvider(p)) => oauth_providers.push(p),
            Ok(pyana_caveats::PyanaGrant::OAuthScope(s)) => oauth_scopes.push(s),
            Ok(pyana_caveats::PyanaGrant::FromMachine(m)) => machines.push(m),
            Ok(pyana_caveats::PyanaGrant::Command(c)) => commands.push(c),
            Ok(pyana_caveats::PyanaGrant::Organization(id)) => orgs.push(id),
            Ok(pyana_caveats::PyanaGrant::ValidityWindow {
                not_before,
                not_after,
            }) => validity_windows.push((not_before, not_after)),
            _ => {}
        }
    }

    let now = request.now.unwrap_or_else(|| {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    });

    // Check time first
    for (not_before, not_after) in &validity_windows {
        if let Some(nb) = not_before {
            if now < *nb {
                return format!("token not yet valid (not before {})", nb);
            }
        }
        if let Some(na) = not_after {
            if now > *na {
                return format!("token expired (expired at {})", na);
            }
        }
    }

    // Check specific dimension mismatches
    if let Some(req_app) = &request.app_id {
        if !apps.is_empty() && !apps.iter().any(|(id, _)| id == req_app) {
            return format!("token not valid for app '{}'", req_app);
        }
        if let Some(req_action) = &request.action {
            let req_act = Action::parse(req_action);
            if let Some((_, allowed)) = apps.iter().find(|(id, _)| id == req_app) {
                if !allowed.contains(req_act) {
                    return format!(
                        "app '{}' grants {}, request needs {}",
                        req_app, allowed, req_act
                    );
                }
            }
        }
    }

    if let Some(req_svc) = &request.service {
        if !services.is_empty() && !services.iter().any(|(name, _)| name == req_svc) {
            return format!("token not valid for service '{}'", req_svc);
        }
        if let Some(req_action) = &request.action {
            let req_act = Action::parse(req_action);
            if let Some((_, allowed)) = services.iter().find(|(name, _)| name == req_svc) {
                if !allowed.contains(req_act) {
                    return format!(
                        "service '{}' grants {}, request needs {}",
                        req_svc, allowed, req_act
                    );
                }
            }
        }
    }

    if let Some(req_user) = &request.user_id {
        if !confined_users.is_empty() && !confined_users.contains(req_user) {
            return format!(
                "token confined to user(s) {:?}, request is for '{}'",
                confined_users, req_user
            );
        }
    }

    if let Some(req_org) = request.org_id {
        if !orgs.is_empty() && !orgs.contains(&req_org) {
            return format!(
                "token restricted to org(s) {:?}, requested org {}",
                orgs, req_org
            );
        }
    }

    if let Some(req_provider) = &request.oauth_provider {
        if !oauth_providers.is_empty() && !oauth_providers.contains(req_provider) {
            return format!("token not valid for OAuth provider '{}'", req_provider);
        }
    }

    if let Some(req_machine) = &request.machine_id {
        if !machines.is_empty() && !machines.contains(req_machine) {
            return format!("token not valid for machine '{}'", req_machine);
        }
    }

    if let Some(req_cmd) = &request.command {
        if !commands.is_empty() && !commands.contains(req_cmd) {
            return format!("token not valid for command '{}'", req_cmd);
        }
    }

    if !request.features.is_empty() && !features.is_empty() {
        for req_feat in &request.features {
            if !features.contains(req_feat) {
                return format!("feature '{}' not granted by token", req_feat);
            }
        }
    }

    if !request.oauth_scopes.is_empty() && !oauth_scopes.is_empty() {
        for req_scope in &request.oauth_scopes {
            if !oauth_scopes.contains(req_scope) {
                return format!("OAuth scope '{}' not granted by token", req_scope);
            }
        }
    }

    "authorization denied by policy evaluation".into()
}

// ============================================================================
// Deny-check rules (pre-evaluation checks not representable in Datalog)
// ============================================================================

/// Pre-Datalog checks that result in immediate denial.
///
/// Some checks in the old `verify_caveats` are NEGATIVE constraints (deny-if-match)
/// that are awkward in a pure-positive Datalog. We handle these as pre-checks:
/// - Time validity (not_before / not_after)
/// - Organization restriction
/// - User confinement
/// - Machine binding
/// - Command restriction
/// - OAuth provider/scope restriction
/// - Feature set containment
/// - Feature glob patterns
///
/// These run BEFORE the Datalog evaluation and produce Denied errors directly.
/// The Datalog engine handles the POSITIVE allow logic (app/service/action matching).
///
/// NOTE: This is semantically equivalent to having deny rules in Datalog with
/// negation-as-failure. For the STARK circuit, these checks become additional
/// constraints in the arithmetic circuit. The two-phase approach (deny-checks +
/// allow-rules) is an implementation detail that produces identical results to
/// a hypothetical stratified Datalog with negation.
pub fn pre_evaluation_deny_checks(
    caveat_set: &CaveatSet,
    request: &AuthRequest,
) -> Result<(), TokenError> {
    let mut orgs: Vec<u64> = Vec::new();
    let mut confined_users: Vec<String> = Vec::new();
    let mut oauth_providers: Vec<String> = Vec::new();
    let mut oauth_scopes: Vec<String> = Vec::new();
    let mut machines: Vec<String> = Vec::new();
    let mut commands: Vec<String> = Vec::new();
    let mut features: Vec<String> = Vec::new();
    let mut validity_windows: Vec<(Option<i64>, Option<i64>)> = Vec::new();
    let mut feature_globs: Vec<(Vec<String>, Vec<String>)> = Vec::new();

    let mut budgets: Vec<(String, u64)> = Vec::new(); // (budget_id, limit)
    let mut revocable_ids: Vec<String> = Vec::new();

    for wc in caveat_set.first_party_caveats() {
        match pyana_caveats::decode_grant(&wc) {
            Ok(pyana_caveats::PyanaGrant::Organization(id)) => orgs.push(id),
            Ok(pyana_caveats::PyanaGrant::ConfineUser(uid)) => confined_users.push(uid),
            Ok(pyana_caveats::PyanaGrant::OAuthProvider(p)) => oauth_providers.push(p),
            Ok(pyana_caveats::PyanaGrant::OAuthScope(s)) => oauth_scopes.push(s),
            Ok(pyana_caveats::PyanaGrant::FromMachine(m)) => machines.push(m),
            Ok(pyana_caveats::PyanaGrant::Command(c)) => commands.push(c),
            Ok(pyana_caveats::PyanaGrant::Feature(name)) => features.push(name),
            Ok(pyana_caveats::PyanaGrant::ValidityWindow {
                not_before,
                not_after,
            }) => validity_windows.push((not_before, not_after)),
            Ok(pyana_caveats::PyanaGrant::FeatureGlob { include, exclude }) => {
                feature_globs.push((include, exclude))
            }
            // Issue #1: Budget and revocation MUST be checked here.
            Ok(pyana_caveats::PyanaGrant::Budget { id, limit, .. }) => {
                budgets.push((id, limit));
            }
            Ok(pyana_caveats::PyanaGrant::Revocable(token_id)) => {
                revocable_ids.push(token_id);
            }
            Ok(pyana_caveats::PyanaGrant::Unknown(type_id, _)) => {
                // Fail-closed: unknown caveat types MUST deny authorization.
                return Err(TokenError::Denied(format!(
                    "unknown caveat type {} cannot be verified (fail-closed)",
                    type_id
                )));
            }
            // Known types handled elsewhere (App, Service)
            Ok(_) => {}
            Err(e) => {
                return Err(e);
            }
        }
    }

    let now = request.now.unwrap_or_else(|| {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    });

    // Time checks (ALL windows must be satisfied)
    for (not_before, not_after) in &validity_windows {
        if let Some(nb) = not_before {
            if now < *nb {
                return Err(TokenError::Expired);
            }
        }
        if let Some(na) = not_after {
            if now > *na {
                return Err(TokenError::Expired);
            }
        }
    }

    // Organization: match-any.
    // SECURITY: If the token has org restrictions, the request MUST specify an org_id.
    // Otherwise, a token scoped to org=42 could be used on the passthrough path
    // (features-only or time-only requests) without the org being verified.
    if !orgs.is_empty() {
        match request.org_id {
            Some(req_org) => {
                if !orgs.contains(&req_org) {
                    return Err(TokenError::Denied(format!(
                        "token restricted to org(s) {:?}, requested org {}",
                        orgs, req_org
                    )));
                }
            }
            None => {
                return Err(TokenError::Denied(format!(
                    "token restricted to org(s) {:?} but request does not specify org_id",
                    orgs
                )));
            }
        }
    }

    // User: match-any.
    // SECURITY: If the token confines to specific users, the request MUST specify user_id.
    // Otherwise, a user-confined token could bypass the restriction via the passthrough path.
    if !confined_users.is_empty() {
        match &request.user_id {
            Some(req_user) => {
                if !confined_users.contains(req_user) {
                    return Err(TokenError::Denied(format!(
                        "token confined to user(s) {:?}, request is for '{}'",
                        confined_users, req_user
                    )));
                }
            }
            None => {
                return Err(TokenError::Denied(format!(
                    "token confined to user(s) {:?} but request does not specify user_id",
                    confined_users
                )));
            }
        }
    }

    // OAuth provider: match-any.
    // SECURITY: If the token has OAuth provider restrictions, the request MUST specify oauth_provider.
    // Otherwise, a token scoped to a specific provider could be used without provider verification.
    if !oauth_providers.is_empty() {
        match &request.oauth_provider {
            Some(req_provider) => {
                if !oauth_providers.contains(req_provider) {
                    return Err(TokenError::Denied(format!(
                        "token not valid for OAuth provider '{}'",
                        req_provider
                    )));
                }
            }
            None => {
                return Err(TokenError::Denied(
                    "token requires OAuth provider but request omits it".into(),
                ));
            }
        }
    }

    // OAuth scopes: set containment (fail-closed)
    // SECURITY: If the token has OAuth scope restrictions, the request MUST specify oauth_scopes.
    // Otherwise, a token scoped to specific OAuth scopes could be used without scope verification.
    if !oauth_scopes.is_empty() && request.oauth_scopes.is_empty() {
        return Err(TokenError::Denied(
            "token requires OAuth scopes but request specifies none".into(),
        ));
    }
    if !request.oauth_scopes.is_empty() && !oauth_scopes.is_empty() {
        for req_scope in &request.oauth_scopes {
            if !oauth_scopes.contains(req_scope) {
                return Err(TokenError::Denied(format!(
                    "OAuth scope '{}' not granted by token",
                    req_scope
                )));
            }
        }
    }

    // Machine: match-any.
    // SECURITY: If the token is machine-restricted, the request MUST specify machine_id.
    if !machines.is_empty() {
        match &request.machine_id {
            Some(req_machine) => {
                if !machines.contains(req_machine) {
                    return Err(TokenError::Denied(format!(
                        "token not valid for machine '{}'",
                        req_machine
                    )));
                }
            }
            None => {
                return Err(TokenError::Denied(
                    "token restricted to specific machine(s) but request does not specify machine_id".into(),
                ));
            }
        }
    }

    // Command: match-any.
    // SECURITY: If the token has command restrictions, the request MUST specify command.
    // Otherwise, a command-restricted token could be used without command verification.
    if !commands.is_empty() {
        match &request.command {
            Some(req_cmd) => {
                if !commands.contains(req_cmd) {
                    return Err(TokenError::Denied(format!(
                        "token not valid for command '{}'",
                        req_cmd
                    )));
                }
            }
            None => {
                return Err(TokenError::Denied(
                    "token requires command but request omits it".into(),
                ));
            }
        }
    }

    // Features: set containment.
    // SECURITY: If the token has feature restrictions, the request MUST specify features.
    // Otherwise, a feature-restricted token could be used without feature verification.
    if !features.is_empty() && request.features.is_empty() {
        return Err(TokenError::Denied(
            "token requires features but request specifies none".into(),
        ));
    }
    if !request.features.is_empty() && !features.is_empty() {
        for req_feat in &request.features {
            if !features.contains(req_feat) {
                return Err(TokenError::Denied(format!(
                    "feature '{}' not granted by token",
                    req_feat
                )));
            }
        }
    }

    // Feature globs
    if !request.features.is_empty() && !feature_globs.is_empty() {
        for req_feat in &request.features {
            for (include, exclude) in &feature_globs {
                for pat in exclude {
                    if let Ok(matcher) = globset::Glob::new(pat).map(|g| g.compile_matcher()) {
                        if matcher.is_match(req_feat) {
                            return Err(TokenError::Denied(format!(
                                "feature '{}' matches exclusion pattern '{}'",
                                req_feat, pat
                            )));
                        }
                    }
                }
                if !include.is_empty() {
                    let matched = include.iter().any(|pat| {
                        globset::Glob::new(pat)
                            .map(|g| g.compile_matcher().is_match(req_feat))
                            .unwrap_or(false)
                    });
                    if !matched {
                        return Err(TokenError::Denied(format!(
                            "feature '{}' does not match any include pattern",
                            req_feat
                        )));
                    }
                }
            }
        }
    }

    // Issue #1 (CRITICAL): Budget enforcement — MUST run regardless of request dimensions.
    // Previously budgets were collected but never validated here, allowing bypass
    // via the "dimension passthrough" path in verify_token_datalog_full.
    if !budgets.is_empty() {
        if request.budget_states.is_empty() {
            return Err(TokenError::Denied(
                "budget state required for verification: token has budget caveats but no budget state was provided".into(),
            ));
        }
        let request_cost = request.request_cost.unwrap_or(1);
        for (budget_id, limit) in &budgets {
            match request.budget_states.get(budget_id) {
                Some(&remaining) => {
                    // SECURITY: Reject if caller claims more remaining than the token's limit.
                    // This catches obvious spoofing where the caller inflates remaining to bypass.
                    if remaining > *limit {
                        return Err(TokenError::Denied(format!(
                            "budget '{}' state claims remaining ({}) exceeds token limit ({})",
                            budget_id, remaining, limit
                        )));
                    }
                    if remaining < request_cost {
                        return Err(TokenError::Denied(format!(
                            "budget '{}' exhausted: {} remaining, {} required",
                            budget_id, remaining, request_cost
                        )));
                    }
                }
                None => {
                    return Err(TokenError::Denied(format!(
                        "budget state required for budget '{}' but not provided",
                        budget_id
                    )));
                }
            }
        }
    }

    // Issue #1 (CRITICAL): Revocation enforcement — MUST run regardless of request dimensions.
    // Previously revocable_ids were collected but never validated here, allowing bypass
    // via the "dimension passthrough" path in verify_token_datalog_full.
    if !revocable_ids.is_empty() {
        if request.not_revoked.is_empty() {
            return Err(TokenError::Denied(
                "revocation state required for verification: token is revocable but no revocation proof was provided".into(),
            ));
        }
        for token_id in &revocable_ids {
            if !request.not_revoked.contains(token_id) {
                return Err(TokenError::Denied(format!(
                    "token '{}' has been revoked or no non-revocation proof provided",
                    token_id
                )));
            }
        }
    }

    Ok(())
}

/// Full Datalog verification with pre-evaluation deny checks.
///
/// This is the complete replacement for `verify_caveats`:
/// 1. Run deny checks (time, org, user, machine, etc.)
/// 2. Enforce least-privilege dimension checks
/// 3. Run Datalog evaluation for positive authorization (app/service/action)
/// 4. Return clearance or denial
///
/// # Semantics (Least-Privilege)
///
/// A token only authorizes requests in dimensions it EXPLICITLY grants:
/// - Token with `app=X` can only authorize app=X requests; service requests are DENIED.
/// - Token with `service=Y` can only authorize service=Y requests; app requests are DENIED.
/// - Token with both app and service caveats can authorize either dimension.
/// - Token with NO app/service caveats (empty caveat set) is unrestricted.
///
/// Missing caveats mean DENY, not ALLOW. This prevents privilege escalation
/// where an app-scoped token could authorize service requests simply because
/// no service caveat existed.
pub fn verify_token_datalog_full(
    caveat_set: &CaveatSet,
    request: &AuthRequest,
) -> Result<TokenClearance, TokenError> {
    // Phase 1: Deny checks (negative constraints)
    pre_evaluation_deny_checks(caveat_set, request)?;

    // Phase 2: Determine which positive dimensions the token restricts
    let caveats = caveat_set.first_party_caveats();

    let has_app_caveats = caveats
        .iter()
        .any(|wc| wc.caveat_type == crate::pyana_caveats::CAV_APP);
    let has_service_caveats = caveats
        .iter()
        .any(|wc| wc.caveat_type == crate::pyana_caveats::CAV_SERVICE);
    let is_empty = caveats.is_empty(); // unrestricted root token

    // Phase 2b: Least-privilege dimension enforcement.
    // If the request specifies a dimension that the token does NOT grant, DENY.
    // A token must explicitly grant each dimension it's used for.
    if !is_empty {
        if request.service.is_some() && !has_service_caveats {
            return Err(TokenError::Denied(
                "token does not grant service access".into(),
            ));
        }
        if request.app_id.is_some() && !has_app_caveats {
            return Err(TokenError::Denied("token does not grant app access".into()));
        }
    }

    // Determine if the request targets a restricted dimension
    let request_targets_restricted_app = request.app_id.is_some() && has_app_caveats;
    let request_targets_restricted_service = request.service.is_some() && has_service_caveats;

    // If the request targets a restricted dimension, run Datalog
    if request_targets_restricted_app || request_targets_restricted_service || is_empty {
        return verify_token_datalog_trusted(caveat_set, request);
    }

    // If we reach here, the token has caveats (not empty) but the request
    // doesn't specify app_id or service.
    //
    // SECURITY: If the token has dimension caveats (app or service) but the
    // request omits those dimensions entirely, the request is under-specified.
    // We fail-closed to prevent a bypass where an attacker strips dimensions
    // from the request to skip Datalog evaluation.
    let token_has_dimension_caveats = has_app_caveats || has_service_caveats;
    if token_has_dimension_caveats {
        return Err(TokenError::Denied(
            "request is missing required dimensions (app_id or service) that the token \
             restricts — cannot authorize an under-specified request"
                .into(),
        ));
    }

    // Passthrough ONLY for tokens with NO dimension caveats (e.g., features-only
    // or time-only tokens where app/service dimensions are genuinely irrelevant).
    // The deny checks already validated other dimensions.
    let capabilities = extract_capabilities(caveat_set);
    let (expires_at, subject) = extract_metadata(caveat_set);
    Ok(TokenClearance {
        matched_policy: Some("dimension_passthrough".into()),
        capabilities,
        format: TokenFormat::Macaroon,
        expires_at,
        subject,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
#[allow(deprecated)]
mod tests {
    use super::*;
    use crate::pyana_caveats::*;
    use pyana_macaroon::caveat::CaveatSet;
    use pyana_macaroon::caveat::WireCaveat;

    // --- Comparison tests: verify BOTH paths give the same answer ---

    /// Helper: run both old and new verification paths and compare.
    fn verify_both(
        caveat_set: &CaveatSet,
        request: &AuthRequest,
    ) -> (
        Result<crate::pyana_caveats::CaveatVerifyResult, TokenError>,
        Result<TokenClearance, TokenError>,
    ) {
        let old_result = crate::pyana_caveats::verify_caveats(caveat_set, request);
        let new_result = verify_token_datalog_full(caveat_set, request);
        (old_result, new_result)
    }

    /// Assert both paths agree on allow/deny.
    fn assert_paths_agree(caveat_set: &CaveatSet, request: &AuthRequest) {
        let (old, new) = verify_both(caveat_set, request);
        match (&old, &new) {
            (Ok(_), Ok(_)) => {}   // Both allow -- good
            (Err(_), Err(_)) => {} // Both deny -- good
            (Ok(_), Err(e)) => panic!(
                "DISAGREEMENT: old path ALLOWS, new path DENIES with: {:?}",
                e
            ),
            (Err(e), Ok(_)) => panic!(
                "DISAGREEMENT: old path DENIES with {:?}, new path ALLOWS",
                e
            ),
        }
    }

    #[test]
    fn test_comparison_app_match() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_app_wrong_app() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));

        let request = AuthRequest {
            app_id: Some("other-app".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_app_insufficient_actions() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_APP, encode_name_actions("my-app", "r")));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("w".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_service_match() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("http", "rw"),
        ));

        let request = AuthRequest {
            service: Some("http".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_expired() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(None, Some(1000)),
        ));

        let request = AuthRequest {
            now: Some(2000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_not_yet_valid() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(5000), None),
        ));

        let request = AuthRequest {
            now: Some(2000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_validity_window_ok() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        let request = AuthRequest {
            now: Some(3000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_confine_user_match() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

        let request = AuthRequest {
            user_id: Some("alice".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_confine_user_wrong() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

        let request = AuthRequest {
            user_id: Some("bob".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_no_restrictions() {
        let set = CaveatSet::new();
        let request = AuthRequest {
            app_id: Some("any-app".into()),
            action: Some("rwcd".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);
    }

    #[test]
    fn test_comparison_unrestricted_dimension() {
        // An app-scoped token must NOT authorize service requests (least-privilege).
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));

        let request = AuthRequest {
            service: Some("http".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        // Both paths should now DENY this cross-dimension request.
        assert_paths_agree(&set, &request);
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "app-scoped token must not authorize service requests"
        );
    }

    #[test]
    fn test_comparison_features_subset() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_FEATURE, encode_string("ai")));
        set.push(WireCaveat::new(CAV_FEATURE, encode_string("gpu")));

        let request = AuthRequest {
            features: vec!["ai".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        let request2 = AuthRequest {
            features: vec!["quantum".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);
    }

    #[test]
    fn test_comparison_combined_restrictions() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        // All conditions met
        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            user_id: Some("alice".into()),
            now: Some(3000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        // Wrong user
        let request2 = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            user_id: Some("bob".into()),
            now: Some(3000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);

        // Expired
        let request3 = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            user_id: Some("alice".into()),
            now: Some(6000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request3);
    }

    #[test]
    fn test_comparison_oauth_provider() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_PROVIDER, encode_string("github")));

        let request = AuthRequest {
            oauth_provider: Some("github".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        let request2 = AuthRequest {
            oauth_provider: Some("google".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);
    }

    #[test]
    fn test_comparison_command() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_COMMAND, encode_string("deploy")));
        set.push(WireCaveat::new(CAV_COMMAND, encode_string("status")));

        let request = AuthRequest {
            command: Some("deploy".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        let request2 = AuthRequest {
            command: Some("rollback".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);
    }

    #[test]
    fn test_comparison_feature_glob_include() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_FEATURE_GLOB,
            encode_feature_glob(&["src/components/**".into()], &[]),
        ));

        let request = AuthRequest {
            features: vec!["src/components/nav.tsx".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        let request2 = AuthRequest {
            features: vec!["src/config/settings.ts".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);
    }

    #[test]
    fn test_comparison_feature_glob_exclude() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_FEATURE_GLOB,
            encode_feature_glob(&["src/**".into()], &["src/components/secrets.ts".into()]),
        ));

        let request = AuthRequest {
            features: vec!["src/components/nav.tsx".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request);

        let request2 = AuthRequest {
            features: vec!["src/components/secrets.ts".into()],
            now: Some(1700000000),
            ..Default::default()
        };
        assert_paths_agree(&set, &request2);
    }

    // --- Direct Datalog verification tests ---

    #[test]
    fn test_datalog_unrestricted_allows() {
        let set = CaveatSet::new(); // empty = unrestricted
        let request = AuthRequest {
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(result.is_ok());
    }

    #[test]
    fn test_datalog_app_action_allows() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("dashboard", "rw"),
        ));

        let request = AuthRequest {
            app_id: Some("dashboard".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(result.is_ok());
    }

    #[test]
    fn test_datalog_app_action_denies_wrong_action() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("dashboard", "r"),
        ));

        let request = AuthRequest {
            app_id: Some("dashboard".into()),
            action: Some("w".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(result.is_err());
    }

    #[test]
    fn test_datalog_expired_denies() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(None, Some(1000)),
        ));

        let request = AuthRequest {
            now: Some(2000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(result.is_err());
    }

    #[test]
    fn test_datalog_trace_is_produced() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        // Use the full trace-producing version
        pre_evaluation_deny_checks(&set, &request).unwrap();
        let result = verify_token_datalog(&set, &request);
        assert!(result.is_ok());
        let dr = result.unwrap();
        assert!(!dr.trace.steps.is_empty());
        match dr.trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                assert!(policy_rule_id > 0);
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }

    // =========================================================================
    // Least-privilege dimension enforcement tests (P2 security fix)
    // =========================================================================

    #[test]
    fn test_app_scoped_token_cannot_auth_service_request() {
        // Token: app=dashboard with rw
        // Request: service=compute-api with r
        // Expected: DENY (token does not grant service access)
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("dashboard", "rw"),
        ));

        let request = AuthRequest {
            service: Some("compute-api".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "app-scoped token must NOT authorize service requests"
        );
        match result.unwrap_err() {
            TokenError::Denied(msg) => {
                assert!(msg.contains("service"), "denial reason: {}", msg);
            }
            other => panic!("expected Denied, got: {:?}", other),
        }
    }

    #[test]
    fn test_service_scoped_token_cannot_auth_app_request() {
        // Token: service=compute-api with rw
        // Request: app=dashboard with r
        // Expected: DENY (token does not grant app access)
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("compute-api", "rw"),
        ));

        let request = AuthRequest {
            app_id: Some("dashboard".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "service-scoped token must NOT authorize app requests"
        );
        match result.unwrap_err() {
            TokenError::Denied(msg) => {
                assert!(msg.contains("app"), "denial reason: {}", msg);
            }
            other => panic!("expected Denied, got: {:?}", other),
        }
    }

    #[test]
    fn test_token_with_both_dimensions_can_auth_either() {
        // Token: app=dashboard rw + service=compute-api rw
        // Request for app: should ALLOW
        // Request for service: should ALLOW
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("dashboard", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("compute-api", "rw"),
        ));

        let app_request = AuthRequest {
            app_id: Some("dashboard".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &app_request);
        assert!(
            result.is_ok(),
            "token with both dimensions should allow app request"
        );

        let svc_request = AuthRequest {
            service: Some("compute-api".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &svc_request);
        assert!(
            result.is_ok(),
            "token with both dimensions should allow service request"
        );
    }

    #[test]
    fn test_token_with_neither_dimension_is_useless_for_app_and_service() {
        // Token: only has a confine_user caveat (no app, no service)
        // Request for app: should DENY
        // Request for service: should DENY
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

        let app_request = AuthRequest {
            app_id: Some("dashboard".into()),
            action: Some("r".into()),
            user_id: Some("alice".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &app_request);
        assert!(
            result.is_err(),
            "token without app/service grants must deny app requests"
        );

        let svc_request = AuthRequest {
            service: Some("compute-api".into()),
            action: Some("r".into()),
            user_id: Some("alice".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &svc_request);
        assert!(
            result.is_err(),
            "token without app/service grants must deny service requests"
        );
    }

    #[test]
    fn test_empty_token_is_unrestricted() {
        // Empty caveat set = root/unrestricted token (no caveats to restrict)
        // Should allow anything.
        let set = CaveatSet::new();

        let request = AuthRequest {
            app_id: Some("anything".into()),
            service: Some("anything".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "empty (unrestricted) token should allow all requests"
        );
    }

    #[test]
    fn test_least_privilege_old_path_agrees() {
        // Verify the old verify_caveats path also denies cross-dimension requests.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("dashboard", "rw"),
        ));

        // App token -> service request: both paths should deny
        let request = AuthRequest {
            service: Some("compute-api".into()),
            action: Some("r".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let old_result = crate::pyana_caveats::verify_caveats(&set, &request);
        let new_result = verify_token_datalog_full(&set, &request);
        assert!(
            old_result.is_err(),
            "old path must also deny cross-dimension"
        );
        assert!(new_result.is_err(), "new path must deny cross-dimension");
    }

    #[test]
    fn test_dimension_passthrough_denied_when_token_has_service_caveat() {
        // SECURITY: A token with a service caveat must NOT be authorized when
        // the request omits the service dimension. This prevents bypassing
        // Datalog evaluation by stripping dimensions from the request.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("payments", "rw"),
        ));

        // Request with no service or app dimension — must FAIL.
        let request = AuthRequest {
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "token with service caveat + request without service dimension must fail"
        );
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("missing required dimensions"),
            "error should mention missing dimensions, got: {err_msg}"
        );
    }

    #[test]
    fn test_dimension_passthrough_denied_when_token_has_app_caveat() {
        // Same as above but with app caveats.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("admin-panel", "rw"),
        ));

        // Request with no app or service dimension — must FAIL.
        let request = AuthRequest {
            now: Some(1700000000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "token with app caveat + request without app dimension must fail"
        );
    }

    #[test]
    fn test_dimension_passthrough_allowed_for_non_dimension_caveats() {
        // Tokens with ONLY non-dimension caveats (e.g., time, user, features)
        // should still pass through when the request omits app/service.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));
        set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

        let request = AuthRequest {
            user_id: Some("alice".into()),
            now: Some(3000),
            ..Default::default()
        };
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "token without dimension caveats should still allow passthrough, got: {:?}",
            result.unwrap_err()
        );
        let clearance = result.unwrap();
        assert_eq!(
            clearance.matched_policy,
            Some("dimension_passthrough".into())
        );
    }

    // =========================================================================
    // Security tests: fail-closed for OAuth/command/features
    // =========================================================================

    #[test]
    fn test_oauth_provider_fails_closed_when_request_omits_provider() {
        // ATTACK: Token has OAuthProvider("github") restriction.
        // Request omits oauth_provider entirely.
        // Previously this would PASS (fail-open). Now it must DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_PROVIDER, encode_string("github")));

        let request = AuthRequest {
            now: Some(1700000000),
            // oauth_provider: None -- omitted!
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_err(),
            "token with OAuth provider restriction must deny when request omits oauth_provider"
        );
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("OAuth provider"),
            "error should mention OAuth provider, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_command_fails_closed_when_request_omits_command() {
        // ATTACK: Token has Command("deploy") restriction.
        // Request omits command entirely.
        // Previously this would PASS (fail-open). Now it must DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_COMMAND, encode_string("deploy")));

        let request = AuthRequest {
            now: Some(1700000000),
            // command: None -- omitted!
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_err(),
            "token with command restriction must deny when request omits command"
        );
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("command"),
            "error should mention command, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_features_fails_closed_when_request_omits_features() {
        // ATTACK: Token has Feature("ai-engine") restriction.
        // Request omits features entirely.
        // Previously this would PASS (fail-open). Now it must DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_FEATURE, encode_string("ai-engine")));

        let request = AuthRequest {
            now: Some(1700000000),
            features: vec![], // empty -- omitted!
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_err(),
            "token with feature restriction must deny when request omits features"
        );
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("features"),
            "error should mention features, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_oauth_provider_allows_when_request_provides_matching_provider() {
        // Ensure the fail-closed fix doesn't break the happy path.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_PROVIDER, encode_string("github")));

        let request = AuthRequest {
            oauth_provider: Some("github".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_ok(),
            "matching OAuth provider should pass, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_command_allows_when_request_provides_matching_command() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_COMMAND, encode_string("deploy")));

        let request = AuthRequest {
            command: Some("deploy".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_ok(),
            "matching command should pass, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_features_allows_when_request_provides_matching_features() {
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_FEATURE, encode_string("ai-engine")));

        let request = AuthRequest {
            features: vec!["ai-engine".into()],
            now: Some(1700000000),
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_ok(),
            "matching features should pass, got: {:?}",
            result.unwrap_err()
        );
    }

    // =========================================================================
    // OAuth scopes fail-closed tests
    // =========================================================================

    #[test]
    fn test_oauth_scopes_fails_closed_when_request_omits_scopes() {
        // ATTACK: Token has OAuthScope("repo") restriction.
        // Request omits oauth_scopes entirely.
        // Previously this would PASS (fail-open). Now it must DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_SCOPE, encode_string("repo")));

        let request = AuthRequest {
            now: Some(1700000000),
            oauth_scopes: vec![], // empty -- omitted!
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_err(),
            "token with OAuth scope restriction must deny when request omits oauth_scopes"
        );
        let err_msg = format!("{}", result.unwrap_err());
        assert!(
            err_msg.contains("OAuth scopes"),
            "error should mention OAuth scopes, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_oauth_scopes_allows_when_request_provides_matching_scopes() {
        // Ensure the fail-closed fix doesn't break the happy path.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_SCOPE, encode_string("repo")));

        let request = AuthRequest {
            oauth_scopes: vec!["repo".into()],
            now: Some(1700000000),
            ..Default::default()
        };

        let result = pre_evaluation_deny_checks(&set, &request);
        assert!(
            result.is_ok(),
            "matching OAuth scopes should pass, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_oauth_scopes_fails_closed_old_path_agrees() {
        // Verify both paths agree on the fail-closed behavior.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(CAV_OAUTH_SCOPE, encode_string("repo")));
        set.push(WireCaveat::new(CAV_OAUTH_SCOPE, encode_string("read:org")));

        let request = AuthRequest {
            now: Some(1700000000),
            oauth_scopes: vec![], // empty -- omitted!
            ..Default::default()
        };

        let old_result = crate::pyana_caveats::verify_caveats(&set, &request);
        assert!(
            old_result.is_err(),
            "old path must also deny when request omits oauth_scopes"
        );
    }

    // =========================================================================
    // valid_after (not_before) Datalog enforcement tests
    // =========================================================================

    #[test]
    fn test_datalog_valid_after_denies_before_activation() {
        // Token with valid_after=5000 but request time is 2000 (before activation).
        // The STARK trace must NOT produce an allow conclusion.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(5000), None),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(2000), // before valid_after
            ..Default::default()
        };

        // Pre-evaluation deny checks catch this (trusted mode)
        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "token with valid_after must deny requests before activation time"
        );
    }

    #[test]
    fn test_datalog_valid_after_allows_after_activation() {
        // Token with valid_after=1000, request time is 3000 (after activation).
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), None),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(3000), // after valid_after
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "token with valid_after should allow requests after activation, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_datalog_valid_after_at_exact_activation_time() {
        // Token with valid_after=3000, request time is exactly 3000.
        // Should ALLOW (>= semantics).
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(3000), None),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(3000), // exactly at activation
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "token should allow at exact activation time (>= semantics), got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_datalog_full_window_allows_within() {
        // Token with valid_after=1000 AND valid_until=5000, request at 3000.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(3000), // within window
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "token should allow within full window, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_datalog_full_window_denies_before() {
        // Token with valid_after=1000 AND valid_until=5000, request at 500.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(500), // before valid_after
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "token should deny before activation in full window"
        );
    }

    #[test]
    fn test_datalog_full_window_denies_after() {
        // Token with valid_after=1000 AND valid_until=5000, request at 6000.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(6000), // after valid_until
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(result.is_err(), "token should deny after expiry in full window");
    }

    #[test]
    fn test_datalog_valid_after_unrestricted_token() {
        // Unrestricted token (no app/service) with valid_after=5000.
        // Request at time 3000 should DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(5000), None),
        ));

        let request = AuthRequest {
            now: Some(3000), // before activation
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "unrestricted token with valid_after must deny before activation"
        );
    }

    #[test]
    fn test_datalog_valid_after_unrestricted_token_allows() {
        // Unrestricted token (no app/service) with valid_after=1000.
        // Request at time 3000 should ALLOW.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), None),
        ));

        let request = AuthRequest {
            now: Some(3000), // after activation
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "unrestricted token with valid_after should allow after activation, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_datalog_valid_after_service_token() {
        // Service token with valid_after=5000, request at 3000 should DENY.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("payments", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(5000), None),
        ));

        let request = AuthRequest {
            service: Some("payments".into()),
            action: Some("r".into()),
            now: Some(3000), // before activation
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_err(),
            "service token with valid_after must deny before activation"
        );
    }

    #[test]
    fn test_datalog_valid_after_service_token_allows() {
        // Service token with valid_after=1000, request at 3000 should ALLOW.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_SERVICE,
            encode_name_actions("payments", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), None),
        ));

        let request = AuthRequest {
            service: Some("payments".into()),
            action: Some("r".into()),
            now: Some(3000), // after activation
            ..Default::default()
        };

        let result = verify_token_datalog_full(&set, &request);
        assert!(
            result.is_ok(),
            "service token with valid_after should allow after activation, got: {:?}",
            result.unwrap_err()
        );
    }

    #[test]
    fn test_datalog_valid_after_trace_covers_not_before() {
        // Verify that the STARK trace actually includes the valid_after check.
        // When a token has valid_after=1000 and request_time=3000, the trace
        // should fire a rule that includes the GreaterThanOrEqual check.
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), None),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(3000),
            ..Default::default()
        };

        let result = verify_token_datalog(&set, &request);
        assert!(result.is_ok());
        let dr = result.unwrap();
        match dr.trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                // Must be Rule 13 (APP_ACTION_NOT_BEFORE) since token has
                // valid_after only (no valid_until).
                assert_eq!(
                    policy_rule_id,
                    rule_ids::APP_ACTION_NOT_BEFORE,
                    "expected rule 13 (APP_ACTION_NOT_BEFORE), got rule {}",
                    policy_rule_id
                );
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }

    #[test]
    fn test_datalog_full_window_trace_fires_correct_rule() {
        // When both valid_after and valid_until are present, the full-window
        // rule (16) should fire, not the valid_until-only rule (10).
        let mut set = CaveatSet::new();
        set.push(WireCaveat::new(
            CAV_APP,
            encode_name_actions("my-app", "rw"),
        ));
        set.push(WireCaveat::new(
            CAV_VALIDITY_WINDOW,
            encode_validity_window(Some(1000), Some(5000)),
        ));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("r".into()),
            now: Some(3000),
            ..Default::default()
        };

        let result = verify_token_datalog(&set, &request);
        assert!(result.is_ok());
        let dr = result.unwrap();
        match dr.trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                assert_eq!(
                    policy_rule_id,
                    rule_ids::APP_ACTION_FULL_WINDOW,
                    "expected rule 16 (APP_ACTION_FULL_WINDOW), got rule {}",
                    policy_rule_id
                );
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }
}
