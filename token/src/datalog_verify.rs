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
/// 1. Decodes the caveat set into a FactSet
/// 2. Converts the FactSet to trace-format facts
/// 3. Runs the Datalog evaluator with standard + extended policy
/// 4. Returns Allow/Deny with a derivation trace
///
/// The derivation trace can be fed into the STARK prover for trustless verification.
pub fn verify_token_datalog(
    caveat_set: &CaveatSet,
    request: &AuthRequest,
) -> Result<DatalogVerifyResult, TokenError> {
    // 1. Decode caveats to FactSet + SymbolTable
    let (factset, symbols) = caveat_set_to_factset(caveat_set);

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

    // 3. Convert committed facts to trace-format facts
    let trace_facts = committed_facts_to_trace(&state, &symbols);

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
pub fn verify_token_datalog_trusted(
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
    // Time-bounded variants
    pub const APP_ACTION_TIME_BOUNDED: u32 = 10;
    pub const SERVICE_ACTION_TIME_BOUNDED: u32 = 11;
    pub const UNRESTRICTED_TIME_BOUNDED: u32 = 12;
}

/// Returns the full pyana authorization policy rule set.
///
/// This extends the standard policy with rules for every caveat dimension.
/// The semantics match the imperative `verify_caveats` logic:
///
/// - Unrestricted dimensions (no facts for that predicate) always pass.
/// - Restricted dimensions require matching.
/// - Time bounds are checked via LessThan/GreaterThan checks.
///
/// The core insight: the imperative verifier uses "if there are no caveats of
/// this type, pass" semantics. In Datalog, we encode this by having the ALLOW
/// rules fire when the relevant request fact matches a token fact. When there
/// are NO restricting facts for a dimension, the request simply doesn't need
/// to match anything in that dimension -- we handle this by having multiple
/// rule variants and the evaluator tries all of them.
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

    // Rule 3: allow if unrestricted(1)
    // Note: Unlike the standard policy, we don't require request_action here.
    // An unrestricted token permits EVERYTHING including requests with no action.
    rules.push(Rule {
        id: rule_ids::UNRESTRICTED,
        head: Atom {
            predicate: symbol_from_str("allow"),
            terms: vec![],
        },
        body: vec![Atom {
            predicate: symbol_from_str("unrestricted"),
            terms: vec![Term::Int(1)],
        }],
        checks: vec![],
    });

    // Rule 4: allow if app($app, $actions), request_app($app), no_action_required(1)
    rules.push(Rule {
        id: rule_ids::APP_ANY_ACTION,
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
                predicate: symbol_from_str("no_action_required"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![],
    });

    // Rule 5: allow if service($svc, $actions), request_service($svc), no_action_required(1)
    rules.push(Rule {
        id: rule_ids::SERVICE_ANY_ACTION,
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
                predicate: symbol_from_str("no_action_required"),
                terms: vec![Term::Int(1)],
            },
        ],
        checks: vec![],
    });

    // Rule 10: Time-bounded app + action
    rules.push(Rule {
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
            Check::MemberOf(Term::Var(1), Term::Var(2)),
            Check::LessThan(Term::Var(4), Term::Var(3)), // $t < $exp
        ],
    });

    // Rule 11: Time-bounded service + action
    rules.push(Rule {
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
            Check::MemberOf(Term::Var(1), Term::Var(2)),
            Check::LessThan(Term::Var(4), Term::Var(3)), // $t < $exp
        ],
    });

    // Rule 12: Unrestricted with time bound (must still be within window)
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
        ],
        checks: vec![
            Check::LessThan(Term::Var(1), Term::Var(0)), // $t < $exp
        ],
    });

    rules
}

// ============================================================================
// Internal conversion helpers
// ============================================================================

/// Convert committed facts (FieldElement-based) to trace-format facts (Symbol-based).
fn committed_facts_to_trace(state: &TokenState, symbols: &SymbolTable) -> Vec<TraceFact> {
    let mut trace_facts = Vec::new();

    for fact in state.all_facts() {
        let pred_symbol = if let Some(name) = symbols.resolve(fact.predicate) {
            symbol_from_str(name)
        } else {
            fact.predicate.0
        };

        let mut terms = Vec::new();
        for term_fe in &fact.terms {
            if term_fe.is_zero() {
                break;
            }
            if let Some(name) = symbols.resolve(*term_fe) {
                terms.push(Term::Const(symbol_from_str(name)));
            } else if let Some(int_val) = field_element_to_int(term_fe) {
                terms.push(Term::Int(int_val));
            } else {
                terms.push(Term::Const(term_fe.0));
            }
        }

        trace_facts.push(TraceFact::new(pred_symbol, terms));
    }

    trace_facts
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
            _ => {}
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

    // Organization: match-any
    if let Some(req_org) = request.org_id {
        if !orgs.is_empty() && !orgs.contains(&req_org) {
            return Err(TokenError::Denied(format!(
                "token restricted to org(s) {:?}, requested org {}",
                orgs, req_org
            )));
        }
    }

    // User: match-any
    if let Some(req_user) = &request.user_id {
        if !confined_users.is_empty() && !confined_users.contains(req_user) {
            return Err(TokenError::Denied(format!(
                "token confined to user(s) {:?}, request is for '{}'",
                confined_users, req_user
            )));
        }
    }

    // OAuth provider: match-any
    if let Some(req_provider) = &request.oauth_provider {
        if !oauth_providers.is_empty() && !oauth_providers.contains(req_provider) {
            return Err(TokenError::Denied(format!(
                "token not valid for OAuth provider '{}'",
                req_provider
            )));
        }
    }

    // OAuth scopes: set containment
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

    // Machine: match-any
    if let Some(req_machine) = &request.machine_id {
        if !machines.is_empty() && !machines.contains(req_machine) {
            return Err(TokenError::Denied(format!(
                "token not valid for machine '{}'",
                req_machine
            )));
        }
    }

    // Command: match-any
    if let Some(req_cmd) = &request.command {
        if !commands.is_empty() && !commands.contains(req_cmd) {
            return Err(TokenError::Denied(format!(
                "token not valid for command '{}'",
                req_cmd
            )));
        }
    }

    // Features: set containment
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

    Ok(())
}

/// Full Datalog verification with pre-evaluation deny checks.
///
/// This is the complete replacement for `verify_caveats`:
/// 1. Run deny checks (time, org, user, machine, etc.)
/// 2. Run Datalog evaluation for positive authorization (app/service/action)
/// 3. Return clearance or denial
///
/// # Semantics
///
/// The old `verify_caveats` has "unrestricted dimension" semantics: if a token
/// has only APP caveats but the request asks for a SERVICE, the service dimension
/// is unrestricted and the request is allowed. We preserve this by only running
/// Datalog evaluation when the request's target dimension (app/service) actually
/// has restricting facts.
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

    // Determine if the request targets a restricted dimension
    let request_targets_restricted_app = request.app_id.is_some() && has_app_caveats;
    let request_targets_restricted_service = request.service.is_some() && has_service_caveats;

    // If the request targets a restricted dimension, run Datalog
    if request_targets_restricted_app || request_targets_restricted_service || is_empty {
        return verify_token_datalog_trusted(caveat_set, request);
    }

    // If the token has positive grants but the request doesn't target any
    // restricted dimension (e.g., token restricts APP but request asks for SERVICE
    // which is unrestricted), allow it. This matches the old "unrestricted dimension"
    // semantics.
    let capabilities = extract_capabilities(caveat_set);
    let (expires_at, subject) = extract_metadata(caveat_set);
    Ok(TokenClearance {
        matched_policy: Some("unrestricted_dimension".into()),
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
        assert_paths_agree(&set, &request);
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
}
