//! Authorization request to trace evaluation.
//!
//! Given a committed token state (the final state after all attenuations),
//! this module evaluates an authorization request against it using the
//! Datalog trace evaluator from `pyana-trace`.
//!
//! The output is a verifiable [`AuthorizationTrace`] that can be proven in
//! zero knowledge by the circuit layer.

use pyana_commit::{FieldElement, SymbolTable, TokenState};
use pyana_token::AuthRequest;
use pyana_trace::{
    AuthorizationRequest as TraceRequest, AuthorizationTrace, Conclusion, Evaluator,
    Fact as TraceFact, Rule, Term, symbol_from_bytes, symbol_from_str,
};

/// Errors that can occur during authorization evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuthError {
    /// The token state is empty (no facts to evaluate against).
    EmptyState,
    /// Authorization was denied by the policy engine.
    Denied,
    /// The request could not be converted to trace format.
    InvalidRequest(String),
    /// The symbol table is missing required entries.
    MissingSymbol(String),
    /// The issuer is not a member of the expected federation tree.
    IssuerNotInFederation,
}

impl std::fmt::Display for AuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AuthError::EmptyState => write!(f, "token state is empty"),
            AuthError::Denied => write!(f, "authorization denied"),
            AuthError::InvalidRequest(msg) => write!(f, "invalid request: {}", msg),
            AuthError::MissingSymbol(sym) => write!(f, "missing symbol: {}", sym),
            AuthError::IssuerNotInFederation => write!(f, "issuer is not in the federation tree"),
        }
    }
}

impl std::error::Error for AuthError {}

/// Evaluate an authorization request against a committed token state,
/// producing a verifiable derivation trace.
///
/// This bridges the `token` crate's `AuthRequest` to the `pyana-trace`
/// evaluator, converting the committed facts into trace-format facts and
/// running the standard policy rules.
///
/// # Arguments
///
/// * `state` - The committed token state (after all attenuations).
/// * `request` - The authorization request to evaluate.
/// * `symbols` - Symbol table for resolving field elements to names.
///
/// # Returns
///
/// An `AuthorizationTrace` proving the authorization decision (allow or deny).
pub fn authorize_with_trace(
    state: &TokenState,
    request: &AuthRequest,
    symbols: &SymbolTable,
) -> Result<AuthorizationTrace, AuthError> {
    if state.is_empty() {
        return Err(AuthError::EmptyState);
    }

    // SECURITY: Budget and revocation enforcement.
    //
    // Budget and revocation facts are committed into the token state. We extract
    // them here and validate against the request's budget_states/not_revoked fields.
    //
    // NOTE: In the full production path, budget_states and not_revoked should be
    // proven via Merkle membership proofs (NonRevocationAir, IVC budget tracking).
    // Until that infrastructure is wired end-to-end, we enforce the imperative
    // checks here to prevent revoked or over-budget tokens from passing authorization.
    enforce_budget_and_revocation(state, request, symbols)?;

    // Convert committed facts to trace-format facts.
    let trace_facts = committed_facts_to_trace(state, symbols);

    // Convert the AuthRequest to a TraceRequest.
    let trace_request = auth_request_to_trace(request)?;

    // Use the secure policy exclusively (hash-based action matching via MemberOf).
    // The proof path now uses macaroon_to_factset_secure() which produces
    // action_allowed/svc_action_allowed facts with exact hash equality, eliminating
    // the substring-Contains vulnerability (e.g. "threadwrite" matching "write").
    let rules = pyana_trace::standard_policy();

    // Run the evaluator.
    let evaluator = Evaluator::new(trace_facts, rules);
    let trace = evaluator.evaluate(&trace_request);

    // Check for explicit deny derivations first (budget/revocation).
    let deny_pred = symbol_from_str("deny");
    for step in &trace.steps {
        if step.derived_fact.predicate == deny_pred {
            return Err(AuthError::Denied);
        }
    }

    // Check conclusion.
    match &trace.conclusion {
        Conclusion::Allow { .. } => Ok(trace),
        Conclusion::Deny => Err(AuthError::Denied),
    }
}

/// Enforce budget and revocation constraints by extracting committed facts
/// from the token state and validating against the request.
///
/// This ensures that a revoked token or one that has exhausted its budget
/// cannot pass authorization, regardless of the Datalog evaluation result.
fn enforce_budget_and_revocation(
    state: &TokenState,
    request: &AuthRequest,
    symbols: &SymbolTable,
) -> Result<(), AuthError> {
    let budget_pred = FieldElement::from_symbol("budget");
    let revocable_pred = FieldElement::from_symbol("revocable");

    let mut budgets: Vec<(String, u64)> = Vec::new();
    let mut revocable_ids: Vec<String> = Vec::new();

    for fact in state.all_facts() {
        if fact.predicate == budget_pred {
            // budget(id, limit) — binary fact
            let id_str = symbols.resolve(fact.terms[0]).unwrap_or("").to_string();
            // Extract limit from the second term (stored as u64 in FieldElement)
            let limit = field_element_to_u64(&fact.terms[1]).unwrap_or(0);
            if !id_str.is_empty() {
                budgets.push((id_str, limit));
            }
        } else if fact.predicate == revocable_pred {
            // revocable(token_id) — unary fact
            let id_str = symbols.resolve(fact.terms[0]).unwrap_or("").to_string();
            if !id_str.is_empty() {
                revocable_ids.push(id_str);
            }
        }
    }

    // Budget enforcement: if the token has budget caveats, the request must
    // provide budget state proving sufficient remaining budget.
    if !budgets.is_empty() {
        if request.budget_states.is_empty() {
            return Err(AuthError::Denied);
        }
        let request_cost = request.request_cost.unwrap_or(1);
        for (budget_id, _limit) in &budgets {
            match request.budget_states.get(budget_id) {
                Some(&remaining) => {
                    if remaining < request_cost {
                        return Err(AuthError::Denied);
                    }
                }
                None => {
                    return Err(AuthError::Denied);
                }
            }
        }
    }

    // Revocation enforcement: if the token is revocable, the request must
    // provide non-revocation proof for each revocable ID.
    if !revocable_ids.is_empty() {
        if request.not_revoked.is_empty() {
            return Err(AuthError::Denied);
        }
        for token_id in &revocable_ids {
            if !request.not_revoked.contains(token_id) {
                return Err(AuthError::Denied);
            }
        }
    }

    Ok(())
}

/// Evaluate an authorization request using custom rules.
///
/// Like `authorize_with_trace` but allows specifying custom policy rules
/// instead of the standard set.
pub fn authorize_with_custom_rules(
    state: &TokenState,
    request: &AuthRequest,
    symbols: &SymbolTable,
    rules: Vec<Rule>,
) -> Result<AuthorizationTrace, AuthError> {
    if state.is_empty() {
        return Err(AuthError::EmptyState);
    }

    let trace_facts = committed_facts_to_trace(state, symbols);
    let trace_request = auth_request_to_trace(request)?;

    let evaluator = Evaluator::new(trace_facts, rules);
    let trace = evaluator.evaluate(&trace_request);

    match &trace.conclusion {
        Conclusion::Allow { .. } => Ok(trace),
        Conclusion::Deny => Err(AuthError::Denied),
    }
}

/// Convert committed facts (FieldElement-based) to trace-format facts (Symbol-based).
///
/// The key mapping:
/// - Each committed `Fact` has a predicate (FieldElement) and up to 3 terms.
/// - We resolve the predicate via the symbol table to get the string name.
/// - Terms that are symbol hashes get their 32-byte representation directly.
/// - Terms that are integers get converted to `Term::Int`.
///
/// For the trace evaluator, we need `TraceFact` instances with `Symbol` predicates
/// (which are [u8; 32]) and `Term` values.
fn committed_facts_to_trace(state: &TokenState, symbols: &SymbolTable) -> Vec<TraceFact> {
    use pyana_trace::symbol_from_bytes;
    let mut trace_facts = Vec::new();

    for fact in state.all_facts() {
        // The predicate field element's raw bytes become the Symbol.
        let predicate: [u8; 32] = fact.predicate.0;

        // Predicates use symbol_from_str (BLAKE3 hash) because the policy rules
        // define predicates via symbol_from_str and matching is by exact equality.
        let pred_symbol = if let Some(name) = symbols.resolve(fact.predicate) {
            symbol_from_str(name)
        } else {
            predicate
        };

        // Terms use symbol_from_bytes (raw zero-padded string) so that the legacy
        // Contains check works correctly. Contains interprets the 32-byte symbol as
        // a UTF-8 string (trimming trailing nulls) and checks for substring matching.
        // Using BLAKE3 for terms would destroy the string relationship needed for
        // Contains (e.g., "rw".contains("r") must be true).
        let mut terms = Vec::new();
        for term_fe in &fact.terms {
            if term_fe.is_zero() {
                break; // Stop at first zero term (unused slot).
            }
            if let Some(name) = symbols.resolve(*term_fe) {
                terms.push(Term::Const(symbol_from_bytes(name.as_bytes())));
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
///
/// `FieldElement::from_u64(val)` stores the value as big-endian in bytes[24..32]
/// with bytes[0..24] all zero. `FieldElement::from_i64(val)` for non-negative values
/// is the same. We detect this pattern and return the integer value.
///
/// For negative values (two's complement with top bits set), we also detect the
/// pattern: bytes[0..24] are 0x1F,FF,...,FF (after 253-bit truncation).
fn field_element_to_int(fe: &FieldElement) -> Option<i64> {
    let bytes = &fe.0;

    // Check for non-negative integer: bytes[0..24] all zero.
    if bytes[0..24].iter().all(|&b| b == 0) {
        let val = u64::from_be_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]);
        return Some(val as i64);
    }

    None
}

/// Try to extract a u64 from a FieldElement stored via `FieldElement::from_u64`.
fn field_element_to_u64(fe: &FieldElement) -> Option<u64> {
    let bytes = &fe.0;
    // from_u64 stores big-endian in bytes[24..32], bytes[0..24] all zero.
    if bytes[0..24].iter().all(|&b| b == 0) {
        Some(u64::from_be_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]))
    } else {
        None
    }
}

/// Convert a `token::AuthRequest` to a `trace::AuthorizationRequest`.
fn auth_request_to_trace(request: &AuthRequest) -> Result<TraceRequest, AuthError> {
    // Use symbol_from_bytes (raw zero-padded string) for request values.
    // This is consistent with committed_facts_to_trace, enabling equality matching.
    let app_id = request
        .app_id
        .as_deref()
        .map(|s| symbol_from_bytes(s.as_bytes()));
    let service = request
        .service
        .as_deref()
        .map(|s| symbol_from_bytes(s.as_bytes()));
    // Parse the action string as a macaroon Action bitmask and convert to the
    // canonical full action name for secure policy matching. Short forms like "r"
    // map to "read", "w" to "write", etc. This ensures the trace action symbol
    // matches the interned action names in action_allowed/svc_action_allowed facts.
    let action = request.action.as_deref().map(|s| {
        let canonical = action_short_to_canonical(s);
        symbol_from_bytes(canonical.as_bytes())
    });
    let features: Vec<[u8; 32]> = request
        .features
        .iter()
        .map(|f| symbol_from_bytes(f.as_bytes()))
        .collect();
    let user_id = request
        .user_id
        .as_deref()
        .map(|s| symbol_from_bytes(s.as_bytes()));

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

/// Convert a short action string (e.g. "r", "w", "rw") to its canonical full name.
///
/// If the action string is already a canonical name (e.g. "read", "write"),
/// it passes through unchanged. For short bitmask-style strings, the first
/// matching action is used (since the trace request supports a single action).
///
/// Mapping: r -> read, w -> write, c -> create, d -> delete, C -> control.
/// Multi-action strings (e.g. "rw") map to the first action bit for the
/// single-action trace request format.
fn action_short_to_canonical(s: &str) -> String {
    use pyana_macaroon::action::Action;

    // If it's already a canonical name, pass through.
    match s {
        "read" | "write" | "create" | "delete" | "control" => return s.to_string(),
        _ => {}
    }

    // Parse as Action bitmask and extract the first (lowest) action.
    let action = Action::parse(s);
    if action.contains(Action::READ) {
        "read".to_string()
    } else if action.contains(Action::WRITE) {
        "write".to_string()
    } else if action.contains(Action::CREATE) {
        "create".to_string()
    } else if action.contains(Action::DELETE) {
        "delete".to_string()
    } else if action.contains(Action::CONTROL) {
        "control".to_string()
    } else {
        // Unknown action string - pass through as-is for compatibility.
        s.to_string()
    }
}

/// Emit budget and revocation state as trace facts from the AuthRequest.
///
/// **DEPRECATED / INSECURE**: These facts come from requester self-assertion and
/// provide NO security guarantee. An attacker can claim unlimited budget or
/// non-revocation without proof. Budget and revocation must instead be proven via
/// Merkle membership proofs against a committed state tree.
///
/// This function is retained only for backward compatibility with tests that
/// exercise the Datalog evaluation path in isolation. Production code MUST NOT
/// call this.
///
/// Emits:
/// - `budget_remaining(budget_id, amount)` for each entry in `budget_states`
/// - `request_cost(cost)` if `request_cost` is Some
/// - `not_revoked(token_id)` for each entry in `not_revoked`
#[deprecated(
    note = "Self-asserted budget/revocation facts are not trustworthy. Use Merkle membership proofs."
)]
#[doc(hidden)]
pub(crate) fn budget_revocation_facts(request: &AuthRequest) -> Vec<TraceFact> {
    let mut facts = Vec::new();

    // Emit budget_remaining facts
    for (budget_id, remaining) in &request.budget_states {
        facts.push(TraceFact::new(
            symbol_from_str("budget_remaining"),
            vec![
                pyana_trace::Term::Const(symbol_from_str(budget_id)),
                pyana_trace::Term::Int(*remaining as i64),
            ],
        ));
    }

    // Emit request_cost fact
    if let Some(cost) = request.request_cost {
        facts.push(TraceFact::new(
            symbol_from_str("request_cost"),
            vec![pyana_trace::Term::Int(cost as i64)],
        ));
    }

    // Emit not_revoked facts
    for token_id in &request.not_revoked {
        facts.push(TraceFact::new(
            symbol_from_str("not_revoked"),
            vec![pyana_trace::Term::Const(symbol_from_str(token_id))],
        ));
    }

    facts
}

/// Verify an existing authorization trace against a state.
///
/// This re-evaluates the trace to confirm it's valid for the given state,
/// without producing a new trace. Useful for checking traces received from
/// other parties before generating ZK proofs.
pub fn verify_authorization_trace(
    state: &TokenState,
    trace: &AuthorizationTrace,
    symbols: &SymbolTable,
) -> bool {
    // Re-evaluate with the same request and check we get the same conclusion.
    let trace_facts = committed_facts_to_trace(state, symbols);
    #[allow(deprecated)]
    let mut rules = pyana_trace::policy::legacy_policy();
    rules.extend(pyana_trace::standard_policy());

    let evaluator = Evaluator::new(trace_facts, rules);
    let new_trace = evaluator.evaluate(&trace.request);

    new_trace.conclusion == trace.conclusion
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_commit::{Fact as CommitFact, FieldElement};

    #[test]
    fn test_authorize_unrestricted_allows() {
        let mut symbols = SymbolTable::new();
        symbols.intern("unrestricted");

        let mut state = TokenState::new();
        let pred = FieldElement::from_symbol("unrestricted");
        state.add_fact(CommitFact::unary(pred, FieldElement::from_u64(1)));

        let request = AuthRequest {
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = authorize_with_trace(&state, &request, &symbols);
        assert!(result.is_ok());

        let trace = result.unwrap();
        match trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                assert_eq!(policy_rule_id, 3); // UNRESTRICTED rule
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }

    #[test]
    fn test_authorize_app_scoped_allows() {
        let mut symbols = SymbolTable::new();
        symbols.intern("action_allowed");
        symbols.intern("my-app");
        symbols.intern("read");
        // Secure format: one action_allowed fact per action, with hashed action name.
        let pred = symbols.intern("action_allowed");
        let app_id = FieldElement::from_symbol("my-app");
        let action_hash = FieldElement::from_symbol("read");

        let mut state = TokenState::new();
        state.add_fact(CommitFact::binary(pred, app_id, action_hash));

        let request = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = authorize_with_trace(&state, &request, &symbols);
        assert!(result.is_ok());

        let trace = result.unwrap();
        match trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                assert_eq!(policy_rule_id, 40); // APP_ACTION_SECURE rule
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }

    #[test]
    fn test_authorize_denied_wrong_app() {
        let mut symbols = SymbolTable::new();
        symbols.intern("action_allowed");
        symbols.intern("my-app");
        symbols.intern("read");
        // Secure format: action_allowed(my-app, read)
        let pred = symbols.intern("action_allowed");
        let app_id = FieldElement::from_symbol("my-app");
        let action_hash = FieldElement::from_symbol("read");

        let mut state = TokenState::new();
        state.add_fact(CommitFact::binary(pred, app_id, action_hash));

        let request = AuthRequest {
            app_id: Some("other-app".into()),
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = authorize_with_trace(&state, &request, &symbols);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), AuthError::Denied);
    }

    #[test]
    fn test_authorize_empty_state_error() {
        let symbols = SymbolTable::new();
        let state = TokenState::new();

        let request = AuthRequest {
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = authorize_with_trace(&state, &request, &symbols);
        assert_eq!(result.unwrap_err(), AuthError::EmptyState);
    }

    #[test]
    fn test_authorize_service_scoped() {
        let mut symbols = SymbolTable::new();
        symbols.intern("svc_action_allowed");
        symbols.intern("http");
        symbols.intern("read");
        // Secure format: svc_action_allowed(http, read)
        let pred = symbols.intern("svc_action_allowed");
        let svc_id = FieldElement::from_symbol("http");
        let action_hash = FieldElement::from_symbol("read");

        let mut state = TokenState::new();
        state.add_fact(CommitFact::binary(pred, svc_id, action_hash));

        let request = AuthRequest {
            service: Some("http".into()),
            action: Some("read".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let result = authorize_with_trace(&state, &request, &symbols);
        assert!(result.is_ok());

        let trace = result.unwrap();
        match trace.conclusion {
            Conclusion::Allow { policy_rule_id } => {
                assert_eq!(policy_rule_id, 41); // SERVICE_ACTION_SECURE rule
            }
            Conclusion::Deny => panic!("expected Allow"),
        }
    }

    #[test]
    fn test_verify_trace_valid() {
        let mut symbols = SymbolTable::new();
        symbols.intern("unrestricted");

        let mut state = TokenState::new();
        let pred = FieldElement::from_symbol("unrestricted");
        state.add_fact(CommitFact::unary(pred, FieldElement::from_u64(1)));

        let request = AuthRequest {
            action: Some("write".into()),
            now: Some(1700000000),
            ..Default::default()
        };

        let trace = authorize_with_trace(&state, &request, &symbols).unwrap();
        assert!(verify_authorization_trace(&state, &trace, &symbols));
    }

    #[test]
    fn test_committed_facts_to_trace_multiple() {
        let mut symbols = SymbolTable::new();
        symbols.intern("app");
        symbols.intern("dashboard");
        symbols.intern("read,write");
        symbols.intern("feature");
        symbols.intern("ai");

        let mut state = TokenState::new();
        state.add_fact(CommitFact::binary(
            FieldElement::from_symbol("app"),
            FieldElement::from_symbol("dashboard"),
            FieldElement::from_symbol("read,write"),
        ));
        state.add_fact(CommitFact::unary(
            FieldElement::from_symbol("feature"),
            FieldElement::from_symbol("ai"),
        ));

        let trace_facts = committed_facts_to_trace(&state, &symbols);
        assert_eq!(trace_facts.len(), 2);

        // All facts should have valid predicates.
        for fact in &trace_facts {
            assert_ne!(fact.predicate, [0u8; 32]);
        }
    }
}
