//! Attenuation to FoldDelta conversion.
//!
//! When a plaintext token is attenuated (caveats are added), this module produces
//! the corresponding [`FoldDelta`] that captures the state transition in a form
//! suitable for ZK proof generation.
//!
//! # Design
//!
//! Macaroon attenuation adds caveats (restrictions). In the ZK world, this means:
//! - If a new restriction replaces an unrestricted fact, the "unrestricted" fact is REMOVED.
//! - New restriction caveats become CHECK facts (rule-prefixed in the Merkle tree).
//! - The FoldDelta captures: old_root, new_root, removed facts, added checks.
//!
//! The key invariant: attenuation can only NARROW capabilities. The fold delta
//! enforces this by only allowing fact removals and check additions.

use pyana_commit::{Fact, FieldElement, FoldDelta, FoldDeltaBuilder, SymbolTable, TokenState};
use pyana_token::{Attenuation, MacaroonToken};

use crate::convert::{attenuation_to_facts, macaroon_to_factset};

/// The result of computing an attenuation delta.
#[derive(Clone, Debug)]
pub struct AttenuationDelta {
    /// The fold delta representing the state transition.
    pub fold_delta: FoldDelta,
    /// The new token state after attenuation.
    pub new_state: TokenState,
    /// The symbol table with all interned symbols.
    pub symbols: SymbolTable,
}

/// Compute the FoldDelta between a token's old state and its attenuated new state.
///
/// Given the old token, the new (attenuated) token, and the old committed state,
/// this function determines what facts were removed and what checks were added,
/// and produces a verifiable FoldDelta.
///
/// # Arguments
///
/// * `old_token` - The token before attenuation.
/// * `new_token` - The token after attenuation (with additional caveats).
/// * `old_state` - The committed state corresponding to old_token.
/// * `old_symbols` - The symbol table from the old token's conversion.
///
/// # Returns
///
/// An `AttenuationDelta` containing the fold delta, new state, and updated symbols.
/// Returns `None` if the delta cannot be computed (e.g., states are invalid).
pub fn attenuation_to_delta(
    old_token: &MacaroonToken,
    new_token: &MacaroonToken,
    old_state: &TokenState,
    old_symbols: &SymbolTable,
) -> Option<AttenuationDelta> {
    // Convert both tokens to fact sets.
    let (old_fs, _old_syms) = macaroon_to_factset(old_token);
    let (new_fs, new_syms) = macaroon_to_factset(new_token);

    // Merge symbol tables.
    let mut symbols = old_symbols.clone();
    symbols.merge(&new_syms);

    // Determine which facts were removed (in old but not in new).
    let old_facts: Vec<Fact> = old_fs.iter().copied().collect();
    let new_facts: Vec<Fact> = new_fs.iter().copied().collect();

    let removed: Vec<Fact> = old_facts
        .iter()
        .filter(|f| !new_facts.contains(f))
        .copied()
        .collect();

    // Determine which facts were added (in new but not in old).
    // These are restriction checks — they narrow access.
    let added_checks: Vec<Fact> = new_facts
        .iter()
        .filter(|f| !old_facts.contains(f))
        .copied()
        .collect();

    // Build the fold delta using the commit crate's builder.
    // We use the old_state directly since it's the canonical committed state.
    let mut builder = FoldDeltaBuilder::new(old_state.clone());

    for fact in &removed {
        builder = builder.remove_fact(*fact);
    }

    // Added checks become rule-prefixed facts in the new state.
    // We encode them as checks using a bridge-specific naming convention.
    for (i, fact) in added_checks.iter().enumerate() {
        // Create a check fact that encodes the restriction.
        let _check_name = format!("bridge_check_{}", i);
        let _terms: Vec<&str> = vec![];
        // Use the fact's predicate as the check name in the symbol table.
        let pred_name = symbols.resolve(fact.predicate).unwrap_or("unknown");
        let check_terms: Vec<String> = fact
            .terms
            .iter()
            .filter(|t| !t.is_zero())
            .enumerate()
            .map(|(j, _)| format!("term_{}", j))
            .collect();
        let term_refs: Vec<&str> = check_terms.iter().map(|s| s.as_str()).collect();
        builder = builder.add_named_check(pred_name, &term_refs);
    }

    // If nothing changed, the attenuation was a no-op (shouldn't happen with
    // valid tokens, but handle gracefully).
    if removed.is_empty() && added_checks.is_empty() {
        // Even if facts didn't change at the fact level, the attenuation may have
        // added checks that translate to rule facts. Try building anyway.
        if added_checks.is_empty() {
            return None;
        }
    }

    let fold_delta = builder.build()?;

    // Reconstruct the new state from the delta.
    let new_state = fold_delta.reconstruct_new_state(old_state)?;

    Some(AttenuationDelta {
        fold_delta,
        new_state,
        symbols,
    })
}

/// Compute a fold delta from raw state transitions.
///
/// This is a lower-level interface that works directly with `TokenState` objects
/// rather than token instances. Useful when you've already performed the conversion
/// separately.
///
/// # Arguments
///
/// * `old_state` - The committed state before attenuation.
/// * `removed` - Facts that were removed (narrowing capabilities).
/// * `added_checks` - Restriction checks that were added.
///
/// # Returns
///
/// A `FoldDelta` if the transition is valid, `None` otherwise.
pub fn compute_fold_delta(
    old_state: &TokenState,
    removed: Vec<Fact>,
    added_checks: Vec<(&str, &[&str])>,
) -> Option<FoldDelta> {
    let mut builder = FoldDeltaBuilder::new(old_state.clone());

    for fact in removed {
        builder = builder.remove_fact(fact);
    }

    for (name, terms) in added_checks {
        builder = builder.add_named_check(name, terms);
    }

    builder.build()
}

/// Compute the fold delta for the transition from an unrestricted root token
/// to a first-level attenuated token.
///
/// This is the most common case: the issuer mints a root token and immediately
/// attenuates it for a specific use case.
///
/// # Arguments
///
/// * `attenuation` - The restrictions being applied.
/// * `symbols` - Symbol table to intern names into.
///
/// # Returns
///
/// A tuple of (old_state, new_state, fold_delta) representing the transition
/// from the unrestricted root to the attenuated state.
pub fn initial_attenuation_delta(
    attenuation: &Attenuation,
    symbols: &mut SymbolTable,
) -> Option<(TokenState, TokenState, FoldDelta)> {
    // Create the unrestricted root state.
    let unrestricted_pred = symbols.intern("unrestricted");
    let unrestricted_fact = Fact::unary(unrestricted_pred, FieldElement::from_u64(1));

    let mut old_state = TokenState::new();
    old_state.add_fact(unrestricted_fact);

    // Compute the new facts from the attenuation.
    let new_facts = attenuation_to_facts(attenuation, symbols);

    if new_facts.is_empty() {
        return None;
    }

    // The old "unrestricted" fact is removed, and the new restriction facts
    // are added as checks.
    let mut builder = FoldDeltaBuilder::new(old_state.clone());
    builder = builder.remove_fact(unrestricted_fact);

    // Each new restriction becomes a named check.
    for (i, fact) in new_facts.iter().enumerate() {
        let pred_name = symbols.resolve(fact.predicate).unwrap_or("restriction");

        // SECURITY: Validate the predicate is a known restriction type.
        if !is_valid_check_predicate(pred_name) {
            return None;
        }

        let check_name = format!("{}_{}", pred_name, i);
        builder = builder.add_named_check(&check_name, &[]);
    }

    let fold_delta = builder.build()?;
    let new_state = fold_delta.reconstruct_new_state(&old_state)?;

    Some((old_state, new_state, fold_delta))
}

/// Known valid check predicates that can be added during attenuation.
///
/// Only predicates in this set are accepted as valid check prefixes.
/// This prevents an attacker from injecting arbitrary rule-prefixed facts
/// that could influence the derivation engine.
const VALID_CHECK_PREDICATES: &[&str] = &[
    "app",
    "service",
    "feature",
    "organization",
    "confine_user",
    "valid_until",
    "valid_after",
    "oauth_provider",
    "oauth_scope",
    "from_machine",
    "command",
    "feature_glob_include",
    "feature_glob_exclude",
    "budget",
    "revocable",
    "action_allowed",
    "svc_action_allowed",
    "app_registered",
    "svc_registered",
];

/// Validate that a check predicate name corresponds to a known derivation rule.
///
/// Returns `true` if the predicate is a recognized restriction type that can
/// legitimately appear as a fold check. Returns `false` for unknown predicates,
/// which would indicate either a bug or an attacker trying to inject arbitrary
/// rule-prefixed facts.
fn is_valid_check_predicate(pred_name: &str) -> bool {
    VALID_CHECK_PREDICATES.contains(&pred_name)
}

/// Compute a fold delta for subsequent attenuations (not from root).
///
/// This handles the case where an already-restricted token is further restricted.
/// The new attenuation adds additional constraints (checks) without removing
/// existing ones.
///
/// # Arguments
///
/// * `current_state` - The current committed state.
/// * `new_restrictions` - Additional facts representing new restrictions.
/// * `symbols` - Symbol table for resolving names.
///
/// # Returns
///
/// A tuple of (new_state, fold_delta) if valid. Returns `None` if any restriction
/// has an unrecognized predicate (fail-closed: unknown check types are rejected).
pub fn further_attenuation_delta(
    current_state: &TokenState,
    new_restrictions: &[Fact],
    symbols: &SymbolTable,
) -> Option<(TokenState, FoldDelta)> {
    if new_restrictions.is_empty() {
        return None;
    }

    let mut builder = FoldDeltaBuilder::new(current_state.clone());

    // Each new restriction becomes a check.
    for (_i, fact) in new_restrictions.iter().enumerate() {
        let pred_name = symbols.resolve(fact.predicate).unwrap_or("check");

        // SECURITY: Validate the predicate is a known restriction type.
        // Unknown predicates are rejected (fail-closed) because they could be
        // attacker-controlled values that influence the derivation engine in
        // unexpected ways.
        if !is_valid_check_predicate(pred_name) {
            return None;
        }

        let terms: Vec<String> = fact
            .terms
            .iter()
            .filter(|t| !t.is_zero())
            .enumerate()
            .map(|(j, _)| format!("{}_{}", pred_name, j))
            .collect();
        let term_refs: Vec<&str> = terms.iter().map(|s| s.as_str()).collect();
        builder = builder.add_named_check(pred_name, &term_refs);
    }

    let fold_delta = builder.build()?;
    let new_state = fold_delta.reconstruct_new_state(current_state)?;

    Some((new_state, fold_delta))
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_commit::verify_fold_chain;

    fn test_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[31] = 0xFF;
        key
    }

    #[test]
    fn test_initial_attenuation_delta() {
        let mut symbols = SymbolTable::new();
        let att = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };

        let result = initial_attenuation_delta(&att, &mut symbols);
        assert!(result.is_some());

        let (old_state, new_state, delta) = result.unwrap();

        // Old state should have had the unrestricted fact.
        assert_eq!(old_state.len(), 1);

        // Delta should verify.
        assert!(delta.apply_and_verify());

        // New state should have the check fact.
        assert!(new_state.len() >= 1);
    }

    #[test]
    fn test_further_attenuation_delta() {
        let mut symbols = SymbolTable::new();

        // First: create initial state with an app restriction.
        let att1 = Attenuation {
            apps: vec![("my-app".into(), "rw".into())],
            ..Default::default()
        };

        let (_, state1, delta1) = initial_attenuation_delta(&att1, &mut symbols).unwrap();

        // Second: further restrict with a user confinement.
        let user_pred = symbols.intern("confine_user");
        let user_fe = symbols.intern("alice");
        let new_restriction = Fact::unary(user_pred, user_fe);

        let result = further_attenuation_delta(&state1, &[new_restriction], &symbols);
        assert!(result.is_some());

        let (_state2, delta2) = result.unwrap();

        // Both deltas should verify.
        assert!(delta1.apply_and_verify());
        assert!(delta2.apply_and_verify());

        // Chain should verify.
        assert!(verify_fold_chain(&[delta1, delta2]));
    }

    #[test]
    fn test_compute_fold_delta_removal() {
        // Create a state with multiple facts.
        let mut state = TokenState::new();
        state.add_fact(Fact::from_symbols("owns", &["alice", "file1"]));
        state.add_fact(Fact::from_symbols("owns", &["alice", "file2"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "file1"]));
        state.add_fact(Fact::from_symbols("can_read", &["alice", "file2"]));

        // Remove access to file2.
        let removed = vec![
            Fact::from_symbols("owns", &["alice", "file2"]),
            Fact::from_symbols("can_read", &["alice", "file2"]),
        ];

        let delta = compute_fold_delta(&state, removed, vec![]);
        assert!(delta.is_some());

        let delta = delta.unwrap();
        assert!(delta.apply_and_verify());
        assert_eq!(delta.num_removed(), 2);
    }

    #[test]
    fn test_compute_fold_delta_with_checks() {
        let mut state = TokenState::new();
        state.add_fact(Fact::from_symbols("access", &["resource"]));

        let delta = compute_fold_delta(&state, vec![], vec![("expires", &["2025-12-31"])]);
        assert!(delta.is_some());

        let delta = delta.unwrap();
        assert!(delta.apply_and_verify());
        assert_eq!(delta.num_removed(), 0);
        assert_eq!(delta.num_added_checks(), 1);
    }

    #[test]
    fn test_empty_attenuation_returns_none() {
        let mut symbols = SymbolTable::new();
        let att = Attenuation::default();

        let result = initial_attenuation_delta(&att, &mut symbols);
        assert!(result.is_none());
    }
}
