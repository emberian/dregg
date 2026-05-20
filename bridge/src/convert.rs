//! Token to FactSet conversion.
//!
//! Converts a MacaroonToken's caveats (or BiscuitToken's facts) into a
//! [`FactSet`] suitable for Merkle commitment. Each caveat/fact is mapped to
//! one or more `Fact` entries (predicate + up to 3 terms as field elements).
//!
//! # Canonical Implementation
//!
//! The canonical fact encoding now lives in `pyana_token::factset`. This module
//! re-exports and delegates to that implementation. The encoding is part of the
//! token semantics (it defines what a token MEANS in Datalog), so it belongs
//! with the token crate.
//!
//! # Mapping Strategy
//!
//! Macaroon caveats map to facts as follows:
//!
//! | Caveat Type      | Fact Predicate       | Terms                           |
//! |-----------------|---------------------|---------------------------------|
//! | App(id, actions) | "app"              | [hash(id), hash(actions), _]    |
//! | Service(n, act)  | "service"          | [hash(n), hash(actions), _]     |
//! | Feature(name)    | "feature"          | [hash(name), _, _]              |
//! | Organization(id) | "organization"     | [id_as_u64, _, _]               |
//! | ConfineUser(uid) | "confine_user"     | [hash(uid), _, _]               |
//! | ValidityWindow   | "valid_until"      | [not_after_as_i64, _, _]        |
//! | OAuthProvider(p) | "oauth_provider"   | [hash(p), _, _]                 |
//! | OAuthScope(s)    | "oauth_scope"      | [hash(s), _, _]                 |
//! | FromMachine(m)   | "from_machine"     | [hash(m), _, _]                 |
//! | Command(c)       | "command"          | [hash(c), _, _]                 |
//! | Budget{..}       | "budget"           | [hash(id), limit, _]            |
//! | Revocable(svc)   | "revocable"        | [hash(svc), _, _]               |
//! | (no caveats)     | "unrestricted"     | [1, _, _]                       |
//!
//! An "unrestricted" fact is added when the token has no caveats at all,
//! representing a root token with unlimited access.

use pyana_commit::{Fact, FactSet, FieldElement, SymbolTable};
use pyana_token::{Attenuation, AuthToken, MacaroonToken};
use pyana_token::pyana_caveats::{self, PyanaGrant};

// Re-export the canonical implementations from token::factset.
// The bridge delegates to the token crate for fact encoding since
// Datalog is now the sole canonical evaluator and the encoding defines
// what tokens MEAN.
pub use pyana_token::factset::grant_to_facts as canonical_grant_to_facts;

/// Convert a MacaroonToken's caveats into a `FactSet` and `SymbolTable`.
///
/// The token must have been verified (HMAC chain valid) before calling this.
/// This function extracts the caveats and produces a committed fact set
/// representing the token's authorization scope.
///
/// Returns the fact set (ready for Merkle commitment) and a symbol table
/// mapping field elements back to their human-readable names.
pub fn macaroon_to_factset(token: &MacaroonToken) -> (FactSet, SymbolTable) {
    let mut factset = FactSet::new();
    let mut symbols = SymbolTable::new();

    // Decode all caveats from the macaroon's internal caveat set.
    let caveats = token.inner().caveats.first_party_caveats();

    if caveats.is_empty() {
        // No caveats means unrestricted root token.
        let pred = symbols.intern("unrestricted");
        let fact = Fact::unary(pred, FieldElement::from_u64(1));
        factset.insert(fact);
        return (factset, symbols);
    }

    for wc in &caveats {
        let grant = match pyana_caveats::decode_grant(wc) {
            Ok(g) => g,
            Err(_) => continue, // Skip malformed caveats.
        };

        let facts = grant_to_facts(&grant, &mut symbols);
        for fact in facts {
            factset.insert(fact);
        }
    }

    (factset, symbols)
}

/// Convert a single decoded grant (caveat) into one or more Facts,
/// interning all symbol names into the provided symbol table.
pub fn grant_to_facts(grant: &PyanaGrant, symbols: &mut SymbolTable) -> Vec<Fact> {
    match grant {
        PyanaGrant::App { id, actions } => {
            let pred = symbols.intern("app");
            let id_fe = symbols.intern(id);
            let actions_fe = symbols.intern(&actions.to_string());
            vec![Fact::binary(pred, id_fe, actions_fe)]
        }

        PyanaGrant::Service { name, actions } => {
            let pred = symbols.intern("service");
            let name_fe = symbols.intern(name);
            let actions_fe = symbols.intern(&actions.to_string());
            vec![Fact::binary(pred, name_fe, actions_fe)]
        }

        PyanaGrant::Feature(name) => {
            let pred = symbols.intern("feature");
            let name_fe = symbols.intern(name);
            vec![Fact::unary(pred, name_fe)]
        }

        PyanaGrant::Organization(org_id) => {
            let pred = symbols.intern("organization");
            let id_fe = FieldElement::from_u64(*org_id);
            vec![Fact::unary(pred, id_fe)]
        }

        PyanaGrant::ConfineUser(uid) => {
            let pred = symbols.intern("confine_user");
            let uid_fe = symbols.intern(uid);
            vec![Fact::unary(pred, uid_fe)]
        }

        PyanaGrant::ValidityWindow {
            not_before: _,
            not_after,
        } => {
            // We commit the expiration as a `valid_until` fact.
            // The not_before is a runtime check that doesn't need commitment
            // (it's ephemeral — once the window opens, it's always valid).
            let mut facts = Vec::new();
            if let Some(na) = not_after {
                let pred = symbols.intern("valid_until");
                let ts_fe = FieldElement::from_i64(*na);
                facts.push(Fact::unary(pred, ts_fe));
            }
            facts
        }

        PyanaGrant::OAuthProvider(provider) => {
            let pred = symbols.intern("oauth_provider");
            let prov_fe = symbols.intern(provider);
            vec![Fact::unary(pred, prov_fe)]
        }

        PyanaGrant::OAuthScope(scope) => {
            let pred = symbols.intern("oauth_scope");
            let scope_fe = symbols.intern(scope);
            vec![Fact::unary(pred, scope_fe)]
        }

        PyanaGrant::FromMachine(machine) => {
            let pred = symbols.intern("from_machine");
            let machine_fe = symbols.intern(machine);
            vec![Fact::unary(pred, machine_fe)]
        }

        PyanaGrant::Command(cmd) => {
            let pred = symbols.intern("command");
            let cmd_fe = symbols.intern(cmd);
            vec![Fact::unary(pred, cmd_fe)]
        }

        PyanaGrant::FeatureGlob { include, exclude } => {
            // Feature globs are encoded as individual include/exclude facts.
            let mut facts = Vec::new();
            for pat in include {
                let pred = symbols.intern("feature_glob_include");
                let pat_fe = symbols.intern(pat);
                facts.push(Fact::unary(pred, pat_fe));
            }
            for pat in exclude {
                let pred = symbols.intern("feature_glob_exclude");
                let pat_fe = symbols.intern(pat);
                facts.push(Fact::unary(pred, pat_fe));
            }
            facts
        }

        PyanaGrant::Budget {
            id, limit, ..
        } => {
            let pred = symbols.intern("budget");
            let id_fe = symbols.intern(id);
            let limit_fe = FieldElement::from_u64(*limit);
            vec![Fact::binary(pred, id_fe, limit_fe)]
        }

        PyanaGrant::Revocable(svc) => {
            let pred = symbols.intern("revocable");
            let svc_fe = symbols.intern(svc);
            vec![Fact::unary(pred, svc_fe)]
        }

        PyanaGrant::Unknown(_, _) => {
            // Unknown caveats are not committed — they're opaque.
            vec![]
        }
    }
}

/// Convert an `Attenuation` specification to a list of facts that would be
/// added or removed from the fact set.
///
/// Returns `(new_facts, removed_predicates)`:
/// - `new_facts`: Facts the attenuation adds (restriction checks).
/// - `removed_predicates`: Predicate names whose facts should be replaced.
pub fn attenuation_to_facts(
    attenuation: &pyana_token::Attenuation,
    symbols: &mut SymbolTable,
) -> Vec<Fact> {
    // Convert the attenuation to wire caveats, then decode each as a grant,
    // then convert grants to facts.
    let wire_caveats = pyana_caveats::attenuation_to_wire_caveats(attenuation);
    let mut facts = Vec::new();

    for wc in &wire_caveats {
        if let Ok(grant) = pyana_caveats::decode_grant(wc) {
            facts.extend(grant_to_facts(&grant, symbols));
        }
    }

    facts
}

// ============================================================================
// Secure action-set conversion (hash-based, no substring vulnerability)
// ============================================================================

/// Convert a MacaroonToken's caveats into a `FactSet` using secure hash-based
/// action membership instead of string-based Contains matching.
///
/// Instead of emitting `app(id, "rw")` facts (which rely on substring matching),
/// this function emits individual `action_allowed(app_id, action_hash)` facts
/// for each action in the action set. The policy rules then use `MemberOf`
/// (exact hash equality) instead of `Contains` (substring matching).
///
/// This eliminates the vulnerability where e.g. "threadwrite" matches "write"
/// via substring.
pub fn macaroon_to_factset_secure(token: &MacaroonToken) -> (FactSet, SymbolTable) {
    let mut factset = FactSet::new();
    let mut symbols = SymbolTable::new();

    let caveats = token.inner().caveats.first_party_caveats();

    if caveats.is_empty() {
        let pred = symbols.intern("unrestricted");
        let fact = Fact::unary(pred, FieldElement::from_u64(1));
        factset.insert(fact);
        return (factset, symbols);
    }

    for wc in &caveats {
        let grant = match pyana_caveats::decode_grant(wc) {
            Ok(g) => g,
            Err(_) => continue,
        };

        let facts = grant_to_facts_secure(&grant, &mut symbols);
        for fact in facts {
            factset.insert(fact);
        }
    }

    (factset, symbols)
}

/// Convert a grant to facts using the secure per-action-hash pattern.
///
/// For App and Service grants, instead of storing a single fact with a
/// comma-separated action string, emits one `action_allowed` or
/// `svc_action_allowed` fact per action in the set.
pub fn grant_to_facts_secure(grant: &PyanaGrant, symbols: &mut SymbolTable) -> Vec<Fact> {
    match grant {
        PyanaGrant::App { id, actions } => {
            let id_fe = symbols.intern(id);
            // Emit one action_allowed fact per action bit in the bitmask.
            let mut facts = Vec::new();
            let action_names = action_to_names(actions);
            for name in &action_names {
                let pred = symbols.intern("action_allowed");
                // Hash the action name the same way FieldElement::from_symbol does
                // (BLAKE3 hash truncated to 253 bits).
                let action_hash = FieldElement::from_symbol(name);
                facts.push(Fact::binary(pred, id_fe, action_hash));
            }
            // Also emit the app predicate for app-matching (without actions string).
            let app_pred = symbols.intern("app_registered");
            facts.push(Fact::unary(app_pred, id_fe));
            facts
        }

        PyanaGrant::Service { name, actions } => {
            let name_fe = symbols.intern(name);
            let mut facts = Vec::new();
            let action_names = action_to_names(actions);
            for action_name in &action_names {
                let pred = symbols.intern("svc_action_allowed");
                let action_hash = FieldElement::from_symbol(action_name);
                facts.push(Fact::binary(pred, name_fe, action_hash));
            }
            let svc_pred = symbols.intern("svc_registered");
            facts.push(Fact::unary(svc_pred, name_fe));
            facts
        }

        // All other grant types use the same conversion as before.
        other => grant_to_facts(other, symbols),
    }
}

/// Convert an `Action` bitmask to a list of human-readable action names.
///
/// This bridges the compact bitmask representation (used in macaroons) to
/// the named-action representation (used in the secure hash-based policy).
fn action_to_names(action: &pyana_macaroon::action::Action) -> Vec<String> {
    use pyana_macaroon::action::Action;
    let mut names = Vec::new();
    if action.contains(Action::READ) {
        names.push("read".to_string());
    }
    if action.contains(Action::WRITE) {
        names.push("write".to_string());
    }
    if action.contains(Action::CREATE) {
        names.push("create".to_string());
    }
    if action.contains(Action::DELETE) {
        names.push("delete".to_string());
    }
    if action.contains(Action::CONTROL) {
        names.push("control".to_string());
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_token::{Attenuation, MacaroonToken};

    fn test_key() -> [u8; 32] {
        let mut key = [0u8; 32];
        key[0] = 0x42;
        key[31] = 0xFF;
        key
    }

    #[test]
    fn test_unrestricted_token_to_factset() {
        let key = test_key();
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        let (mut factset, symbols) = macaroon_to_factset(&token);
        assert_eq!(factset.len(), 1);

        // Should have the unrestricted fact.
        let pred = FieldElement::from_symbol("unrestricted");
        let unrestricted_facts = factset.iter().filter(|f| f.predicate == pred).count();
        assert_eq!(unrestricted_facts, 1);

        // Symbol table should contain "unrestricted".
        assert!(symbols.resolve(pred).is_some());
        assert_eq!(symbols.resolve(pred), Some("unrestricted"));

        // Merkle root should be non-zero.
        let root = factset.root();
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn test_attenuated_token_to_factset() {
        let key = test_key();
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        // Use the inner macaroon API to attenuate and reconstruct.
        let restricted = token
            .attenuate(&Attenuation {
                apps: vec![("my-app".into(), "rw".into())],
                services: vec![("http".into(), "r".into())],
                not_after: Some(2000000000),
                confine_user: Some("alice".into()),
                ..Default::default()
            })
            .unwrap();

        // Encode and re-decode to get a concrete MacaroonToken.
        let encoded = restricted.to_encoded().unwrap();
        let mac_token = MacaroonToken::from_encoded(&encoded, key).unwrap();

        let (mut factset, symbols) = macaroon_to_factset(&mac_token);

        // Should have: app, service, valid_until, confine_user = 4 facts.
        assert_eq!(factset.len(), 4);

        // Verify specific facts exist.
        let app_pred = FieldElement::from_symbol("app");
        let svc_pred = FieldElement::from_symbol("service");
        let valid_pred = FieldElement::from_symbol("valid_until");
        let user_pred = FieldElement::from_symbol("confine_user");

        assert_eq!(factset.iter().filter(|f| f.predicate == app_pred).count(), 1);
        assert_eq!(factset.iter().filter(|f| f.predicate == svc_pred).count(), 1);
        assert_eq!(factset.iter().filter(|f| f.predicate == valid_pred).count(), 1);
        assert_eq!(factset.iter().filter(|f| f.predicate == user_pred).count(), 1);

        // Symbol table should resolve all predicates.
        assert_eq!(symbols.resolve(app_pred), Some("app"));
        assert_eq!(symbols.resolve(svc_pred), Some("service"));
        assert_eq!(symbols.resolve(valid_pred), Some("valid_until"));
        assert_eq!(symbols.resolve(user_pred), Some("confine_user"));

        // Merkle root should be deterministic.
        let root1 = factset.root();
        let root2 = factset.root();
        assert_eq!(root1, root2);
    }

    #[test]
    fn test_attenuation_to_facts() {
        let mut symbols = SymbolTable::new();
        let att = Attenuation {
            apps: vec![("app-1".into(), "r".into())],
            features: vec!["ai".into(), "gpu".into()],
            ..Default::default()
        };

        let facts = attenuation_to_facts(&att, &mut symbols);
        // 1 app + 2 features = 3 facts.
        assert_eq!(facts.len(), 3);

        // All facts should have non-zero predicates.
        for fact in &facts {
            assert!(!fact.predicate.is_zero());
        }
    }

    #[test]
    fn test_grant_to_facts_organization() {
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::Organization(42);
        let facts = grant_to_facts(&grant, &mut symbols);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].predicate, FieldElement::from_symbol("organization"));
        assert_eq!(facts[0].terms[0], FieldElement::from_u64(42));
    }

    #[test]
    fn test_grant_to_facts_budget() {
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::Budget {
            id: "agent:daily".into(),
            parent_id: None,
            class: "api_calls".into(),
            limit: 500,
            window: Some("1d".into()),
        };
        let facts = grant_to_facts(&grant, &mut symbols);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].predicate, FieldElement::from_symbol("budget"));
        assert_eq!(facts[0].terms[0], FieldElement::from_symbol("agent:daily"));
        assert_eq!(facts[0].terms[1], FieldElement::from_u64(500));
    }

    #[test]
    fn test_grant_to_facts_feature_glob() {
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::FeatureGlob {
            include: vec!["src/**".into()],
            exclude: vec!["**/*.env".into()],
        };
        let facts = grant_to_facts(&grant, &mut symbols);
        // 1 include + 1 exclude = 2 facts.
        assert_eq!(facts.len(), 2);
        assert_eq!(
            facts[0].predicate,
            FieldElement::from_symbol("feature_glob_include")
        );
        assert_eq!(
            facts[1].predicate,
            FieldElement::from_symbol("feature_glob_exclude")
        );
    }

    // ======================================================================
    // Secure (hash-based) conversion tests
    // ======================================================================

    #[test]
    fn test_secure_app_grant_emits_per_action_facts() {
        use pyana_macaroon::action::Action;
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::App {
            id: "my-app".into(),
            actions: Action::READ.union(Action::WRITE),
        };
        let facts = grant_to_facts_secure(&grant, &mut symbols);

        // Should have: 2 action_allowed facts + 1 app_registered fact = 3
        assert_eq!(facts.len(), 3);

        let action_allowed_pred = FieldElement::from_symbol("action_allowed");
        let app_registered_pred = FieldElement::from_symbol("app_registered");

        let action_facts: Vec<_> = facts.iter().filter(|f| f.predicate == action_allowed_pred).collect();
        let app_facts: Vec<_> = facts.iter().filter(|f| f.predicate == app_registered_pred).collect();

        assert_eq!(action_facts.len(), 2);
        assert_eq!(app_facts.len(), 1);

        // Both action facts should have the same app_id as first term.
        let app_id_fe = FieldElement::from_symbol("my-app");
        for fact in &action_facts {
            assert_eq!(fact.terms[0], app_id_fe);
        }

        // The action hashes should be different (read != write).
        assert_ne!(action_facts[0].terms[1], action_facts[1].terms[1]);

        // The action hashes should match FieldElement::from_symbol("read") and from_symbol("write").
        let read_hash = FieldElement::from_symbol("read");
        let write_hash = FieldElement::from_symbol("write");
        let action_hashes: Vec<_> = action_facts.iter().map(|f| f.terms[1]).collect();
        assert!(action_hashes.contains(&read_hash));
        assert!(action_hashes.contains(&write_hash));
    }

    #[test]
    fn test_secure_service_grant_emits_per_action_facts() {
        use pyana_macaroon::action::Action;
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::Service {
            name: "http".into(),
            actions: Action::READ.union(Action::WRITE).union(Action::DELETE),
        };
        let facts = grant_to_facts_secure(&grant, &mut symbols);

        // Should have: 3 svc_action_allowed facts + 1 svc_registered fact = 4
        assert_eq!(facts.len(), 4);

        let svc_action_pred = FieldElement::from_symbol("svc_action_allowed");
        let svc_registered_pred = FieldElement::from_symbol("svc_registered");

        let action_facts: Vec<_> = facts.iter().filter(|f| f.predicate == svc_action_pred).collect();
        let svc_facts: Vec<_> = facts.iter().filter(|f| f.predicate == svc_registered_pred).collect();

        assert_eq!(action_facts.len(), 3);
        assert_eq!(svc_facts.len(), 1);
    }

    #[test]
    fn test_secure_conversion_no_substring_vulnerability() {
        use pyana_macaroon::action::Action;
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::App {
            id: "my-app".into(),
            actions: Action::WRITE, // only write
        };
        let facts = grant_to_facts_secure(&grant, &mut symbols);

        let action_allowed_pred = FieldElement::from_symbol("action_allowed");
        let action_facts: Vec<_> = facts.iter().filter(|f| f.predicate == action_allowed_pred).collect();

        assert_eq!(action_facts.len(), 1);
        let write_hash = FieldElement::from_symbol("write");
        assert_eq!(action_facts[0].terms[1], write_hash);

        // "threadwrite" should NOT match — it hashes to a completely different value.
        let threadwrite_hash = FieldElement::from_symbol("threadwrite");
        assert_ne!(write_hash, threadwrite_hash);
        // The fact set does not contain a fact for "threadwrite".
        assert!(!action_facts.iter().any(|f| f.terms[1] == threadwrite_hash));
    }

    #[test]
    fn test_secure_unrestricted_token() {
        let key = test_key();
        let token = MacaroonToken::mint(key, b"kid-sec", "pyana.dev");

        let (factset, symbols) = macaroon_to_factset_secure(&token);
        assert_eq!(factset.len(), 1);

        let pred = FieldElement::from_symbol("unrestricted");
        assert!(factset.iter().any(|f| f.predicate == pred));
        assert_eq!(symbols.resolve(pred), Some("unrestricted"));
    }

    #[test]
    fn test_secure_attenuated_token() {
        let key = test_key();
        let token = MacaroonToken::mint(key, b"kid-sec", "pyana.dev");

        let restricted = token
            .attenuate(&Attenuation {
                apps: vec![("dashboard".into(), "rw".into())],
                services: vec![("http".into(), "r".into())],
                confine_user: Some("alice".into()),
                ..Default::default()
            })
            .unwrap();

        let encoded = restricted.to_encoded().unwrap();
        let mac_token = MacaroonToken::from_encoded(&encoded, key).unwrap();

        let (factset, _symbols) = macaroon_to_factset_secure(&mac_token);

        // App "rw" = 2 action_allowed facts + 1 app_registered
        // Service "r" = 1 svc_action_allowed fact + 1 svc_registered
        // confine_user = 1
        // Total = 6
        let action_allowed_pred = FieldElement::from_symbol("action_allowed");
        let svc_action_pred = FieldElement::from_symbol("svc_action_allowed");
        let user_pred = FieldElement::from_symbol("confine_user");

        let app_actions = factset.iter().filter(|f| f.predicate == action_allowed_pred).count();
        let svc_actions = factset.iter().filter(|f| f.predicate == svc_action_pred).count();
        let user_facts = factset.iter().filter(|f| f.predicate == user_pred).count();

        assert_eq!(app_actions, 2); // read + write
        assert_eq!(svc_actions, 1); // read only
        assert_eq!(user_facts, 1);
    }
}
