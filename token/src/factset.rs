//! Token to FactSet conversion (canonical encoding of caveats as Datalog facts).
//!
//! This module encodes token caveats into the committed fact format used by the
//! Datalog evaluator. It is the single source of truth for how a token's
//! authorization scope maps to a `FactSet` + `SymbolTable`.
//!
//! Previously this lived in the `bridge` crate, but the encoding is part of
//! the token semantics — the bridge should simply call into here.
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
//! |                  | "valid_after"       | [not_before_as_i64, _, _]       |
//! | OAuthProvider(p) | "oauth_provider"   | [hash(p), _, _]                 |
//! | OAuthScope(s)    | "oauth_scope"      | [hash(s), _, _]                 |
//! | FromMachine(m)   | "from_machine"     | [hash(m), _, _]                 |
//! | Command(c)       | "command"          | [hash(c), _, _]                 |
//! | Budget{..}       | "budget"           | [hash(id), limit, _]            |
//! | Revocable(svc)   | "revocable"        | [hash(svc), _, _]               |
//! | (no caveats)     | "unrestricted"     | [1, _, _]                       |

use pyana_commit::{Fact, FactSet, FieldElement, SymbolTable};

#[cfg(feature = "rand-deps")]
use crate::MacaroonToken;
use crate::pyana_caveats::{self, PyanaGrant};
use crate::traits::Attenuation;

/// Convert a MacaroonToken's caveats into a `FactSet` and `SymbolTable`.
///
/// The token must have been verified (HMAC chain valid) before calling this.
/// This function extracts the caveats and produces a committed fact set
/// representing the token's authorization scope.
///
/// Returns the fact set (ready for Merkle commitment) and a symbol table
/// mapping field elements back to their human-readable names.
#[cfg(feature = "rand-deps")]
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
            not_before,
            not_after,
        } => {
            let mut facts = Vec::new();
            if let Some(na) = not_after {
                let pred = symbols.intern("valid_until");
                let ts_fe = FieldElement::from_i64(*na);
                facts.push(Fact::unary(pred, ts_fe));
            }
            if let Some(nb) = not_before {
                let pred = symbols.intern("valid_after");
                let ts_fe = FieldElement::from_i64(*nb);
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

        PyanaGrant::Budget { id, limit, .. } => {
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
            // Unknown caveats are not committed -- they're opaque.
            vec![]
        }
    }
}

/// Convert an `Attenuation` specification to a list of facts.
///
/// Used when computing the FactSet for an attenuated token.
pub fn attenuation_to_facts(attenuation: &Attenuation, symbols: &mut SymbolTable) -> Vec<Fact> {
    let wire_caveats = pyana_caveats::attenuation_to_wire_caveats(attenuation);
    let mut facts = Vec::new();

    for wc in &wire_caveats {
        if let Ok(grant) = pyana_caveats::decode_grant(wc) {
            facts.extend(grant_to_facts(&grant, symbols));
        }
    }

    facts
}

/// Convert a CaveatSet directly to a FactSet and SymbolTable.
///
/// This is the core function used by the Datalog verifier: given decoded
/// caveats (after HMAC verification), produce the fact set for evaluation.
pub fn caveat_set_to_factset(
    caveat_set: &pyana_macaroon::caveat::CaveatSet,
) -> (FactSet, SymbolTable) {
    let mut factset = FactSet::new();
    let mut symbols = SymbolTable::new();

    let caveats = caveat_set.first_party_caveats();

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
            Err(_) => continue,
        };

        let facts = grant_to_facts(&grant, &mut symbols);
        for fact in facts {
            factset.insert(fact);
        }
    }

    (factset, symbols)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::AuthToken;

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

        let pred = FieldElement::from_symbol("unrestricted");
        let unrestricted_facts = factset.iter().filter(|f| f.predicate == pred).count();
        assert_eq!(unrestricted_facts, 1);
        assert_eq!(symbols.resolve(pred), Some("unrestricted"));

        let root = factset.root();
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn test_attenuated_token_to_factset() {
        let key = test_key();
        let token = MacaroonToken::mint(key, b"kid-1", "pyana.dev");

        let restricted = token
            .attenuate(&Attenuation {
                apps: vec![("my-app".into(), "rw".into())],
                services: vec![("http".into(), "r".into())],
                not_after: Some(2000000000),
                confine_user: Some("alice".into()),
                ..Default::default()
            })
            .unwrap();

        let encoded = restricted.to_encoded().unwrap();
        let mac_token = MacaroonToken::from_encoded(&encoded, key).unwrap();

        let (mut factset, symbols) = macaroon_to_factset(&mac_token);

        // Should have: app, service, valid_until, confine_user = 4 facts.
        assert_eq!(factset.len(), 4);

        let app_pred = FieldElement::from_symbol("app");
        let svc_pred = FieldElement::from_symbol("service");
        let valid_pred = FieldElement::from_symbol("valid_until");
        let user_pred = FieldElement::from_symbol("confine_user");

        assert_eq!(
            factset.iter().filter(|f| f.predicate == app_pred).count(),
            1
        );
        assert_eq!(
            factset.iter().filter(|f| f.predicate == svc_pred).count(),
            1
        );
        assert_eq!(
            factset.iter().filter(|f| f.predicate == valid_pred).count(),
            1
        );
        assert_eq!(
            factset.iter().filter(|f| f.predicate == user_pred).count(),
            1
        );

        assert_eq!(symbols.resolve(app_pred), Some("app"));
        assert_eq!(symbols.resolve(svc_pred), Some("service"));

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
        assert_eq!(facts.len(), 3);

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
        assert_eq!(
            facts[0].predicate,
            FieldElement::from_symbol("organization")
        );
        assert_eq!(facts[0].terms[0], FieldElement::from_u64(42));
    }

    #[test]
    fn test_grant_to_facts_validity_window_both() {
        let mut symbols = SymbolTable::new();
        let grant = PyanaGrant::ValidityWindow {
            not_before: Some(1000),
            not_after: Some(5000),
        };
        let facts = grant_to_facts(&grant, &mut symbols);
        // Both valid_until AND valid_after
        assert_eq!(facts.len(), 2);
        assert_eq!(facts[0].predicate, FieldElement::from_symbol("valid_until"));
        assert_eq!(facts[1].predicate, FieldElement::from_symbol("valid_after"));
    }
}
