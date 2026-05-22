//! Pyana-specific authorization patterns.
//!
//! Defines the standard fact names, check patterns, and policy templates used
//! across both Macaroon and Biscuit tokens in the Pyana runtime.
//!
//! # Fact Schema (Biscuit Datalog)
//!
//! Authority facts (set at token creation):
//! ```text
//! organization({org_id});
//! app({app_id}, {actions});         // e.g., app("my-app", "rwcd")
//! service({name}, {actions});       // e.g., service("http", "rw")
//! secret_access({namespace}, {actions});
//! feature({name});                  // e.g., feature("ai-engine")
//! oauth_provider({name});
//! oauth_scope({scope});
//! user({user_id});
//! machine({machine_id});
//! command({name});
//! ```
//!
//! Restriction checks (added during attenuation):
//! ```text
//! check if organization($org);
//! check if app($app, $actions), $actions.contains("r");
//! check if time($t), $t < {not_after};
//! check if time($t), $t > {not_before};
//! check if user({user_id});
//! ```
//!
//! Standard authorizer policies:
//! ```text
//! allow if app($app, $actions), request_app($app), request_action($act),
//!          $actions.contains($act);
//! deny if true;
//! ```

use crate::error::TokenError;
use crate::traits::{Attenuation, AuthRequest};

/// Sanitize a string for safe interpolation into Biscuit Datalog.
///
/// Uses an allowlist approach: only alphanumeric characters and a small set of
/// safe punctuation are permitted. Returns an error if the input contains
/// characters outside the allowlist, preventing identity confusion where two
/// distinct inputs could map to the same sanitized output.
fn sanitize_datalog_string(s: &str) -> Result<String, TokenError> {
    // Allowlist: alphanumeric plus safe punctuation that cannot break Datalog grammar.
    const SAFE_CHARS: &str = " -_./:@";
    if s.chars()
        .all(|c| c.is_alphanumeric() || SAFE_CHARS.contains(c))
    {
        Ok(s.to_string())
    } else {
        let bad_chars: Vec<char> = s
            .chars()
            .filter(|c| !c.is_alphanumeric() && !SAFE_CHARS.contains(*c))
            .collect();
        Err(TokenError::Malformed(format!(
            "datalog string contains disallowed characters {:?}: {:?}",
            bad_chars, s
        )))
    }
}

/// Standard Pyana Datalog fact names.
pub mod facts {
    pub const ORGANIZATION: &str = "organization";
    pub const APP: &str = "app";
    pub const SERVICE: &str = "service";
    pub const SECRET_ACCESS: &str = "secret_access";
    pub const FEATURE: &str = "feature";
    pub const OAUTH_PROVIDER: &str = "oauth_provider";
    pub const OAUTH_SCOPE: &str = "oauth_scope";
    pub const USER: &str = "user";
    pub const MACHINE: &str = "machine";
    pub const COMMAND: &str = "command";
}

/// Standard Pyana Datalog authorizer fact names (ambient facts from the request).
pub mod authorizer_facts {
    pub const REQUEST_ORG: &str = "request_org";
    pub const REQUEST_APP: &str = "request_app";
    pub const REQUEST_SERVICE: &str = "request_service";
    pub const REQUEST_ACTION: &str = "request_action";
    pub const REQUEST_FEATURE: &str = "request_feature";
    pub const REQUEST_USER: &str = "request_user";
    pub const REQUEST_MACHINE: &str = "request_machine";
    pub const REQUEST_COMMAND: &str = "request_command";
    pub const TIME: &str = "time";
}

/// Build Biscuit authority block Datalog code from an [`AuthRequest`]-shaped
/// set of permissions.
///
/// This generates the facts that go into the authority block when minting
/// a new Biscuit token.
///
/// Returns an error if any input string contains characters that are not safe
/// for Datalog interpolation.
pub fn authority_datalog(
    org_id: Option<u64>,
    apps: &[(String, String)],
    services: &[(String, String)],
    features: &[String],
    oauth_providers: &[String],
    oauth_scopes: &[String],
    user_id: Option<&str>,
    machine_id: Option<&str>,
    commands: &[String],
) -> Result<String, TokenError> {
    let mut code = String::new();

    if let Some(org) = org_id {
        code.push_str(&format!("{}({});\n", facts::ORGANIZATION, org));
    }
    for (app, actions) in apps {
        code.push_str(&format!(
            "{}(\"{}\", \"{}\");\n",
            facts::APP,
            sanitize_datalog_string(app)?,
            sanitize_datalog_string(actions)?
        ));
    }
    for (svc, actions) in services {
        code.push_str(&format!(
            "{}(\"{}\", \"{}\");\n",
            facts::SERVICE,
            sanitize_datalog_string(svc)?,
            sanitize_datalog_string(actions)?,
        ));
    }
    for feat in features {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::FEATURE,
            sanitize_datalog_string(feat)?
        ));
    }
    for provider in oauth_providers {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::OAUTH_PROVIDER,
            sanitize_datalog_string(provider)?
        ));
    }
    for scope in oauth_scopes {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::OAUTH_SCOPE,
            sanitize_datalog_string(scope)?
        ));
    }
    if let Some(uid) = user_id {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::USER,
            sanitize_datalog_string(uid)?
        ));
    }
    if let Some(mid) = machine_id {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::MACHINE,
            sanitize_datalog_string(mid)?
        ));
    }
    for cmd in commands {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            facts::COMMAND,
            sanitize_datalog_string(cmd)?
        ));
    }

    // Emit unrestricted(true) only when the token has zero app and zero
    // service grants — i.e., it is a true root / superuser token. This
    // allows the wildcard authorizer policy to fire for intentional root
    // tokens while preventing accidentally unscoped tokens from passing.
    if apps.is_empty() && services.is_empty() {
        code.push_str("unrestricted(true);\n");
    }

    Ok(code)
}

/// Build Biscuit restriction block Datalog code from an [`Attenuation`].
///
/// These are checks that further restrict the token's capabilities.
///
/// Returns an error if any input string contains characters that are not safe
/// for Datalog interpolation.
pub fn attenuation_datalog(att: &Attenuation) -> Result<String, TokenError> {
    let mut code = String::new();

    for (app, actions) in &att.apps {
        code.push_str(&format!(
            "check if {}(\"{}\", $actions), $actions.contains(\"{}\");\n",
            facts::APP,
            sanitize_datalog_string(app)?,
            sanitize_datalog_string(actions)?,
        ));
    }
    for (svc, actions) in &att.services {
        code.push_str(&format!(
            "check if {}(\"{}\", $actions), $actions.contains(\"{}\");\n",
            facts::SERVICE,
            sanitize_datalog_string(svc)?,
            sanitize_datalog_string(actions)?,
        ));
    }
    for feat in &att.features {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::FEATURE,
            sanitize_datalog_string(feat)?
        ));
    }
    if let Some(ts) = att.not_after {
        code.push_str(&format!(
            "check if {}($t), $t < {};\n",
            authorizer_facts::TIME,
            ts
        ));
    }
    if let Some(ts) = att.not_before {
        code.push_str(&format!(
            "check if {}($t), $t > {};\n",
            authorizer_facts::TIME,
            ts
        ));
    }
    if let Some(uid) = &att.confine_user {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::USER,
            sanitize_datalog_string(uid)?
        ));
    }
    for provider in &att.oauth_providers {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::OAUTH_PROVIDER,
            sanitize_datalog_string(provider)?,
        ));
    }
    for scope in &att.oauth_scopes {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::OAUTH_SCOPE,
            sanitize_datalog_string(scope)?,
        ));
    }
    if let Some(mid) = &att.from_machine {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::MACHINE,
            sanitize_datalog_string(mid)?
        ));
    }
    for cmd in &att.commands {
        code.push_str(&format!(
            "check if {}(\"{}\");\n",
            facts::COMMAND,
            sanitize_datalog_string(cmd)?
        ));
    }
    // Feature glob restrictions are macaroon-specific (Biscuit doesn't use glob matching).
    // Budget and Revocable are service-level concerns, not Datalog checks.
    //
    // SECURITY: raw_datalog was removed to prevent Datalog injection attacks.
    // Structured caveats cover all legitimate attenuation use cases.

    Ok(code)
}

/// Build Biscuit authorizer Datalog code from an [`AuthRequest`].
///
/// These are the ambient facts + policies added by the verifier.
///
/// Returns an error if any input string contains characters that are not safe
/// for Datalog interpolation.
pub fn authorizer_datalog(req: &AuthRequest) -> Result<String, TokenError> {
    let mut code = String::new();

    // Ambient facts from the request
    if let Some(org) = req.org_id {
        code.push_str(&format!("{}({});\n", authorizer_facts::REQUEST_ORG, org));
    }
    if let Some(app) = &req.app_id {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_APP,
            sanitize_datalog_string(app)?,
        ));
    }
    if let Some(svc) = &req.service {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_SERVICE,
            sanitize_datalog_string(svc)?,
        ));
    }
    if let Some(act) = &req.action {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_ACTION,
            sanitize_datalog_string(act)?,
        ));
    }
    for feat in &req.features {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_FEATURE,
            sanitize_datalog_string(feat)?,
        ));
    }
    if let Some(uid) = &req.user_id {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_USER,
            sanitize_datalog_string(uid)?,
        ));
    }
    if let Some(mid) = &req.machine_id {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_MACHINE,
            sanitize_datalog_string(mid)?,
        ));
    }
    if let Some(cmd) = &req.command {
        code.push_str(&format!(
            "{}(\"{}\");\n",
            authorizer_facts::REQUEST_COMMAND,
            sanitize_datalog_string(cmd)?,
        ));
    }

    // Time fact
    let now = req.now.unwrap_or_else(|| {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() as i64
    });
    code.push_str(&format!("{}({});\n", authorizer_facts::TIME, now));

    // Standard allow/deny policies
    code.push_str("\n// App-level authorization\n");
    code.push_str("allow if app($app, $actions), request_app($app), request_action($act), $actions.contains($act);\n");
    code.push_str("\n// Service-level authorization\n");
    code.push_str("allow if service($svc, $actions), request_service($svc), request_action($act), $actions.contains($act);\n");
    code.push_str("\n// Wildcard — only for explicit root tokens with unrestricted(true) fact\n");
    code.push_str("allow if unrestricted(true), request_action($act);\n");
    code.push_str("\n// Default deny\n");
    code.push_str("deny if true;\n");

    Ok(code)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_authority_datalog_generation() {
        let code = authority_datalog(
            Some(42),
            &[("my-app".into(), "rwcd".into())],
            &[("http".into(), "rw".into())],
            &["ai-engine".into()],
            &["github".into()],
            &["repo".into(), "user:email".into()],
            Some("user-123"),
            None,
            &[],
        )
        .unwrap();
        assert!(code.contains("organization(42)"));
        assert!(code.contains("app(\"my-app\", \"rwcd\")"));
        assert!(code.contains("service(\"http\", \"rw\")"));
        assert!(code.contains("feature(\"ai-engine\")"));
        assert!(code.contains("oauth_provider(\"github\")"));
        assert!(code.contains("user(\"user-123\")"));
        // Token with app+service grants must NOT get unrestricted
        assert!(!code.contains("unrestricted"));
    }

    #[test]
    fn test_authority_datalog_unrestricted_root_token() {
        // A token with no app and no service grants is a root token
        let code = authority_datalog(
            Some(1),
            &[],
            &[],
            &[],
            &[],
            &["read".into()],
            Some("alice"),
            None,
            &[],
        )
        .unwrap();
        assert!(code.contains("unrestricted(true)"));
        assert!(code.contains("user(\"alice\")"));
    }

    #[test]
    fn test_authority_datalog_app_only_no_unrestricted() {
        // A token with app grants but no service grants is NOT unrestricted
        let code = authority_datalog(
            None,
            &[("my-app".into(), "rw".into())],
            &[],
            &[],
            &[],
            &[],
            None,
            None,
            &[],
        )
        .unwrap();
        assert!(code.contains("app(\"my-app\", \"rw\")"));
        assert!(!code.contains("unrestricted"));
    }

    #[test]
    fn test_attenuation_datalog_generation() {
        let att = Attenuation {
            apps: vec![("my-app".into(), "r".into())],
            not_after: Some(1700000000),
            confine_user: Some("user-456".into()),
            ..Default::default()
        };
        let code = attenuation_datalog(&att).unwrap();
        assert!(code.contains("check if app(\"my-app\", $actions)"));
        assert!(code.contains("check if time($t), $t < 1700000000"));
        assert!(code.contains("check if user(\"user-456\")"));
    }

    #[test]
    fn test_authorizer_datalog_generation() {
        let req = AuthRequest {
            app_id: Some("my-app".into()),
            action: Some("read".into()),
            service: Some("http".into()),
            now: Some(1700000000),
            ..Default::default()
        };
        let code = authorizer_datalog(&req).unwrap();
        assert!(code.contains("request_app(\"my-app\")"));
        assert!(code.contains("request_action(\"read\")"));
        assert!(code.contains("request_service(\"http\")"));
        assert!(code.contains("time(1700000000)"));
        assert!(code.contains("allow if"));
        assert!(code.contains("deny if true"));
        // Wildcard rule must require unrestricted(true)
        assert!(code.contains("allow if unrestricted(true), request_action($act)"));
    }

    // =========================================================================
    // Security tests
    // =========================================================================

    #[test]
    fn test_sanitize_datalog_string_rejects_injection_chars() {
        // Attempt to inject Datalog via backslash escape — must return Err
        assert!(sanitize_datalog_string("app\"); allow if true; //").is_err());

        // Newline injection
        assert!(sanitize_datalog_string("app\nallow if true").is_err());

        // Null byte injection
        assert!(sanitize_datalog_string("app\x00evil").is_err());

        // Control characters
        assert!(sanitize_datalog_string("app\x01\x02\x03").is_err());

        // Valid safe strings pass through unchanged
        assert_eq!(
            sanitize_datalog_string("my-app_v2.0").unwrap(),
            "my-app_v2.0"
        );
        assert_eq!(
            sanitize_datalog_string("user@domain.com").unwrap(),
            "user@domain.com"
        );
        assert_eq!(
            sanitize_datalog_string("path/to/resource").unwrap(),
            "path/to/resource"
        );
    }

    #[test]
    fn test_sanitize_rejects_identity_confusion() {
        // Two inputs that would map to the same output under stripping
        // must both be rejected (identity confusion prevention).
        assert!(sanitize_datalog_string("my-app\"").is_err());
        assert!(sanitize_datalog_string("my-app").is_ok());
        // These are distinct inputs that must NOT silently normalize to the same string.
        assert!(sanitize_datalog_string("admin;--").is_err());
        assert!(sanitize_datalog_string("user\x00name").is_err());
    }

    #[test]
    fn test_authority_datalog_rejects_bad_input() {
        let result = authority_datalog(
            None,
            &[("my-app\"".into(), "rw".into())],
            &[],
            &[],
            &[],
            &[],
            None,
            None,
            &[],
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_raw_datalog_injection_removed() {
        // Verify that the Attenuation struct no longer has raw_datalog.
        // Attempting to inject arbitrary Datalog via attenuation is impossible
        // because the field no longer exists.
        let att = Attenuation {
            apps: vec![("my-app".into(), "r".into())],
            ..Default::default()
        };
        let code = attenuation_datalog(&att).unwrap();
        // Verify that only structured checks appear
        assert!(code.contains("check if app("));
        // No way to inject arbitrary code
        assert!(!code.contains("allow if"));
        assert!(!code.contains("deny if"));
    }
}
