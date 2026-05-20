//! Typed Pyana caveats for Macaroon tokens.
//!
//! Defines the platform caveat types (IDs 0–15) used by the Pyana runtime,
//! plus the collective verification logic that checks decoded caveats against
//! an authorization request.
//!
//! # Caveat Type Table
//!
//! | ID | Name           | Body (MsgPack)                           |
//! |----|----------------|------------------------------------------|
//! |  0 | Organization   | `u64`                                    |
//! |  1 | App            | `(String, String)` — (app_id, actions)   |
//! |  2 | Service        | `(String, String)` — (service, actions)  |
//! |  4 | Feature        | `String`                                 |
//! |  5 | ValidityWindow | `(Option<i64>, Option<i64>)` — (nb, na)  |
//! |  8 | ConfineUser    | `String`                                 |
//! |  9 | OAuthProvider  | `String`                                 |
//! | 10 | OAuthScope     | `String`                                 |
//! | 11 | FromMachine    | `String`                                 |
//! | 12 | Command        | `String`                                 |
//! | 13 | FeatureGlob    | `(Vec<String>, Vec<String>)` — (inc, exc) |
//! | 14 | Budget         | `(String, String, u64, Option<String>)`  |
//! | 15 | Revocable      | `String` — revocation service URL        |
//!
//! # Verification Model
//!
//! Individual caveats cannot be checked in isolation with AND semantics for
//! set-valued types (e.g., multiple `Feature` caveats). Instead,
//! [`verify_caveats`] groups all caveats by type and performs collective
//! checks:
//!
//! - **Set-valued** (Feature, OAuthScope, Command): all values form an allowed
//!   set; the request's values must be a subset.
//! - **Match-any** (App, Service, Organization, ConfineUser, OAuthProvider,
//!   FromMachine): if the request specifies a value, at least one caveat of
//!   that type must match.
//! - **All-must-pass** (ValidityWindow): every window caveat is checked
//!   independently against `now`.

use pyana_macaroon::action::Action;
use pyana_macaroon::caveat::{CaveatSet, CaveatType, WireCaveat};

use crate::error::TokenError;
use crate::traits::{Attenuation, AuthRequest, Capability};

// ============================================================================
// Caveat type IDs
// ============================================================================

/// Organization restriction (body: u64 org ID).
pub const CAV_ORGANIZATION: CaveatType = 0;
/// App restriction (body: (app_id, actions) tuple).
pub const CAV_APP: CaveatType = 1;
/// Service restriction (body: (service, actions) tuple).
pub const CAV_SERVICE: CaveatType = 2;
// 3 = Secret — reserved, not yet used in Attenuation
/// Feature restriction (body: feature name string).
pub const CAV_FEATURE: CaveatType = 4;
/// Validity window restriction (body: (not_before, not_after) tuple).
pub const CAV_VALIDITY_WINDOW: CaveatType = 5;
// 6 = IfPresent — reserved
// 7 = reserved
/// Confine to a specific user (body: user_id string).
pub const CAV_CONFINE_USER: CaveatType = 8;
/// OAuth provider restriction (body: provider name string).
pub const CAV_OAUTH_PROVIDER: CaveatType = 9;
/// OAuth scope restriction (body: scope string).
pub const CAV_OAUTH_SCOPE: CaveatType = 10;
/// Machine binding (body: machine_id string).
pub const CAV_FROM_MACHINE: CaveatType = 11;
/// Command restriction (body: command name string).
pub const CAV_COMMAND: CaveatType = 12;
/// Feature glob pattern (body: (Vec<String>, Vec<String>) — (include, exclude)).
pub const CAV_FEATURE_GLOB: CaveatType = 13;
/// Budget enrollment (body: (String, String, u64, Option<String>) — (id, class, limit, window)).
pub const CAV_BUDGET: CaveatType = 14;
/// Revocable marker (body: String — revocation service URL).
pub const CAV_REVOCABLE: CaveatType = 15;

// ============================================================================
// Decoded grant enum
// ============================================================================

/// A decoded Pyana caveat representing a single access grant/restriction.
#[derive(Debug, Clone)]
pub enum PyanaGrant {
  Organization(u64),
  App {
    id: String,
    actions: Action,
  },
  Service {
    name: String,
    actions: Action,
  },
  Feature(String),
  ValidityWindow {
    not_before: Option<i64>,
    not_after: Option<i64>,
  },
  ConfineUser(String),
  OAuthProvider(String),
  OAuthScope(String),
  FromMachine(String),
  Command(String),
  /// Feature glob pattern with include/exclude lists.
  FeatureGlob {
    include: Vec<String>,
    exclude: Vec<String>,
  },
  /// Budget enrollment (locally enforced when budget state is provided).
  Budget {
    id: String,
    parent_id: Option<String>,
    class: String,
    limit: u64,
    window: Option<String>,
  },
  /// Revocable marker (locally enforced when revocation state is provided).
  Revocable(String),
  /// Unrecognized caveat type — preserved but not enforced.
  Unknown(CaveatType, Vec<u8>),
}

// ============================================================================
// Encoding helpers (MsgPack via rmp-serde)
// ============================================================================

pub(crate) fn encode_name_actions(name: &str, actions: &str) -> Vec<u8> {
  rmp_serde::to_vec(&(name, actions)).expect("msgpack encode of fixed-schema tuple cannot fail")
}

fn decode_name_actions(body: &[u8]) -> Result<(String, String), TokenError> {
  rmp_serde::from_slice::<(String, String)>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

pub(crate) fn encode_string(s: &str) -> Vec<u8> {
  rmp_serde::to_vec(s).expect("msgpack encode should not fail")
}

fn decode_string(body: &[u8]) -> Result<String, TokenError> {
  rmp_serde::from_slice::<String>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

pub fn encode_u64(v: u64) -> Vec<u8> {
  rmp_serde::to_vec(&v).expect("msgpack encode should not fail")
}

fn decode_u64(body: &[u8]) -> Result<u64, TokenError> {
  rmp_serde::from_slice::<u64>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

pub(crate) fn encode_validity_window(not_before: Option<i64>, not_after: Option<i64>) -> Vec<u8> {
  rmp_serde::to_vec(&(not_before, not_after)).expect("msgpack encode should not fail")
}

fn decode_validity_window(body: &[u8]) -> Result<(Option<i64>, Option<i64>), TokenError> {
  rmp_serde::from_slice::<(Option<i64>, Option<i64>)>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

pub(crate) fn encode_feature_glob(include: &[String], exclude: &[String]) -> Vec<u8> {
  rmp_serde::to_vec(&(include, exclude)).expect("msgpack encode should not fail")
}

fn decode_feature_glob(body: &[u8]) -> Result<(Vec<String>, Vec<String>), TokenError> {
  rmp_serde::from_slice::<(Vec<String>, Vec<String>)>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

fn encode_budget(id: &str, parent_id: Option<&str>, class: &str, limit: u64, window: Option<&str>) -> Vec<u8> {
  rmp_serde::to_vec(&(id, parent_id, class, limit, window)).expect("msgpack encode should not fail")
}

fn decode_budget(body: &[u8]) -> Result<(String, Option<String>, String, u64, Option<String>), TokenError> {
  rmp_serde::from_slice::<(String, Option<String>, String, u64, Option<String>)>(body)
    .map_err(|e| TokenError::Malformed(format!("caveat body decode: {e}")))
}

// ============================================================================
// Decode WireCaveat → PyanaGrant
// ============================================================================

/// Decode a [`WireCaveat`] into a typed [`PyanaGrant`].
pub fn decode_grant(wc: &WireCaveat) -> Result<PyanaGrant, TokenError> {
  match wc.caveat_type {
    CAV_ORGANIZATION => {
      let org_id = decode_u64(&wc.body)?;
      Ok(PyanaGrant::Organization(org_id))
    }
    CAV_APP => {
      let (id, actions_str) = decode_name_actions(&wc.body)?;
      Ok(PyanaGrant::App {
        id,
        actions: Action::parse(&actions_str),
      })
    }
    CAV_SERVICE => {
      let (name, actions_str) = decode_name_actions(&wc.body)?;
      Ok(PyanaGrant::Service {
        name,
        actions: Action::parse(&actions_str),
      })
    }
    CAV_FEATURE => {
      let name = decode_string(&wc.body)?;
      Ok(PyanaGrant::Feature(name))
    }
    CAV_VALIDITY_WINDOW => {
      let (not_before, not_after) = decode_validity_window(&wc.body)?;
      Ok(PyanaGrant::ValidityWindow {
        not_before,
        not_after,
      })
    }
    CAV_CONFINE_USER => {
      let uid = decode_string(&wc.body)?;
      Ok(PyanaGrant::ConfineUser(uid))
    }
    CAV_OAUTH_PROVIDER => {
      let provider = decode_string(&wc.body)?;
      Ok(PyanaGrant::OAuthProvider(provider))
    }
    CAV_OAUTH_SCOPE => {
      let scope = decode_string(&wc.body)?;
      Ok(PyanaGrant::OAuthScope(scope))
    }
    CAV_FROM_MACHINE => {
      let mid = decode_string(&wc.body)?;
      Ok(PyanaGrant::FromMachine(mid))
    }
    CAV_COMMAND => {
      let cmd = decode_string(&wc.body)?;
      Ok(PyanaGrant::Command(cmd))
    }
    CAV_FEATURE_GLOB => {
      let (include, exclude) = decode_feature_glob(&wc.body)?;
      Ok(PyanaGrant::FeatureGlob { include, exclude })
    }
    CAV_BUDGET => {
      let (id, parent_id, class, limit, window) = decode_budget(&wc.body)?;
      Ok(PyanaGrant::Budget {
        id,
        parent_id,
        class,
        limit,
        window,
      })
    }
    CAV_REVOCABLE => {
      let service = decode_string(&wc.body)?;
      Ok(PyanaGrant::Revocable(service))
    }
    other => Ok(PyanaGrant::Unknown(other, wc.body.clone())),
  }
}

// ============================================================================
// Build WireCaveats from Attenuation
// ============================================================================

/// Convert an [`Attenuation`] into typed [`WireCaveat`]s.
///
/// Each restriction field produces one or more caveats. Empty/None fields
/// are skipped.
pub fn attenuation_to_wire_caveats(att: &Attenuation) -> Vec<WireCaveat> {
  let mut caveats = Vec::new();

  for (app_id, actions) in &att.apps {
    caveats.push(WireCaveat::new(
      CAV_APP,
      encode_name_actions(app_id, actions),
    ));
  }
  for (svc, actions) in &att.services {
    caveats.push(WireCaveat::new(
      CAV_SERVICE,
      encode_name_actions(svc, actions),
    ));
  }
  for feat in &att.features {
    caveats.push(WireCaveat::new(CAV_FEATURE, encode_string(feat)));
  }
  if att.not_after.is_some() || att.not_before.is_some() {
    caveats.push(WireCaveat::new(
      CAV_VALIDITY_WINDOW,
      encode_validity_window(att.not_before, att.not_after),
    ));
  }
  if let Some(uid) = &att.confine_user {
    caveats.push(WireCaveat::new(CAV_CONFINE_USER, encode_string(uid)));
  }
  for provider in &att.oauth_providers {
    caveats.push(WireCaveat::new(CAV_OAUTH_PROVIDER, encode_string(provider)));
  }
  for scope in &att.oauth_scopes {
    caveats.push(WireCaveat::new(CAV_OAUTH_SCOPE, encode_string(scope)));
  }
  if let Some(mid) = &att.from_machine {
    caveats.push(WireCaveat::new(CAV_FROM_MACHINE, encode_string(mid)));
  }
  for cmd in &att.commands {
    caveats.push(WireCaveat::new(CAV_COMMAND, encode_string(cmd)));
  }
  if let Some(fg) = &att.feature_globs {
    if !fg.include.is_empty() || !fg.exclude.is_empty() {
      caveats.push(WireCaveat::new(
        CAV_FEATURE_GLOB,
        encode_feature_glob(&fg.include, &fg.exclude),
      ));
    }
  }
  if let Some(budget) = &att.budget {
    caveats.push(WireCaveat::new(
      CAV_BUDGET,
      encode_budget(&budget.id, budget.parent_id.as_deref(), &budget.class, budget.limit, budget.window.as_deref()),
    ));
  }
  if let Some(svc) = &att.revocable {
    caveats.push(WireCaveat::new(CAV_REVOCABLE, encode_string(svc)));
  }

  caveats
}

// ============================================================================
// Collective caveat verification
// ============================================================================

/// Verify decoded caveats against an authorization request.
///
/// After the macaroon HMAC chain has been validated (proving authenticity),
/// this function checks whether the *authorization* embodied in the caveats
/// actually permits the requested access.
///
/// Result of caveat verification, containing both capabilities and metadata.
#[derive(Debug)]
pub struct CaveatVerifyResult {
  /// Effective capabilities after verification.
  pub capabilities: Vec<Capability>,
  /// Tightest expiration timestamp from ValidityWindow caveats (if any).
  pub expires_at: Option<i64>,
  /// Subject user ID from ConfineUser caveats (if any).
  pub subject: Option<String>,
}

/// Returns the effective capabilities and token metadata on success.
///
/// # Deprecation
///
/// This function uses imperative string-matching logic that is NOT the canonical
/// semantics. Use [`crate::datalog_verify::verify_token_datalog_full`] instead,
/// which evaluates via Datalog (the ground truth for both trusted and trustless modes).
#[deprecated(
  since = "0.1.0",
  note = "Use datalog_verify::verify_token_datalog_full for canonical Datalog semantics"
)]
pub fn verify_caveats(
  caveat_set: &CaveatSet,
  request: &AuthRequest,
) -> Result<CaveatVerifyResult, TokenError> {
  // Decode all first-party caveats into typed grants
  let mut orgs: Vec<u64> = Vec::new();
  let mut apps: Vec<(String, Action)> = Vec::new();
  let mut services: Vec<(String, Action)> = Vec::new();
  let mut features: Vec<String> = Vec::new();
  let mut validity_windows: Vec<(Option<i64>, Option<i64>)> = Vec::new();
  let mut confined_users: Vec<String> = Vec::new();
  let mut oauth_providers: Vec<String> = Vec::new();
  let mut oauth_scopes: Vec<String> = Vec::new();
  let mut machines: Vec<String> = Vec::new();
  let mut commands: Vec<String> = Vec::new();
  let mut feature_globs: Vec<(Vec<String>, Vec<String>)> = Vec::new();
  let mut budgets: Vec<(String, u64)> = Vec::new(); // (budget_id, limit)
  let mut revocable_ids: Vec<String> = Vec::new();

  for wc in caveat_set.first_party_caveats() {
    match decode_grant(wc)? {
      PyanaGrant::Organization(id) => orgs.push(id),
      PyanaGrant::App { id, actions } => apps.push((id, actions)),
      PyanaGrant::Service { name, actions } => services.push((name, actions)),
      PyanaGrant::Feature(name) => features.push(name),
      PyanaGrant::ValidityWindow {
        not_before,
        not_after,
      } => {
        validity_windows.push((not_before, not_after));
      }
      PyanaGrant::ConfineUser(uid) => confined_users.push(uid),
      PyanaGrant::OAuthProvider(p) => oauth_providers.push(p),
      PyanaGrant::OAuthScope(s) => oauth_scopes.push(s),
      PyanaGrant::FromMachine(mid) => machines.push(mid),
      PyanaGrant::Command(cmd) => commands.push(cmd),
      PyanaGrant::FeatureGlob { include, exclude } => feature_globs.push((include, exclude)),
      PyanaGrant::Budget { id, limit, .. } => budgets.push((id, limit)),
      PyanaGrant::Revocable(token_id) => revocable_ids.push(token_id),
      PyanaGrant::Unknown(_, _) => {}
    }
  }

  let now = request.now.unwrap_or_else(|| {
    std::time::SystemTime::now()
      .duration_since(std::time::UNIX_EPOCH)
      .unwrap_or_default()
      .as_secs() as i64
  });

  // --- Time checks (ALL windows must be satisfied) ---
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

  // --- Organization: match-any ---
  if let Some(req_org) = request.org_id {
    if !orgs.is_empty() && !orgs.contains(&req_org) {
      return Err(TokenError::Denied(format!(
        "token restricted to org(s) {:?}, requested org {}",
        orgs, req_org
      )));
    }
  }

  // Parse the requested action once
  let req_action = request.action.as_deref().map(Action::parse);

  // --- App: match-any with action containment ---
  if let Some(req_app) = &request.app_id {
    if !apps.is_empty() {
      let matched = apps.iter().find(|(id, _)| id == req_app);
      match matched {
        Some((_, allowed)) => {
          if let Some(ra) = &req_action {
            if !allowed.contains(*ra) {
              return Err(TokenError::Denied(format!(
                "app '{}' grants {}, request needs {}",
                req_app, allowed, ra
              )));
            }
          }
        }
        None => {
          return Err(TokenError::Denied(format!(
            "token not valid for app '{}'",
            req_app
          )));
        }
      }
    }
  }

  // --- Service: match-any with action containment ---
  if let Some(req_svc) = &request.service {
    if !services.is_empty() {
      let matched = services.iter().find(|(name, _)| name == req_svc);
      match matched {
        Some((_, allowed)) => {
          if let Some(ra) = &req_action {
            if !allowed.contains(*ra) {
              return Err(TokenError::Denied(format!(
                "service '{}' grants {}, request needs {}",
                req_svc, allowed, ra
              )));
            }
          }
        }
        None => {
          return Err(TokenError::Denied(format!(
            "token not valid for service '{}'",
            req_svc
          )));
        }
      }
    }
  }

  // --- Features: set containment ---
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

  // --- User: match-any ---
  if let Some(req_user) = &request.user_id {
    if !confined_users.is_empty() && !confined_users.contains(req_user) {
      return Err(TokenError::Denied(format!(
        "token confined to user(s) {:?}, request is for '{}'",
        confined_users, req_user
      )));
    }
  }

  // --- OAuth provider: match-any ---
  if let Some(req_provider) = &request.oauth_provider {
    if !oauth_providers.is_empty() && !oauth_providers.contains(req_provider) {
      return Err(TokenError::Denied(format!(
        "token not valid for OAuth provider '{}'",
        req_provider
      )));
    }
  }

  // --- OAuth scopes: set containment ---
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

  // --- Machine: match-any ---
  if let Some(req_machine) = &request.machine_id {
    if !machines.is_empty() && !machines.contains(req_machine) {
      return Err(TokenError::Denied(format!(
        "token not valid for machine '{}'",
        req_machine
      )));
    }
  }

  // --- Command: match-any ---
  if let Some(req_cmd) = &request.command {
    if !commands.is_empty() && !commands.contains(req_cmd) {
      return Err(TokenError::Denied(format!(
        "token not valid for command '{}'",
        req_cmd
      )));
    }
  }

  // --- Feature globs: all glob caveats must permit all requested features ---
  if !request.features.is_empty() && !feature_globs.is_empty() {
    for req_feat in &request.features {
      for (include, exclude) in &feature_globs {
        // Check excludes first — any match denies
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
        // If includes are specified, at least one must match
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

  // --- Budget enforcement: locally verified, not passthrough ---
  if !budgets.is_empty() {
    if request.budget_states.is_empty() {
      return Err(TokenError::Denied(
        "budget state required for verification: token has budget caveats but no budget state was provided".into(),
      ));
    }
    let request_cost = request.request_cost.unwrap_or(1);
    for (budget_id, _limit) in &budgets {
      match request.budget_states.get(budget_id) {
        Some(&remaining) => {
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

  // --- Revocation enforcement: locally verified, not passthrough ---
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

  // --- Build capabilities from the grants ---
  let mut capabilities = Vec::new();
  for (id, actions) in &apps {
    capabilities.push(Capability {
      resource_type: "app".into(),
      resource_id: id.clone(),
      actions: actions.to_string(),
    });
  }
  for (name, actions) in &services {
    capabilities.push(Capability {
      resource_type: "service".into(),
      resource_id: name.clone(),
      actions: actions.to_string(),
    });
  }
  for feat in &features {
    capabilities.push(Capability {
      resource_type: "feature".into(),
      resource_id: feat.clone(),
      actions: "*".into(),
    });
  }
  for provider in &oauth_providers {
    capabilities.push(Capability {
      resource_type: "oauth_provider".into(),
      resource_id: provider.clone(),
      actions: "*".into(),
    });
  }
  for scope in &oauth_scopes {
    capabilities.push(Capability {
      resource_type: "oauth_scope".into(),
      resource_id: scope.clone(),
      actions: "*".into(),
    });
  }

  // --- Extract metadata ---
  // Tightest expiration: minimum not_after across all validity windows.
  let expires_at = validity_windows
    .iter()
    .filter_map(|(_, na)| *na)
    .min();

  // Subject: first confined user (typically only one).
  let subject = confined_users.into_iter().next();

  Ok(CaveatVerifyResult {
    capabilities,
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

  #[test]
  fn test_encode_decode_organization() {
    let wc = WireCaveat::new(CAV_ORGANIZATION, encode_u64(42));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Organization(id) => assert_eq!(id, 42),
      _ => panic!("expected Organization grant"),
    }
  }

  #[test]
  fn test_encode_decode_app() {
    let wc = WireCaveat::new(CAV_APP, encode_name_actions("my-app", "rw"));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::App { id, actions } => {
        assert_eq!(id, "my-app");
        assert!(actions.contains(Action::READ));
        assert!(actions.contains(Action::WRITE));
        assert!(!actions.contains(Action::DELETE));
      }
      _ => panic!("expected App grant"),
    }
  }

  #[test]
  fn test_encode_decode_service() {
    let wc = WireCaveat::new(CAV_SERVICE, encode_name_actions("http", "rwcd"));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Service { name, actions } => {
        assert_eq!(name, "http");
        assert_eq!(actions, Action::parse("rwcd"));
      }
      _ => panic!("expected Service grant"),
    }
  }

  #[test]
  fn test_encode_decode_feature() {
    let wc = WireCaveat::new(CAV_FEATURE, encode_string("ai-engine"));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Feature(name) => assert_eq!(name, "ai-engine"),
      _ => panic!("expected Feature grant"),
    }
  }

  #[test]
  fn test_encode_decode_validity_window() {
    let wc = WireCaveat::new(
      CAV_VALIDITY_WINDOW,
      encode_validity_window(Some(1000), Some(2000)),
    );
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::ValidityWindow {
        not_before,
        not_after,
      } => {
        assert_eq!(not_before, Some(1000));
        assert_eq!(not_after, Some(2000));
      }
      _ => panic!("expected ValidityWindow grant"),
    }
  }

  #[test]
  fn test_encode_decode_confine_user() {
    let wc = WireCaveat::new(CAV_CONFINE_USER, encode_string("alice"));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::ConfineUser(uid) => assert_eq!(uid, "alice"),
      _ => panic!("expected ConfineUser grant"),
    }
  }

  #[test]
  fn test_encode_decode_unknown_type() {
    let wc = WireCaveat::new(99, vec![0x42]);
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Unknown(typ, body) => {
        assert_eq!(typ, 99);
        assert_eq!(body, vec![0x42]);
      }
      _ => panic!("expected Unknown grant"),
    }
  }

  // --- attenuation_to_wire_caveats ---

  #[test]
  fn test_attenuation_to_wire_caveats_full() {
    let att = Attenuation {
      apps: vec![("app1".into(), "rw".into())],
      services: vec![("http".into(), "r".into())],
      features: vec!["ai".into()],
      not_after: Some(2000000000),
      not_before: None,
      confine_user: Some("user-1".into()),
      oauth_providers: vec!["github".into()],
      oauth_scopes: vec!["repo".into()],
      from_machine: Some("host-1".into()),
      commands: vec!["deploy".into()],
      ..Default::default()
    };
    let caveats = attenuation_to_wire_caveats(&att);
    assert_eq!(caveats.len(), 9);
    assert_eq!(caveats[0].caveat_type, CAV_APP);
    assert_eq!(caveats[1].caveat_type, CAV_SERVICE);
    assert_eq!(caveats[2].caveat_type, CAV_FEATURE);
    assert_eq!(caveats[3].caveat_type, CAV_VALIDITY_WINDOW);
    assert_eq!(caveats[4].caveat_type, CAV_CONFINE_USER);
    assert_eq!(caveats[5].caveat_type, CAV_OAUTH_PROVIDER);
    assert_eq!(caveats[6].caveat_type, CAV_OAUTH_SCOPE);
    assert_eq!(caveats[7].caveat_type, CAV_FROM_MACHINE);
    assert_eq!(caveats[8].caveat_type, CAV_COMMAND);
  }

  #[test]
  fn test_attenuation_to_wire_caveats_empty() {
    let att = Attenuation::default();
    let caveats = attenuation_to_wire_caveats(&att);
    assert!(caveats.is_empty());
  }

  // --- verify_caveats ---

  #[test]
  fn test_verify_app_match() {
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
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert_eq!(caps.len(), 1);
    assert_eq!(caps[0].resource_type, "app");
    assert_eq!(caps[0].resource_id, "my-app");
    assert_eq!(caps[0].actions, "rw");
  }

  #[test]
  fn test_verify_app_wrong_app() {
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
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_app_insufficient_actions() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_APP, encode_name_actions("my-app", "r")));

    let request = AuthRequest {
      app_id: Some("my-app".into()),
      action: Some("w".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_service_match() {
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
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert_eq!(caps.len(), 1);
    assert_eq!(caps[0].resource_type, "service");
  }

  #[test]
  fn test_verify_expired() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_VALIDITY_WINDOW,
      encode_validity_window(None, Some(1000)),
    ));

    let request = AuthRequest {
      now: Some(2000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_not_yet_valid() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_VALIDITY_WINDOW,
      encode_validity_window(Some(5000), None),
    ));

    let request = AuthRequest {
      now: Some(2000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_validity_window_ok() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_VALIDITY_WINDOW,
      encode_validity_window(Some(1000), Some(5000)),
    ));

    let request = AuthRequest {
      now: Some(3000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_verify_multiple_apps() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_APP, encode_name_actions("app-a", "rw")));
    set.push(WireCaveat::new(CAV_APP, encode_name_actions("app-b", "r")));

    let request = AuthRequest {
      app_id: Some("app-b".into()),
      action: Some("r".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert_eq!(caps.len(), 2); // both apps reported
  }

  #[test]
  fn test_verify_confine_user_match() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

    let request = AuthRequest {
      user_id: Some("alice".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_verify_confine_user_wrong() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_CONFINE_USER, encode_string("alice")));

    let request = AuthRequest {
      user_id: Some("bob".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_no_restrictions_is_superuser() {
    let set = CaveatSet::new();
    let request = AuthRequest {
      app_id: Some("any-app".into()),
      action: Some("rwcd".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert!(caps.is_empty()); // unrestricted, nothing to report
  }

  #[test]
  fn test_verify_unrestricted_dimension_allowed() {
    // Token restricted to an app, but request asks for a service (no
    // service caveats) — should be allowed since the service dimension
    // is unrestricted.
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
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_verify_features_subset() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_FEATURE, encode_string("ai")));
    set.push(WireCaveat::new(CAV_FEATURE, encode_string("gpu")));

    // Request for a granted feature
    let request = AuthRequest {
      features: vec!["ai".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());

    // Request for an ungranted feature
    let request2 = AuthRequest {
      features: vec!["quantum".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());
  }

  #[test]
  fn test_verify_combined_restrictions() {
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
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert_eq!(caps.len(), 1); // 1 app

    // Wrong user
    let request2 = AuthRequest {
      app_id: Some("my-app".into()),
      action: Some("r".into()),
      user_id: Some("bob".into()),
      now: Some(3000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());

    // Expired
    let request3 = AuthRequest {
      app_id: Some("my-app".into()),
      action: Some("r".into()),
      user_id: Some("alice".into()),
      now: Some(6000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request3).is_err());
  }

  #[test]
  fn test_verify_oauth_provider() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_OAUTH_PROVIDER, encode_string("github")));

    let request = AuthRequest {
      oauth_provider: Some("github".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());

    let request2 = AuthRequest {
      oauth_provider: Some("google".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());
  }

  #[test]
  fn test_verify_command() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(CAV_COMMAND, encode_string("deploy")));
    set.push(WireCaveat::new(CAV_COMMAND, encode_string("status")));

    let request = AuthRequest {
      command: Some("deploy".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());

    let request2 = AuthRequest {
      command: Some("rollback".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());
  }

  #[test]
  fn test_roundtrip_attenuation_verify() {
    let att = Attenuation {
      apps: vec![("my-app".into(), "rw".into())],
      services: vec![("http".into(), "r".into())],
      not_after: Some(2000000000),
      confine_user: Some("alice".into()),
      ..Default::default()
    };

    let wire_caveats = attenuation_to_wire_caveats(&att);
    let mut set = CaveatSet::new();
    for wc in wire_caveats {
      set.push(wc);
    }

    let request = AuthRequest {
      app_id: Some("my-app".into()),
      service: Some("http".into()),
      action: Some("r".into()),
      user_id: Some("alice".into()),
      now: Some(1700000000),
      ..Default::default()
    };
    let result = verify_caveats(&set, &request).unwrap();
    let caps = &result.capabilities;
    assert_eq!(caps.len(), 2); // 1 app + 1 service
  }

  // --- FeatureGlob tests ---

  #[test]
  fn test_encode_decode_feature_glob() {
    let wc = WireCaveat::new(
      CAV_FEATURE_GLOB,
      encode_feature_glob(
        &["src/components/**".into(), "tests/**".into()],
        &["**/*.env".into()],
      ),
    );
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::FeatureGlob { include, exclude } => {
        assert_eq!(include, vec!["src/components/**", "tests/**"]);
        assert_eq!(exclude, vec!["**/*.env"]);
      }
      _ => panic!("expected FeatureGlob grant"),
    }
  }

  #[test]
  fn test_verify_feature_glob_include_match() {
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
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_verify_feature_glob_include_no_match() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_FEATURE_GLOB,
      encode_feature_glob(&["src/components/**".into()], &[]),
    ));

    let request = AuthRequest {
      features: vec!["src/config/settings.ts".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_err());
  }

  #[test]
  fn test_verify_feature_glob_exclude() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_FEATURE_GLOB,
      encode_feature_glob(
        &["src/**".into()],
        &["src/components/secrets.ts".into()],
      ),
    ));

    // Allowed file
    let request = AuthRequest {
      features: vec!["src/components/nav.tsx".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());

    // Excluded file
    let request2 = AuthRequest {
      features: vec!["src/components/secrets.ts".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());
  }

  #[test]
  fn test_verify_feature_glob_exclude_env() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_FEATURE_GLOB,
      encode_feature_glob(&["**".into()], &["**/*.env".into()]),
    ));

    let request = AuthRequest {
      features: vec!["src/main.rs".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());

    let request2 = AuthRequest {
      features: vec![".env".into()],
      now: Some(1700000000),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request2).is_err());
  }

  // --- Budget tests ---

  #[test]
  fn test_encode_decode_budget() {
    let wc = WireCaveat::new(
      CAV_BUDGET,
      encode_budget("ci-bot-7:daily", None, "api_calls", 200, Some("1d")),
    );
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Budget {
        id,
        parent_id,
        class,
        limit,
        window,
      } => {
        assert_eq!(id, "ci-bot-7:daily");
        assert_eq!(parent_id, None);
        assert_eq!(class, "api_calls");
        assert_eq!(limit, 200);
        assert_eq!(window, Some("1d".into()));
      }
      _ => panic!("expected Budget grant"),
    }
  }

  #[test]
  fn test_budget_enforcement_allows_when_sufficient() {
    // Budget caveat with sufficient remaining budget should ALLOW.
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_BUDGET,
      encode_budget("agent:daily", None, "api_calls", 500, Some("1d")),
    ));
    set.push(WireCaveat::new(
      CAV_APP,
      encode_name_actions("my-app", "rw"),
    ));

    let mut budget_states = std::collections::HashMap::new();
    budget_states.insert("agent:daily".into(), 50u64);

    let request = AuthRequest {
      app_id: Some("my-app".into()),
      action: Some("r".into()),
      now: Some(1700000000),
      budget_states,
      request_cost: Some(10),
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_budget_enforcement_denies_when_exhausted() {
    // Budget caveat with insufficient remaining budget should DENY.
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_BUDGET,
      encode_budget("agent:daily", None, "api_calls", 100, Some("1d")),
    ));

    let mut budget_states = std::collections::HashMap::new();
    budget_states.insert("agent:daily".into(), 5u64);

    let request = AuthRequest {
      now: Some(1700000000),
      budget_states,
      request_cost: Some(10),
      ..Default::default()
    };
    let err = verify_caveats(&set, &request).unwrap_err();
    assert!(format!("{err}").contains("exhausted"));
  }

  #[test]
  fn test_budget_enforcement_requires_state() {
    // Budget caveat without budget_states should ERROR.
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_BUDGET,
      encode_budget("agent:daily", None, "api_calls", 500, Some("1d")),
    ));

    let request = AuthRequest {
      now: Some(1700000000),
      ..Default::default()
    };
    let err = verify_caveats(&set, &request).unwrap_err();
    assert!(format!("{err}").contains("budget state required"));
  }

  // --- Revocable tests ---

  #[test]
  fn test_encode_decode_revocable() {
    let wc = WireCaveat::new(CAV_REVOCABLE, encode_string("revoke.pyana.dev"));
    let grant = decode_grant(&wc).unwrap();
    match grant {
      PyanaGrant::Revocable(svc) => assert_eq!(svc, "revoke.pyana.dev"),
      _ => panic!("expected Revocable grant"),
    }
  }

  #[test]
  fn test_revocable_enforcement_allows_when_not_revoked() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_REVOCABLE,
      encode_string("token-id-abc"),
    ));

    let mut not_revoked = std::collections::HashSet::new();
    not_revoked.insert("token-id-abc".into());

    let request = AuthRequest {
      now: Some(1700000000),
      not_revoked,
      ..Default::default()
    };
    assert!(verify_caveats(&set, &request).is_ok());
  }

  #[test]
  fn test_revocable_enforcement_denies_when_no_proof() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_REVOCABLE,
      encode_string("token-id-abc"),
    ));

    let request = AuthRequest {
      now: Some(1700000000),
      ..Default::default()
    };
    let err = verify_caveats(&set, &request).unwrap_err();
    assert!(format!("{err}").contains("revocation state required"));
  }

  #[test]
  fn test_revocable_enforcement_denies_wrong_token_id() {
    let mut set = CaveatSet::new();
    set.push(WireCaveat::new(
      CAV_REVOCABLE,
      encode_string("token-id-abc"),
    ));

    let mut not_revoked = std::collections::HashSet::new();
    not_revoked.insert("token-id-xyz".into());

    let request = AuthRequest {
      now: Some(1700000000),
      not_revoked,
      ..Default::default()
    };
    let err = verify_caveats(&set, &request).unwrap_err();
    assert!(format!("{err}").contains("revoked"));
  }

  // --- Attenuation with new types ---

  #[test]
  fn test_attenuation_to_wire_caveats_with_new_types() {
    use crate::traits::{BudgetSpec, FeatureGlobSpec};

    let att = Attenuation {
      apps: vec![("my-app".into(), "rw".into())],
      feature_globs: Some(FeatureGlobSpec {
        include: vec!["src/**".into()],
        exclude: vec!["**/*.env".into()],
      }),
      budget: Some(BudgetSpec {
        id: "agent:daily".into(),
        parent_id: None,
        class: "api_calls".into(),
        limit: 500,
        window: Some("1d".into()),
      }),
      revocable: Some("revoke.pyana.dev".into()),
      ..Default::default()
    };
    let caveats = attenuation_to_wire_caveats(&att);
    // 1 app + 1 feature_glob + 1 budget + 1 revocable = 4
    assert_eq!(caveats.len(), 4);
    assert_eq!(caveats[0].caveat_type, CAV_APP);
    assert_eq!(caveats[1].caveat_type, CAV_FEATURE_GLOB);
    assert_eq!(caveats[2].caveat_type, CAV_BUDGET);
    assert_eq!(caveats[3].caveat_type, CAV_REVOCABLE);
  }
}
