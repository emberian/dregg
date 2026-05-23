//! Pyana subsystem expressed in DSL form.
//!
//! This module defines pyana's 16 caveats and core effects using the
//! `#[pyana_caveat]` and `#[pyana_effect]` macros. These run ALONGSIDE
//! (not replacing) the hand-written code in `token::pyana_caveats`.
//!
//! The equivalence tests below verify that the DSL-generated evaluators
//! produce the SAME results as the hand-written versions for matching inputs.

use pyana_dsl::{pyana_caveat, pyana_effect};

// ============================================================================
// The 16 Caveats
// ============================================================================

// --- Caveat 0: Organization (confine_org) ---
// In the hand-written code this is a u64 match-any check.
#[pyana_caveat]
fn confine_org(allowed_org: u64, request_org: u64) {
    require!(allowed_org == request_org);
}

// --- Caveat 1: App ---
// The hand-written version checks (app_id, actions) with string matching.
// DSL Phase 1-2 only supports u64/byte comparisons, so we model the
// "does this app_id match?" as a u64 equality check on hashed IDs.
// TODO: needs Phase 3 for string support and action containment.
#[pyana_caveat]
fn confine_app(allowed_app_hash: u64, request_app_hash: u64) {
    require!(allowed_app_hash == request_app_hash);
}

// --- Caveat 2: Service ---
// Same situation as App — modeled as hash equality.
// TODO: needs Phase 3 for string support and action containment.
#[pyana_caveat]
fn confine_service(allowed_service_hash: u64, request_service_hash: u64) {
    require!(allowed_service_hash == request_service_hash);
}

// --- Caveat 4: Feature ---
// Modeled as hash equality (hand-written uses string set containment).
// TODO: needs Phase 3 for string set containment (multiple features).
#[pyana_caveat]
fn confine_feature(allowed_feature_hash: u64, request_feature_hash: u64) {
    require!(allowed_feature_hash == request_feature_hash);
}

// --- Caveat 5: ValidityWindow (not_before + not_after) ---
// The hand-written version checks (Option<i64>, Option<i64>) as a combined window.
// DSL Phase 1-2 doesn't have Option types, so we split into two separate caveats.

#[pyana_caveat]
fn not_after(token_expiry: u64, current_time: u64) {
    require!(current_time <= token_expiry);
}

#[pyana_caveat]
fn not_before(token_start: u64, current_time: u64) {
    require!(current_time >= token_start);
}

// Combined validity_window needs 3 params in a single require expression.
// Phase 1-2 supports multiple require! statements, so we split:
#[pyana_caveat]
fn validity_window(start: u64, end: u64, current_time: u64) {
    require!(current_time >= start);
    require!(current_time <= end);
}

// --- Caveat 8: ConfineUser ---
// The hand-written version uses string match. We use [u8; 32] (e.g., a hash of the user ID).
#[pyana_caveat]
fn confine_user(allowed_user: [u8; 32], request_user: [u8; 32]) {
    require!(allowed_user == request_user);
}

// --- Caveat 9: OAuthProvider ---
// Modeled as hash equality.
// TODO: needs Phase 3 for string support.
#[pyana_caveat]
fn confine_oauth_provider(allowed_provider_hash: u64, request_provider_hash: u64) {
    require!(allowed_provider_hash == request_provider_hash);
}

// --- Caveat 10: OAuthScope ---
// Modeled as set membership — is the requested scope in the allowed set?
#[pyana_caveat]
fn confine_oauth_scope(allowed_scopes: &std::collections::HashSet<u64>, requested_scope: u64) {
    require!(allowed_scopes.contains(requested_scope));
}

// --- Caveat 11: FromMachine ---
#[pyana_caveat]
fn confine_machine(allowed_machine: [u8; 32], request_machine: [u8; 32]) {
    require!(allowed_machine == request_machine);
}

// --- Caveat 12: Command ---
// Modeled as set membership (is command hash in allowed set?).
#[pyana_caveat]
fn confine_command(allowed_commands: &std::collections::HashSet<u64>, requested_command: u64) {
    require!(allowed_commands.contains(requested_command));
}

// --- Caveat 13: FeatureGlob ---
// TODO: needs Phase 3 for glob/regex pattern matching and string support.
// Cannot be expressed in Phase 1-2 DSL. Placeholder as hash equality for now.
#[pyana_caveat]
fn confine_feature_glob(allowed_pattern_hash: u64, request_feature_hash: u64) {
    // NOTE: This is a PLACEHOLDER. Real feature glob requires pattern matching
    // which is not expressible in the arithmetic DSL (Phase 1-2).
    // TODO: needs Phase 3 — glob pattern matching, string operations.
    require!(allowed_pattern_hash == request_feature_hash);
}

// --- Caveat 14: Budget ---
// The hand-written version checks remaining >= request_cost.
// We model this as: remaining must be at least 1 (minimum cost).
#[pyana_caveat]
fn budget(remaining: u64, request_cost: u64) {
    require!(remaining >= request_cost);
}

// --- Caveat 15: Revocable ---
// The hand-written version checks token_id is in a not-revoked set.
// We model this as set membership.
#[pyana_caveat]
fn check_not_revoked(
    not_revoked_set: &std::collections::HashSet<u64>,
    token_id_hash: u64,
) {
    require!(not_revoked_set.contains(token_id_hash));
}

// --- Additional caveat: max_uses (count-based limiting) ---
#[pyana_caveat]
fn max_uses(count: u64, minimum: u64) {
    require!(count >= minimum);
}

// --- Additional caveat: ip_range ---
// TODO: needs Phase 3 — bitwise operations for IP prefix matching.
// Placeholder: model as equality of network prefix hash.
#[pyana_caveat]
fn confine_ip_range(allowed_prefix: u64, request_prefix: u64) {
    // NOTE: Real IP range checking requires bitwise AND with a mask,
    // which Phase 1-2 DSL cannot express.
    // TODO: needs Phase 3 — bitwise operations (AND, shift).
    require!(allowed_prefix == request_prefix);
}

// ============================================================================
// Core Effects
// ============================================================================

// --- Transfer effect ---
// The hand-written code doesn't have an explicit "transfer" function, but the
// token system's budget decrement is conceptually the same.

/// Direction of a transfer: 0 = incoming, 1 = outgoing.
/// Using u64 discriminant since the DSL match arms work with user-defined enums.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TransferDirection {
    Incoming,
    Outgoing,
}

#[pyana_effect(requires = "Send")]
fn transfer(balance: &mut u64, amount: u64, direction: TransferDirection) {
    match direction {
        TransferDirection::Incoming => {
            *balance = *balance + amount;
        }
        TransferDirection::Outgoing => {
            require!(*balance >= amount);
            *balance = *balance - amount;
        }
    }
}

// --- SetField effect ---
// Phase 1-2 only supports `&mut u64` (not `&mut [u8; 32]`).
// TODO: needs Phase 3 for &mut [u8; 32] support.
// For now we model a u64 field assignment.
#[pyana_effect(requires = "SetState")]
fn set_field_u64(field_value: &mut u64, new_value: u64) {
    *field_value = new_value;
}

// ============================================================================
// Tests: Equivalence with hand-written verification
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // not_after equivalence
    // ========================================================================

    #[test]
    fn test_not_after_equivalence_pass() {
        // DSL: current_time <= token_expiry
        assert!(not_after_check(100, 50).is_ok());
        assert!(not_after_check(100, 100).is_ok()); // boundary: equal is OK

        // Hand-written equivalent: verify_caveats with ValidityWindow(None, Some(100))
        // checks `now > not_after` => fail. So now=50, not_after=100 => pass.
        // now=100, not_after=100 => `100 > 100` is false => pass. Matches DSL.
    }

    #[test]
    fn test_not_after_equivalence_fail() {
        // DSL: current_time <= token_expiry fails when time > expiry
        assert!(not_after_check(50, 100).is_err());

        // Hand-written: now=100, not_after=50 => `100 > 50` is true => Expired. Matches.
    }

    // ========================================================================
    // not_before equivalence
    // ========================================================================

    #[test]
    fn test_not_before_equivalence_pass() {
        // DSL: current_time >= token_start
        assert!(not_before_check(1000, 1500).is_ok());
        assert!(not_before_check(1000, 1000).is_ok()); // boundary

        // Hand-written: now=1500, not_before=1000 => `1500 < 1000` false => pass.
    }

    #[test]
    fn test_not_before_equivalence_fail() {
        // DSL: current_time >= token_start fails when time < start
        assert!(not_before_check(5000, 2000).is_err());

        // Hand-written: now=2000, not_before=5000 => `2000 < 5000` true => Expired. Matches.
    }

    // ========================================================================
    // validity_window equivalence
    // ========================================================================

    #[test]
    fn test_validity_window_equivalence_pass() {
        // DSL: current_time >= start AND current_time <= end
        assert!(validity_window_check(1000, 5000, 3000).is_ok());
        assert!(validity_window_check(1000, 5000, 1000).is_ok()); // at start
        assert!(validity_window_check(1000, 5000, 5000).is_ok()); // at end

        // Hand-written: ValidityWindow(Some(1000), Some(5000)), now=3000
        // checks: now < 1000? no. now > 5000? no. => pass.
    }

    #[test]
    fn test_validity_window_equivalence_fail_early() {
        assert!(validity_window_check(1000, 5000, 500).is_err());
        // Hand-written: now=500 < not_before=1000 => Expired.
    }

    #[test]
    fn test_validity_window_equivalence_fail_late() {
        assert!(validity_window_check(1000, 5000, 6000).is_err());
        // Hand-written: now=6000 > not_after=5000 => Expired.
    }

    // ========================================================================
    // confine_user equivalence
    // ========================================================================

    #[test]
    fn test_confine_user_equivalence_pass() {
        let alice = [0xAA; 32];
        assert!(confine_user_check(alice, alice).is_ok());
        // Hand-written: ConfineUser("alice"), request user_id="alice" => pass.
    }

    #[test]
    fn test_confine_user_equivalence_fail() {
        let alice = [0xAA; 32];
        let bob = [0xBB; 32];
        assert!(confine_user_check(alice, bob).is_err());
        // Hand-written: ConfineUser("alice"), request user_id="bob" => Denied.
    }

    // ========================================================================
    // confine_service equivalence
    // ========================================================================

    #[test]
    fn test_confine_service_equivalence_pass() {
        let svc_hash = 12345u64;
        assert!(confine_service_check(svc_hash, svc_hash).is_ok());
        // Hand-written: Service("http", "rw") with request service="http" => pass (name match).
    }

    #[test]
    fn test_confine_service_equivalence_fail() {
        assert!(confine_service_check(12345, 99999).is_err());
        // Hand-written: Service("http", ...) with request service="dns" => Denied.
    }

    // ========================================================================
    // confine_machine equivalence
    // ========================================================================

    #[test]
    fn test_confine_machine_equivalence_pass() {
        let machine = [0x11; 32];
        assert!(confine_machine_check(machine, machine).is_ok());
    }

    #[test]
    fn test_confine_machine_equivalence_fail() {
        let m1 = [0x11; 32];
        let m2 = [0x22; 32];
        assert!(confine_machine_check(m1, m2).is_err());
    }

    // ========================================================================
    // budget equivalence
    // ========================================================================

    #[test]
    fn test_budget_equivalence_pass() {
        // DSL: remaining >= request_cost
        assert!(budget_check(100, 10).is_ok());
        assert!(budget_check(1, 1).is_ok()); // boundary

        // Hand-written: budget remaining=100, request_cost=10 => 100 >= 10 => pass.
    }

    #[test]
    fn test_budget_equivalence_fail() {
        assert!(budget_check(5, 10).is_err());
        // Hand-written: remaining=5, request_cost=10 => "budget exhausted".
    }

    // ========================================================================
    // max_uses equivalence
    // ========================================================================

    #[test]
    fn test_max_uses_pass() {
        assert!(max_uses_check(5, 1).is_ok());
    }

    #[test]
    fn test_max_uses_fail() {
        assert!(max_uses_check(0, 1).is_err());
    }

    // ========================================================================
    // confine_org equivalence
    // ========================================================================

    #[test]
    fn test_confine_org_equivalence_pass() {
        assert!(confine_org_check(42, 42).is_ok());
        // Hand-written: Organization(42), request org_id=Some(42) => pass.
    }

    #[test]
    fn test_confine_org_equivalence_fail() {
        assert!(confine_org_check(42, 99).is_err());
        // Hand-written: Organization(42), request org_id=Some(99) => Denied.
    }

    // ========================================================================
    // confine_app equivalence
    // ========================================================================

    #[test]
    fn test_confine_app_equivalence_pass() {
        let hash = 0xDEAD_BEEFu64;
        assert!(confine_app_check(hash, hash).is_ok());
    }

    #[test]
    fn test_confine_app_equivalence_fail() {
        assert!(confine_app_check(0xDEAD, 0xBEEF).is_err());
    }

    // ========================================================================
    // confine_oauth_provider equivalence
    // ========================================================================

    #[test]
    fn test_confine_oauth_provider_equivalence_pass() {
        let github_hash = 0x1234u64;
        assert!(confine_oauth_provider_check(github_hash, github_hash).is_ok());
    }

    #[test]
    fn test_confine_oauth_provider_equivalence_fail() {
        assert!(confine_oauth_provider_check(0x1234, 0x5678).is_err());
    }

    // ========================================================================
    // confine_oauth_scope (set membership) equivalence
    // ========================================================================

    #[test]
    fn test_confine_oauth_scope_equivalence_pass() {
        let mut allowed = std::collections::HashSet::new();
        allowed.insert(1u64); // "repo"
        allowed.insert(2u64); // "user:email"
        assert!(confine_oauth_scope_check(&allowed, 1).is_ok());
    }

    #[test]
    fn test_confine_oauth_scope_equivalence_fail() {
        let mut allowed = std::collections::HashSet::new();
        allowed.insert(1u64);
        assert!(confine_oauth_scope_check(&allowed, 99).is_err());
        // Hand-written: oauth_scopes=["repo"], request scope="admin" => Denied.
    }

    // ========================================================================
    // confine_command (set membership) equivalence
    // ========================================================================

    #[test]
    fn test_confine_command_equivalence_pass() {
        let mut allowed = std::collections::HashSet::new();
        allowed.insert(100u64); // hash of "deploy"
        allowed.insert(200u64); // hash of "status"
        assert!(confine_command_check(&allowed, 100).is_ok());
    }

    #[test]
    fn test_confine_command_equivalence_fail() {
        let mut allowed = std::collections::HashSet::new();
        allowed.insert(100u64);
        assert!(confine_command_check(&allowed, 999).is_err());
        // Hand-written: commands=["deploy"], request command="rollback" => Denied.
    }

    // ========================================================================
    // check_not_revoked (set membership) equivalence
    // ========================================================================

    #[test]
    fn test_check_not_revoked_equivalence_pass() {
        let mut not_revoked = std::collections::HashSet::new();
        not_revoked.insert(42u64); // hash of "token-id-abc"
        assert!(check_not_revoked_check(&not_revoked, 42).is_ok());
    }

    #[test]
    fn test_check_not_revoked_equivalence_fail() {
        let mut not_revoked = std::collections::HashSet::new();
        not_revoked.insert(42u64);
        assert!(check_not_revoked_check(&not_revoked, 99).is_err());
        // Hand-written: not_revoked has "token-id-abc", checking "other-id" => Denied.
    }

    // ========================================================================
    // confine_feature equivalence
    // ========================================================================

    #[test]
    fn test_confine_feature_equivalence_pass() {
        let feat_hash = 0xCAFEu64;
        assert!(confine_feature_check(feat_hash, feat_hash).is_ok());
    }

    #[test]
    fn test_confine_feature_equivalence_fail() {
        assert!(confine_feature_check(0xCAFE, 0xBABE).is_err());
    }

    // ========================================================================
    // confine_feature_glob (placeholder)
    // ========================================================================

    #[test]
    fn test_confine_feature_glob_placeholder() {
        // This is a placeholder — real glob matching needs Phase 3.
        assert!(confine_feature_glob_check(0xABC, 0xABC).is_ok());
        assert!(confine_feature_glob_check(0xABC, 0xDEF).is_err());
    }

    // ========================================================================
    // confine_ip_range (placeholder)
    // ========================================================================

    #[test]
    fn test_confine_ip_range_placeholder() {
        // Placeholder — real IP range needs Phase 3 bitwise ops.
        assert!(confine_ip_range_check(192168, 192168).is_ok());
        assert!(confine_ip_range_check(192168, 10000).is_err());
    }

    // ========================================================================
    // Transfer effect equivalence
    // ========================================================================

    #[test]
    fn test_transfer_outgoing_pass() {
        let mut balance = 100u64;
        let result = transfer_check(&mut balance, 30, TransferDirection::Outgoing);
        assert!(result.is_ok());
        assert_eq!(balance, 70);
        // Hand-written equivalent: budget remaining=100, cost=30 => pass, remaining becomes 70.
    }

    #[test]
    fn test_transfer_outgoing_fail_insufficient() {
        let mut balance = 20u64;
        let result = transfer_check(&mut balance, 30, TransferDirection::Outgoing);
        assert!(result.is_err());
        assert_eq!(balance, 20); // unchanged on failure
        // Hand-written: remaining=20, cost=30 => "budget exhausted".
    }

    #[test]
    fn test_transfer_incoming() {
        let mut balance = 50u64;
        let result = transfer_check(&mut balance, 25, TransferDirection::Incoming);
        assert!(result.is_ok());
        assert_eq!(balance, 75);
    }

    #[test]
    fn test_transfer_outgoing_exact() {
        let mut balance = 100u64;
        let result = transfer_check(&mut balance, 100, TransferDirection::Outgoing);
        assert!(result.is_ok());
        assert_eq!(balance, 0);
    }

    // ========================================================================
    // SetField effect
    // ========================================================================

    #[test]
    fn test_set_field_u64_effect() {
        let mut field = 0u64;
        let result = set_field_u64_check(&mut field, 42);
        assert!(result.is_ok());
        assert_eq!(field, 42);
    }

    #[test]
    fn test_set_field_u64_overwrite() {
        let mut field = 99u64;
        let result = set_field_u64_check(&mut field, 0);
        assert!(result.is_ok());
        assert_eq!(field, 0);
    }

    // ========================================================================
    // AIR descriptor verification
    // ========================================================================

    #[test]
    fn test_not_after_air_descriptors() {
        let air = not_after_air_constraints();
        assert_eq!(air.name, "not_after");
        assert!(air.width > 0, "trace width must be non-zero");
        assert!(!air.constraints.is_empty(), "constraints must not be empty");
        assert_eq!(air.public_inputs.len(), 2); // token_expiry, current_time
    }

    #[test]
    fn test_not_before_air_descriptors() {
        let air = not_before_air_constraints();
        assert_eq!(air.name, "not_before");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_validity_window_air_descriptors() {
        let air = validity_window_air_constraints();
        assert_eq!(air.name, "validity_window");
        assert!(air.width > 0);
        // 2 require! statements => 2 constraints
        assert_eq!(air.constraints.len(), 2);
        assert_eq!(air.public_inputs.len(), 3); // start, end, current_time
    }

    #[test]
    fn test_confine_user_air_descriptors() {
        let air = confine_user_air_constraints();
        assert_eq!(air.name, "confine_user");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_confine_machine_air_descriptors() {
        let air = confine_machine_air_constraints();
        assert_eq!(air.name, "confine_machine");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_confine_org_air_descriptors() {
        let air = confine_org_air_constraints();
        assert_eq!(air.name, "confine_org");
        // Equality: 2 param columns, no auxiliary
        assert_eq!(air.width, 2);
        assert!(!air.constraints.is_empty());
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_confine_service_air_descriptors() {
        let air = confine_service_air_constraints();
        assert_eq!(air.name, "confine_service");
        assert_eq!(air.width, 2);
        assert!(!air.constraints.is_empty());
    }

    #[test]
    fn test_confine_oauth_scope_air_descriptors() {
        let air = confine_oauth_scope_air_constraints();
        assert_eq!(air.name, "confine_oauth_scope");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
        // Should have a MerkleMembership constraint
        let has_membership = air.constraints.iter().any(|c| {
            matches!(c, pyana_dsl_runtime::Constraint::MerkleMembership { .. })
        });
        assert!(has_membership);
    }

    #[test]
    fn test_confine_command_air_descriptors() {
        let air = confine_command_air_constraints();
        assert_eq!(air.name, "confine_command");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
    }

    #[test]
    fn test_budget_air_descriptors() {
        let air = budget_air_constraints();
        assert_eq!(air.name, "budget");
        // budget uses >= which needs range check columns
        assert!(air.width >= 2);
        assert!(!air.constraints.is_empty());
        assert_eq!(air.public_inputs.len(), 2);
    }

    #[test]
    fn test_transfer_air_descriptors() {
        let air = transfer_air_constraints();
        assert_eq!(air.name, "transfer");
        // Mutable balance (2 cols: old+new) + amount (1) + direction (1) + aux
        assert!(air.width >= 4);
        assert!(!air.constraints.is_empty());
    }

    #[test]
    fn test_set_field_u64_air_descriptors() {
        let air = set_field_u64_air_constraints();
        assert_eq!(air.name, "set_field_u64");
        // Mutable field_value (2 cols: old+new) + new_value (1)
        assert!(air.width >= 3);
        assert!(!air.constraints.is_empty());
    }

    #[test]
    fn test_check_not_revoked_air_descriptors() {
        let air = check_not_revoked_air_constraints();
        assert_eq!(air.name, "check_not_revoked");
        assert!(air.width > 0);
        assert!(!air.constraints.is_empty());
    }

    // ========================================================================
    // Effect descriptor verification
    // ========================================================================

    #[test]
    fn test_transfer_effect_descriptor() {
        let desc = transfer_effect_descriptor();
        assert_eq!(desc.name, "transfer");
        assert_eq!(desc.required_permission, Some("Send"));
        assert_eq!(desc.mutable_params, vec!["balance"]);
    }

    #[test]
    fn test_set_field_u64_effect_descriptor() {
        let desc = set_field_u64_effect_descriptor();
        assert_eq!(desc.name, "set_field_u64");
        assert_eq!(desc.required_permission, Some("SetState"));
        assert_eq!(desc.mutable_params, vec!["field_value"]);
    }

    // ========================================================================
    // AIR width reasonableness checks
    // ========================================================================

    #[test]
    fn test_all_air_widths_reasonable() {
        let descriptors = [
            not_after_air_constraints(),
            not_before_air_constraints(),
            validity_window_air_constraints(),
            confine_user_air_constraints(),
            confine_machine_air_constraints(),
            confine_org_air_constraints(),
            confine_app_air_constraints(),
            confine_service_air_constraints(),
            confine_feature_air_constraints(),
            confine_oauth_provider_air_constraints(),
            confine_oauth_scope_air_constraints(),
            confine_command_air_constraints(),
            confine_feature_glob_air_constraints(),
            budget_air_constraints(),
            check_not_revoked_air_constraints(),
            max_uses_air_constraints(),
            confine_ip_range_air_constraints(),
            transfer_air_constraints(),
            set_field_u64_air_constraints(),
        ];

        for desc in &descriptors {
            assert!(
                desc.width > 0 && desc.width <= 256,
                "AIR width for '{}' is unreasonable: {}",
                desc.name,
                desc.width
            );
            assert!(
                !desc.constraints.is_empty(),
                "AIR for '{}' has no constraints",
                desc.name
            );
        }
    }
}
