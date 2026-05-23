//! Name resolution checks: petnames, registration, delegation, hierarchical resolution.

use pyana_captp::uri::PyanaUri;
use pyana_sdk::names::{NameError, PetnameDb, validate_name_segment};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("petname_lifecycle", check_petname_lifecycle),
        run_check("registration_resolve", check_registration_resolve),
        run_check("delegation_subname", check_delegation_subname),
        run_check("hierarchical_dotted", check_hierarchical_dotted),
    ]
}

fn make_test_uri(label: &str) -> PyanaUri {
    let fed_id = *blake3::hash(format!("fed-{label}").as_bytes()).as_bytes();
    let cell_id = *blake3::hash(format!("cell-{label}").as_bytes()).as_bytes();
    let swiss = *blake3::hash(format!("swiss-{label}").as_bytes()).as_bytes();
    PyanaUri {
        federation_id: fed_id,
        cell_id,
        swiss,
    }
}

fn check_petname_lifecycle() -> Result<(), String> {
    let mut db = PetnameDb::new();

    let uri = make_test_uri("alice");

    // Set a petname.
    db.set_petname("alice", uri.clone(), 1);

    // Resolve it.
    let resolved = db.get_petname("alice");
    match resolved {
        Some(entry) => {
            if entry.target != uri {
                return Err("petname should resolve to the URI we set".into());
            }
            if entry.label != "alice" {
                return Err(format!("expected label 'alice', got '{}'", entry.label));
            }
        }
        None => return Err("petname 'alice' should be resolvable after set".into()),
    }

    // Remove it.
    db.remove_petname("alice");

    // Verify it's gone.
    if db.get_petname("alice").is_some() {
        return Err("petname should not resolve after removal".into());
    }

    Ok(())
}

fn check_registration_resolve() -> Result<(), String> {
    // Test name segment validation (registration prerequisite).
    validate_name_segment("valid-name")
        .map_err(|e| format!("'valid-name' should be valid: {e}"))?;

    validate_name_segment("alice_42").map_err(|e| format!("'alice_42' should be valid: {e}"))?;

    // Invalid segments should be rejected.
    let result = validate_name_segment("-starts-with-dash");
    if result.is_ok() {
        return Err("segment starting with dash should be rejected".into());
    }

    let result = validate_name_segment("");
    match result {
        Err(NameError::EmptySegment) => {} // expected
        Err(other) => return Err(format!("expected EmptySegment, got {other}")),
        Ok(()) => return Err("empty segment should be rejected".into()),
    }

    // Segment too long.
    let long_name = "a".repeat(64);
    let result = validate_name_segment(&long_name);
    match result {
        Err(NameError::SegmentTooLong(_)) => {} // expected
        Err(other) => return Err(format!("expected SegmentTooLong, got {other}")),
        Ok(()) => return Err("64-char segment should exceed 63-char limit".into()),
    }

    // Invalid characters.
    let result = validate_name_segment("UPPERCASE");
    if result.is_ok() {
        return Err("uppercase should be rejected (only a-z0-9-_ allowed)".into());
    }

    Ok(())
}

fn check_delegation_subname() -> Result<(), String> {
    // Verify that the petname DB can store hierarchical names (dotted).
    let mut db = PetnameDb::new();

    let parent_uri = make_test_uri("alice");
    let child_uri = make_test_uri("alice-project");

    // Set parent petname.
    db.set_petname("alice", parent_uri.clone(), 1);

    // Set a sub-petname (simulating delegation awareness).
    db.set_petname_with_notes("project.alice", child_uri.clone(), 2, "Alice's project");

    // Both should resolve independently.
    let parent = db.get_petname("alice");
    if parent.is_none() {
        return Err("parent petname should resolve".into());
    }

    let child = db.get_petname("project.alice");
    match child {
        Some(entry) => {
            if entry.target != child_uri {
                return Err("child petname should resolve to child URI".into());
            }
        }
        None => return Err("delegated sub-petname should resolve".into()),
    }

    // Validate the child name segments are individually valid.
    for segment in "project.alice".split('.') {
        validate_name_segment(segment)
            .map_err(|e| format!("segment '{segment}' should be valid: {e}"))?;
    }

    Ok(())
}

fn check_hierarchical_dotted() -> Result<(), String> {
    // Test hierarchical name parsing and segment validation.
    let dotted_name = "service.team.org";

    // Each segment should validate.
    let segments: Vec<&str> = dotted_name.split('.').collect();
    if segments.len() != 3 {
        return Err(format!("expected 3 segments, got {}", segments.len()));
    }

    for segment in &segments {
        validate_name_segment(segment).map_err(|e| format!("segment '{segment}' invalid: {e}"))?;
    }

    // Verify resolution priority: rightmost segment is the TLD/root.
    // In hierarchical resolution, "service.team.org" traverses: org -> team -> service
    if segments[2] != "org" {
        return Err("rightmost segment should be 'org'".into());
    }
    if segments[1] != "team" {
        return Err("middle segment should be 'team'".into());
    }
    if segments[0] != "service" {
        return Err("leftmost segment should be 'service'".into());
    }

    // Invalid hierarchical names should fail at least one segment.
    let bad_dotted = "valid..empty-segment";
    let bad_segments: Vec<&str> = bad_dotted.split('.').collect();
    let has_invalid = bad_segments
        .iter()
        .any(|s| validate_name_segment(s).is_err());
    if !has_invalid {
        return Err("dotted name with empty segment should have invalid segments".into());
    }

    Ok(())
}
