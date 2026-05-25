//! Integration: sturdy-ref serialization → wire transmission → restore at recipient.
//!
//! Covers:
//! - Serialize a PyanaUri (pyana:// format), transmit as bytes, parse at receiver,
//!   reconstruct the original swiss entry by re-presenting to the SwissTable
//! - Verify the receiver gets the same cell_id and permissions
//! - Verify tampered URI (wrong swiss) fails to enliven
//! - Verify corrupt base58 is rejected by the parser

use pyana_captp::{PyanaUri, SwissTable};
use pyana_cell::AuthRequired;
use pyana_types::CellId;

fn cell(b: u8) -> CellId {
    CellId([b; 32])
}

// =============================================================================
// Serialize → transmit (Vec<u8>) → parse → enliven at receiver
// =============================================================================

#[test]
fn sturdy_ref_serialize_transmit_restore_enlivens() {
    let mut sender_table = SwissTable::new();
    let cap_cell = cell(0xBE);
    let fed_id = [0xFE; 32];

    // Sender exports the cap.
    let swiss = sender_table.export(cap_cell, AuthRequired::Signature, 1, None);
    let uri = sender_table.make_uri(fed_id, &swiss).unwrap();

    // Serialize to the canonical pyana:// string (wire representation).
    let wire_string = uri.to_uri_string();
    assert!(wire_string.starts_with("pyana://"));

    // Simulate transmission: convert to bytes and back to string.
    let wire_bytes = wire_string.as_bytes().to_vec();
    let received_str = std::str::from_utf8(&wire_bytes).unwrap();

    // Receiver parses the URI.
    let parsed = PyanaUri::parse(received_str).expect("valid URI must parse");
    assert_eq!(parsed.federation_id, fed_id);
    assert_eq!(parsed.cell_id, cap_cell.0);
    assert_eq!(parsed.swiss, swiss);

    // Receiver presents the swiss number to the sender's table (or a replica of it).
    let entry = sender_table
        .enliven(&parsed.swiss, 1)
        .expect("receiver must be able to enliven the parsed swiss number");

    assert_eq!(entry.cell_id, cap_cell);
    assert_eq!(entry.permissions, AuthRequired::Signature);
}

// =============================================================================
// Tampered URI (wrong swiss bytes) fails to enliven
// =============================================================================

#[test]
fn tampered_swiss_fails_to_enliven() {
    let mut table = SwissTable::new();
    let c = cell(0x11);
    let fed_id = [0xAA; 32];

    let swiss = table.export(c, AuthRequired::Signature, 1, None);

    // Construct a URI with a valid-format but wrong swiss (all 0xFF).
    let tampered = PyanaUri {
        federation_id: fed_id,
        cell_id: c.0,
        swiss: [0xFF; 32],
    };
    let tampered_str = tampered.to_uri_string();
    let parsed = PyanaUri::parse(&tampered_str).unwrap();

    // swiss in parsed != our registered swiss
    assert_ne!(parsed.swiss, swiss);

    let err = table
        .enliven(&parsed.swiss, 1)
        .expect_err("tampered swiss must not enliven");
    assert_eq!(err, pyana_captp::EnlivenError::NotFound);
}

// =============================================================================
// Corrupt base58 in URI is rejected at parse time
// =============================================================================

#[test]
fn corrupt_base58_rejected_by_parser() {
    // '0', 'O', 'I', 'l' are not valid base58 characters.
    let bad_uri = "pyana://0INVALID_BASE58/validpart/validpart";
    let err = PyanaUri::parse(bad_uri).expect_err("corrupt base58 must fail");
    assert!(matches!(err, pyana_captp::UriError::Base58Decode { .. }));
}

// =============================================================================
// Wrong segment count is rejected
// =============================================================================

#[test]
fn wrong_segment_count_rejected() {
    // Only two path segments (missing swiss).
    // Build a minimal valid two-segment URI using a real cap URI minus its last segment.
    let mut table = SwissTable::new();
    let swiss = table.export(cell(0xAA), AuthRequired::None, 1, None);
    let uri = table.make_uri([0x11; 32], &swiss).unwrap();
    let full = uri.to_uri_string();
    // Strip the last /swiss segment.
    let two_seg: String = {
        let mut parts: Vec<&str> = full.split('/').collect();
        parts.pop();
        parts.join("/")
    };
    let err = PyanaUri::parse(&two_seg).expect_err("two-segment URI must fail");
    assert!(matches!(
        err,
        pyana_captp::UriError::WrongSegmentCount { .. }
    ));
}

// =============================================================================
// Wrong scheme prefix is rejected
// =============================================================================

#[test]
fn wrong_scheme_rejected() {
    let err = PyanaUri::parse("https://example.com/a/b/c").expect_err("wrong scheme must fail");
    assert_eq!(err, pyana_captp::UriError::InvalidScheme);
}

// =============================================================================
// Two independent caps produce distinct URIs
// =============================================================================

#[test]
fn two_caps_produce_distinct_uris() {
    let mut table = SwissTable::new();
    let fed_id = [0xDD; 32];

    let s1 = table.export(cell(0x01), AuthRequired::Signature, 1, None);
    let s2 = table.export(cell(0x02), AuthRequired::Signature, 1, None);

    // Swiss numbers must be distinct (probabilistic: 2^256 collision space).
    assert_ne!(s1, s2);

    let u1 = table.make_uri(fed_id, &s1).unwrap();
    let u2 = table.make_uri(fed_id, &s2).unwrap();
    assert_ne!(u1.to_uri_string(), u2.to_uri_string());

    // Each URI enlivens its own cap and only its own cap.
    let e1 = table.enliven(&u1.swiss, 1).unwrap();
    assert_eq!(e1.cell_id, cell(0x01));

    let e2 = table.enliven(&u2.swiss, 1).unwrap();
    assert_eq!(e2.cell_id, cell(0x02));
}

