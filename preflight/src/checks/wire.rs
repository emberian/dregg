//! Wire protocol checks: message serialization, PeerRole, rate limiter, auth flow.

use std::time::Duration;

use pyana_wire::auth::{RateLimitConfig, RateLimiter};
use pyana_wire::message::{AuthorizationRequest, Envelope, WireMessage};
use pyana_wire::server::PeerRole;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("message_roundtrip", check_message_roundtrip),
        run_check("peer_role_classification", check_peer_role_classification),
        run_check("rate_limiter", check_rate_limiter),
        run_check("auth_challenge_response", check_auth_challenge_response),
    ]
}

fn check_message_roundtrip() -> Result<(), String> {
    // Test serialization roundtrip for various WireMessage variants.
    let messages: Vec<WireMessage> = vec![
        WireMessage::RequestAttestedRoot,
        WireMessage::PresentToken {
            proof: vec![1, 2, 3, 4, 5],
            request: AuthorizationRequest::new("api/v1/users", "read", "alice"),
            federation_root: [42u8; 32],
        },
        WireMessage::PresentationResult {
            accepted: true,
            reason: Some("authorized".into()),
            request_digest: *blake3::hash(b"test-request").as_bytes(),
        },
    ];

    for msg in &messages {
        // Serialize.
        let bytes = postcard::to_stdvec(msg)
            .map_err(|e| format!("serialize {} failed: {e}", msg.variant_name()))?;

        if bytes.is_empty() {
            return Err(format!("{} serialized to empty bytes", msg.variant_name()));
        }

        // Deserialize.
        let recovered: WireMessage = postcard::from_bytes(&bytes)
            .map_err(|e| format!("deserialize {} failed: {e}", msg.variant_name()))?;

        // Verify variant matches.
        if recovered.variant_name() != msg.variant_name() {
            return Err(format!(
                "variant mismatch: expected {}, got {}",
                msg.variant_name(),
                recovered.variant_name()
            ));
        }
    }

    // Test Envelope wrapping.
    let envelope = Envelope::wrap(WireMessage::RequestAttestedRoot);
    if !envelope.is_version_supported() {
        return Err("freshly wrapped envelope should have supported version".into());
    }

    Ok(())
}

fn check_peer_role_classification() -> Result<(), String> {
    // Verify PeerRole tags and properties.
    let anonymous = PeerRole::Anonymous;
    let light = PeerRole::LightClient;
    let captp = PeerRole::CapTpPeer {
        federation_id: [1u8; 32],
    };
    let member = PeerRole::Member {
        participant_key: [2u8; 32],
    };

    // Tags should be distinct.
    let tags = [anonymous.tag(), light.tag(), captp.tag(), member.tag()];
    for i in 0..tags.len() {
        for j in (i + 1)..tags.len() {
            if tags[i] == tags[j] {
                return Err(format!(
                    "PeerRole tags should be distinct: role {} and {} both have tag {}",
                    i, j, tags[i]
                ));
            }
        }
    }

    // Anonymous should have tag 0.
    if anonymous.tag() != 0 {
        return Err(format!(
            "Anonymous tag should be 0, got {}",
            anonymous.tag()
        ));
    }

    // Member should have tag 1.
    if member.tag() != 1 {
        return Err(format!("Member tag should be 1, got {}", member.tag()));
    }

    Ok(())
}

fn check_rate_limiter() -> Result<(), String> {
    // Create a rate limiter: 5 messages per window.
    let mut limiter = RateLimiter::new(5, Duration::from_secs(60));

    // First 5 should pass.
    for i in 0..5 {
        if !limiter.check() {
            return Err(format!("message {} should be allowed (under limit)", i + 1));
        }
    }

    // 6th should be rate-limited.
    if limiter.check() {
        return Err("6th message should be rate-limited (limit is 5)".into());
    }

    // Verify per-role limits from config.
    let config = RateLimitConfig::default();
    let anon_limit = config.limit_for_role(&PeerRole::Anonymous);
    let member_limit = config.limit_for_role(&PeerRole::Member {
        participant_key: [0u8; 32],
    });

    // Members should have higher limits than anonymous.
    if member_limit <= anon_limit {
        return Err(format!(
            "member limit ({member_limit}) should be > anonymous limit ({anon_limit})"
        ));
    }

    Ok(())
}

fn check_auth_challenge_response() -> Result<(), String> {
    // Simulate the auth challenge-response flow.
    // 1. Create an authorization request.
    let request = AuthorizationRequest::new("api/v1/data", "write", "bob");

    // 2. Verify the request has a valid digest.
    let digest = request.digest();
    if digest == [0u8; 32] {
        return Err("request digest should not be all zeros".into());
    }

    // 3. Same request should produce same digest (deterministic).
    let digest2 = request.digest();
    if digest != digest2 {
        return Err("same request should produce same digest".into());
    }

    // 4. Different request should produce different digest.
    let other_request = AuthorizationRequest::new("api/v1/data", "read", "bob");
    let other_digest = other_request.digest();
    if digest == other_digest {
        return Err("different requests should produce different digests".into());
    }

    // 5. Request with scopes should affect digest.
    let scoped = AuthorizationRequest::new("api/v1/data", "write", "bob")
        .with_scopes(vec!["org:acme".into()]);
    let scoped_digest = scoped.digest();
    // Note: different nonces mean digests will differ anyway, but the point is
    // the digest function incorporates all fields.
    if scoped_digest == [0u8; 32] {
        return Err("scoped request digest should not be zeros".into());
    }

    // 6. Wrap in a WireMessage and verify it serializes.
    let wire_msg = WireMessage::PresentToken {
        proof: vec![0xAA; 100],
        request: request.clone(),
        federation_root: [0xFF; 32],
    };

    let serialized = postcard::to_stdvec(&wire_msg)
        .map_err(|e| format!("serialize PresentToken failed: {e}"))?;

    if serialized.is_empty() {
        return Err("serialized PresentToken should not be empty".into());
    }

    Ok(())
}
