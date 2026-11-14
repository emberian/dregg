//! Receipt policy hints cannot replace the proof-required history envelope.
use dregg_lightclient::external_envelope::{
    EXTERNAL_HISTORY_ENVELOPE_VERSION, ExternalHistoryEnvelope,
};

#[test]
fn coordination_policy_rejects_exempt_envelope() {
    let baseline = ExternalHistoryEnvelope::new("00".repeat(32), String::new());
    assert!(
        serde_json::from_value::<ExternalHistoryEnvelope>(serde_json::to_value(baseline).unwrap())
            .is_ok()
    );
    let signature_only = serde_json::json!({
        "version": EXTERNAL_HISTORY_ENVELOPE_VERSION,
        "vk_fingerprint_hex": "00".repeat(32),
        "proof_status": "not_required",
    });
    assert!(serde_json::from_value::<ExternalHistoryEnvelope>(signature_only).is_err());
}

#[test]
fn coordination_policy_rejects_signature_only_bytes() {
    let vk = dregg_circuit_prove::ivc_turn_chain::RecursionVk([0; 32]);
    for bytes in [
        b"".as_slice(),
        br#"{"proof_status":"not_required"}"#.as_slice(),
    ] {
        assert!(dregg_lightclient::verify_history_bytes(bytes, &vk).is_err());
    }
}
