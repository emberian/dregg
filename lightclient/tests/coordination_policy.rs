//! Receipt policy hints cannot replace the proof-required history envelope.
use dregg_lightclient::external_envelope::{
    EXTERNAL_HISTORY_ENVELOPE_VERSION, ExternalHistoryEnvelope,
};

#[test]
fn not_required_is_not_a_light_client_proof_envelope() {
    let signature_only = serde_json::json!({
        "version": EXTERNAL_HISTORY_ENVELOPE_VERSION,
        "vk_fingerprint_hex": "00".repeat(32),
        "proof_status": "not_required",
    });
    assert!(serde_json::from_value::<ExternalHistoryEnvelope>(signature_only).is_err());
}
