//! Canonical witnessed-receipt artifact helpers.
//!
//! The wire/disk format is owned by `dregg-turn` as the `DWR1` envelope. The
//! SDK re-exports thin helpers so clients do not depend on node-local JSON
//! response shapes or raw postcard details.

use crate::error::SdkError;
use dregg_turn::WitnessedReceipt;

/// Current canonical witnessed-receipt artifact format tag.
pub const WITNESSED_RECEIPT_ARTIFACT_FORMAT: &str = "DWR1";

/// Encode a witnessed receipt into the canonical DWR1 artifact envelope.
pub fn encode_witnessed_receipt_artifact(
    witnessed: &WitnessedReceipt,
) -> Result<Vec<u8>, SdkError> {
    witnessed
        .to_artifact_bytes()
        .map_err(SdkError::WitnessArtifact)
}

/// Decode a witnessed receipt from the canonical DWR1 artifact envelope.
pub fn decode_witnessed_receipt_artifact(bytes: &[u8]) -> Result<WitnessedReceipt, SdkError> {
    WitnessedReceipt::from_artifact_bytes(bytes).map_err(SdkError::WitnessArtifact)
}

/// Decode a node `/api/receipts/{hash}/witnesses` `witness_artifacts` hex item.
pub fn decode_witnessed_receipt_artifact_hex(hex: &str) -> Result<WitnessedReceipt, SdkError> {
    let bytes = decode_hex(hex).map_err(SdkError::WitnessArtifact)?;
    decode_witnessed_receipt_artifact(&bytes)
}

fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("hex string has odd length".into());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for idx in (0..s.len()).step_by(2) {
        let byte = u8::from_str_radix(&s[idx..idx + 2], 16)
            .map_err(|_| format!("invalid hex byte at offset {idx}"))?;
        out.push(byte);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_witnessed() -> WitnessedReceipt {
        let mut receipt = dregg_turn::TurnReceipt::default();
        receipt.turn_hash = [7; 32];
        receipt.effects_hash = [8; 32];
        receipt.agent = dregg_types::CellId([9; 32]);
        WitnessedReceipt::from_components(receipt, vec![1, 2, 3], vec![4, 5], None)
    }

    #[test]
    fn sdk_decodes_canonical_witness_artifact() {
        let witnessed = sample_witnessed();
        let artifact = encode_witnessed_receipt_artifact(&witnessed).expect("encode artifact");
        let decoded = decode_witnessed_receipt_artifact(&artifact).expect("decode artifact");
        assert_eq!(
            decoded.receipt.receipt_hash(),
            witnessed.receipt.receipt_hash()
        );
        assert_eq!(decoded.proof_bytes, witnessed.proof_bytes);
        assert_eq!(WITNESSED_RECEIPT_ARTIFACT_FORMAT, "DWR1");
    }
}
