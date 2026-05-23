//! Pyana-specific peer messages exchanged over iroh connections.
//!
//! All messages are serialized with postcard (a compact no_std-friendly format)
//! and framed with a 4-byte big-endian length prefix over QUIC streams.

use serde::{Deserialize, Serialize};

// Used by pad_message for random fill.
#[allow(unused_imports)]
use rand::Fill;

/// Messages exchanged between pyana peers over direct QUIC connections
/// or disseminated via gossip.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum PeerMessage {
    // ─── Turn dissemination (causal chaining) ───────────────────────
    /// Publish a new turn to peers. Contains the turn hash, serialized turn data,
    /// and the hashes of causally-preceding turns.
    PublishTurn {
        turn_hash: [u8; 32],
        turn_data: Vec<u8>,
        causal_deps: Vec<[u8; 32]>,
    },

    /// Request a specific turn by hash (pull-based sync).
    RequestTurn { turn_hash: [u8; 32] },

    /// Response to a turn request. `None` means the turn is not known.
    TurnResponse { turn_data: Option<Vec<u8>> },

    // ─── Federation sync ────────────────────────────────────────────
    /// Broadcast an updated attested root (serialized AttestedRoot).
    AttestedRootUpdate { root: Vec<u8> },

    /// Gossip a token revocation to the network.
    RevocationGossip {
        token_id: String,
        signature: Vec<u8>,
    },

    // ─── Cell state sync ────────────────────────────────────────────
    /// Request the current state of a cell by ID.
    CellStateRequest { cell_id: [u8; 32] },

    /// Response with the serialized cell state (or None if unknown).
    CellStateResponse { cell: Option<Vec<u8>> },

    // ─── Intent dissemination ─────────────────────────────────────────
    /// Publish an intent to the gossip network (dedicated variant).
    PublishIntent {
        intent_hash: [u8; 32],
        intent_data: Vec<u8>,
    },

    // ─── Atomic multi-party coordination ────────────────────────────
    /// Propose an atomic turn affecting multiple cells.
    ProposeAtomicTurn {
        forest_hash: [u8; 32],
        participants: Vec<[u8; 32]>,
        forest_data: Vec<u8>,
    },

    /// Vote on an atomic turn proposal.
    VoteAtomicTurn {
        forest_hash: [u8; 32],
        vote: bool,
        signature: Vec<u8>,
    },

    /// Commit an atomic turn with a quorum certificate.
    CommitAtomicTurn {
        forest_hash: [u8; 32],
        /// Serialized quorum certificate (signatures from participants).
        qc: Vec<u8>,
    },

    // ─── Pipeline dissemination ────────────────────────────────────
    /// Publish a pipeline to peers for federated execution.
    PublishPipeline {
        pipeline_hash: [u8; 32],
        pipeline_data: Vec<u8>,
    },

    // ─── Checkpoint dissemination ─────────────────────────────────
    /// Publish a checkpoint (federation-attested state snapshot) to peers.
    /// Contains the checkpoint height and serialized checkpoint data.
    PublishCheckpoint {
        height: u64,
        checkpoint_data: Vec<u8>,
    },
}

/// Length-prefixed framing for messages over QUIC streams.
impl PeerMessage {
    /// Serialize this message with a 4-byte big-endian length prefix.
    pub fn encode(&self) -> Vec<u8> {
        let payload = postcard::to_stdvec(self).expect("PeerMessage serialization cannot fail");
        let len = payload.len() as u32;
        let mut buf = Vec::with_capacity(4 + payload.len());
        buf.extend_from_slice(&len.to_be_bytes());
        buf.extend_from_slice(&payload);
        buf
    }

    /// Decode a message from a length-prefixed buffer.
    /// The buffer must start with the 4-byte length prefix.
    pub fn decode(buf: &[u8]) -> Result<(Self, usize), DecodeError> {
        if buf.len() < 4 {
            return Err(DecodeError::Incomplete);
        }
        let len = u32::from_be_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
        if buf.len() < 4 + len {
            return Err(DecodeError::Incomplete);
        }
        let msg = postcard::from_bytes(&buf[4..4 + len])
            .map_err(|e| DecodeError::Postcard(e.to_string()))?;
        Ok((msg, 4 + len))
    }

    /// Decode from a byte slice without length prefix (raw postcard).
    pub fn decode_raw(buf: &[u8]) -> Result<Self, DecodeError> {
        postcard::from_bytes(buf).map_err(|e| DecodeError::Postcard(e.to_string()))
    }

    /// Serialize without length prefix (for gossip, where framing is handled externally).
    pub fn encode_raw(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("PeerMessage serialization cannot fail")
    }
}

// ─── Two-Bucket Message Padding ─────────────────────────────────────────────
//
// Hides message type from traffic-analysis by padding all wire messages to one
// of two fixed sizes. See docs/design-network-privacy.md Phase 1.

/// Small bucket size: 4 KiB. Covers turns, intents, revocations.
pub const SMALL_BUCKET: usize = 4096;

/// Large bucket size: 512 KiB. Covers STARK proofs, recursive proofs, checkpoints.
pub const LARGE_BUCKET: usize = 524_288;

/// Pad a serialized payload to a fixed bucket size.
///
/// Wire format of the padded output:
/// ```text
/// [4 bytes: actual payload length, little-endian u32]
/// [payload bytes]
/// [random padding to fill bucket]
/// ```
///
/// Messages larger than `LARGE_BUCKET - 4` bytes are returned as-is with a
/// 4-byte length prefix but no additional padding (they are already identifiable
/// by their exceptional size and padding would be wasteful).
pub fn pad_message(payload: &[u8]) -> Vec<u8> {
    // The padded frame needs 4 bytes for the length prefix plus the payload.
    let framed_len = 4 + payload.len();

    let target_size = if framed_len <= SMALL_BUCKET {
        SMALL_BUCKET
    } else if framed_len <= LARGE_BUCKET {
        LARGE_BUCKET
    } else {
        // Too large to pad economically — just frame it.
        tracing::warn!(
            "Message too large for padding buckets ({} bytes); sending unpadded",
            payload.len()
        );
        framed_len
    };

    let mut padded = Vec::with_capacity(target_size);
    // 4-byte length prefix (actual payload length).
    padded.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    // Actual payload.
    padded.extend_from_slice(payload);
    // Random padding to fill bucket.
    let pad_len = target_size - 4 - payload.len();
    if pad_len > 0 {
        let mut pad = vec![0u8; pad_len];
        rand::rng().fill(&mut pad[..]);
        padded.extend_from_slice(&pad);
    }

    padded
}

/// Strip padding from a received padded frame, returning the original payload.
///
/// Returns `None` if the frame is malformed (too short or inner length exceeds
/// frame bounds).
pub fn unpad_message(padded: &[u8]) -> Option<&[u8]> {
    if padded.len() < 4 {
        return None;
    }
    let len = u32::from_le_bytes(padded[0..4].try_into().ok()?) as usize;
    if 4 + len > padded.len() {
        return None;
    }
    Some(&padded[4..4 + len])
}

/// Errors from message decoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    /// Not enough data to decode the message (need more bytes).
    Incomplete,
    /// Postcard deserialization failed.
    Postcard(String),
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecodeError::Incomplete => write!(f, "incomplete message (need more bytes)"),
            DecodeError::Postcard(e) => write!(f, "postcard decode error: {e}"),
        }
    }
}

impl std::error::Error for DecodeError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_publish_turn() {
        let msg = PeerMessage::PublishTurn {
            turn_hash: [0xab; 32],
            turn_data: vec![1, 2, 3, 4, 5],
            causal_deps: vec![[0xcd; 32], [0xef; 32]],
        };
        let encoded = msg.encode();
        let (decoded, consumed) = PeerMessage::decode(&encoded).unwrap();
        assert_eq!(decoded, msg);
        assert_eq!(consumed, encoded.len());
    }

    #[test]
    fn roundtrip_all_variants() {
        let messages = vec![
            PeerMessage::PublishTurn {
                turn_hash: [1; 32],
                turn_data: vec![10, 20, 30],
                causal_deps: vec![],
            },
            PeerMessage::RequestTurn { turn_hash: [2; 32] },
            PeerMessage::TurnResponse {
                turn_data: Some(vec![99]),
            },
            PeerMessage::TurnResponse { turn_data: None },
            PeerMessage::AttestedRootUpdate {
                root: vec![5, 6, 7, 8],
            },
            PeerMessage::RevocationGossip {
                token_id: "token-xyz-123".to_string(),
                signature: vec![0xaa; 64],
            },
            PeerMessage::PublishIntent {
                intent_hash: [10; 32],
                intent_data: vec![11, 12, 13],
            },
            PeerMessage::CellStateRequest { cell_id: [3; 32] },
            PeerMessage::CellStateResponse {
                cell: Some(vec![42; 100]),
            },
            PeerMessage::ProposeAtomicTurn {
                forest_hash: [4; 32],
                participants: vec![[5; 32], [6; 32]],
                forest_data: vec![7; 200],
            },
            PeerMessage::VoteAtomicTurn {
                forest_hash: [8; 32],
                vote: true,
                signature: vec![0xbb; 64],
            },
            PeerMessage::CommitAtomicTurn {
                forest_hash: [9; 32],
                qc: vec![0xcc; 128],
            },
        ];

        for msg in &messages {
            let encoded = msg.encode();
            let (decoded, consumed) = PeerMessage::decode(&encoded).unwrap();
            assert_eq!(&decoded, msg);
            assert_eq!(consumed, encoded.len());

            // Also test raw encoding
            let raw = msg.encode_raw();
            let decoded_raw = PeerMessage::decode_raw(&raw).unwrap();
            assert_eq!(&decoded_raw, msg);
        }
    }

    #[test]
    fn decode_incomplete() {
        assert_eq!(PeerMessage::decode(&[0, 0]), Err(DecodeError::Incomplete));
        // Length says 100 bytes but we only have 4
        assert_eq!(
            PeerMessage::decode(&[0, 0, 0, 100]),
            Err(DecodeError::Incomplete)
        );
    }

    // ─── Two-bucket padding tests ──────────────────────────────────────────

    #[test]
    fn pad_small_message_to_small_bucket() {
        let payload = vec![0xAB; 100]; // 100 bytes, well under 4 KiB
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::SMALL_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_empty_message_to_small_bucket() {
        let payload: Vec<u8> = vec![];
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::SMALL_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_max_small_message() {
        // Maximum payload that fits in small bucket: SMALL_BUCKET - 4 bytes for length
        let payload = vec![0x42; super::SMALL_BUCKET - 4];
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::SMALL_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_just_over_small_goes_to_large_bucket() {
        // One byte too large for small bucket
        let payload = vec![0x42; super::SMALL_BUCKET - 3];
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::LARGE_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_medium_message_to_large_bucket() {
        let payload = vec![0xCD; 50_000]; // 50 KiB, goes to large bucket
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::LARGE_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_max_large_message() {
        // Maximum payload that fits in large bucket: LARGE_BUCKET - 4
        let payload = vec![0xEF; super::LARGE_BUCKET - 4];
        let padded = super::pad_message(&payload);
        assert_eq!(padded.len(), super::LARGE_BUCKET);

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_oversized_message_not_padded() {
        // Larger than large bucket — sent as-is with just the length prefix
        let payload = vec![0xFF; super::LARGE_BUCKET]; // exactly LARGE_BUCKET payload => framed is LARGE_BUCKET + 4
        let padded = super::pad_message(&payload);
        // Should be exactly 4 + payload.len() (no extra padding)
        assert_eq!(padded.len(), 4 + payload.len());

        let recovered = super::unpad_message(&padded).unwrap();
        assert_eq!(recovered, &payload[..]);
    }

    #[test]
    fn pad_random_fill_not_all_zeros() {
        // Padding should be random, not zeros (statistical check)
        let payload = vec![0x00; 10];
        let padded = super::pad_message(&payload);
        // The padding region starts at offset 4 + 10 = 14
        let padding_region = &padded[14..];
        // With 4082 random bytes, probability of all zeros is negligible
        let nonzero_count = padding_region.iter().filter(|&&b| b != 0).count();
        assert!(
            nonzero_count > 100,
            "Padding should contain random bytes, found only {} non-zero in {} bytes",
            nonzero_count,
            padding_region.len()
        );
    }

    #[test]
    fn unpad_rejects_short_frame() {
        assert!(super::unpad_message(&[]).is_none());
        assert!(super::unpad_message(&[1, 2, 3]).is_none());
    }

    #[test]
    fn unpad_rejects_invalid_length() {
        // Length prefix says 100 bytes but frame is only 10 bytes total
        let mut frame = vec![0u8; 10];
        frame[0..4].copy_from_slice(&100u32.to_le_bytes());
        assert!(super::unpad_message(&frame).is_none());
    }

    #[test]
    fn all_message_types_pad_to_bucket_sizes() {
        // Verify that typical message types all produce exactly bucket-sized outputs
        let messages = vec![
            PeerMessage::PublishTurn {
                turn_hash: [1; 32],
                turn_data: vec![10; 800],
                causal_deps: vec![[2; 32]],
            },
            PeerMessage::PublishIntent {
                intent_hash: [3; 32],
                intent_data: vec![4; 400],
            },
            PeerMessage::RevocationGossip {
                token_id: "tok-123".to_string(),
                signature: vec![0xaa; 64],
            },
            PeerMessage::PublishCheckpoint {
                height: 42,
                checkpoint_data: vec![0xbb; 100_000], // large, goes to LARGE_BUCKET
            },
        ];

        for msg in &messages {
            let raw = msg.encode_raw();
            let padded = super::pad_message(&raw);
            assert!(
                padded.len() == super::SMALL_BUCKET || padded.len() == super::LARGE_BUCKET,
                "Message padded to unexpected size: {} (expected {} or {})",
                padded.len(),
                super::SMALL_BUCKET,
                super::LARGE_BUCKET,
            );
            // Verify roundtrip
            let recovered = super::unpad_message(&padded).unwrap();
            let decoded = PeerMessage::decode_raw(recovered).unwrap();
            assert_eq!(&decoded, msg);
        }
    }
}
