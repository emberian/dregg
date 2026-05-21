//! Pyana-specific peer messages exchanged over iroh connections.
//!
//! All messages are serialized with postcard (a compact no_std-friendly format)
//! and framed with a 4-byte big-endian length prefix over QUIC streams.

use serde::{Deserialize, Serialize};

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
}
