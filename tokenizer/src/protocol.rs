//! Protocol messages for the tokenizer daemon IPC.
//!
//! Uses postcard (length-prefixed) for wire encoding, consistent with `pyana-wire`.
//! Frame format: `[4-byte LE payload length][postcard-encoded message]`

use serde::{Deserialize, Serialize};

/// Maximum payload size: 1 MiB (secrets should be small).
pub const MAX_PAYLOAD_SIZE: u32 = 1024 * 1024;

/// Frame header size.
pub const HEADER_SIZE: usize = 4;

/// Request from client to daemon.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Request {
    /// Encrypt plaintext with the daemon's current public key.
    Seal { plaintext: Vec<u8> },

    /// Decrypt a sealed secret using the daemon's private key(s).
    Unseal { sealed: Vec<u8> },

    /// Get the current (newest) public key.
    GetPublicKey,

    /// Rotate: generate a new keypair, return the new public key.
    /// Old keys are retained for decryption.
    Rotate,

    /// Graceful shutdown request.
    Shutdown,
}

/// Response from daemon to client.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Response {
    /// Successful seal: contains the sealed bytes.
    Sealed { data: Vec<u8> },

    /// Successful unseal: contains the plaintext.
    Unsealed { plaintext: Vec<u8> },

    /// Public key response.
    PublicKey { key: [u8; 32] },

    /// Rotation completed: new public key.
    Rotated { new_public_key: [u8; 32] },

    /// Shutdown acknowledged.
    ShutdownAck,

    /// Error response.
    Error { message: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_seal_roundtrip() {
        let req = Request::Seal {
            plaintext: b"my-secret".to_vec(),
        };
        let encoded = postcard::to_allocvec(&req).unwrap();
        let decoded: Request = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(req, decoded);
    }

    #[test]
    fn request_unseal_roundtrip() {
        let req = Request::Unseal {
            sealed: vec![0xAA; 100],
        };
        let encoded = postcard::to_allocvec(&req).unwrap();
        let decoded: Request = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(req, decoded);
    }

    #[test]
    fn request_get_public_key_roundtrip() {
        let req = Request::GetPublicKey;
        let encoded = postcard::to_allocvec(&req).unwrap();
        let decoded: Request = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(req, decoded);
    }

    #[test]
    fn request_rotate_roundtrip() {
        let req = Request::Rotate;
        let encoded = postcard::to_allocvec(&req).unwrap();
        let decoded: Request = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(req, decoded);
    }

    #[test]
    fn request_shutdown_roundtrip() {
        let req = Request::Shutdown;
        let encoded = postcard::to_allocvec(&req).unwrap();
        let decoded: Request = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(req, decoded);
    }

    #[test]
    fn response_sealed_roundtrip() {
        let resp = Response::Sealed {
            data: vec![0xBB; 80],
        };
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn response_unsealed_roundtrip() {
        let resp = Response::Unsealed {
            plaintext: b"recovered-secret".to_vec(),
        };
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn response_public_key_roundtrip() {
        let resp = Response::PublicKey { key: [0x42; 32] };
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn response_error_roundtrip() {
        let resp = Response::Error {
            message: "decryption failed".to_string(),
        };
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn response_rotated_roundtrip() {
        let resp = Response::Rotated {
            new_public_key: [0xFF; 32],
        };
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn response_shutdown_ack_roundtrip() {
        let resp = Response::ShutdownAck;
        let encoded = postcard::to_allocvec(&resp).unwrap();
        let decoded: Response = postcard::from_bytes(&encoded).unwrap();
        assert_eq!(resp, decoded);
    }

    #[test]
    fn all_request_variants_distinct() {
        // Ensure different request variants encode to different bytes.
        let variants: Vec<Request> = vec![
            Request::Seal {
                plaintext: b"x".to_vec(),
            },
            Request::Unseal {
                sealed: b"y".to_vec(),
            },
            Request::GetPublicKey,
            Request::Rotate,
            Request::Shutdown,
        ];

        let encodings: Vec<Vec<u8>> = variants
            .iter()
            .map(|v| postcard::to_allocvec(v).unwrap())
            .collect();

        for i in 0..encodings.len() {
            for j in (i + 1)..encodings.len() {
                assert_ne!(
                    encodings[i], encodings[j],
                    "variants {} and {} encode identically",
                    i, j
                );
            }
        }
    }

    #[test]
    fn payload_size_constants() {
        assert_eq!(HEADER_SIZE, 4);
        assert_eq!(MAX_PAYLOAD_SIZE, 1024 * 1024);
    }
}
