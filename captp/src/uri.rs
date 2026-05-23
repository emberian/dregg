//! Pyana URI parsing and formatting.
//!
//! A `pyana://` URI represents a durable capability reference:
//!
//! ```text
//! pyana://<federation-id-base58>/<cell-id-base58>/<swiss-number-base58>
//! ```
//!
//! The federation ID identifies which federation to connect to, the cell ID
//! identifies the target object, and the swiss number is the bearer secret
//! that proves the holder was granted access.

use serde::{Deserialize, Serialize};
use std::fmt;

/// Errors that can occur when parsing a `pyana://` URI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UriError {
    /// The URI does not start with the `pyana://` scheme.
    InvalidScheme,
    /// The URI does not have exactly three path segments.
    WrongSegmentCount { found: usize },
    /// A base58 segment could not be decoded.
    Base58Decode {
        segment: &'static str,
        message: String,
    },
    /// A decoded segment is not exactly 32 bytes.
    InvalidLength {
        segment: &'static str,
        expected: usize,
        found: usize,
    },
}

impl fmt::Display for UriError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UriError::InvalidScheme => write!(f, "URI must start with 'pyana://'"),
            UriError::WrongSegmentCount { found } => {
                write!(f, "expected 3 path segments, found {found}")
            }
            UriError::Base58Decode { segment, message } => {
                write!(f, "base58 decode failed for {segment}: {message}")
            }
            UriError::InvalidLength {
                segment,
                expected,
                found,
            } => {
                write!(f, "{segment}: expected {expected} bytes, got {found}")
            }
        }
    }
}

impl std::error::Error for UriError {}

/// A `pyana://` URI representing a durable capability reference.
///
/// Contains enough information to enliven (reconnect to) a capability:
/// - `federation_id`: identifies the federation (or reference group) hosting the target
/// - `cell_id`: identifies the target cell/object
/// - `swiss`: the bearer secret proving authorization
///
/// # Unified Lace Note
///
/// In the unified blocklace model, `federation_id` is semantically a `GroupId`
/// (the reference group that orders/hosts the target cell). The field name is
/// preserved for wire-format stability.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PyanaUri {
    /// The group (federation) hosting the target. Equivalent to `GroupId` in the unified model.
    pub federation_id: [u8; 32],
    pub cell_id: [u8; 32],
    pub swiss: [u8; 32],
}

impl PyanaUri {
    /// Parse a `pyana://` URI string into its components.
    ///
    /// # Format
    ///
    /// ```text
    /// pyana://<federation-id-base58>/<cell-id-base58>/<swiss-number-base58>
    /// ```
    ///
    /// Each segment must decode to exactly 32 bytes.
    pub fn parse(s: &str) -> Result<Self, UriError> {
        let rest = s.strip_prefix("pyana://").ok_or(UriError::InvalidScheme)?;

        let segments: Vec<&str> = rest.split('/').collect();
        if segments.len() != 3 {
            return Err(UriError::WrongSegmentCount {
                found: segments.len(),
            });
        }

        let federation_id = decode_segment(segments[0], "federation_id")?;
        let cell_id = decode_segment(segments[1], "cell_id")?;
        let swiss = decode_segment(segments[2], "swiss")?;

        Ok(PyanaUri {
            federation_id,
            cell_id,
            swiss,
        })
    }

    /// Format this URI as a string.
    pub fn to_uri_string(&self) -> String {
        format!(
            "pyana://{}/{}/{}",
            bs58::encode(&self.federation_id).into_string(),
            bs58::encode(&self.cell_id).into_string(),
            bs58::encode(&self.swiss).into_string()
        )
    }
}

impl fmt::Display for PyanaUri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_uri_string())
    }
}

impl fmt::Debug for PyanaUri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PyanaUri({})", self.to_uri_string())
    }
}

/// Decode a base58 segment into a 32-byte array.
fn decode_segment(s: &str, name: &'static str) -> Result<[u8; 32], UriError> {
    let bytes = bs58::decode(s)
        .into_vec()
        .map_err(|e| UriError::Base58Decode {
            segment: name,
            message: e.to_string(),
        })?;

    if bytes.len() != 32 {
        return Err(UriError::InvalidLength {
            segment: name,
            expected: 32,
            found: bytes.len(),
        });
    }

    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);
    Ok(arr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let uri = PyanaUri {
            federation_id: [0xaa; 32],
            cell_id: [0xbb; 32],
            swiss: [0xcc; 32],
        };

        let s = uri.to_uri_string();
        assert!(s.starts_with("pyana://"));

        let parsed = PyanaUri::parse(&s).unwrap();
        assert_eq!(parsed, uri);
    }

    #[test]
    fn parse_invalid_scheme() {
        let err = PyanaUri::parse("http://foo/bar/baz").unwrap_err();
        assert_eq!(err, UriError::InvalidScheme);
    }

    #[test]
    fn parse_wrong_segments() {
        let err = PyanaUri::parse("pyana://foo/bar").unwrap_err();
        assert!(matches!(err, UriError::WrongSegmentCount { found: 2 }));
    }

    #[test]
    fn parse_invalid_base58() {
        // '0', 'O', 'I', 'l' are not valid base58 characters
        let err = PyanaUri::parse("pyana://0invalid/bar/baz").unwrap_err();
        assert!(matches!(err, UriError::Base58Decode { .. }));
    }

    #[test]
    fn parse_wrong_length() {
        // Encode a 16-byte value — too short
        let short = bs58::encode(&[0xaa; 16]).into_string();
        let valid = bs58::encode(&[0xbb; 32]).into_string();
        let s = format!("pyana://{short}/{valid}/{valid}");
        let err = PyanaUri::parse(&s).unwrap_err();
        assert!(matches!(
            err,
            UriError::InvalidLength {
                segment: "federation_id",
                expected: 32,
                found: 16,
            }
        ));
    }

    #[test]
    fn display_impl() {
        let uri = PyanaUri {
            federation_id: [1; 32],
            cell_id: [2; 32],
            swiss: [3; 32],
        };
        let displayed = format!("{uri}");
        assert!(displayed.starts_with("pyana://"));
        assert_eq!(displayed, uri.to_uri_string());
    }
}
