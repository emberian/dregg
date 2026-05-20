//! Macaroon token backend.
//!
//! Wraps the `pyana_macaroon` crate to implement [`AuthToken`].
//! Macaroons use HMAC-SHA256 symmetric key chaining — fast (~0.5μs verify)
//! but requires the root secret key for verification.

use pyana_macaroon::Macaroon;
use zeroize::Zeroizing;

use crate::error::TokenError;
use crate::format::TokenFormat;
use crate::traits::{Attenuation, AuthRequest, AuthToken, TokenClearance};

/// A Macaroon-backed authorization token.
///
/// Wraps `pyana_macaroon::Macaroon` with the root key needed for verification.
pub struct MacaroonToken {
  /// The inner macaroon token.
  inner: Macaroon,
  /// Root key for verification (HMAC-SHA256). Zeroized on drop.
  root_key: Zeroizing<[u8; 32]>,
  /// Discharge macaroons for third-party caveats.
  discharges: Vec<Macaroon>,
}

impl std::fmt::Debug for MacaroonToken {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("MacaroonToken")
      .field("location", &self.inner.location)
      .field("caveat_count", &self.inner.caveats.len())
      .field("discharges", &self.discharges.len())
      .finish()
  }
}

impl MacaroonToken {
  /// Create a new macaroon token with root key and optional discharges.
  pub fn new(inner: Macaroon, root_key: [u8; 32], discharges: Vec<Macaroon>) -> Self {
    Self {
      inner,
      root_key: Zeroizing::new(root_key),
      discharges,
    }
  }

  /// Mint a new root macaroon with the given key ID and location.
  pub fn mint(root_key: [u8; 32], kid: &[u8], location: &str) -> Self {
    let inner = Macaroon::new(&root_key, kid.to_vec(), location.to_string());
    Self {
      inner,
      root_key: Zeroizing::new(root_key),
      discharges: Vec::new(),
    }
  }

  /// Deserialize a macaroon token from its `em2_` encoded form.
  pub fn from_encoded(encoded: &str, root_key: [u8; 32]) -> Result<Self, TokenError> {
    let inner = Macaroon::decode(encoded).map_err(|e| TokenError::Encoding(e.to_string()))?;
    Ok(Self {
      inner,
      root_key: Zeroizing::new(root_key),
      discharges: Vec::new(),
    })
  }

  /// Deserialize a macaroon token with pre-bound discharge macaroons.
  ///
  /// Each entry in `discharge_bytes` is the serialized bytes of a discharge
  /// macaroon (as returned by `Macaroon::serialize()`).
  pub fn from_encoded_with_discharges(
    encoded: &str,
    root_key: [u8; 32],
    discharge_bytes: &[Vec<u8>],
  ) -> Result<Self, TokenError> {
    let inner = Macaroon::decode(encoded).map_err(|e| TokenError::Encoding(e.to_string()))?;
    let mut discharges = Vec::with_capacity(discharge_bytes.len());
    for (i, d) in discharge_bytes.iter().enumerate() {
      let dm = Macaroon::deserialize(d)
        .map_err(|e| TokenError::Encoding(format!("discharge[{}]: {}", i, e)))?;
      discharges.push(dm);
    }
    Ok(Self {
      inner,
      root_key: Zeroizing::new(root_key),
      discharges,
    })
  }

  /// Add a discharge macaroon.
  pub fn add_discharge(&mut self, discharge: Macaroon) {
    self.discharges.push(discharge);
  }

  /// Extract the key ID (nonce.kid) from an encoded macaroon without verifying HMAC.
  ///
  /// This allows key lookup before verification: decode → extract kid →
  /// find matching root key → verify.
  pub fn extract_key_id(encoded: &str) -> Result<Vec<u8>, TokenError> {
    let mac = Macaroon::decode(encoded).map_err(|e| TokenError::Encoding(e.to_string()))?;
    Ok(mac.nonce.kid.clone())
  }

  /// Access the inner macaroon.
  pub fn inner(&self) -> &Macaroon {
    &self.inner
  }

  /// Access discharges.
  pub fn discharges(&self) -> &[Macaroon] {
    &self.discharges
  }
}

impl AuthToken for MacaroonToken {
  fn format(&self) -> TokenFormat {
    TokenFormat::Macaroon
  }

  fn verify(&self, request: &AuthRequest) -> Result<TokenClearance, TokenError> {
    // 1. Validate HMAC chain (proves authenticity + integrity)
    let cleared = self
      .inner
      .verify(&*self.root_key, &self.discharges)
      .map_err(|e| TokenError::VerificationFailed(e.to_string()))?;

    // 2. Check authorization via Datalog (canonical semantics).
    //    The Datalog evaluator is the sole ground truth for authorization.
    //    Both trusted (local eval) and trustless (STARK proof) modes use
    //    the same semantics.
    #[cfg(feature = "datalog")]
    {
      crate::datalog_verify::verify_token_datalog_full(&cleared, request)
    }
    #[cfg(not(feature = "datalog"))]
    {
      // Fallback: imperative verification when datalog feature is disabled.
      #[allow(deprecated)]
      let result = crate::pyana_caveats::verify_caveats(&cleared, request)?;
      Ok(TokenClearance {
        matched_policy: Some("hmac_chain_valid".into()),
        capabilities: result.capabilities,
        format: TokenFormat::Macaroon,
        expires_at: result.expires_at,
        subject: result.subject,
      })
    }
  }

  fn attenuate(&self, restrictions: &Attenuation) -> Result<Box<dyn AuthToken>, TokenError> {
    let wire_caveats = crate::pyana_caveats::attenuation_to_wire_caveats(restrictions);
    if wire_caveats.is_empty() {
      return Err(TokenError::Malformed(
        "no restrictions specified for attenuation".into(),
      ));
    }

    let mut new_mac = self.inner.clone();
    for wc in wire_caveats {
      new_mac.add_first_party_wire(wc);
    }

    Ok(Box::new(MacaroonToken {
      inner: new_mac,
      root_key: Zeroizing::new(*self.root_key),
      discharges: self.discharges.clone(),
    }))
  }

  fn to_bytes(&self) -> Result<Vec<u8>, TokenError> {
    self
      .inner
      .serialize()
      .map_err(|e| TokenError::Encoding(e.to_string()))
  }

  fn to_encoded(&self) -> Result<String, TokenError> {
    self
      .inner
      .encode()
      .map_err(|e| TokenError::Encoding(e.to_string()))
  }

  fn is_attenuable(&self) -> bool {
    true // Macaroons are always attenuable
  }

  fn seal(&self) -> Result<Box<dyn AuthToken>, TokenError> {
    // Macaroons don't have a sealing concept — they're already
    // tamper-proof via HMAC. Return a clone.
    Ok(Box::new(MacaroonToken {
      inner: self.inner.clone(),
      root_key: Zeroizing::new(*self.root_key),
      discharges: self.discharges.clone(),
    }))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn test_root_key() -> [u8; 32] {
    let mut key = [0u8; 32];
    getrandom::fill(&mut key).unwrap();
    key
  }

  #[test]
  fn test_mint_attenuate_verify() {
    let key = test_root_key();
    let token = MacaroonToken::mint(key, b"test-kid", "pyana.dev");

    // Root token verifies with default request
    let clearance = token.verify(&AuthRequest::default()).unwrap();
    assert_eq!(clearance.format, TokenFormat::Macaroon);

    // Attenuated token still verifies (HMAC chain is valid)
    let restricted = token
      .attenuate(&Attenuation {
        apps: vec![("app".into(), "r".into())],
        ..Default::default()
      })
      .unwrap();
    let clearance2 = restricted.verify(&AuthRequest::default()).unwrap();
    assert_eq!(clearance2.format, TokenFormat::Macaroon);
  }

  #[test]
  fn test_encode_decode_roundtrip() {
    let key = test_root_key();
    let token = MacaroonToken::mint(key, b"test-kid", "pyana.dev");
    let encoded = token.to_encoded().unwrap();
    assert!(encoded.starts_with("em2_"));

    let decoded = MacaroonToken::from_encoded(&encoded, key).unwrap();
    assert_eq!(decoded.inner.location, token.inner.location);
  }

  #[test]
  fn test_wrong_key_fails() {
    let key1 = test_root_key();
    let key2 = test_root_key();
    let token = MacaroonToken::mint(key1, b"kid", "loc");
    let encoded = token.to_encoded().unwrap();
    let decoded = MacaroonToken::from_encoded(&encoded, key2).unwrap();

    let request = AuthRequest::default();
    assert!(decoded.verify(&request).is_err());
  }

}
