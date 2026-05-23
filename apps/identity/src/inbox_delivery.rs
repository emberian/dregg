//! Store-and-forward credential delivery via [`CapInbox`].
//!
//! When an issuer issues a credential to a holder who is offline, the signed
//! [`DelegatedToken`] (serialized as bytes) is pushed into a [`CapInbox`] as an
//! `InboxMessage::Capability`. The holder reads messages on reconnect and the
//! signature can be re-verified from the deserialized `DelegatedToken`.
//!
//! # Security
//!
//! - Uses the **mandatory-signature v2 envelope**: every `DelegatedToken` in the
//!   inbox must carry a valid `delegator_signature` over the full envelope hash.
//! - Callers must supply a `DelegationAuthority` policy when verifying the token on
//!   receipt so that the public key in `delegator_public_key` is trusted
//!   out-of-band (e.g., `DelegationAuthority::TrustedKey(issuer_pk)`).
//! - The inbox anti-spam `min_deposit` is set to 0 in tests; production deployments
//!   should raise it to deter junk deliveries.
//!
//! # Framework primitives used
//!
//! - `AppServer::with_inbox(path, endpoint)` — mounts the endpoint.
//! - `InboxEndpoint::new(capacity, min_deposit)` — wraps [`CapInbox`].

use pyana_app_framework::inbox_endpoint::InboxEndpoint;

/// Build a credential-delivery inbox endpoint.
///
/// * `capacity_per_user` — maximum queued messages before the inbox is full.
/// * `min_deposit` — minimum deposit (anti-spam); use 0 for tests.
pub fn credential_inbox_endpoint(capacity_per_user: usize, min_deposit: u64) -> InboxEndpoint {
    InboxEndpoint::new(capacity_per_user, min_deposit)
}
