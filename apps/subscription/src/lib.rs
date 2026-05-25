//! # pyana-subscription
//!
//! Content subscription service built on pyana primitives:
//!
//! - **Store-and-forward delivery**: when a creator publishes, content is
//!   encrypted-per-subscriber and pushed into a shared
//!   [`pyana_storage::inbox::CapInbox`] as `InboxMessage::Encrypted`. Offline
//!   subscribers retrieve the ciphertext on reconnect and decrypt locally.
//!   The inbox sees only opaque bytes — no creator content leaks through it.
//! - **Delegated auto-debit**: subscribers issue a signed [`DelegatedToken`]
//!   that authorizes the payment executor to debit up to `max_per_epoch` of
//!   a specific `asset_id`. Envelopes are verified by the SDK's full
//!   [`AgentCipherclerk::receive_signed_delegation`] path under
//!   [`DelegationAuthority::TrustedKey`].
//! - **Credential-gated tiers**: premium tiers require a signed
//!   `DelegatedToken` issued by a known "premium issuer". Free tiers do not.
//! - **Real balance state**: debits move numbers in a `BalanceLedger`. No
//!   accounting is faked; per-epoch limits are enforced cumulatively.
//!
//! # Module overview
//!
//! - [`crypto`]: subscriber-bound encryption (X25519 + ChaCha20-Poly1305).
//! - [`creator`]: content creators and their tier catalog.
//! - [`subscriber`]: subscriber registry and signed-delegation handling.
//! - [`payments`]: balance ledger + `BatchExecutor` for batched debits.
//! - [`delivery`]: publish-time encryption and inbox push.
//! - [`server`]: HTTP API.
//!
//! [`DelegatedToken`]: pyana_sdk::DelegatedToken
//! [`AgentCipherclerk::receive_signed_delegation`]: pyana_sdk::AgentCipherclerk::receive_signed_delegation
//! [`DelegationAuthority::TrustedKey`]: pyana_sdk::DelegationAuthority::TrustedKey

pub mod creator;
pub mod crypto;
pub mod delivery;
pub mod payments;
pub mod server;
pub mod subscriber;

#[cfg(test)]
mod tests;
