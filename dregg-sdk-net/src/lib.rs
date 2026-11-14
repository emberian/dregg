//! # dregg-sdk-net
//!
//! The **networked layer** of the dregg agent SDK. The offline core —
//! `AgentCipherclerk`, its receipt/turn surface, token attenuation, proof
//! generation, the wire-free `DreggEngine` — lives in [`dregg_sdk`] and is
//! wasm-buildable (no tokio/reqwest/dregg-wire/dregg-captp). This crate adds the
//! parts that need a transport or the distributed-core crates:
//!
//! - **CapTP** capability sharing, enlivening, offline handoff, and pipelining
//!   ([`captp_client`], [`channels`], [`names`]);
//! - **federation registration** and **custom-program deployment** (the
//!   [`NetClerk`] HTTP convenience methods);
//! - the **hosted-mailbox crank** ([`mailbox`]);
//! - the **silo client**, **discharge gateway client**, and **private (PIR)
//!   intent discovery** ([`client`], [`discharge`], [`discovery`]);
//! - the **receipt event stream** ([`events`]);
//! - the **remote runtime** twin ([`remote`]);
//! - the no-I/O **wire codec** ([`WireCodec`]) over [`dregg_sdk::embed::DreggEngine`].
//!
//! ## The state-lift: `NetClerk`
//!
//! The core [`AgentCipherclerk`](dregg_sdk::AgentCipherclerk) no longer carries a
//! CapTP client. The CapTP client state lives here, in the [`NetClerk`] wrapper
//! (`{ clerk, captp }`). The former inherent CapTP convenience methods
//! (`share_capability` / `accept_capability` / `delegate_offline` / …) are
//! methods on `NetClerk`; the former federation HTTP methods
//! (`register_with_federation` / `deregister_from_federation` / `deploy_program`)
//! are `NetClerk` methods over `&self.clerk` and a node URL; private intent
//! discovery is the free function [`discovery::discover_intents_privately`].

// THE VERIFIED PQ CORES, for THIS crate's lib-test binary, at PROCESS START.
//
// `dregg-sdk-net` never calls `dregg-pq` itself — it reaches ML-DSA through the identity
// derivation in `dregg_turn::pq` / `dregg_cell_crypto`, and those crates install a core only
// under their OWN `cfg(test)`, which is not set when they are compiled as dependencies here.
// With nothing installed `dregg-pq` refuses with an uncatchable `process::abort()`, and all
// six `faithful_spend::tests` — the whole bounded-page spend protocol — died as bare SIGABRTs.
//
// Process-start rather than a call at a gateway: the reach is transitive and arrives from
// several directions, so a hand-audited call list would be coverage by audit. This runs before
// libtest starts, so no test can beat it and `--test-threads` cannot change the outcome.
// `#[cfg(test)]`, so the shipped crate stays archive-free — `sdk/src/runtime.rs` installs the
// same cores when an `AgentRuntime` is built.
#[cfg(test)]
dregg_pq_testkit::install_at_process_start!();

pub mod captp_client;
pub mod channels;
pub mod client;
pub mod client_sign;
pub mod deos_server;
pub mod discharge;
pub mod discovery;
pub mod events;
pub mod faithful_spend;
pub mod mailbox;
pub mod names;
pub mod node_world_sink;
pub mod remote;

/// A REAL-executor in-process test node (`TestNode`), exported so OTHER crates'
/// tests drive a genuine node — not a stub. Gated behind `test-support`; carries
/// no `deos-js` dependency (executor + HTTP only).
#[cfg(feature = "test-support")]
pub mod test_support;

mod wire_codec;
pub mod embed {
    //! The networked face of [`dregg_sdk::embed`]: the [`WireCodec`].
    pub use crate::wire_codec::WireCodec;
    pub use dregg_wire::message::WireMessage;
}

// ── CapTP capability sharing + pipelining ────────────────────────────────────
pub use captp_client::{CapTpClient, CapTpConfig, EventualRef, LiveRef};

// ── Petname resolution ───────────────────────────────────────────────────────
pub use names::{
    CipherclerkNames, EdgeNameEntry, NameError, NameProvenance, NameResolver, PetnameDb,
    PetnameEntry, ProposedNameEntry, ResolvedName, WhoisResult,
};

// ── Hosted-mailbox crank (ORGANS §2) ─────────────────────────────────────────
pub use mailbox::{
    CrankDisposition, CrankOutcome, CrankReport, CustodyReceipt, DeliveredMessage, MailboxCrank,
    MailboxTransport, MailboxTurnIntent, RefusalReason, RelayHttpTransport, seal_intent,
};

// ── The deos-host private-server client (discover + fire) ────────────────────
pub use deos_server::{
    DiscoveredAffordance, FireOutcome, ServerDiscovery, discover_server_affordances,
    fire_affordance,
};

// ── The client-side NodeWorldSink (inhabit a remote box's node over HTTP) ─────
#[cfg(feature = "world-sink")]
pub use node_world_sink::NodeWorldSink;
pub use node_world_sink::{CoordinationClass, NodeHttpClient};

// ── Silo client / discharge / discovery / events ─────────────────────────────
pub use client::{PresentationResult, RevocationStatus, SiloClient};
pub use discharge::{authorize_with_discharges, extract_third_party_tickets, obtain_discharge};
pub use discovery::{
    PirTransport, PrivateDiscoveryClient, discover_intents_privately, discover_matching_intents,
};
pub use events::{NodeEvents, ReceiptFilter, ReceiptStream};
pub use faithful_spend::{
    FaithfulNoteMirror, FaithfulNoteMirrorAnchor, FaithfulNoteMirrorHead, FaithfulNoteMirrorRecord,
    FaithfulNoteMirrorRequest, FaithfulNoteMirrorResponse, FaithfulNoteMirrorTrust,
    FaithfulNullifierMirrorRecord, FaithfulPriorSpend, FaithfulPriorSpendContext,
    FaithfulSpendProverContext, LocalFaithfulNoteWitness,
};
pub use remote::RemoteRuntime;

// ── The wire codec over the wire-free `DreggEngine` ──────────────────────────
pub use wire_codec::WireCodec;

// ── CapTP protocol types re-exported from `dregg-captp` for convenience ───────
pub use dregg_captp::handoff::HandoffCertificate;
pub use dregg_captp::pipeline::PipelinedAction;
pub use dregg_captp::uri::DreggUri;
pub use dregg_captp::{FederationId, GroupId};

use dregg_cell::AuthRequired;
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::error::SdkError;
use dregg_types::CellId;

/// The networked clerk: an [`AgentCipherclerk`] paired with a [`CapTpClient`].
///
/// The CapTP client state used to hang off the core cipherclerk; it was lifted
/// off so the core crate stays net-free and wasm-buildable. Construct a
/// `NetClerk` to use the CapTP convenience methods (capability sharing,
/// enlivening, offline handoff) and the federation HTTP methods.
pub struct NetClerk {
    /// The offline core identity (keys, tokens, receipt chain, sovereign state).
    pub clerk: AgentCipherclerk,
    /// The CapTP client (sturdy refs, imports/exports GC, handoff, pipelining).
    pub captp: CapTpClient,
}

impl NetClerk {
    /// Pair an existing cipherclerk with a CapTP client.
    pub fn new(clerk: AgentCipherclerk, captp: CapTpClient) -> Self {
        Self { clerk, captp }
    }

    /// Pair a cipherclerk with a CapTP client built from `config`.
    pub fn with_config(clerk: AgentCipherclerk, config: CapTpConfig) -> Self {
        Self {
            clerk,
            captp: CapTpClient::new(config),
        }
    }

    /// Borrow the underlying cipherclerk.
    pub fn cipherclerk(&self) -> &AgentCipherclerk {
        &self.clerk
    }

    /// Mutably borrow the underlying cipherclerk.
    pub fn cipherclerk_mut(&mut self) -> &mut AgentCipherclerk {
        &mut self.clerk
    }

    /// Borrow the CapTP client.
    pub fn captp_client(&self) -> &CapTpClient {
        &self.captp
    }

    /// Mutably borrow the CapTP client.
    pub fn captp_client_mut(&mut self) -> &mut CapTpClient {
        &mut self.captp
    }

    // ── CapTP convenience (formerly inherent on AgentCipherclerk) ────────────

    /// Share a cell as a `dregg://` URI (sturdy reference).
    ///
    /// The returned URI can be shared with any agent; they can enliven it to
    /// obtain a live reference to the cell.
    pub fn share_capability(&mut self, cell_id: CellId) -> Result<DreggUri, SdkError> {
        Ok(self
            .captp
            .export_sturdy_ref(cell_id, AuthRequired::Signature, None))
    }

    /// Accept (enliven) a `dregg://` URI, returning a live reference.
    ///
    /// The returned [`LiveRef`] tracks the import in the GC manager and sends a
    /// DropRef message when dropped.
    pub fn accept_capability(&mut self, uri: &str) -> Result<LiveRef, SdkError> {
        self.captp.enliven_uri(uri, AuthRequired::Signature)
    }

    /// Create a handoff certificate for offline delegation of a cell to a
    /// recipient.
    ///
    /// The returned certificate can travel out-of-band (QR code, email, BLE).
    /// The recipient presents it to the target federation to obtain access.
    pub fn delegate_offline(
        &mut self,
        cell_id: CellId,
        recipient_pk: [u8; 32],
    ) -> Result<HandoffCertificate, SdkError> {
        let signing_key = self.clerk.gossip_signing_key();
        Ok(self.captp.create_handoff(
            &signing_key,
            cell_id,
            recipient_pk,
            AuthRequired::Signature,
            None,
            None,
        ))
    }

    // ── Federation registration / program deployment (HTTP) ──────────────────

    /// Register this clerk's sovereign cell with a federation node (ephemeral).
    ///
    /// The federation stores only the state commitment and TTL metadata; the
    /// registration expires after `ttl_blocks` of inactivity.
    pub async fn register_with_federation(
        &self,
        node_url: &str,
        ttl_blocks: u64,
    ) -> Result<(), SdkError> {
        let cell_id_bytes = self.clerk.public_key().0;
        let commitment = self.clerk.current_state_commitment().unwrap_or([0u8; 32]);

        let mut message = Vec::with_capacity(64);
        message.extend_from_slice(&cell_id_bytes);
        message.extend_from_slice(&commitment);
        let sig = dregg_types::sign(&self.clerk.gossip_signing_key(), &message);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "commitment": hex_encode_bytes(&commitment),
            "ttl_blocks": ttl_blocks,
            "signature": hex_encode_bytes(&sig.0),
        });

        let url = format!("{}/cells/register", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("federation register request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation register returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse register response: {e}")))?;

        if result.get("registered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected registration: {error}"
            )))
        }
    }

    /// Deregister this clerk's sovereign cell from the federation.
    pub async fn deregister_from_federation(&self, node_url: &str) -> Result<(), SdkError> {
        let cell_id_bytes = self.clerk.public_key().0;
        let sig = dregg_types::sign(&self.clerk.gossip_signing_key(), &cell_id_bytes);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "signature": hex_encode_bytes(&sig.0),
        });

        let url = format!("{}/cells/deregister", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp =
            client.post(&url).json(&body).send().await.map_err(|e| {
                SdkError::Wire(format!("federation deregister request failed: {e}"))
            })?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation deregister returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deregister response: {e}")))?;

        if result.get("deregistered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected deregistration: {error}"
            )))
        }
    }

    /// Deploy a custom cell program to the federation.
    ///
    /// Serializes the `CircuitDescriptor` via postcard and submits it to the
    /// node's `/programs/deploy` endpoint. On success, returns the 32-byte VK
    /// hash that identifies the program in the registry.
    pub async fn deploy_program(
        &self,
        node_url: &str,
        descriptor: &dregg_dsl_runtime::CircuitDescriptor,
        version: u32,
    ) -> Result<[u8; 32], SdkError> {
        let serialized = postcard::to_allocvec(descriptor)
            .map_err(|e| SdkError::Wire(format!("failed to serialize descriptor: {e}")))?;

        let body = serde_json::json!({
            "descriptor_bytes": hex_encode_bytes(&serialized),
            "version": version,
        });

        let url = format!("{}/programs/deploy", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("program deploy request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "program deploy returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deploy response: {e}")))?;

        if result.get("deployed").and_then(|v| v.as_bool()) == Some(true) {
            let vk_hex = result
                .get("vk_hash")
                .and_then(|v| v.as_str())
                .ok_or_else(|| SdkError::Wire("deploy response missing vk_hash".into()))?;
            let vk_bytes = hex_decode_bytes(vk_hex)
                .map_err(|_| SdkError::Wire("invalid vk_hash hex in deploy response".into()))?;
            if vk_bytes.len() != 32 {
                return Err(SdkError::Wire("vk_hash is not 32 bytes".into()));
            }
            let mut vk = [0u8; 32];
            vk.copy_from_slice(&vk_bytes);
            Ok(vk)
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected program deployment: {error}"
            )))
        }
    }
}

/// Encode bytes to a lowercase hex string (used by the federation HTTP methods).
fn hex_encode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a hex string into bytes.
fn hex_decode_bytes(s: &str) -> Result<Vec<u8>, ()> {
    if !s.len().is_multiple_of(2) {
        return Err(());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| ()))
        .collect()
}
