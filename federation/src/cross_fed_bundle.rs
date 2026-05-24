//! `CrossFedReceiptBundle` — the Silver-Vision cross-federation evidence artifact.
//!
//! See `SILVER-VISION-E2E-VERIFICATION.md` §3.1 and §5.2.4. A bundle carries
//! everything an independent verifier needs to reconstruct the
//! "Alice on F1 → Bob on F2 via CapTP bearer cap" story:
//!
//! 1. `recipient_chain` — the `Vec<WitnessedReceipt>` Bob's wallet exports
//!    (typically one entry: the F2-side `Effect::Transfer` exercise).
//! 2. `issuer_attested_root` — F1's `AttestedRoot` at the height covering
//!    the cert's issuance turn. Lets the verifier check "F1's committee
//!    attests this height/root, and the cert was minted by an introducer
//!    keyed to F1's committee."
//! 3. `recipient_attested_root` — F2's `AttestedRoot` at the height
//!    covering Bob's exercise turn. Binds the receipt chain to F2's
//!    finalized state.
//! 4. `cross_fed_cert` — the `HandoffCertificate` Alice signed naming
//!    `target_federation = F2`. The cross-link between the two
//!    federations' chains.
//! 5. `recipient_federation_receipt` — optional `FederationReceipt`
//!    (BLS-aggregate over Bob's R2). The cheap "trust F2's committee"
//!    path; the verifier can early-exit on a valid BLS QC if it
//!    chooses, or fall through to scope-2 replay of every
//!    `WitnessedReceipt`.
//!
//! The bundle is `Serialize + Deserialize` so it round-trips through
//! JSON / postcard / on-disk artifact formats without losing any
//! verification material.

use pyana_captp::handoff::HandoffCertificate;
use pyana_turn::WitnessedReceipt;
use pyana_types::AttestedRoot;
use serde::{Deserialize, Serialize};

use crate::receipt::FederationReceipt;

/// The Silver-Vision cross-federation evidence bundle.
///
/// Constructed by the recipient's wallet (Bob's, in the canonical demo)
/// at chain-export time. Consumed by `pyana-verifier verify-cross-fed-bundle`
/// (or any compatible standalone verifier) to issue an end-to-end verdict.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrossFedReceiptBundle {
    /// Bundle format version. Bump on incompatible shape changes.
    pub version: u32,
    /// The recipient federation's per-turn witnessed-receipt chain. For
    /// the canonical Silver demo this is a one-element vector covering
    /// Bob's `Effect::Transfer` exercise turn. Production / multi-turn
    /// variants extend this naturally.
    pub recipient_chain: Vec<WitnessedReceipt>,
    /// The issuing federation's attested root at the height covering the
    /// cert's issuance turn. The verifier checks its quorum signatures
    /// against `issuer_committee` (provided out-of-band, per Step 0.2 of
    /// the demo spec).
    pub issuer_attested_root: AttestedRoot,
    /// The receiving federation's attested root at the height covering
    /// the most recent receipt in `recipient_chain`. Verified against
    /// `recipient_committee`.
    pub recipient_attested_root: AttestedRoot,
    /// The handoff certificate that authorized Bob to exercise the cap.
    /// The verifier checks `cross_fed_cert.introducer == F1`,
    /// `cross_fed_cert.target_federation == F2`, and that
    /// `cross_fed_cert.nonce` cross-links to the receipt's authorization
    /// (when the receipt carries `Authorization::CapTpDelivered`).
    pub cross_fed_cert: HandoffCertificate,
    /// Optional federation-level receipt over the last recipient-chain
    /// receipt. Cheap trust path: a verified BLS QC over the receipt's
    /// `body_hash` lets a caller that already trusts F2's committee
    /// accept the bundle without scope-2 replay.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recipient_federation_receipt: Option<FederationReceipt>,
}

impl CrossFedReceiptBundle {
    /// Current bundle format version.
    pub const VERSION: u32 = 1;

    /// Build a v1 bundle. The caller is responsible for ensuring the
    /// pieces are mutually consistent (chain receipts belong to the
    /// receiving federation, attested roots match their committees,
    /// the cert names the right introducer/target). The verifier
    /// re-checks all of that — this constructor is purely structural.
    pub fn new(
        recipient_chain: Vec<WitnessedReceipt>,
        issuer_attested_root: AttestedRoot,
        recipient_attested_root: AttestedRoot,
        cross_fed_cert: HandoffCertificate,
        recipient_federation_receipt: Option<FederationReceipt>,
    ) -> Self {
        Self {
            version: Self::VERSION,
            recipient_chain,
            issuer_attested_root,
            recipient_attested_root,
            cross_fed_cert,
            recipient_federation_receipt,
        }
    }

    /// Serialize as pretty JSON (the demo's on-disk wire shape).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_captp::FederationId;
    use pyana_cell::AuthRequired;
    use pyana_turn::turn::TurnReceipt;
    use pyana_types::{AttestedRoot, CellId, PublicKey, generate_keypair};

    fn dummy_receipt() -> TurnReceipt {
        TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 42,
            effects_hash: [5u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId::from_bytes([0xAB; 32]),
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
        }
    }

    fn dummy_attested_root(height: u64) -> AttestedRoot {
        AttestedRoot::new_legacy(
            [height as u8; 32],
            height,
            (1_700_000_000 + height as i64) * 1,
            Vec::new(),
            None,
            0,
        )
    }

    fn dummy_cert() -> HandoffCertificate {
        let (sk, _pk) = generate_keypair();
        HandoffCertificate::create(
            &sk,
            FederationId([0xAA; 32]),
            FederationId([0xBB; 32]),
            CellId([0xCC; 32]),
            [0xDD; 32],
            AuthRequired::Signature,
            None,
            Some(1_000_000),
            Some(1),
            [0xEE; 32],
        )
    }

    #[test]
    fn bundle_roundtrips_through_json() {
        let chain = vec![WitnessedReceipt::from_components(
            dummy_receipt(),
            vec![0u8; 8],
            vec![1, 2, 3],
            None,
        )];
        let bundle = CrossFedReceiptBundle::new(
            chain,
            dummy_attested_root(1),
            dummy_attested_root(2),
            dummy_cert(),
            None,
        );
        let j = bundle.to_json().unwrap();
        let back = CrossFedReceiptBundle::from_json(&j).unwrap();
        assert_eq!(back.version, CrossFedReceiptBundle::VERSION);
        assert_eq!(back.recipient_chain.len(), 1);
        assert_eq!(back.issuer_attested_root.height, 1);
        assert_eq!(back.recipient_attested_root.height, 2);
        assert_eq!(back.cross_fed_cert.introducer.0, [0xAA; 32]);
    }

    #[test]
    fn version_constant_is_one() {
        assert_eq!(CrossFedReceiptBundle::VERSION, 1);
    }

    // suppress unused-import warning when running without test-only deps
    #[allow(dead_code)]
    fn _unused(_: PublicKey) {}
}
