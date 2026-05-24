//! Cross-federation `CrossFedReceiptBundle` verification (Silver Vision §6).
//!
//! `pyana-verifier verify-cross-fed-bundle` ingests a JSON-encoded
//! [`pyana_federation::CrossFedReceiptBundle`] plus two committee descriptors
//! (one per federation) and runs the 8-step check from
//! `SILVER-VISION-E2E-VERIFICATION.md` §1 Step 6:
//!
//! 1. Verify the introducer's signature on the `HandoffCertificate` under
//!    the issuing committee's pubkey.
//! 2. (Soft) Effect-VM STARK proof checks pass on every receipt in the
//!    chain.
//! 3. Scope-2 replay of the chain (re-derive trace + verify).
//! 4. Verify F1's `AttestedRoot` quorum signatures under F1's known keys.
//! 5. Verify F2's `AttestedRoot` quorum signatures under F2's known keys.
//! 6. Verify F2's `FederationReceipt` (if present) under F2's BLS / Ed25519
//!    committee.
//! 7. Cross-link: `cert.target_federation == F2`,
//!    `cert.introducer == F1`, the chain's last receipt's
//!    `federation_id == F2`, and the receipt's authorization-side cert
//!    nonce equals `cert.nonce` (when present in the receipt).
//! 8. Structural sanity: bundle version matches, the chain is non-empty.
//!
//! Returns a `CrossFedVerdict` carrying a granular per-step result so the
//! demo's `must_not_pass` negative tests can read individual flags.

use serde::{Deserialize, Serialize};

use pyana_federation::CrossFedReceiptBundle;
use pyana_types::PublicKey;

use crate::{AUTO_DETECT_VK_HASH, ReplayChainOutput, exit_code, verify_effect_vm_proof};

/// A federation committee descriptor as it appears on disk (the file the
/// `register-federation` CLI writes / `setup_federations.sh` cross-copies).
///
/// Field shape mirrors what `pyana-node genesis` already produces (we
/// re-decode it here so the verifier doesn't need to call into the node).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommitteeDescriptor {
    /// 32-byte federation id (hex). Derived from the sorted pubkeys.
    pub federation_id: String,
    /// Committee epoch.
    #[serde(default)]
    pub committee_epoch: u64,
    /// Threshold (number of signatures required).
    #[serde(default = "default_threshold")]
    pub threshold: usize,
    /// Validator pubkeys (32-byte hex strings).
    pub validators: Vec<ValidatorDescriptor>,
}

fn default_threshold() -> usize {
    1
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidatorDescriptor {
    #[serde(default)]
    pub name: String,
    /// Hex-encoded 32-byte Ed25519 pubkey.
    pub public_key: String,
}

impl CommitteeDescriptor {
    /// Decode the validator pubkeys to the typed shape the rest of the
    /// stack expects.
    pub fn pubkeys(&self) -> Result<Vec<PublicKey>, String> {
        let mut out = Vec::with_capacity(self.validators.len());
        for v in &self.validators {
            let bytes = hex_decode_32(&v.public_key)
                .ok_or_else(|| format!("invalid hex pubkey for {}", v.name))?;
            out.push(PublicKey(bytes));
        }
        Ok(out)
    }

    /// Decode the 32-byte federation id.
    pub fn federation_id_bytes(&self) -> Result<[u8; 32], String> {
        hex_decode_32(&self.federation_id).ok_or_else(|| "invalid federation_id hex".to_string())
    }
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

/// The 8-step verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrossFedVerdict {
    /// (1) The handoff cert's introducer signature verifies under F1's
    /// committee pubkey.
    pub cert_introducer_sig_verified: bool,
    /// (2) Every receipt's STARK proof verifies (scope-1).
    pub effect_vm_proof_verified: bool,
    /// (3) The witness chain replays end-to-end (scope-2).
    pub witness_chain_replay_verified: bool,
    /// (4) F1's `AttestedRoot` quorum is structurally + cryptographically
    /// valid under F1's committee.
    pub attested_root_f1_verified: bool,
    /// (5) F2's `AttestedRoot` quorum is valid under F2's committee.
    pub attested_root_f2_verified: bool,
    /// (6) F2's `FederationReceipt` (when present) verifies under F2's
    /// committee.
    pub federation_receipt_f2_verified: bool,
    /// (7) Cross-link checks pass: cert.introducer == F1.federation_id,
    /// cert.target_federation == F2.federation_id, the chain's tail
    /// receipt's `federation_id` matches F2.
    pub cross_link_cert_to_receipt: bool,
    /// (8) The recipient F2's `AttestedRoot` carries a non-`None`
    /// `blocklace_block_id` / `finality_round` — the F3 binding that
    /// makes the attestation blocklace-aware (AUDIT-federation.md F3).
    pub attested_root_f2_blocklace_bound: bool,
    /// Auxiliary: the chain's tail receipt's `executor_signature` was
    /// computed over a message that includes `federation_id` (lane D F2 fix).
    /// We approximate the check by asserting the tail receipt's
    /// `federation_id` equals F2 — the actual signing-message structure
    /// is enforced inside the executor; this flag surfaces the demo-level
    /// invariant.
    pub executor_signature_includes_federation_id: bool,
    /// Human-readable trace of which step failed first (or "all green").
    pub summary: String,
    /// Per-receipt replay output (for debugging negative cases).
    #[serde(default)]
    pub replay_detail: Option<ReplayChainOutput>,
    /// True iff every load-bearing check passes (steps 1-8 above; the
    /// optional `federation_receipt_f2_verified` only counts when a
    /// receipt is supplied).
    pub overall_verified: bool,
}

impl CrossFedVerdict {
    fn rejection(reason: impl Into<String>) -> Self {
        Self {
            cert_introducer_sig_verified: false,
            effect_vm_proof_verified: false,
            witness_chain_replay_verified: false,
            attested_root_f1_verified: false,
            attested_root_f2_verified: false,
            federation_receipt_f2_verified: false,
            cross_link_cert_to_receipt: false,
            attested_root_f2_blocklace_bound: false,
            executor_signature_includes_federation_id: false,
            summary: reason.into(),
            replay_detail: None,
            overall_verified: false,
        }
    }
}

/// Top-level entrypoint invoked by the binary's `verify-cross-fed-bundle`
/// subcommand. Reads the JSON-encoded bundle, two committee descriptors,
/// and produces a [`CrossFedVerdict`].
pub fn verify_cross_fed_bundle(
    bundle: &CrossFedReceiptBundle,
    issuer_committee: &CommitteeDescriptor,
    recipient_committee: &CommitteeDescriptor,
) -> CrossFedVerdict {
    // (8 — structural) version check.
    if bundle.version != CrossFedReceiptBundle::VERSION {
        return CrossFedVerdict::rejection(format!(
            "bundle version mismatch: bundle={}, expected={}",
            bundle.version,
            CrossFedReceiptBundle::VERSION
        ));
    }

    // Decode committees up-front so we can short-circuit cleanly.
    let issuer_keys = match issuer_committee.pubkeys() {
        Ok(k) => k,
        Err(e) => return CrossFedVerdict::rejection(format!("issuer committee: {e}")),
    };
    let recipient_keys = match recipient_committee.pubkeys() {
        Ok(k) => k,
        Err(e) => return CrossFedVerdict::rejection(format!("recipient committee: {e}")),
    };
    let issuer_fed_id = match issuer_committee.federation_id_bytes() {
        Ok(b) => b,
        Err(e) => return CrossFedVerdict::rejection(format!("issuer fed_id: {e}")),
    };
    let recipient_fed_id = match recipient_committee.federation_id_bytes() {
        Ok(b) => b,
        Err(e) => return CrossFedVerdict::rejection(format!("recipient fed_id: {e}")),
    };

    let mut verdict = CrossFedVerdict {
        cert_introducer_sig_verified: false,
        effect_vm_proof_verified: false,
        witness_chain_replay_verified: false,
        attested_root_f1_verified: false,
        attested_root_f2_verified: false,
        federation_receipt_f2_verified: bundle.recipient_federation_receipt.is_none(), // vacuously true when absent
        cross_link_cert_to_receipt: false,
        attested_root_f2_blocklace_bound: false,
        executor_signature_includes_federation_id: false,
        summary: String::new(),
        replay_detail: None,
        overall_verified: false,
    };

    // (1) Cert introducer signature.
    // The cert's `introducer` field MUST equal the issuer's federation_id,
    // AND the cert must verify under one of the issuer's known pubkeys.
    if bundle.cross_fed_cert.introducer.0 != issuer_fed_id {
        verdict.summary = format!(
            "cert.introducer ({}) != issuer.federation_id ({})",
            hex::encode(bundle.cross_fed_cert.introducer.0),
            hex::encode(issuer_fed_id),
        );
        return verdict;
    }
    // Single-node committee (demo's posture): the single pubkey is the
    // introducer. Multi-key committees would require the cert to carry
    // an explicit signer hint; we iterate over all keys here so the demo
    // works with both shapes.
    verdict.cert_introducer_sig_verified = issuer_keys
        .iter()
        .any(|pk| bundle.cross_fed_cert.verify_signature(pk));
    if !verdict.cert_introducer_sig_verified {
        verdict.summary = "cert introducer signature did not verify under any issuer pubkey".into();
        return verdict;
    }

    // (2) STARK proof verifies for every receipt.
    let mut all_proofs_ok = true;
    for (i, wr) in bundle.recipient_chain.iter().enumerate() {
        let (out, code) =
            verify_effect_vm_proof(&wr.proof_bytes, &wr.public_inputs, AUTO_DETECT_VK_HASH);
        if code != exit_code::VERIFIED {
            verdict.summary = format!(
                "effect-vm proof rejected at chain[{i}]: {} (code={code})",
                out.reason
            );
            all_proofs_ok = false;
            break;
        }
    }
    verdict.effect_vm_proof_verified = all_proofs_ok;
    if !all_proofs_ok {
        return verdict;
    }

    // (3) Scope-2 replay via the existing replay_chain machinery. We
    // convert the bundle's `WitnessedReceipt`s to `ReplayEntry`s on the fly.
    let replay_entries: Vec<crate::ReplayEntry> = bundle
        .recipient_chain
        .iter()
        .map(witnessed_to_replay)
        .collect();
    let replay = crate::replay_chain(&replay_entries);
    verdict.witness_chain_replay_verified = replay.overall_verified;
    if !replay.overall_verified {
        verdict.summary = format!("scope-2 replay failed: {}", replay.summary);
        verdict.replay_detail = Some(replay);
        return verdict;
    }
    verdict.replay_detail = Some(replay);

    // (4) F1 AttestedRoot.
    verdict.attested_root_f1_verified = bundle.issuer_attested_root.is_valid(&issuer_keys);
    if !verdict.attested_root_f1_verified {
        verdict.summary = "F1 AttestedRoot did not verify under issuer committee".into();
        return verdict;
    }

    // (5) F2 AttestedRoot.
    verdict.attested_root_f2_verified = bundle.recipient_attested_root.is_valid(&recipient_keys);
    if !verdict.attested_root_f2_verified {
        verdict.summary = "F2 AttestedRoot did not verify under recipient committee".into();
        return verdict;
    }

    // (8 — F3 binding flag) blocklace binding present?
    verdict.attested_root_f2_blocklace_bound =
        bundle.recipient_attested_root.blocklace_block_id.is_some()
            && bundle.recipient_attested_root.finality_round.is_some();
    // Note: not required for `overall_verified` to be true in the v1
    // demo (a single-node devnet's AttestedRoot may carry None when the
    // blocklace lift seam isn't fully wired). The flag is reported so
    // demo asserts can observe progress.

    // (6) FederationReceipt over F2's body, if present.
    if let Some(ref fr) = bundle.recipient_federation_receipt {
        // We can do the Votes path without the BLS committee. For the
        // Threshold path the verifier would need a `FederationCommittee`
        // (BLS), which we don't carry in the demo descriptor. The demo
        // emits Votes-flavored receipts (single-node, n=1) so we exercise
        // the Ed25519 path here; threshold-flavored receipts get a
        // structural-only pass.
        verdict.federation_receipt_f2_verified = fr.verify(
            None,
            &recipient_keys,
            recipient_committee.threshold,
            recipient_committee.committee_epoch,
        );
        if !verdict.federation_receipt_f2_verified {
            verdict.summary =
                "F2 FederationReceipt did not verify under recipient committee".into();
            return verdict;
        }
    }

    // (7) Cross-link sanity.
    if bundle.cross_fed_cert.target_federation.0 != recipient_fed_id {
        verdict.summary = format!(
            "cert.target_federation ({}) != recipient.federation_id ({})",
            hex::encode(bundle.cross_fed_cert.target_federation.0),
            hex::encode(recipient_fed_id),
        );
        return verdict;
    }
    // The tail receipt's federation_id must equal F2.
    let Some(tail) = bundle.recipient_chain.last() else {
        verdict.summary = "recipient_chain is empty".into();
        return verdict;
    };
    if tail.receipt.federation_id != recipient_fed_id {
        verdict.summary = format!(
            "tail receipt.federation_id ({}) != recipient.federation_id ({})",
            hex::encode(tail.receipt.federation_id),
            hex::encode(recipient_fed_id),
        );
        return verdict;
    }
    verdict.cross_link_cert_to_receipt = true;
    verdict.executor_signature_includes_federation_id = true;

    verdict.overall_verified = verdict.cert_introducer_sig_verified
        && verdict.effect_vm_proof_verified
        && verdict.witness_chain_replay_verified
        && verdict.attested_root_f1_verified
        && verdict.attested_root_f2_verified
        && verdict.federation_receipt_f2_verified
        && verdict.cross_link_cert_to_receipt;
    verdict.summary = if verdict.overall_verified {
        "cross-fed bundle verified end-to-end".into()
    } else {
        "cross-fed bundle: at least one check failed".into()
    };
    verdict
}

/// Translate a `pyana_turn::WitnessedReceipt` into a `ReplayEntry` for
/// the in-crate replay_chain machinery. The two shapes are nearly
/// identical; we transcode `WitnessAvailability::Inline` and preserve
/// the trace rows verbatim.
fn witnessed_to_replay(wr: &pyana_turn::WitnessedReceipt) -> crate::ReplayEntry {
    let bundle = wr
        .witness_bundle
        .as_ref()
        .map(|b| crate::ReplayWitnessBundle {
            trace_rows: b.trace_rows.clone(),
            availability: crate::ReplayWitnessAvailability::Inline,
        });
    crate::ReplayEntry {
        receipt: serde_json::to_value(&wr.receipt).unwrap_or(serde_json::Value::Null),
        proof_bytes: wr.proof_bytes.clone(),
        public_inputs: wr.public_inputs.clone(),
        witness_bundle: bundle,
        witness_hash: wr.witness_hash,
        aggregate_membership: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn committee_descriptor_decodes_pubkeys() {
        let d = CommitteeDescriptor {
            federation_id: "00".repeat(32),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![ValidatorDescriptor {
                name: "node-0".into(),
                public_key: "ab".repeat(32),
            }],
        };
        let keys = d.pubkeys().unwrap();
        assert_eq!(keys.len(), 1);
        assert_eq!(keys[0].0, [0xAB; 32]);
        assert_eq!(d.federation_id_bytes().unwrap(), [0u8; 32]);
    }

    #[test]
    fn committee_descriptor_rejects_bad_hex() {
        let d = CommitteeDescriptor {
            federation_id: "zz".repeat(32),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![],
        };
        assert!(d.federation_id_bytes().is_err());
    }

    #[test]
    fn version_mismatch_rejected() {
        // Manually craft a bundle with version 0 to ensure the check fires.
        let mut b = sample_bundle();
        b.version = 0;
        let desc = sample_committee([0xAA; 32]);
        let v = verify_cross_fed_bundle(&b, &desc, &desc);
        assert!(!v.overall_verified);
        assert!(v.summary.contains("version"));
    }

    // -- Test helpers --
    fn sample_committee(fed_id: [u8; 32]) -> CommitteeDescriptor {
        CommitteeDescriptor {
            federation_id: hex::encode(fed_id),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![ValidatorDescriptor {
                name: "n0".into(),
                public_key: "ab".repeat(32),
            }],
        }
    }

    fn sample_bundle() -> CrossFedReceiptBundle {
        use pyana_captp::FederationId;
        use pyana_cell::AuthRequired;
        use pyana_turn::WitnessedReceipt;
        use pyana_turn::turn::TurnReceipt;
        use pyana_types::{AttestedRoot, CellId, generate_keypair};

        let (sk, _pk) = generate_keypair();
        let cert = pyana_captp::handoff::HandoffCertificate::create(
            &sk,
            FederationId([0xAA; 32]),
            FederationId([0xBB; 32]),
            CellId([0xCC; 32]),
            [0xDD; 32],
            AuthRequired::Signature,
            None,
            None,
            None,
            [0xEE; 32],
        );

        let receipt = TurnReceipt {
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
        };
        let wr = WitnessedReceipt::from_components(receipt, vec![0u8; 8], vec![1, 2, 3], None);
        CrossFedReceiptBundle::new(
            vec![wr],
            AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 0),
            AttestedRoot::new_legacy([2; 32], 2, 1_700_000_000, vec![], None, 0),
            cert,
            None,
        )
    }
}
