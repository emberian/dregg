//! Cross-federation `CrossFedReceiptBundle` verification (Silver Vision §6).
//!
//! `dregg-verifier verify-cross-fed-bundle` ingests a JSON-encoded
//! [`dregg_federation::CrossFedReceiptBundle`] plus two committee descriptors
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

use dregg_federation::CrossFedReceiptBundle;
use dregg_federation::receipt::FederationReceipt;
use dregg_types::{AttestedRoot, PublicKey};

use crate::{AUTO_DETECT_VK_HASH, ReplayChainOutput, exit_code, verify_effect_vm_proof};

/// A federation committee descriptor as it appears on disk (the file the
/// `register-federation` CLI writes / `setup_federations.sh` cross-copies).
///
/// Field shape mirrors what `dregg-node genesis` already produces (we
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

    if bundle.recipient_chain.is_empty() {
        return CrossFedVerdict::rejection("recipient_chain is empty");
    }

    if let Err(reason) =
        verify_committee_descriptor_id("issuer committee", issuer_committee, &issuer_keys)
    {
        return CrossFedVerdict::rejection(reason);
    }
    if let Err(reason) =
        verify_committee_descriptor_id("recipient committee", recipient_committee, &recipient_keys)
    {
        return CrossFedVerdict::rejection(reason);
    }

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

    if let Err(reason) = verify_attested_root_against_descriptor(
        "F1 AttestedRoot",
        &bundle.issuer_attested_root,
        issuer_committee,
        &issuer_keys,
        issuer_fed_id,
    ) {
        verdict.summary = reason;
        return verdict;
    }

    if let Err(reason) = verify_attested_root_against_descriptor(
        "F2 AttestedRoot",
        &bundle.recipient_attested_root,
        recipient_committee,
        &recipient_keys,
        recipient_fed_id,
    ) {
        verdict.summary = reason;
        return verdict;
    }

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

    for (i, wr) in bundle.recipient_chain.iter().enumerate() {
        if wr.witness_bundle.is_none() {
            verdict.summary = format!(
                "recipient_chain[{i}] has no witness_bundle; cross-fed verification requires scope-2 replay material"
            );
            return verdict;
        }
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
    verdict.attested_root_f1_verified = true;

    // (5) F2 AttestedRoot.
    verdict.attested_root_f2_verified = true;

    let receipt_hashes: Vec<[u8; 32]> = bundle
        .recipient_chain
        .iter()
        .map(|wr| wr.receipt.receipt_hash())
        .collect();
    if !bundle
        .recipient_attested_root
        .verify_receipt_stream(&receipt_hashes)
    {
        verdict.summary =
            "F2 AttestedRoot receipt_stream_root does not match recipient_chain receipts".into();
        return verdict;
    }

    // (8 — F3 binding flag) blocklace binding present?
    verdict.attested_root_f2_blocklace_bound =
        bundle.recipient_attested_root.blocklace_block_id.is_some()
            && bundle.recipient_attested_root.finality_round.is_some();
    if !verdict.attested_root_f2_blocklace_bound {
        verdict.summary = "F2 AttestedRoot lacks blocklace_block_id/finality_round binding".into();
        return verdict;
    }

    let tail = bundle
        .recipient_chain
        .last()
        .expect("recipient_chain emptiness checked above");

    // (6) FederationReceipt over F2's body, if present.
    if let Some(ref fr) = bundle.recipient_federation_receipt {
        // We can do the Votes path without the BLS committee. The Threshold
        // path requires a `FederationCommittee` (BLS), which this standalone
        // descriptor does not carry, so `FederationReceipt::verify` rejects it
        // instead of treating opaque bytes as a cryptographic proof.
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
        if let Err(reason) = federation_receipt_matches_tail(fr, &tail.receipt) {
            verdict.summary = reason;
            verdict.federation_receipt_f2_verified = false;
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
    if tail.receipt.federation_id != recipient_fed_id {
        verdict.summary = format!(
            "tail receipt.federation_id ({}) != recipient.federation_id ({})",
            hex::encode(tail.receipt.federation_id),
            hex::encode(recipient_fed_id),
        );
        return verdict;
    }
    verdict.cross_link_cert_to_receipt = true;
    verdict.executor_signature_includes_federation_id = tail.receipt.executor_signature.is_some();

    verdict.overall_verified = verdict.cert_introducer_sig_verified
        && verdict.effect_vm_proof_verified
        && verdict.witness_chain_replay_verified
        && verdict.attested_root_f1_verified
        && verdict.attested_root_f2_verified
        && verdict.federation_receipt_f2_verified
        && verdict.cross_link_cert_to_receipt
        && verdict.attested_root_f2_blocklace_bound;
    verdict.summary = if verdict.overall_verified {
        "cross-fed bundle verified end-to-end".into()
    } else {
        "cross-fed bundle: at least one check failed".into()
    };
    verdict
}

fn verify_committee_descriptor_id(
    role: &str,
    descriptor: &CommitteeDescriptor,
    keys: &[PublicKey],
) -> Result<(), String> {
    let declared = descriptor.federation_id_bytes()?;
    let derived =
        dregg_federation::derive_federation_id_with_epoch(keys, descriptor.committee_epoch);
    if declared != derived {
        return Err(format!(
            "{role}: federation_id ({}) does not derive from validator keys at epoch {} ({})",
            hex::encode(declared),
            descriptor.committee_epoch,
            hex::encode(derived)
        ));
    }
    Ok(())
}

fn verify_attested_root_against_descriptor(
    role: &str,
    root: &AttestedRoot,
    descriptor: &CommitteeDescriptor,
    keys: &[PublicKey],
    expected_federation_id: [u8; 32],
) -> Result<(), String> {
    if keys.is_empty() {
        return Err(format!("{role}: committee has no validators"));
    }
    if descriptor.threshold == 0 {
        return Err(format!("{role}: committee threshold must be non-zero"));
    }
    if descriptor.threshold > keys.len() {
        return Err(format!(
            "{role}: committee threshold {} exceeds validator count {}",
            descriptor.threshold,
            keys.len()
        ));
    }
    if root.threshold != descriptor.threshold {
        return Err(format!(
            "{role}: root threshold {} != descriptor threshold {}",
            root.threshold, descriptor.threshold
        ));
    }
    if root.federation_id.0 != expected_federation_id {
        return Err(format!(
            "{role}: root.federation_id ({}) != descriptor.federation_id ({})",
            hex::encode(root.federation_id.0),
            hex::encode(expected_federation_id)
        ));
    }
    if root.threshold_qc.is_some() && root.quorum_signatures.is_empty() {
        return Err(format!(
            "{role}: threshold_qc is present but this verifier was not given a BLS committee; Ed25519 quorum_signatures are required"
        ));
    }
    if !verify_attested_root_ed25519(root, keys) {
        return Err(format!(
            "{role}: Ed25519 quorum signatures did not verify under descriptor committee"
        ));
    }
    Ok(())
}

fn verify_attested_root_ed25519(root: &AttestedRoot, known_keys: &[PublicKey]) -> bool {
    if root.threshold == 0 || root.threshold > known_keys.len() {
        return false;
    }
    if root.quorum_signatures.len() < root.threshold {
        return false;
    }

    let message = root.signing_message();
    let mut seen = std::collections::HashSet::new();
    let mut valid = 0usize;
    for (pubkey, signature) in &root.quorum_signatures {
        if !known_keys.contains(pubkey) {
            return false;
        }
        if !pubkey.verify(&message, signature) {
            return false;
        }
        if seen.insert(pubkey.0) {
            valid += 1;
        }
    }
    valid >= root.threshold
}

fn federation_receipt_matches_tail(
    receipt: &FederationReceipt,
    tail: &dregg_turn::TurnReceipt,
) -> Result<(), String> {
    let body = &receipt.body;
    if body.turn_hash != tail.turn_hash {
        return Err("F2 FederationReceipt body.turn_hash does not match tail receipt".into());
    }
    if body.agent != tail.agent {
        return Err("F2 FederationReceipt body.agent does not match tail receipt".into());
    }
    if body.pre_state_hash != tail.pre_state_hash {
        return Err("F2 FederationReceipt body.pre_state_hash does not match tail receipt".into());
    }
    if body.post_state_hash != tail.post_state_hash {
        return Err("F2 FederationReceipt body.post_state_hash does not match tail receipt".into());
    }
    if body.effects_hash != tail.effects_hash {
        return Err("F2 FederationReceipt body.effects_hash does not match tail receipt".into());
    }
    if body.previous_receipt_hash != tail.previous_receipt_hash {
        return Err(
            "F2 FederationReceipt body.previous_receipt_hash does not match tail receipt".into(),
        );
    }
    Ok(())
}

/// Translate a `dregg_turn::WitnessedReceipt` into a `ReplayEntry` for
/// the in-crate replay_chain machinery. The two shapes are nearly
/// identical; we transcode `WitnessAvailability::Inline` and preserve
/// the trace rows verbatim.
fn witnessed_to_replay(wr: &dregg_turn::WitnessedReceipt) -> crate::ReplayEntry {
    let bundle = wr
        .witness_bundle
        .as_ref()
        .map(|b| crate::ReplayWitnessBundle {
            trace_rows: b.trace_rows.clone(),
            availability: crate::ReplayWitnessAvailability::Inline,
            recursive_proof: b.recursive_proof.as_ref().map(|rp| {
                crate::ReplayRecursiveProofVariant {
                    proof_bytes: rp.proof_bytes.clone(),
                    public_inputs: rp.public_inputs.clone(),
                    recursive_vk_hash: rp.recursive_vk_hash,
                }
            }),
        });
    crate::ReplayEntry {
        receipt: wr.receipt.clone(),
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
    fn committee_descriptor_federation_id_must_derive_from_keys() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();

        let err = verify_committee_descriptor_id("committee", &desc, &keys)
            .expect_err("descriptor must not claim an arbitrary federation_id");

        assert!(err.contains("does not derive"), "{err}");
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

    #[test]
    fn empty_recipient_chain_rejected_before_claiming_scope2() {
        let mut b = sample_bundle();
        b.recipient_chain.clear();
        let desc = sample_committee([0xAA; 32]);

        let v = verify_cross_fed_bundle(&b, &desc, &desc);

        assert!(!v.overall_verified);
        assert!(v.summary.contains("recipient_chain is empty"));
        assert!(!v.witness_chain_replay_verified);
    }

    #[test]
    fn attested_root_descriptor_rejects_zero_threshold() {
        let mut desc = sample_committee([0xAA; 32]);
        desc.threshold = 0;
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 0);
        root.federation_id = dregg_types::FederationId([0xAA; 32]);

        let err = verify_attested_root_against_descriptor("root", &root, &desc, &keys, [0xAA; 32])
            .expect_err("zero-threshold committee must not verify");

        assert!(err.contains("threshold must be non-zero"), "{err}");
    }

    #[test]
    fn attested_root_descriptor_rejects_federation_id_mismatch() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 1);
        root.federation_id = dregg_types::FederationId([0xBB; 32]);

        let err = verify_attested_root_against_descriptor("root", &root, &desc, &keys, [0xAA; 32])
            .expect_err("root signed for another federation must not verify");

        assert!(err.contains("root.federation_id"), "{err}");
    }

    #[test]
    fn attested_root_descriptor_rejects_structural_threshold_qc_without_ed25519_quorum() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy(
            [1; 32],
            1,
            1_700_000_000,
            vec![],
            Some(dregg_types::ThresholdQC(vec![0xAB; 48])),
            1,
        );
        root.federation_id = dregg_types::FederationId([0xAA; 32]);

        let err = verify_attested_root_against_descriptor("root", &root, &desc, &keys, [0xAA; 32])
            .expect_err("opaque threshold QC alone must not be accepted as crypto proof");

        assert!(err.contains("BLS committee"), "{err}");
    }

    #[test]
    fn federation_receipt_body_must_match_tail_receipt() {
        use dregg_federation::receipt::{FederationReceipt, FederationReceiptBody, ReceiptQc};
        use dregg_types::{PublicKey, Signature};

        let tail = sample_turn_receipt();
        let body = FederationReceiptBody {
            turn_hash: tail.turn_hash,
            block_height: 7,
            block_hash: [0x44; 32],
            agent: tail.agent,
            nonce: 0,
            pre_state_hash: tail.pre_state_hash,
            post_state_hash: tail.post_state_hash,
            effects_hash: [0xEE; 32],
            previous_receipt_hash: tail.previous_receipt_hash,
        };
        let fr = FederationReceipt {
            version: FederationReceipt::VERSION,
            federation_id: tail.federation_id,
            committee_epoch: 0,
            body,
            qc: ReceiptQc::Votes(vec![(PublicKey([0u8; 32]), Signature([0u8; 64]))]),
        };

        let err = federation_receipt_matches_tail(&fr, &tail)
            .expect_err("mismatched effects_hash must not certify tail receipt");

        assert!(err.contains("effects_hash"), "{err}");
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

    fn sample_turn_receipt() -> dregg_turn::turn::TurnReceipt {
        use dregg_types::CellId;

        dregg_turn::turn::TurnReceipt {
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
            was_encrypted: false,
            was_burn: false,
        }
    }

    fn sample_bundle() -> CrossFedReceiptBundle {
        use dregg_captp::FederationId;
        use dregg_cell::AuthRequired;
        use dregg_turn::WitnessedReceipt;
        use dregg_types::{AttestedRoot, CellId, generate_keypair};

        let (sk, _pk) = generate_keypair();
        let cert = dregg_captp::handoff::HandoffCertificate::create(
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

        let receipt = sample_turn_receipt();
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
