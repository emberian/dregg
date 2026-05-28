//! Cross-federation receipt citation.
//!
//! A cell in federation F2 can cite a *specific* receipt produced in federation
//! F1 by binding to that receipt's hash through a
//! [`UnilateralAttestation::Custom`] entry. The attestation preimage is
//! domain-separated and binds the citing cell to the cited federation's
//! receipt, so a forged attestation minted against a different federation F1'
//! cannot be substituted.
//!
//! Preimage:
//! ```text
//! blake3("dregg-cross-fed-receipt-cite-v1"
//!        || citing_cell_id
//!        || source_federation_id
//!        || cited_receipt_hash)
//! ```
//!
//! This is the canonical shared implementation (promoted from the
//! `silver_vision_multi_fed_graph_e2e` test, task #123) so producers and
//! verifiers across the workspace agree byte-for-byte.

use dregg_cell::{CellId, UnilateralAttestation, UnilateralAttestationKind};

/// Domain tag identifying a cross-federation receipt citation among
/// `UnilateralAttestationKind::Custom` entries. Stable wire constant.
pub const CROSS_FED_RECEIPT_CITE_KIND_TAG: u32 = 0x0001;

/// Domain-separation label for the citation preimage. Stable wire constant.
const CROSS_FED_RECEIPT_CITE_DOMAIN: &[u8] = b"dregg-cross-fed-receipt-cite-v1";

/// Build the canonical cross-federation receipt-citation attestation binding
/// `citing_cell_id` to `cited_receipt_hash` produced under `source_federation_id`.
pub fn cross_fed_receipt_cite(
    citing_cell_id: &CellId,
    source_federation_id: &[u8; 32],
    cited_receipt_hash: &[u8; 32],
) -> UnilateralAttestation {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CROSS_FED_RECEIPT_CITE_DOMAIN);
    hasher.update(citing_cell_id.as_bytes());
    hasher.update(source_federation_id);
    hasher.update(cited_receipt_hash);
    UnilateralAttestation {
        kind: UnilateralAttestationKind::Custom {
            kind_tag: CROSS_FED_RECEIPT_CITE_KIND_TAG,
        },
        attestation_data: *hasher.finalize().as_bytes(),
    }
}

/// Verify that `attestation` is a valid cross-fed receipt cite for the
/// `(citing_cell_id, source_federation_id, cited_receipt_hash)` triple.
///
/// Returns `false` for any other attestation kind/tag, or if the bound data
/// does not match the recomputed preimage.
pub fn verify_cross_fed_citation(
    attestation: &UnilateralAttestation,
    citing_cell_id: &CellId,
    source_federation_id: &[u8; 32],
    cited_receipt_hash: &[u8; 32],
) -> bool {
    match &attestation.kind {
        UnilateralAttestationKind::Custom { kind_tag }
            if *kind_tag == CROSS_FED_RECEIPT_CITE_KIND_TAG => {}
        _ => return false,
    }
    let expected = cross_fed_receipt_cite(citing_cell_id, source_federation_id, cited_receipt_hash);
    attestation.attestation_data == expected.attestation_data
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId([b; 32])
    }

    #[test]
    fn roundtrip_accepts_matching_triple() {
        let citing = cid(1);
        let fed = [7u8; 32];
        let rh = [9u8; 32];
        let att = cross_fed_receipt_cite(&citing, &fed, &rh);
        assert!(verify_cross_fed_citation(&att, &citing, &fed, &rh));
    }

    #[test]
    fn rejects_wrong_source_federation() {
        let citing = cid(1);
        let rh = [9u8; 32];
        let att = cross_fed_receipt_cite(&citing, &[7u8; 32], &rh);
        // A different (forged) source federation must not verify.
        assert!(!verify_cross_fed_citation(&att, &citing, &[8u8; 32], &rh));
    }

    #[test]
    fn rejects_wrong_citing_cell_and_receipt() {
        let fed = [7u8; 32];
        let att = cross_fed_receipt_cite(&cid(1), &fed, &[9u8; 32]);
        assert!(!verify_cross_fed_citation(&att, &cid(2), &fed, &[9u8; 32]));
        assert!(!verify_cross_fed_citation(&att, &cid(1), &fed, &[10u8; 32]));
    }

    #[test]
    fn rejects_non_custom_kind() {
        let citing = cid(1);
        let fed = [7u8; 32];
        let rh = [9u8; 32];
        let mut att = cross_fed_receipt_cite(&citing, &fed, &rh);
        att.kind = UnilateralAttestationKind::Custom { kind_tag: 0xDEAD };
        assert!(!verify_cross_fed_citation(&att, &citing, &fed, &rh));
    }
}
