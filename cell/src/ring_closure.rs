//! Ring-closure attestation — coequalizer of N pairwise transfers.
//!
//! Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.6 + §5.3 + §9.1.3: γ.2's
//! bilateral binding is the **equalizer** of two cell projections over
//! a shared `transfer_id`. The categorical dual — the **coequalizer**
//! — identifies the outcomes of N parallel transfers under a single
//! "cycle closes" relation. Today the cycle-closure property is
//! implicit (per-cell balance equality in the executor's effect-apply
//! step + call_forest's structural shape); lifting it to a first-class
//! artifact gives apps composable rings.
//!
//! ## Silver Vision vs Golden Vision
//!
//! **Silver (this module):** `closure_proof` is a BLAKE3 keyed
//! commitment over the canonical encoding of the ring (participants
//! in cycle order, transfer_ids in cycle order, per-leg PI digests).
//! Validators check pairwise consistency + cycle closure (no leg
//! orphaned; every participant appears as exactly one sender and one
//! receiver). The witness data carries each participant's bilateral
//! PIs so the verifier can recompute the bilateral binding hashes.
//!
//! **Golden (deferred):** `closure_proof` becomes a STARK over the
//! ring's per-cell PIs — the coequalizer's universal arrow as a single
//! aggregate proof. This module's `RingClosureAttestation` shape is
//! forward-compatible: the `closure_proof: Vec<u8>` carrier is opaque
//! to the verifier dispatch (it routes by a `closure_proof_kind`
//! discriminant), so swapping the Silver commitment for a Golden STARK
//! is a per-variant addition, not a wire format break.
//!
//! ## App drivers
//!
//! - **Orderbook ring fills** (`apps/orderbook/ring_trade.rs`): N
//!   counterparties each provide one good for another in a cycle.
//!   The attestation proves the cycle closes without revealing
//!   individual leg amounts (those ride in the per-leg γ.2 bindings).
//! - **DEX multi-pair settlements**: A→B→C→A cyclical price arb. The
//!   attestation is the audit artifact "this arb cycle netted out."
//! - **Circular intent matching**: matchmaker fuses N intents into a
//!   ring fill; the attestation is the proof the fusion is balanced.
//!
//! ## Composability
//!
//! The coequalizer's universal property — "every other identification
//! of the legs factors through this one" — gives ring attestations a
//! free composition law: two ring attestations over disjoint
//! cycles compose into a multi-ring attestation; a ring attestation
//! plus a bilateral transfer composes when the bilateral participates
//! in the ring's pairwise leg-set.
//!
//! ## Boundary contract
//!
//! - **Cleartext-inside:** ring participants (each sees its own
//!   pairwise PIs + the cycle structure).
//! - **Commitment-inside:** validators (see the `closure_proof`
//!   commitment + canonical ring encoding).
//! - **Acceptance-inside:** post-verification observers (see the
//!   attestation passed validation; learn nothing about leg amounts).
//! - **Out-of-band:** everyone else.

use serde::{Deserialize, Serialize};

use crate::id::CellId;

/// Domain key for the canonical ring encoding hash.
const RING_CLOSURE_CANONICAL_KEY: &str = "pyana-ring-closure-canonical-v1";

/// Domain key for the per-leg PI digest used inside the canonical
/// encoding. Each leg contributes one digest derived from the leg's
/// bilateral γ.2 PIs.
const RING_CLOSURE_LEG_PI_KEY: &str = "pyana-ring-closure-leg-pi-v1";

/// The Silver-Vision proof kind: a 32-byte BLAKE3 keyed commitment.
/// Golden Vision adds a `Stark { ... }` variant that carries STARK
/// proof bytes; the discriminant lets verifiers dispatch on shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClosureProofKind {
    /// Silver — BLAKE3 keyed-derive commitment over the canonical ring
    /// encoding + per-leg PI digests. Cheap to compute, cheap to
    /// verify; provides cycle-closure binding under the random-oracle
    /// model.
    Silver,
}

/// Per-leg bilateral γ.2 PIs the validator needs to verify the ring's
/// pairwise consistency.
///
/// Each leg in the ring corresponds to one bilateral transfer
/// (sender_cell → receiver_cell, transfer_id, amount commitment, etc.).
/// The fields here are the *minimum* a Silver-Vision validator needs
/// to confirm the leg's bilateral binding matches the participant
/// pair's view; the actual γ.2 binding lives in the per-cell
/// `outgoing_transfer_root` / `incoming_transfer_root` accumulators
/// (verified by the cross-cell match loop in the turn executor).
///
/// The Golden-Vision STARK variant will fold this into the AIR
/// constraints; the Silver variant uses these fields directly in the
/// canonical hash.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingLegPi {
    /// Sender cell — must equal `participants[leg_index]`.
    pub sender_cell: CellId,
    /// Receiver cell — must equal
    /// `participants[(leg_index + 1) % N]` (the ring is cyclic).
    pub receiver_cell: CellId,
    /// The canonical γ.2 `transfer_id` for this leg.
    /// `H("pyana-transfer-id-v1", sender, receiver, amount, nonce)`
    /// — must equal `transfer_ids[leg_index]`.
    pub transfer_id: [u8; 32],
    /// Domain-tagged digest of the leg's full PI vector (amount
    /// commitments, value-conservation proof witnesses, …). Silver
    /// callers compute this from their per-leg bilateral PIs; Golden
    /// callers will fold it into a STARK.
    pub pi_digest: [u8; 32],
}

impl RingLegPi {
    /// Compute the canonical leg PI digest from raw bytes — domain-
    /// keyed BLAKE3 so two distinct callers compute the same digest
    /// from the same bytes. `pi_bytes` is the canonical encoding of
    /// the leg's bilateral PI vector (callers ensure the encoding is
    /// deterministic).
    pub fn pi_digest_from_bytes(pi_bytes: &[u8]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(RING_CLOSURE_LEG_PI_KEY);
        hasher.update(&(pi_bytes.len() as u64).to_le_bytes());
        hasher.update(pi_bytes);
        *hasher.finalize().as_bytes()
    }
}

/// First-class attestation that a set of N bilateral transfers forms a
/// closed cycle.
///
/// The categorical role per §3.6/§5.3/§9.1.3: the **coequalizer** of
/// the N pairwise transfers. The cycle's universal-arrow property is
/// what makes ring attestations composable.
///
/// # Cycle ordering convention
///
/// `participants[i]` sends to `participants[(i + 1) % N]` via
/// `transfer_ids[i]`. The ring closes when every participant appears
/// exactly once and the modular indexing is well-defined.
///
/// # Construction
///
/// Callers should use [`RingClosureAttestation::silver`] which derives
/// `closure_proof` from the canonical encoding. Direct field-by-field
/// construction is allowed (the type is `pub` for serde / wire
/// purposes) but [`Self::verify`] enforces well-formedness regardless.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RingClosureAttestation {
    /// Cell ids of the ring participants, in cycle order. The ring
    /// closes when participants[i] sends to participants[(i+1) % N].
    /// `participants.len() == transfer_ids.len() == leg_pis.len()`.
    pub participants: Vec<CellId>,
    /// The bilateral γ.2 `transfer_id` for each leg, in cycle order.
    /// `transfer_ids[i]` binds the leg
    /// `(participants[i] → participants[(i+1) % N])`.
    pub transfer_ids: Vec<[u8; 32]>,
    /// Per-leg bilateral PI summaries; one per leg, cycle order.
    pub leg_pis: Vec<RingLegPi>,
    /// The kind of closure proof this attestation carries.
    pub closure_proof_kind: ClosureProofKind,
    /// The closure proof bytes. For [`ClosureProofKind::Silver`], a
    /// 32-byte BLAKE3 keyed-derive commitment over the canonical
    /// encoding. For Golden (future), STARK proof bytes.
    pub closure_proof: Vec<u8>,
}

/// Errors a ring-closure attestation can surface on construction or
/// verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RingClosureError {
    /// The ring has fewer than 2 participants (a "ring" of one cell
    /// degenerates to a self-transfer, which γ.2 bilateral handles
    /// directly; rings start at N=2 — though typically N≥3).
    DegenerateRing { participants: usize },
    /// `participants`, `transfer_ids`, and `leg_pis` have inconsistent
    /// lengths.
    LengthMismatch {
        participants: usize,
        transfer_ids: usize,
        leg_pis: usize,
    },
    /// A leg's `sender_cell` doesn't match `participants[i]`.
    LegSenderMismatch {
        leg_index: usize,
        expected: CellId,
        actual: CellId,
    },
    /// A leg's `receiver_cell` doesn't match
    /// `participants[(i+1) % N]`.
    LegReceiverMismatch {
        leg_index: usize,
        expected: CellId,
        actual: CellId,
    },
    /// A leg's `transfer_id` field doesn't match `transfer_ids[i]`.
    LegTransferIdMismatch {
        leg_index: usize,
        expected: [u8; 32],
        actual: [u8; 32],
    },
    /// The ring's `participants` list contains a duplicate — every
    /// participant must appear exactly once.
    DuplicateParticipant {
        leg_index: usize,
        cell: CellId,
    },
    /// The closure proof bytes don't match the canonical encoding's
    /// expected commitment.
    ClosureCommitmentMismatch {
        expected: [u8; 32],
        actual: Vec<u8>,
    },
    /// The closure proof bytes have the wrong shape for the declared
    /// `closure_proof_kind`.
    ClosureProofMalformed {
        kind: ClosureProofKind,
        reason: String,
    },
}

impl core::fmt::Display for RingClosureError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::DegenerateRing { participants } => write!(
                f,
                "ring has {participants} participants; rings require ≥ 2"
            ),
            Self::LengthMismatch {
                participants,
                transfer_ids,
                leg_pis,
            } => write!(
                f,
                "ring length mismatch: participants={participants}, transfer_ids={transfer_ids}, leg_pis={leg_pis}"
            ),
            Self::LegSenderMismatch {
                leg_index,
                expected,
                actual,
            } => write!(
                f,
                "leg[{leg_index}] sender mismatch: expected {expected:?}, got {actual:?}"
            ),
            Self::LegReceiverMismatch {
                leg_index,
                expected,
                actual,
            } => write!(
                f,
                "leg[{leg_index}] receiver mismatch: expected {expected:?}, got {actual:?}"
            ),
            Self::LegTransferIdMismatch {
                leg_index,
                expected,
                actual,
            } => write!(
                f,
                "leg[{leg_index}] transfer_id mismatch: expected {expected:02x?}, got {actual:02x?}"
            ),
            Self::DuplicateParticipant { leg_index, cell } => write!(
                f,
                "ring participant {cell:?} appears more than once (at leg index {leg_index}); rings must be simple cycles"
            ),
            Self::ClosureCommitmentMismatch { expected, .. } => write!(
                f,
                "ring closure commitment mismatch: expected {expected:02x?}"
            ),
            Self::ClosureProofMalformed { kind, reason } => {
                write!(f, "closure proof ({kind:?}) malformed: {reason}")
            }
        }
    }
}

impl std::error::Error for RingClosureError {}

impl RingClosureAttestation {
    /// Construct a Silver-Vision attestation: the `closure_proof`
    /// bytes are the canonical BLAKE3 commitment over the ring's
    /// participants, transfer_ids, and per-leg PI digests.
    ///
    /// Validates well-formedness (lengths match, legs reference
    /// `participants` correctly, no duplicate participants). Returns
    /// `Err` if the inputs don't form a consistent ring.
    pub fn silver(
        participants: Vec<CellId>,
        transfer_ids: Vec<[u8; 32]>,
        leg_pis: Vec<RingLegPi>,
    ) -> Result<Self, RingClosureError> {
        Self::check_shape(&participants, &transfer_ids, &leg_pis)?;
        let commitment = canonical_silver_commitment(&participants, &transfer_ids, &leg_pis);
        Ok(Self {
            participants,
            transfer_ids,
            leg_pis,
            closure_proof_kind: ClosureProofKind::Silver,
            closure_proof: commitment.to_vec(),
        })
    }

    /// Verify the attestation is well-formed AND the closure proof
    /// matches the canonical encoding.
    ///
    /// **Silver:** recomputes the canonical commitment and compares to
    /// `closure_proof` (must be exactly 32 bytes).
    pub fn verify(&self) -> Result<(), RingClosureError> {
        Self::check_shape(&self.participants, &self.transfer_ids, &self.leg_pis)?;
        match self.closure_proof_kind {
            ClosureProofKind::Silver => {
                if self.closure_proof.len() != 32 {
                    return Err(RingClosureError::ClosureProofMalformed {
                        kind: ClosureProofKind::Silver,
                        reason: format!(
                            "Silver closure proof must be 32 bytes, got {}",
                            self.closure_proof.len()
                        ),
                    });
                }
                let expected = canonical_silver_commitment(
                    &self.participants,
                    &self.transfer_ids,
                    &self.leg_pis,
                );
                if &self.closure_proof[..] != &expected[..] {
                    return Err(RingClosureError::ClosureCommitmentMismatch {
                        expected,
                        actual: self.closure_proof.clone(),
                    });
                }
                Ok(())
            }
        }
    }

    /// Number of participants in the ring (same as the number of
    /// legs).
    pub fn arity(&self) -> usize {
        self.participants.len()
    }

    /// Common shape-validation invoked by `silver` and `verify`.
    fn check_shape(
        participants: &[CellId],
        transfer_ids: &[[u8; 32]],
        leg_pis: &[RingLegPi],
    ) -> Result<(), RingClosureError> {
        if participants.len() < 2 {
            return Err(RingClosureError::DegenerateRing {
                participants: participants.len(),
            });
        }
        if transfer_ids.len() != participants.len() || leg_pis.len() != participants.len() {
            return Err(RingClosureError::LengthMismatch {
                participants: participants.len(),
                transfer_ids: transfer_ids.len(),
                leg_pis: leg_pis.len(),
            });
        }
        // Every participant appears exactly once (simple cycle).
        for i in 0..participants.len() {
            for j in (i + 1)..participants.len() {
                if participants[i] == participants[j] {
                    return Err(RingClosureError::DuplicateParticipant {
                        leg_index: j,
                        cell: participants[j],
                    });
                }
            }
        }
        // Each leg references the right cells + transfer_id.
        let n = participants.len();
        for (i, leg) in leg_pis.iter().enumerate() {
            let expected_sender = participants[i];
            let expected_receiver = participants[(i + 1) % n];
            if leg.sender_cell != expected_sender {
                return Err(RingClosureError::LegSenderMismatch {
                    leg_index: i,
                    expected: expected_sender,
                    actual: leg.sender_cell,
                });
            }
            if leg.receiver_cell != expected_receiver {
                return Err(RingClosureError::LegReceiverMismatch {
                    leg_index: i,
                    expected: expected_receiver,
                    actual: leg.receiver_cell,
                });
            }
            if leg.transfer_id != transfer_ids[i] {
                return Err(RingClosureError::LegTransferIdMismatch {
                    leg_index: i,
                    expected: transfer_ids[i],
                    actual: leg.transfer_id,
                });
            }
        }
        Ok(())
    }
}

/// Compute the Silver-Vision canonical commitment for a ring closure.
///
/// `BLAKE3_keyed("pyana-ring-closure-canonical-v1",
///   u64(N) || cell_0 || transfer_id_0 || pi_digest_0
///           || cell_1 || transfer_id_1 || pi_digest_1
///           || ...)`.
///
/// The cycle ordering is encoded by position; the modular receiver
/// reference is implicit (validator recomputes from indices). Two
/// rings with the same cycle but different starting positions produce
/// distinct commitments — this is intentional, so the attestation
/// commits to the canonical-starting-point as well as the cycle.
pub fn canonical_silver_commitment(
    participants: &[CellId],
    transfer_ids: &[[u8; 32]],
    leg_pis: &[RingLegPi],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(RING_CLOSURE_CANONICAL_KEY);
    hasher.update(&(participants.len() as u64).to_le_bytes());
    for ((cell, tid), leg) in participants
        .iter()
        .zip(transfer_ids.iter())
        .zip(leg_pis.iter())
    {
        hasher.update(cell.as_bytes());
        hasher.update(tid);
        hasher.update(&leg.pi_digest);
    }
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cell(byte: u8) -> CellId {
        CellId::from_bytes([byte; 32])
    }

    fn transfer_id(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn pi_digest(byte: u8) -> [u8; 32] {
        let mut d = [0u8; 32];
        d[0] = byte;
        d[31] = 0xCC;
        d
    }

    fn ring_of_3() -> (Vec<CellId>, Vec<[u8; 32]>, Vec<RingLegPi>) {
        let participants = vec![cell(0x01), cell(0x02), cell(0x03)];
        let transfer_ids = vec![transfer_id(0xAA), transfer_id(0xBB), transfer_id(0xCC)];
        let legs = vec![
            RingLegPi {
                sender_cell: cell(0x01),
                receiver_cell: cell(0x02),
                transfer_id: transfer_id(0xAA),
                pi_digest: pi_digest(0x10),
            },
            RingLegPi {
                sender_cell: cell(0x02),
                receiver_cell: cell(0x03),
                transfer_id: transfer_id(0xBB),
                pi_digest: pi_digest(0x20),
            },
            RingLegPi {
                sender_cell: cell(0x03),
                receiver_cell: cell(0x01),
                transfer_id: transfer_id(0xCC),
                pi_digest: pi_digest(0x30),
            },
        ];
        (participants, transfer_ids, legs)
    }

    fn ring_of_5() -> (Vec<CellId>, Vec<[u8; 32]>, Vec<RingLegPi>) {
        let participants: Vec<CellId> = (0..5).map(|i| cell(0x10 + i)).collect();
        let transfer_ids: Vec<[u8; 32]> = (0..5).map(|i| transfer_id(0x50 + i)).collect();
        let legs: Vec<RingLegPi> = (0..5)
            .map(|i| RingLegPi {
                sender_cell: participants[i],
                receiver_cell: participants[(i + 1) % 5],
                transfer_id: transfer_ids[i],
                pi_digest: pi_digest(0x70 + i as u8),
            })
            .collect();
        (participants, transfer_ids, legs)
    }

    #[test]
    fn silver_ring_of_3_constructs_and_verifies() {
        let (p, t, l) = ring_of_3();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver construction");
        assert_eq!(att.arity(), 3);
        assert_eq!(att.closure_proof.len(), 32);
        att.verify().expect("silver round-trip verifies");
    }

    #[test]
    fn silver_ring_of_5_constructs_and_verifies() {
        let (p, t, l) = ring_of_5();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver construction");
        assert_eq!(att.arity(), 5);
        att.verify().expect("silver ring-of-5 round-trip");
    }

    #[test]
    fn tampered_transfer_id_in_proof_field_rejects() {
        // Adversary swaps one transfer_id in `transfer_ids` after
        // construction — the leg_pis still bind the original id, so
        // shape-check fails (LegTransferIdMismatch).
        let (p, t, l) = ring_of_3();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver");
        let mut tampered = att.clone();
        tampered.transfer_ids[1] = transfer_id(0xFF);
        let err = tampered.verify().unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::LegTransferIdMismatch { leg_index: 1, .. }
        ));
    }

    #[test]
    fn tampered_leg_pi_breaks_commitment() {
        // Adversary swaps a leg's pi_digest after construction — the
        // shape check still passes, but the closure commitment differs
        // from the canonical re-hash.
        let (p, t, l) = ring_of_3();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver");
        let mut tampered = att.clone();
        tampered.leg_pis[0].pi_digest = pi_digest(0xEE);
        let err = tampered.verify().unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::ClosureCommitmentMismatch { .. }
        ));
    }

    #[test]
    fn ring_doesnt_close_when_receiver_doesnt_match_next_participant() {
        // Adversary forges a leg whose receiver is not the next ring
        // participant (the cycle breaks).
        let (p, t, mut l) = ring_of_3();
        l[1].receiver_cell = cell(0x99); // not in the ring
        let err = RingClosureAttestation::silver(p, t, l).unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::LegReceiverMismatch { leg_index: 1, .. }
        ));
    }

    #[test]
    fn ring_doesnt_close_when_sender_doesnt_match_participant() {
        let (p, t, mut l) = ring_of_3();
        l[2].sender_cell = cell(0x77); // not the i=2 participant
        let err = RingClosureAttestation::silver(p, t, l).unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::LegSenderMismatch { leg_index: 2, .. }
        ));
    }

    #[test]
    fn degenerate_ring_rejected() {
        // 1-cell self-loop is rejected — γ.2 bilateral covers it; rings
        // are N≥2 (and typically N≥3 for non-trivial cycles).
        let err = RingClosureAttestation::silver(
            vec![cell(0x01)],
            vec![transfer_id(0xAA)],
            vec![RingLegPi {
                sender_cell: cell(0x01),
                receiver_cell: cell(0x01),
                transfer_id: transfer_id(0xAA),
                pi_digest: pi_digest(0x10),
            }],
        )
        .unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::DegenerateRing { participants: 1 }
        ));
    }

    #[test]
    fn length_mismatch_rejected() {
        // transfer_ids/leg_pis lengths don't match participants.
        let p = vec![cell(0x01), cell(0x02), cell(0x03)];
        let t = vec![transfer_id(0xAA), transfer_id(0xBB)]; // short
        let l = vec![
            RingLegPi {
                sender_cell: cell(0x01),
                receiver_cell: cell(0x02),
                transfer_id: transfer_id(0xAA),
                pi_digest: pi_digest(0x10),
            };
            3
        ];
        let err = RingClosureAttestation::silver(p, t, l).unwrap_err();
        assert!(matches!(err, RingClosureError::LengthMismatch { .. }));
    }

    #[test]
    fn duplicate_participant_rejected() {
        // Same cell appears twice in the ring — not a simple cycle.
        let p = vec![cell(0x01), cell(0x02), cell(0x01)]; // dup
        let t = vec![transfer_id(0xAA), transfer_id(0xBB), transfer_id(0xCC)];
        let l = vec![
            RingLegPi {
                sender_cell: cell(0x01),
                receiver_cell: cell(0x02),
                transfer_id: transfer_id(0xAA),
                pi_digest: pi_digest(0x10),
            },
            RingLegPi {
                sender_cell: cell(0x02),
                receiver_cell: cell(0x01),
                transfer_id: transfer_id(0xBB),
                pi_digest: pi_digest(0x20),
            },
            RingLegPi {
                sender_cell: cell(0x01),
                receiver_cell: cell(0x01),
                transfer_id: transfer_id(0xCC),
                pi_digest: pi_digest(0x30),
            },
        ];
        let err = RingClosureAttestation::silver(p, t, l).unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::DuplicateParticipant { .. }
        ));
    }

    #[test]
    fn silver_proof_wrong_length_rejected_on_verify() {
        // Construct a well-shaped attestation, then truncate
        // closure_proof — verify must reject.
        let (p, t, l) = ring_of_3();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver");
        let mut tampered = att.clone();
        tampered.closure_proof.truncate(16);
        let err = tampered.verify().unwrap_err();
        assert!(matches!(
            err,
            RingClosureError::ClosureProofMalformed {
                kind: ClosureProofKind::Silver,
                ..
            }
        ));
    }

    #[test]
    fn distinct_rings_yield_distinct_commitments() {
        // Different participants / transfer_ids / pi_digests must
        // produce distinct closure commitments — the canonical hash
        // doesn't collide on the test inputs.
        let (p1, t1, l1) = ring_of_3();
        let (p2, t2, l2) = ring_of_5();
        let a1 = RingClosureAttestation::silver(p1, t1, l1).expect("silver");
        let a2 = RingClosureAttestation::silver(p2, t2, l2).expect("silver");
        assert_ne!(a1.closure_proof, a2.closure_proof);
    }

    #[test]
    fn pi_digest_from_bytes_is_deterministic_and_length_sensitive() {
        let a = RingLegPi::pi_digest_from_bytes(b"some-leg-pi");
        let b = RingLegPi::pi_digest_from_bytes(b"some-leg-pi");
        let c = RingLegPi::pi_digest_from_bytes(b"some-leg-pi-different");
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn attestation_roundtrips_serde() {
        let (p, t, l) = ring_of_3();
        let att = RingClosureAttestation::silver(p, t, l).expect("silver");
        let bytes = postcard::to_allocvec(&att).expect("serialize");
        let back: RingClosureAttestation =
            postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(back, att);
        back.verify().expect("post-serde verification");
    }
}
