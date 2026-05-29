//! Stage 7-γ.2 Phase 1 — bilateral cross-cell pair verifier.
//!
//! Off-AIR verifier for a *bundle* of [`WitnessedReceipt`]s that all describe
//! the same [`Turn`]. Given the turn (carrying the canonical `call_forest`
//! and `ACTOR_NONCE`) plus the per-cell WRs that came out of executing it,
//! the verifier:
//!
//!   1. Reconstructs the expected bilateral schedule (`Transfer`, `Grant`,
//!      `Introduce`) from `(call_forest, ACTOR_NONCE)` alone.
//!   2. For each `(cell_id, WitnessedReceipt)` entry, lifts the PI u32 vector
//!      into BabyBear felts and compares the γ.2 bilateral slots
//!      (counts + 7 accumulator roots) to what the schedule predicts.
//!   3. Enforces `IS_AGENT_CELL` is `1` exactly on the proof whose cell is
//!      `turn.agent`, and `0` on all the others.
//!   4. Cross-side existence: a Transfer / Grant naming a covered cell must
//!      have its peer covered in the bundle; an Introduce naming any role
//!      must have all three roles covered.
//!
//! All of the above closes the threats from
//! `EXECUTOR-HONESTY-AUDIT.md` T1 / T3 / T15 — *the verifier can now confirm
//! cross-cell agreement without trusting the executor*. See
//! `STAGE-7-GAMMA-2-PI-DESIGN.md` §4 for the full algorithm.
//!
//! This module exposes a JSON-friendly bundle shape (`BilateralBundle`) for
//! the `dregg-verifier bilateral-pair` CLI subcommand. The CLI consumes one
//! JSON file containing both the turn and the WR entries; the design choice
//! is for the bundle to be a single artifact so an auditor can ship one file
//! and rerun the verification.

use dregg_turn::{Turn, WitnessedReceipt};
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// On-disk JSON shape
// ---------------------------------------------------------------------------

/// One entry in a bilateral bundle: the cell identifier plus its
/// [`WitnessedReceipt`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BilateralEntry {
    /// The cell whose per-cell proof this WR carries.
    pub cell_id: CellId,
    /// The WR itself (proof bytes + PI + optional witness bundle).
    pub witnessed_receipt: WitnessedReceipt,
}

/// A bundle of per-cell WRs from one turn, packaged for off-AIR bilateral
/// verification. The CLI's `bilateral-pair` subcommand reads this JSON shape.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BilateralBundle {
    /// The canonical turn (carries `call_forest`, `nonce`, `agent`).
    pub turn: Turn,
    /// One entry per touched cell. Order does not matter; the verifier's
    /// schedule reconstruction is order-independent.
    pub entries: Vec<BilateralEntry>,
    /// γ.2 unilateral binding (1-arity sibling of bilateral): per-cell
    /// self-attestations the prover claims it produced this turn.
    /// Each `(cell_id, attestations)` entry is folded into the accumulator
    /// the verifier compares against the cell's PI[UNILATERAL_*] slots.
    ///
    /// Empty when no cell self-attested. Order within each cell's vec is
    /// the accumulator-absorb order — must match the producer side.
    ///
    /// `peer_exchange` composition: a sovereign cell using
    /// `PeerStateTransition::unilateral_attestation` populates this map
    /// with the attestation it signed; the receiver verifies it matches
    /// the sender's per-cell PI accumulator. Forging the attestation on
    /// behalf of another cell-id is rejected because the
    /// `attestation_data` canonical preimage includes `cell_id` — a
    /// forged sender produces a different data hash and a different
    /// accumulator root.
    #[serde(default)]
    pub unilateral_attestations: std::collections::BTreeMap<
        CellId,
        Vec<dregg_turn::bilateral_schedule::UnilateralAttestation>,
    >,
}

// ---------------------------------------------------------------------------
// Verdict
// ---------------------------------------------------------------------------

/// Result of a bilateral-pair verification, serialized to stdout by the CLI.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BilateralVerdict {
    /// True iff every check passed.
    pub verified: bool,
    /// Number of bundle entries (cells covered).
    pub entry_count: usize,
    /// Number of Transfers, Grants, Introduces in the reconstructed schedule.
    pub transfer_count: usize,
    pub grant_count: usize,
    pub introduce_count: usize,
    /// Per-cell list of cell ids in the order they appeared in the bundle.
    pub cells: Vec<String>,
    /// Human-readable reason when `verified == false`; "ok" otherwise.
    pub reason: String,
}

impl BilateralVerdict {
    fn accept(entry_count: usize, sched_counts: (usize, usize, usize), cells: Vec<String>) -> Self {
        Self {
            verified: true,
            entry_count,
            transfer_count: sched_counts.0,
            grant_count: sched_counts.1,
            introduce_count: sched_counts.2,
            cells,
            reason: "ok".to_string(),
        }
    }

    fn reject(
        entry_count: usize,
        sched_counts: (usize, usize, usize),
        cells: Vec<String>,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            verified: false,
            entry_count,
            transfer_count: sched_counts.0,
            grant_count: sched_counts.1,
            introduce_count: sched_counts.2,
            cells,
            reason: reason.into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Core API
// ---------------------------------------------------------------------------

/// Verify a bilateral bundle.
///
/// Returns a [`BilateralVerdict`] describing the outcome. The caller decides
/// the exit code (`exit_code::VERIFIED` on success, `REJECTED` on a check
/// failure, `ERROR` on bundle parse / structural issues).
pub fn verify_bilateral_bundle_json(json: &str) -> BilateralVerdict {
    let bundle: BilateralBundle = match serde_json::from_str(json) {
        Ok(b) => b,
        Err(e) => {
            return BilateralVerdict {
                verified: false,
                entry_count: 0,
                transfer_count: 0,
                grant_count: 0,
                introduce_count: 0,
                cells: vec![],
                reason: format!("bundle JSON parse error: {e}"),
            };
        }
    };
    verify_bilateral_bundle(&bundle)
}

/// Verify a deserialized [`BilateralBundle`]. Pure function over the bundle.
pub fn verify_bilateral_bundle(bundle: &BilateralBundle) -> BilateralVerdict {
    let cells: Vec<String> = bundle
        .entries
        .iter()
        .map(|e| hex::encode(e.cell_id.as_bytes()))
        .collect();
    // Build the schedule and inject unilateral attestations from the bundle
    // (γ.2 1-arity sibling — cell-side data that doesn't live in the Turn).
    let mut sched = dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(&bundle.turn);
    for (cell, attestations) in &bundle.unilateral_attestations {
        for att in attestations {
            sched.push_unilateral(cell.clone(), att.clone());
        }
    }
    let sched_counts = (
        sched.transfers.len(),
        sched.grants.len(),
        sched.introduces.len(),
    );
    let entry_count = bundle.entries.len();

    // Build the (CellId, &WitnessedReceipt) view the executor API consumes.
    let view: Vec<(CellId, &WitnessedReceipt)> = bundle
        .entries
        .iter()
        .map(|e| (e.cell_id.clone(), &e.witnessed_receipt))
        .collect();

    match WitnessedReceipt::verify_bilateral_chain_with_schedule(&view, &bundle.turn, &sched) {
        Ok(()) => BilateralVerdict::accept(entry_count, sched_counts, cells),
        Err(e) => BilateralVerdict::reject(entry_count, sched_counts, cells, format!("{e:?}")),
    }
    .also_check_stark_pi(bundle)
}

impl BilateralVerdict {
    /// Optional structural overlay: confirm every WR's `public_inputs` length
    /// is at least the γ.2 `BASE_COUNT`; reject otherwise. (The bilateral
    /// chain verify already enforces this — we keep the check here as a
    /// belt-and-suspenders surface for when `entries` is empty / the chain
    /// verify short-circuits early.)
    fn also_check_stark_pi(mut self, bundle: &BilateralBundle) -> Self {
        if !self.verified {
            return self;
        }
        use dregg_circuit::effect_vm::pi as p;
        for (i, e) in bundle.entries.iter().enumerate() {
            if e.witnessed_receipt.public_inputs.len() < p::BASE_COUNT {
                self.verified = false;
                self.reason = format!(
                    "entry {i} (cell {}): PI vector has {} entries, expected at least {} (γ.2 layout)",
                    hex::encode(e.cell_id.as_bytes()),
                    e.witnessed_receipt.public_inputs.len(),
                    p::BASE_COUNT
                );
                return self;
            }
        }
        self
    }
}

// ---------------------------------------------------------------------------
// Helpers used by tests + CLI
// ---------------------------------------------------------------------------

/// Build a [`WitnessedReceipt`] whose PI vector is populated with the γ.2
/// bilateral slots for `cell_id` (the rest are zero). Used by tests and the
/// integration demo to fabricate an "honest" bundle without going through a
/// full STARK prover.
///
/// In a production setting the `public_inputs` come from the prover's actual
/// proof; this helper exists so that off-AIR bilateral consistency can be
/// exercised end-to-end without paying the proving cost.
pub fn fabricate_witnessed_receipt(
    turn: &Turn,
    cell_id: &CellId,
    receipt: dregg_turn::TurnReceipt,
) -> WitnessedReceipt {
    fabricate_witnessed_receipt_with_schedule(
        turn,
        cell_id,
        receipt,
        &dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(turn),
    )
}

/// Same as [`fabricate_witnessed_receipt`] but using a caller-provided
/// schedule. Pass a schedule with `unilateral_attestations` populated to
/// exercise the γ.2 unilateral-binding PI slots.
pub fn fabricate_witnessed_receipt_with_schedule(
    turn: &Turn,
    cell_id: &CellId,
    receipt: dregg_turn::TurnReceipt,
    schedule: &dregg_turn::bilateral_schedule::ExpectedBilateral,
) -> WitnessedReceipt {
    use dregg_circuit::effect_vm::pi as p;
    use dregg_circuit::field::BabyBear;
    use dregg_turn::bilateral_schedule::project_into_pi;

    let counts = schedule.counts_for(cell_id);
    let roots = schedule.roots_for(cell_id, turn.nonce);

    let mut pi_bb = vec![BabyBear::ZERO; p::BASE_COUNT];
    // Populate turn-identity slots (shared across all per-cell proofs of one turn).
    let (th, eg, _, prev) = dregg_turn::executor::TurnExecutor::compute_turn_identity_pi(turn);
    for i in 0..4 {
        pi_bb[p::TURN_HASH_BASE + i] = th[i];
        pi_bb[p::EFFECTS_HASH_GLOBAL_BASE + i] = eg[i];
        pi_bb[p::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
    }
    pi_bb[p::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
    project_into_pi(&mut pi_bb, &counts, &roots);
    pi_bb[p::IS_AGENT_CELL] = if cell_id == &turn.agent {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };
    let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();

    // Attach a minimal scope-2 witness trace so the artifact is a full
    // scope-(2) WitnessedReceipt. The Phase-2 aggregator
    // (`prove_aggregated_bundle`) requires scope-2 inputs — accepting a
    // scope-1-only WR would let an aggregate look stronger than the receipt
    // material it summarizes. A single zero row is sufficient to populate the
    // inline witness bundle + witness-hash binding.
    let trace = vec![vec![BabyBear::ZERO; dregg_circuit::effect_vm::EFFECT_VM_WIDTH]];
    WitnessedReceipt::from_components(receipt, vec![], pi_u32, Some(trace.as_slice()))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::effect_vm::pi as p;
    use dregg_turn::{ActionBuilder, TurnBuilder, TurnReceipt};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn dummy_receipt(agent: CellId) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 0,
            effects_hash: [0u8; 32],
            computrons_used: 0,
            action_count: 0,
            previous_receipt_hash: None,
            agent,
            federation_id: [0u8; 32],
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
        }
    }

    fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
        let mut builder = TurnBuilder::new(alice, nonce);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, amount)
            .build();
        builder.add_action(action);
        builder.fee(0).build()
    }

    #[test]
    fn happy_path_bilateral_transfer_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(verdict.verified, "honest bundle must verify: {:?}", verdict);
        assert_eq!(verdict.entry_count, 2);
        assert_eq!(verdict.transfer_count, 1);
    }

    #[test]
    fn tampered_amount_rejects() {
        // Receiver claims amount=50; sender (and the canonical Turn) say 100.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let real_turn = make_transfer_turn(alice, bob, 100, 1);
        let lie_turn = make_transfer_turn(alice, bob, 50, 1);

        let bundle = BilateralBundle {
            turn: real_turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &real_turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    // Bob's PI is fabricated against a different turn (50 not 100).
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &lie_turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(!verdict.verified);
        assert!(
            verdict.reason.contains("root") || verdict.reason.contains("incoming_transfer"),
            "expected root/incoming mismatch, got: {}",
            verdict.reason
        );
    }

    #[test]
    fn tampered_transfer_id_via_root_overwrite_rejects() {
        // Equivalent to "tamper with transfer_id" — overwrite Alice's
        // OUTGOING_TRANSFER_ROOT with a garbage felt. The accumulator absorbs
        // transfer_id; mangling the root is the externally-visible footprint
        // of any in-PI transfer_id tamper.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut alice_wr = fabricate_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
        let bob_wr = fabricate_witnessed_receipt(&turn, &bob, dummy_receipt(alice));
        // Tamper: zap one felt of OUTGOING_TRANSFER_ROOT (transfer_id is folded
        // into the root, so any in-PI transfer_id manipulation shows up here).
        alice_wr.public_inputs[p::OUTGOING_TRANSFER_ROOT_BASE] = 0xDEAD_BEEF_u32 & 0x7FFF_FFFF;

        let bundle = BilateralBundle {
            turn,
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: alice_wr,
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: bob_wr,
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(!verdict.verified, "transfer_id tamper must reject");
    }

    #[test]
    fn wrong_peer_cell_id_rejects() {
        // Adversarial: bundle declares Bob's cell-id as some attacker-controlled
        // cid(0xCC) instead of the real bob (0xB2). The schedule walks the
        // canonical turn and expects (alice, bob); the bundle's "bob" entry's
        // PI is fabricated for cid(0xCC) — its OUTGOING/INCOMING roots
        // diverge from the schedule's prediction for the real bob, so the
        // bundle rejects on the cross-side existence check AND the per-cell
        // PI root check.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let attacker = cid(0xCC);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: attacker,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &attacker, // PI derived against attacker, not bob
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(!verdict.verified, "wrong peer cell must reject");
    }

    #[test]
    fn fabricated_inbound_without_sender_rejects() {
        // Adversarial: a bundle declares an incoming transfer to bob (PI's
        // INBOUND_TRANSFER_COUNT > 0) but the canonical Turn never names that
        // transfer at all. We achieve this by feeding the verifier a Turn with
        // no Transfer effects, while Bob's PI was fabricated against a Turn
        // that *does* declare the transfer.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let real_turn_with_transfer = make_transfer_turn(alice, bob, 100, 1);
        // Verifier uses an empty turn (no transfer in call_forest).
        let mut empty_builder = TurnBuilder::new(alice, 1);
        let noop_action = ActionBuilder::new_unchecked_for_tests(alice, "noop", alice).build();
        empty_builder.add_action(noop_action);
        let empty_turn = empty_builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: empty_turn, // schedule says: no transfers expected
            entries: vec![BilateralEntry {
                cell_id: bob,
                // Bob's fabricated PI claims an inbound transfer.
                witnessed_receipt: fabricate_witnessed_receipt(
                    &real_turn_with_transfer,
                    &bob,
                    dummy_receipt(alice),
                ),
            }],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            !verdict.verified,
            "claimed inbound transfer absent from schedule must reject"
        );
    }

    #[test]
    fn json_roundtrip_and_verify() {
        // The CLI parses a JSON bundle from disk → verify_bilateral_bundle_json.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let json = serde_json::to_string(&bundle).expect("serialize");
        let verdict = verify_bilateral_bundle_json(&json);
        assert!(verdict.verified, "{:?}", verdict);

        // Edge case: malformed JSON (missing required fields) must reject.
        let bad_json = r#"{"turn": null, "entries": []}"#;
        let bad_verdict = verify_bilateral_bundle_json(bad_json);
        assert!(
            !bad_verdict.verified,
            "malformed JSON must be rejected: {:?}",
            bad_verdict
        );

        // Edge case: empty JSON must reject.
        let empty_verdict = verify_bilateral_bundle_json("{}");
        assert!(
            !empty_verdict.verified,
            "empty JSON must be rejected: {:?}",
            empty_verdict
        );
    }

    // ---- bilateral Grant happy-path -----------------------------------------

    #[test]
    fn happy_path_bilateral_grant_verifies() {
        // Alice grants a capability to Bob; verifier confirms grantor +
        // grantee accumulator roots match.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let target = cid(0xCC);
        let mut builder = TurnBuilder::new(alice, 1);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "grant", alice)
            .effect_grant_capability(
                alice,
                bob,
                dregg_cell::CapabilityRef {
                    target,
                    slot: 0,
                    permissions: dregg_cell::AuthRequired::Signature,
                    expires_at: None,
                    breadstuff: None,
                    allowed_effects: None,
                },
            )
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            verdict.verified,
            "honest bilateral grant must verify: {:?}",
            verdict
        );
        assert_eq!(verdict.grant_count, 1);
    }

    // ---- trilateral Introduce happy-path ------------------------------------

    // ---- γ.2 unilateral binding tests (1-arity sibling) -----------------

    #[test]
    fn unilateral_attestation_happy_path() {
        // Alice transfers to Bob *and* publishes a SelfStateTransition
        // attestation. The bundle carries the attestation; the verifier
        // confirms Alice's PI[UNILATERAL_*] matches what the schedule predicts.
        use dregg_turn::bilateral_schedule::{
            ExpectedBilateral, UnilateralAttestation, UnilateralAttestationKind,
        };
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let att = UnilateralAttestation {
            kind: UnilateralAttestationKind::SelfStateTransition,
            attestation_data: [0xAA; 32],
        };
        let mut sched = ExpectedBilateral::from_turn(&turn);
        sched.push_unilateral(alice, att.clone());

        let mut atts = std::collections::BTreeMap::new();
        atts.insert(alice, vec![att]);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt_with_schedule(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                        &sched,
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt_with_schedule(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                        &sched,
                    ),
                },
            ],
            unilateral_attestations: atts,
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            verdict.verified,
            "honest unilateral attestation must verify: {:?}",
            verdict
        );
    }

    #[test]
    fn unilateral_tampered_root_rejects() {
        // Same as the happy-path setup but the prover's PI carries a different
        // unilateral root than what the bundle declares.
        use dregg_turn::bilateral_schedule::{
            ExpectedBilateral, UnilateralAttestation, UnilateralAttestationKind,
        };
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        // Schedule used for the prover-side PI fabrication: WITHOUT the
        // attestation (so the prover's PI shows sentinel root).
        let sched_without = ExpectedBilateral::from_turn(&turn);

        // The bundle, however, claims an attestation — the verifier will
        // rebuild the schedule with the attestation, expect a non-sentinel
        // root, and reject Alice's PI (which carries the sentinel).
        let att = UnilateralAttestation {
            kind: UnilateralAttestationKind::SelfStateTransition,
            attestation_data: [0xAA; 32],
        };
        let mut atts = std::collections::BTreeMap::new();
        atts.insert(alice, vec![att]);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt_with_schedule(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                        &sched_without,
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt_with_schedule(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                        &sched_without,
                    ),
                },
            ],
            unilateral_attestations: atts,
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            !verdict.verified,
            "missing unilateral attestation in PI must reject"
        );
    }

    #[test]
    fn unilateral_pi_overwrite_rejects() {
        // The bundle declares no attestation; the schedule expects a sentinel;
        // but Alice's PI carries a garbage non-sentinel unilateral root.
        // The PI-vs-schedule mismatch must reject.
        use dregg_circuit::effect_vm::pi as p;
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut alice_wr = fabricate_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
        let bob_wr = fabricate_witnessed_receipt(&turn, &bob, dummy_receipt(alice));
        alice_wr.public_inputs[p::UNILATERAL_ATTESTATIONS_COUNT] = 1;
        alice_wr.public_inputs[p::UNILATERAL_ATTESTATIONS_ROOT_BASE] = 0xDEADBEEF & 0x7FFF_FFFF;

        let bundle = BilateralBundle {
            turn,
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: alice_wr,
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: bob_wr,
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            !verdict.verified,
            "tampered unilateral PI must reject: {:?}",
            verdict
        );
    }

    #[test]
    fn happy_path_trilateral_introduce_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);
        let mut builder = TurnBuilder::new(alice, 1);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "introduce", alice)
            .effect_introduce(alice, bob, carol, dregg_cell::AuthRequired::Signature)
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: carol,
                    witnessed_receipt: fabricate_witnessed_receipt(
                        &turn,
                        &carol,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = verify_bilateral_bundle(&bundle);
        assert!(
            verdict.verified,
            "honest trilateral introduce must verify: {:?}",
            verdict
        );
        assert_eq!(verdict.introduce_count, 1);
        assert_eq!(verdict.entry_count, 3);
    }
}
