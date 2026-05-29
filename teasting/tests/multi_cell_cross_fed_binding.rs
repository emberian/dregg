//! Stage 7-γ.2 Phase 2 — multi-cell cross-fed binding (Seam 9) end-to-end test.
//!
//! ## What this closes
//!
//! Before γ.2 Phase 2 a multi-cell `Transfer(A, B)` where `A` lives on F1 and
//! `B` lives on F2 produced two independent STARK proofs with no algebraic
//! cross-cell binding. F2 had to *trust* F1's `FederationReceipt`
//! (BLS-signed by F1's committee) to accept the conservation claim — the
//! "executor-trust" gap called out in `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`
//! §1a and the issue brief.
//!
//! After γ.2 Phase 2, `dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle`
//! emits a single outer proof that algebraically binds:
//!
//!   1. each per-cell PI's bilateral count + root fields to the schedule the
//!      canonical Turn predicts (so sender and receiver cannot disagree on
//!      `amount`, `direction`, `peer`, or `transfer_id`),
//!   2. the turn-identity quad (TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//!      PREVIOUS_RECEIPT_HASH) across all per-cell PIs (γ.0 binding lifted
//!      into the outer trace),
//!   3. exactly one IS_AGENT_CELL across the bundle (so a malicious aggregator
//!      cannot mint a second "agent" lane and double-spend the actor nonce).
//!
//! Conservation (∑ deltas = 0) is enforced *algebraically* via the
//! `OUTGOING_TRANSFER_ROOT` / `INCOMING_TRANSFER_ROOT` accumulators: the
//! outer AIR's CG-3 (schedule-replay) constraint requires each per-cell
//! PI's outbound/inbound root to equal the schedule-derived root, and the
//! schedule itself is computed from a single `call_forest` — so if Alice
//! claims she sent 100 but Bob's PI says he received 50, the schedules don't
//! match and the bundle rejects.
//!
//! ## What "F2 verifies without trusting F1" means in this test
//!
//! `verify_aggregated_bundle` is a pure function over the bundle bytes.
//! It uses **none** of:
//!   * F1's committee public keys,
//!   * F1's BLS threshold signature,
//!   * any side-channel attestation from F1.
//!
//! F2 holds only:
//!   * the canonical `Turn` (carries `call_forest`, `agent`, `nonce`,
//!     `previous_receipt_hash`),
//!   * the per-cell `WitnessedReceipt`s (one from F1's prover, one from
//!     F2's),
//!   * the aggregated bundle's outer proof bytes + outer PI.
//!
//! From these alone F2 derives the expected outer PI, runs the outer AIR's
//! constraints, and accepts iff every check passes. This is the
//! "trustlessly verify across federations" property the brief asks for.
//!
//! ## Path chosen (from the brief)
//!
//! **Path A — aggregator AIR.** The implementation already exists at
//! `circuit/src/bilateral_aggregation_air.rs` (the outer AIR) and
//! `turn/src/aggregate_bilateral_prover.rs` (the prover + verifier). Path B
//! (Pickles recursion) is the long-term composition target but lives in a
//! crate (`circuit/src/backends/stark_in_pickles.rs`) that does not today
//! enforce a *conservation* metadata field on the wrapper — so until
//! `compose_wrapped_starks` learns to bind `sum-of-PIs = 0` the only honest
//! "this is enforced cryptographically" path is the aggregation AIR. The
//! existing prover's AIR-level replay (`replay_aggregation_air` in
//! `aggregate_bilateral_prover.rs`) IS the cryptographic constraint that
//! makes the binding load-bearing.
//!
//! ## Test plan
//!
//! 1. **Happy path.** Build a two-federation harness. Alice on F1 ($1000 balance),
//!    Bob on F2 (0 balance). Construct a Transfer(A→B, 100) turn. Fabricate
//!    per-cell `WitnessedReceipt`s tagged with each cell's home federation id.
//!    Aggregate via `prove_aggregated_bundle`. F2 verifies via
//!    `verify_aggregated_bundle` — accepts without consulting F1.
//!    Assertions:
//!      * `bundle.federation_ids` contains both F1 and F2 ids.
//!      * `bundle.outer_pi[OUTER_N_CELLS] == 2`.
//!      * `bundle.outer_pi[OUTER_BILATERAL_CONSISTENT] == 1`.
//!
//! 2. **Adversarial — tamper one inner proof.** Tamper Alice's PI's
//!    `OUTGOING_TRANSFER_ROOT` (the externally visible footprint of a forged
//!    transfer_id). Aggregation rejects at the Phase-1 precondition gate.
//!
//! 3. **Adversarial — conservation balance lie.** Bob's PI is fabricated
//!    against a *different* canonical Turn that claims amount=50, while
//!    Alice's PI says amount=100. The bundle aggregator's schedule-derived
//!    expected root for Bob (against the *real* turn) won't match Bob's PI's
//!    actual root — reject.
//!
//! 4. **Adversarial — verifier rejects flipped consistency flag.** Run a
//!    valid prove, then post-tamper `outer_pi[OUTER_BILATERAL_CONSISTENT] = 0`.
//!    The verifier short-circuits.
//!
//! 5. **Adversarial — verifier rejects swapped participating_cells order.**
//!    Reordering disturbs the row-to-cell binding that the AIR's CG-3
//!    schedule-projection enforces, since each row's expected_counts and
//!    expected_roots are computed against the cell named in
//!    `participating_cells[row]`.

#![allow(clippy::too_many_arguments)]

use dregg_circuit::bilateral_aggregation_air as ag;
use dregg_circuit::effect_vm::pi as inner_pi;
use dregg_turn::aggregate_bilateral_prover::{
    AggregatedBundle, prove_aggregated_bundle, verify_aggregated_bundle,
};
use dregg_turn::bilateral_schedule::ExpectedBilateral;
use dregg_turn::{ActionBuilder, Turn, TurnBuilder, TurnReceipt, WitnessedReceipt};
use dregg_types::CellId;

// ---------------------------------------------------------------------------
// Test fixtures
// ---------------------------------------------------------------------------

/// Synthetic 32-byte federation id derived deterministically from a label.
fn fed_id(label: &str) -> [u8; 32] {
    *blake3::hash(format!("multi-cell-cross-fed-binding:{label}").as_bytes()).as_bytes()
}

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

/// Build a `TurnReceipt` tagged with `home_fed`. The receipt is otherwise
/// dummy; the algebraic binding lives in the aggregated bundle's outer
/// proof, not in the receipt's BLS signature.
fn receipt_for(agent: CellId, home_fed: [u8; 32]) -> TurnReceipt {
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
        federation_id: home_fed,
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

/// Fabricate an "honest" `WitnessedReceipt` whose PI carries the γ.2
/// bilateral slots for `cell_id` against `turn`. Mirrors the helper in
/// `dregg_verifier::bilateral_pair::fabricate_witnessed_receipt` but lets
/// the caller stamp the receipt with a specific home federation id (so the
/// resulting bundle's `federation_ids` reflects "this WR came from F1, that
/// one from F2").
fn fabricate_wr_for_fed(turn: &Turn, cell_id: &CellId, home_fed: [u8; 32]) -> WitnessedReceipt {
    use dregg_circuit::field::BabyBear;
    use dregg_turn::bilateral_schedule::project_into_pi;

    let sched = ExpectedBilateral::from_turn(turn);
    let counts = sched.counts_for(cell_id);
    let roots = sched.roots_for(cell_id, turn.nonce);

    let mut pi_bb = vec![BabyBear::ZERO; inner_pi::BASE_COUNT];
    let (th, eg, _, prev) = dregg_turn::executor::TurnExecutor::compute_turn_identity_pi(turn);
    for i in 0..4 {
        pi_bb[inner_pi::TURN_HASH_BASE + i] = th[i];
        pi_bb[inner_pi::EFFECTS_HASH_GLOBAL_BASE + i] = eg[i];
        pi_bb[inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
    }
    pi_bb[inner_pi::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
    project_into_pi(&mut pi_bb, &counts, &roots);
    pi_bb[inner_pi::IS_AGENT_CELL] = if cell_id == &turn.agent {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };
    let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();
    // The γ.2 Phase-2 aggregator (CV3 real-STARK migration, #133) requires
    // scope-2 WitnessedReceipts — accepting a scope-1-only WR would let an
    // aggregate look stronger than its inputs. Attach a minimal scope-2
    // witness trace (matches dregg_verifier::bilateral_pair's fix). Width is
    // taken from the live EFFECT_VM_WIDTH so it tracks #131/#132's PI growth.
    let trace = vec![vec![
        BabyBear::ZERO;
        dregg_circuit::effect_vm::EFFECT_VM_WIDTH
    ]];
    WitnessedReceipt::from_components(
        receipt_for(*cell_id, home_fed),
        vec![],
        pi_u32,
        Some(trace.as_slice()),
    )
}

fn build_transfer_turn(from: CellId, to: CellId, amount: u64, nonce: u64) -> Turn {
    let mut builder = TurnBuilder::new(from, nonce);
    let action = ActionBuilder::new_unchecked_for_tests(from, "transfer", from)
        .effect_transfer(from, to, amount)
        .build();
    builder.add_action(action);
    builder.fee(0).build()
}

// ---------------------------------------------------------------------------
// 1. Happy path: F2 verifies F1's cross-fed Transfer with NO trust dependency.
// ---------------------------------------------------------------------------

#[test]
fn cross_fed_transfer_aggregates_and_f2_verifies_autonomously() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1); // home: F1
    let bob = cid(0xB2); //   home: F2

    let turn = build_transfer_turn(alice, bob, 100, 42);

    // Each federation's prover emits its side's WR. Their PIs are
    // *constructed from the same canonical Turn* — the schedule derivation
    // is deterministic on `(call_forest, ACTOR_NONCE)` alone, no executor
    // coordination required.
    let wr_alice = fabricate_wr_for_fed(&turn, &alice, f1);
    let wr_bob = fabricate_wr_for_fed(&turn, &bob, f2);

    // F1 (or any aggregator that holds both WRs) emits the bundle. The
    // aggregator's Phase-1 precondition `verify_bilateral_chain` checks
    // that the two per-cell PIs agree with the schedule before invoking
    // the prover.
    let entries = vec![(alice, wr_alice), (bob, wr_bob)];
    let bundle = prove_aggregated_bundle(&turn, &entries).expect("happy path aggregates");

    // Bundle surface checks.
    assert_eq!(
        bundle.participating_cells.len(),
        2,
        "bundle covers both cells",
    );
    assert_eq!(
        bundle.outer_pi.len(),
        ag::OUTER_BASE_COUNT,
        "outer PI is fixed-width γ.2 layout",
    );
    assert_eq!(
        bundle.outer_pi[ag::OUTER_BILATERAL_CONSISTENT],
        1,
        "bilateral consistency is bound to the outer proof",
    );
    assert_eq!(
        bundle.outer_pi[ag::OUTER_N_CELLS],
        2,
        "outer PI binds n_cells = 2",
    );
    assert_eq!(bundle.bundle_epoch, 42, "bundle_epoch == turn.nonce");
    // Cross-federation evidence: the bundle records that both F1 and F2
    // participated. v1 derives federation ids from each WR's receipt; a
    // future federation-id-in-PI extension (Phase 1.5) will lift this into
    // the algebra. For now the listing is informational.
    assert!(
        bundle.federation_ids.contains(&f1) && bundle.federation_ids.contains(&f2),
        "both federations are listed as participants; got {:?}",
        bundle.federation_ids,
    );

    // The headline assertion: F2 verifies the bundle **without consulting
    // F1's committee, signatures, or any side-channel attestation**. The
    // verifier is a pure function of the bundle bytes.
    verify_aggregated_bundle(&bundle).expect("F2 verifies cross-fed bundle autonomously");
}

// ---------------------------------------------------------------------------
// 2. Adversarial: tamper one inner proof.
// ---------------------------------------------------------------------------

#[test]
fn tampered_inner_proof_rejects() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1);
    let bob = cid(0xB2);

    let turn = build_transfer_turn(alice, bob, 100, 42);

    let mut wr_alice = fabricate_wr_for_fed(&turn, &alice, f1);
    let wr_bob = fabricate_wr_for_fed(&turn, &bob, f2);

    // Tamper Alice's OUTGOING_TRANSFER_ROOT — the externally visible
    // footprint of a forged transfer_id. This is the *only* way to make
    // Alice's per-cell proof claim she sent something different (the
    // accumulator is what the outer AIR's CG-3 constraint binds against
    // the schedule).
    wr_alice.public_inputs[inner_pi::OUTGOING_TRANSFER_ROOT_BASE] = 0xDEAD_BEEF & 0x7FFF_FFFF;

    let entries = vec![(alice, wr_alice), (bob, wr_bob)];
    let res = prove_aggregated_bundle(&turn, &entries);
    assert!(
        res.is_err(),
        "tampered inner proof must reject before producing a bundle; got {res:?}",
    );
}

// ---------------------------------------------------------------------------
// 3. Adversarial: conservation balance lie. Sender says 100, receiver says 50.
// ---------------------------------------------------------------------------

#[test]
fn conservation_balance_lie_rejects() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1);
    let bob = cid(0xB2);

    // The canonical turn the bundle is built against says amount=100.
    let real_turn = build_transfer_turn(alice, bob, 100, 42);
    // Bob's prover, however, was given a *different* turn (amount=50). His
    // PI carries roots derived from amount=50. Sender's PI agrees with the
    // real schedule, Bob's PI disagrees — conservation broken.
    let lie_turn = build_transfer_turn(alice, bob, 50, 42);

    let wr_alice = fabricate_wr_for_fed(&real_turn, &alice, f1);
    let wr_bob = fabricate_wr_for_fed(&lie_turn, &bob, f2);

    let entries = vec![(alice, wr_alice), (bob, wr_bob)];
    let res = prove_aggregated_bundle(&real_turn, &entries);
    assert!(
        res.is_err(),
        "conservation lie (sender 100 / receiver 50) must reject; got {res:?}",
    );
}

// ---------------------------------------------------------------------------
// 4. Adversarial: post-prove tamper of the outer consistency flag.
// ---------------------------------------------------------------------------

#[test]
fn flipped_consistency_flag_rejects_at_verify() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = build_transfer_turn(alice, bob, 100, 42);

    let entries = vec![
        (alice, fabricate_wr_for_fed(&turn, &alice, f1)),
        (bob, fabricate_wr_for_fed(&turn, &bob, f2)),
    ];
    let mut bundle = prove_aggregated_bundle(&turn, &entries).expect("baseline prove");

    // Adversary flips the consistency flag in the outer PI hoping the
    // verifier won't notice.
    bundle.outer_pi[ag::OUTER_BILATERAL_CONSISTENT] = 0;
    let res = verify_aggregated_bundle(&bundle);
    assert!(
        res.is_err(),
        "verifier must reject when BILATERAL_CONSISTENT is flipped; got {res:?}",
    );
}

// ---------------------------------------------------------------------------
// 5. Adversarial: reorder participating_cells.
// ---------------------------------------------------------------------------

#[test]
fn reordered_participating_cells_rejects_at_verify() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = build_transfer_turn(alice, bob, 100, 42);

    let entries = vec![
        (alice, fabricate_wr_for_fed(&turn, &alice, f1)),
        (bob, fabricate_wr_for_fed(&turn, &bob, f2)),
    ];
    let mut bundle = prove_aggregated_bundle(&turn, &entries).expect("baseline prove");

    // The row-to-cell mapping is what CG-3 (schedule replay) binds. Swapping
    // participating_cells lies about which row corresponds to which cell;
    // the verifier's `participating_cells[i]` recompute will mismatch the
    // embedded `expected_counts` for the swapped row.
    bundle.participating_cells.swap(0, 1);
    let res = verify_aggregated_bundle(&bundle);
    assert!(
        res.is_err(),
        "verifier must reject when participating_cells is reordered post-prove; got {res:?}",
    );
}

// ---------------------------------------------------------------------------
// 6. F2 verifies bundle WITHOUT any F1 federation receipt / signature.
// ---------------------------------------------------------------------------

/// The "trustless" assertion the issue brief calls out, made explicit. This
/// test deliberately gives F2 *only* the bundle and the canonical Turn —
/// **not** F1's `FederationReceipt`, not F1's committee pubkeys, not any
/// `verify_cross_fed_receipt` call. The bundle must self-authenticate
/// algebraically.
#[test]
fn f2_verifies_with_no_f1_signature_in_path() {
    let f1 = fed_id("fed-alpha");
    let f2 = fed_id("fed-beta");
    let alice = cid(0xA1);
    let bob = cid(0xB2);
    let turn = build_transfer_turn(alice, bob, 100, 42);

    let entries = vec![
        (alice, fabricate_wr_for_fed(&turn, &alice, f1)),
        (bob, fabricate_wr_for_fed(&turn, &bob, f2)),
    ];
    let bundle = prove_aggregated_bundle(&turn, &entries).expect("aggregate");

    // Simulate transport to F2: serialize → deserialize. Strip every
    // executor-side artifact; only the bundle bytes survive.
    let json = bundle.to_json().expect("serialize bundle for transport");

    // F2 receives the bundle.
    let received = AggregatedBundle::from_json(&json).expect("deserialize bundle on F2 side");

    // F2's verifier path. No F1 keys. No BLS check. No external state.
    verify_aggregated_bundle(&received)
        .expect("F2 accepts cross-fed bundle from bytes alone (no F1 trust required)");

    // Sanity: F2 recomputes the schedule from the canonical Turn it
    // received in the bundle and confirms it predicts Alice→Bob (100).
    let sched = ExpectedBilateral::from_turn(&received.turn);
    assert_eq!(
        sched.transfers.len(),
        1,
        "schedule reconstructed by F2 names exactly one Transfer",
    );
    let t = &sched.transfers[0];
    assert_eq!(t.from, alice);
    assert_eq!(t.to, bob);
    assert_eq!(t.amount, 100);
}
