//! # PrivateLeg: tests for the witnessless-participant turn role.
//!
//! Exercises the Rust production-wiring of `Dregg2/Distributed/PrivateLeg.lean` (keystone
//! `joint_turn_sound_with_private_legs`) and `metatheory/docs/PRIVATE-OFFLINE-CELLS.md` §4/§7:
//!
//!   * the commit-path verify-gate `MixedJoint::check_private_legs_admissible` — every private
//!     leg's ZK proof verifies AND binds the shared `jid` (the Rust analog of the Lean
//!     `MixedAdmissible` private conjuncts);
//!   * state-root continuity across turns (`check_chain_bound`) — `commit_post[i] ==
//!     commit_pre[i+1]`, mirroring `HistoryAggregation.ChainBound`.
//!
//! The two teeth the keystone demands, both polarities:
//!   * ACCEPT — an honest leg with a binding, accepting proof is admitted
//!     (`privLeg_real_verifies`);
//!   * ANTI-GHOST — a private leg whose proof does NOT bind the shared `jid` is REFUSED
//!     (`privLeg_forged_rejected`): only the extractability carrier could rescue an unbound
//!     proof, and the honest gate here refuses it.

#![cfg(test)]

use dregg_cell::{Cell, CellId, Ledger, Preconditions};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
use dregg_turn::{CallForest, ComputronCosts};

use crate::atomic::{
    AtomicForest, ChainBreak, Coordinator, Decision, MixedAdmitError, MixedJoint,
    PrivateContribution, PrivateLeg, PrivateLegProof, Vote, check_chain_bound,
};

// ───────────────────────────── helpers ─────────────────────────────

fn node_id(n: u8) -> [u8; 32] {
    let mut id = [0u8; 32];
    id[0] = n;
    id
}

fn keypair(n: u8) -> ([u8; 32], [u8; 32]) {
    let seed = *blake3::hash(&[n; 1]).as_bytes();
    let pk = Vote::public_key_from_signing_key(&seed);
    (seed, pk)
}

/// A 32-byte field-element commitment / id derived from a label (stands in for the Poseidon2
/// state root in production; opaque here, exactly as the Lean model keeps `commitPre`/`commitPost`
/// abstract `ℤ`).
fn root(label: &str) -> [u8; 32] {
    *blake3::hash(label.as_bytes()).as_bytes()
}

fn asset(label: &str) -> [u8; 32] {
    *blake3::hash(label.as_bytes()).as_bytes()
}

/// A permissive public cell (for the PUBLIC backbone of a mixed turn).
fn permissive_cell(key_byte: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = key_byte;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = dregg_cell::Permissions {
        send: dregg_cell::AuthRequired::None,
        receive: dregg_cell::AuthRequired::None,
        set_state: dregg_cell::AuthRequired::None,
        set_permissions: dregg_cell::AuthRequired::None,
        set_verification_key: dregg_cell::AuthRequired::None,
        increment_nonce: dregg_cell::AuthRequired::None,
        delegate: dregg_cell::AuthRequired::None,
        access: dregg_cell::AuthRequired::None,
    };
    cell
}

fn transfer_action(from: CellId, to: CellId, amount: u64) -> Action {
    Action {
        target: from,
        method: *blake3::hash(b"transfer").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// Build a tiny single-public-leg `AtomicForest` + its ledger (the PUBLIC backbone for a mixed
/// turn) and return the forest plus the live ledger.
fn public_backbone() -> (Ledger, AtomicForest) {
    let mut ledger = Ledger::new();
    let c0 = permissive_cell(1, 100);
    let c1 = permissive_cell(2, 0);
    let id0 = ledger.insert_cell(c0).unwrap();
    let id1 = ledger.insert_cell(c1).unwrap();

    let mut forest = CallForest::new();
    forest.add_root(transfer_action(id0, id1, 10));

    let af = AtomicForest::new(vec![node_id(1)], forest, vec![], id0, 0, None);
    (ledger, af)
}

// ───────────────────────────── ACCEPT ─────────────────────────────

/// **ACCEPT — an honest private leg with a binding, accepting proof is admitted.** The maintainer
/// publishes `(asset, commitPre, commitPost, jid)` + a proof built `for_leg` (binds that exact
/// statement, STARK accepting). The commit-path gate `check_private_legs_admissible` returns
/// `Ok(())`. (Lean `privLeg_real_verifies`.)
#[test]
fn private_leg_accept_binding_proof() {
    let jid = root("turn-jid-A");
    let leg = PrivateLeg::new(asset("asset-0"), root("pre-A"), root("post-A"), jid);
    let proof = PrivateLegProof::for_leg(&leg);

    // The per-leg gate verifies.
    assert!(proof.verify(&leg), "honest binding proof must verify");

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(
        jid,
        public_forest,
        vec![PrivateContribution::new(leg, proof)],
    );

    assert_eq!(
        mj.check_private_legs_admissible(),
        Ok(()),
        "mixed turn with one honest private leg must be admissible"
    );
}

/// **ACCEPT — multiple honest private legs all binding the shared jid.** Two offline maintainers
/// each contribute a binding, accepting proof for the SAME `jid`. The gate admits the whole set.
#[test]
fn private_legs_accept_multiple() {
    let jid = root("turn-jid-multi");
    let leg0 = PrivateLeg::new(asset("asset-0"), root("p0-pre"), root("p0-post"), jid);
    let leg1 = PrivateLeg::new(asset("asset-1"), root("p1-pre"), root("p1-post"), jid);
    let pc0 = PrivateContribution::new(leg0, PrivateLegProof::for_leg(&leg0));
    let pc1 = PrivateContribution::new(leg1, PrivateLegProof::for_leg(&leg1));

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(jid, public_forest, vec![pc0, pc1]);

    assert_eq!(mj.check_private_legs_admissible(), Ok(()));
}

/// **ACCEPT — a mixed turn with ZERO private legs is trivially admissible** (a pure public turn is
/// the degenerate `MixedJoint`; the private gate is vacuously satisfied).
#[test]
fn private_legs_accept_empty() {
    let jid = root("turn-jid-empty");
    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(jid, public_forest, vec![]);
    assert_eq!(mj.check_private_legs_admissible(), Ok(()));
}

// ───────────────────────────── ANTI-GHOST ─────────────────────────────

/// **ANTI-GHOST — a private leg whose proof does NOT bind the jid is REFUSED.** The maintainer
/// publishes a leg for `jid = turn`, but its proof was produced binding a DIFFERENT `jid` (a proof
/// lifted from another turn, or forged). The per-leg `verify` fails (the bound statement digest
/// differs because the jid differs), and the commit-path gate refuses the turn with
/// `PrivateProofRejected`. (Lean `privLeg_forged_rejected`: only the extractability carrier could
/// rescue an unbound proof.)
#[test]
fn private_leg_anti_ghost_proof_does_not_bind_jid() {
    let turn_jid = root("turn-jid-real");
    let other_jid = root("turn-jid-OTHER");

    // The leg consents to `turn_jid`...
    let leg = PrivateLeg::new(asset("asset-0"), root("pre"), root("post"), turn_jid);
    // ...but the proof binds a leg with a DIFFERENT jid (same asset/commitments, wrong jid).
    let wrong_jid_leg = PrivateLeg {
        jid: other_jid,
        ..leg
    };
    let forged_proof = PrivateLegProof::for_leg(&wrong_jid_leg);

    // The per-leg gate REFUSES: the proof's bound statement (over other_jid) ≠ leg's statement.
    assert!(
        !forged_proof.verify(&leg),
        "a proof binding a different jid must NOT verify for this leg"
    );

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(
        turn_jid,
        public_forest,
        vec![PrivateContribution::new(leg, forged_proof)],
    );

    // The commit-path gate refuses the whole mixed turn (all-or-none abort).
    assert_eq!(
        mj.check_private_legs_admissible(),
        Err(MixedAdmitError::PrivateProofRejected { index: 0 }),
        "mixed turn with a non-jid-binding private proof must be refused"
    );
}

/// **ANTI-GHOST — a leg consenting to the WRONG jid is refused before proof check.** Even if the
/// proof binds the leg's own (wrong) jid, the leg does not consent to THIS turn's shared id, so
/// the CG-2 binding gate rejects it with `PrivateJidMismatch`. (A leg from another turn cannot be
/// smuggled into this one.)
#[test]
fn private_leg_anti_ghost_wrong_jid_consent() {
    let turn_jid = root("turn-jid-this");
    let foreign_jid = root("turn-jid-foreign");

    // A perfectly self-consistent leg+proof — but for a DIFFERENT turn.
    let foreign_leg = PrivateLeg::new(asset("a"), root("pre"), root("post"), foreign_jid);
    let proof = PrivateLegProof::for_leg(&foreign_leg);
    assert!(
        proof.verify(&foreign_leg),
        "the foreign leg's own proof binds it"
    );

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(
        turn_jid,
        public_forest,
        vec![PrivateContribution::new(foreign_leg, proof)],
    );

    assert_eq!(
        mj.check_private_legs_admissible(),
        Err(MixedAdmitError::PrivateJidMismatch {
            index: 0,
            leg_jid: foreign_jid,
            turn_jid,
        }),
        "a leg consenting to a foreign jid must be refused"
    );
}

/// **ANTI-GHOST — a tampered commitment (conjure-value) breaks binding.** The maintainer keeps the
/// jid but swaps `commit_post` to a value its proof was not produced for (claiming a different
/// hidden post-state). The proof no longer binds, and the turn is refused. (The state-root binding
/// half of the anti-ghost: you cannot re-point a proof at a different post-state.)
#[test]
fn private_leg_anti_ghost_tampered_commitment() {
    let jid = root("turn-jid-tamper");
    let honest = PrivateLeg::new(asset("a"), root("pre"), root("post"), jid);
    let proof = PrivateLegProof::for_leg(&honest); // binds the HONEST post-root

    // Adversary publishes the same proof but a tampered post-commitment.
    let tampered = PrivateLeg {
        commit_post: root("post-TAMPERED"),
        ..honest
    };
    assert!(
        !proof.verify(&tampered),
        "a proof must not verify against a tampered commitment"
    );

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(
        jid,
        public_forest,
        vec![PrivateContribution::new(tampered, proof)],
    );
    assert_eq!(
        mj.check_private_legs_admissible(),
        Err(MixedAdmitError::PrivateProofRejected { index: 0 }),
    );
}

/// **ANTI-GHOST — a non-accepting STARK is refused even if it binds.** A proof that binds the leg's
/// exact statement but whose `stark_ok = false` (the underlying STARK rejected) is refused: the §8
/// floor requires an ACCEPTING proof, not merely a correctly-addressed one.
#[test]
fn private_leg_anti_ghost_rejecting_stark() {
    let jid = root("turn-jid-reject");
    let leg = PrivateLeg::new(asset("a"), root("pre"), root("post"), jid);
    let mut proof = PrivateLegProof::for_leg(&leg);
    proof.stark_ok = false; // the STARK did not accept

    assert!(!proof.verify(&leg), "a non-accepting STARK must not verify");

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(
        jid,
        public_forest,
        vec![PrivateContribution::new(leg, proof)],
    );
    assert_eq!(
        mj.check_private_legs_admissible(),
        Err(MixedAdmitError::PrivateProofRejected { index: 0 }),
    );
}

/// **ANTI-GHOST — the FIRST offending private leg is reported (fail-closed at index 1).** A good
/// leg followed by a forged one: the gate refuses, pinning the offender's index. Confirms the
/// all-or-none gate does not silently admit a partial set.
#[test]
fn private_legs_anti_ghost_reports_first_offender() {
    let jid = root("turn-jid-firstbad");
    let good = PrivateLeg::new(asset("a0"), root("p0pre"), root("p0post"), jid);
    let bad = PrivateLeg::new(asset("a1"), root("p1pre"), root("p1post"), jid);

    let pc_good = PrivateContribution::new(good, PrivateLegProof::for_leg(&good));
    // bad's proof binds a different statement (asset swapped) — does not bind `bad`.
    let mut bad_proof = PrivateLegProof::for_leg(&bad);
    bad_proof.bound_statement = root("unrelated-statement");
    let pc_bad = PrivateContribution::new(bad, bad_proof);

    let (_ledger, public_forest) = public_backbone();
    let mj = MixedJoint::new(jid, public_forest, vec![pc_good, pc_bad]);

    assert_eq!(
        mj.check_private_legs_admissible(),
        Err(MixedAdmitError::PrivateProofRejected { index: 1 }),
    );
}

// ───────────────────────────── state-root continuity (ChainBound) ─────────────────────────────

/// **CHAIN-BOUND ACCEPT — a continuous offline history is admitted.** A long-lived offline cell
/// publishes three turns whose roots chain: `post[i] == pre[i+1]`. `check_chain_bound` returns
/// `Ok(())`. (Mirrors `HistoryAggregation.ChainBound`.)
#[test]
fn chain_bound_accepts_continuous_history() {
    let jid = root("turn-jid-chain");
    let r0 = root("root-0");
    let r1 = root("root-1");
    let r2 = root("root-2");
    let r3 = root("root-3");
    let a = asset("a");

    let legs = vec![
        PrivateLeg::new(a, r0, r1, jid), // turn 1: r0 -> r1
        PrivateLeg::new(a, r1, r2, jid), // turn 2: r1 -> r2  (post[0] == pre[1])
        PrivateLeg::new(a, r2, r3, jid), // turn 3: r2 -> r3  (post[1] == pre[2])
    ];

    assert_eq!(check_chain_bound(&legs), Ok(()));
}

/// **CHAIN-BOUND ACCEPT — empty and singleton sequences are trivially chained.**
#[test]
fn chain_bound_accepts_trivial() {
    assert_eq!(check_chain_bound(&[]), Ok(()));
    let jid = root("j");
    let solo = vec![PrivateLeg::new(asset("a"), root("x"), root("y"), jid)];
    assert_eq!(check_chain_bound(&solo), Ok(()));
}

/// **CHAIN-BOUND REJECT — a discontinuous history is refused.** Turn 2's `commit_pre` does NOT
/// equal turn 1's `commit_post` (a forked/forged history). `check_chain_bound` reports the first
/// break with the mismatching roots. (The continuity tooth: an offline cell cannot teleport
/// between unrelated states across turns.)
#[test]
fn chain_bound_rejects_discontinuity() {
    let jid = root("turn-jid-break");
    let r0 = root("root-0");
    let r1 = root("root-1");
    let forked = root("root-FORKED");
    let r3 = root("root-3");
    let a = asset("a");

    let legs = vec![
        PrivateLeg::new(a, r0, r1, jid),     // turn 1: r0 -> r1
        PrivateLeg::new(a, forked, r3, jid), // turn 2: pre = forked ≠ r1  ⇒ BREAK at index 0
    ];

    assert_eq!(
        check_chain_bound(&legs),
        Err(ChainBreak {
            index: 0,
            expected_pre: r1,
            found_pre: forked,
        }),
    );
}

/// **CHAIN-BOUND REJECT — a break in the middle of a longer chain is found.** The first two turns
/// chain; the third forks. The break is reported at index 1 (the leg whose `post` fails to match
/// the successor's `pre`).
#[test]
fn chain_bound_rejects_mid_chain_break() {
    let jid = root("turn-jid-midbreak");
    let r0 = root("r0");
    let r1 = root("r1");
    let r2 = root("r2");
    let forked = root("r-forked");
    let r4 = root("r4");
    let a = asset("a");

    let legs = vec![
        PrivateLeg::new(a, r0, r1, jid),     // ok: post r1
        PrivateLeg::new(a, r1, r2, jid),     // ok: pre r1 == prior post; post r2
        PrivateLeg::new(a, forked, r4, jid), // BREAK at index 1: pre forked ≠ r2
    ];

    assert_eq!(
        check_chain_bound(&legs),
        Err(ChainBreak {
            index: 1,
            expected_pre: r2,
            found_pre: forked,
        }),
    );
}

// ─────────────────── full mixed turn: public 2PC commits + private gate admits ───────────────────

/// **WHOLE MIXED TURN — the public 2PC commits AND the private gate admits.** The complete
/// `MixedAdmissible` shape end-to-end: a real `Coordinator` runs the public-leg 2PC to
/// `Decision::Commit` on the shared ledger, AND the private-leg verify-gate returns `Ok(())`. The
/// turn is admissible as a whole, with the private participant contributing only its commitments +
/// proof — never its hidden state. (Lean `joint_turn_sound_with_private_legs` admissibility.)
#[test]
fn mixed_turn_public_commits_and_private_admits() {
    let jid = root("turn-jid-whole");

    // PUBLIC backbone: a single-participant forest the real 2PC commits.
    let (mut ledger, public_forest) = public_backbone();
    let (sk, pk) = keypair(1);
    let mut participant_keys = std::collections::HashMap::new();
    participant_keys.insert(node_id(1), pk);

    let mut coord = Coordinator::new(
        node_id(1),
        *blake3::hash(b"whole-turn-coord").as_bytes(),
        1, // threshold 1 of 1
        ComputronCosts::zero(),
        u64::MAX,
        participant_keys,
    );
    let prop = coord.propose(public_forest.clone()).unwrap();
    // ARM the NATIVE 2PC differential sibling BY NAME: `evaluate_votes_no_gate` has ONE body for
    // every cfg and it is the PRODUCTION fail-closed `Abort`, so a test that asserts the native
    // tally verdict through `receive_vote` says so explicitly.
    let _native = crate::atomic::NativeDifferentialArmed::new();
    let vote = Vote::yes(Vote::sign_yes(&prop.proposal_id, &public_forest.hash, &sk));
    let decision = coord.receive_vote(node_id(1), vote).unwrap();
    assert_eq!(decision, Some(Decision::Commit), "public 2PC must commit");
    // The public side actually applies to the shared ledger.
    let _commit = coord.commit(&mut ledger).expect("public commit applies");

    // PRIVATE side: a witnessless leg with a binding proof, consenting to the same jid.
    let leg = PrivateLeg::new(asset("private-asset"), root("ppre"), root("ppost"), jid);
    let mj = MixedJoint::new(
        jid,
        public_forest,
        vec![PrivateContribution::new(
            leg,
            PrivateLegProof::for_leg(&leg),
        )],
    );
    assert_eq!(
        mj.check_private_legs_admissible(),
        Ok(()),
        "the private half of the mixed turn must be admissible"
    );
}
