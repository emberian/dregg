//! The STANDING gate on the REAL executor path — the mission's second required
//! tooth: *standing flips only via the governance turn, not a self-write.*
//!
//! Mirrors `starbridge-identity/tests/deos_seam.rs`: the seeded account cell carries
//! the full [`starbridge_guard::guard_program`] (`Cases`, with the
//! `SenderAuthorized(PublicRoot { GOVERNANCE_ROOT_SLOT })` gate on `set_standing`),
//! and the `EmbeddedExecutor`'s default registry is the REAL Poseidon2-STARK
//! `MerkleMembership` verifier. So:
//!
//!   - a WITNESSED `set_standing` by the governance authority (the firing signer,
//!     seeded into `GOVERNANCE_ROOT`) COMMITS and flips the standing — the governance
//!     turn is real;
//!   - an UNWITNESSED `set_standing` fails CLOSED at the real verifier — a bare
//!     self-write can never present a governance member's proof;
//!   - a `set_standing` whose signer is NOT in `GOVERNANCE_ROOT` (a foreign authority
//!     seeded) is REFUSED by the real STARK even carrying the signer's own proof — a
//!     non-governance subject can never move its own standing.
//!
//! Meanwhile the SUBJECT still meters its OWN quota (`consume_quota` carries no sender
//! gate), so the two rights tiers are cleanly separated on the live executor.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, field_from_u64};
use starbridge_guard::{
    CEILING_SLOT, CONSUMED_SLOT, GOVERNANCE_ROOT_SLOT, STANDING_GOOD, STANDING_SLOT,
    STANDING_SUSPENDED, SUBJECT_SLOT, Standing, build_consume_action, build_set_standing_action,
    governance_root_for, guard_program, seed_subject, subject_id_field,
};

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

/// (a) THE GOVERNANCE TURN: a witnessed `set_standing` by the seeded governance
/// authority COMMITS and flips the standing good → suspended, THROUGH the real
/// `SenderAuthorized` verifier (the membership proof attached). And the subject can
/// still meter its own quota first — the two rights tiers on one live account.
#[test]
fn a_witnessed_governance_set_standing_commits_and_flips_standing() {
    let (cclerk, executor) = agent(0x71);
    // Seeds the full guard_program + config, with the firing signer as the sole
    // governance authority (GOVERNANCE_ROOT = single_member_authorized_root(signer)).
    seed_subject(&executor, &cclerk, "subject-x", 4);
    let account = cclerk.cell_id();

    // The SUBJECT meters one quota unit first (consume carries no sender gate) — live
    // truth that the subject self-services under its ceiling.
    executor
        .submit_action(&cclerk, build_consume_action(&cclerk, account, 0))
        .expect("the subject meters its own quota (no governance gate on consume)");
    assert_eq!(
        executor.cell_state(account).unwrap().fields[CONSUMED_SLOT as usize],
        field_from_u64(1),
        "the subject advanced its own meter"
    );

    // The GOVERNANCE authority suspends the subject: a witnessed `set_standing` turn
    // (the membership proof attached) passes the real `SenderAuthorized` STARK.
    executor
        .submit_action(
            &cclerk,
            build_set_standing_action(&cclerk, account, Standing::Suspended, "confirmed abuse"),
        )
        .expect("a witnessed governance set_standing commits through the real verifier");
    assert_eq!(
        executor.cell_state(account).unwrap().fields[STANDING_SLOT as usize],
        field_from_u64(STANDING_SUSPENDED),
        "the governance turn flipped standing good → suspended"
    );
}

/// (b) THE SELF-WRITE IS REFUSED: an UNWITNESSED `set_standing` (a bare self-write,
/// no membership proof) fails CLOSED at the real `SenderAuthorized` verifier — even
/// though the signer IS the seeded governance authority, the absent proof refuses.
/// The proof, not the signer identity alone, does the work.
#[test]
fn an_unwitnessed_set_standing_is_refused_the_self_write_fails_closed() {
    let (cclerk, executor) = agent(0x71);
    seed_subject(&executor, &cclerk, "subject-x", 4);
    let account = cclerk.cell_id();

    // A structurally-valid standing flip with NO membership witness attached.
    let bare = cclerk.make_action(
        account,
        "set_standing",
        vec![dregg_app_framework::Effect::SetField {
            cell: account,
            index: STANDING_SLOT as usize,
            value: field_from_u64(STANDING_SUSPENDED),
        }],
    );
    let refused = executor.submit_action(&cclerk, bare);
    assert!(
        refused.is_err(),
        "an unwitnessed set_standing must fail closed under the real verifier"
    );
    let msg = format!("{:?}", refused.unwrap_err()).to_lowercase();
    assert!(
        msg.contains("senderauthorized")
            || msg.contains("membership")
            || msg.contains("witness")
            || msg.contains("program"),
        "the executor refuses on the SenderAuthorized membership tooth, got: {msg}"
    );

    // The standing never moved — the refused self-write committed nothing (anti-ghost).
    assert_eq!(
        executor.cell_state(account).unwrap().fields[STANDING_SLOT as usize],
        field_from_u64(STANDING_GOOD),
        "the refused self-write left standing at good"
    );
}

/// (c) A NON-GOVERNANCE SIGNER CANNOT MOVE STANDING: with a FOREIGN governance
/// authority seeded into `GOVERNANCE_ROOT`, a `set_standing` by the subject — carrying
/// the subject's OWN membership proof — is REFUSED by the real STARK, because the
/// subject's leaf does not reach the foreign root. A subject that is not the
/// governance authority can never move its own standing.
#[test]
fn a_non_governance_signer_cannot_move_standing() {
    let (cclerk, executor) = agent(0x72);
    let account = cclerk.cell_id();

    // Seed manually: the full guard_program, but GOVERNANCE_ROOT names a FOREIGN
    // authority (NOT the firing signer).
    let foreign_authority = [0xEEu8; 32];
    executor.install_program(account, guard_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&account) {
            c.state.set_field(CEILING_SLOT as usize, field_from_u64(4));
            c.state
                .set_field(SUBJECT_SLOT as usize, subject_id_field("subject-x"));
            c.state.set_field(
                GOVERNANCE_ROOT_SLOT as usize,
                governance_root_for(&foreign_authority),
            );
            c.state.set_field(CONSUMED_SLOT as usize, field_from_u64(0));
            c.state
                .set_field(STANDING_SLOT as usize, field_from_u64(STANDING_GOOD));
        }
    });

    // The subject signs a witnessed set_standing — but its proof is against ITS OWN
    // pubkey, which is not the foreign governance root.
    let refused = executor.submit_action(
        &cclerk,
        build_set_standing_action(
            &cclerk,
            account,
            Standing::Suspended,
            "self-takedown attempt",
        ),
    );
    assert!(
        refused.is_err(),
        "a set_standing whose signer is not in GOVERNANCE_ROOT must be refused by the real STARK"
    );

    // The standing never moved.
    assert_eq!(
        executor.cell_state(account).unwrap().fields[STANDING_SLOT as usize],
        field_from_u64(STANDING_GOOD),
        "the non-governance self-takedown left standing at good"
    );
}
