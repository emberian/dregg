//! # Integration teeth for the edge-identity mandate — every claim a real executor
//! turn, never a mock.
//!
//! The mandate cell is BORN from its [`FactoryDescriptor`](starbridge_edge_mandate::mandate_factory_descriptor)
//! (so the executor installs the life-of-mandate `StateConstraint`s at birth FOR
//! LIFE), then driven through the verified executor:
//!
//!   * **enrol** is a witnessed turn — the `WriteOnce` identity / account / budget /
//!     caps-digest binds admit from zero; the record is mirrored into the committed
//!     heap;
//!   * a **spend within the sub-budget** commits — the meter draws down;
//!   * a **spend past the sub-budget** is REFUSED by the executor's
//!     `AffineLe(spent ≤ budget)` gate, in the fire path — the durable meter is
//!     unmoved (fail-closed);
//!   * **revoke** is a witnessed turn — the kill switch flips and the
//!     `authorized_keys` adapter line goes dark;
//!   * the `authorized_keys` line is a pure function of the LIVE cell throughout.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, EmbeddedExecutor,
};
use dregg_cell::FactoryCreationParams;

use starbridge_edge_mandate::{
    CapMandate, DEFAULT_ATTACH_BIN, EnrolRequest, MANDATE_FACTORY_VK, authorized_keys_line,
    budget_of, build_enrol_action, build_revoke_action, build_spend_action, caps_of, epoch_of,
    is_revoked, mandate_child_program_vk, mandate_factory_descriptor, mint_mandate, mirror_record,
    seed_mandate, spent_of,
};

const ALICE_KEY: &str =
    "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIAlIcEoZ1ENESf0Kk6zc8alICEforAlIcEkeyblob alice@laptop";

/// Build a born mandate cell driven by `cclerk`/`exec`, returning its CellId.
/// Mirrors the proven agent-orchestration / swarm-orchestration factory-birth
/// pattern: deploy the factory, fund the agent's creation budget, birth the cell,
/// then grant the agent a `Signature` cap over it so it can drive its turns.
fn born_mandate(cclerk: &AppCipherclerk, exec: &EmbeddedExecutor, seed: &[u8]) -> CellId {
    exec.deploy_factory(mandate_factory_descriptor());
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&agent) {
            c.state.set_balance(100_000_000);
        }
    });
    let owner = cclerk.public_key().0;
    let token = *blake3::hash(seed).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(mandate_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(MANDATE_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("mandate cell birth commits");
    let cell = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|l| {
        if let Some(a) = l.get_mut(&agent) {
            a.capabilities.grant(cell, AuthRequired::Signature);
        }
    });
    cell
}

fn budget_live(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let c = exec.with_ledger_mut(|l| l.get(&cell).cloned()).unwrap();
    budget_of(&c)
}
fn spent_live(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let c = exec.with_ledger_mut(|l| l.get(&cell).cloned()).unwrap();
    spent_of(&c)
}
fn epoch_live(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let c = exec.with_ledger_mut(|l| l.get(&cell).cloned()).unwrap();
    epoch_of(&c)
}

#[test]
fn enrol_spend_refuse_revoke_as_witnessed_turns() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let cell = born_mandate(&cclerk, &exec, b"alice");

    // The operator's held grant: fs + a scoped GitHub egress + a scoped pay vendor,
    // underwriting up to $50.00.
    let held = CapMandate::held(
        ["fs", "http:api.github.com", "pay:openai"],
        5000,
        "operator",
    );
    // Enrol alice with a 500-cent sub-budget and a subset of the held caps.
    let req = EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "fs,http:api.github.com");
    let minted = mint_mandate(&held, &req).expect("valid mandate");
    assert!(minted.le(&held), "granted ⊑ held");

    // ── ENROL as a witnessed turn — the WriteOnce binds admit from zero. ──
    let enrol_turn = build_enrol_action(&cclerk, cell, &minted, &req.ssh_pubkey);
    exec.submit_action(&cclerk, enrol_turn)
        .expect("the enrol turn commits");
    // Mirror the deploy-facing enrolment record into the committed heap.
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&cell) {
            mirror_record(c, &minted, &req);
        }
    });
    assert_eq!(budget_live(&exec, cell), 500, "the sealed sub-budget");
    assert_eq!(spent_live(&exec, cell), 0, "nothing spent yet");

    // ── A SPEND within the sub-budget commits — the meter draws down. ──
    let ep = epoch_live(&exec, cell);
    let s1 = build_spend_action(&cclerk, cell, 200, 200, ep + 1);
    exec.submit_action(&cclerk, s1)
        .expect("an in-budget spend commits");
    assert_eq!(spent_live(&exec, cell), 200);

    // ── A SPEND past the sub-budget is REFUSED by the executor's AffineLe gate. ──
    let ep = epoch_live(&exec, cell);
    // 200 already spent; a draw to 600 would breach the 500 ceiling.
    let over = build_spend_action(&cclerk, cell, 600, 400, ep + 1);
    assert!(
        exec.submit_action(&cclerk, over).is_err(),
        "an over-budget spend is refused by AffineLe(spent ≤ budget), in the fire path"
    );
    assert_eq!(
        spent_live(&exec, cell),
        200,
        "the refused spend moved nothing (fail-closed)"
    );

    // ── The authorized_keys line is a pure function of the LIVE cell. ──
    let live = exec.with_ledger_mut(|l| l.get(&cell).cloned()).unwrap();
    let line = authorized_keys_line(&live, DEFAULT_ATTACH_BIN).expect("a live mandate → a line");
    assert!(line.contains("dregg-agent attach --account dga1_alice --budget 500"));
    assert!(line.contains("--caps fs,http:api.github.com"));
    assert!(line.contains(",restrict,pty "));
    assert!(line.ends_with("alice@laptop"));

    // ── REVOKE as a witnessed turn — the line goes dark. ──
    let ep = epoch_live(&exec, cell);
    let rev = build_revoke_action(&cclerk, cell, ep + 1);
    exec.submit_action(&cclerk, rev)
        .expect("the revoke turn commits");
    let after = exec.with_ledger_mut(|l| l.get(&cell).cloned()).unwrap();
    assert!(is_revoked(&after), "the mandate is revoked");
    assert!(
        authorized_keys_line(&after, DEFAULT_ATTACH_BIN).is_none(),
        "a revoked mandate emits no attach line"
    );
}

#[test]
fn seed_mandate_installs_the_program_and_enrols_the_genesis() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [7u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let held = CapMandate::held(["fs", "http:api.github.com"], 1000, "operator");
    let minted = seed_mandate(
        &exec,
        &held,
        &EnrolRequest::new("dga1_x", ALICE_KEY, 400, "fs"),
    )
    .expect("seed enrols");
    assert_eq!(minted.budget, 400);
    let cell = exec
        .with_ledger_mut(|l| l.get(&exec.cell_id()).cloned())
        .unwrap();
    assert_eq!(budget_of(&cell), 400);
    assert_eq!(spent_of(&cell), 0);
    assert_eq!(caps_of(&cell).as_deref(), Some("fs"));
}
