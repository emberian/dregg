//! Factory-BIRTH executor tests: the canonical way a subject-account (guard) cell
//! comes alive, and the CONSUME-CEILING tooth on the real executor path.
//!
//! Mirrors `starbridge-tool-access-delegation/tests/factory_birth.rs`: the descriptor
//! is born empty, the `constitute` turn binds SUBJECT/CEILING/GOVERNANCE_ROOT from
//! zero under `WriteOnce`, frozen thereafter, and the born cell carries the
//! descriptor's `state_constraints` FOR LIFE. These tests drive the full lane:
//!
//!   1. `deploy_factory(guard_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn committed via `submit_turn`,
//!   3. the born cell carries the descriptor's flat caveats,
//!   4. CONSTITUTE then the full granted budget of CONSUMEs are ACCEPTED,
//!   5. **the over-ceiling consume is REFUSED IN-BAND** (the `402`/`429` shape — the
//!      `FieldLteField(consumed <= ceiling)` installed at birth), and a counter
//!      rollback (`Monotonic`) and a ceiling raise (`WriteOnce`) are REFUSED.
//!
//! This is the mission's first required tooth on the real submission path: *a subject
//! over its rate ceiling is refused.*

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_guard::{
    CEILING_SLOT, CONSUMED_SLOT, GUARD_FACTORY_VK, build_constitute_action, build_consume_action,
    governance_root, guard_child_program_vk, guard_factory_descriptor,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x67u8; 32])
}

/// Deploy the guard factory and birth a subject-account cell from it through the
/// executor. Returns the born cell's id.
fn birth_account_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(guard_factory_descriptor());

    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(guard_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(GUARD_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("account-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Birth → CONSTITUTE (ACCEPT: subject/ceiling/governance-root bound from zero) →
/// three metered consumes (ACCEPT: the full granted budget) → a fourth consume
/// (REFUSE: over-ceiling, `consumed <= ceiling` installed at birth — the CEILING
/// TOOTH, the in-band `402`/`429`).
#[test]
fn factory_born_account_meters_the_budget_and_refuses_over_ceiling() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let account = birth_account_cell(&exec, &cclerk, b"subject-account-1");

    // The born cell carries the descriptor caveats as its program.
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&account)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born account must carry a CellProgram");

    // ACCEPT: constitute binds SUBJECT / CEILING / GOVERNANCE_ROOT (ceiling 3).
    exec.submit_action(
        &cclerk,
        build_constitute_action(&cclerk, account, "subject-x", 3, governance_root(&cclerk)),
    )
    .expect("constitute must commit on the factory-born cell");

    let ceiling = exec.with_ledger_mut(|ledger| {
        ledger.get(&account).unwrap().state.fields[CEILING_SLOT as usize]
    });
    assert_eq!(ceiling, field_from_u64(3), "constitute binds the ceiling");

    // ACCEPT: the three granted consumes (counter 0→1→2→3).
    for prev in 0u64..3 {
        exec.submit_action(&cclerk, build_consume_action(&cclerk, account, prev))
            .unwrap_or_else(|e| panic!("consume {} must commit: {e}", prev + 1));
    }

    // REFUSE: the fourth consume overruns the granted ceiling (4 > 3) — IN-BAND.
    let err = exec
        .submit_action(&cclerk, build_consume_action(&cclerk, account, 3))
        .expect_err("the over-ceiling consume must be refused — the CEILING TOOTH");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("lte") || msg.contains("field") || msg.contains("program"),
        "refusal must cite the consumed ≤ ceiling budget, got: {msg}"
    );

    // ...and the metered counter survives the refused overrun.
    let consumed = exec.with_ledger_mut(|ledger| {
        ledger.get(&account).unwrap().state.fields[CONSUMED_SLOT as usize]
    });
    assert_eq!(consumed, field_from_u64(3));
}

/// Birth → constitute → consume once → counter rollback (REFUSE, `Monotonic`: a
/// subject can never roll the meter back to forge head-room) and ceiling raise
/// (REFUSE, `WriteOnce`: the granted ceiling is frozen at constitute).
#[test]
fn factory_born_account_refuses_meter_rollback_and_ceiling_raise() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let account = birth_account_cell(&exec, &cclerk, b"subject-account-2");

    exec.submit_action(
        &cclerk,
        build_constitute_action(&cclerk, account, "subject-x", 3, governance_root(&cclerk)),
    )
    .expect("constitute must commit");
    exec.submit_action(&cclerk, build_consume_action(&cclerk, account, 0))
        .expect("first consume must commit");

    // REFUSE: rolling the meter back 1 → 0.
    let rollback = cclerk.make_action(
        account,
        "consume_quota",
        vec![Effect::SetField {
            cell: account,
            index: CONSUMED_SLOT as usize,
            value: field_from_u64(0),
        }],
    );
    let err = exec
        .submit_action(&cclerk, rollback)
        .expect_err("meter rollback must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite Monotonic, got: {msg}"
    );

    // REFUSE: raising the granted ceiling 3 → 100.
    let raise = cclerk.make_action(
        account,
        "constitute",
        vec![Effect::SetField {
            cell: account,
            index: CEILING_SLOT as usize,
            value: field_from_u64(100),
        }],
    );
    let err = exec
        .submit_action(&cclerk, raise)
        .expect_err("ceiling raise must be refused by WriteOnce");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );
}
