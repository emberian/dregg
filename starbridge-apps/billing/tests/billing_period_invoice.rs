//! # Billing, end to end — settled charges → a sealed invoice, and the 402 ceiling.
//!
//! The two verified turns of the billing plane, proven on dregg-native primitives with NO
//! new kernel effect:
//!
//!   1. **assemble-invoice-for-period** — an account's charges settle as REAL conserving
//!      `Transfer` turns (each producing a native [`TurnReceipt`]); their receipt hashes are
//!      aggregated into a per-resource invoice that re-witnesses against the receipts; and
//!      the invoice is SEALED as its own turn receipt (its `body_hash` bound into the
//!      billing cell by a verified turn, so the executor's receipt for that turn is the
//!      seal).
//!   2. **charge-under-cap** — a charge that fits under the cap is admitted (the mirrored
//!      spend advances, the value moves, Σ conserves); a charge that would exceed the cap
//!      is REFUSED BY THE EXECUTOR in-band (the `FieldLteField(spent ≤ cap)` tooth rejects
//!      the whole turn — the 402, with no value moved).
//!
//! Conservation (Σ CREDIT = 0) is asserted across the whole flow.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor,
};
use dregg_cell::{Cell, CellId, EFFECT_MINT, Permissions};

use starbridge_billing::{
    BillableResource, BillingPeriod, CAP_SLOT, Invoice, PROVIDER_SLOT, RateCard, SPENT_SLOT,
    START_SLOT, SettleReceipt, UsageEvent, build_charge_action, build_seal_invoice_action,
    cell_tag, field_from_u64, sealed_invoice_digest,
};

/// The shared credit asset every value cell denominates in (its `token_id`).
const CREDIT: [u8; 32] = [0xCDu8; 32];
/// The billing-period start block.
const START: i64 = 1_000;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn credit_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37).wrapping_add(1);
    let mut cell = Cell::with_balance(pk, CREDIT, 0);
    cell.permissions = open_permissions();
    cell
}

fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

fn per_asset_supply(exec: &EmbeddedExecutor, asset: &[u8; 32]) -> i128 {
    exec.with_ledger_mut(|ledger| {
        ledger
            .iter()
            .filter(|(_, c)| c.token_id() == asset)
            .map(|(_, c)| c.state.balance() as i128)
            .sum()
    })
}

fn balance_of(exec: &EmbeddedExecutor, cell: CellId) -> i64 {
    exec.with_ledger_mut(|ledger| ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
}

fn spent_slot(exec: &EmbeddedExecutor, cell: CellId) -> u64 {
    let state = exec.cell_state(cell).expect("cell state");
    let f = state.fields[SPENT_SLOT as usize];
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Build a fully-wired World: an operator that mints CREDIT and controls a funded billing
/// cell (cap `cap`, prepaid `prepaid`) + a provider cell. Returns
/// `(operator, exec, billing_id, provider_id)`.
fn world(cap: i64, prepaid: u64) -> (AppCipherclerk, EmbeddedExecutor, CellId, CellId) {
    let operator = AppCipherclerk::new(AgentCipherclerk::new(), [0x42u8; 32]);
    let exec = EmbeddedExecutor::new(&operator, "default");
    let operator_cell = operator.cell_id();

    let provider = credit_cell(1);
    let billing = credit_cell(2);
    let provider_id = provider.id();
    let billing_id = billing.id();
    exec.ensure_cell(provider).expect("provider co-placed");
    exec.ensure_cell(billing).expect("billing co-placed");

    let well_id = derived_well_id(&CREDIT);

    exec.with_ledger_mut(|ledger| {
        let op = ledger
            .get_mut(&operator_cell)
            .expect("operator cell exists");
        op.capabilities
            .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
            .expect("grant mint-cap over CREDIT well");
        op.capabilities
            .grant(billing_id, AuthRequired::None)
            .expect("grant billing access");
        op.capabilities
            .grant(provider_id, AuthRequired::None)
            .expect("grant provider access");
    });

    // Fund the billing cell with a prepaid balance (a mint conserves).
    let mint = operator.make_action(
        billing_id,
        "fund_billing",
        vec![Effect::Mint {
            target: billing_id,
            slot: 0,
            amount: prepaid,
        }],
    );
    exec.submit_action(&operator, mint)
        .expect("fund the billing cell");
    assert_eq!(balance_of(&exec, billing_id), prepaid as i64);
    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "Σ CREDIT = 0 after funding"
    );

    // Install the billing program + seal the scalar economics (cap/provider/start/spent=0)
    // directly into the ledger. The executor re-enforces the invariants on every turn.
    exec.install_program(billing_id, starbridge_billing::billing_cell_program());
    exec.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&billing_id).expect("billing cell");
        cell.state.set_field(SPENT_SLOT as usize, field_from_u64(0));
        cell.state
            .set_field(CAP_SLOT as usize, field_from_u64(cap.max(0) as u64));
        cell.state
            .set_field(PROVIDER_SLOT as usize, cell_tag(provider_id));
        cell.state
            .set_field(START_SLOT as usize, field_from_u64(START as u64));
    });

    (operator, exec, billing_id, provider_id)
}

#[test]
fn an_invoice_aggregates_its_period_settle_receipts_and_seals() {
    let card = RateCard::default();
    let (operator, exec, billing_id, provider_id) = world(1_000, 1_000);

    // Three settled charges for alice's account, each a REAL conserving Transfer whose
    // TurnReceipt is the settle-receipt anchor a line will trace to.
    let charges: [(BillableResource, &str, u64); 3] = [
        (BillableResource::Compute, "lease-7", 20), // 20 steps × 1
        (BillableResource::Bandwidth, "blog", 3),   // 3 MiB × 5
        (BillableResource::Site, "blog", 2),        // op 10 + 2 KiB × 1
    ];

    let mut events: Vec<UsageEvent> = Vec::new();
    let mut running_spent: i64 = 0;
    let mut settled_hashes: Vec<[u8; 32]> = Vec::new();
    for (period_ord, (resource, subject, qty)) in charges.into_iter().enumerate() {
        let amount = card.cost(resource, qty);
        running_spent += amount;

        // The charge settles: SetField(spent) + Transfer(billing → provider), a real turn.
        let action = build_charge_action(
            &operator,
            billing_id,
            provider_id,
            running_spent,
            amount as u64,
        );
        let receipt = exec
            .submit_action(&operator, action)
            .expect("an under-cap charge settles");
        settled_hashes.push(receipt.receipt_hash());

        // The settled charge becomes a receipt-anchored usage event.
        events.push(UsageEvent::settled(
            "alice",
            resource,
            subject,
            qty,
            card.unit_rate_for(resource),
            card.flat_for(resource),
            SettleReceipt::new(receipt.receipt_hash(), "CREDIT", amount, period_ord as i64),
        ));

        assert_eq!(
            per_asset_supply(&exec, &CREDIT),
            0,
            "Σ CREDIT = 0 after each charge settles"
        );
    }

    // The provider received exactly what settled; the account spent it.
    let total_settled = 20 + 15 + 12;
    assert_eq!(balance_of(&exec, provider_id), total_settled);
    assert_eq!(balance_of(&exec, billing_id), 1_000 - total_settled);

    // ── assemble-invoice-for-period: aggregate the period's settle receipts. ──
    let inv = Invoice::assemble(
        "alice",
        BillingPeriod::new("2026-06", START, START + 1_000),
        "CREDIT",
        &events,
        "t0",
    );
    assert_eq!(inv.line_items.len(), 3, "one line per resource");
    assert_eq!(
        inv.total_units, total_settled,
        "the bill totals what settled"
    );
    assert_eq!(
        inv.verify_against_receipts(),
        Ok(()),
        "every line traces to its settled turn receipts"
    );

    // Every line's anchor is one of the REAL settled turn receipts (no phantom lines).
    let mut invoice_hashes: Vec<[u8; 32]> = inv
        .line_items
        .iter()
        .flat_map(|l| l.receipts.iter().map(|r| r.receipt_hash))
        .collect();
    invoice_hashes.sort();
    settled_hashes.sort();
    assert_eq!(
        invoice_hashes, settled_hashes,
        "lines trace to the real receipts"
    );

    // ── seal the invoice as ITS OWN turn receipt. ──
    let seal_action = build_seal_invoice_action(&operator, billing_id, &inv);
    let seal_receipt = exec
        .submit_action(&operator, seal_action)
        .expect("the invoice seals into the billing cell");
    let sealed = inv.clone().seal(seal_receipt.receipt_hash());

    // The seal turn bound the invoice body hash into the cell — a light client sees it.
    let cell = exec
        .with_ledger_mut(|l| l.get(&billing_id).cloned())
        .expect("billing cell");
    assert_eq!(
        sealed_invoice_digest(&cell),
        Some(inv.body_hash()),
        "the sealed invoice digest is committed on the cell"
    );
    assert!(sealed.reseals(), "the sealed invoice re-derives");

    // A tampered bill re-hashes to a different digest and no longer matches the seal.
    let mut forged = sealed.clone();
    forged.invoice.total_units += 1;
    assert!(!forged.reseals(), "a tampered bill fails the re-derive");

    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "Σ CREDIT = 0 across the whole billing flow"
    );
}

#[test]
fn an_over_cap_charge_is_refused_in_band() {
    let (operator, exec, billing_id, provider_id) = world(100, 1_000);

    // A charge that fits under the 100 cap is admitted (spent advances, value moves).
    let under = build_charge_action(&operator, billing_id, provider_id, 60, 60);
    exec.submit_action(&operator, under)
        .expect("an under-cap charge settles");
    assert_eq!(
        spent_slot(&exec, billing_id),
        60,
        "the mirrored spend advanced"
    );
    assert_eq!(balance_of(&exec, provider_id), 60, "the value moved");

    // A charge that would push spent to 110 (> the 100 cap) is REFUSED BY THE EXECUTOR:
    // the FieldLteField(spent ≤ cap) tooth rejects the whole turn — the 402, in-band.
    let over = build_charge_action(&operator, billing_id, provider_id, 110, 50);
    assert!(
        exec.submit_action(&operator, over).is_err(),
        "an over-cap charge is refused by the executor (the 402)"
    );

    // Nothing moved on the refusal: spend + provider balance unchanged.
    assert_eq!(
        spent_slot(&exec, billing_id),
        60,
        "the refused charge left spend untouched"
    );
    assert_eq!(
        balance_of(&exec, provider_id),
        60,
        "no value moved on the 402"
    );

    // Exactly filling the cap (spent → 100) is admitted; the next unit is refused.
    let fill = build_charge_action(&operator, billing_id, provider_id, 100, 40);
    exec.submit_action(&operator, fill)
        .expect("a cap-filling charge settles");
    assert_eq!(spent_slot(&exec, billing_id), 100);
    let past = build_charge_action(&operator, billing_id, provider_id, 101, 1);
    assert!(
        exec.submit_action(&operator, past).is_err(),
        "a charge one unit past the cap is refused"
    );

    assert_eq!(
        per_asset_supply(&exec, &CREDIT),
        0,
        "Σ CREDIT = 0 across the capped charges"
    );
}
