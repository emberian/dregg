//! # starbridge-billing — invoices, spend caps, and estimation, with NO new primitive.
//!
//! A customer-facing **billing plane** for the dregg value layer, built entirely by
//! composing capacities the substrate already proves — the same discipline the sibling
//! `starbridge-apps/execution-lease` follows. Nothing here meters, mints, or invents a
//! kernel effect; billing is a set of VIEWS and CEILINGS over settled turns:
//!
//!   * **An invoice is an aggregation VIEW over settled turn receipts** ([`invoice`]) —
//!     an account's settled charges over a billing period, grouped into per-resource line
//!     items (`quantity × rate = amount`), each line carrying the **settle-receipt hash**
//!     of the turns it was billed from ([`SettleReceipt`]). The bill re-witnesses against
//!     its receipts ([`Invoice::verify_against_receipts`]) and is sealed as ITS OWN turn
//!     receipt: [`build_seal_invoice_action`] binds the invoice's canonical
//!     [`Invoice::body_hash`] into the billing cell, so the executor's [`dregg_app_framework::TurnReceipt`] for
//!     that turn is the invoice's tamper-evident seal.
//!   * **A spend cap is an allowance ceiling cell** ([`cap`], on
//!     `cell/src/allowance.rs`) — an account may be charged at most `cap` per period. An
//!     over-cap charge is **refused by the executor**: [`cap_invariants`] installs a
//!     `FieldLteField(spent ≤ cap)` tooth, so a charge turn that would push the mirrored
//!     [`SPENT_SLOT`] over [`CAP_SLOT`] is rejected in-band — the **402 (Payment
//!     Required)** shape, with no value moved.
//!   * **An estimate is a pure function over a rate card** ([`estimate`]) — a total
//!     function, no cell/turn/receipt; the `estimate` read seam the service names
//!     `Serviced`.
//!   * **The recurring half rides the standing-obligation capacity** ([`recurring`], on
//!     `cell/src/obligation_standing.rs`) — a fixed periodic fee, discharged once per
//!     period, lapsing on a missed period.
//!
//! This ports the LOGIC of a prior imperative billing module (its `invoice` / `limits` /
//! `estimate` / `usage` files) onto the native cells; the prior module's own bespoke
//! receipt chain and replenishing-budget cell are replaced by the native turn receipt and
//! the native allowance capacity.
//!
//! ## The four axes (the unified starbridge-app template)
//!
//!   * the verified core — the [`FactoryDescriptor`] + the [`billing_cell_program`] (this
//!     file): the `WriteOnce` economics + the `Monotonic`/`FieldLteField` spend-cap teeth
//!     the executor re-enforces on every touching turn;
//!   * the SERVICE-CELL `invoke()` front door ([`service`]): a typed `InterfaceDescriptor`
//!     (`charge` / `seal` / `estimate` / `status`);
//!   * the deos-view CARD ([`card`]): the billing dashboard as a `deos.ui.*` tree;
//!   * the deos surface — the composed [`DeosApp`] ([`billing_app`] / [`register_deos`]).
//!
//! ## Honest gaps (what this is, and is not)
//!
//! The spend-cap **ceiling** (`FieldLteField(spent ≤ cap)`) and the value **move** (a
//! conserving `Transfer`) are REAL verified turns the executor enforces + the kernel's
//! per-asset Σδ=0 conserves. The allowance heap ledger and the invoice `body_hash` mirror
//! are executor-side / cell-committed steps (the same named in-circuit `SpendAllowance` /
//! sealed-digest seam the allowance + obligation capacities describe): a re-executing
//! validator holding the cell + terms witnesses every forge; the light-client batch
//! circuit binding is the named next slice, not forged from the app layer.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, InspectorDescriptor, InvokeAuthority, InvokeRefused, Payable,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, Turn,
    canonical_program_vk, hex_encode_32, symbol,
};
pub use dregg_app_framework::{FieldElement, field_from_u64};

use dregg_cell::Cell;
use dregg_cell::allowance::{
    AllowanceError, AllowanceState, AllowanceTerms, Spend, open_allowance, spend,
};

/// The spend cap on the proven rate-limited-allowance capacity (`cell/src/allowance.rs`).
pub mod cap;
/// The deos-view CARD: the billing dashboard as a renderer-independent view-tree.
pub mod card;
/// Cost estimation — a pure function over a rate card.
pub mod estimate;
/// The invoice: an aggregation view over settled turn receipts, sealed as a turn receipt.
pub mod invoice;
/// The recurring half — a periodic fee on the standing-obligation capacity.
pub mod recurring;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()` dispatch.
pub mod service;
/// The billing source layer: rate card, resource taxonomy, settle-receipt-anchored usage.
pub mod usage;

pub use cap::{CapError, PERIOD_WINDOW_BLOCKS, SpendCap, SpendDecision};
pub use estimate::{Estimate, EstimateLine, ResourceDeclaration, estimate};
pub use invoice::{BillingPeriod, Invoice, InvoiceError, LineItem, SealedInvoice, invoices_for};
pub use recurring::{RecurringBill, RecurringError, RecurringPlan};
pub use usage::{BillableResource, RateCard, SettleReceipt, UsageEvent};

// =============================================================================
// Slot layout (the billing cell) — the program-enforced scalars
// =============================================================================

/// Slot 0 — `spent`. The value charged against the account within the current billing
/// period. `Monotonic` (a charge never rewinds spend to fake headroom) and bounded by the
/// cap (`FieldLteField(spent ≤ cap)`). Mirrors the committed allowance `spent_this_epoch`.
pub const SPENT_SLOT: u8 = 0;
/// Slot 1 — `cap`. The per-period spend ceiling (big-endian u64). `WriteOnce` (the cap is
/// sealed at open — it cannot be silently raised on a live account). The right operand of
/// the `FieldLteField(spent ≤ cap)` tooth.
pub const CAP_SLOT: u8 = 1;
/// Slot 2 — `provider`. The provider/beneficiary cell tag (charges are paid to it).
/// `WriteOnce`.
pub const PROVIDER_SLOT: u8 = 2;
/// Slot 3 — `period_start`. The block at which the billing period begins. `WriteOnce`.
pub const START_SLOT: u8 = 3;
/// Slot 4 — `invoice_digest`. The canonical [`Invoice::body_hash`] of the latest sealed
/// invoice — the on-cell anchor a customer re-derives to re-witness the seal. Unconstrained
/// (a new invoice seals each period).
pub const INVOICE_DIGEST_SLOT: u8 = 4;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK the provider publishes for billing-account cells.
pub const BILLING_FACTORY_VK: [u8; 32] = *b"starbridge-billing-account-fact!";

/// Default per-epoch slot-creation budget (how many billing accounts the provider issues).
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Default demo spend cap (in the account's asset).
pub const DEFAULT_CAP: u64 = 1_000;
/// Default demo billing-period start block.
pub const DEFAULT_START: i64 = 1_000;

// =============================================================================
// Field helpers
// =============================================================================

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`]).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A field tag for a cell id (its raw 32 bytes) — used to pin the provider into
/// [`PROVIDER_SLOT`].
pub fn cell_tag(cell: CellId) -> FieldElement {
    let mut f = [0u8; 32];
    f.copy_from_slice(cell.as_bytes());
    f
}

// =============================================================================
// The verified core — CellProgram + FactoryDescriptor
// =============================================================================

/// The **spend-cap invariants** the executor re-enforces on every touching turn:
///
///   * `WriteOnce` on `CAP` / `PROVIDER` / `START` — the account economics are sealed at
///     open; a live account cannot be silently re-capped or re-pointed;
///   * `Monotonic` on `SPENT` — accrued spend only moves FORWARD within a period (a charge
///     cannot rewind spend to fake headroom);
///   * `FieldLteField(SPENT ≤ CAP)` — **the ceiling**: a charge turn that would push the
///     accrued spend over the cap is REFUSED in-band (the 402 shape).
pub fn cap_invariants() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce { index: CAP_SLOT },
        StateConstraint::WriteOnce {
            index: PROVIDER_SLOT,
        },
        StateConstraint::WriteOnce { index: START_SLOT },
        StateConstraint::Monotonic { index: SPENT_SLOT },
        StateConstraint::FieldLteField {
            left_index: SPENT_SLOT,
            right_index: CAP_SLOT,
        },
    ]
}

/// The billing cell program: an `Always` case carrying [`cap_invariants`] (the economics +
/// spend-cap teeth re-enforced on EVERY touching turn — including the `FieldLteField`
/// ceiling on a `charge`, and the no-op-admitting monotonicity on a `seal`). A pure
/// invariants program, so every operation — `open` / `charge` / `seal` — is admitted as
/// long as the invariants hold.
pub fn billing_cell_program() -> CellProgram {
    CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: cap_invariants(),
    }])
}

/// The spend-cap invariants as a flat `Predicate` program — installed on a seeded billing
/// cell so the deos fires re-enforce them.
pub fn billing_invariants_program() -> CellProgram {
    CellProgram::Predicate(cap_invariants())
}

/// Canonical child program VK for billing cells.
pub fn billing_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&billing_cell_program())
}

/// The provider's factory descriptor for minting billing-account cells.
pub fn billing_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: BILLING_FACTORY_VK,
        child_program_vk: Some(billing_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(billing_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: cap_invariants(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![billing_factory_descriptor()]
}

// =============================================================================
// Billing core — pure operations over a Cell (unit-testable, executor-seedable)
// =============================================================================

/// **Open a billing account** on a cell: seal the spend cap (both the scalar economics and
/// the proven allowance heap ledger), pin the `WriteOnce` economics, and initialize the
/// accrued spend to zero. After this the cell's commitment binds the cap AND the allowance
/// terms; nothing has been charged. Returns the sealed [`AllowanceTerms`] (the ledger the
/// forge-detecting charges verify against). Rejects a non-positive cap.
pub fn open_billing(
    cell: &mut Cell,
    provider: CellId,
    cap_units: i64,
    start: i64,
) -> Result<AllowanceTerms, CapError> {
    let account = cell.id();
    let asset = CellId::from_bytes(*cell.token_id());
    let terms = AllowanceTerms::new(
        account,
        asset,
        cap_units,
        PERIOD_WINDOW_BLOCKS,
        start.max(0),
    );
    if !terms.is_well_formed() {
        return Err(CapError::IllFormedTerms);
    }
    // The forge-detecting cap ledger: seal the allowance capacity into the cell's heap.
    open_allowance(cell, &terms).map_err(CapError::Allowance)?;

    let st = &mut cell.state;
    st.set_field(SPENT_SLOT as usize, field_from_u64(0));
    st.set_field(CAP_SLOT as usize, field_from_u64(cap_units.max(0) as u64));
    st.set_field(PROVIDER_SLOT as usize, cell_tag(provider));
    st.set_field(START_SLOT as usize, field_from_u64(start.max(0) as u64));
    Ok(terms)
}

/// The accrued spend within the current period (the committed allowance `spent_this_epoch`,
/// which the scalar [`SPENT_SLOT`] mirrors).
pub fn spent_this_period(cell: &Cell) -> i64 {
    AllowanceState::read(cell)
        .map(|s| s.spent_this_epoch)
        .unwrap_or_else(|_| {
            cell.state
                .get_field(SPENT_SLOT as usize)
                .map(|f| field_to_u64(f) as i64)
                .unwrap_or(0)
        })
}

/// **Charge under the cap** on a billing cell: run the charge through the proven allowance
/// [`spend`] (the forge-detecting ceiling), and on admit MIRROR the new accrued spend into
/// the scalar [`SPENT_SLOT`] (the value the executor's `FieldLteField(SPENT ≤ CAP)` tooth
/// re-enforces on the produced turn). Over the cap → [`SpendDecision::Refused`] (the 402),
/// nothing mutated.
///
/// This is the executor-side ledger advance (the committed cursor moves — a light client
/// sees the charge); pairing it with [`charge_effects`] is the metered-and-moved charge.
pub fn charge_under_cap(
    cell: &mut Cell,
    terms: &AllowanceTerms,
    amount: i64,
    at_block: i64,
) -> Result<SpendDecision, CapError> {
    if amount <= 0 {
        let spent = spent_this_period(cell);
        return Ok(SpendDecision::Admitted {
            spent_units: spent,
            remaining_units: (terms.limit_per_epoch - spent).max(0),
        });
    }
    match spend(cell, terms, &Spend { amount, at_block }) {
        Ok(_moved) => {
            let spent = AllowanceState::read(cell)
                .map(|s| s.spent_this_epoch)
                .unwrap_or(0);
            cell.state
                .set_field(SPENT_SLOT as usize, field_from_u64(spent.max(0) as u64));
            Ok(SpendDecision::Admitted {
                spent_units: spent,
                remaining_units: (terms.limit_per_epoch - spent).max(0),
            })
        }
        Err(AllowanceError::ExceedsCeiling {
            spent,
            amount,
            limit,
        }) => Ok(SpendDecision::Refused {
            cap_units: limit,
            spent_units: spent,
            attempted: amount,
        }),
        Err(e) => Err(CapError::Allowance(e)),
    }
}

/// **The `charge` effects** — advance the mirrored accrued spend to `new_spent` and move
/// `amount` value from the billing cell to the provider (a conserving `Transfer`). The
/// executor re-enforces `Monotonic(SPENT)` + `FieldLteField(SPENT ≤ CAP)`, so an over-cap
/// charge is a REAL refusal (the whole turn — including the transfer — is rejected, so
/// nothing moves: the 402).
pub fn charge_effects(
    billing_cell: CellId,
    provider: CellId,
    new_spent: i64,
    amount: u64,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: billing_cell,
            index: SPENT_SLOT as usize,
            value: field_from_u64(new_spent.max(0) as u64),
        },
        Effect::Transfer {
            from: billing_cell,
            to: provider,
            amount,
        },
        Effect::EmitEvent {
            cell: billing_cell,
            event: Event::new(
                symbol("billing-charged"),
                vec![
                    field_from_u64(amount),
                    field_from_u64(new_spent.max(0) as u64),
                ],
            ),
        },
    ]
}

/// **The `seal` effects** — bind an assembled invoice's canonical `body_hash` into the
/// billing cell's [`INVOICE_DIGEST_SLOT`] and emit an `invoice-sealed` event carrying the
/// digest + total. The verified turn that carries these is the invoice's OWN turn-receipt
/// seal: the executor's [`dregg_app_framework::TurnReceipt`] binds the digest into the cell commitment, so a
/// light client sees the sealed bill and a customer re-derives [`Invoice::body_hash`].
pub fn seal_invoice_effects(billing_cell: CellId, body_hash: [u8; 32], total: i64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: billing_cell,
            index: INVOICE_DIGEST_SLOT as usize,
            value: body_hash,
        },
        Effect::EmitEvent {
            cell: billing_cell,
            event: Event::new(
                symbol("invoice-sealed"),
                vec![body_hash, field_from_u64(total.max(0) as u64)],
            ),
        },
    ]
}

/// The sealed invoice digest currently committed on the billing cell (the last invoice
/// sealed), if any.
pub fn sealed_invoice_digest(cell: &Cell) -> Option<[u8; 32]> {
    cell.state
        .get_field(INVOICE_DIGEST_SLOT as usize)
        .filter(|f| **f != [0u8; 32])
        .copied()
}

// =============================================================================
// Payment — the conserving Transfer through the Payable DSI
// =============================================================================

/// A [`Payable`] handle on a billing-account cell — the account pays a charge THROUGH the
/// shared `Payable` interface (a conserving kernel `Transfer`), so a billing charge
/// interoperates with every other `Payable` app by default.
#[derive(Clone, Copy, Debug)]
pub struct BillingWallet {
    /// The billing-account cell that holds + pays the balance.
    pub account: CellId,
    /// The asset charges are denominated in (the account cell's `token_id`).
    pub asset: CellId,
}

impl BillingWallet {
    /// A wallet handle on `account` denominating in `asset`.
    pub fn new(account: CellId, asset: CellId) -> Self {
        BillingWallet { account, asset }
    }
}

impl Payable for BillingWallet {
    fn payable_cell(&self) -> CellId {
        self.account
    }
    fn payable_asset(&self) -> [u8; 32] {
        let mut a = [0u8; 32];
        a.copy_from_slice(self.asset.as_bytes());
        a
    }
}

/// **Pay a charge** — a [`Payable`] `pay` of `amount` from the account cell to the
/// provider, desugaring to ONE conserving kernel [`Effect::Transfer`]. Submit the returned
/// [`Turn`] to move the value (per-asset Σδ=0 holds). The `authority` is the account
/// holder's authority for the `Signature`-gated `pay`.
pub fn pay_charge(
    cipherclerk: &AppCipherclerk,
    wallet: &BillingWallet,
    amount: u64,
    provider: CellId,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    wallet.pay(cipherclerk, amount, provider, authority)
}

// =============================================================================
// The deos-native surface — the billing account as a composed DeosApp
// =============================================================================

/// The billing rights tiers, on the real attenuation lattice:
///   * the ACCOUNT holder holds [`AuthRequired::Signature`] — it can be `charge`d and can
///     `seal` its period's invoice;
///   * the PROVIDER holds root — it owns the account (it can everything the holder can).
pub const ACCOUNT_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The provider rights tier (root). See [`ACCOUNT_RIGHTS`].
pub const PROVIDER_RIGHTS: AuthRequired = AuthRequired::None;

/// **The billing account as a composed [`DeosApp`]** — the whole interaction surface on the
/// deos bones. The billing cell is the account's own cell (`cipherclerk.cell_id()`).
///
///   * `charge` — a cap-gated charge (the executor's `FieldLteField(SPENT ≤ CAP)` tooth is
///     the real 402), `Signature`;
///   * `seal` — seal the period's invoice as a turn receipt, `Signature`.
pub fn billing_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let account = cipherclerk.cell_id();

    let charge = CellAffordance::new(
        "charge",
        ACCOUNT_RIGHTS,
        Effect::EmitEvent {
            cell: account,
            event: Event::new(symbol("billing-charged"), vec![]),
        },
    );
    let seal = CellAffordance::new(
        "seal",
        ACCOUNT_RIGHTS,
        Effect::EmitEvent {
            cell: account,
            event: Event::new(symbol("invoice-sealed"), vec![]),
        },
    );

    DeosApp::builder("billing", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["billing".into(), "invoices".into()])
        .cell(
            DeosCell::new(account, "billing")
                .affordance(charge)
                .affordance(seal)
                .publish(ACCOUNT_RIGHTS),
        )
        .build()
}

/// **Seed the billing cell** so the fires have live state + the invariants bite: install
/// [`billing_cell_program`] (so the executor re-enforces the spend-cap + economics
/// invariants on every touching turn), then open the account genesis state directly into
/// the embedded ledger.
pub fn seed_billing(executor: &EmbeddedExecutor, provider: CellId, cap_units: i64, start: i64) {
    let account = executor.cell_id();
    executor.install_program(account, billing_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&account) {
            let _ = open_billing(cell, provider, cap_units, start);
        }
    });
}

/// Build the on-ledger [`Action`] opening a billing account (a record of the seal — the
/// cap + provider + period start). The state-binding `open_billing` runs executor-side;
/// this is the signed turn that records the open.
pub fn build_open_billing_action(
    cipherclerk: &AppCipherclerk,
    account: CellId,
    provider: CellId,
    cap_units: i64,
    start: i64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: account,
            index: CAP_SLOT as usize,
            value: field_from_u64(cap_units.max(0) as u64),
        },
        Effect::SetField {
            cell: account,
            index: PROVIDER_SLOT as usize,
            value: cell_tag(provider),
        },
        Effect::SetField {
            cell: account,
            index: START_SLOT as usize,
            value: field_from_u64(start.max(0) as u64),
        },
        Effect::EmitEvent {
            cell: account,
            event: Event::new(
                symbol("billing-opened"),
                vec![
                    field_from_u64(cap_units.max(0) as u64),
                    cell_tag(provider),
                    field_from_u64(start.max(0) as u64),
                ],
            ),
        },
    ];
    cipherclerk.make_action(account, "open_billing", effects)
}

/// Build the on-ledger [`Action`] for one `charge` — the cap-guarded [`charge_effects`].
/// The executor re-enforces the ceiling, so an over-cap charge is refused in-band.
pub fn build_charge_action(
    cipherclerk: &AppCipherclerk,
    account: CellId,
    provider: CellId,
    new_spent: i64,
    amount: u64,
) -> Action {
    cipherclerk.make_action(
        account,
        "charge",
        charge_effects(account, provider, new_spent, amount),
    )
}

/// Build the on-ledger [`Action`] sealing an assembled `invoice` as its own turn receipt —
/// the [`seal_invoice_effects`] binding the invoice `body_hash` into the account cell.
pub fn build_seal_invoice_action(
    cipherclerk: &AppCipherclerk,
    account: CellId,
    invoice: &Invoice,
) -> Action {
    cipherclerk.make_action(
        account,
        "seal_invoice",
        seal_invoice_effects(account, invoice.body_hash(), invoice.total_units),
    )
}

/// Mount the deos-native surface ([`billing_app`]) on a shared context: build the composed
/// [`DeosApp`], seed the billing cell's program + genesis state, and fold the app into the
/// context's affordance registry.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = billing_app(ctx.cipherclerk(), ctx.executor());
    let provider = CellId::from_bytes([0xAB; 32]);
    seed_billing(ctx.executor(), provider, DEFAULT_CAP as i64, DEFAULT_START);
    app.register(ctx);
    app
}

/// The canonical web-constants module — the slot layout + event topics + factory VK the JS
/// surface is rendered from.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("billing")
        .slot("SPENT_SLOT", SPENT_SLOT as u64)
        .slot("CAP_SLOT", CAP_SLOT as u64)
        .slot("PROVIDER_SLOT", PROVIDER_SLOT as u64)
        .slot("START_SLOT", START_SLOT as u64)
        .slot("INVOICE_DIGEST_SLOT", INVOICE_DIGEST_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&BILLING_FACTORY_VK))
        .topic("CHARGED", "billing-charged")
        .topic("SEALED", "invoice-sealed")
}

/// Register the billing starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(billing_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "billing".into(),
        descriptor: serde_json::json!({
            "component": "dregg-billing",
            "module": "/starbridge-apps/billing/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["spent", "cap", "provider", "invoice_digest"],
            "slot_layout": {
                "spent": SPENT_SLOT,
                "cap": CAP_SLOT,
                "provider": PROVIDER_SLOT,
                "period_start": START_SLOT,
                "invoice_digest": INVOICE_DIGEST_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&billing_child_program_vk()),
            "operations": ["open", "charge", "seal", "estimate"],
        }),
    });

    register_deos(ctx);
    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn billing_cell() -> Cell {
        // account pubkey 7, asset 9.
        Cell::with_balance([7u8; 32], [9u8; 32], 0)
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            billing_factory_descriptor().hash(),
            billing_factory_descriptor().hash()
        );
    }

    #[test]
    fn open_seals_cap_and_economics() {
        let mut cell = billing_cell();
        let terms = open_billing(&mut cell, cid(2), 500, DEFAULT_START).unwrap();
        assert_eq!(terms.limit_per_epoch, 500);
        assert_eq!(spent_this_period(&cell), 0);
        assert_eq!(
            field_to_u64(cell.state.get_field(CAP_SLOT as usize).unwrap()),
            500
        );
        // The allowance ledger (the forge-detecting cap) is sealed into the heap.
        assert!(AllowanceState::read(&cell).is_ok());
    }

    #[test]
    fn ill_formed_cap_is_rejected() {
        let mut cell = billing_cell();
        assert!(matches!(
            open_billing(&mut cell, cid(2), 0, DEFAULT_START),
            Err(CapError::IllFormedTerms)
        ));
    }

    #[test]
    fn charge_under_cap_admits_and_mirrors_then_refuses_over_cap() {
        let mut cell = billing_cell();
        let terms = open_billing(&mut cell, cid(2), 100, DEFAULT_START).unwrap();

        // Under cap: admit + mirror the scalar SPENT_SLOT.
        let d = charge_under_cap(&mut cell, &terms, 60, DEFAULT_START + 5).unwrap();
        assert!(d.is_admitted());
        assert_eq!(
            field_to_u64(cell.state.get_field(SPENT_SLOT as usize).unwrap()),
            60,
            "the scalar mirror advanced"
        );

        // Over cap: 60 + 50 > 100 → refused (402), nothing mutated.
        let over = charge_under_cap(&mut cell, &terms, 50, DEFAULT_START + 6).unwrap();
        assert!(over.is_refused());
        assert_eq!(
            field_to_u64(cell.state.get_field(SPENT_SLOT as usize).unwrap()),
            60,
            "the refused charge left the mirror untouched"
        );
    }

    #[test]
    fn charge_effects_are_a_setfield_and_a_conserving_transfer() {
        let effects = charge_effects(cid(7), cid(2), 60, 60);
        assert!(matches!(
            effects[0],
            Effect::SetField { index, .. } if index == SPENT_SLOT as usize
        ));
        assert!(matches!(
            effects[1],
            Effect::Transfer { from, to, amount } if from == cid(7) && to == cid(2) && amount == 60
        ));
    }

    #[test]
    fn seal_effects_bind_the_invoice_body_hash() {
        let inv = Invoice::assemble(
            "alice",
            BillingPeriod::new("2026-06", 0, 1000),
            "CREDIT",
            &[],
            "t0",
        );
        let effects = seal_invoice_effects(cid(7), inv.body_hash(), inv.total_units);
        assert!(matches!(
            effects[0],
            Effect::SetField { index, value, .. }
                if index == INVOICE_DIGEST_SLOT as usize && value == inv.body_hash()
        ));
    }

    #[test]
    fn pay_charge_desugars_to_one_conserving_transfer() {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [5u8; 32]);
        let account = cipherclerk.cell_id();
        let wallet = BillingWallet::new(account, cid(9));
        let turn = pay_charge(
            &cipherclerk,
            &wallet,
            60,
            cid(2),
            InvokeAuthority::Signature,
        )
        .unwrap();
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.effects.len(), 1);
        assert!(matches!(
            action.effects[0],
            Effect::Transfer { from, to, amount }
                if from == account && to == cid(2) && amount == 60
        ));
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, BILLING_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("billing").is_some());
    }
}
