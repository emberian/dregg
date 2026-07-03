# starbridge-billing

A customer-facing **billing plane** for the dregg value layer — invoices, spend caps,
cost estimation, and recurring charges — built with **no new primitive**. Nothing here
meters, mints, or invents a kernel effect. Billing is a set of *views* and *ceilings* over
turns the executor already settled, composed from capacities the substrate already proves.
It is a full four-axis starbridge-app (verified core + service face + deos-view card),
following the same discipline as the sibling `starbridge-apps/execution-lease`.

## The four ideas, each a composition (not a primitive)

| billing idea      | is really…                                              | on |
|-------------------|---------------------------------------------------------|----|
| **an invoice**    | an aggregation VIEW over settled turn receipts, sealed as its own turn receipt | native `TurnReceipt` |
| **a spend cap**   | a rate-limited-allowance ceiling cell; an over-cap charge is refused by the executor (the 402) | `cell/src/allowance.rs` |
| **an estimate**   | a pure function over a rate card                         | — |
| **the recurring half** | a standing obligation — a fixed periodic fee, once per period, lapsing on a miss | `cell/src/obligation_standing.rs` |

### An invoice is a VIEW over settled turn receipts

An [`Invoice`](src/invoice.rs) aggregates an account's settled charges over a
[`BillingPeriod`](src/invoice.rs) into per-resource line items (`quantity × rate = amount`).
Every line item carries the **settle-receipt hash** of the turns it was billed from — each
a real [`TurnReceipt::receipt_hash`], anchored in a [`SettleReceipt`](src/usage.rs). The
bill re-witnesses against those receipts (`Invoice::verify_against_receipts`: each line's
amount is exactly the sum of its receipts, and the total is exactly the sum of the lines —
a padded line or inflated total is caught), and it is **sealed as its own turn receipt**:
`build_seal_invoice_action` binds the invoice's canonical `Invoice::body_hash` into the
billing cell, so the executor's receipt for that turn is the invoice's tamper-evident seal
(a customer re-derives `body_hash` and finds it committed on the cell).

### A spend cap is an allowance ceiling — the 402 is a real executor refusal

A [`SpendCap`](src/cap.rs) is the proven rate-limited-allowance capacity
(`cell/src/allowance.rs`) named in billing vocabulary: an account may be charged at most
`cap` per period; an over-cap charge is **refused** (`SpendDecision::Refused`), nothing
drawn — the "402 Payment Required" shape. The executor-enforced twin is the
[`cap_invariants`](src/lib.rs) program: `FieldLteField(spent ≤ cap)` + `Monotonic(spent)` +
`WriteOnce(cap)`, so a `charge` **turn** that would push the mirrored `SPENT_SLOT` over
`CAP_SLOT` is rejected **in-band** by the executor — no value moves. The value move itself
is an ordinary conserving `Transfer` (per-asset Σδ = 0).

### An estimate is a pure function

[`estimate`](src/estimate.rs) costs a resource declaration against a `RateCard` with the
exact same `quantity × unit_rate + flat` arithmetic a charge bills on — so an estimate of N
units equals what a charge of N units costs. No cell, no turn, no receipt: the `estimate`
read seam the service face names `Serviced` (never desugared to a turn).

### The recurring half rides the standing-obligation capacity

[`RecurringBill`](src/recurring.rs) is a fixed periodic fee expressed directly as a
`StandingObligation` (`cell/src/obligation_standing.rs`), mirroring
`starbridge-subscription`'s shape: a period is billed once, on schedule, for the exact fee
(the forge-detectors bite: no early / double / over / under), a miss lapses (the audit
tooth), and the per-period value is a real conserving `Transfer`.

## The four axes

- **verified core** ([`src/lib.rs`](src/lib.rs)) — the `FactoryDescriptor` +
  `billing_cell_program` (the `WriteOnce`/`Monotonic`/`FieldLteField` teeth) + the
  invoice/cap/estimate/recurring cores.
- **service face** ([`src/service.rs`](src/service.rs)) — a typed `InterfaceDescriptor` on
  the `invoke()` front door: `charge` / `seal` (replayable, `Signature`) and `estimate` /
  `status` (serviced read seams).
- **deos-view card** ([`src/card.rs`](src/card.rs)) — the billing dashboard as a
  renderer-independent `deos.ui.*` view-tree (the spent-vs-cap gauge is the killer visual).

## Verified turns (the teeth)

- **assemble-invoice-for-period** — settled `Transfer` turns produce receipts; their hashes
  aggregate into a per-resource invoice that re-witnesses against them, then seals as its
  own turn receipt.
- **charge-under-cap** — an under-cap charge settles; an over-cap charge is refused by the
  executor in-band (the 402), nothing moved.

Run the teeth: `cargo test -p starbridge-billing`.

## Honest gaps

The spend-cap **ceiling** (`FieldLteField(spent ≤ cap)`) and the value **move** (a
conserving `Transfer`) are REAL verified turns the executor enforces + the kernel conserves.
The allowance heap ledger and the invoice `body_hash` mirror are executor-side /
cell-committed steps — the same named in-circuit `SpendAllowance` / sealed-digest seam the
allowance + obligation capacities describe. A re-executing validator holding the cell +
terms witnesses every forge; welding the light-client batch circuit binding is the named
next slice, not forged from the app layer. This is a billing view + ceiling over settled
turns, not a metering engine.

This crate ports the LOGIC of a prior imperative billing module (its `invoice` / `limits` /
`estimate` / `usage` files) onto the native cells; that module's bespoke receipt chain and
replenishing-budget cell are replaced by the native turn receipt and the native allowance
capacity.
