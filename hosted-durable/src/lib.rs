//! `hosted-durable` — the conserving settlement + metering rail for the hosting
//! substrate's durable-execution leases.
//!
//! This crate carries the half of the operated layer's durable-execution stack
//! that breadstuffs owns natively: the **conserving settlement rail** a hosted
//! lease pays through. A funded `execution-lease` accrues per-period
//! [`LeaseCharge`]s; each is settled as one conserving `Effect::Transfer`
//! (paired-delta, `recTransfer` law) by a [`Settlement`] backend, producing a
//! [`SettleReceipt`]. The in-process [`TestConservingLedger`] is the always-green
//! twin the offline proof exercises; the production rail submits each charge over
//! an injected [`payable::PaySubmitter`] wire (a node client signs + executes the
//! turn).
//!
//! ```text
//!   dregg (meters / pays / verifies the lease — breadstuffs)
//!     └─ hosted-durable (THIS crate — the conserving settlement + metering rail)
//!        └─ [the durable-execution workflow: an operated-layer follow-up, below]
//! ```
//!
//! ## What is (and is not) in scope here
//!
//! The **settlement + metering** layer is native and complete:
//! - [`conserve`] — the conserving-move primitive, computed by the substrate's
//!   *proven* [`dregg_cell::CellState`](conserve) signed-balance discipline on
//!   every build (the kernel `Effect::Transfer` paired-delta law).
//! - [`meter`] — the funded, refuse-over-budget [`meter::Account`] plus the
//!   process-global observability tally.
//! - [`payable`] — the production settlement rail: each charge submitted as one
//!   conserving `Effect::Transfer` turn over an injected [`payable::PaySubmitter`].
//! - [`settle`] — [`LeaseCharge`] / [`SettleReceipt`] / the [`Settlement`] trait +
//!   the [`TestConservingLedger`] in-process twin (the metering surface the
//!   agent-platform's billing binds to).
//!
//! The **durable-execution workflow** upstream (a duroxide orchestration whose
//! steps run owned-sandbox workloads through the operated compute tier, with a
//! transactional-outbox meter and crash-exact resume) is NOT imported here: it
//! binds the operated-execution executor + the Postgres/duroxide store, neither a
//! breadstuffs sibling. It is a named follow-up; the settlement rail below stands
//! complete without it, and swapping in the workflow does not change a line of it.

use serde::{Deserialize, Serialize};

/// The conserving-move primitive the settlement rail upholds — the kernel
/// `Effect::Transfer` paired-delta law, computed by the substrate's *proven*
/// `dregg_cell::CellState` signed-balance discipline
/// (`recTransfer_balanceSum_conserve`) on every build. See [`conserve`].
pub mod conserve;
/// The funded, refuse-over-budget [`meter::Account`] plus the process-global
/// observability tally.
pub mod meter;
/// The production settlement rail: each charge submitted as one conserving
/// `Effect::Transfer` turn over an injected [`payable::PaySubmitter`] wire (a
/// node client signs + executes it).
pub mod payable;
pub mod settle;
pub use conserve::{ConservedMove, apply_conserving_transfer};
pub use meter::{Account, OverBudget};
pub use payable::{PaySubmitter, PayTerms, PayableSettlement, SubmittedPay};
pub use settle::{
    ConservingLedger, LeaseCharge, SettleError, SettleReceipt, Settlement, TestConservingLedger,
};

/// The settlement-outbox table name a `Payable` settlement reads charges from
/// (the durable-workflow follow-up writes them; kept here as the shared name).
pub const METER_TABLE: &str = "hosted_meter";

/// One lease meter charge — the per-period settlement input.
///
/// `period` is the step ordinal within the lease (1-based); `amount` is the units
/// to debit for this period. The `(lease_id, period)` pair is the idempotency key,
/// so a re-run after a crash never charges the same period twice.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct MeterCharge {
    pub period: i64,
    pub amount: i64,
}
