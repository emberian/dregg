//! # `grain-turn` — the R2 kernel-turn weld, KERNEL-facing half.
//!
//! *THE-GRAIN.md face #1 (Unfoolable), rung R2: "actions become kernel turns,
//! receipts become views" (`turn_receipt_hash` populated).*
//!
//! `dregg-agent`'s [`AgentCloud::drive_state`] is, by default, a PARALLEL universe:
//! a local [`ReplenishingMeter`], a `BTreeMap<String, String>` heap, a BLAKE3
//! `cell_root`, an ed25519 receipt chain — **no executor, no `dregg_cell::Cell`, no
//! kernel turn**. The [`GrainTurnMinter`] seam
//! ([`dregg_agent::agent::GrainTurnMinter`]) is the bridge; this crate is its ONE
//! real implementation: [`ToolGatewayMinter`] turns every admitted agent action
//! into a **genuine committed executor turn** on a real `dregg_cell::Cell` (the
//! "grain turn-cell"), and hands back that turn's `turn_hash`, which the agent run
//! loop seals into the action's [`AgentReceipt`] as its `turn_receipt_hash` — the
//! receipt becomes a typed VIEW over a real kernel transition.
//!
//! ## The grain turn-cell
//!
//! The grain turn-cell IS the [`ToolGateway`]'s cap-gated worker cell. Its slots:
//!
//! * **`calls_made`** (slot [`CALLS_MADE_SLOT`](dregg_sdk::CALLS_MADE_SLOT), = 4) — the metered turn counter the
//!   gateway advances `c → c+1` on every committed invocation, carrying the proven
//!   [`mandate_program`](dregg_sdk::ToolGateway) backstop
//!   `FieldLte { calls_made ≤ rate_limit } ∧ Monotonic { calls_made }`. This is the
//!   host-side meter: the EXECUTOR ITSELF rejects an over-rate or rolled-back
//!   counter write, even against a buggy or bypassing session loop.
//! * **`consumed`** (slot [`CONSUMED_SLOT`], = 5) — the session meter's post-draw
//!   consumed total, written as witness state on the same metered turn.
//! * **`heap_root`** (slot [`HEAP_ROOT_SLOT`], = 6) — the agent's committed cell
//!   root at the point of the call, likewise witnessed on the turn.
//! * **`action`** (slot [`ACTION_SLOT`], = 7) — [`action_commit`]`(label, cost)`,
//!   the BLAKE3 commit to WHICH action this turn was minted for and what it drew;
//!   the kernel transition itself commits to the action, so a receipt and its
//!   linked turn cannot silently disagree about what was done.
//! * the cell **nonce** — advanced by the executor on every committed turn (the
//!   anti-replay/anti-reorder link binding each turn to its predecessor's receipt).
//!
//! ## Honest scope (R2, not R3)
//!
//! R2 makes the executor's own `calls_made` caveat (`FieldLte` + `Monotonic`)
//! enforce the meter **host-side** — the meter stops being merely session-local: a
//! session loop that skipped or double-counted its local meter still cannot drive
//! the on-ledger counter past the granted ceiling, because the executor rejects the
//! turn. It still TRUSTS THE EXECUTOR HOST that committed the turn — that residual
//! is exactly what R3's whole-history STARK leg (`WHOLE_HISTORY_GAP`) removes: R2
//! makes the meter a kernel caveat, R3 makes it a FRI-floor theorem.
//!
//! The rate ceiling is set to the agent's **budget**, so `calls_made ≤ budget`
//! host-side is the call-count face of the session meter. For the flat cost-1 path
//! the two coincide exactly; for variable-cost (`Spend`) actions the on-ledger
//! `calls_made ≤ budget` is a conservative call-count backstop under the session
//! meter's value bound (the session meter remains the value ceiling).

use std::sync::{Arc, RwLock};

use dregg_agent::agent::GrainTurnMinter;
use dregg_cell::program::field_from_u64;
use dregg_sdk::{AgentCipherclerk, AgentRuntime, CellId, Effect, SdkError, ToolGateway, ToolGrant};

/// Slot on the grain turn-cell that witnesses the session meter's post-draw
/// `consumed` total (written on the metered turn). Distinct from
/// [`CALLS_MADE_SLOT`](dregg_sdk::CALLS_MADE_SLOT) (the gateway-owned counter) and [`HEAP_ROOT_SLOT`].
pub const CONSUMED_SLOT: usize = 5;

/// Slot on the grain turn-cell that witnesses the agent's committed cell
/// `heap_root` at the point of the call (written on the metered turn).
pub const HEAP_ROOT_SLOT: usize = 6;

/// Slot on the grain turn-cell that witnesses WHICH action this turn was minted
/// for: [`action_commit`]`(label, cost)` — the BLAKE3 commit binding the action
/// label and its budget draw into the committed kernel state. Without this slot
/// the turn would witness only meter state (a turn happened, the meter moved);
/// with it, the kernel transition itself commits to *what* the action was, so a
/// receipt and its linked turn cannot silently disagree about the action.
pub const ACTION_SLOT: usize = 7;

/// Domain separator for [`action_commit`].
pub const ACTION_COMMIT_DOMAIN: &[u8] = b"dregg-grain-action-commit-v1";

/// The canonical action commit witnessed at [`ACTION_SLOT`] on every grain turn:
/// `BLAKE3(domain ‖ len(label) ‖ label ‖ cost)`. Length-prefixed so `(label,
/// cost)` pairs cannot collide by concatenation. Pure — a verifier holding a
/// receipt's `(action, cost)` recomputes it to check what the turn witnessed.
pub fn action_commit(label: &str, cost: i64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(ACTION_COMMIT_DOMAIN);
    h.update(&(label.len() as u64).to_le_bytes());
    h.update(label.as_bytes());
    h.update(&cost.to_le_bytes());
    *h.finalize().as_bytes()
}

/// A large-but-finite deadline for the grain mandate — the DEADLINE conjunct of
/// `delegAdmit` is not the meter here (the rate ceiling is), so it is set far out;
/// a real deployment binds it to the lease expiry.
const GRAIN_DEADLINE: i64 = i64::MAX / 2;

/// The single allowlisted tool id the grain mandate is scoped to (the SCOPE
/// conjunct); every grain turn presents this id.
const GRAIN_TOOL_ID: i64 = 1;

/// The executor method verb the grain worker's biscuit credential is scoped to.
const GRAIN_TOOL_METHOD: &str = "grain.turn";

/// **The REAL [`GrainTurnMinter`]** — drives every admitted agent action through a
/// genuine [`ToolGateway::invoke`] on a real `dregg_cell::Cell` grain turn-cell.
///
/// Construct one with [`ToolGatewayMinter::open`] (it mints a fresh runtime, admits
/// a cap-gated worker under a rate-`budget` [`ToolGrant`], and installs the
/// `mandate_program` backstop on the worker cell), then hand `Some(&mut minter)` to
/// [`AgentCloud::run_goal_minted`](dregg_agent::agent::AgentCloud::run_goal_minted)
/// / [`Session::run_goal_minted`](dregg_agent::session::Session::run_goal_minted).
/// Each admitted action becomes a committed kernel turn; a turn the executor
/// REFUSES (over-rate / insolvent) is surfaced as an `Err`, and the agent run loop
/// admits nothing for it (no draw, no receipt).
pub struct ToolGatewayMinter {
    /// The shared ledger the worker turns commit against (also the read path for
    /// [`read_slot`](Self::read_slot) — what the grain turn-cell REALLY committed).
    runtime: AgentRuntime,
    /// The cap-gated worker + its metered `calls_made` counter + the mandate cell.
    gateway: ToolGateway,
    /// The presentation clock/height every grain turn is stamped at. The DEADLINE
    /// leg is far out; the meter is the RATE leg (`calls_made ≤ budget`).
    now: i64,
    /// The committed turn hashes, in order — the "committed-turn manifest" a
    /// grain-verify R2 tooth checks the agent's receipts against.
    minted: Vec<[u8; 32]>,
}

impl ToolGatewayMinter {
    /// Open a grain turn-cell: a fresh runtime + a [`ToolGateway`] whose cap-gated
    /// worker cell IS the grain turn-cell. The rate ceiling is `budget`, so the
    /// executor's own `calls_made` `FieldLte` caveat bounds the number of committed
    /// turns host-side (the meter as a kernel caveat). Fails only if the executor
    /// refuses to admit the worker.
    pub fn open(domain: &str, budget: i64) -> Result<ToolGatewayMinter, SdkError> {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[0x6au8; 32], domain);
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), domain);
        let grant = ToolGrant {
            tool_id: GRAIN_TOOL_ID,
            rate_limit: budget.max(0),
            deadline: GRAIN_DEADLINE,
            tool_method: GRAIN_TOOL_METHOD.to_string(),
        };
        let gateway = ToolGateway::admit(&runtime, &root, grant)?;
        Ok(ToolGatewayMinter {
            runtime,
            gateway,
            now: 0,
            minted: Vec::new(),
        })
    }

    /// Read a witnessed slot straight off the COMMITTED grain turn-cell state in
    /// the real ledger (not a tracked mirror). `None` if the cell is absent or the
    /// index is out of range. This is the ground-truth read the slot-witness tests
    /// use: what the kernel actually committed, not what this struct remembers.
    pub fn read_slot(&self, index: usize) -> Option<[u8; 32]> {
        let ledger = self.runtime.ledger().lock().ok()?;
        let cell = ledger.get(&self.gateway.worker_cell())?;
        cell.state.fields.get(index).copied()
    }

    /// The grain turn-cell id (the mandate cell carrying `calls_made`).
    pub fn grain_cell(&self) -> CellId {
        self.gateway.worker_cell()
    }

    /// The number of grain turns committed so far (the on-ledger `calls_made`).
    pub fn calls_made(&self) -> i64 {
        self.gateway.calls_made()
    }

    /// The committed turn hashes, in order — the manifest a grain-verify R2 tooth
    /// checks each agent receipt's `turn_receipt_hash` against ("this link names a
    /// genuine committed turn").
    pub fn committed_turns(&self) -> &[[u8; 32]] {
        &self.minted
    }
}

impl GrainTurnMinter for ToolGatewayMinter {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let cell = self.gateway.worker_cell();
        // The tool's witness work rides the SAME metered turn as the gateway's
        // `calls_made : c → c+1` advance: the session's consumed total, the
        // agent's heap root, AND the action commit (`action_commit(label, cost)`)
        // are written as grain-turn-cell state, so the committed turn witnesses
        // WHAT the action was — which action, at what cost, over which heap —
        // not merely that a turn happened.
        let work = vec![
            Effect::SetField {
                cell,
                index: CONSUMED_SLOT,
                value: field_from_u64(consumed_after.max(0) as u64),
            },
            Effect::SetField {
                cell,
                index: HEAP_ROOT_SLOT,
                value: cell_root,
            },
            Effect::SetField {
                cell,
                index: ACTION_SLOT,
                value: action_commit(label, cost),
            },
        ];
        // The genuine executor turn. `Err` = the executor refused host-side (its
        // `calls_made` caveat over-rate, or an insolvent turn) — the agent run loop
        // treats it as a refused action (no draw, no receipt).
        let receipt = self
            .gateway
            .invoke(GRAIN_TOOL_ID, self.now, work)
            .map_err(|e| e.to_string())?;
        let turn_hash = receipt.receipt.turn_hash;
        self.minted.push(turn_hash);
        Ok(turn_hash)
    }
}
