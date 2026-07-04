//! `agent` — the **Verifiable Agent Cloud** onramp.
//!
//! The pitch made runnable: *give an autonomous agent a budget and a capability;
//! get back a proof of everything it did and a hard bound on everything it could
//! have done.* This module does not invent a new mechanism — it **braids** three
//! primitives that already exist in the workspace into one flow:
//!
//! 1. **the bound** — a [`ReplenishingMeter`](crate::meter::ReplenishingMeter)
//!    over a [`ReplenishingBudget`](crate::budget::ReplenishingBudget) cell (DEC
//!    budget · period · refill). Every action the agent takes is *drawn* from this
//!    cell; an exhausted budget refuses further actions **in-band** (the runaway
//!    is contained, not merely logged). The un-drawn headroom is the hard ceiling
//!    on everything the agent *could* still have done.
//! 2. **the authority** — the cap bundle / powerbox: a `dregg-webauth`
//!    `dga1_` credential (the attenuable, offline-verifiable ed25519 caveat-chain,
//!    the `attenuate_subset` no-amplify lattice). Each action is **cap-gated**: a
//!    tool-call / cell-op outside the bundle is refused by
//!    [`Credential::verify`](crate::cred::Credential::verify) before it
//!    runs. A sub-agent gets a genuinely **attenuated** child credential (it can
//!    only narrow).
//! 3. **the proof** — the receipt chain: a `dregg-receipt`
//!    [`ReceiptChain`](crate::receipt::ReceiptChain) seals every admitted action
//!    into a prev-hash-linked, ed25519-signed record. The whole run is
//!    re-witnessable by a non-witness with
//!    [`verify_chain`](crate::receipt::verify_chain) — no trust in the host.
//!
//! ## Where the pieces this realizes already live
//!
//! - This module is the **std-only, green-gated onramp**: it drives the agent's
//!   intended actions directly (the local / mock-LLM path) so the whole loop is
//!   provable in one command, with no heavy compute guest. The compute tools the
//!   agent reaches via `invoke` are closure-injected through the [`crate::toolkit`]
//!   so a host can wire any sandbox behind them without this core depending on it.
//! - The **brain** is the [`AgentBrain`] seam. A [`PlannedBrain`] (a fixed list
//!   of intended actions — the mock LLM) drives the safe-autonomous path. The
//!   **confined Hermes agent** (`deos-hermes`, the real reactive brain with a BYO
//!   LLM key serving a remote user) is the *reviewed-go* substitution behind this
//!   exact seam: it emits the same [`AgentAction`]s, gated/metered/receipted by
//!   the same braid.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::cred::{Credential, PublicKey, RootKey, WireError};
use crate::grant::{CapGrant, attenuate_grants, cap_context, mint_grants};
use crate::receipt::{
    BodyHasher, ChainError, ReceiptAttestation, ReceiptBody, ReceiptChain, verify_chain,
};

use crate::budget::BudgetTerms;
use crate::meter::{Meter, MeterError, MeterKey, ReplenishingMeter};

// ---------------------------------------------------------------------------
// The capability vocabulary — how an action names the authority it needs.
// ---------------------------------------------------------------------------

/// The cap a service `invoke` requires (`invoke:<service>`).
fn invoke_cap(service: &str) -> String {
    format!("invoke:{service}")
}
/// The cap a cell read requires (`cell-read:<path>`).
fn cell_read_cap(path: &str) -> String {
    format!("cell-read:{path}")
}
/// The cap a cell write requires (`cell-write:<path>`).
fn cell_write_cap(path: &str) -> String {
    format!("cell-write:{path}")
}

// ---------------------------------------------------------------------------
// The OPERATOR toolkit — a real, capable agent on a leash.
// ---------------------------------------------------------------------------
//
// Beyond the flat `invoke`/`Spend`/cell rails, the agent reaches a rich operator
// toolkit (a real shell, fs, http, git) through [`AgentAction::Op`]. Each op is
// **per-tool AND per-resource** cap-gated: the required cap carries the resource
// (the file path, the egress host), so the cap bundle can grant `shell` yet bound
// it to `/workdir`, grant `http` only to `api.github.com`, etc. The grant rides
// [`CapGrant::Prefix`] so the resource scope is part of the *signed* authority a
// sub-agent can only narrow — not a check the run loop could forget.

/// The operator-tool names the brain can call. Each rides [`AgentAction::Op`].
pub mod op {
    /// A real shell command (workdir-confined, timeout-bounded). Cap: `shell`.
    pub const SHELL: &str = "shell";
    /// Read a file under the workdir. Cap: `fs-read:<abs-path>`.
    pub const FS_READ: &str = "fs_read";
    /// Write a file under the workdir. Cap: `fs-write:<abs-path>`.
    pub const FS_WRITE: &str = "fs_write";
    /// List a directory under the workdir. Cap: `fs-read:<abs-path>`.
    pub const LIST_DIR: &str = "list_dir";
    /// Create a directory under the workdir. Cap: `fs-write:<abs-path>`.
    pub const MKDIR: &str = "mkdir";
    /// HTTP GET a URL. Cap: `http:<host>` (per-host egress).
    pub const HTTP_GET: &str = "http_get";
    /// `git clone` a repo into the workdir. Cap: `http:<host>` (the fetch egress).
    pub const GIT_CLONE: &str = "git_clone";
    /// **Provision a SaaS via the Stripe Projects skill** (`stripe projects add
    /// <provider>/<service>`). Cap: `provision:<provider>` (per-provider). The
    /// agent provisions its own infrastructure; the tier cost is drawn from the
    /// budget cell (over-budget → refused in-band before the CLI runs).
    pub const STRIPE_PROVISION: &str = "stripe_provision";
    /// **Pay a vendor via the Stripe Link skill** (`@stripe/link-cli`). Cap:
    /// `pay:<vendor>` (per-vendor). The agent pays for the services it uses; the
    /// variable `amount_cents` is drawn from the budget cell (over-ceiling →
    /// refused in-band before any money moves).
    pub const STRIPE_PAY: &str = "stripe_pay";

    /// Every operator tool name (for the spec helper / display).
    pub const ALL: &[&str] = &[
        SHELL,
        FS_READ,
        FS_WRITE,
        LIST_DIR,
        MKDIR,
        HTTP_GET,
        GIT_CLONE,
        STRIPE_PROVISION,
        STRIPE_PAY,
    ];
}

/// One operator-tool call the brain decided: a tool name + its string args. The
/// rich, freeform-argument path (a shell command, a file path + content, a URL) —
/// the flexible counterpart to the fixed `invoke:<service>` rail. Cap-gated **per
/// resource** via [`ToolCall::default_cap`] (the run loop resolves the path/host
/// against the workdir first; see [`ToolKit::op_cap`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToolCall {
    /// The operator tool (one of [`op`]).
    pub tool: String,
    /// The tool's string arguments (`cmd` for shell, `path`/`content` for fs,
    /// `url`/`dest` for http/git).
    pub args: BTreeMap<String, String>,
}

impl ToolCall {
    /// A tool call from a name + arg pairs.
    pub fn new(
        tool: impl Into<String>,
        args: impl IntoIterator<Item = (String, String)>,
    ) -> ToolCall {
        ToolCall {
            tool: tool.into(),
            args: args.into_iter().collect(),
        }
    }

    /// An arg by key.
    pub fn arg(&self, key: &str) -> Option<&str> {
        self.args.get(key).map(String::as_str)
    }

    /// The host of a URL arg (for `http:<host>` egress caps) — the authority
    /// between `://` and the next `/`, `?`, or `:`. `""` if not a URL.
    pub fn url_host(&self, key: &str) -> String {
        host_of(self.arg(key).unwrap_or(""))
    }

    /// The **resource-scoped** capability this call needs, computed from the raw
    /// args alone (the run loop prefers [`ToolKit::op_cap`], which resolves fs
    /// paths against the workdir; this is the fallback / no-toolkit form).
    pub fn default_cap(&self) -> String {
        match self.tool.as_str() {
            op::SHELL => "shell".to_string(),
            op::FS_READ | op::LIST_DIR => format!("fs-read:{}", self.arg("path").unwrap_or("")),
            op::FS_WRITE | op::MKDIR => format!("fs-write:{}", self.arg("path").unwrap_or("")),
            op::HTTP_GET => format!("http:{}", self.url_host("url")),
            op::GIT_CLONE => format!("http:{}", self.url_host("url")),
            // The Stripe Skills are gated PER RESOURCE: only `provision:<provider>`
            // / `pay:<vendor>` grants reach them (a sub-agent can only narrow).
            op::STRIPE_PROVISION => format!("provision:{}", self.arg("provider").unwrap_or("")),
            op::STRIPE_PAY => format!("pay:{}", self.arg("vendor").unwrap_or("")),
            other => format!("op:{other}"),
        }
    }

    /// The variable budget amount (USD-cents) this call draws, if it carries an
    /// `amount_cents` arg — the priced operator tools (`stripe_pay`'s pay amount,
    /// `stripe_provision`'s tier cost) draw their *price* from the budget cell
    /// rather than the flat `cost_per_action`, so the cell IS the dollar ceiling
    /// and an over-ceiling spend is refused in-band before the CLI runs.
    pub fn amount_cents(&self) -> Option<i64> {
        self.arg("amount_cents")
            .and_then(|s| s.trim().parse::<i64>().ok())
    }

    /// A short human label for logs/receipts (`shell:cargo test`, `git_clone:…`).
    pub fn label(&self) -> String {
        let detail = match self.tool.as_str() {
            op::SHELL => self.arg("cmd").unwrap_or("").to_string(),
            op::FS_READ | op::FS_WRITE | op::LIST_DIR | op::MKDIR => {
                self.arg("path").unwrap_or("").to_string()
            }
            op::HTTP_GET | op::GIT_CLONE => self.arg("url").unwrap_or("").to_string(),
            op::STRIPE_PROVISION => format!(
                "{}/{}",
                self.arg("provider").unwrap_or(""),
                self.arg("service").unwrap_or("")
            ),
            op::STRIPE_PAY => format!(
                "{}={}c",
                self.arg("vendor").unwrap_or(""),
                self.arg("amount_cents").unwrap_or("?")
            ),
            _ => String::new(),
        };
        let detail: String = detail.chars().take(48).collect();
        if detail.is_empty() {
            format!("op:{}", self.tool)
        } else {
            format!("{}:{}", self.tool, detail)
        }
    }
}

/// The host (authority) of a URL — between `://` and the next `/ ? :`, lowercased.
fn host_of(url: &str) -> String {
    let after = url.split_once("://").map(|(_, r)| r).unwrap_or(url);
    let end = after.find(['/', '?', ':', '#']).unwrap_or(after.len());
    after[..end].to_ascii_lowercase()
}

// ---------------------------------------------------------------------------
// The agent spec — the two things the user hands a deployed agent.
// ---------------------------------------------------------------------------

/// What an agent is deployed with: **(a)** a replenishing-budget cell (the spend
/// bound) and **(b)** a cap bundle (the attenuable authority — which services it
/// may `invoke`, which cells it may touch).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentSpec {
    /// The agent id (the meter subject + the receipt-chain root identity).
    pub id: String,
    /// The asset the budget is denominated in (e.g. `DREGG`).
    pub asset: String,
    /// The spend ceiling — max outstanding consumption per `period`.
    pub budget: i64,
    /// The replenishment granularity in blocks (a billing knob, not a sale window).
    pub period: i64,
    /// How much a matured refill returns (defaults to the whole budget).
    pub refill: i64,
    /// Bound on the live refill queue (the MCS `refill_max`).
    pub refill_max: u16,
    /// The schedule genesis block (no action may be backdated before it).
    pub start: i64,
    /// The services the agent may `invoke` (each becomes an `invoke:<service>` cap).
    pub services: Vec<String>,
    /// The cells the agent may read+write (each becomes `cell-read:`/`cell-write:` caps).
    pub cells: Vec<String>,
    /// **Resource-scoped operator grants** beyond the flat services/cells: e.g.
    /// `Exact("shell")`, `Prefix("fs-read:/workdir")`, `Exact("http:api.github.com")`.
    /// These ride [`CapGrant::Prefix`] so a path/host scope is part of the signed
    /// bundle (per-tool AND per-resource authority), and a sub-agent can only narrow.
    #[serde(default)]
    pub grants: Vec<CapGrant>,
    /// The budget cost charged per action (drawn from the budget cell). Must be `> 0`.
    pub cost_per_action: i64,
}

impl AgentSpec {
    /// A spec for `id` with a `budget`-unit ceiling and sensible defaults: a
    /// large period (so within one run the ceiling is the hard bound), one-chunk
    /// refill, cost `1` per action, and an empty cap bundle (add services / cells).
    pub fn new(id: impl Into<String>, budget: i64) -> AgentSpec {
        AgentSpec {
            id: id.into(),
            asset: "DREGG".to_string(),
            budget,
            period: 1_000_000,
            refill: budget,
            refill_max: 1,
            start: 0,
            services: Vec::new(),
            cells: Vec::new(),
            grants: Vec::new(),
            cost_per_action: 1,
        }
    }

    /// Grant the agent the right to `invoke` `service`.
    pub fn with_service(mut self, service: impl Into<String>) -> AgentSpec {
        self.services.push(service.into());
        self
    }

    /// Grant the agent read+write over `cell`.
    pub fn with_cell(mut self, cell: impl Into<String>) -> AgentSpec {
        self.cells.push(cell.into());
        self
    }

    /// Add a **resource-scoped operator grant** (per-tool / per-resource), e.g.
    /// `CapGrant::Exact("shell")`, `CapGrant::Prefix("fs-read:/workdir")`,
    /// `CapGrant::Exact("http:api.github.com")`.
    pub fn with_grant(mut self, grant: CapGrant) -> AgentSpec {
        self.grants.push(grant);
        self
    }

    /// Grant `shell` (workdir-confined by the runner; the cap itself is coarse).
    pub fn with_shell(self) -> AgentSpec {
        self.with_grant(CapGrant::Exact("shell".to_string()))
    }

    /// Grant fs read+write **bounded to `root`** (a prefix grant: any path under
    /// `root` is reachable, nothing outside it).
    pub fn with_workdir_fs(self, root: impl AsRef<str>) -> AgentSpec {
        let root = root.as_ref();
        self.with_grant(CapGrant::Prefix(format!("fs-read:{root}")))
            .with_grant(CapGrant::Prefix(format!("fs-write:{root}")))
    }

    /// Grant HTTP/git egress to a single `host` (per-host: `http:<host>`).
    pub fn with_http_host(self, host: impl AsRef<str>) -> AgentSpec {
        self.with_grant(CapGrant::Exact(format!("http:{}", host.as_ref())))
    }

    /// Grant the **Stripe Projects skill** for one `provider` (`provision:<provider>`):
    /// the agent may provision SaaS from that provider only (a sub-agent can narrow,
    /// never widen, and a non-granted provider is cap-refused before the CLI runs).
    pub fn with_stripe_provision(self, provider: impl AsRef<str>) -> AgentSpec {
        self.with_grant(CapGrant::Exact(format!("provision:{}", provider.as_ref())))
    }

    /// Grant the **Stripe Link skill** for one `vendor` (`pay:<vendor>`): the agent
    /// may pay that vendor only (the amount is still bounded by the budget cell).
    pub fn with_stripe_pay(self, vendor: impl AsRef<str>) -> AgentSpec {
        self.with_grant(CapGrant::Exact(format!("pay:{}", vendor.as_ref())))
    }

    /// The full resource-scoped grant bundle: an `invoke:` exact per service, a
    /// `cell-read:`/`cell-write:` exact pair per cell, plus the explicit
    /// [`grants`](AgentSpec::grants).
    fn grant_bundle(&self) -> Vec<CapGrant> {
        let mut g = Vec::new();
        for s in &self.services {
            g.push(CapGrant::Exact(invoke_cap(s)));
        }
        for c in &self.cells {
            g.push(CapGrant::Exact(cell_read_cap(c)));
            g.push(CapGrant::Exact(cell_write_cap(c)));
        }
        g.extend(self.grants.iter().cloned());
        g
    }

    /// The replenishing-budget terms this spec opens.
    fn budget_terms(&self) -> BudgetTerms {
        BudgetTerms::new(
            self.asset.clone(),
            self.budget,
            self.period,
            self.refill,
            self.refill_max,
            self.start,
        )
    }

    /// The cap bundle as display strings (a prefix renders with a trailing `*`).
    fn caps(&self) -> Vec<String> {
        self.grant_bundle().iter().map(CapGrant::display).collect()
    }
}

// ---------------------------------------------------------------------------
// The brain seam — what the agent decides to do, one action at a time.
// ---------------------------------------------------------------------------

/// One action the agent's brain decides to take. The mock-LLM path emits these
/// directly; the confined-Hermes brain (reviewed-go) emits the same vocabulary
/// over its tool-call wire.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AgentAction {
    /// Call a service / tool (the `tool-call` shape). Cap: `invoke:<service>`.
    Invoke {
        /// The service to call.
        service: String,
    },
    /// **A budget-gated, variable-amount priced call** — the spend rail. Like
    /// [`Invoke`](AgentAction::Invoke) (cap: `invoke:<service>`), but its budget
    /// draw is the call's *price* (`amount_cents`) rather than the flat
    /// `cost_per_action`: so the budget cell IS the dollar ceiling and an
    /// over-ceiling spend is refused **in-band, before the priced tool runs** (no
    /// money moves). The amount is bound into the receipt (`cost`), so a forged
    /// "I paid $X" breaks the signature. This is the outbound-Stripe-spend shape
    /// (`stripe_pay`): a credit card the agent provably cannot max out past its
    /// funded budget.
    Spend {
        /// The priced service / tool to call (e.g. `stripe_pay`).
        service: String,
        /// The dollar amount of the spend, in budget units (USD-cents). Drawn from
        /// the budget cell as the action's cost. Must be `> 0`.
        amount_cents: i64,
    },
    /// Write the agent's own committed cell. Cap: `cell-write:<path>`.
    CellWrite {
        /// The cell path.
        path: String,
        /// The value to commit.
        value: String,
    },
    /// Read the agent's own committed cell. Cap: `cell-read:<path>`.
    CellRead {
        /// The cell path.
        path: String,
    },
    /// **A rich operator-tool call** — the real shell / fs / http / git path.
    /// Cap-gated **per resource** (`shell`, `fs-read:<path>`, `http:<host>`, …),
    /// metered, and receipted with a [`WitnessedRun`] over `(command, inputs,
    /// result)` so the work is tamper-evident and re-witnessable.
    Op(ToolCall),
}

impl AgentAction {
    /// The capability this action needs to be admitted. A [`Spend`](AgentAction::Spend)
    /// needs the same `invoke:<service>` authority as a plain invoke — the spend
    /// rail does not widen reach, it only prices the draw.
    fn required_cap(&self) -> String {
        match self {
            AgentAction::Invoke { service } => invoke_cap(service),
            AgentAction::Spend { service, .. } => invoke_cap(service),
            AgentAction::CellWrite { path, .. } => cell_write_cap(path),
            AgentAction::CellRead { path } => cell_read_cap(path),
            AgentAction::Op(call) => call.default_cap(),
        }
    }

    /// A stable, human-readable label (also the receipt's `action` field). A
    /// `spend:<service>` label distinguishes a priced spend from a flat invoke in
    /// the P&L.
    fn label(&self) -> String {
        match self {
            AgentAction::Invoke { service } => format!("invoke:{service}"),
            AgentAction::Spend { service, .. } => format!("spend:{service}"),
            AgentAction::CellWrite { path, .. } => format!("cell-write:{path}"),
            AgentAction::CellRead { path } => format!("cell-read:{path}"),
            AgentAction::Op(call) => call.label(),
        }
    }

    /// The budget units this action draws: a [`Spend`](AgentAction::Spend) — or a
    /// priced [`Op`](AgentAction::Op) carrying an `amount_cents` arg (a Stripe
    /// Skill) — draws its variable price; everything else draws the agent's flat
    /// `cost_per_action` default.
    fn draw_cost(&self, default: i64) -> i64 {
        match self {
            AgentAction::Spend { amount_cents, .. } => *amount_cents,
            // A priced operator tool (a Stripe Skill carrying an `amount_cents`
            // arg) draws its price from the budget cell; every other op draws the
            // flat `cost_per_action`.
            AgentAction::Op(call) => call.amount_cents().unwrap_or(default),
            _ => default,
        }
    }
}

/// What the brain learns about one decided action after the braid weighed in —
/// the gate's verdict (and any tool result), fed back so a *reactive* brain (the
/// live LLM path) adapts its next decision to confinement. A scripted brain
/// ignores it; the [`crate::brain::KimiBrain`] folds it back into the running
/// conversation so the model reasons over "this tool was refused / this tool
/// returned X" and picks its next move accordingly.
#[derive(Clone, Debug)]
pub struct ActionObservation {
    /// The action label the brain decided (`invoke:check_health`, …).
    pub action: String,
    /// `true` iff the braid admitted it (cap ✓ · budget ✓ · receipted).
    pub admitted: bool,
    /// On refusal: the reason (the missing cap, or budget-exhausted). `None` on admit.
    pub refusal: Option<String>,
    /// For an admitted `invoke` dispatched to a live tool: the tool's verdict.
    pub tool_ok: Option<bool>,
    /// The tool's summary, if any (bound into the receipt; surfaced to the brain).
    pub tool_summary: Option<String>,
}

/// The agent's reactive brain — yields its next intended action, or `None` when
/// it is done. The single seam the mock-LLM path and the live BYO-key LLM brain
/// both implement.
pub trait AgentBrain {
    /// The next action the agent wants to take at `step` (0-based), or `None` to stop.
    fn next_action(&mut self, step: u64) -> Option<AgentAction>;

    /// Observe the braid's verdict on the brain's *last* decided action — the
    /// gate's allow/refuse (and any tool verdict). Default no-op (a scripted
    /// brain ignores it); a reactive brain folds it back in to decide the next
    /// step under confinement. Called by the run loop once per decided action,
    /// between deciding it and asking for the next.
    fn observe(&mut self, _obs: &ActionObservation) {}
}

/// A brain that replays a fixed plan — the mock-LLM / scripted path. A runaway is
/// just a long plan of repeated actions; the budget contains it regardless.
pub struct PlannedBrain {
    plan: Vec<AgentAction>,
}

impl PlannedBrain {
    /// A brain that will emit `plan` in order, then stop.
    pub fn new(plan: Vec<AgentAction>) -> PlannedBrain {
        PlannedBrain { plan }
    }
}

impl AgentBrain for PlannedBrain {
    fn next_action(&mut self, step: u64) -> Option<AgentAction> {
        self.plan.get(step as usize).cloned()
    }
}

// ---------------------------------------------------------------------------
// The toolkit seam — what an admitted `invoke` actually DOES.
// ---------------------------------------------------------------------------

/// The **witnessed execution binding** a compute-tier tool emits — the part of a
/// QA verdict that makes it a *proof the work happened* rather than the runtime's
/// say-so. It binds the three facts a re-witness can independently check:
///
/// - **`command`** — the exact test/verify invocation (lang · tier · entrypoint),
/// - **`code_root`** — a commitment to the code the run executed against (the same
///   content commitment a deploy publishes, so a verifier can check the tests ran
///   on *the code that was actually deployed*, not arbitrary code),
/// - the **result** — the entrypoint's `exit` (0 = pass) and an `output_digest`
///   over the run's output values.
///
/// This is folded into the action's receipt and re-checked by
/// [`verify_witnessed_qa`]: a re-execution from `(command, code_root)` must
/// reproduce `(exit, output_digest)`. A lying runtime that recorded a verdict its
/// execution does not actually produce is caught here — the binding mismatches on
/// re-witness. The honest limit: the re-execution still runs in the same compute
/// substrate, so this proves "the substrate ran these tests on this code with
/// this result"; full operator-independence needs the tier run *itself* attested
/// by the federation / light client (the in-circuit witness — named the residual
/// in `docs/VISION-NEXT-PRODUCT.md`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessedRun {
    /// The exact command the tier executed (e.g. `run_tests[lang=wat,tier=Sandboxed,entry=run]`).
    pub command: String,
    /// The content commitment to the code the run executed against — tied to the
    /// deploy's published `content_root` so a verifier can confirm the tests ran
    /// on the deployed code.
    pub code_root: String,
    /// The entrypoint's exit / failure count (`0` = pass), as the tier returned it.
    pub exit: i64,
    /// A domain-separated digest over the run's output values (the result).
    pub output_digest: [u8; 32],
}

impl WitnessedRun {
    /// `true` iff the run reported success (exit `0`).
    pub fn passed(&self) -> bool {
        self.exit == 0
    }
}

/// The verdict a live tool returns for an admitted `invoke` — the QA / ops
/// result the toolkit produces (*did the tests pass? did the deploy verify? is
/// the node healthy?*). It is folded into the action's receipt, so the verdict
/// itself is re-witnessable, not merely the fact that a call happened: a forged
/// "the tests passed" is caught on re-witness, because flipping `ok` breaks the
/// receipt signature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ToolOutcome {
    /// The verdict: `true` = passed / verified / healthy, `false` = failed /
    /// anomalous. A `false` outcome is still a *real, receipted result* (the QA
    /// ran and the answer is "fail"), not a refusal.
    pub ok: bool,
    /// A short human-readable summary (the test counts, the verify result, the
    /// flagged anomalies). Bound into the receipt alongside `ok`.
    pub summary: String,
    /// For an execution-witnessing tool (`run_tests` / `verify_deploy` over a
    /// compute tier): the [`WitnessedRun`] binding `(command, code_root, result)`
    /// the run emitted. `None` for tools whose verdict is not a re-runnable tier
    /// execution (e.g. a local health probe). Bound into the receipt and
    /// re-checked by [`verify_witnessed_qa`].
    #[serde(default)]
    pub witnessed: Option<WitnessedRun>,
}

impl ToolOutcome {
    /// A passing verdict (tests green / deploy verified / node healthy).
    pub fn pass(summary: impl Into<String>) -> ToolOutcome {
        ToolOutcome {
            ok: true,
            summary: summary.into(),
            witnessed: None,
        }
    }
    /// A failing verdict (tests red / deploy mismatch / anomaly flagged). Still
    /// a real receipted result, not a refusal.
    pub fn fail(summary: impl Into<String>) -> ToolOutcome {
        ToolOutcome {
            ok: false,
            summary: summary.into(),
            witnessed: None,
        }
    }
    /// Attach a [`WitnessedRun`] execution binding to this verdict (so the
    /// receipt carries `(command, code_root, result)`, not just a pass/fail bit).
    pub fn with_witness(mut self, witnessed: WitnessedRun) -> ToolOutcome {
        self.witnessed = Some(witnessed);
        self
    }
}

/// A live toolkit behind the `invoke` rail: maps an admitted `invoke:<service>`
/// to a real capability (run the tests, verify the deploy, check health). By the
/// time this runs the rail has already **cap-gated** the call (an out-of-bundle
/// service was refused before reaching here) and **metered** it (drawn from the
/// budget); the toolkit performs the work and returns its verdict, which the
/// rail then seals into the receipt chain. The concrete toolkit lives in
/// [`crate::toolkit`].
///
/// `cells` is the agent's committed cell heap (read-only) — a tool may read it
/// for context (e.g. the deploy name the agent just wrote to `/deploy`).
pub trait ToolKit {
    /// Perform the admitted `service` call and return its verdict. `amount_cents`
    /// is `Some` for a [`Spend`](AgentAction::Spend) (the priced amount already
    /// drawn from the budget, before this runs — so a priced tool, e.g. a Stripe
    /// payout, knows the dollar amount to move) and `None` for a flat
    /// [`Invoke`](AgentAction::Invoke).
    fn invoke(
        &self,
        service: &str,
        amount_cents: Option<i64>,
        cells: &BTreeMap<String, String>,
    ) -> ToolOutcome;

    /// The **resource-scoped capability** an [`AgentAction::Op`] needs — the place
    /// a toolkit that owns a workdir resolves a (possibly relative) fs path to its
    /// absolute form so the cap-gate compares against the granted prefix. The
    /// default is the raw [`ToolCall::default_cap`] (no workdir resolution). The
    /// run loop cap-gates against *this* before [`run_op`](ToolKit::run_op) runs,
    /// so a tool/resource outside the bundle is refused **before** any effect.
    fn op_cap(&self, call: &ToolCall) -> String {
        call.default_cap()
    }

    /// Execute a rich operator-tool call (a real shell / fs / http / git op) and
    /// return its verdict (with a [`WitnessedRun`] binding so the result is
    /// tamper-evident). Reached only AFTER the cap-gate admitted
    /// [`op_cap`](ToolKit::op_cap) and the meter drew the action's cost. The
    /// default has no operator tools (a flat toolkit) and fails closed.
    fn run_op(&self, call: &ToolCall, _cells: &BTreeMap<String, String>) -> ToolOutcome {
        ToolOutcome::fail(format!(
            "no operator tools on this toolkit (tool `{}`)",
            call.tool
        ))
    }
}

// ---------------------------------------------------------------------------
// The R2 kernel-turn seam — actions become kernel turns, receipts become views.
// ---------------------------------------------------------------------------

/// **The R2 kernel-turn seam** (THE-GRAIN.md face #1, rung R2: *"actions become
/// kernel turns, receipts become views"*).
///
/// By default a [`drive_state`](AgentCloud) run is a PARALLEL universe: a local
/// meter, a `BTreeMap` heap, an ed25519 receipt chain — **no executor, no
/// `dregg_cell::Cell`, no kernel turn**. A `GrainTurnMinter`, when supplied, welds
/// that universe onto the real one: every ADMITTED action is turned into a GENUINE
/// committed executor turn on a "grain turn-cell", and the minter hands back that
/// turn's `turn_hash`, which the run loop SEALS into the action's [`AgentReceipt`]
/// as its [`turn_receipt_hash`](crate::receipt::ReceiptAttestation::turn_receipt_hash)
/// — so the receipt becomes a typed VIEW over a real kernel transition, not a
/// free-standing log line.
///
/// The minter is ALSO an admission surface. [`mint_turn`](GrainTurnMinter::mint_turn)
/// returns `Err` when the EXECUTOR refuses the turn — e.g. its own `calls_made`
/// `FieldLte`/`Monotonic` caveat bites, so the meter is enforced HOST-SIDE even
/// against a buggy or bypassing session loop. A refused mint admits NOTHING: no
/// budget draw, no effect, no receipt (fail-closed, exactly parallel to the
/// cap-gate). That is the R2 strength — the executor's OWN caveat, not merely the
/// session-local meter, bounds the run. Its honest residual (the run still trusts
/// the executor host that committed the turn) is what R3's whole-history STARK
/// removes; R2 makes the meter a kernel caveat, R3 makes it a FRI-floor theorem.
///
/// The heavyweight REAL implementation — driving `dregg_sdk::ToolGateway::invoke`
/// on a real `dregg_cell::Cell` — lives OUT of this std-only crate (in the
/// `grain-turn` crate, which depends on the kernel), so this crate stays
/// substrate-only. [`SyntheticMinter`] is a dep-free deterministic minter for
/// tests, demos, and the grain-verify R2 tooth.
pub trait GrainTurnMinter {
    /// Mint a genuine kernel turn for ONE admitted action and return the committed
    /// turn receipt hash (`turn_hash`) the [`AgentReceipt`] becomes a view of — or
    /// `Err(reason)` if the executor REFUSED the turn (its host-side caveat bit; the
    /// action is then not admitted). `label` names the action; `cost` is the budget
    /// it draws; `consumed_after` is the session meter's projected post-draw total;
    /// `cell_root` is the grain heap root at the point of the call.
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String>;
}

/// A dep-free, DETERMINISTIC [`GrainTurnMinter`] for tests, demos, and the
/// grain-verify R2 tooth.
///
/// It mints a synthetic turn hash `BLAKE3(domain ‖ seq ‖ label ‖ cost ‖ consumed ‖
/// cell_root)` per call and RECORDS it, so a caller can supply the recorded hashes
/// as the "committed-turn manifest" the R2 tooth checks a report's receipts
/// against. It does **not** run a real executor — that is `grain-turn`'s
/// `ToolGatewayMinter` — so it only exercises the SEAM (that every admitted receipt
/// carries a bound `turn_receipt_hash`), never the genuine kernel transition.
///
/// [`refusing_after`](SyntheticMinter::refusing_after) models the executor's
/// host-side refusal (its `calls_made` rate caveat biting after `n` admitted calls)
/// so a both-polarity test can drive the R2 refusal path without the kernel.
#[derive(Clone, Debug, Default)]
pub struct SyntheticMinter {
    seq: u64,
    minted: Vec<[u8; 32]>,
    refuse_after: Option<u64>,
}

impl SyntheticMinter {
    /// A minter that admits (mints) every action.
    pub fn new() -> SyntheticMinter {
        SyntheticMinter::default()
    }

    /// A minter that REFUSES (executor-style) once `n` turns have been minted —
    /// models the `calls_made` rate caveat biting host-side after `n` admitted
    /// calls, for the both-polarity R2 refusal test.
    pub fn refusing_after(n: u64) -> SyntheticMinter {
        SyntheticMinter {
            seq: 0,
            minted: Vec::new(),
            refuse_after: Some(n),
        }
    }

    /// The turn hashes this minter has committed, in order — the "committed-turn
    /// manifest" the grain-verify R2 tooth checks a report's receipts against.
    pub fn committed_turns(&self) -> &[[u8; 32]] {
        &self.minted
    }
}

impl GrainTurnMinter for SyntheticMinter {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        if let Some(n) = self.refuse_after {
            if self.minted.len() as u64 >= n {
                return Err(format!(
                    "executor refused the turn (synthetic calls_made caveat: {} of {n} used)",
                    self.minted.len()
                ));
            }
        }
        let mut h = BodyHasher::new(b"dregg-agent-synthetic-grain-turn-v1");
        h.u64(self.seq)
            .field(label.as_bytes())
            .u64(cost as u64)
            .u64(consumed_after as u64)
            .field(&cell_root);
        let hash = h.finalize();
        self.seq += 1;
        self.minted.push(hash);
        Ok(hash)
    }
}

// ---------------------------------------------------------------------------
// The per-action outcome + the receipt body.
// ---------------------------------------------------------------------------

/// What happened to one decided action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ActionOutcome {
    /// Cap ✓ · budget ✓ · ran · receipted.
    Admitted,
    /// Refused by the cap-gate: the cap is outside the agent's bundle. No draw, no
    /// receipt (fail-closed — the agent never reached outside its authority).
    CapRefused {
        /// The cap the action needed but the bundle did not grant.
        cap: String,
    },
    /// Refused by the meter: the budget is exhausted (the runaway is contained).
    /// No commit, no receipt.
    BudgetRefused {
        /// The headroom available when the draw was refused.
        headroom: i64,
    },
    /// **R2** — refused by the EXECUTOR when a [`GrainTurnMinter`] is present: the
    /// kernel turn for this action did not commit (the executor's own host-side
    /// caveat bit — e.g. the `calls_made` `FieldLte`/`Monotonic` rate ceiling). No
    /// draw, no effect, no receipt (fail-closed, exactly like the cap-gate). This
    /// is the meter enforced HOST-SIDE, not merely session-local.
    TurnRefused {
        /// Why the executor refused the turn (the leg of its caveat that bit).
        reason: String,
    },
}

/// One line of the run log: the action and what the braid did with it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActionRecord {
    /// The action's label.
    pub action: String,
    /// The outcome (admitted / cap-refused / budget-refused).
    pub outcome: ActionOutcome,
}

/// The signed, chained receipt of one **admitted** action — the re-witnessable
/// "what the agent did". Implements [`ReceiptBody`] so a run's receipts verify
/// end-to-end with [`verify_chain`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentReceipt {
    /// The producer-monotonic sequence (the chain position).
    pub seq: u64,
    /// The agent that took the action.
    pub agent: String,
    /// The action label (`invoke:search`, `cell-write:/scratch`, …).
    pub action: String,
    /// The budget units drawn for it.
    pub cost: i64,
    /// The agent's total consumed budget after this action.
    pub consumed_after: i64,
    /// The agent's remaining headroom after this action.
    pub headroom_after: i64,
    /// The agent's committed cell root after this action.
    pub cell_root: [u8; 32],
    /// For an admitted `invoke` dispatched to a live tool: the tool's verdict
    /// (`Some(true)` = pass/verified/healthy, `Some(false)` = fail/anomalous).
    /// `None` for non-invoke actions and for the no-toolkit local path. Bound
    /// into [`body_hash`](AgentReceipt::body_hash), so a tampered verdict breaks
    /// the signature — a forged "tests passed" is caught on re-witness.
    #[serde(default)]
    pub tool_ok: Option<bool>,
    /// The tool's summary, bound into the receipt alongside `tool_ok`.
    #[serde(default)]
    pub tool_summary: Option<String>,
    /// For an execution-witnessing `invoke` (`run_tests` / `verify_deploy` over a
    /// compute tier): the [`WitnessedRun`] binding `(command, code_root, result)`
    /// the tier run emitted. Bound into [`body_hash`](AgentReceipt::body_hash), so
    /// a tampered command / code-root / result breaks the signature; re-checked
    /// against a re-execution by [`verify_witnessed_qa`]. `None` for actions whose
    /// verdict is not a re-runnable tier execution.
    #[serde(default)]
    pub witnessed: Option<WitnessedRun>,
    /// The chained attestation (prev-hash link + ed25519 signature).
    pub attestation: Option<ReceiptAttestation>,
}

impl ReceiptBody for AgentReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"dregg-agent-action-receipt-v1");
        h.field(self.agent.as_bytes())
            .u64(self.seq)
            .field(self.action.as_bytes())
            .u64(self.cost as u64)
            .u64(self.consumed_after as u64)
            .u64(self.headroom_after as u64)
            .field(&self.cell_root);
        // Bind the tool verdict (present/absent marker + value), so a forged
        // verdict moves the body hash and breaks the signature on re-witness.
        match self.tool_ok {
            Some(ok) => {
                h.u64(1).bool(ok);
            }
            None => {
                h.u64(0);
            }
        }
        h.field(self.tool_summary.as_deref().unwrap_or("").as_bytes());
        // Bind the witnessed-execution binding (present marker + the command, the
        // code root, the exit, and the output digest), so a tampered command /
        // code-root / result moves the body hash and breaks the signature — and
        // so the bound the re-witness re-checks is itself signed.
        match &self.witnessed {
            Some(w) => {
                h.u64(1)
                    .field(w.command.as_bytes())
                    .field(w.code_root.as_bytes())
                    .u64(w.exit as u64)
                    .field(&w.output_digest);
            }
            None => {
                h.u64(0);
            }
        }
        h.finalize()
    }

    fn seq(&self) -> u64 {
        self.seq
    }

    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attestation.as_ref()
    }
}

// ---------------------------------------------------------------------------
// The run report — the proof + the bound the user gets back.
// ---------------------------------------------------------------------------

/// The output of an agent run: the **proof** (the receipt chain of everything it
/// did) and the **bound** (the budget cell's hard ceiling on everything it could
/// have done — un-drawn headroom is un-exercised authority).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentRunReport {
    /// The agent id.
    pub agent: String,
    /// The asset the budget is denominated in.
    pub asset: String,
    /// The spend ceiling (the hard bound).
    pub budget: i64,
    /// Total budget consumed over the run.
    pub consumed: i64,
    /// The un-drawn headroom — the ceiling on everything the agent could still
    /// have done (`budget - consumed`). The could-have bound, surfaced.
    pub headroom: i64,
    /// Actions admitted (cap ✓ · budget ✓ · ran · receipted).
    pub admitted: u64,
    /// Actions refused by the cap-gate (outside the bundle).
    pub cap_refused: u64,
    /// Actions refused by the meter (over the ceiling — runaway contained).
    pub budget_refused: u64,
    /// **R2** — actions refused by the EXECUTOR host-side (the grain turn-cell's
    /// own `calls_made` caveat bit; only nonzero when a [`GrainTurnMinter`] drives
    /// the run). `0` for the default parallel-universe path.
    #[serde(default)]
    pub turn_refused: u64,
    /// The receipt chain of every admitted action (re-witnessable via [`verify_chain`]).
    pub receipts: Vec<AgentReceipt>,
    /// The full ordered run log (every decided action + its outcome).
    pub log: Vec<ActionRecord>,
    /// The receipt-chain signer public key (the trust anchor a verifier pins).
    pub signer: [u8; 32],
    /// The agent's committed cell heap after the run.
    pub cells: BTreeMap<String, String>,
}

impl AgentRunReport {
    /// The receipt-chain tip (the final committed receipt hash), or `None` if the
    /// agent committed nothing.
    pub fn tip(&self) -> Option<[u8; 32]> {
        self.receipts.last().and_then(|r| r.receipt_hash())
    }

    /// The QA/ops verdicts the run produced: `(action, ok, summary)` for every
    /// admitted `invoke` that a live tool answered. The re-witnessable record of
    /// *what the agent's QA/monitoring found* (tests passed, deploy verified,
    /// node healthy — or not).
    pub fn tool_results(&self) -> Vec<(String, bool, String)> {
        self.receipts
            .iter()
            .filter_map(|r| {
                let ok = r.tool_ok?;
                Some((
                    r.action.clone(),
                    ok,
                    r.tool_summary.clone().unwrap_or_default(),
                ))
            })
            .collect()
    }

    /// The total budget drawn by admitted **spends** (priced `spend:<service>`
    /// actions) — the vendor outflow side of the P&L. A flat invoke / cell-op is
    /// not a spend and is excluded.
    pub fn spent_total(&self) -> i64 {
        self.receipts
            .iter()
            .filter(|r| r.action.starts_with("spend:"))
            .map(|r| r.cost)
            .sum()
    }

    /// The admitted spends as `(service, amount_cents)` — the vendor ledger line
    /// items, each traceable to a receipt.
    pub fn spends(&self) -> Vec<(String, i64)> {
        self.receipts
            .iter()
            .filter(|r| r.action.starts_with("spend:"))
            .map(|r| (r.action.clone(), r.cost))
            .collect()
    }

    /// `true` iff every tool the run invoked returned a passing verdict (and at
    /// least one tool ran). The one-line "did the QA pass?" rollup.
    pub fn all_tools_passed(&self) -> bool {
        let results = self.tool_results();
        !results.is_empty() && results.iter().all(|(_, ok, _)| *ok)
    }
}

/// The result of re-witnessing an agent run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentVerified {
    /// The number of admitted actions re-witnessed in the chain.
    pub actions: usize,
    /// The consumed budget the chain attests to.
    pub consumed: i64,
    /// The un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// The budget ceiling.
    pub budget: i64,
}

/// Why an agent run failed to re-witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentVerifyError {
    /// The receipt chain did not verify (forged / tampered / spliced).
    Chain(ChainError),
    /// The run's consumed budget exceeds the ceiling — the bound was violated
    /// (a forged report claiming more spend than the budget could permit).
    BoundViolated {
        /// The consumed total claimed.
        consumed: i64,
        /// The ceiling it exceeds.
        budget: i64,
    },
    /// The chain's final attested `consumed_after` disagrees with the report's
    /// `consumed` total (the proof and the bound do not agree).
    ConsumedMismatch {
        /// The report's claimed total.
        report: i64,
        /// The chain's final attested total.
        chain: i64,
    },
}

impl std::fmt::Display for AgentVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AgentVerifyError::Chain(e) => write!(f, "receipt chain did not verify: {e:?}"),
            AgentVerifyError::BoundViolated { consumed, budget } => write!(
                f,
                "bound violated: consumed {consumed} exceeds the budget ceiling {budget}"
            ),
            AgentVerifyError::ConsumedMismatch { report, chain } => write!(
                f,
                "proof/bound mismatch: report claims {report} consumed, the chain attests {chain}"
            ),
        }
    }
}

impl std::error::Error for AgentVerifyError {}

/// **Re-witness an agent run** the way a non-witness does (`dregg verify` for an
/// agent): (1) the receipt chain verifies — signed, unbroken, tamper-evident;
/// (2) the consumed budget stays at or under the ceiling (the hard bound holds);
/// (3) the chain's final attested consumption agrees with the report's total (the
/// proof and the bound agree). Needs only the report — no host trusted.
pub fn verify_agent_run(report: &AgentRunReport) -> Result<AgentVerified, AgentVerifyError> {
    verify_chain(&report.receipts).map_err(AgentVerifyError::Chain)?;
    if report.consumed > report.budget {
        return Err(AgentVerifyError::BoundViolated {
            consumed: report.consumed,
            budget: report.budget,
        });
    }
    let chain_consumed = report
        .receipts
        .last()
        .map(|r| r.consumed_after)
        .unwrap_or(0);
    if chain_consumed != report.consumed {
        return Err(AgentVerifyError::ConsumedMismatch {
            report: report.consumed,
            chain: chain_consumed,
        });
    }
    Ok(AgentVerified {
        actions: report.receipts.len(),
        consumed: report.consumed,
        headroom: report.headroom,
        budget: report.budget,
    })
}

/// What a re-execution of a [`WitnessedRun`] reproduces — the `(exit, output_digest)`
/// the tier produces when the command is run again against the same code. The
/// re-witness oracle ([`verify_witnessed_qa`]'s `rerun`) returns this; the
/// compute-tier wiring runs the workload, a test supplies a deterministic stand-in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReWitness {
    /// The exit / failure count the re-execution reported (`0` = pass).
    pub exit: i64,
    /// The output digest the re-execution produced.
    pub output_digest: [u8; 32],
}

/// Why an execution-witnessing (`run_tests` / `verify_deploy`) verdict failed to
/// re-witness — the runtime recorded something its execution does not actually
/// produce, or the code it tested is not the code that was deployed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessVerifyError {
    /// The witnessed run's `code_root` is not the deployed `content_root` — the
    /// tests ran against *different code* than what was deployed (or none).
    CodeRootMismatch {
        /// The action whose binding mismatched.
        action: String,
        /// The code root the run bound.
        bound: String,
        /// The deployed content root it must equal.
        deployed: String,
    },
    /// The re-execution could not be performed (the verifier could not reproduce
    /// the run — e.g. no source registered for this `code_root`). Fail-closed: an
    /// un-re-witnessable verdict is NOT accepted.
    NotReWitnessable {
        /// The action whose binding could not be re-executed.
        action: String,
        /// The command the binding named.
        command: String,
    },
    /// The re-execution produced a *different* result than the runtime recorded —
    /// a lying runtime is caught here (the recorded verdict does not match the
    /// witnessed execution).
    ExecutionMismatch {
        /// The action whose result mismatched.
        action: String,
        /// What the runtime recorded.
        recorded: ReWitness,
        /// What the re-execution actually produced.
        rewitnessed: ReWitness,
    },
}

impl std::fmt::Display for WitnessVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WitnessVerifyError::CodeRootMismatch {
                action,
                bound,
                deployed,
            } => write!(
                f,
                "{action}: the tests ran against code_root {bound} but the deployed content_root is \
                 {deployed} — the QA did not run on the deployed code"
            ),
            WitnessVerifyError::NotReWitnessable { action, command } => write!(
                f,
                "{action}: the witnessed run `{command}` could not be re-executed (no reproducible \
                 source) — an un-re-witnessable verdict is not accepted"
            ),
            WitnessVerifyError::ExecutionMismatch {
                action,
                recorded,
                rewitnessed,
            } => write!(
                f,
                "{action}: the recorded result {recorded:?} does not match the re-witnessed \
                 execution {rewitnessed:?} — the runtime recorded a verdict its execution does not \
                 produce"
            ),
        }
    }
}

impl std::error::Error for WitnessVerifyError {}

/// What re-witnessing the execution-witnessing verdicts of a run found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessVerified {
    /// The number of witnessed runs (`run_tests` / `verify_deploy`) re-executed
    /// and confirmed.
    pub witnessed: usize,
    /// How many of them passed (exit `0`).
    pub passed: usize,
}

/// **Re-witness the execution-bound QA verdicts of a run** — the Layer-3 check
/// that lifts `agent verify` from "the runtime committed X and couldn't edit it"
/// to "the substrate ran *these tests* on *the deployed code* with *this result*".
///
/// For every receipt carrying a [`WitnessedRun`] binding it checks:
///
/// 1. **the code is the deployed code** — `code_root == deployed_root` (the tests
///    ran on what was actually deployed, not arbitrary code), and
/// 2. **the result matches the execution** — re-running the bound `(command,
///    code_root)` through `rerun` reproduces the bound `(exit, output_digest)`. A
///    runtime that recorded a verdict its execution does not produce is caught
///    here (the binding mismatches on re-execution); an un-re-executable binding
///    is rejected fail-closed.
///
/// `rerun` is the re-execution oracle: the compute-tier wiring runs the workload
/// again (`run_tests` rides `crate::run_workload`); it returns `None` when it
/// cannot reproduce the run (no registered source for that `code_root`). This is
/// the dregg-side witness; the residual is that `rerun` still executes in the
/// same compute substrate — full operator-independence needs the tier run itself
/// attested by the federation / light client (the in-circuit witness, named in
/// `docs/VISION-NEXT-PRODUCT.md`).
///
/// Run [`verify_agent_run`] first (the chain + bound); this is the execution leg.
pub fn verify_witnessed_qa(
    report: &AgentRunReport,
    deployed_root: &str,
    rerun: impl Fn(&WitnessedRun) -> Option<ReWitness>,
) -> Result<WitnessVerified, WitnessVerifyError> {
    let mut witnessed = 0usize;
    let mut passed = 0usize;
    for r in &report.receipts {
        let Some(w) = &r.witnessed else { continue };
        witnessed += 1;
        // (1) the tests ran on the deployed code.
        if w.code_root != deployed_root {
            return Err(WitnessVerifyError::CodeRootMismatch {
                action: r.action.clone(),
                bound: w.code_root.clone(),
                deployed: deployed_root.to_string(),
            });
        }
        // (2) the recorded result matches a re-execution of the witnessed turn.
        let Some(re) = rerun(w) else {
            return Err(WitnessVerifyError::NotReWitnessable {
                action: r.action.clone(),
                command: w.command.clone(),
            });
        };
        let recorded = ReWitness {
            exit: w.exit,
            output_digest: w.output_digest,
        };
        if re != recorded {
            return Err(WitnessVerifyError::ExecutionMismatch {
                action: r.action.clone(),
                recorded,
                rewitnessed: re,
            });
        }
        if w.passed() {
            passed += 1;
        }
    }
    Ok(WitnessVerified { witnessed, passed })
}

// ---------------------------------------------------------------------------
// A deployed agent handle.
// ---------------------------------------------------------------------------

/// A deployed agent: its id, the cap bundle (the encoded `dga1_` credential —
/// bearer authority), the granted cap set (for display + the no-amplify check),
/// and the budget ceiling. A budget cell for `id` is open in the cloud's meter.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AgentHandle {
    /// The agent id (the meter subject + receipt identity).
    pub id: String,
    /// The cap bundle as the encoded `dga1_` bearer credential.
    pub credential: String,
    /// The granted cap strings (display form; a prefix renders with `*`).
    pub caps: Vec<String>,
    /// The granted [`CapGrant`]s (exact + resource prefixes) — the no-amplify
    /// `covers` check `deploy_subagent` uses.
    #[serde(default)]
    pub grants: Vec<CapGrant>,
    /// The budget ceiling.
    pub budget: i64,
    /// The asset.
    pub asset: String,
    /// The cost charged per action.
    pub cost_per_action: i64,
    /// The block actions are metered at (the run block).
    pub block: i64,
}

// ---------------------------------------------------------------------------
// The cloud — deploy, run, attenuate.
// ---------------------------------------------------------------------------

/// Why deploying / attenuating an agent failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentError {
    /// The budget cell could not be opened / attenuated (e.g. a sub-agent budget
    /// that tried to widen past the parent — the meter refuses it).
    Budget(MeterError),
    /// The parent credential did not decode (an attenuation off a malformed handle).
    Cred(WireError),
    /// A sub-agent's cap bundle tried to widen past the parent (the no-amplify
    /// lattice rule: a child may only narrow).
    Widen {
        /// The cap the child requested that the parent does not hold.
        cap: String,
    },
}

impl std::fmt::Display for AgentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AgentError::Budget(e) => write!(f, "budget refused: {e}"),
            AgentError::Cred(e) => write!(f, "credential decode failed: {e}"),
            AgentError::Widen { cap } => write!(
                f,
                "sub-agent cap `{cap}` is outside the parent bundle (a child may only narrow)"
            ),
        }
    }
}

impl std::error::Error for AgentError {}

/// The Verifiable Agent Cloud: it holds the root authority + the shared meter, and
/// **deploys** agents (open a budget cell + mint a cap bundle), **runs** them
/// confined (every action cap-gated + metered + receipted), and **attenuates**
/// sub-agents (a narrower child budget + a narrower child credential).
pub struct AgentCloud {
    root: RootKey,
    meter: ReplenishingMeter,
}

impl Default for AgentCloud {
    fn default() -> Self {
        AgentCloud::new()
    }
}

impl AgentCloud {
    /// A fresh cloud with a random root authority.
    pub fn new() -> AgentCloud {
        AgentCloud {
            root: RootKey::generate(),
            meter: ReplenishingMeter::new(),
        }
    }

    /// A cloud with a deterministic root (tests / reproducible deploys).
    pub fn from_seed(seed: [u8; 32]) -> AgentCloud {
        AgentCloud {
            root: RootKey::from_seed(seed),
            meter: ReplenishingMeter::new(),
        }
    }

    /// The root public key a verifier checks the agents' cap bundles under.
    pub fn root_public(&self) -> PublicKey {
        self.root.public()
    }

    /// A receipt-chain secret derived from this cloud's (secret) root key, domain
    /// separated. Because the root secret is never published (only its public half
    /// rides the credential), the derived receipt seed is unpredictable to a
    /// report-holder — yet reproducible for a seeded cloud (`from_seed`). Used for a
    /// one-shot [`run`](AgentCloud::run); a persistent session persists its own
    /// random secret instead (see [`crate::session::Session`]).
    fn derived_receipt_secret(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"dregg-agent-receipt-chain-seed-v2");
        h.field(&self.root.secret_bytes());
        h.finalize()
    }

    /// **Deploy** an agent: open its replenishing-budget cell and mint its cap
    /// bundle (a `dga1_` credential granting exactly the spec's services + cells).
    pub fn deploy(&self, spec: &AgentSpec) -> Result<AgentHandle, AgentError> {
        self.meter
            .open(&spec.id, spec.budget_terms())
            .map_err(AgentError::Budget)?;
        let grants = spec.grant_bundle();
        let caps = spec.caps();
        let credential = mint_grants(&self.root, &grants, None).encode();
        Ok(AgentHandle {
            id: spec.id.clone(),
            credential,
            caps,
            grants,
            budget: spec.budget,
            asset: spec.asset.clone(),
            cost_per_action: spec.cost_per_action,
            block: spec.start,
        })
    }

    /// **Deploy a sub-agent**, attenuated off `parent`: a child budget (the meter
    /// refuses any widening — child budget ≤ parent, child may not refill faster)
    /// AND a child credential genuinely attenuated off the parent's real chain
    /// (`attenuate_caps`, the no-amplify lattice). A child cap outside the parent
    /// bundle is refused up front ([`AgentError::Widen`]) and is unreachable on
    /// the wire even if it were not.
    pub fn deploy_subagent(
        &self,
        parent: &AgentHandle,
        child: &AgentSpec,
    ) -> Result<AgentHandle, AgentError> {
        let child_grants = child.grant_bundle();
        let child_caps = child.caps();
        // (1) the no-amplify rule: every child grant must be COVERED by some parent
        // grant (exact==exact, or a parent prefix covering a child exact/prefix —
        // a child can only narrow a resource scope, never widen it).
        for cg in &child_grants {
            if !parent.grants.iter().any(|pg| pg.covers(cg)) {
                return Err(AgentError::Widen { cap: cg.display() });
            }
        }
        // (2) the child budget cell, attenuated off the parent (the meter refuses
        // a widening child — larger ceiling / faster refill).
        self.meter
            .attenuate_child(
                &parent.id,
                &child.id,
                child.budget,
                child.period,
                child.refill,
                child.refill_max,
                child.start,
            )
            .map_err(AgentError::Budget)?;
        // (3) the child credential, attenuated off the parent's real chain. Decode
        // the parent's bearer token, append the narrower cap caveat, re-encode —
        // the child verifies under the SAME root, and the parent's meet still
        // rejects anything the child tried to widen to.
        let parent_cred = Credential::decode(&parent.credential).map_err(AgentError::Cred)?;
        let child_cred = attenuate_grants(parent_cred, &child_grants, None);
        Ok(AgentHandle {
            id: child.id.clone(),
            credential: child_cred.encode(),
            caps: child_caps,
            grants: child_grants,
            budget: child.budget,
            asset: child.asset.clone(),
            cost_per_action: child.cost_per_action,
            block: child.start,
        })
    }

    /// **Run** `handle` confined against the local (no-live-tool) path: drive
    /// `brain`'s decided actions, and for each one — cap-gate it (refused outside
    /// the bundle), meter it (drawn from the budget cell, refused when
    /// exhausted), run it, and seal a chained receipt. An `invoke` here leaves
    /// the committed heap unchanged (there is no live service). Returns the proof
    /// (the receipt chain) + the bound (the budget ceiling and the un-drawn
    /// headroom). To give `invoke` a *real* effect (run the tests / verify the
    /// deploy / check health), use [`run_with_toolkit`](AgentCloud::run_with_toolkit).
    pub fn run(&self, handle: &AgentHandle, brain: &mut dyn AgentBrain) -> AgentRunReport {
        self.run_inner(handle, brain, None)
    }

    /// **Run** `handle` confined with a live [`ToolKit`]: identical to
    /// [`run`](AgentCloud::run) on the authority + bound + receipt rails, but an
    /// admitted `invoke:<service>` is dispatched to the toolkit (it runs the
    /// tests / verifies the deploy / checks health) and the tool's verdict is
    /// **bound into that action's receipt**. So the whole QA/ops sequence —
    /// deploy → test → verify → monitor — lands in one re-witnessable receipt
    /// chain: a self-verifying coding/ops agent. The teeth are unchanged: a tool
    /// not in the cap bundle is refused before it runs, an over-budget call is
    /// bounded, and a forged verdict breaks the receipt signature.
    pub fn run_with_toolkit(
        &self,
        handle: &AgentHandle,
        brain: &mut dyn AgentBrain,
        toolkit: &dyn ToolKit,
    ) -> AgentRunReport {
        self.run_inner(handle, brain, Some(toolkit))
    }

    fn run_inner(
        &self,
        handle: &AgentHandle,
        brain: &mut dyn AgentBrain,
        toolkit: Option<&dyn ToolKit>,
    ) -> AgentRunReport {
        // A one-shot run is a session of exactly one goal: a fresh persistent
        // state, driven once, snapshotted into a report. Its receipt-chain secret is
        // derived from THIS cloud's (secret) root key — reproducible under
        // `AgentCloud::from_seed`, unpredictable under `AgentCloud::new`, and never a
        // public function of the agent id.
        let mut state = SessionState::from_secret(self.derived_receipt_secret());
        self.drive_state(handle, brain, toolkit, None, &mut state);
        self.report_snapshot(handle, &state)
    }

    /// **Run one goal of a persistent [`Session`]** against `state`: drive the
    /// brain's decided actions through the SAME cap-gate · budget · receipt braid
    /// as [`run`](AgentCloud::run), but thread the result into the *persistent*
    /// `state` — the receipt chain keeps linking, the budget keeps drawing down
    /// (the meter cell is the cloud's, so it persists across goals), and the
    /// monotonic seq continues. Returns the **cumulative** report so far (the
    /// whole session as one re-witnessable artifact). The interactive twin of
    /// [`run_with_toolkit`](AgentCloud::run_with_toolkit): call it once per goal a
    /// user types, and the budget/chain accumulate across the conversation.
    pub fn run_goal(
        &self,
        handle: &AgentHandle,
        state: &mut SessionState,
        brain: &mut dyn AgentBrain,
        toolkit: &dyn ToolKit,
    ) -> AgentRunReport {
        self.run_goal_minted(handle, state, brain, toolkit, None)
    }

    /// **[`run_goal`](AgentCloud::run_goal) welded to a genuine kernel turn per
    /// admitted action (R2).** Identical on every authority · bound · receipt rail,
    /// but when a [`GrainTurnMinter`] is supplied each admitted action first becomes
    /// a REAL committed executor turn on the grain turn-cell, and that turn's
    /// `turn_hash` is sealed into the action's [`AgentReceipt`] as its
    /// [`turn_receipt_hash`](crate::receipt::ReceiptAttestation::turn_receipt_hash)
    /// — the receipt becomes a VIEW over the kernel transition. A turn the executor
    /// REFUSES (its host-side `calls_made` caveat) admits nothing: the action is
    /// [`TurnRefused`](ActionOutcome::TurnRefused), drawing no budget and sealing no
    /// receipt. Passing `None` is exactly [`run_goal`](AgentCloud::run_goal).
    pub fn run_goal_minted(
        &self,
        handle: &AgentHandle,
        state: &mut SessionState,
        brain: &mut dyn AgentBrain,
        toolkit: &dyn ToolKit,
        minter: Option<&mut dyn GrainTurnMinter>,
    ) -> AgentRunReport {
        self.drive_state(handle, brain, Some(toolkit), minter, state);
        self.report_snapshot(handle, state)
    }

    /// The **cumulative report of a session so far** — the whole receipt chain +
    /// the current bound (drawn vs ceiling), without driving another goal. What
    /// [`crate::session::Session::verify`] re-witnesses, and what a `verify`
    /// command writes out. Host-untrusted: needs only the cloud's meter (for the
    /// live consumed total) and the persistent `state`.
    pub fn session_report(&self, handle: &AgentHandle, state: &SessionState) -> AgentRunReport {
        self.report_snapshot(handle, state)
    }

    /// **Restore a session's prior consumption at re-attach.** A hosted session is
    /// rented per SSH connection, but each fresh attach process opens a fresh
    /// in-memory meter — so without this the budget silently RESETS to full on every
    /// reconnect and a tenant can spend unbounded across detach/re-attach. The host
    /// loads the account's persisted cumulative consumed total (the durable
    /// [`crate::session_store`]) and calls this once, right after [`deploy`], to
    /// pre-charge the meter by `prior_consumed` so the ceiling is drawn down exactly
    /// as it was at detach and an over-budget draw is refused ACROSS the reconnect.
    ///
    /// It also seeds a genesis "carryover" receipt so the re-attached chain's final
    /// `consumed_after` agrees with the meter's `consumed` even before the first new
    /// action (so [`crate::session::Session::verify`] holds on a bare re-attach).
    /// `prior_consumed` is clamped to the ceiling — a corrupt stored value can never
    /// exceed the bound. A no-op for `prior_consumed <= 0`.
    ///
    /// [`deploy`]: AgentCloud::deploy
    pub fn restore_consumed(
        &self,
        handle: &AgentHandle,
        state: &mut SessionState,
        prior_consumed: i64,
    ) {
        let prior = prior_consumed.clamp(0, handle.budget);
        if prior == 0 {
            return;
        }
        // Pre-charge the meter under the reserved carryover key (a negative period
        // that can never collide with an in-session per-action draw key, `seq >= 0`)
        // so `drawn_total` reflects the prior spend and every subsequent draw is
        // gated against the already-drawn-down headroom — over-budget refused across
        // the reconnect, exactly as if the tenant never detached.
        let _ = self.meter.draw(
            &MeterKey::new(&handle.id, CARRYOVER_PERIOD),
            prior,
            handle.block,
        );
        // Seed a genesis carryover receipt so the chain's final `consumed_after`
        // equals the reported consumed total even with zero new actions this attach.
        let consumed = self.meter.drawn_total(&handle.id);
        let mut receipt = AgentReceipt {
            seq: state.seq,
            agent: handle.id.clone(),
            action: "carryover:prior-session-spend".to_string(),
            cost: 0,
            consumed_after: consumed,
            headroom_after: (handle.budget - consumed).max(0),
            cell_root: cell_root(&state.cells),
            tool_ok: None,
            tool_summary: None,
            witnessed: None,
            attestation: None,
        };
        receipt.attestation = Some(state.chain.seal(receipt.body_hash(), state.seq, None));
        state.receipts.push(receipt);
        state.seq += 1;
    }

    /// A fresh, host-untrusted report snapshot from the persistent `state` — the
    /// cumulative receipt chain + the current bound (drawn so far vs the ceiling).
    fn report_snapshot(&self, handle: &AgentHandle, state: &SessionState) -> AgentRunReport {
        let consumed = self.meter.drawn_total(&handle.id);
        AgentRunReport {
            agent: handle.id.clone(),
            asset: handle.asset.clone(),
            budget: handle.budget,
            consumed,
            headroom: (handle.budget - consumed).max(0),
            admitted: state.admitted,
            cap_refused: state.cap_refused,
            budget_refused: state.budget_refused,
            turn_refused: state.turn_refused,
            receipts: state.receipts.clone(),
            log: state.log.clone(),
            signer: state.chain.signer_public(),
            cells: state.cells.clone(),
        }
    }

    /// The core run loop, parameterized over the *persistent* [`SessionState`]: a
    /// one-shot run drives a fresh state once; a session drives the same state
    /// across many goals. Identical authority · bound · receipt teeth either way.
    fn drive_state(
        &self,
        handle: &AgentHandle,
        brain: &mut dyn AgentBrain,
        toolkit: Option<&dyn ToolKit>,
        mut minter: Option<&mut dyn GrainTurnMinter>,
        state: &mut SessionState,
    ) {
        let cred = Credential::decode(&handle.credential)
            .expect("a deployed handle always carries a valid credential");
        let root_pub = self.root.public();
        // The brain is per-goal; its step ordinal restarts at 0 each goal. The
        // chain, cells, receipts, counts, and seq all live in `state` and persist.
        let mut step = 0u64;

        while let Some(action) = brain.next_action(step) {
            step += 1;
            let label = action.label();

            // (1) AUTHORITY — cap-gate the action's required cap against the bundle.
            // Refused outside the bundle BEFORE any draw or commit (fail-closed).
            // An Op resolves its resource cap through the toolkit (which owns the
            // workdir), so a relative path is gated against its absolute prefix.
            let cap = match (&action, toolkit) {
                (AgentAction::Op(call), Some(tk)) => tk.op_cap(call),
                _ => action.required_cap(),
            };
            if cred
                .verify(&root_pub, &cap_context(&cap, handle.block.max(0) as u64))
                .is_err()
            {
                state.cap_refused += 1;
                brain.observe(&ActionObservation {
                    action: label.clone(),
                    admitted: false,
                    refusal: Some(format!("outside the cap bundle: {cap}")),
                    tool_ok: None,
                    tool_summary: None,
                });
                state.log.push(ActionRecord {
                    action: label,
                    outcome: ActionOutcome::CapRefused { cap },
                });
                continue;
            }

            let draw_amount = action.draw_cost(handle.cost_per_action);

            // (2) R2 — the KERNEL TURN admission. When a `GrainTurnMinter` is
            // present, this admitted action becomes a GENUINE committed executor
            // turn on the grain turn-cell; its `turn_hash` is sealed into the
            // receipt below, so the receipt is a VIEW over a real kernel transition.
            // The minter is ALSO an admission surface: an `Err` is the EXECUTOR
            // refusing the turn host-side (its own `calls_made` caveat) — the action
            // admits NOTHING (no draw, no effect, no receipt), exactly like the
            // cap-gate. `projected_consumed` is the meter's post-draw total (the
            // value the receipt's `consumed_after` will carry), bound into the turn.
            // Placed BEFORE the draw so a refused turn leaves the meter untouched and
            // the chain/meter stay consistent (`verify_agent_run` holds).
            let turn_hash: Option<[u8; 32]> = match minter.as_deref_mut() {
                None => None,
                Some(m) => {
                    let projected_consumed = self.meter.drawn_total(&handle.id) + draw_amount;
                    match m.mint_turn(
                        &label,
                        draw_amount,
                        projected_consumed,
                        cell_root(&state.cells),
                    ) {
                        Ok(h) => Some(h),
                        Err(reason) => {
                            state.turn_refused += 1;
                            brain.observe(&ActionObservation {
                                action: label.clone(),
                                admitted: false,
                                refusal: Some(format!(
                                    "executor refused the kernel turn: {reason}"
                                )),
                                tool_ok: None,
                                tool_summary: None,
                            });
                            state.log.push(ActionRecord {
                                action: label,
                                outcome: ActionOutcome::TurnRefused { reason },
                            });
                            continue;
                        }
                    }
                }
            };

            // (3) BOUND — draw the action's cost from the budget cell. A flat
            // action draws `cost_per_action`; a `Spend` draws its variable
            // `amount_cents` (the priced spend) so the budget cell IS the dollar
            // ceiling. An over-ceiling draw refuses the action in-band — BEFORE the
            // priced tool runs, so no money moves; the draw is exactly-once per
            // (agent, seq).
            let key = MeterKey::new(&handle.id, state.seq as i64);
            match self.meter.draw(&key, draw_amount, handle.block) {
                Ok(_) => {}
                Err(MeterError::OverBudget { headroom, .. }) => {
                    state.budget_refused += 1;
                    brain.observe(&ActionObservation {
                        action: label.clone(),
                        admitted: false,
                        refusal: Some(format!("budget exhausted (headroom {headroom})")),
                        tool_ok: None,
                        tool_summary: None,
                    });
                    state.log.push(ActionRecord {
                        action: label,
                        outcome: ActionOutcome::BudgetRefused { headroom },
                    });
                    continue;
                }
                Err(_other) => {
                    // Any other budget refusal (structural) is also contained,
                    // reported with zero headroom (fail-closed).
                    state.budget_refused += 1;
                    brain.observe(&ActionObservation {
                        action: label.clone(),
                        admitted: false,
                        refusal: Some("budget refused".to_string()),
                        tool_ok: None,
                        tool_summary: None,
                    });
                    state.log.push(ActionRecord {
                        action: label,
                        outcome: ActionOutcome::BudgetRefused { headroom: 0 },
                    });
                    continue;
                }
            }

            // (4) RUN the admitted effect against the agent's own cell heap. An
            // `invoke` is dispatched to the live toolkit when one is present (run
            // the tests / verify the deploy / check health); its verdict is
            // captured and bound into the receipt below. Without a toolkit (the
            // local path) an `invoke` leaves the heap unchanged.
            let (mut tool_ok, mut tool_summary): (Option<bool>, Option<String>) = (None, None);
            let mut tool_witnessed: Option<WitnessedRun> = None;
            match &action {
                AgentAction::CellWrite { path, value } => {
                    state.cells.insert(path.clone(), value.clone());
                }
                AgentAction::Invoke { service } => {
                    if let Some(tk) = toolkit {
                        let oc = tk.invoke(service, None, &state.cells);
                        tool_ok = Some(oc.ok);
                        tool_summary = Some(oc.summary);
                        tool_witnessed = oc.witnessed;
                    }
                }
                AgentAction::Spend {
                    service,
                    amount_cents,
                } => {
                    // The budget already admitted this draw (over-ceiling refused
                    // above), so reaching here means the spend is funded — dispatch
                    // the priced tool (the Stripe payout) with the amount in hand.
                    if let Some(tk) = toolkit {
                        let oc = tk.invoke(service, Some(*amount_cents), &state.cells);
                        tool_ok = Some(oc.ok);
                        tool_summary = Some(oc.summary);
                        tool_witnessed = oc.witnessed;
                    }
                }
                // cell_read leaves the committed heap unchanged.
                AgentAction::CellRead { .. } => {}
                AgentAction::Op(call) => {
                    // The cap-gate already admitted this tool+resource; run the real
                    // op (shell / fs / http / git) and bind its witnessed result.
                    if let Some(tk) = toolkit {
                        let oc = tk.run_op(call, &state.cells);
                        tool_ok = Some(oc.ok);
                        tool_summary = Some(oc.summary);
                        tool_witnessed = oc.witnessed;
                    }
                }
            }

            // (5) RECEIPT — seal the admitted action (and any tool verdict) into
            // the PERSISTENT chain (it keeps linking across goals in a session).
            let consumed = self.meter.drawn_total(&handle.id);
            let headroom = self.meter.headroom(&handle.id, handle.block);
            // Capture the verdict for the brain before it is moved into the receipt.
            let obs_tool_summary = tool_summary.clone();
            let mut receipt = AgentReceipt {
                seq: state.seq,
                agent: handle.id.clone(),
                action: label.clone(),
                cost: draw_amount,
                consumed_after: consumed,
                headroom_after: headroom,
                cell_root: cell_root(&state.cells),
                tool_ok,
                tool_summary: tool_summary.take(),
                witnessed: tool_witnessed,
                attestation: None,
            };
            // Seal with the R2 kernel-turn link: `Some(turn_hash)` when a minter
            // committed the action's genuine executor turn (the receipt is a VIEW of
            // it — a tampered link breaks the signature, see `receipt.rs`), `None`
            // on the default parallel-universe path.
            receipt.attestation = Some(state.chain.seal(receipt.body_hash(), state.seq, turn_hash));
            state.receipts.push(receipt);
            brain.observe(&ActionObservation {
                action: label.clone(),
                admitted: true,
                refusal: None,
                tool_ok,
                tool_summary: obs_tool_summary,
            });
            state.log.push(ActionRecord {
                action: label,
                outcome: ActionOutcome::Admitted,
            });
            state.admitted += 1;
            state.seq += 1;
        }
    }
}

/// The **persistent run state of a [`Session`]** — everything that must survive
/// across goals so a hosted agent session accumulates into ONE re-witnessable
/// artifact. Held by the cloud's caller (a [`crate::session::Session`]) and
/// threaded through [`AgentCloud::run_goal`] once per goal:
///
/// - the **receipt chain** keeps linking (goal 2's first receipt's prev-hash is
///   goal 1's last receipt — a spliced-out goal breaks the chain);
/// - the committed **cell heap** carries forward (a value written in goal 1 is
///   still readable in goal 3);
/// - the running **counts** and the monotonic **seq** continue, so the meter
///   draws stay exactly-once per `(agent, seq)` across the whole session.
///
/// The budget itself lives in the cloud's meter cell keyed by the agent id, so it
/// draws down across goals automatically — this state only needs the seq cursor
/// to keep the per-action draw keys unique.
pub struct SessionState {
    chain: ReceiptChain,
    cells: BTreeMap<String, String>,
    receipts: Vec<AgentReceipt>,
    log: Vec<ActionRecord>,
    admitted: u64,
    cap_refused: u64,
    budget_refused: u64,
    turn_refused: u64,
    seq: u64,
}

impl SessionState {
    /// Fresh persistent state seeded from an explicit 32-byte **receipt-chain
    /// secret**. That secret IS the ed25519 signing seed for the whole chain
    /// ([`ReceiptSigner::from_seed`](crate::receipt::ReceiptSigner::from_seed)), so
    /// whoever holds it can sign the chain. It MUST therefore be a per-session
    /// RANDOM secret — and, for a session that must survive detach/re-attach, one
    /// that is PERSISTED so a resumed session recovers the SAME key (see
    /// [`crate::session::Session`] / [`crate::session_store::ConsumedStore`]).
    ///
    /// It must NEVER be a public function of the agent id: the agent id is printed
    /// in cleartext in every report (`report.agent`, `receipt.agent`), so a hashed
    /// id would let ANY holder of a report re-derive the signing key and forge a
    /// fully self-consistent chain — exactly the third-party-forgery hole this
    /// closes. The report still exposes only the ed25519 PUBLIC key
    /// ([`report.signer`](AgentRunReport::signer)); the secret stays host-side.
    pub fn from_secret(receipt_secret: [u8; 32]) -> SessionState {
        SessionState {
            chain: ReceiptChain::from_seed(receipt_secret),
            cells: BTreeMap::new(),
            receipts: Vec::new(),
            log: Vec::new(),
            admitted: 0,
            cap_refused: 0,
            budget_refused: 0,
            turn_refused: 0,
            seq: 0,
        }
    }

    /// Fresh persistent state with a freshly-generated RANDOM receipt-chain secret
    /// (OS CSPRNG). For an EPHEMERAL run whose chain need not survive re-attach; a
    /// persistent [`Session`](crate::session::Session) threads a persisted secret
    /// through [`from_secret`](SessionState::from_secret) instead.
    pub fn new_random() -> SessionState {
        SessionState::from_secret(fresh_receipt_secret())
    }

    /// The cumulative receipt chain so far (every admitted action across every
    /// goal) — the re-witnessable record of the whole session.
    pub fn receipts(&self) -> &[AgentReceipt] {
        &self.receipts
    }

    /// The full ordered run log so far (admitted + refused, across every goal).
    pub fn log(&self) -> &[ActionRecord] {
        &self.log
    }

    /// Admitted-action count across the session.
    pub fn admitted(&self) -> u64 {
        self.admitted
    }
    /// Cap-refused count across the session.
    pub fn cap_refused(&self) -> u64 {
        self.cap_refused
    }
    /// Budget-refused count across the session.
    pub fn budget_refused(&self) -> u64 {
        self.budget_refused
    }
    /// **R2** — executor-refused count across the session (the grain turn-cell's
    /// host-side `calls_made` caveat bit; `0` unless a [`GrainTurnMinter`] drove it).
    pub fn turn_refused(&self) -> u64 {
        self.turn_refused
    }
}

/// The reserved meter period for the carried-over prior consumption restored at
/// SSH re-attach ([`AgentCloud::restore_consumed`]). Negative so it can never
/// collide with an in-session per-action draw key (`MeterKey` period `= seq >= 0`).
const CARRYOVER_PERIOD: i64 = -1;

/// Generate a fresh, unpredictable 32-byte receipt-chain secret from OS randomness.
/// This is the ed25519 signing seed for a chain, so it must be a real CSPRNG draw —
/// never a function of any public value (the retired `receipt_seed(agent_id)` hashed
/// the cleartext agent id, which let any report-holder re-derive the key and forge
/// the chain; see [`SessionState::from_secret`]).
fn fresh_receipt_secret() -> [u8; 32] {
    let mut secret = [0u8; 32];
    getrandom::fill(&mut secret).expect("operating-system randomness is available");
    secret
}

/// The committed cell root: a domain-separated hash over the heap's `(key, value)`
/// pairs in sorted-key order (a `BTreeMap` is already sorted), so the root binds
/// the committed contents and a write moves it.
fn cell_root(cells: &BTreeMap<String, String>) -> [u8; 32] {
    let mut h = BodyHasher::new(b"dregg-agent-cell-root-v1");
    for (k, v) in cells {
        h.field(k.as_bytes()).field(v.as_bytes());
    }
    h.finalize()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A spec for an agent that may invoke `search` + `fetch` and touch `/scratch`,
    /// with a `budget`-unit ceiling at cost 1/action.
    fn demo_spec(id: &str, budget: i64) -> AgentSpec {
        AgentSpec::new(id, budget)
            .with_service("search")
            .with_service("fetch")
            .with_cell("/scratch")
    }

    // ── THE HAPPY PATH: cap-gated + metered + receipted + verifiable ──────────

    #[test]
    fn an_agent_run_is_capped_metered_and_receipted() {
        let cloud = AgentCloud::from_seed([1u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:alpha", 10)).unwrap();
        let plan = vec![
            AgentAction::Invoke {
                service: "search".into(),
            },
            AgentAction::CellWrite {
                path: "/scratch".into(),
                value: "note".into(),
            },
            AgentAction::CellRead {
                path: "/scratch".into(),
            },
        ];
        let report = cloud.run(&handle, &mut PlannedBrain::new(plan));

        assert_eq!(report.admitted, 3, "all three in-bundle actions ran");
        assert_eq!(report.cap_refused, 0);
        assert_eq!(report.budget_refused, 0);
        assert_eq!(report.consumed, 3, "three draws of cost 1");
        assert_eq!(report.headroom, 7, "the could-have bound: 10 − 3");
        assert_eq!(report.receipts.len(), 3, "one receipt per admitted action");
        // The proof re-witnesses without trusting the host.
        let v = verify_agent_run(&report).expect("the run re-witnesses");
        assert_eq!(v.actions, 3);
        assert_eq!(v.consumed, 3);
        // The cell write committed.
        assert_eq!(report.cells.get("/scratch"), Some(&"note".to_string()));
    }

    // ── TOOTH 1: an out-of-bundle invoke is REFUSED (cap-gate) ────────────────

    #[test]
    fn an_out_of_bundle_invoke_is_refused_and_not_receipted() {
        let cloud = AgentCloud::from_seed([2u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:beta", 10)).unwrap();
        let plan = vec![
            AgentAction::Invoke {
                service: "search".into(),
            }, // in bundle → admitted
            AgentAction::Invoke {
                service: "exfiltrate".into(),
            }, // OUT of bundle → refused
        ];
        let report = cloud.run(&handle, &mut PlannedBrain::new(plan));

        assert_eq!(report.admitted, 1, "only the in-bundle invoke ran");
        assert_eq!(report.cap_refused, 1, "the out-of-bundle invoke is refused");
        assert_eq!(report.consumed, 1, "the refused call drew nothing");
        assert_eq!(report.receipts.len(), 1, "the refused call left no receipt");
        // The refusal names the missing cap.
        let refused = report
            .log
            .iter()
            .find(|r| matches!(r.outcome, ActionOutcome::CapRefused { .. }))
            .unwrap();
        assert!(
            matches!(&refused.outcome, ActionOutcome::CapRefused { cap } if cap == "invoke:exfiltrate")
        );
    }

    // ── TOOTH 2: the runaway is BUDGET-BOUNDED (rate-bounded) ─────────────────

    #[test]
    fn a_runaway_is_contained_by_the_budget_ceiling() {
        let cloud = AgentCloud::from_seed([3u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:runaway", 5)).unwrap();
        // The agent tries to invoke `search` 100 times — a runaway.
        let plan: Vec<AgentAction> = (0..100)
            .map(|_| AgentAction::Invoke {
                service: "search".into(),
            })
            .collect();
        let report = cloud.run(&handle, &mut PlannedBrain::new(plan));

        assert_eq!(
            report.admitted, 5,
            "exactly budget/cost actions are admitted"
        );
        assert_eq!(report.budget_refused, 95, "the rest are rate-bounded");
        assert_eq!(report.consumed, 5, "consumption is capped at the ceiling");
        assert_eq!(
            report.headroom, 0,
            "the ceiling is fully drawn — nothing more is possible"
        );
        // The bound holds under re-witness.
        let v = verify_agent_run(&report).unwrap();
        assert_eq!(v.consumed, 5);
        assert!(v.consumed <= v.budget, "consumed never exceeds the ceiling");
    }

    // ── TOOTH 3: the receipt chain verifies, and tampering is caught ──────────

    #[test]
    fn the_receipt_chain_verifies_and_tampering_is_caught() {
        let cloud = AgentCloud::from_seed([4u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:gamma", 10)).unwrap();
        let plan = vec![
            AgentAction::Invoke {
                service: "search".into(),
            },
            AgentAction::Invoke {
                service: "fetch".into(),
            },
        ];
        let mut report = cloud.run(&handle, &mut PlannedBrain::new(plan));
        assert!(verify_agent_run(&report).is_ok());

        // Forge an action label after sealing → the signature no longer matches.
        report.receipts[0].action = "invoke:secret".into();
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    /// A spliced-out receipt breaks the chain link.
    #[test]
    fn removing_a_receipt_breaks_the_chain() {
        let cloud = AgentCloud::from_seed([5u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:delta", 10)).unwrap();
        let plan: Vec<AgentAction> = (0..4)
            .map(|_| AgentAction::Invoke {
                service: "search".into(),
            })
            .collect();
        let mut report = cloud.run(&handle, &mut PlannedBrain::new(plan));
        report.receipts.remove(1);
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BrokenLink { .. }))
        ));
    }

    // ── THE SPEND RAIL: a priced spend draws its variable amount, over-ceiling refused ──

    /// A struct-only toolkit for the spend tests: a `stripe_pay` priced tool that
    /// always succeeds, recording the amount it was handed.
    struct SpendKit;
    impl ToolKit for SpendKit {
        fn invoke(
            &self,
            service: &str,
            amount_cents: Option<i64>,
            _cells: &BTreeMap<String, String>,
        ) -> ToolOutcome {
            match (service, amount_cents) {
                ("stripe_pay", Some(a)) => ToolOutcome::pass(format!("paid {a}c")),
                _ => ToolOutcome::fail("not a priced spend".to_string()),
            }
        }
    }

    #[test]
    fn a_priced_spend_draws_its_amount_and_over_ceiling_is_refused_before_money_moves() {
        let cloud = AgentCloud::from_seed([70u8; 32]);
        // Budget 5000 cents; the spend tool is in the bundle.
        let handle = cloud
            .deploy(&AgentSpec::new("agent:spender", 5000).with_service("stripe_pay"))
            .unwrap();
        let plan = vec![
            AgentAction::Spend {
                service: "stripe_pay".into(),
                amount_cents: 1800,
            }, // ok → consumed 1800
            AgentAction::Spend {
                service: "stripe_pay".into(),
                amount_cents: 1200,
            }, // ok → consumed 3000, headroom 2000
            AgentAction::Spend {
                service: "stripe_pay".into(),
                amount_cents: 2500,
            }, // 2500 > 2000 headroom → REFUSED in-band, no payout
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &SpendKit);

        assert_eq!(report.admitted, 2, "two funded spends ran");
        assert_eq!(
            report.budget_refused, 1,
            "the over-ceiling spend is refused"
        );
        assert_eq!(report.consumed, 3000, "the variable amounts were drawn");
        assert_eq!(report.headroom, 2000, "the un-spent ceiling is the bound");
        assert_eq!(report.spent_total(), 3000, "the P&L vendor outflow");
        // The refused spend never reached the payout tool (no receipt for it).
        assert_eq!(report.receipts.len(), 2);
        // Every spend traces to a receipt and re-witnesses.
        verify_agent_run(&report).expect("the spend run re-witnesses");
        // A forged spend amount breaks the signature.
        let mut forged = report.clone();
        forged.receipts[0].cost = 1; // "I only paid 1c"
        assert!(matches!(
            verify_agent_run(&forged),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    // ── TOOTH 4: a sub-agent attenuates and cannot exceed the parent ──────────

    #[test]
    fn a_subagent_attenuates_and_cannot_exceed_the_parent() {
        let cloud = AgentCloud::from_seed([6u8; 32]);
        let parent = cloud.deploy(&demo_spec("agent:parent", 20)).unwrap();
        // The child gets HALF the budget and ONLY the `search` service.
        let child_spec = AgentSpec::new("agent:child", 8).with_service("search");
        let child = cloud.deploy_subagent(&parent, &child_spec).unwrap();

        // The child can invoke `search` up to its (narrower) ceiling, no more.
        let plan: Vec<AgentAction> = (0..50)
            .map(|_| AgentAction::Invoke {
                service: "search".into(),
            })
            .collect();
        let report = cloud.run(&child, &mut PlannedBrain::new(plan));
        assert_eq!(
            report.admitted, 8,
            "the child is bounded by its attenuated budget"
        );
        assert_eq!(report.consumed, 8);
        assert!(
            report.consumed <= parent.budget,
            "the child cannot exceed the parent ceiling"
        );

        // The child CANNOT invoke a service the parent had but the child didn't.
        let fetch_plan = vec![AgentAction::Invoke {
            service: "fetch".into(),
        }];
        let fetch_report = cloud.run(&child, &mut PlannedBrain::new(fetch_plan));
        assert_eq!(
            fetch_report.cap_refused, 1,
            "fetch is outside the child's narrowed bundle"
        );
        assert_eq!(fetch_report.admitted, 0);
    }

    /// A sub-agent that tries to WIDEN (a cap the parent never held, or a larger
    /// budget) is refused — the no-amplify lattice on both axes.
    #[test]
    fn a_widening_subagent_is_refused() {
        let cloud = AgentCloud::from_seed([7u8; 32]);
        let parent = cloud
            .deploy(&AgentSpec::new("agent:p", 10).with_service("search"))
            .unwrap();

        // Widen the cap bundle: the child asks for `fetch`, which the parent lacks.
        let wider_caps = AgentSpec::new("agent:c1", 5).with_service("fetch");
        assert!(matches!(
            cloud.deploy_subagent(&parent, &wider_caps),
            Err(AgentError::Widen { .. })
        ));

        // Widen the budget: the child asks for MORE budget than the parent.
        let wider_budget = AgentSpec::new("agent:c2", 1_000).with_service("search");
        assert!(matches!(
            cloud.deploy_subagent(&parent, &wider_budget),
            Err(AgentError::Budget(_))
        ));
    }

    // ── the could-have bound: un-drawn headroom = un-exercised authority ──────

    #[test]
    fn the_budget_proves_the_could_have_bound() {
        let cloud = AgentCloud::from_seed([8u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:bound", 100)).unwrap();
        let plan: Vec<AgentAction> = (0..7)
            .map(|_| AgentAction::Invoke {
                service: "search".into(),
            })
            .collect();
        let report = cloud.run(&handle, &mut PlannedBrain::new(plan));
        // It did 7 things; it could have done at most 93 more — the hard ceiling.
        assert_eq!(report.consumed, 7);
        assert_eq!(
            report.headroom, 93,
            "un-drawn headroom is the could-have bound"
        );
        assert_eq!(report.consumed + report.headroom, report.budget);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // R2 — the kernel-turn seam: admitted actions become VIEWS over kernel turns.
    // ═══════════════════════════════════════════════════════════════════════

    /// A trivial toolkit (every invoke passes) — the minted-run tests only exercise
    /// the R2 seam, not a live tool.
    struct NoKit;
    impl ToolKit for NoKit {
        fn invoke(
            &self,
            _service: &str,
            _amount_cents: Option<i64>,
            _cells: &BTreeMap<String, String>,
        ) -> ToolOutcome {
            ToolOutcome::pass("ok")
        }
    }

    // ── every admitted receipt carries the committed turn's hash, bound ───────
    #[test]
    fn r2_admitted_receipts_are_views_over_minted_kernel_turns() {
        let cloud = AgentCloud::from_seed([40u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:r2", 10)).unwrap();
        let mut state = SessionState::from_secret([0x9au8; 32]);
        let mut minter = SyntheticMinter::new();
        let plan = vec![
            AgentAction::Invoke {
                service: "search".into(),
            },
            AgentAction::CellWrite {
                path: "/scratch".into(),
                value: "note".into(),
            },
            AgentAction::Invoke {
                service: "fetch".into(),
            },
        ];
        let report = cloud.run_goal_minted(
            &handle,
            &mut state,
            &mut PlannedBrain::new(plan),
            &NoKit,
            Some(&mut minter),
        );

        assert_eq!(report.admitted, 3);
        assert_eq!(report.turn_refused, 0);
        // Every admitted receipt is a VIEW: its turn_receipt_hash is Some AND equals
        // the turn the minter committed for that action, in order.
        let minted = minter.committed_turns();
        assert_eq!(minted.len(), 3, "one committed turn per admitted action");
        for (r, &h) in report.receipts.iter().zip(minted) {
            assert_eq!(
                r.attestation.as_ref().unwrap().turn_receipt_hash,
                Some(h),
                "the receipt links to the genuine committed turn"
            );
        }
        // The whole run still re-witnesses (the turn link rode the signed body).
        verify_agent_run(&report).expect("a minted run re-witnesses");

        // A TAMPERED turn link breaks the signature (the receipt IS a view — the
        // link is bound into receipt_hash; see receipt.rs `turn_receipt_view_is_bound`).
        let mut forged = report.clone();
        forged.receipts[0]
            .attestation
            .as_mut()
            .unwrap()
            .turn_receipt_hash = Some([0u8; 32]);
        assert!(matches!(
            verify_agent_run(&forged),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    // ── the executor's host-side caveat REFUSES over-rate; refused admits nothing ─
    #[test]
    fn r2_an_executor_refusal_admits_nothing_and_the_run_stays_consistent() {
        let cloud = AgentCloud::from_seed([41u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:r2-refuse", 100)).unwrap();
        let mut state = SessionState::from_secret([0x9bu8; 32]);
        // The executor (synthetic calls_made caveat) admits only 2 turns, even
        // though the session budget (100) would allow all 5 — the meter is enforced
        // HOST-SIDE, not merely session-local.
        let mut minter = SyntheticMinter::refusing_after(2);
        let plan: Vec<AgentAction> = (0..5)
            .map(|_| AgentAction::Invoke {
                service: "search".into(),
            })
            .collect();
        let report = cloud.run_goal_minted(
            &handle,
            &mut state,
            &mut PlannedBrain::new(plan),
            &NoKit,
            Some(&mut minter),
        );

        assert_eq!(report.admitted, 2, "only the 2 executor-admitted turns ran");
        assert_eq!(report.turn_refused, 3, "the executor refused the other 3");
        assert_eq!(report.receipts.len(), 2, "a refused turn seals no receipt");
        assert_eq!(report.consumed, 2, "a refused turn draws no budget");
        // Refused-by-executor actions left the meter and chain consistent.
        verify_agent_run(&report).expect("the run re-witnesses after host-side refusals");
        // Both admitted receipts are genuine views.
        assert!(
            report.receipts.iter().all(|r| r
                .attestation
                .as_ref()
                .unwrap()
                .turn_receipt_hash
                .is_some())
        );
    }

    /// A forged report claiming more consumed than the chain attests is caught.
    #[test]
    fn a_forged_consumed_total_is_caught() {
        let cloud = AgentCloud::from_seed([9u8; 32]);
        let handle = cloud.deploy(&demo_spec("agent:forge", 10)).unwrap();
        let plan = vec![AgentAction::Invoke {
            service: "search".into(),
        }];
        let mut report = cloud.run(&handle, &mut PlannedBrain::new(plan));
        // Forge the consumed total downward (claim it did less than it did).
        report.consumed = 0;
        report.headroom = 10;
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::ConsumedMismatch { .. })
        ));
    }
}
