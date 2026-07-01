//! # `dregg-userspace-verify` — lint your turn before you spend gas.
//!
//! The SDK ([`dregg_turn::CallForest`] via the `sdk` turn builders, the
//! `intent` ring lowerings, the factory/polis plan builders) hands you a
//! **constructed-but-not-yet-submitted** artifact: a [`CallForest`] of
//! [`CallTree`] nodes, each carrying an [`Action`] with a list of
//! [`Effect`]s. Before you pay gas to submit it, you want an assurance
//! *verdict*: does this forest plausibly satisfy the five
//! `Dregg2.AssuranceCase` guarantees — or will the executor reject it (and
//! charge you anyway)?
//!
//! This toolkit is the **static, userspace, pre-submission** half of that
//! question. It reads the forest (never executes it — no executor, no
//! circuit, no proof) and checks the properties that ARE decidable from the
//! artifact alone:
//!
//!   * [`check_conservation`] — guarantee **B**. Per asset, the forest's
//!     value MOVES sum to exactly zero (`Transfer`s and signed
//!     `balance_change` deltas net out per `(asset)` column; note
//!     create/spend value is tracked per `asset_type`). A non-conserving
//!     forest is rejected by the executor's conservation law — find it here
//!     first.
//!   * [`check_no_amplification`] — guarantee **A**. Along the forest's
//!     delegation edges (a child node grants a capability), a granted cap
//!     must be an attenuation (bitwise-facet ⊆, narrower-or-equal target /
//!     expiry) of a cap the parent itself granted into that scope. Catches
//!     the structurally-amplifying grant the executor's non-amplification
//!     gate would reject.
//!   * [`check_wellformed`] — structural integrity. No `Authorization::
//!     Unchecked` outside genesis, no empty action, references resolve,
//!     `OneOf` carries no `Unchecked` candidate, balance-change deltas are
//!     present where the conservation pattern needs them.
//!   * [`check_ring_balance`] — the intent-ring specialization of B: a
//!     settlement ring's legs form a closed cycle that conserves PER ASSET
//!     (the userspace twin of `intent`'s `RingBalanced` / `settleRing_
//!     conserves`, checked statically before the ring is lowered+submitted).
//!
//! Each check returns a [`Verdict`] that, on failure, names the **precise
//! locus** (which root, which node path, which effect index, which asset)
//! so the SDK can point the user at the offending construction site.
//!
//! ## The honest static/dynamic boundary
//!
//! These checks are **necessary, not sufficient**. They certify the
//! userspace-decidable shape of the artifact; they do NOT — and CANNOT —
//! stand in for the executor or the proof. See [`boundary`] for the precise
//! list. In short:
//!
//!   * **Static (this crate, from the artifact alone):** per-asset move
//!     conservation, intra-forest delegation-edge attenuation, structural
//!     well-formedness, ring cycle-closure + per-asset balance.
//!   * **Dynamic (needs the executor / live state — NOT here):** whether the
//!     signer actually HELD the capability it grants (the c-list lookup),
//!     whether balances suffice (`from` has the value), credential/signature
//!     validity, caveat discharge against live `ShadowHostCtx`, nullifier
//!     freshness, and the whole-state commitment / proof (guarantees C, D, E
//!     and the *holding* half of A). For THOSE, route the forest through
//!     `dregg-intent::verified_settle` (the per-asset verified-executor fold)
//!     or submit and verify the receipt — this crate is the cheap pre-flight,
//!     not a substitute.

use std::collections::BTreeMap;

use dregg_cell::CapabilityRef;
use dregg_turn::action::{Authorization, Effect};
use dregg_turn::{CallForest, CallTree};

pub mod app;
pub mod boundary;
pub mod ffi;

#[cfg(test)]
mod tests;

/// A location within a [`CallForest`]: the path from the forest down to a
/// specific effect, used to point a user at the offending construction site.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Locus {
    /// Indices from the forest root down the tree (`[2, 0, 1]` = root 2,
    /// its child 0, that child's child 1).
    pub node_path: Vec<usize>,
    /// Index of the offending effect within that node's `effects`, if the
    /// finding is effect-specific.
    pub effect_index: Option<usize>,
    /// The asset column the finding concerns, if asset-specific
    /// (hex of the 32-byte asset id, or `"computron"` for the native
    /// `Transfer`/`balance_change` column).
    pub asset: Option<String>,
}

impl Locus {
    /// The forest-level (whole-artifact) locus — no specific node.
    pub fn forest() -> Self {
        Locus {
            node_path: Vec::new(),
            effect_index: None,
            asset: None,
        }
    }
    /// A node-level locus.
    pub fn node(node_path: Vec<usize>) -> Self {
        Locus {
            node_path,
            effect_index: None,
            asset: None,
        }
    }
    /// Attach an effect index.
    pub fn at_effect(mut self, i: usize) -> Self {
        self.effect_index = Some(i);
        self
    }
    /// Attach an asset column.
    pub fn at_asset(mut self, asset: impl Into<String>) -> Self {
        self.asset = Some(asset.into());
        self
    }
}

impl std::fmt::Display for Locus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.node_path.is_empty() {
            write!(f, "<forest>")?;
        } else {
            write!(f, "node ")?;
            for (i, p) in self.node_path.iter().enumerate() {
                if i > 0 {
                    write!(f, ".")?;
                }
                write!(f, "{p}")?;
            }
        }
        if let Some(e) = self.effect_index {
            write!(f, " effect[{e}]")?;
        }
        if let Some(a) = &self.asset {
            write!(f, " asset[{a}]")?;
        }
        Ok(())
    }
}

/// One failing finding: which guarantee, where, and why.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Finding {
    /// Which assurance guarantee this finding falls under
    /// (`"A"`/`"B"`/well-formedness/`"ring"`).
    pub guarantee: String,
    /// Where in the forest the problem is.
    pub locus: Locus,
    /// Human-readable explanation of the violation.
    pub message: String,
}

/// The result of one check: either `Pass` or a list of [`Finding`]s.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Verdict {
    /// The check passed: the property holds over the artifact (modulo the
    /// dynamic boundary).
    Pass,
    /// The check failed with one or more located findings.
    Fail(Vec<Finding>),
}

impl Verdict {
    /// The passing verdict (also the serde default for optional verdict fields
    /// like [`Assurance::exposure`], so older JSON that predates the field still
    /// deserializes as a clean pass).
    pub fn pass() -> Self {
        Verdict::Pass
    }
    /// `true` iff the verdict is [`Verdict::Pass`].
    pub fn is_pass(&self) -> bool {
        matches!(self, Verdict::Pass)
    }
    /// The findings (empty on `Pass`).
    pub fn findings(&self) -> &[Finding] {
        match self {
            Verdict::Pass => &[],
            Verdict::Fail(f) => f,
        }
    }
    /// Build a verdict from a findings vec (`Pass` iff empty).
    pub fn from_findings(findings: Vec<Finding>) -> Self {
        if findings.is_empty() {
            Verdict::Pass
        } else {
            Verdict::Fail(findings)
        }
    }
}

/// The combined verdict over all checks: one [`Verdict`] per check, plus a
/// roll-up `pass`.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Assurance {
    pub conservation: Verdict,
    pub no_amplification: Verdict,
    pub wellformed: Verdict,
    pub ring_balance: Verdict,
    /// The `≤` exposure ceiling — `Σ provisional-exposure ≤ reserve`
    /// ([`app::check_exposure_bound`]). Like [`Self::ring_balance`], this needs
    /// a schema (which reserve slot on which cell) it cannot infer from the bare
    /// forest, so [`analyze`] leaves it `Pass` (vacuously — no reserve to
    /// exceed); the FFI's `exposure` sub-request (or a direct
    /// `check_exposure_bound` call) populates it with the real verdict.
    #[serde(default = "Verdict::pass")]
    pub exposure: Verdict,
}

impl Assurance {
    /// `true` iff every check passed.
    pub fn pass(&self) -> bool {
        self.conservation.is_pass()
            && self.no_amplification.is_pass()
            && self.wellformed.is_pass()
            && self.ring_balance.is_pass()
            && self.exposure.is_pass()
    }
    /// All findings across all checks, flattened.
    pub fn all_findings(&self) -> Vec<Finding> {
        let mut v = Vec::new();
        for verdict in [
            &self.conservation,
            &self.no_amplification,
            &self.wellformed,
            &self.ring_balance,
            &self.exposure,
        ] {
            v.extend(verdict.findings().iter().cloned());
        }
        v
    }
}

/// The native value column (computrons) — `Transfer` / `balance_change`
/// move against this single asset.
pub const COMPUTRON_ASSET: &str = "computron";

fn hex32(b: &[u8; 32]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &byte in b {
        s.push(LUT[(byte >> 4) as usize] as char);
        s.push(LUT[(byte & 0x0f) as usize] as char);
    }
    s
}

// ─── walking the forest with loci ──────────────────────────────────────────

/// Visit every node in the forest, calling `f(path, node)` where `path` is
/// the index-path from the forest down to `node` (pre-order DFS — the order the
/// executor applies the actions).
pub(crate) fn walk<'a>(forest: &'a CallForest, mut f: impl FnMut(&[usize], &'a CallTree)) {
    fn rec<'a>(
        path: &mut Vec<usize>,
        node: &'a CallTree,
        f: &mut impl FnMut(&[usize], &'a CallTree),
    ) {
        f(path, node);
        for (i, child) in node.children.iter().enumerate() {
            path.push(i);
            rec(path, child, f);
            path.pop();
        }
    }
    let mut path = Vec::new();
    for (i, root) in forest.roots.iter().enumerate() {
        path.push(i);
        rec(&mut path, root, &mut f);
        path.pop();
    }
}

// ─── B: conservation ───────────────────────────────────────────────────────

/// **Guarantee B (conservation), statically over the forest's moves.**
///
/// Sums every value-moving effect into a per-asset signed ledger and checks
/// each asset column nets to exactly zero:
///
///   * `Transfer { from, to, amount }` → `−amount` at `from`, `+amount` at
///     `to` in the `computron` column. Within a closed forest the two cancel,
///     so any net-nonzero column means value was conjured or destroyed.
///   * `Action::balance_change: Some(delta)` → the Mina-style signed delta on
///     the action's target, in the `computron` column. The `AssuranceCase`
///     conservation law requires the sum of all `balance_change` deltas to be
///     zero across the turn.
///   * `NoteCreate { value, asset_type, .. }` / `NoteSpend { value,
///     asset_type, .. }` → a spend RELEASES `value` of `asset_type` (a credit
///     into the move-pool) and a create LOCKS `value` (a debit). A turn that
///     spends notes worth N and creates notes worth M ≠ N in the same asset
///     does not conserve.
///   * `BridgeMint` carries an external-federation value the userspace view
///     cannot net (its conservation is a cross-federation portable-proof
///     property, NOT a within-forest sum) — flagged in [`boundary`], not
///     summed here.
///
/// On failure the [`Finding`] names the asset column and the net residue.
///
/// NOTE the boundary: this proves the forest's MOVES net to zero — it does
/// NOT prove `from` HELD the value (a balance underflow is an executor /
/// live-state check). A forest that conserves here can still be rejected for
/// insufficient balance. See [`boundary`].
pub fn check_conservation(forest: &CallForest) -> Verdict {
    // asset column -> net signed sum (i128 to avoid u64 overflow on large turns).
    let mut net: BTreeMap<String, i128> = BTreeMap::new();
    walk(forest, |_path, node| {
        for eff in &node.action.effects {
            match eff {
                Effect::Transfer { amount, .. } => {
                    // from −amount, to +amount: nets to zero by construction;
                    // we still record both so an asymmetric construction (a
                    // future variant) would surface.
                    *net.entry(COMPUTRON_ASSET.to_string()).or_default() -= *amount as i128;
                    *net.entry(COMPUTRON_ASSET.to_string()).or_default() += *amount as i128;
                }
                Effect::NoteSpend {
                    value, asset_type, ..
                } => {
                    // spend releases value into the pool: +value.
                    *net.entry(format!("note:{asset_type}")).or_default() += *value as i128;
                }
                Effect::NoteCreate {
                    value, asset_type, ..
                } => {
                    // create locks value out of the pool: −value.
                    *net.entry(format!("note:{asset_type}")).or_default() -= *value as i128;
                }
                _ => {}
            }
        }
        // The signed balance_change delta (Mina-style composable conservation).
        if let Some(delta) = node.action.balance_change {
            *net.entry(COMPUTRON_ASSET.to_string()).or_default() += delta as i128;
        }
    });

    let mut findings = Vec::new();
    for (asset, residue) in net {
        if residue != 0 {
            findings.push(Finding {
                guarantee: "B (conservation)".to_string(),
                locus: Locus::forest().at_asset(asset.clone()),
                message: format!(
                    "asset column `{asset}` does not conserve: net residue = {residue} \
                     (a conserving turn must net to exactly 0 per asset; \
                     {} value was {} across the forest)",
                    residue.unsigned_abs(),
                    if residue > 0 { "conjured" } else { "destroyed" },
                ),
            });
        }
    }
    Verdict::from_findings(findings)
}

// ─── A: non-amplification along delegation edges ────────────────────────────

/// Whether `granted` is a structural attenuation of `parent` — i.e. granting
/// `granted` confers no authority `parent` does not already carry. This is
/// the userspace, artifact-only half of the `AuthModes.captp_granted_le_held`
/// / `EffectsAuthority.introduce_non_amplifying` lattice check.
///
/// `granted ⊑ parent` requires:
///   * same target cell (a grant cannot RE-TARGET to a different cell),
///   * facet mask narrower-or-equal: `granted.allowed_effects ⊆
///     parent.allowed_effects` (where `None` = unrestricted = top, so
///     `Some(_) ⊆ None` but `None ⊄ Some(_)`),
///   * expiry no-later: `granted.expires_at ≤ parent.expires_at` (a `None`
///     parent expiry = no bound = top, so any child expiry is ≤ it; a `Some`
///     parent expiry cannot be widened to `None` or a later height).
pub fn cap_attenuates(granted: &CapabilityRef, parent: &CapabilityRef) -> bool {
    if granted.target != parent.target {
        return false;
    }
    // facet mask: child bits must be a subset of parent bits.
    let facet_ok = match (granted.allowed_effects, parent.allowed_effects) {
        (_, None) => true,        // parent unrestricted = top; any child ⊆ top
        (None, Some(_)) => false, // child unrestricted but parent restricted = amplify
        // EffectMask = u32 bitmask: child ⊆ parent iff (child & parent) == child.
        (Some(g), Some(p)) => (g & p) == g,
    };
    if !facet_ok {
        return false;
    }
    // expiry: child must not outlive parent.
    match (granted.expires_at, parent.expires_at) {
        (_, None) => true,        // parent never-expires = top
        (None, Some(_)) => false, // child never-expires but parent does = amplify
        (Some(g), Some(p)) => g <= p,
    }
}

/// **Guarantee A (non-amplification), statically over the forest's
/// delegation edges.**
///
/// Walks every parent→child edge. When a child node grants a capability
/// (`Effect::GrantCapability { from, cap, .. }` where `from` is a cell the
/// PARENT granted authority over within this same forest), the granted `cap`
/// must [`cap_attenuates`] some cap the parent granted into that scope. A
/// child that grants a WIDER capability than the chain handed it is
/// structurally amplifying — the executor's non-amplification gate rejects it.
///
/// THE BOUNDARY (the load-bearing honesty): this can only check
/// amplification *relative to grants made WITHIN the same forest*. The signer
/// may legitimately hold caps from PRIOR turns (the live c-list) that this
/// artifact does not contain; a grant with no in-forest parent grant is
/// therefore NOT flagged as amplifying (it is `Unknown` — the *holding* check
/// is dynamic, [`boundary`]). What we DO flag: a grant that demonstrably
/// exceeds a cap delegated to it earlier in the SAME forest — a provable
/// in-artifact amplification.
pub fn check_no_amplification(forest: &CallForest) -> Verdict {
    let mut findings = Vec::new();

    // Recurse carrying the set of caps the chain has granted into each cell
    // scope so far (cell -> caps granted to it by ancestors in this forest).
    fn rec(
        path: &mut Vec<usize>,
        node: &CallTree,
        granted_to: &BTreeMap<dregg_types::CellId, Vec<CapabilityRef>>,
        findings: &mut Vec<Finding>,
    ) {
        // Caps this node grants, indexed by recipient, to pass to children.
        let mut child_granted = granted_to.clone();

        for (ei, eff) in node.action.effects.iter().enumerate() {
            if let Effect::GrantCapability { from, to, cap } = eff {
                // Does the granting cell `from` itself hold an in-forest cap
                // covering `cap`'s target? If so, the grant must attenuate it.
                if let Some(parent_caps) = granted_to.get(from) {
                    let covers_target = parent_caps.iter().any(|p| p.target == cap.target);
                    if covers_target {
                        let attenuates = parent_caps.iter().any(|p| cap_attenuates(cap, p));
                        if !attenuates {
                            findings.push(Finding {
                                guarantee: "A (non-amplification)".to_string(),
                                locus: Locus::node(path.clone()).at_effect(ei),
                                message: format!(
                                    "grant from cell {} amplifies: the granted cap \
                                     (target slot {}, facet {:?}, expiry {:?}) is NOT an \
                                     attenuation of any cap this cell was delegated earlier \
                                     in the forest for the same target — it confers wider \
                                     authority than the chain handed it",
                                    short_cell(from),
                                    cap.slot,
                                    cap.allowed_effects,
                                    cap.expires_at,
                                ),
                            });
                        }
                    }
                    // covers_target == false: the grant is over a DIFFERENT
                    // target than anything delegated in-forest → holding is a
                    // dynamic (live c-list) question; not flagged. boundary.
                }
                // Record the grant so descendants under `to` inherit it.
                child_granted.entry(*to).or_default().push(cap.clone());
            }
        }

        for (i, child) in node.children.iter().enumerate() {
            path.push(i);
            rec(path, child, &child_granted, findings);
            path.pop();
        }
    }

    let mut path = Vec::new();
    let empty = BTreeMap::new();
    for (i, root) in forest.roots.iter().enumerate() {
        path.push(i);
        rec(&mut path, root, &empty, &mut findings);
        path.pop();
    }
    Verdict::from_findings(findings)
}

fn short_cell(c: &dregg_types::CellId) -> String {
    let h = hex32(&c.0);
    h[..8].to_string()
}

// ─── structural well-formedness ─────────────────────────────────────────────

/// **Structural well-formedness.** Catches the constructions the executor
/// rejects on shape alone, before any semantic gate:
///
///   * an `Authorization::Unchecked` outside genesis (the grep-able
///     auth-bypass sentinel — the SDK's `raw` module is the only legitimate
///     producer, and only for genesis),
///   * an `Authorization::OneOf` carrying an `Unchecked` candidate (the
///     `OneOf::Unchecked`-is-rejected rule),
///   * a node with zero effects (`sign()` refuses an empty turn; a forest
///     node with no effects is a malformed splice),
///   * an `ExerciseViaCapability` with empty `inner_effects` (a no-op
///     exercise — almost always a construction bug).
pub fn check_wellformed(forest: &CallForest) -> Verdict {
    let mut findings = Vec::new();
    walk(forest, |path, node| {
        // empty action
        if node.action.effects.is_empty() {
            findings.push(Finding {
                guarantee: "well-formedness".to_string(),
                locus: Locus::node(path.to_vec()),
                message: "node carries zero effects (an empty action — the SDK's \
                          sign() refuses these; a forest splice should not produce one)"
                    .to_string(),
            });
        }
        // Unchecked authorization
        match &node.action.authorization {
            Authorization::Unchecked => {
                findings.push(Finding {
                    guarantee: "well-formedness".to_string(),
                    locus: Locus::node(path.to_vec()),
                    message: "node carries Authorization::Unchecked outside genesis \
                              (the auth-bypass sentinel; only the sealed `raw` genesis \
                              path may emit it — the executor rejects it elsewhere)"
                        .to_string(),
                });
            }
            Authorization::OneOf { candidates, .. } => {
                if candidates
                    .iter()
                    .any(|c| matches!(c, Authorization::Unchecked))
                {
                    findings.push(Finding {
                        guarantee: "well-formedness".to_string(),
                        locus: Locus::node(path.to_vec()),
                        message: "Authorization::OneOf carries an Unchecked candidate \
                                  (auth-bypass-by-naming-Unchecked; the executor rejects \
                                  any OneOf whose candidate is Unchecked)"
                            .to_string(),
                    });
                }
            }
            _ => {}
        }
        // no-op exercise
        for (ei, eff) in node.action.effects.iter().enumerate() {
            if let Effect::ExerciseViaCapability { inner_effects, .. } = eff
                && inner_effects.is_empty()
            {
                findings.push(Finding {
                    guarantee: "well-formedness".to_string(),
                    locus: Locus::node(path.to_vec()).at_effect(ei),
                    message: "ExerciseViaCapability with empty inner_effects \
                                  (a no-op exercise — pays gas, changes nothing)"
                        .to_string(),
                });
            }
        }
    });
    Verdict::from_findings(findings)
}

// ─── ring balance (intent specialization of B) ──────────────────────────────

/// One leg of a settlement ring, in the userspace view: a move of `amount`
/// of `asset` from `from` to `to`. This mirrors `intent::solver::Settlement`
/// projected onto the artifact, without depending on the intent crate's
/// discovery types.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RingLeg {
    pub from: dregg_types::CellId,
    pub to: dregg_types::CellId,
    /// The 32-byte asset id (hex). Use `"computron"` for native value.
    pub asset: String,
    pub amount: u64,
}

/// **Ring balance — the intent-ring specialization of guarantee B.**
///
/// A settlement ring (the `intent::Intent::RingSettlement` lowering, or any
/// closed cyclic-trade forest) must (1) be a *closed cycle* — every cell that
/// receives also sends (no participant is a pure source or pure sink) — and
/// (2) *conserve per asset* — each asset's legs net to zero. This is the
/// userspace twin of the Lean `RingBalanced` (`settleRing_conserves`),
/// checkable on the legs BEFORE the ring is lowered and submitted.
///
/// Pass the legs you extracted from the ring (or use [`extract_ring_legs`] to
/// pull them from a forest of bare `Transfer`s).
pub fn check_ring_balance(legs: &[RingLeg]) -> Verdict {
    let mut findings = Vec::new();

    // (1) per-asset conservation
    let mut net: BTreeMap<String, i128> = BTreeMap::new();
    for leg in legs {
        *net.entry(leg.asset.clone()).or_default() += leg.amount as i128; // received by `to`
        *net.entry(leg.asset.clone()).or_default() -= leg.amount as i128; // sent by `from`
    }
    // The above always nets to zero per asset by construction (each leg is a
    // balanced move), so per-asset conservation of a pure-transfer ring is
    // automatic; the substantive ring check is per-CELL net + cycle closure.

    // (2) per-cell, per-asset net: in a balanced ring EVERY participant nets
    // to zero in EVERY asset (what they give equals what they get). A
    // participant with a nonzero net in some asset is an un-closed leg.
    let mut cell_net: BTreeMap<(dregg_types::CellId, String), i128> = BTreeMap::new();
    let mut participants: BTreeMap<dregg_types::CellId, ()> = BTreeMap::new();
    for leg in legs {
        *cell_net.entry((leg.from, leg.asset.clone())).or_default() -= leg.amount as i128;
        *cell_net.entry((leg.to, leg.asset.clone())).or_default() += leg.amount as i128;
        participants.insert(leg.from, ());
        participants.insert(leg.to, ());
    }
    for ((cell, asset), residue) in &cell_net {
        if *residue != 0 {
            findings.push(Finding {
                guarantee: "ring".to_string(),
                locus: Locus::forest().at_asset(asset.clone()),
                message: format!(
                    "ring is not balanced for participant {}: net {residue} in asset `{asset}` \
                     (a closed settlement ring nets every participant to zero per asset — \
                     this cell {} more than it {})",
                    short_cell(cell),
                    if *residue > 0 { "receives" } else { "gives" },
                    if *residue > 0 { "gives" } else { "receives" },
                ),
            });
        }
    }

    // (3) cycle closure: a ring of < 2 participants is degenerate; a self-loop
    // (from == to) is rejected by the solver (`SolverError::SelfLoop`).
    if !legs.is_empty() {
        if participants.len() < 2 {
            findings.push(Finding {
                guarantee: "ring".to_string(),
                locus: Locus::forest(),
                message: format!(
                    "ring has {} participant(s); a settlement ring needs at least 2 \
                     (SolverError::TooSmall)",
                    participants.len()
                ),
            });
        }
        for leg in legs {
            if leg.from == leg.to {
                findings.push(Finding {
                    guarantee: "ring".to_string(),
                    locus: Locus::forest(),
                    message: format!(
                        "ring contains a self-loop on {} (SolverError::SelfLoop)",
                        short_cell(&leg.from)
                    ),
                });
            }
        }
    }

    Verdict::from_findings(findings)
}

/// Pull settlement legs from a forest of bare `Transfer` effects (the shape
/// `intent::lowering::lower_settlement_leg` emits — each ring leg is a bare
/// `Effect::Transfer`). Non-transfer effects are ignored. Use the result with
/// [`check_ring_balance`].
pub fn extract_ring_legs(forest: &CallForest) -> Vec<RingLeg> {
    let mut legs = Vec::new();
    walk(forest, |_path, node| {
        for eff in &node.action.effects {
            if let Effect::Transfer { from, to, amount } = eff {
                legs.push(RingLeg {
                    from: *from,
                    to: *to,
                    asset: COMPUTRON_ASSET.to_string(),
                    amount: *amount,
                });
            }
        }
    });
    legs
}

// ─── the combined entry ─────────────────────────────────────────────────────

/// Run every static check over a constructed forest and return the combined
/// [`Assurance`]. This is the SDK-facing `analyze()` entry: build a turn,
/// call this, and refuse-or-warn before paying to submit.
///
/// Pass `treat_as_ring = true` to additionally run [`check_ring_balance`] over
/// the legs [`extract_ring_legs`] pulls from the forest (for
/// `Intent::RingSettlement` artifacts). For an ordinary turn, ring balance is
/// `Pass` (vacuously — no ring legs to imbalance) unless you opt in.
///
/// The [`Assurance::exposure`] ceiling is likewise `Pass` here — it needs a
/// reserve schema this entry does not take; run [`app::check_exposure_bound`]
/// (or the FFI `exposure` sub-request) to populate it.
pub fn analyze(forest: &CallForest, treat_as_ring: bool) -> Assurance {
    // One FUSED pre-order pass produces the conservation, no-amplification, and
    // well-formedness verdicts together — each with its own accumulator, so the
    // verdicts are byte-identical to running the three checks independently. The
    // ring check works off extracted legs (a separate, opt-in projection).
    let fused = fused_walk(forest);
    let ring_balance = if treat_as_ring {
        check_ring_balance(&extract_ring_legs(forest))
    } else {
        Verdict::Pass
    };
    Assurance {
        conservation: fused.conservation,
        no_amplification: fused.no_amplification,
        wellformed: fused.wellformed,
        ring_balance,
        // The exposure ceiling needs a reserve schema `analyze` does not carry
        // (which slot on which cell holds `R`); it is `Pass` here (vacuously —
        // no reserve to exceed) and populated by the FFI `exposure` sub-request
        // or a direct `app::check_exposure_bound` call. Mirrors `ring_balance`.
        exposure: Verdict::Pass,
    }
}

/// The three forest-walk verdicts produced together by [`fused_walk`].
struct FusedVerdicts {
    conservation: Verdict,
    no_amplification: Verdict,
    wellformed: Verdict,
}

/// A persistent (immutable, structurally-shared) map of the caps granted into
/// each cell scope by ancestors of the current node. Threading this by `&`
/// avoids the per-node `BTreeMap::clone` of the whole inherited map: a child
/// that grants nothing reuses the parent's map by reference; a child that
/// grants caps layers a small overlay node in front, so only the grants
/// themselves (not the inherited bulk) are copied.
enum GrantedScope<'a> {
    Root,
    /// `parent` plus the caps `additions` grants into each recipient cell.
    Layer {
        parent: &'a GrantedScope<'a>,
        additions: BTreeMap<dregg_types::CellId, Vec<CapabilityRef>>,
    },
}

impl<'a> GrantedScope<'a> {
    /// All caps any ancestor (or this layer) granted into `cell`, walking the
    /// layer chain. Order matches the flattened `granted_to` the cloning
    /// version built (parent grants are visited before this layer's), so any
    /// `.iter().any(..)` predicate over them yields the identical result.
    fn caps_for(&self, cell: &dregg_types::CellId) -> Vec<&CapabilityRef> {
        let mut out = Vec::new();
        self.collect_into(cell, &mut out);
        out
    }

    fn collect_into<'s>(&'s self, cell: &dregg_types::CellId, out: &mut Vec<&'s CapabilityRef>) {
        match self {
            GrantedScope::Root => {}
            GrantedScope::Layer { parent, additions } => {
                parent.collect_into(cell, out);
                if let Some(caps) = additions.get(cell) {
                    out.extend(caps.iter());
                }
            }
        }
    }
}

fn fused_walk(forest: &CallForest) -> FusedVerdicts {
    // B (conservation): per-asset signed ledger.
    let mut net: BTreeMap<String, i128> = BTreeMap::new();
    // A (non-amplification) and well-formedness: located findings.
    let mut amp_findings: Vec<Finding> = Vec::new();
    let mut wf_findings: Vec<Finding> = Vec::new();

    fn rec(
        path: &mut Vec<usize>,
        node: &CallTree,
        scope: &GrantedScope<'_>,
        net: &mut BTreeMap<String, i128>,
        amp_findings: &mut Vec<Finding>,
        wf_findings: &mut Vec<Finding>,
    ) {
        // ── conservation (mirrors check_conservation's per-node body) ──
        for eff in &node.action.effects {
            match eff {
                Effect::Transfer { amount, .. } => {
                    *net.entry(COMPUTRON_ASSET.to_string()).or_default() -= *amount as i128;
                    *net.entry(COMPUTRON_ASSET.to_string()).or_default() += *amount as i128;
                }
                Effect::NoteSpend {
                    value, asset_type, ..
                } => {
                    *net.entry(format!("note:{asset_type}")).or_default() += *value as i128;
                }
                Effect::NoteCreate {
                    value, asset_type, ..
                } => {
                    *net.entry(format!("note:{asset_type}")).or_default() -= *value as i128;
                }
                _ => {}
            }
        }
        if let Some(delta) = node.action.balance_change {
            *net.entry(COMPUTRON_ASSET.to_string()).or_default() += delta as i128;
        }

        // ── well-formedness (mirrors check_wellformed's per-node body) ──
        if node.action.effects.is_empty() {
            wf_findings.push(Finding {
                guarantee: "well-formedness".to_string(),
                locus: Locus::node(path.clone()),
                message: "node carries zero effects (an empty action — the SDK's \
                          sign() refuses these; a forest splice should not produce one)"
                    .to_string(),
            });
        }
        match &node.action.authorization {
            Authorization::Unchecked => {
                wf_findings.push(Finding {
                    guarantee: "well-formedness".to_string(),
                    locus: Locus::node(path.clone()),
                    message: "node carries Authorization::Unchecked outside genesis \
                              (the auth-bypass sentinel; only the sealed `raw` genesis \
                              path may emit it — the executor rejects it elsewhere)"
                        .to_string(),
                });
            }
            Authorization::OneOf { candidates, .. } => {
                if candidates
                    .iter()
                    .any(|c| matches!(c, Authorization::Unchecked))
                {
                    wf_findings.push(Finding {
                        guarantee: "well-formedness".to_string(),
                        locus: Locus::node(path.clone()),
                        message: "Authorization::OneOf carries an Unchecked candidate \
                                  (auth-bypass-by-naming-Unchecked; the executor rejects \
                                  any OneOf whose candidate is Unchecked)"
                            .to_string(),
                    });
                }
            }
            _ => {}
        }

        // ── non-amplification + no-op-exercise well-formedness, in one pass over
        //    effects (mirrors the two effect loops, same order) ──
        let mut additions: BTreeMap<dregg_types::CellId, Vec<CapabilityRef>> = BTreeMap::new();
        for (ei, eff) in node.action.effects.iter().enumerate() {
            match eff {
                Effect::GrantCapability { from, to, cap } => {
                    let parent_caps = scope.caps_for(from);
                    if !parent_caps.is_empty() {
                        let covers_target = parent_caps.iter().any(|p| p.target == cap.target);
                        if covers_target {
                            let attenuates = parent_caps.iter().any(|p| cap_attenuates(cap, p));
                            if !attenuates {
                                amp_findings.push(Finding {
                                    guarantee: "A (non-amplification)".to_string(),
                                    locus: Locus::node(path.clone()).at_effect(ei),
                                    message: format!(
                                        "grant from cell {} amplifies: the granted cap \
                                         (target slot {}, facet {:?}, expiry {:?}) is NOT an \
                                         attenuation of any cap this cell was delegated earlier \
                                         in the forest for the same target — it confers wider \
                                         authority than the chain handed it",
                                        short_cell(from),
                                        cap.slot,
                                        cap.allowed_effects,
                                        cap.expires_at,
                                    ),
                                });
                            }
                        }
                    }
                    additions.entry(*to).or_default().push(cap.clone());
                }
                Effect::ExerciseViaCapability { inner_effects, .. } => {
                    if inner_effects.is_empty() {
                        wf_findings.push(Finding {
                            guarantee: "well-formedness".to_string(),
                            locus: Locus::node(path.clone()).at_effect(ei),
                            message: "ExerciseViaCapability with empty inner_effects \
                                      (a no-op exercise — pays gas, changes nothing)"
                                .to_string(),
                        });
                    }
                }
                _ => {}
            }
        }

        // Recurse. If this node granted nothing, children inherit the parent
        // scope by reference (no clone); otherwise layer the additions in front.
        if additions.is_empty() {
            for (i, child) in node.children.iter().enumerate() {
                path.push(i);
                rec(path, child, scope, net, amp_findings, wf_findings);
                path.pop();
            }
        } else {
            let child_scope = GrantedScope::Layer {
                parent: scope,
                additions,
            };
            for (i, child) in node.children.iter().enumerate() {
                path.push(i);
                rec(path, child, &child_scope, net, amp_findings, wf_findings);
                path.pop();
            }
        }
    }

    let mut path = Vec::new();
    let root_scope = GrantedScope::Root;
    for (i, root) in forest.roots.iter().enumerate() {
        path.push(i);
        rec(
            &mut path,
            root,
            &root_scope,
            &mut net,
            &mut amp_findings,
            &mut wf_findings,
        );
        path.pop();
    }

    // conservation findings (mirrors check_conservation's post-walk loop — the
    // BTreeMap iteration order is the same deterministic ascending-key order).
    let mut cons_findings = Vec::new();
    for (asset, residue) in net {
        if residue != 0 {
            cons_findings.push(Finding {
                guarantee: "B (conservation)".to_string(),
                locus: Locus::forest().at_asset(asset.clone()),
                message: format!(
                    "asset column `{asset}` does not conserve: net residue = {residue} \
                     (a conserving turn must net to exactly 0 per asset; \
                     {} value was {} across the forest)",
                    residue.unsigned_abs(),
                    if residue > 0 { "conjured" } else { "destroyed" },
                ),
            });
        }
    }

    FusedVerdicts {
        conservation: Verdict::from_findings(cons_findings),
        no_amplification: Verdict::from_findings(amp_findings),
        wellformed: Verdict::from_findings(wf_findings),
    }
}
