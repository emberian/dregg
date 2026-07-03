//! THE AGENT-ACTIVITY SURFACE — the ADOS keystone (the integrator wedge, visual).
//!
//! An agent is an intricate LOOP — perceive, decide, act, repeat. Most of that
//! loop is unverifiable churn (model calls, planning, tool selection). dregg
//! grounds the ONE seam that matters — **the agent's ACTIONS, at the
//! tool-call/turn boundary** — by making every action a cap-gated, receipted,
//! conservation-checked TURN against the verified executor. This surface renders
//! that grounded seam: an agent cell's *provable activity*, as a Surface cell.
//!
//! `docs/DREGG-DESKTOP-OS.md` §1 casts the whole desktop as the firmament made
//! visual: a window is a `Capability{ Surface(cell) }`. The agent-activity panel
//! is one such surface — a cap-confined VIEW of an agent cell — showing:
//!
//!   * **THE HELD MANDATE** — the agent's attenuated capability: which cells it
//!     can reach and at what rights (`AuthRequired`), the effect-facet mask that
//!     confines it to a subset of the interface, and any expiry. This is the
//!     "adoption IS attenuation" story made legible: an agent is exactly as
//!     powerful as the mandate it holds — nothing ambient.
//!   * **THE CAP-GATED ACTIONS (turns) + their RECEIPTS** — the agent's recent
//!     committed turns, read from the embedded [`World`](crate::world)'s receipt
//!     log + the [`WorldEvent`](crate::dynamics::WorldEvent) dynamics stream
//!     (filtered to this agent). Each carries the executor's verdict: the
//!     receipt hash (the provenance chain), the action count, the computrons
//!     metered, and the human-meaningful effects it produced — a refused action
//!     is shown as REFUSED (the ocap/verification guarantee firing, never faked).
//!   * **WHAT IT IS AUTHORIZED TO DO** — the projection of the held mandate into
//!     a legible authorization view: the verbs the agent's caps + permissions
//!     permit, and (crucially) the verbs they DON'T — the boundary of the loop's
//!     reach, so an operator can see at a glance what a swarm member can and
//!     cannot touch.
//!
//! The point: the swarm's provable activity, rendered in a cap-gated surface.
//! When you watch an agent here you are not watching its self-report — you are
//! watching the executor's receipts for the turns it actually committed, bound
//! by the mandate it actually holds. The pale-ghost question (§5) applied to
//! agents: *can the operator be fooled about what an agent did, or may do?* No —
//! the activity is the on-ledger truth, and the mandate is the real cap-graph.
//!
//! This module is gpui-FREE and `cargo test`-able (the activity model is built
//! purely from the `World`). The cockpit maps [`AgentActivity`] onto a gpui
//! panel and binds the agent cell to a compositor [`Surface`](crate::surface)
//! via [`AgentSurface`].

use dregg_cell::{AuthRequired, CellId};

use crate::dynamics::WorldEvent;
use crate::world::World;

/// One held capability of an agent — a single edge of its mandate. The agent
/// may reach `target` at `rights`, optionally confined to a facet of the
/// interface (`facet_mask`) and/or bounded by an `expires_at` height. This is
/// the attenuated authority the agent loop runs under (adoption = attenuation).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MandateEdge {
    /// The cell this capability reaches (what the agent may act upon).
    pub target: CellId,
    /// The slot in the agent's c-list (its local handle to this authority).
    pub slot: u32,
    /// The rights the agent holds over `target` (the `AuthRequired` lattice).
    pub rights: AuthRequired,
    /// Whether the capability is confined to a subset of effect types (a facet).
    /// `true` = a faceted (effect-restricted) cap; `false` = unrestricted.
    pub faceted: bool,
    /// An optional expiry height (the cap is invalid beyond it), if any.
    pub expires_at: Option<u64>,
}

impl MandateEdge {
    /// A short operator-legible label for the rights ("open"/"sig"/"proof"/...).
    pub fn rights_label(&self) -> &'static str {
        rights_label(&self.rights)
    }
}

/// One recent action the agent took — a committed (or refused) cap-gated turn,
/// as the executor recorded it. The grounded seam of the agent loop: a single
/// step the agent actually performed, with its receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentAction {
    /// The local chain height of this turn (the agent's step index on-ledger),
    /// or `None` for a refused action (it never advanced the chain).
    pub height: Option<u64>,
    /// Whether the executor COMMITTED the action. A refused action is shown as
    /// such — the ocap/verification guarantee firing (never faked away).
    pub committed: bool,
    /// The receipt hash (the provenance-chain link), if committed.
    pub receipt_hash: Option<[u8; 32]>,
    /// How many actions the turn carried (a forest may bundle several).
    pub action_count: usize,
    /// The computrons the executor metered for the turn (its real cost).
    pub computrons: u64,
    /// A human-meaningful summary of WHAT the action did (the effects it
    /// produced, drawn from the dynamics stream), or the refusal reason.
    pub summary: String,
}

/// What an agent is authorized to do — one verb of its reach. The projection of
/// the held mandate into a legible boundary: the verb, whether the mandate
/// PERMITS it, and a short note (e.g. which target, or why it is denied). The
/// "DON'T" entries are as important as the "CAN" — they are the edge of the loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Authorization {
    /// The verb (a short capability the agent's mandate is asked about).
    pub verb: &'static str,
    /// Whether the agent's held mandate + permissions authorize it.
    pub permitted: bool,
    /// A short note (the basis — which target it reaches, or why it cannot).
    pub note: String,
}

/// THE AGENT-ACTIVITY MODEL — an agent cell's provable activity, built purely
/// from the embedded [`World`]. gpui-free: the cockpit renders it; tests assert
/// it. This is the ADOS keystone made data — the swarm's grounded seam.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentActivity {
    /// The agent cell this activity is for.
    pub agent: CellId,
    /// A short operator-legible id for the agent (abbreviated cell id).
    pub short: String,
    /// Whether the agent cell is present + live in the ledger (a missing/dead
    /// agent is shown honestly — its loop is grounded in a real cell or it is not).
    pub backed: bool,
    /// The agent's live balance (the resources its loop holds — pay-for-action).
    pub balance: i64,
    /// The agent's nonce (its total committed-turn count — the loop's step
    /// counter, enforced by the executor's receipt chain).
    pub nonce: u64,
    /// THE HELD MANDATE — the agent's capability edges (its attenuated reach).
    pub mandate: Vec<MandateEdge>,
    /// THE RECENT CAP-GATED ACTIONS — the agent's committed turns + receipts,
    /// most-recent-first (the grounded seam of the loop).
    pub actions: Vec<AgentAction>,
    /// WHAT IT IS AUTHORIZED TO DO — the legible boundary of the mandate.
    pub authorizations: Vec<Authorization>,
}

impl AgentActivity {
    /// Build an agent's activity from the live world: read its mandate (held
    /// caps), its recent actions (its receipts + the effects they produced from
    /// the dynamics stream), and project its authorization boundary. `max_actions`
    /// bounds how many recent turns to surface (most-recent-first).
    pub fn build(world: &World, agent: CellId, max_actions: usize) -> Self {
        let short = crate::reflect::short_hex(agent.as_bytes());
        let backed = world.ledger().contains(&agent);
        let cell = world.ledger().get(&agent);
        let balance = cell.map(|c| c.state.balance()).unwrap_or(0);
        let nonce = cell.map(|c| c.state.nonce()).unwrap_or(0);

        // THE HELD MANDATE: every capability edge in the agent's c-list.
        let mandate: Vec<MandateEdge> = cell
            .map(|c| {
                c.capabilities
                    .iter()
                    .map(|cap| MandateEdge {
                        target: cap.target,
                        slot: cap.slot,
                        rights: cap.permissions.clone(),
                        faceted: cap.allowed_effects.is_some(),
                        expires_at: cap.expires_at,
                    })
                    .collect()
            })
            .unwrap_or_default();

        // THE RECENT ACTIONS: the agent's committed turns (receipts) + the
        // human-meaningful effects each produced (from the dynamics stream),
        // most-recent-first. We pair each receipt with the dynamics that
        // describe its transition by matching the receipt's turn on the stream.
        let actions = build_actions(world, &agent, max_actions);

        // THE AUTHORIZATION BOUNDARY: project the mandate into legible verbs.
        let authorizations = build_authorizations(cell, &mandate);

        AgentActivity {
            agent,
            short,
            backed,
            balance,
            nonce,
            mandate,
            actions,
            authorizations,
        }
    }

    /// The number of committed actions the agent has taken (the loop's grounded
    /// step count on-ledger). Distinct from `actions.len()`, which is capped.
    pub fn committed_action_count(&self) -> usize {
        self.actions.iter().filter(|a| a.committed).count()
    }

    /// The total reach of the mandate (how many distinct cells the agent can
    /// act upon) — the breadth of the loop's authority at a glance.
    pub fn reach(&self) -> usize {
        let mut targets: Vec<&CellId> = self.mandate.iter().map(|m| &m.target).collect();
        targets.sort_unstable_by_key(|c| c.as_bytes());
        targets.dedup();
        targets.len()
    }
}

/// Build the agent's recent actions from the dynamics stream + the receipt log,
/// most-recent-first, capped at `max` — with committed and REFUSED rows
/// INTERLEAVED in true observation order. One ordered walk of the stream is the
/// spine (a refusal that happened between two commits reads between them, not
/// sorted to the top — the loop's real story); receipts the stream never
/// observed (e.g. re-seeded genesis after a reset) are prepended oldest-first so
/// the log stays complete.
fn build_actions(world: &World, agent: &CellId, max: usize) -> Vec<AgentAction> {
    let events = world.dynamics().all();
    let mut seen: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
    let mut actions: Vec<AgentAction> = Vec::new();
    for (idx, ev) in events.iter().enumerate() {
        match ev {
            WorldEvent::TurnCommitted {
                agent: a,
                height,
                receipt_hash,
                action_count,
                computrons,
                ..
            } if a == agent => {
                seen.insert(*receipt_hash);
                actions.push(AgentAction {
                    height: Some(*height),
                    committed: true,
                    receipt_hash: Some(*receipt_hash),
                    action_count: *action_count,
                    computrons: *computrons,
                    summary: summarize_effects_after(events, idx),
                });
            }
            WorldEvent::TurnRejected { agent: a, reason } if a == agent => {
                actions.push(AgentAction {
                    height: None,
                    committed: false,
                    receipt_hash: None,
                    action_count: 0,
                    computrons: 0,
                    summary: format!("REFUSED — {reason}"),
                });
            }
            _ => {}
        }
    }

    // Receipts whose commit predates the stream (a reset re-seed) still deserve
    // rows — oldest, before everything the stream observed.
    let mut full: Vec<AgentAction> = world
        .receipts()
        .iter()
        .filter(|r| &r.agent == agent && !seen.contains(&r.receipt_hash()))
        .map(|r| AgentAction {
            height: None,
            committed: true,
            receipt_hash: Some(r.receipt_hash()),
            action_count: r.action_count,
            computrons: r.computrons_used,
            summary: "committed".to_string(),
        })
        .collect();
    full.extend(actions);

    // Most-recent-first, capped.
    full.reverse();
    full.truncate(max);
    full
}

/// Summarize the effect-events that follow the `TurnCommitted` at `idx`, up to
/// the next `TurnCommitted` — the transition's human-meaningful effects.
fn summarize_effects_after(events: &[WorldEvent], idx: usize) -> String {
    let mut parts: Vec<String> = Vec::new();
    for ev in &events[idx + 1..] {
        if matches!(ev, WorldEvent::TurnCommitted { .. }) {
            break;
        }
        match ev {
            WorldEvent::BalanceFlowed { before, after, .. } => {
                let d = after - before;
                let sign = if d >= 0 { "+" } else { "" };
                parts.push(format!("flow {sign}{d}"));
            }
            WorldEvent::CapabilityGranted { .. } => parts.push("granted cap".to_string()),
            WorldEvent::CapabilityRevoked { .. } => parts.push("revoked cap".to_string()),
            WorldEvent::FieldSet { index, .. } => parts.push(format!("set field[{index}]")),
            WorldEvent::CellBorn { .. } => parts.push("created cell".to_string()),
            WorldEvent::CellSealed { .. } => parts.push("sealed".to_string()),
            WorldEvent::CellUnsealed { .. } => parts.push("unsealed".to_string()),
            WorldEvent::CellDestroyed { .. } => parts.push("destroyed".to_string()),
            WorldEvent::Burned { amount, .. } => parts.push(format!("burned {amount}")),
            _ => {}
        }
    }
    if parts.is_empty() {
        "committed".to_string()
    } else {
        parts.join(" · ")
    }
}

/// Project the agent's mandate into a legible authorization boundary — the verbs
/// it CAN and CANNOT exercise. The "cannot" entries are deliberate: they are the
/// edge of the loop's reach (what a swarm member is confined away from).
fn build_authorizations(
    cell: Option<&dregg_cell::Cell>,
    mandate: &[MandateEdge],
) -> Vec<Authorization> {
    let mut out = Vec::new();

    // "act on a peer cell" — does the agent hold ANY outbound capability?
    let reachable: Vec<&CellId> = mandate.iter().map(|m| &m.target).collect();
    out.push(Authorization {
        verb: "act on a peer cell",
        permitted: !reachable.is_empty(),
        note: if reachable.is_empty() {
            "holds no outbound capability — confined to itself".to_string()
        } else {
            format!("reaches {} cell(s) via its c-list", distinct_reach(mandate))
        },
    });

    // "delegate authority" — does the agent's own `delegate` permission allow
    // it to hand a cap onward? (The executor still enforces no-amplification.)
    let can_delegate = cell
        .map(|c| !matches!(c.permissions.delegate, AuthRequired::Impossible))
        .unwrap_or(false);
    out.push(Authorization {
        verb: "delegate authority",
        permitted: can_delegate && !reachable.is_empty(),
        note: if !can_delegate {
            "delegate permission is Impossible — cannot hand caps onward".to_string()
        } else if reachable.is_empty() {
            "nothing to delegate (holds no caps)".to_string()
        } else {
            "may attenuate + hand a held cap onward (executor enforces ⊆)".to_string()
        },
    });

    // "send value" — can the agent move balance out? (Its `send` permission.)
    let can_send = cell
        .map(|c| !matches!(c.permissions.send, AuthRequired::Impossible))
        .unwrap_or(false);
    out.push(Authorization {
        verb: "send value",
        permitted: can_send,
        note: if can_send {
            "send permission allows outbound transfers (conserving)".to_string()
        } else {
            "send permission is Impossible — cannot move value out".to_string()
        },
    });

    // "modify its own state" — its `set_state` permission.
    let can_set = cell
        .map(|c| !matches!(c.permissions.set_state, AuthRequired::Impossible))
        .unwrap_or(false);
    out.push(Authorization {
        verb: "modify its own state",
        permitted: can_set,
        note: if can_set {
            "set_state permission allows field writes".to_string()
        } else {
            "set_state is Impossible — its state is frozen".to_string()
        },
    });

    // Note any faceted (effect-restricted) caps — the agent is confined to a
    // SUBSET of the target's interface (E-language facets).
    let faceted = mandate.iter().filter(|m| m.faceted).count();
    if faceted > 0 {
        out.push(Authorization {
            verb: "exercise a faceted cap",
            permitted: true,
            note: format!("{faceted} cap(s) confined to an effect-facet (subset of interface)"),
        });
    }

    out
}

/// The mandate's distinct-target reach (small helper for the authorization
/// note; `AgentActivity::reach` is the public method over the same logic).
fn distinct_reach(mandate: &[MandateEdge]) -> usize {
    let mut targets: Vec<&CellId> = mandate.iter().map(|m| &m.target).collect();
    targets.sort_unstable_by_key(|c| c.as_bytes());
    targets.dedup();
    targets.len()
}

/// A short operator-legible label for an `AuthRequired` rights value.
fn rights_label(r: &AuthRequired) -> &'static str {
    match r {
        AuthRequired::None => "open",
        AuthRequired::Signature => "sig",
        AuthRequired::Proof => "proof",
        AuthRequired::Either => "sig|proof",
        AuthRequired::Impossible => "locked",
        AuthRequired::Custom { .. } => "custom",
    }
}

/// THE AGENT SURFACE — binds an agent cell to the compositor as a cap-confined
/// Surface cell (the agent-activity panel IS a surface, §1). It holds the
/// agent's [`SurfaceId`] (its window handle in the shell) and the agent cell it
/// views; the cockpit composites it like any other surface, and the panel body
/// renders the agent's [`AgentActivity`]. Distinct from a plain cell-view: this
/// surface's body is the agent's GROUNDED-SEAM activity, not just raw cell state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AgentSurface {
    /// The shell surface id this agent panel renders into (its window handle).
    pub surface: crate::surface::SurfaceId,
    /// The agent cell this surface views (the loop being grounded).
    pub agent: CellId,
}

impl AgentSurface {
    pub fn new(surface: crate::surface::SurfaceId, agent: CellId) -> Self {
        AgentSurface { surface, agent }
    }

    /// Build this agent surface's live activity from the world (the body the
    /// cockpit renders). A convenience that pairs the binding with its model.
    pub fn activity(&self, world: &World, max_actions: usize) -> AgentActivity {
        AgentActivity::build(world, self.agent, max_actions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{grant_capability, transfer};

    /// A world with an agent cell that holds a mandate (a cap to a peer) and has
    /// committed some real cap-gated turns — its grounded activity to render.
    fn agent_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let peer = w.genesis_cell(0x33, 0);
        // The agent is born holding a capability reaching the peer (its mandate).
        let (agent, _slot) = w.genesis_cell_with_cap(0x22, 10_000, peer);
        // The agent commits real cap-gated turns: a transfer to the peer + a
        // grant (re-granting its peer cap to a fresh slot — legitimate).
        let t1 = w.turn(agent, vec![transfer(agent, peer, 1_000)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(agent, vec![grant_capability(agent, agent, peer, 5)]);
        assert!(w.commit_turn(t2).is_committed());
        (w, agent, peer)
    }

    #[test]
    fn activity_reads_the_held_mandate() {
        // THE HELD MANDATE: the agent's cap edges are read from its live c-list.
        let (w, agent, peer) = agent_world();
        let act = AgentActivity::build(&w, agent, 16);
        assert!(act.backed, "the agent cell is live");
        assert!(!act.mandate.is_empty(), "the agent holds a mandate");
        // It reaches the peer (its outbound authority).
        assert!(
            act.mandate.iter().any(|m| m.target == peer),
            "the mandate reaches the peer cell"
        );
        assert!(act.reach() >= 1, "the mandate has non-trivial reach");
    }

    #[test]
    fn activity_lists_the_cap_gated_actions_with_receipts() {
        // THE GROUNDED SEAM: the agent's committed turns appear as actions, each
        // with a real receipt + a human-meaningful summary of what it did.
        let (w, agent, _peer) = agent_world();
        let act = AgentActivity::build(&w, agent, 16);
        assert_eq!(
            act.committed_action_count(),
            2,
            "two committed cap-gated turns"
        );
        // Every committed action carries a receipt hash (the provenance chain).
        for a in act.actions.iter().filter(|a| a.committed) {
            assert!(a.receipt_hash.is_some(), "a committed action has a receipt");
            assert!(a.height.is_some(), "and a chain height");
        }
        // Most-recent-first: the grant (height 2) is first, the transfer second.
        let committed: Vec<&AgentAction> = act.actions.iter().filter(|a| a.committed).collect();
        assert!(committed[0].height.unwrap() > committed[1].height.unwrap());
        // The transfer's summary mentions the flow it produced.
        assert!(
            act.actions.iter().any(|a| a.summary.contains("flow")),
            "the transfer action summarizes its balance flow, got {:?}",
            act.actions.iter().map(|a| &a.summary).collect::<Vec<_>>()
        );
        // The grant's summary mentions the cap it granted.
        assert!(
            act.actions
                .iter()
                .any(|a| a.summary.contains("granted cap")),
            "the grant action summarizes the cap it granted"
        );
    }

    #[test]
    fn activity_projects_the_authorization_boundary() {
        // WHAT IT IS AUTHORIZED TO DO: the mandate projects into legible verbs,
        // including what it CAN (act on a peer, since it holds a cap) and the
        // boundary.
        let (w, agent, _peer) = agent_world();
        let act = AgentActivity::build(&w, agent, 16);
        assert!(
            !act.authorizations.is_empty(),
            "the authorization boundary is projected"
        );
        // It CAN act on a peer (it holds an outbound cap).
        let act_peer = act
            .authorizations
            .iter()
            .find(|a| a.verb == "act on a peer cell")
            .unwrap();
        assert!(
            act_peer.permitted,
            "the agent can act on a peer (holds a cap)"
        );
        // The open-permissions demo agent can send value + modify state.
        assert!(act
            .authorizations
            .iter()
            .any(|a| a.verb == "send value" && a.permitted));
    }

    #[test]
    fn a_confined_agent_shows_its_boundary() {
        // An agent that holds NO outbound capability is confined to itself — the
        // authorization boundary says so (the "cannot" edge of the loop).
        let mut w = World::new();
        let lonely = w.genesis_cell(0x44, 100); // no cap granted
        let act = AgentActivity::build(&w, lonely, 16);
        assert!(act.mandate.is_empty(), "a lonely agent holds no mandate");
        assert_eq!(act.reach(), 0, "it reaches no peer");
        let act_peer = act
            .authorizations
            .iter()
            .find(|a| a.verb == "act on a peer cell")
            .unwrap();
        assert!(
            !act_peer.permitted,
            "it is NOT authorized to act on a peer (confined)"
        );
        assert!(
            act_peer.note.contains("confined"),
            "the boundary is shown honestly"
        );
    }

    #[test]
    fn a_refused_action_is_shown_as_refused_never_faked() {
        // The ocap/verification guarantee firing: an over-grant the agent
        // ATTEMPTS is REFUSED by the real executor and shown as such (not hidden,
        // not faked as committed) — the loop's grounded truth includes its
        // refusals.
        let mut w = World::new();
        let agent = w.genesis_cell(0x55, 100); // holds NO cap to `target`
        let target = w.genesis_cell(0x66, 0);
        // The agent attempts to grant a cap it does NOT hold → rejected.
        let bad = w.turn(agent, vec![grant_capability(agent, agent, target, 0)]);
        assert!(
            !w.commit_turn(bad).is_committed(),
            "over-grant must be refused"
        );
        let act = AgentActivity::build(&w, agent, 16);
        // The refused action appears, flagged committed=false.
        assert!(
            act.actions
                .iter()
                .any(|a| !a.committed && a.summary.contains("REFUSED")),
            "the refused over-grant is surfaced as REFUSED, got {:?}",
            act.actions
                .iter()
                .map(|a| (a.committed, &a.summary))
                .collect::<Vec<_>>()
        );
        assert_eq!(act.committed_action_count(), 0, "no action committed");
    }

    #[test]
    fn refusals_interleave_with_commits_in_true_order() {
        // The loop's REAL story: commit → refusal → commit must read in exactly
        // that order (most-recent-first), never with the refusal sorted to the
        // top. The regression this pins: build_actions once appended ALL
        // refusals after the committed batch and reversed, so every REFUSED row
        // surfaced newest regardless of when the gate actually fired.
        let mut w = World::new();
        let agent = w.genesis_cell(0x55, 100);
        let target = w.genesis_cell(0x66, 0);

        // 1. a committed nonce bump.
        let t1 = w.turn(
            agent,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: agent }],
        );
        assert!(w.commit_turn(t1).is_committed());
        // 2. a REFUSED over-grant (no cap held).
        let bad = w.turn(agent, vec![grant_capability(agent, agent, target, 0)]);
        assert!(!w.commit_turn(bad).is_committed());
        // 3. another committed nonce bump.
        let t3 = w.turn(
            agent,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: agent }],
        );
        assert!(w.commit_turn(t3).is_committed());

        let act = AgentActivity::build(&w, agent, 16);
        let shape: Vec<bool> = act.actions.iter().map(|a| a.committed).collect();
        // Most-recent-first: committed(3), REFUSED(2), committed(1), then any
        // genesis-era rows (all committed).
        assert!(
            shape.len() >= 3 && shape[0] && !shape[1] && shape[2],
            "commit/refusal/commit must interleave in true order, got {shape:?}"
        );
    }

    #[test]
    fn a_missing_agent_is_shown_unbacked() {
        // An agent cell not in the ledger is shown honestly (a loop grounded in
        // nothing) — it can't masquerade as a live, active agent.
        let w = World::new();
        let ghost = CellId::from_bytes([0x77; 32]);
        let act = AgentActivity::build(&w, ghost, 16);
        assert!(!act.backed, "a missing agent is unbacked");
        assert!(act.mandate.is_empty());
        assert!(act.actions.is_empty());
    }

    #[test]
    fn agent_surface_binds_a_cell_to_a_surface_and_builds_its_activity() {
        // THE SURFACE BINDING: an AgentSurface pairs a surface id with the agent
        // cell, and builds the activity the cockpit renders in that surface.
        let (w, agent, _peer) = agent_world();
        let surf = AgentSurface::new(crate::surface::SurfaceId(7), agent);
        assert_eq!(surf.agent, agent);
        let act = surf.activity(&w, 8);
        assert_eq!(act.agent, agent);
        assert!(
            act.committed_action_count() >= 1,
            "the bound surface renders real activity"
        );
    }
}
