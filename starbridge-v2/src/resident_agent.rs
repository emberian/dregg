//! THE HIRELING — a real confined agent (deos-hermes brain + gate) that LIVES in
//! the desktop World.
//!
//! deos ships a whole confined-agent rail: a [`HermesGateway`] routes every ACP
//! tool-call through the proven `ToolGateway` (cap-gated, metered, receipted, or an
//! in-band refusal), driven by a real closed-loop brain
//! ([`deos_hermes::HermesAgentPeer`] over [`deos_hermes::resident::ResidentBrain`]).
//! But that gate commits its turns on a `dregg_sdk::AgentRuntime` — a DIFFERENT
//! executor than the desktop's [`crate::world::World`]. So a Hermes session's
//! receipts never appear in the operator's own image, and the Agent Room (which
//! reads `World::receipts()`) can never see a live inhabitant.
//!
//! THE MIRROR WELD closes that. This module hires a resident onto the LIVE desktop
//! World: it mints the resident a real desktop cell under an attenuated mandate,
//! drives the confined brain loop through the gate, and for every ADMITTED call it
//! rebases the tool's witness ([`deos_hermes::tool_effects::effects_for_call`])
//! onto the resident's DESKTOP cell and commits a real verified turn on the shared
//! `World` (the exact `World::turn` + `commit_turn` shape [`crate::agent_attach`]
//! uses). Now the Actions/Reach tabs fill from `World::receipts()` with turns a
//! REAL agent committed. Gate refusals stay session-side truth — surfaced through
//! [`AgentHandle::refusals`], NEVER fabricated as World turns (world-truth and
//! gate-truth kept visually distinct; see the red-team note in `agent_attach`).
//!
//! ## Two-executor consistency (the medium-risk seam, stated plainly)
//!
//! There are TWO executors here: the gate's `AgentRuntime` (where the cap/rate/
//! budget legs bite and the ACP receipt is minted) and the desktop `World` (where
//! the mirror turn lands). The gate is the FIRST tooth — it refuses out-of-mandate
//! calls in-band, so nothing is mirrored for a refusal. The mirror turn then goes
//! through the World's OWN verified executor (the SECOND tooth: it re-checks
//! authority/conservation on every committed turn), so even a mirror bug cannot
//! forge a turn the live executor would reject. The witness effect is a self-emit
//! on the resident's own open cell — the same [`deos_hermes::tool_effects`] shape
//! the gate already commits successfully on its own executor.
//!
//! ## Where the Agent Room welds (SHIPPED — `deos_desktop::hireling`)
//!
//! The Agent Room window (`deos_desktop/agent_room.rs`, mounted at `mod.rs`) now
//! carries THE HIRELING STRIP (`deos_desktop/hireling.rs`, `dev-surfaces`):
//!   * "HIRE" → [`hire_resident_seeded`] on the live desktop World (a free seed
//!     pair scanned off the LIVE ledger) and the room pinned to `handle.cell`;
//!   * "STEP" → one [`AgentHandle::prompt`] beat (a rotated confined objective),
//!     then `cx.notify()` so `AgentActivity::build` re-reads the mirrored
//!     receipts; new gate refusals arrive as amber toasts;
//!   * [`AgentHandle::refusals`] merge into the Actions face as REFUSED rows (a
//!     REAL gate verdict, never a fabricated `TurnRejected`);
//!   * "FIRE" → a real `RevokeCapability` turn strips the resident's live-World
//!     mandate, then the handle drops (its leaked runtime is app-lived; that
//!     teardown seam stays named, not hidden).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use dregg_cell::CellId;

use deos_hermes::resident::{resident_brain_from_env, ResidentBrain};
use deos_hermes::tool_effects::effects_for_call;
use deos_hermes::{
    AcpClient, AgentCipherclerk, AgentRuntime, GrantRegistry, HeldToken, HermesAgentPeer,
    HermesGateway, PermissionOutcome, StreamEvent,
};

use crate::world::{CommitOutcome, World};

/// The confinement the operator hires a resident under — an ATTENUATED mandate
/// with a small call budget. The defaults deny the most-dangerous mutating tool
/// (`write_file`) so a hired resident always has a legible refusal to point at,
/// and hold `terminal` to a tight rate ceiling.
#[derive(Clone, Debug)]
pub struct ResidentMandate {
    /// The ACP session id the resident runs under (also its human label).
    pub session_id: String,
    /// The balance the resident's desktop cell is born with (its allowance body;
    /// the paid-market / 402-budget leg welds here later — see the TODO below).
    pub allowance: i64,
    /// Deny `write_file` outright (rate 0) — the guaranteed in-band refusal that
    /// makes confinement legible on the first prompt.
    pub deny_write: bool,
    /// The rate ceiling on `terminal` (the most visceral tool). A small integer
    /// is a call budget on the hands.
    pub terminal_rate: i64,
}

impl ResidentMandate {
    /// The canonical attenuated mandate: a modest allowance, `write_file` denied,
    /// `terminal` held to rate 5.
    pub fn attenuated(session_id: &str) -> ResidentMandate {
        ResidentMandate {
            session_id: session_id.to_string(),
            allowance: 10_000,
            deny_write: true,
            terminal_rate: 5,
        }
    }
}

/// One gate refusal the resident hit — SESSION-side truth, surfaced for the room
/// to render (never mirrored as a World turn).
#[derive(Clone, Debug)]
pub struct Refusal {
    /// The tool the resident reached for.
    pub tool: String,
    /// The in-band reason the gate returned (the mandate leg that bit).
    pub reason: String,
}

/// A LIVE confined resident bound to the desktop World: its real cell, the
/// cap-gated gateway it acts through (held across prompts so budgets persist),
/// the receipts its admitted calls mirrored onto the World, and the refusals the
/// gate returned.
///
/// The gateway borrows a `'static` [`AgentRuntime`] (leaked once at hire, exactly
/// like [`deos_hermes::cockpit_surface`]'s app-lived session), so the handle can
/// be held by a desktop window without a self-referential struct.
pub struct AgentHandle {
    /// The resident's cell on the LIVE desktop World (its Actions/Reach subject).
    pub cell: CellId,
    /// The ACP session id / label.
    pub session_id: String,
    /// The cap-gated gateway, taken into the driving client per prompt and
    /// restored after (budgets persist across turns).
    gateway: Option<HermesGateway<'static>>,
    /// The presentation clock the gate stamps each metered turn at.
    clock: i64,
    /// The receipt hashes the resident's admitted calls landed on the LIVE World
    /// (the mirror weld's output — what `World::receipts()` now witnesses).
    pub receipts: Vec<[u8; 32]>,
    /// Every gate refusal the resident hit (surfaced, not fabricated).
    pub refusals: Vec<Refusal>,
    /// **The HERMETIC pin.** When `true`, every beat thinks with the on-box
    /// [`ResidentBrain::OnBox`] REGARDLESS of the environment — a provider key in
    /// the operator's env is deliberately NOT consulted. This is what makes the
    /// Attach Wizard's "hermetic (on-box)" pick a truthful one: choosing it means
    /// no credential leaves the box, even if one is present. `false` (the default,
    /// and what the Agent Room's plain HIRE sets) resolves the brain from the env
    /// per the [`resident_brain_from_env`] precedence (BYO key when present).
    pub force_on_box: bool,
}

/// The outcome of one resident prompt: how many admitted calls mirrored real
/// desktop turns, and how many the gate refused in-band.
#[derive(Clone, Debug, Default)]
pub struct PromptSummary {
    /// Admitted calls that committed a real verified turn on the LIVE World.
    pub mirrored: usize,
    /// Calls the gate refused in-band this prompt.
    pub refused: usize,
    /// The agent's final message (its own summary of the turn).
    pub agent_text: String,
}

/// HIRE A RESIDENT onto the live desktop `world` under `mandate` — the named seam
/// the Agent Room drives.
///
/// Mints the resident a real desktop cell (a genesis cell holding an attenuated
/// capability reaching a fresh peer, funded with the mandate's allowance — the
/// same `genesis_cell_with_cap` shape the agent tests stand up), then opens a
/// cap-gated [`HermesGateway`] confined by `mandate`. The returned [`AgentHandle`]
/// is driven with [`AgentHandle::prompt`]; the room later welds Hire/Fire buttons
/// to this call (see the module doc).
pub fn hire_resident(world: &Rc<RefCell<World>>, mandate: ResidentMandate) -> AgentHandle {
    hire_resident_seeded(world, mandate, 0x5A, 0x5B)
}

/// [`hire_resident`] with CALLER-CHOSEN genesis seeds for the peer + resident
/// cells. The fixed `0x5A`/`0x5B` pair derives FIXED cell ids, and the World's
/// genesis path refuses a second insert at an occupied id — so a hire→fire→hire
/// cycle (the Agent Room's) must scan the LIVE ledger for a free pair and hand
/// it here (see `deos_desktop::hireling::free_seed_pair`). Same confinement,
/// same mirror weld — only the birth address moves.
pub fn hire_resident_seeded(
    world: &Rc<RefCell<World>>,
    mandate: ResidentMandate,
    peer_seed: u8,
    agent_seed: u8,
) -> AgentHandle {
    // Mint the resident's DESKTOP cell (genesis path — no executor turn): a peer
    // it can reach (non-trivial authority) + the resident cell holding that cap,
    // funded with its allowance.
    let cell = {
        let mut w = world.borrow_mut();
        let peer = w.genesis_cell(peer_seed, 0);
        let (agent, _slot) = w.genesis_cell_with_cap(agent_seed, mandate.allowance, peer);
        agent
    };

    // The gate-side grantor: a root token on a leaked, app-lived runtime (the
    // canonical owned-`'static` trick for a long-lived `!Send` resource a window
    // holds without self-reference). This runtime is a DIFFERENT executor than the
    // desktop World — the mirror weld reconciles the two (see the module doc).
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[0x5C; 32], "deos");
    let runtime: &'static AgentRuntime = Box::leak(Box::new(AgentRuntime::new(
        Arc::new(RwLock::new(cclerk)),
        "deos",
    )));

    // The ATTENUATED confinement: standard floors, `write_file` denied (a legible
    // refusal), `terminal` held to its rate ceiling.
    // TODO(weld): a PAID gateway (`HermesGateway::new_paid` + `ToolMarket` with a
    // session budget) turns the allowance into a real 402-budget leg — Proposal-3's
    // lane. This free gateway keeps the two-ledger surface small for phase 1.
    let mut registry = GrantRegistry::default_for_session(1_000_000)
        .with_standard_tool_grants(1_000_000)
        .with_tool_grant("terminal", mandate.terminal_rate, 1_000_000);
    if mandate.deny_write {
        registry = registry.with_grant_for_tool_deny("write_file");
    }
    let gateway = HermesGateway::new(runtime, root, registry);

    AgentHandle {
        cell,
        session_id: mandate.session_id,
        gateway: Some(gateway),
        clock: 10,
        receipts: Vec::new(),
        refusals: Vec::new(),
        // Env-resolved by default; the wizard's hermetic pin (set on the returned
        // handle) is what forces on-box regardless of a present key.
        force_on_box: false,
    }
}

impl AgentHandle {
    /// Drive one prompt through the resident's confined brain loop and MIRROR the
    /// admitted calls onto the live desktop `world`.
    ///
    /// For every `Allow` verdict the gate returned, the tool's witness effect is
    /// rebased onto the resident's desktop cell and committed as a real verified
    /// turn on the SHARED `World` (the receipt lands on the live provenance log +
    /// dynamics feed, exactly like every other desktop turn). Every `Reject` is
    /// recorded in [`AgentHandle::refusals`] — session truth, surfaced, never a
    /// fabricated World turn. Returns a [`PromptSummary`].
    pub fn prompt(&mut self, world: &Rc<RefCell<World>>, prompt: &str) -> PromptSummary {
        // A fresh brain per prompt (on-box by default, BYO-key when present), over
        // the SAME persisted gateway so budgets carry across prompts. The hermetic
        // pin forces on-box even when a provider key sits in the env — the wizard's
        // "no credential leaves the box" pick, honored on every beat.
        let brain = if self.force_on_box {
            ResidentBrain::default()
        } else {
            resident_brain_from_env()
        };
        let peer = HermesAgentPeer::new(&self.session_id, brain);
        let gw = self
            .gateway
            .take()
            .expect("the resident gateway is present between prompts");
        let mut client = AcpClient::new(peer, gw, self.clock);

        let mut verdicts = Vec::new();
        let mut agent_text = String::new();
        let _ = client.run_prompt_streaming("/deos/resident", prompt, None, &mut |ev| match &ev {
            StreamEvent::Verdict { call, outcome } => {
                verdicts.push((call.clone(), outcome.clone()));
            }
            StreamEvent::AgentChunk { text } => agent_text.push_str(text),
            _ => {}
        });
        let gateway = client.into_gateway();
        self.clock += verdicts.len() as i64 + 1;
        self.gateway = Some(gateway);

        // THE MIRROR WELD: admitted → a real desktop turn; refused → surfaced.
        let mut summary = PromptSummary {
            agent_text: agent_text.trim().to_string(),
            ..Default::default()
        };
        for (call, outcome) in &verdicts {
            match outcome {
                PermissionOutcome::Allow { .. } => {
                    // Rebase the gate's tool witness onto the resident's DESKTOP
                    // cell and commit it through the World's own verified executor.
                    let effects = effects_for_call(call, self.cell);
                    let mut w = world.borrow_mut();
                    let turn = w.turn(self.cell, effects);
                    match w.commit_turn(turn) {
                        CommitOutcome::Committed { receipt, .. } => {
                            self.receipts.push(receipt.receipt_hash());
                            summary.mirrored += 1;
                        }
                        // The World's executor is the SECOND tooth — if it rejects
                        // the mirror (it should not, for a self-emit on an owned
                        // open cell), we drop it rather than forge a receipt.
                        CommitOutcome::Rejected { .. } | CommitOutcome::Queued { .. } => {}
                    }
                }
                PermissionOutcome::Reject { reason, .. } => {
                    self.refusals.push(Refusal {
                        tool: call.name.clone(),
                        reason: reason.clone(),
                    });
                    summary.refused += 1;
                }
            }
        }
        summary
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE PHASE-1 ACCEPTANCE (gpui-free, mozjs-free): hire a resident onto a LIVE
    /// desktop World, drive one prompt, and prove (a) its admitted calls mirrored
    /// REAL receipted turns onto the live ledger, and (b) its over-reach was
    /// refused in-band by the attenuated mandate.
    #[test]
    fn bake_attach_resident_and_prompt() {
        let (world, _anchors) = crate::world::demo_world();
        let live = Rc::new(RefCell::new(world));
        let pre_receipts = live.borrow().receipts().len();
        let pre_height = live.borrow().height();

        let mut handle = hire_resident(&live, ResidentMandate::attenuated("resident-bake"));

        // A prompt whose verbs make the on-box brain plan search + read + write +
        // build (so the denied write is reached, and other tools land).
        let summary = handle.prompt(
            &live,
            "search the docs, read the source, write a notes file, then run the build",
        );

        // (a) REAL receipted turns landed on the LIVE World — the mirror weld fed
        // the desktop ledger from a real agent's admitted calls.
        assert!(
            !handle.receipts.is_empty(),
            "the resident mirrored at least one real desktop receipt"
        );
        assert_eq!(
            summary.mirrored,
            handle.receipts.len(),
            "every mirrored call recorded its receipt"
        );
        let post_receipts = live.borrow().receipts().len();
        let post_height = live.borrow().height();
        assert_eq!(
            post_receipts,
            pre_receipts + handle.receipts.len(),
            "the live provenance log grew by exactly the mirrored turns"
        );
        assert_eq!(
            post_height,
            pre_height + handle.receipts.len() as u64,
            "the live World height advanced by exactly the mirrored turns"
        );

        // (b) At least one IN-BAND REFUSAL — the attenuated mandate denied the
        // write, and it is surfaced as gate truth (not a World turn).
        assert!(summary.refused >= 1, "the mandate refused a call in-band");
        assert!(
            handle.refusals.iter().any(|r| r.tool == "write_file"),
            "the denied write_file was the surfaced refusal: {:?}",
            handle.refusals
        );

        // The resident's cell is live on the World the room would render.
        assert!(
            live.borrow().ledger().get(&handle.cell).is_some(),
            "the resident's cell lives on the live desktop image"
        );
    }
}
