//! **THE CARD FEED OF THE PULSE** — attached-World cards ride the same 250ms beat
//! the AppletView-backed panes do.
//!
//! Wave 3 welded THE PULSE into the desktop's content-IR panes
//! ([`super::viewnode_pane::pulse_panes`] / [`super::viewnode_pane::pulse_panes_quiet`]
//! over `Entity<deos_view::AppletView>`), and named the honest gap it left: the OTHER
//! live-card renderer — [`crate::card_pane::CardPane`], the surface every
//! attached-World card (`dock::card_surface`, a launched app's bespoke card) mounts —
//! got no feed at all. A `CardPane` bound to the operator's REAL cell would keep
//! painting a stale value while a foreign resident moved that very cell, because
//! nothing ever told it the World moved.
//!
//! This module is the card half of the weld, mirroring `viewnode_pane`'s pulse pair
//! shape-for-shape over the desktop's open-card registry
//! (`DeosDesktop::card_panes` — every mounted live card, keyed by its substance cell):
//!
//!   - QUIET half (every beat): retire last beat's dirty-glow tint
//!     ([`CardPane::fade_glow`]); catch up turns the card's OWN substance committed
//!     between beats ([`CardPane::catch_up_own_turns`] — an embedded backing's fires
//!     are named in no dynamics stream, so the audit-tape watermark is the tooth).
//!   - LOUD half (a beat where the World moved): broadcast the beat's
//!     `WorldEvent::FieldSet`s into every card's signal registry
//!     ([`CardPane::on_world_events`] — a card bound to a touched `(cell, slot)`
//!     repaints EXACTLY its dirty binds, wearing the one-beat glow; a card bound to
//!     none of the touched sources stays perfectly still), and broadcast the beat's
//!     CELL-WIDE `CellMutated`/`CapabilityRevoked` events through the registry's
//!     conservative `invalidate_cell` tooth ([`CardPane::on_world_cells`]).
//!
//! Both halves are called from [`DeosDesktop::pump_dynamics`] (THE PULSE), right
//! beside the viewnode feed — one beat, two renderers, the same events.
//!
//! Gated on `card-pane` (where `CardPane`/`deos-view`/`deos-js` are in scope), like
//! `viewnode_pane`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use gpui::{App, AppContext, Context, Entity};

use dregg_cell::AuthRequired;
use dregg_types::CellId;

use crate::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
use crate::card_pane::{CardPane, SharedAttached};
use deos_view::{BindFmt, ViewNode};

use super::{id_short, DeosDesktop};

/// **The QUIET half of one pulse beat** over every open live card — runs every beat,
/// even when the World did not move: (a) retire last beat's dirty-glow tint
/// ([`CardPane::fade_glow`] — a glow lasts exactly one beat), (b) catch up turns the
/// card's OWN substance committed between beats ([`CardPane::catch_up_own_turns`] —
/// the audit-tape watermark; free on a still tape). Returns whether ANY card needs a
/// repaint. Mirrors [`super::viewnode_pane::pulse_panes_quiet`] exactly.
pub fn pulse_cards_quiet(cards: &HashMap<CellId, Entity<CardPane>>, cx: &mut App) -> bool {
    let mut any = false;
    for entity in cards.values() {
        let changed = entity.update(cx, |card, cx| {
            let faded = card.fade_glow();
            let caught = !card.catch_up_own_turns().is_empty();
            if faded || caught {
                cx.notify();
            }
            faded || caught
        });
        any |= changed;
    }
    any
}

/// **The LOUD half of one pulse beat** — the World moved past the pulse cursor:
///
///   1. Broadcast the beat's projected `WorldEvent::FieldSet`s (`field_sets`, each a
///      `(cell, slot)` write on the LIVE World) into every card's signal registry via
///      [`CardPane::on_world_events`]. The registry is keyed `(cell, slot)`, so a
///      card whose binds never read a touched source stays perfectly still — and a
///      card over an ATTACHED World cell repaints exactly its dirty binds.
///   2. Broadcast the beat's CELL-WIDE events (`cell_events` — each a
///      `WorldEvent::CellMutated` / `CapabilityRevoked`, naming a cell but no slot)
///      through the registry's conservative `invalidate_cell` tooth
///      ([`CardPane::on_world_cells`]): every binding of a touched cell re-reads
///      (never under-invalidating), a cell no bind reads dirties nothing.
///
/// Returns whether ANY card invalidated (its repaint was `notify`d here). Mirrors
/// [`super::viewnode_pane::pulse_panes`], minus the census weld (the World-Status
/// tracking verbs are a viewnode-panel concern; a card's binds read the live ledger
/// directly, so the broadcast alone is its whole feed).
pub fn pulse_cards(
    cards: &HashMap<CellId, Entity<CardPane>>,
    field_sets: &[(CellId, usize)],
    cell_events: &[CellId],
    cx: &mut App,
) -> bool {
    let mut any = false;
    for entity in cards.values() {
        let changed = entity.update(cx, |card, cx| {
            let mut dirty = 0usize;
            if !field_sets.is_empty() {
                dirty += card.on_world_events(field_sets).len();
            }
            if !cell_events.is_empty() {
                dirty += card.on_world_cells(cell_events).len();
            }
            if dirty > 0 {
                cx.notify();
            }
            dirty > 0
        });
        any |= changed;
    }
    any
}

/// The witnesses of one PROVEN card-pulse beat (the return of
/// [`DeosDesktop::bake_foreign_turn_repaints_card_binds`]): a FOREIGN turn committed
/// on the live World — outside the card, not through its substance — wrote the very
/// slot the card's bind reads, and the card repainted EXACTLY that bind out of the
/// pulse broadcast, with the one-beat dirty glow lit.
pub struct CardPulseWitness {
    /// The bind's live reading before the foreign turn (off the SAME substance the
    /// rendered widgets drive).
    pub count_before: u64,
    /// The bind's live reading after the proof beat — what the cache now paints.
    pub count_after: u64,
    /// The value the card's cache holds for the counter bind after the proof beat —
    /// the broadcast re-read landed (equals `count_after`).
    pub cached_after: Option<u64>,
    /// The proof beat's dirty set (raw `BindingId` indices, driver-friendly).
    pub dirty: Vec<u64>,
    /// The glow set right after the proof beat — the accent tint on the glass.
    pub glowing: Vec<u64>,
    /// Whether the dirty set is EXACTLY the card's counter bind — the fine-grained
    /// bar (one foreign turn lit one row), pre-checked against the card's own bind
    /// plan so the bake driver needs no deos-js types.
    pub dirty_is_exactly_counter_bind: bool,
}

/// The counter card's view-tree, built directly in Rust (no SpiderMonkey — the tree
/// is DATA): a title, a live `bind` on the agent's counter slot, and a `+1` button
/// firing the `bump` affordance. The same card shape `dock::card_surface`'s
/// JS-authored counter card mounts.
pub fn counter_card_tree() -> ViewNode {
    ViewNode::VStack(vec![
        ViewNode::Text("Counter card (live cockpit cell)".into()),
        ViewNode::Bind {
            slot: AGENT_COUNTER_SLOT,
            label: "live count: ".into(),
            fmt: BindFmt::Raw,
        },
        ViewNode::Button {
            label: "+1".into(),
            turn: "bump".into(),
            arg: 1,
        },
    ])
}

impl DeosDesktop {
    /// **Mount the live counter card into the pulse feed** (idempotent) — a
    /// [`CardPane`] over an applet ATTACHED to the desktop's LIVE `World` through
    /// [`WorldSinkAdapter::live`]: the card's substance is the operator's REAL cell,
    /// its `bind` reads that cell's counter slot, its button's fire would commit a
    /// real cap-gated verified turn. Registered in `card_panes`, so THE PULSE
    /// broadcasts every beat's events into its signal registry. Returns whether the
    /// card is mounted after the call.
    pub fn bake_mount_counter_card(&mut self, cx: &mut Context<Self>) -> bool {
        let cell = self.user;
        if self.card_panes.contains_key(&cell) {
            return true;
        }
        let sink = WorldSinkAdapter::live(Rc::clone(&self.world));
        let attached = attach_agent(
            sink,
            cell,
            AuthRequired::Signature,
            vec![("bump".to_string(), AuthRequired::Signature)],
        );
        let shared: SharedAttached = Rc::new(RefCell::new(attached));
        let tree = counter_card_tree();
        let entity = cx.new(|_cx| CardPane::new(shared, tree, "counter card · live World"));
        self.card_panes.insert(cell, entity);
        true
    }

    /// Unmount a card from the pulse feed (a closed card must stop consuming beats).
    pub fn bake_unmount_card(&mut self, cell: &CellId) -> bool {
        self.card_panes.remove(cell).is_some()
    }

    /// How many live cards ride the pulse (a bake assertion).
    pub fn bake_card_pane_count(&self) -> usize {
        self.card_panes.len()
    }

    /// **THE CARD-PULSE WELD, PROVEN** — a FOREIGN turn (committed on the live World:
    /// outside the card, not through its substance) repaints EXACTLY the mounted
    /// counter card's bind, with the one-beat dirty glow lit.
    ///
    /// The loop: (1) mount (or reuse) the live counter card — its bind reads the
    /// operator cell's counter slot off the REAL ledger; (2) SETTLE — drive two pulse
    /// beats so any pending dynamics ride out and last beat's glow fades (the proof
    /// beat's glow must be attributable to the foreign turn alone); (3) THE FOREIGN
    /// TURN — commit a real verified `SetField` on the live World writing the card's
    /// BOUND slot (the turn's `FieldSet` event is the broadcast's whole payload — the
    /// card is told nothing directly); (4) THE PROOF BEAT — one
    /// [`DeosDesktop::pump_dynamics`] beat: the broadcast dirties EXACTLY the counter
    /// bind, the fresh value lands in the card's cache, and the glow is lit. A capture
    /// before/after differs — the repainted value + accent tint reach pixels.
    pub fn bake_foreign_turn_repaints_card_binds(
        &mut self,
        cx: &mut Context<Self>,
    ) -> Result<CardPulseWitness, String> {
        let cell = self.user;

        // (1) The live card on the pulse.
        if !self.bake_mount_counter_card(cx) {
            return Err("the counter card did not mount".into());
        }
        let entity = self
            .card_panes
            .get(&cell)
            .cloned()
            .ok_or("the mounted counter card is not registered on the pulse")?;
        let substance = entity.read(cx).substance();

        // (2) SETTLE — one beat drains pending dynamics (its broadcast may dirty the
        //     card), one more fades the glow (nothing moved in between), so the proof
        //     beat's dirty/glow sets witness the foreign turn ALONE.
        self.pump_dynamics(cx);
        self.pump_dynamics(cx);
        let count_before = substance.borrow().get_u64(AGENT_COUNTER_SLOT);

        // (3) THE FOREIGN TURN — a real verified `SetField` on the live World writing
        //     the card's bound slot, committed outside the card (never through its
        //     substance; the card's own tape stays still).
        let moved = count_before.wrapping_add(667); // a value the seed never holds
        if !self.commit_set_field(cell, AGENT_COUNTER_SLOT, moved) {
            return Err("the foreign SetField turn did not commit".into());
        }

        // (4) THE PROOF BEAT — the FieldSet rides the broadcast into the card.
        self.pump_dynamics(cx);

        let card = entity.read(cx);
        let count_after = substance.borrow().get_u64(AGENT_COUNTER_SLOT);
        let dirty: Vec<u64> = card.last_dirty().iter().map(|b| b.0).collect();
        let glowing: Vec<u64> = card.glowing().iter().map(|b| b.0).collect();
        let expected_bindings = card.bindings_reading(AGENT_COUNTER_SLOT);
        let cached_after = expected_bindings.first().and_then(|b| card.cached(*b));
        let expected: Vec<u64> = expected_bindings.iter().map(|b| b.0).collect();
        let dirty_is_exactly_counter_bind =
            !expected.is_empty() && dirty == expected && glowing == expected;

        self.say(format!(
            "THE CARD-PULSE WELD — a foreign turn moved cell {}'s counter to {moved}; \
             the mounted card repainted exactly its bind off the beat's broadcast \
             (dirty glow lit).",
            id_short(&cell)
        ));

        Ok(CardPulseWitness {
            count_before,
            count_after,
            cached_after,
            dirty,
            glowing,
            dirty_is_exactly_counter_bind,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_counter_card_tree_binds_the_agent_counter_slot() {
        // The mounted card's ONE bind reads the agent's counter slot — the exact
        // source a foreign `SetField { index: AGENT_COUNTER_SLOT }` names, so the
        // broadcast's fine-grained bar ("one foreign turn lit one row") is meaningful.
        let tree = counter_card_tree();
        match &tree {
            ViewNode::VStack(kids) => {
                assert_eq!(kids.len(), 3, "title + bind + button");
                assert!(
                    matches!(&kids[1], ViewNode::Bind { slot, .. } if *slot == AGENT_COUNTER_SLOT),
                    "the bind reads the counter slot the attach weld's bump writes"
                );
                assert!(
                    matches!(&kids[2], ViewNode::Button { turn, .. } if turn == "bump"),
                    "the button fires the attach weld's bump affordance"
                );
            }
            other => panic!("expected a vstack root, got {other:?}"),
        }
    }
}
