//! THE PROVENANCE NAVIGATOR — the blame / who-did-what face over a cell and its
//! receipt-chain (hyperdreggmedia authoring surface #8,
//! `docs/deos/HYPERDREGGMEDIA-NOTES.md` §6).
//!
//! This is the cell-shaped analog of source line-blame: where
//! `deos-js/src/program_doc.rs`'s `ProgramSource::blame` attributes each source
//! LINE to its authoring patch + author, this attributes each TURN that shaped a
//! cell to its author + the effects it applied — and makes the receipt-chain
//! WALKABLE: click a receipt → the turn's contents + its author → "go to that
//! point" (a time-travel cursor that reconstructs the past state the receipt
//! committed).
//!
//! It REUSES the real models, never a parallel one (exactly the
//! [`crate::reflect::Inspectable`] / [`crate::time_travel`] discipline — a
//! gpui-free projection the view paints, `cargo test`-able without a window):
//!
//!   * the LINEAGE reads [`World::recorded_turns`] — the live world's own
//!     canonical [`crate::replay::History`] — and the SAME
//!     [`crate::world::touched_cells`] the commit path uses to decide which cells
//!     a turn touched. A turn is in a cell's lineage iff it touched the cell. The
//!     author is the turn's `agent` (= the receipt's `agent`); the receipt hash +
//!     height are the real ones from the recorded receipt.
//!   * the TURN DETAIL reads the recorded [`dregg_turn::turn::Turn`] +
//!     [`dregg_turn::turn::TurnReceipt`] directly — the turn's real call-forest
//!     (the effects it applied) and the receipt's real attestation surface.
//!   * the GOTO is the SAME root-verified replay [`crate::time_travel`] drives:
//!     [`History::replay_to`](crate::replay::History::replay_to) to the step the
//!     receipt committed, with the honest [`Liveness`] badge ([`Liveness::Live`]
//!     at the head, [`Liveness::ReplayedDeterministic`] in the past).
//!
//! Nothing here mutates the world: building a lineage / detail / cursor is PURE.

use dregg_cell::{CellId, Ledger};
use dregg_turn::action::Effect;
use dregg_turn::turn::Turn;

use crate::replay::{History, RecordedStep};
use crate::ui_snapshot::Liveness;
use crate::world::{touched_cells, World};

// ===========================================================================
// The LINEAGE — the ordered turns that shaped a cell.
// ===========================================================================

/// One turn in a cell's lineage — a committed turn that TOUCHED the cell, with
/// its author + the effect-kinds it applied + the receipt it left.
///
/// This is the cell-blame row: "at height `height` (receipt `receipt_hash`),
/// `author` applied `effects` — and these touched this cell." The `step` is the
/// [`History`] index AFTER this turn committed (so [`goto`] can replay to it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LineageEntry {
    /// The author of this turn — the cell whose receipt-chain it rode (the turn's
    /// `agent`, equal to the receipt's `agent`). The "who-did-it".
    pub author: CellId,
    /// The receipt hash — the navigable provenance node ([`turn_detail`] /
    /// [`goto`] both key on this). The local blocklace edge.
    pub receipt_hash: [u8; 32],
    /// The chain HEIGHT of this turn — its ordinal among the committed turns
    /// (1-based: the first committed turn is height 1). This is the local chain
    /// index, NOT the [`History`] step (which also counts genesis installs).
    pub height: u64,
    /// The [`History`] step index AFTER this turn committed — the landing point
    /// [`goto`] replays to (`history.replay_to(step)` reconstructs the post-state
    /// this receipt committed). In `1..=history.len()`.
    pub step: usize,
    /// The effect-kinds this turn applied (e.g. `["Transfer", "SetField"]`), in
    /// call-forest order — the "what-they-did". A human-meaningful summary of the
    /// turn's call-forest, not the full effect payloads (that is [`turn_detail`]).
    pub effects: Vec<String>,
    /// `true` iff the cell whose lineage this is was DIRECTLY mutated by this turn
    /// (vs merely a counterparty — e.g. the `to` of a transfer is touched, but the
    /// authoring cell `from` is the actor). Both are in the lineage (both were
    /// touched), but this distinguishes the actor leg from the receiving leg.
    pub authored_by_cell: bool,
}

/// The ordered lineage of `cell`: every committed turn that TOUCHED it, in commit
/// order (oldest → newest). Empty iff no committed turn ever touched the cell
/// (it only exists by genesis, or does not exist at all). PURE — never mutates.
///
/// "Touched" is the SAME predicate the commit path uses
/// ([`crate::world::touched_cells`]): a cell is touched by a turn iff one of the
/// turn's effects names it (as a transfer `from`/`to`, a `SetField`/grant/burn
/// target, …). This is exactly the set whose post-state the receipt commits to,
/// so the lineage is the cell's real causal history, not an approximation.
pub fn lineage(world: &World, cell: &CellId) -> Vec<LineageEntry> {
    let history = world.recorded_turns();
    let mut out = Vec::new();
    // The chain height counts committed turns only (genesis installs are not
    // turns); the History step counts every recorded step (genesis + turn).
    let mut height: u64 = 0;
    for (i, step) in history.steps().iter().enumerate() {
        if let RecordedStep::Committed { turn, receipt, .. } = step {
            height += 1;
            let touched = touched_cells(turn);
            if touched.iter().any(|c| c == cell) {
                out.push(LineageEntry {
                    author: receipt.agent,
                    receipt_hash: receipt.receipt_hash(),
                    height,
                    // `replay_to(step)` reconstructs the post-state of step `i`;
                    // the post-state of the i-th recorded step is `replay_to(i+1)`.
                    step: i + 1,
                    effects: effect_kinds(turn),
                    authored_by_cell: &turn.agent == cell,
                });
            }
        }
    }
    out
}

// ===========================================================================
// The TURN DETAIL — a receipt's turn, contents + author.
// ===========================================================================

/// One effect a turn applied, as a human-meaningful line (the kind + the cells it
/// names + a value summary). The detail rows under a clicked receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectDetail {
    /// The effect kind (`"Transfer"`, `"SetField"`, …).
    pub kind: String,
    /// The cells this effect names (a transfer's `from`/`to`, a field-set's
    /// `cell`, …), in payload order — the ocap/value edges the effect touched.
    pub cells: Vec<CellId>,
    /// A short human summary of the effect's payload (`"500 computrons"`,
    /// `"slot 3"`, …); empty for a payload-less effect.
    pub summary: String,
}

/// The full detail of a clicked receipt's turn — the author, the effects, and the
/// receipt's attestation surface. The "click a receipt → turn details + author"
/// face. PURE.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnDetail {
    /// The author — the turn's `agent` (= the receipt's `agent`).
    pub author: CellId,
    /// The receipt hash (the provenance node this detail is keyed on).
    pub receipt_hash: [u8; 32],
    /// The prior receipt in the author's chain, if any — the blocklace back-edge
    /// (walk the chain). `None` iff this is the author's first turn.
    pub previous_receipt: Option<[u8; 32]>,
    /// The chain HEIGHT of this turn (its ordinal among committed turns, 1-based).
    pub height: u64,
    /// The [`History`] step AFTER this turn committed (the [`goto`] landing).
    pub step: usize,
    /// The turn's wall-clock timestamp (folded into the receipt hash).
    pub timestamp: i64,
    /// The metered cost the executor charged this turn.
    pub computrons_used: u64,
    /// The number of effects across the turn's call-forest (the receipt's
    /// `action_count` is the action count; this is the effect count).
    pub effect_count: usize,
    /// Each effect the turn applied, in call-forest order — the real contents.
    pub effects: Vec<EffectDetail>,
}

/// The detail of the turn that left `receipt_hash`, or `None` if no recorded
/// committed turn carries that receipt. PURE — reads the recorded turn + receipt.
pub fn turn_detail(world: &World, receipt_hash: &[u8; 32]) -> Option<TurnDetail> {
    let history = world.recorded_turns();
    let mut height: u64 = 0;
    for (i, step) in history.steps().iter().enumerate() {
        if let RecordedStep::Committed { turn, receipt, .. } = step {
            height += 1;
            if &receipt.receipt_hash() == receipt_hash {
                return Some(TurnDetail {
                    author: receipt.agent,
                    receipt_hash: receipt.receipt_hash(),
                    previous_receipt: receipt.previous_receipt_hash,
                    height,
                    step: i + 1,
                    timestamp: receipt.timestamp,
                    computrons_used: receipt.computrons_used,
                    effect_count: turn_effects(turn).count(),
                    effects: turn_effects(turn).map(effect_detail).collect(),
                });
            }
        }
    }
    None
}

// ===========================================================================
// The GOTO — a time-travel cursor request keyed on a receipt.
// ===========================================================================

/// The reconstructed past at a receipt — the result of "go to that point". The
/// state the receipt committed, ROOT-VERIFIED against the recorded tooth, plus the
/// honest [`Liveness`] badge. This is the [`crate::time_travel`] landing keyed on
/// a receipt rather than a raw scrubber step.
#[derive(Clone, Debug)]
pub struct GotoCursor {
    /// The receipt this cursor lands at.
    pub receipt_hash: [u8; 32],
    /// The [`History`] step the cursor sits at (the post-state of the receipt's
    /// turn — `history.replay_to(step)` reconstructed it).
    pub step: usize,
    /// The canonical [`dregg_cell::Ledger::root`] recorded at this landing (the
    /// root tooth the reconstruction was verified against).
    pub root: [u8; 32],
    /// `true` iff the reconstruction root-VERIFIED against the recorded tooth (the
    /// anti-substitution tooth — `false` is a surfaced bug, never a panic, and
    /// `cells` is then empty).
    pub verified: bool,
    /// The honest liveness of this landing: [`Liveness::Live`] iff the receipt is
    /// the head turn (the live present), else [`Liveness::ReplayedDeterministic`]
    /// (a re-derived past — the camera re-ran from the witnessed log).
    pub liveness: Liveness,
    /// The reconstructed cells at this landing (id, balance, cap-count), sorted by
    /// id. Empty iff the replay failed (`verified == false`).
    pub cells: Vec<(CellId, i64, usize)>,
}

impl GotoCursor {
    /// The reconstructed balance of `cell` at this landing, if it existed then.
    pub fn balance_of(&self, cell: &CellId) -> Option<i64> {
        self.cells
            .iter()
            .find(|(id, ..)| id == cell)
            .map(|(_, bal, _)| *bal)
    }
}

/// **GO TO THAT POINT** — reconstruct the past state the receipt `receipt_hash`
/// committed, by root-verified replay (the time-travel cursor). `None` iff no
/// recorded committed turn carries that receipt. PURE — never mutates the world.
///
/// This is exactly [`crate::time_travel::TimeCockpitModel::build`]'s cursor
/// reconstruction, but keyed on a RECEIPT (the provenance node the navigator
/// clicked) rather than a raw scrubber step: it finds the step the receipt
/// committed, replays to it (root-verifying against the recorded tooth), and
/// badges the landing Live-at-head / ReplayedDeterministic-in-past.
pub fn goto(world: &World, receipt_hash: &[u8; 32]) -> Option<GotoCursor> {
    let history = world.recorded_turns();
    let step = step_of_receipt(history, receipt_hash)?;
    Some(reconstruct(history, step, *receipt_hash))
}

/// The [`History`] step AFTER the turn carrying `receipt_hash` committed, or
/// `None` if no recorded committed turn carries it.
fn step_of_receipt(history: &History, receipt_hash: &[u8; 32]) -> Option<usize> {
    history
        .steps()
        .iter()
        .enumerate()
        .find_map(|(i, step)| match step {
            RecordedStep::Committed { receipt, .. } if &receipt.receipt_hash() == receipt_hash => {
                Some(i + 1)
            }
            _ => None,
        })
}

/// Build the [`GotoCursor`] for a known `step` (root-verified replay + the
/// liveness badge). Shared by [`goto`] and the tests.
fn reconstruct(history: &History, step: usize, receipt_hash: [u8; 32]) -> GotoCursor {
    let head = history.len();
    let liveness = if step == head {
        Liveness::Live
    } else {
        Liveness::ReplayedDeterministic
    };
    let (cells, verified) = match history.replay_to(step) {
        Ok(ledger) => (sorted_cells(&ledger), true),
        Err(_) => (Vec::new(), false),
    };
    GotoCursor {
        receipt_hash,
        step,
        root: history.root_at(step),
        verified,
        liveness,
        cells,
    }
}

// ===========================================================================
// helpers
// ===========================================================================

/// Every effect in a turn's call-forest (roots + one level of children), in
/// order — the SAME traversal `World::commit_turn` derives its dynamics from.
fn turn_effects(turn: &Turn) -> impl Iterator<Item = &Effect> {
    turn.call_forest.roots.iter().flat_map(|tree| {
        tree.action
            .effects
            .iter()
            .chain(tree.children.iter().flat_map(|c| c.action.effects.iter()))
    })
}

/// The effect-kinds a turn applied (in call-forest order) — a short summary row.
/// `pub` because the Provenance Walker's effects column reuses this exact
/// vocabulary (one summary, wherever a turn is named in a row).
pub fn effect_kinds(turn: &Turn) -> Vec<String> {
    turn_effects(turn).map(effect_kind).collect()
}

/// The bare kind name of an effect (`"Transfer"`, `"SetField"`, …).
fn effect_kind(e: &Effect) -> String {
    match e {
        Effect::SetField { .. } => "SetField",
        Effect::Transfer { .. } => "Transfer",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::EmitEvent { .. } => "EmitEvent",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        Effect::CreateCell { .. } => "CreateCell",
        Effect::SetPermissions { .. } => "SetPermissions",
        Effect::SetVerificationKey { .. } => "SetVerificationKey",
        Effect::Burn { .. } => "Burn",
        _ => "Effect",
    }
    .to_string()
}

/// A full per-effect detail row (kind + the cells it names + a payload summary).
fn effect_detail(e: &Effect) -> EffectDetail {
    let (cells, summary): (Vec<CellId>, String) = match e {
        Effect::Transfer { from, to, amount } => (vec![*from, *to], format!("{amount} computrons")),
        Effect::SetField { cell, index, .. } => (vec![*cell], format!("slot {index}")),
        Effect::GrantCapability { from, to, .. } => (vec![*from, *to], String::new()),
        Effect::RevokeCapability { cell, slot } => (vec![*cell], format!("slot {slot}")),
        Effect::EmitEvent { cell, .. } => (vec![*cell], String::new()),
        Effect::IncrementNonce { cell } => (vec![*cell], String::new()),
        Effect::SetPermissions { cell, .. } => (vec![*cell], String::new()),
        Effect::SetVerificationKey { cell, .. } => (vec![*cell], String::new()),
        Effect::Burn { target, amount, .. } => (vec![*target], format!("{amount} computrons")),
        Effect::CreateCell { balance, .. } => (Vec::new(), format!("{balance} computrons")),
        _ => (Vec::new(), String::new()),
    };
    EffectDetail {
        kind: effect_kind(e),
        cells,
        summary,
    }
}

/// The cells of a ledger as `(id, balance, cap-count)`, sorted by id.
fn sorted_cells(ledger: &Ledger) -> Vec<(CellId, i64, usize)> {
    let mut cells: Vec<(CellId, i64, usize)> = ledger
        .iter()
        .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
        .collect();
    cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    cells
}

// ===========================================================================
// TESTS — gpui-free, exactly as time_travel.rs / reflect.rs / replay.rs are.
// `cargo test --features embedded-executor`
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{burn, set_field, transfer, World};

    /// A world with TWO authors: a treasury (1_000) and a user (0). The treasury
    /// transfers to the user twice, then the USER spends back — so the user cell
    /// is shaped by turns from BOTH authors (the receiving leg AND its own actor
    /// leg). Returns the world + (treasury, user).
    fn two_author_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let user = w.genesis_cell(0x22, 0);
        // h1: treasury → user 100   (author = treasury; touches treasury + user)
        let t1 = w.turn(treasury, vec![transfer(treasury, user, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        // h2: treasury → user 200   (author = treasury)
        let t2 = w.turn(treasury, vec![transfer(treasury, user, 200)]);
        assert!(w.commit_turn(t2).is_committed());
        // h3: user → treasury 50    (author = USER; touches user + treasury)
        let t3 = w.turn(user, vec![transfer(user, treasury, 50)]);
        assert!(w.commit_turn(t3).is_committed());
        (w, treasury, user)
    }

    #[test]
    fn lineage_lists_the_shaping_turns_in_order_with_authors_and_receipts() {
        let (w, treasury, user) = two_author_world();

        // The USER's lineage: all three turns touched the user (received twice,
        // spent once) — in commit order, with the REAL authors + receipt hashes.
        let lin = lineage(&w, &user);
        assert_eq!(lin.len(), 3, "all three turns touched the user");

        // Authors are correct: treasury, treasury, USER.
        assert_eq!(lin[0].author, treasury);
        assert_eq!(lin[1].author, treasury);
        assert_eq!(
            lin[2].author, user,
            "the third turn the user authored itself"
        );

        // Heights are the chain ordinals (1-based, genesis NOT counted).
        assert_eq!(lin[0].height, 1);
        assert_eq!(lin[1].height, 2);
        assert_eq!(lin[2].height, 3);

        // The receipt hashes are the REAL ones from the world's receipt log, in
        // order (the local blocklace).
        let log: Vec<[u8; 32]> = w.receipts().iter().map(|r| r.receipt_hash()).collect();
        assert_eq!(lin[0].receipt_hash, log[0]);
        assert_eq!(lin[1].receipt_hash, log[1]);
        assert_eq!(lin[2].receipt_hash, log[2]);

        // The actor leg is flagged: only the third turn was AUTHORED BY the user.
        assert!(!lin[0].authored_by_cell);
        assert!(!lin[1].authored_by_cell);
        assert!(lin[2].authored_by_cell);

        // Each entry names the effect-kind it applied.
        assert_eq!(lin[0].effects, vec!["Transfer".to_string()]);

        // The TREASURY's lineage is also all three (it is from/to in each).
        assert_eq!(lineage(&w, &treasury).len(), 3);
    }

    #[test]
    fn lineage_excludes_turns_that_did_not_touch_the_cell() {
        let mut w = World::new();
        let a = w.genesis_cell(0x11, 1_000);
        let b = w.genesis_cell(0x22, 0);
        let c = w.genesis_cell(0x33, 0); // never touched by any turn
        let t = w.turn(a, vec![transfer(a, b, 10)]);
        assert!(w.commit_turn(t).is_committed());

        assert_eq!(lineage(&w, &a).len(), 1, "a is the from-leg");
        assert_eq!(lineage(&w, &b).len(), 1, "b is the to-leg");
        assert!(
            lineage(&w, &c).is_empty(),
            "c was never touched → empty lineage"
        );
    }

    #[test]
    fn turn_detail_returns_the_real_contents_and_author() {
        let (w, treasury, user) = two_author_world();
        let lin = lineage(&w, &user);

        // Detail the FIRST turn (treasury → user 100).
        let d = turn_detail(&w, &lin[0].receipt_hash).expect("receipt is recorded");
        assert_eq!(
            d.author, treasury,
            "the first turn's author is the treasury"
        );
        assert_eq!(d.height, 1);
        assert_eq!(d.effect_count, 1);
        assert_eq!(d.effects[0].kind, "Transfer");
        // The real payload: from=treasury, to=user, 100 computrons.
        assert_eq!(d.effects[0].cells, vec![treasury, user]);
        assert!(d.effects[0].summary.contains("100"));
        // The first turn has no prior receipt in the treasury's chain.
        assert!(d.previous_receipt.is_none());

        // Detail the THIRD turn (user → treasury 50): its prior receipt is the
        // USER's previous turn — but the user authored ONLY this one, so the
        // chain back-edge for the user is None.
        let d3 = turn_detail(&w, &lin[2].receipt_hash).expect("receipt is recorded");
        assert_eq!(d3.author, user);
        assert!(
            d3.previous_receipt.is_none(),
            "the user's first (only) turn has no prior receipt in its chain"
        );

        // An unknown receipt yields None.
        assert!(turn_detail(&w, &[0xAB; 32]).is_none());
    }

    #[test]
    fn goto_reconstructs_the_earlier_state_root_verified() {
        let (w, treasury, user) = two_author_world();
        let lin = lineage(&w, &user);

        // Go to the FIRST turn's receipt: the past where treasury sent 100.
        // At that point: treasury = 1000 − 100 = 900, user = 100.
        let g1 = goto(&w, &lin[0].receipt_hash).expect("receipt is recorded");
        assert!(g1.verified, "the past reconstruction root-verifies");
        assert_eq!(
            g1.liveness,
            Liveness::ReplayedDeterministic,
            "an earlier receipt is a re-derived past, not the live head"
        );
        assert_eq!(g1.balance_of(&treasury), Some(900));
        assert_eq!(g1.balance_of(&user), Some(100));
        assert_eq!(g1.root, w.recorded_turns().root_at(g1.step));

        // Go to the SECOND turn's receipt: treasury = 1000 − 100 − 200 = 700,
        // user = 300.
        let g2 = goto(&w, &lin[1].receipt_hash).expect("receipt is recorded");
        assert!(g2.verified);
        assert_eq!(g2.balance_of(&treasury), Some(700));
        assert_eq!(g2.balance_of(&user), Some(300));

        // Go to the THIRD (head) turn's receipt: this IS the live present.
        // treasury = 700 + 50 = 750, user = 300 − 50 = 250.
        let g3 = goto(&w, &lin[2].receipt_hash).expect("receipt is recorded");
        assert_eq!(g3.liveness, Liveness::Live, "the head receipt is LIVE");
        assert_eq!(g3.balance_of(&treasury), Some(750));
        assert_eq!(g3.balance_of(&user), Some(250));
        // The head goto reconstructs the live ledger's root.
        assert_eq!(g3.step, w.recorded_turns().len());

        // An unknown receipt yields None (nothing to go to).
        assert!(goto(&w, &[0xAB; 32]).is_none());
    }

    #[test]
    fn goto_lands_at_distinct_roots_per_step() {
        // Each receipt's goto lands at the post-state THAT receipt committed — so
        // the roots advance with the chain (the receipt-chain, walkable).
        let mut w = World::new();
        let a = w.genesis_cell(0x11, 1_000);
        let b = w.genesis_cell(0x22, 0);
        for amt in [10u64, 20, 30] {
            let t = w.turn(a, vec![transfer(a, b, amt)]);
            assert!(w.commit_turn(t).is_committed());
        }
        let roots: Vec<[u8; 32]> = w
            .receipts()
            .iter()
            .map(|r| goto(&w, &r.receipt_hash()).unwrap().root)
            .collect();
        assert_eq!(roots.len(), 3);
        assert_ne!(roots[0], roots[1], "each turn advances the root");
        assert_ne!(roots[1], roots[2]);
    }

    #[test]
    fn lineage_distinguishes_effect_kinds() {
        // A turn that sets a field AND a turn that burns — the effect-kinds are
        // surfaced distinctly (the what-they-did face).
        let mut w = World::new();
        let a = w.genesis_cell(0x11, 1_000);
        let t1 = w.turn(a, vec![set_field(a, 0, [7u8; 32])]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(a, vec![burn(a, 5)]);
        assert!(w.commit_turn(t2).is_committed());

        let lin = lineage(&w, &a);
        assert_eq!(lin.len(), 2);
        assert_eq!(lin[0].effects, vec!["SetField".to_string()]);
        assert_eq!(lin[1].effects, vec!["Burn".to_string()]);

        // The burn's detail names the target + amount.
        let d = turn_detail(&w, &lin[1].receipt_hash).unwrap();
        assert_eq!(d.effects[0].kind, "Burn");
        assert_eq!(d.effects[0].cells, vec![a]);
        assert!(d.effects[0].summary.contains("5"));
    }
}
