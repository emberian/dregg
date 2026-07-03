//! THE PULSE→SIGNALS WELD BAR — the general `on_world_events` entry point (world
//! events naming ANY cell), the one-beat dirty GLOW, and the own-turn catch-up
//! watermark. The sibling of `fine_grained_rerender.rs`: same gpui-free two-bind
//! scene (`AppletView` constructs without a window; only `render` paints), now
//! exercising the cockpit-pump-facing surface:
//!
//!   - `on_world_events` with the applet's OWN cell behaves exactly like
//!     `on_committed_turn` (the sugar relation);
//!   - an event naming a FOREIGN cell dirties NOTHING — the pump can broadcast one
//!     beat's `WorldEvent::FieldSet`s to every open card and only cards actually
//!     bound to the touched `(cell, slot)` repaint (no over-invalidation);
//!   - the dirty GLOW is the per-beat union (two calls in one beat both light),
//!     `fade_glow` retires it exactly once, and `last_dirty` stays the per-call bar;
//!   - `catch_up_own_turns` notices a turn fired directly on the applet (a rendered
//!     button's path — no dynamics stream names its slots), conservatively
//!     invalidates the cell's bindings once, and is FREE on a still audit tape.

use std::cell::RefCell;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::signals::BindingId;
use dregg_cell::AuthRequired;
use dregg_types::CellId;

use deos_view::tree::ViewNode;
use deos_view::AppletView;

/// A two-slot applet: slot 0 = "a" (seed 10), slot 1 = "b" (seed 20). `incA` adds
/// `arg` to slot 0 only. Signature-gated and held (the same fixture shape
/// `fine_grained_rerender.rs` proves the sugar path over).
fn two_slot_applet(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let inc_a = Affordance {
        name: "incA".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        pk,
        [0u8; 32],
        &[(0usize, pack_u64(10)), (1usize, pack_u64(20))],
        vec![inc_a],
        AuthRequired::Signature,
    )
}

/// Two binds — binding 0 reads slot 0, binding 1 reads slot 1.
fn two_bind_tree() -> ViewNode {
    ViewNode::VStack(vec![
        ViewNode::Bind {
            slot: 0,
            label: "a: ".into(),
            fmt: deos_view::BindFmt::Raw,
        },
        ViewNode::Bind {
            slot: 1,
            label: "b: ".into(),
            fmt: deos_view::BindFmt::Raw,
        },
    ])
}

/// A distinct, deterministic FOREIGN cell id (one the applet's binds never read).
fn foreign_cell() -> CellId {
    CellId::from_bytes([0xF0u8; 32])
}

#[test]
fn own_cell_world_event_matches_the_committed_turn_sugar() {
    let shared = Rc::new(RefCell::new(two_slot_applet(0x51)));
    let view = AppletView::new(shared.clone(), two_bind_tree());
    let own = shared.borrow().cell();

    // The general entry point with the applet's own cell = the sugar's dirty set.
    let dirty = view.on_world_events(&[(own, 0)]);
    assert_eq!(
        dirty,
        vec![BindingId(0)],
        "an own-cell world event dirties exactly the slot-0 binding"
    );
    assert_eq!(view.last_dirty(), vec![BindingId(0)]);
    assert_eq!(
        view.cached(BindingId(0)),
        Some(10),
        "the dirty binding re-read its live value into the cache"
    );
}

#[test]
fn a_foreign_cell_event_dirties_nothing() {
    let shared = Rc::new(RefCell::new(two_slot_applet(0x52)));
    let view = AppletView::new(shared.clone(), two_bind_tree());

    // Prime both bindings (what a first paint does lazily).
    view.on_committed_turn(&[0, 1]);
    view.fade_glow();

    // THE BROADCAST GUARANTEE: the pump hands EVERY open card the beat's events; a
    // FieldSet on a cell this card's binds never read must invalidate nothing.
    let dirty = view.on_world_events(&[(foreign_cell(), 0), (foreign_cell(), 1)]);
    assert!(
        dirty.is_empty(),
        "a foreign cell's FieldSet must not over-invalidate this card"
    );
    assert!(
        view.glowing().is_empty(),
        "nothing glows on a foreign event"
    );
    assert_eq!(view.cached(BindingId(0)), Some(10), "cache untouched");
    assert_eq!(view.cached(BindingId(1)), Some(20), "cache untouched");
}

#[test]
fn glow_is_the_per_beat_union_and_fades_once() {
    let shared = Rc::new(RefCell::new(two_slot_applet(0x53)));
    let view = AppletView::new(shared.clone(), two_bind_tree());
    let own = shared.borrow().cell();

    // Two invalidation calls in ONE beat (the pump's field-set feed, then the census
    // drive): the glow is their UNION; `last_dirty` stays the LAST call's set.
    view.on_world_events(&[(own, 0)]);
    view.on_world_events(&[(own, 1)]);
    assert_eq!(
        view.glowing(),
        vec![BindingId(0), BindingId(1)],
        "the glow unions every dirty set since the last fade"
    );
    assert_eq!(
        view.last_dirty(),
        vec![BindingId(1)],
        "last_dirty is the per-call bar (the last call's set)"
    );

    // The host's next beat fades exactly once.
    assert!(
        view.fade_glow(),
        "something was glowing — repaint to un-tint"
    );
    assert!(view.glowing().is_empty(), "the glow retired");
    assert!(!view.fade_glow(), "a second fade on a quiet beat is free");
}

#[test]
fn catch_up_own_turns_notices_a_directly_fired_turn_once() {
    let shared = Rc::new(RefCell::new(two_slot_applet(0x54)));
    let view = AppletView::new(shared.clone(), two_bind_tree());

    // A still audit tape catches up to nothing (the common, free beat).
    assert!(view.catch_up_own_turns().is_empty(), "still tape → clean");

    // A rendered button's path: fire the affordance DIRECTLY on the shared applet —
    // one real cap-gated verified turn, named in no dynamics stream.
    shared
        .borrow_mut()
        .fire("incA", 5)
        .expect("incA commits a verified turn");

    // The catch-up sees the tape moved and (conservatively) invalidates the cell's
    // bindings — both re-read; the fresh slot-0 value lands in the cache.
    let dirty = view.catch_up_own_turns();
    assert_eq!(
        dirty,
        vec![BindingId(0), BindingId(1)],
        "the CellMutated-shaped tooth invalidates every binding of the applet's cell"
    );
    assert_eq!(
        view.cached(BindingId(0)),
        Some(15),
        "slot 0 re-read 10 → 15"
    );
    assert_eq!(
        view.cached(BindingId(1)),
        Some(20),
        "slot 1 re-read (unchanged)"
    );
    assert_eq!(view.glowing(), vec![BindingId(0), BindingId(1)]);

    // The watermark advanced: the NEXT beat is clean again.
    assert!(
        view.catch_up_own_turns().is_empty(),
        "the same turn is never re-invalidated"
    );
}

#[test]
fn cell_wide_events_invalidate_conservatively_and_foreign_cells_stay_still() {
    // THE `CellMutated`/`CapabilityRevoked` FOLD — those events name a cell but no
    // slot, so the pump projects them into `on_world_cells` (the registry's
    // conservative `invalidate_cell` tooth) instead of the `(cell, slot)` broadcast.
    let shared = Rc::new(RefCell::new(two_slot_applet(0x56)));
    let view = AppletView::new(shared.clone(), two_bind_tree());
    let own = shared.borrow().cell();

    // Prime + settle (first-paint fill, then retire the glow).
    view.on_committed_turn(&[0, 1]);
    view.fade_glow();

    // A cell-wide event on a FOREIGN cell dirties nothing (the broadcast guarantee
    // holds for the conservative tooth too).
    assert!(
        view.on_world_cells(&[foreign_cell()]).is_empty(),
        "a foreign CellMutated must not over-invalidate this card"
    );
    assert!(view.glowing().is_empty());

    // Move slot 0 behind the cache's back (a real verified turn), then fold a
    // cell-wide event naming the applet's OWN cell: EVERY binding of the cell
    // re-reads (never under-invalidating) and the fresh value lands in the cache.
    shared
        .borrow_mut()
        .fire("incA", 7)
        .expect("incA commits a verified turn");
    let dirty = view.on_world_cells(&[own]);
    assert_eq!(
        dirty,
        vec![BindingId(0), BindingId(1)],
        "an own-cell CellMutated invalidates every binding of the cell"
    );
    assert_eq!(
        view.cached(BindingId(0)),
        Some(17),
        "slot 0 re-read 10 → 17"
    );
    assert_eq!(
        view.cached(BindingId(1)),
        Some(20),
        "slot 1 re-read (unchanged)"
    );
    assert_eq!(
        view.glowing(),
        vec![BindingId(0), BindingId(1)],
        "the conservative re-read glows like every other feed"
    );
}

#[test]
fn mark_own_turns_seen_suppresses_the_conservative_catch_up() {
    let shared = Rc::new(RefCell::new(two_slot_applet(0x55)));
    let view = AppletView::new(shared.clone(), two_bind_tree());
    let own = shared.borrow().cell();

    // The census-weld path: the host fires the turn itself, folds the EXACT touched
    // slot through on_world_events, then marks the tape seen…
    shared
        .borrow_mut()
        .fire("incA", 3)
        .expect("incA commits a verified turn");
    let dirty = view.on_world_events(&[(own, 0)]);
    assert_eq!(
        dirty,
        vec![BindingId(0)],
        "exact invalidation, not cell-wide"
    );
    view.mark_own_turns_seen();

    // …so the next quiet beat does NOT re-invalidate the whole cell for it.
    assert!(
        view.catch_up_own_turns().is_empty(),
        "an exactly-folded own turn is not double-counted by the watermark"
    );
}
