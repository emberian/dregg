//! **THE VIRTUAL-FACE REGISTRY** — uncapped, tail-following list state for the
//! desktop's dense log faces.
//!
//! [`super::face_scroll`] gave every dense face ONE persistent [`gpui::ScrollHandle`]
//! so its scroll POSITION survives repaints. But the faces themselves still
//! *built* the whole (capped) row set into the element tree every frame — a
//! chronicle hard-stopped at ~24 rows because painting 100k rows would melt the
//! frame. This registry is the other half: it owns the widget kit's
//! [`VirtualListScrollHandle`] per dense face so the face can render through
//! `gpui_component::v_virtual_list` — only the *visible* rows are ever built,
//! and the row count is UNCAPPED. The World's history stops being a peephole.
//!
//! Two truths live here, both keyed by the same [`super::FaceScrollKey`] the
//! flat faces use (so a face that graduates to virtualization keeps its
//! identity):
//!
//!   * **the handle** — the persistent [`VirtualListScrollHandle`]. Its
//!     `base_handle()` is a plain [`gpui::ScrollHandle`] the NT scrollbar
//!     ([`super::chrome::nt_scrollbar`]) reads and drives, so a virtualized face
//!     wears the SAME always-visible chrome the flat faces do — the kit tracks
//!     the visible window, the NT bar tracks the whole (virtual) content.
//!   * **the tail cursor** — the item count the face last rendered. When the log
//!     GROWS (a pulse landed a receipt), [`follow_tail`] defers a scroll to the
//!     new last row: `tail -f` for the World. It fires ONLY on a count change,
//!     so an operator who scrolls up to read history is left in place until the
//!     next receipt actually arrives (then snapped to the fresh tail).
//!
//! The registry is pure, window-free bookkeeping (a `VirtualListScrollHandle` is
//! a couple of `Rc`-counted words whose deferred scroll + offset can be set
//! headlessly), and the visible-range math is a pure function
//! ([`visible_row_range`]) mirroring the kit's own vertical scan — so the "offset
//! N shows rows [a, b)" claim is asserted in [`tests`], not narrated, and the
//! bakes can witness a 10k-row face without a live window.
//!
//! [`follow_tail`]: VirtualFaceRegistry::follow_tail
//! [`VirtualListScrollHandle`]: gpui_component::VirtualListScrollHandle

use std::collections::HashMap;
use std::ops::Range;

use gpui::ScrollStrategy;
use gpui_component::VirtualListScrollHandle;

use super::FaceScrollKey;

/// The desktop's virtual-face book: one persistent [`VirtualListScrollHandle`]
/// (plus a tail cursor) per dense log face. Handles are never evicted — a handle
/// is a couple of `Rc`-counted words, and keeping it across a window close is
/// exactly what lands a reopened chronicle back on the tail it was following.
#[derive(Default)]
pub struct VirtualFaceRegistry {
    handles: HashMap<FaceScrollKey, VirtualListScrollHandle>,
    /// The item count each face last rendered — the tail-follow trigger.
    counts: HashMap<FaceScrollKey, usize>,
}

impl VirtualFaceRegistry {
    /// The face's persistent virtual-scroll handle — minted on first ask, the
    /// SAME live handle (clones share one `Rc` state) on every ask after.
    /// Rendering clones it into the `v_virtual_list` element AND hands its
    /// `base_handle()` to the NT scrollbar; both track the one truth here.
    pub fn ensure(&mut self, key: FaceScrollKey) -> VirtualListScrollHandle {
        self.handles
            .entry(key)
            .or_insert_with(VirtualListScrollHandle::new)
            .clone()
    }

    /// **Tail-follow bookkeeping** — `tail -f` for a virtualized log face.
    ///
    /// If `count` differs from the count this face last rendered, defer a scroll
    /// to the new last row (`count - 1`) and record `count`. The deferred scroll
    /// lands on the face's persistent handle, so the NEXT `v_virtual_list`
    /// prepaint parks the viewport on the fresh tail — the newest receipt in
    /// view the instant the pulse commits it. Returns whether a follow was
    /// scheduled (the bake witness): `true` on a real growth/reset, `false` when
    /// the count is unchanged (leave the operator's manual scroll alone) or the
    /// log is empty.
    ///
    /// Only append-order faces (chronicle, transcript, receipt console) follow
    /// their tail; an id-sorted census (the Ledger) passes through `ensure`
    /// WITHOUT this, so it keeps whatever place the operator scrolled to.
    pub fn follow_tail(&mut self, key: FaceScrollKey, count: usize) -> bool {
        if self.counts.get(&key).copied() == Some(count) {
            return false;
        }
        self.counts.insert(key, count);
        if count == 0 {
            return false;
        }
        self.handles
            .entry(key)
            .or_insert_with(VirtualListScrollHandle::new)
            .scroll_to_item(count - 1, ScrollStrategy::Bottom);
        true
    }

    /// The item count the face last rendered, or `None` if never rendered — the
    /// tail-follow witness for the bakes.
    pub fn last_count(&self, key: &FaceScrollKey) -> Option<usize> {
        self.counts.get(key).copied()
    }
}

/// **The visible half-open row range** for a uniform-height virtualized face at
/// scroll offset `offset_y` — the pure, window-free specialization of the widget
/// kit's `VirtualList` vertical scan (`gpui-component` `virtual_list.rs`, the
/// `Axis::Vertical` arm) for the case every desktop log face uses: every row the
/// same `row_h`, no leading padding.
///
/// `offset_y` follows gpui's convention: `0.0` at the top, growing NEGATIVE as
/// the face scrolls down (so `-offset_y` is the distance scrolled past the top).
/// The returned range is exactly the set of indices the kit would paint — the
/// first row whose bottom edge clears the scrolled top, through the first row
/// whose bottom edge clears the viewport foot (inclusive, kit-clamped to
/// `count`). This is what lets a bake assert "at offset N over 10k rows the face
/// shows rows [a, b)" without standing up a window.
pub fn visible_row_range(count: usize, row_h: f32, viewport_h: f32, offset_y: f32) -> Range<usize> {
    if count == 0 || row_h <= 0.0 {
        return 0..0;
    }

    // First visible: the smallest index whose cumulative bottom passes the
    // scrolled top edge (`-offset_y`). Mirrors the kit's `cumulative_size` loop.
    let mut cumulative = 0.0f32;
    let mut first = 0usize;
    for i in 0..count {
        cumulative += row_h;
        if cumulative > -offset_y {
            first = i;
            break;
        }
    }

    // Last visible: the smallest index whose cumulative bottom passes the
    // viewport foot; the kit then adds one and clamps to `count`. If nothing
    // passes the foot (the whole tail fits), the range runs to the end.
    cumulative = 0.0;
    let mut last = 0usize;
    for i in 0..count {
        cumulative += row_h;
        if cumulative > -offset_y + viewport_h {
            last = i + 1;
            break;
        }
    }
    if last == 0 {
        last = count;
    } else {
        last += 1;
    }

    first..last.min(count)
}

/// The scroll offset that parks a uniform-height face on its TAIL — the last row
/// resting against the viewport foot, exactly where [`VirtualFaceRegistry::follow_tail`]'s
/// deferred `scroll_to_item(last, Bottom)` lands after the kit clamps it. A short
/// log that fits entirely sits at `0.0` (no scroll). The bakes use this to read
/// the rows a tail-following face shows without a window.
pub fn tail_offset(count: usize, row_h: f32, viewport_h: f32) -> f32 {
    let content_h = count as f32 * row_h;
    -(content_h - viewport_h).max(0.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::CellId;

    use crate::deos_desktop::WinKindTag;

    fn key(n: u8) -> FaceScrollKey {
        FaceScrollKey::Window(CellId::from_bytes([n; 32]), WinKindTag::Transcript, 0)
    }

    /// The tail cursor fires a follow ONLY on a count change: first sight and
    /// every growth schedule a scroll; a repaint at the same count does not (so a
    /// reader scrolled up mid-history is left where they are until the next
    /// receipt actually lands).
    #[test]
    fn follow_tail_fires_only_on_growth() {
        let mut reg = VirtualFaceRegistry::default();
        let k = key(0x11);

        // Never-seen face has no recorded count.
        assert_eq!(reg.last_count(&k), None);
        // First sight of a non-empty log follows the tail.
        assert!(reg.follow_tail(k, 24));
        assert_eq!(reg.last_count(&k), Some(24));
        // A repaint at the SAME count does not yank the viewport.
        assert!(!reg.follow_tail(k, 24));
        // A pulse lands a receipt → follow the fresh tail.
        assert!(reg.follow_tail(k, 25));
        assert_eq!(reg.last_count(&k), Some(25));
        // An empty log records the count but schedules nothing.
        assert!(!reg.follow_tail(k, 0));
        assert_eq!(reg.last_count(&k), Some(0));
    }

    /// The handle is persistent: two `ensure`s hand back clones of one shared
    /// state, and the deferred scroll a `follow_tail` set on the registry's copy
    /// is visible through an `ensure` clone — so the element built from `ensure`
    /// carries the tail-follow the registry scheduled.
    #[test]
    fn ensure_shares_one_live_handle() {
        let mut reg = VirtualFaceRegistry::default();
        let k = key(0x22);
        let a = reg.ensure(k);
        a.set_offset(gpui::point(gpui::px(0.0), gpui::px(-12.0)));
        // A later frame's ensure sees the same live offset.
        assert_eq!(f32::from(reg.ensure(k).offset().y), -12.0);
    }

    /// At the TOP (offset 0) a 10k-row face paints only the handful that fit the
    /// viewport — the uncap is virtual, not eager. The window starts at row 0.
    #[test]
    fn top_of_ten_thousand_shows_only_the_visible_head() {
        let n = 10_000;
        let r = visible_row_range(n, 18.0, 360.0, 0.0);
        assert_eq!(r.start, 0);
        // 360 / 18 = 20 rows fit; the kit paints that window + its one-row margin.
        assert!(r.end >= 20 && r.end <= 22, "range was {r:?}");
        assert!(r.len() < 30, "virtualized, not eager: {} rows", r.len());
    }

    /// At a deep offset the window is the rows straddling that scroll position —
    /// NOT the head, NOT the whole log. "Correct rows at offset N."
    #[test]
    fn mid_scroll_shows_the_rows_at_that_offset() {
        let n = 10_000;
        let row_h = 18.0;
        let viewport = 360.0;
        // Scroll down so row 5000's top sits at the viewport top.
        let offset = -(5000.0 * row_h);
        let r = visible_row_range(n, row_h, viewport, offset);
        assert_eq!(r.start, 5000, "first visible is the row at the offset");
        assert!(r.contains(&5000) && r.contains(&5010));
        assert!(
            !r.contains(&4998) && !r.contains(&5030),
            "window is local: {r:?}"
        );
    }

    /// Parked on the tail, the newest row is in the painted window — the visible
    /// end of `tail -f` over a 10k-row log.
    #[test]
    fn tail_offset_paints_the_newest_row() {
        let n = 10_000;
        let row_h = 18.0;
        let viewport = 360.0;
        let off = tail_offset(n, row_h, viewport);
        let r = visible_row_range(n, row_h, viewport, off);
        assert!(r.contains(&(n - 1)), "tail row {} not in {r:?}", n - 1);
        // …and it is still virtualized: the whole head is NOT painted.
        assert!(!r.contains(&0));
    }

    /// A short log that fits entirely renders every row and sits unscrolled.
    #[test]
    fn short_log_fits_without_scrolling() {
        assert_eq!(tail_offset(5, 18.0, 360.0), 0.0);
        assert_eq!(visible_row_range(5, 18.0, 360.0, 0.0), 0..5);
        assert_eq!(visible_row_range(0, 18.0, 360.0, 0.0), 0..0);
    }
}
