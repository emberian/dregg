//! **THE FACE-SCROLL REGISTRY** — persistent scroll positions for every dense face.
//!
//! Before this module, every scrolling surface on the desktop was a naked
//! `.overflow_y_scroll()` with anonymous per-frame element state: no thumb, no
//! visible position, and a scroll offset that evaporated whenever the element
//! tree was rebuilt around it. The registry gives the desktop ONE owned
//! [`gpui::ScrollHandle`] per dense face, so:
//!
//!   * the chrome-kit scrollbar ([`super::chrome::nt_scroll_face`]) has a real
//!     handle to read (thumb position + content size) and to drive (drag the
//!     thumb, click the track), and
//!   * the scroll POSITION becomes desktop view-state — it survives repaints,
//!     tab flips away and back, and even a window close/reopen, exactly like
//!     the spatially-persisted window geometry (a position you chose is a
//!     position the desktop keeps).
//!
//! The registry is pure, gpui-context-free bookkeeping (a `ScrollHandle` is a
//! cheap `Rc` bundle whose offset can be read and written headlessly), so the
//! whole thing is unit-testable without a window — the persistence claim is
//! asserted in [`tests`], not just narrated.

use std::collections::HashMap;

use gpui::ScrollHandle;

use dregg_types::CellId;

use super::WinKindTag;

/// **Which dense face a scroll handle belongs to.** Window bodies are keyed by
/// their window identity plus a face ordinal (tabbed bodies — the World
/// Explorer's ledger/chronicle/conservation, the Agent Room's
/// actions/mandate/reach — scroll independently per tab); the desktop's
/// non-window chrome overlays (the Spotter panel, the receipt-console flyout,
/// the property dialogs) are keyed by name.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FaceScrollKey {
    /// A window body's face: the window's anchor cell, its kind, and the face
    /// ordinal within the window (`0` for single-face bodies; the tab index —
    /// `tab as u8` — for tabbed ones, so each tab keeps its own place).
    Window(CellId, WinKindTag, u8),
    /// A named chrome overlay face (one per desktop): the Spotter panel, the
    /// receipt-console flyout, the desktop Preferences dialog body.
    Chrome(&'static str),
    /// A named chrome face that exists per cell (a cell's Properties dialog).
    CellChrome(&'static str, CellId),
}

/// The desktop's scroll-handle book: get-or-mint per face key. Handles are
/// never evicted — a handle is a couple of `Rc`-counted words, and keeping it
/// across a window close is precisely what makes the reopened window land back
/// where the operator left it.
#[derive(Default)]
pub struct FaceScrollRegistry {
    handles: HashMap<FaceScrollKey, ScrollHandle>,
}

impl FaceScrollRegistry {
    /// The face's persistent handle — minted on first ask, the SAME live handle
    /// (clone of one shared `Rc` state) on every ask after. Rendering clones it
    /// into the element tree; the registry keeps the truth.
    pub fn ensure(&mut self, key: FaceScrollKey) -> ScrollHandle {
        self.handles.entry(key).or_default().clone()
    }

    /// Read a face's current vertical offset in px (`0.0` at the top, growing
    /// NEGATIVE as the face scrolls down — gpui's offset convention), or `None`
    /// if the face has never been rendered/asked-for. The bake hooks' witness.
    pub fn offset_y(&self, key: &FaceScrollKey) -> Option<f32> {
        self.handles.get(key).map(|h| f32::from(h.offset().y))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gpui::{point, px};

    fn cell(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// The UX win, asserted: a face's scroll offset written through one ensure
    /// survives to the next ensure — the registry hands back the SAME live
    /// handle, so the position persists across repaints (and window reopens,
    /// which go through the same key).
    #[test]
    fn scroll_position_persists_across_ensures() {
        let mut reg = FaceScrollRegistry::default();
        let key = FaceScrollKey::Window(cell(0x11), WinKindTag::Transcript, 0);

        let handle = reg.ensure(key);
        handle.set_offset(point(px(0.0), px(-42.0)));
        drop(handle);

        // A later frame's ensure sees the position the earlier frame set.
        assert_eq!(f32::from(reg.ensure(key).offset().y), -42.0);
        assert_eq!(reg.offset_y(&key), Some(-42.0));
    }

    /// Faces scroll independently: distinct keys (another tab of the SAME
    /// window, a chrome overlay) mint distinct handles, and an unseen key
    /// reads `None` rather than a fabricated position.
    #[test]
    fn distinct_faces_hold_distinct_positions() {
        let mut reg = FaceScrollRegistry::default();
        let a = FaceScrollKey::Window(cell(0x22), WinKindTag::WorldExplorer, 0);
        let b = FaceScrollKey::Window(cell(0x22), WinKindTag::WorldExplorer, 1);

        reg.ensure(a).set_offset(point(px(0.0), px(-7.0)));
        let sibling = reg.ensure(b);
        assert_eq!(reg.offset_y(&a), Some(-7.0));
        // The sibling tab's face is untouched at the top…
        assert_eq!(f32::from(sibling.offset().y), 0.0);
        // …and a never-rendered face has no position to report.
        assert_eq!(reg.offset_y(&FaceScrollKey::Chrome("spotter")), None);
    }
}
