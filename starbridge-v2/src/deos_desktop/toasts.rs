//! **PULSE TOASTS** — the World's motion, arriving as small NT cards.
//!
//! The pulse ([`super::DeosDesktop::pump_dynamics`]) already notices when the
//! World moves without the desktop's own hand — a bot reactor, an attached
//! agent, a live node. The status bar narrates one line; a toast makes the
//! moment *arrive*: a small bevel-raised card in the bottom-right stack, green
//! for a committed foreign turn, amber for a REFUSAL (the ocap guarantee
//! firing is the most informative moment the desktop has — it deserves a
//! card, not a whisper). Clicking a toast opens the World Transcript so the
//! narration lands you on the receipt log; each card retires on its own after
//! a few pulse beats, newest at the bottom.
//!
//! ## The clobber-safe split
//!
//! This module owns the gpui-free model ([`Toast`], [`ToastKind`], the
//! [`ToastRack`] push/beat/retire logic — unit-tested below) and a pure
//! presentation fn ([`render_toast_rack`]) that returns inert card elements.
//! The desktop View owns the feed (its pulse pushes), the click listener
//! (open the Transcript, dismiss the rack), and the render-tail mount.

use gpui::{div, px, AnyElement, FontWeight, IntoElement, ParentElement, Styled};

use crate::deos_desktop::chrome::{bevel_raised, NT_DIM, NT_PANEL};

/// How many pulse beats (~250ms each) a toast lives before it retires on its
/// own — 16 beats ≈ four seconds, long enough to read, short enough to stay
/// out of the way of the next arrival.
pub const TOAST_TTL_BEATS: u8 = 16;

/// The most cards the rack shows at once — older cards retire early rather
/// than stacking into a wall (the World can be BUSY; the desktop stays calm).
pub const TOAST_RACK_CAP: usize = 4;

/// What kind of moment a toast announces — the card's color speaks first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToastKind {
    /// A foreign resident's turn COMMITTED (green edge — the world moved).
    Committed,
    /// A turn was REFUSED (amber edge — the ocap guarantee fired).
    Refused,
}

/// One announcement card: the reader-legible line plus its remaining life.
#[derive(Clone, Debug)]
pub struct Toast {
    pub kind: ToastKind,
    /// The card's one-line narration (already formatted by the pulse).
    pub line: String,
    /// Remaining pulse beats before the card retires itself.
    pub ttl: u8,
}

/// **The toast rack** — the gpui-free model the pulse feeds and the render
/// mounts. Push on arrival, beat once per pulse, retire at zero; the cap
/// retires the oldest first.
#[derive(Default)]
pub struct ToastRack {
    toasts: Vec<Toast>,
}

impl ToastRack {
    /// Announce a moment — newest lands at the END (the bottom of the stack);
    /// past the cap the OLDEST card retires early.
    pub fn push(&mut self, kind: ToastKind, line: impl Into<String>) {
        self.toasts.push(Toast {
            kind,
            line: line.into(),
            ttl: TOAST_TTL_BEATS,
        });
        if self.toasts.len() > TOAST_RACK_CAP {
            let overflow = self.toasts.len() - TOAST_RACK_CAP;
            self.toasts.drain(..overflow);
        }
    }

    /// One pulse beat — every card ages; the expired retire. Returns whether
    /// anything changed (the caller repaints only when it did).
    pub fn beat(&mut self) -> bool {
        if self.toasts.is_empty() {
            return false;
        }
        for t in self.toasts.iter_mut() {
            t.ttl = t.ttl.saturating_sub(1);
        }
        self.toasts.retain(|t| t.ttl > 0);
        true
    }

    /// Dismiss every card (the click-through gesture also clears the rack —
    /// you looked, the announcements did their job).
    pub fn clear(&mut self) {
        self.toasts.clear();
    }

    /// The live cards, oldest→newest (render order, top→bottom of the stack).
    pub fn toasts(&self) -> &[Toast] {
        &self.toasts
    }
}

/// Render the rack as inert card elements (oldest→newest, top→bottom). The
/// caller wraps them in the absolutely-positioned stack container and owns the
/// click listener — this fn is pure presentation over the model.
pub fn render_toast_rack(rack: &ToastRack) -> Vec<AnyElement> {
    rack.toasts()
        .iter()
        .map(|t| {
            let (edge, tag) = match t.kind {
                ToastKind::Committed => (0x2f7d3a_u32, "⋯ turn"),
                ToastKind::Refused => (0xa06000_u32, "REFUSED"),
            };
            bevel_raised(
                div()
                    .w(px(300.0))
                    .bg(gpui::rgb(NT_PANEL))
                    .border_l_4()
                    .border_color(gpui::rgb(edge))
                    .px_2()
                    .py_1(),
            )
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .text_size(px(10.0))
                    .child(
                        div()
                            .text_color(gpui::rgb(edge))
                            .font_weight(FontWeight::BOLD)
                            .child(tag),
                    )
                    .child(div().text_color(gpui::rgb(NT_DIM)).child(t.line.clone())),
            )
            .into_any_element()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Push → beat lifecycle: cards age one beat per pulse and retire at zero;
    /// the cap retires the oldest first; clear empties the rack.
    #[test]
    fn rack_push_beat_retire() {
        let mut rack = ToastRack::default();
        assert!(!rack.beat(), "an empty rack has no motion");

        rack.push(ToastKind::Committed, "one");
        for _ in 0..(TOAST_TTL_BEATS - 1) {
            assert!(rack.beat());
        }
        assert_eq!(rack.toasts().len(), 1, "alive until the last beat");
        rack.beat();
        assert!(rack.toasts().is_empty(), "retired at zero");

        for i in 0..(TOAST_RACK_CAP + 2) {
            rack.push(ToastKind::Refused, format!("t{i}"));
        }
        assert_eq!(rack.toasts().len(), TOAST_RACK_CAP, "capped");
        assert_eq!(rack.toasts()[0].line, "t2", "oldest retired first");

        rack.clear();
        assert!(rack.toasts().is_empty());
    }
}
