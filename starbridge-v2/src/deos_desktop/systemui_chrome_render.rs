//! **The graphideOS SystemUI cap-chrome ON THE GLASS** — the gpui render of
//! [`crate::systemui_caps::SystemUiCapChrome`] as a real `deos_desktop` window body.
//!
//! `GRAPHIDEOS.md §1` (the SystemUI row) + `§2` stage 4 named one seam: the pure,
//! `cargo test`-able cap-chrome model ([`crate::systemui_caps`]) was built and proven,
//! and the gpui body that paints it into the live cockpit was "the collision-free
//! `native-full` follow-up". This module IS that body. For a focused
//! [`super::WinKindTag::AndroidCell`] window it renders the phone's SystemUI as the deos
//! cap surface — the three surfaces the model computes:
//!
//! 1. **the status-bar strip** — the always-visible top edge: `🛡 held/total caps` plus
//!    a lit pill per authority the confined android-cell holds right now
//!    ([`SystemUiCapChrome::status_bar`]). The app's standing authority on its face.
//! 2. **the quick-settings shade** — pulled down by the strip's `▾ shade` toggle: the
//!    WHOLE permission roster ([`SystemUiCapChrome::quick_settings`]), each lit ● (held,
//!    green) or dim ○ (not held, muted), with its never-hidden reason. No hidden Settings
//!    tree — pull the shade and SEE every authority the app does and does not hold.
//! 3. **the hand-over sheet** — the dangerous declared-but-dim caps as grant rows
//!    ([`SystemUiCapChrome::grant_sheet`]); tapping one drives a REAL
//!    [`SystemUiCapChrome::hand_over`] — an `Effect::GrantCapability` through the verified
//!    `TurnExecutor` — so the cap lands in the cell's c-list with a kernel receipt and the
//!    badge flips lit (the status pill appears) because the cell GENUINELY holds it. The
//!    powerbox tooth is the backstop: a cap the device principal cannot back is refused by
//!    the executor itself, the cap never lands.
//!
//! This is pure presentation/app over machinery this workspace already PROVES (no new
//! kernel effect, no new authority): a status bar and a shade are two renderings of one
//! [`android_cell::CapBadgeSet`], and a hand-over is one already-verified turn. The live
//! chrome (the `SystemUiCapChrome` wrapping a real `PermWorld` + executor) is held per
//! window in [`super::DeosDesktop::systemui_chromes`], minted lazily on first paint.

use gpui::{
    div, px, AnyElement, Context, InteractiveElement, IntoElement, MouseButton, MouseDownEvent,
    ParentElement, SharedString, Styled,
};

use android_cell::{AndroidPermission, KernelGrantOutcome};
use dregg_types::CellId;

use super::chrome::{
    bevel_raised, face_section, id_hex, NT_DIM, NT_LABEL, NT_OK, NT_PANEL, NT_RULE, NT_TEXT,
    NT_TITLE_ACTIVE, NT_TITLE_TEXT, NT_WARN,
};
use super::DeosDesktop;
use crate::systemui_caps::SystemUiCapChrome;

impl DeosDesktop {
    /// Mint the confined android-cell's live cap-chrome on first paint of its window and
    /// cache it in [`Self::systemui_chromes`]. A demo "Maps" cell declaring
    /// INTERNET (normal) + ACCESS_FINE_LOCATION + CAMERA (dangerous), whose device
    /// principal can back LOCATION but holds NO camera authority — so LOCATION hands over
    /// (the badge lights) and CAMERA is refused by the executor (no ambient escalation).
    /// Each chrome wraps its OWN real `PermWorld` (a confined ledger + the verified
    /// executor); the desktop window only hosts and paints it.
    pub(super) fn ensure_android_chrome(&mut self, cell: CellId) {
        self.systemui_chromes.entry(cell).or_insert_with(|| {
            SystemUiCapChrome::install(
                "Maps · com.example.maps",
                "com.example.maps",
                0x51,
                0x01,
                [
                    AndroidPermission::Internet,
                    AndroidPermission::AccessFineLocation,
                    AndroidPermission::Camera,
                ],
                [AndroidPermission::AccessFineLocation],
            )
        });
    }

    /// Toggle the quick-settings shade for `cell`'s android-cell window (pull it down /
    /// snap it back up).
    pub(super) fn android_toggle_shade(&mut self, cell: CellId) {
        if !self.systemui_shades.remove(&cell) {
            self.systemui_shades.insert(cell);
        }
    }

    /// **TAP A HAND-OVER ROW → the real kernel grant.** Drive
    /// [`SystemUiCapChrome::hand_over`] (an `Effect::GrantCapability` through the verified
    /// executor) for `perm` on `cell`'s confined chrome; surface the verdict in the
    /// desktop status line. On a committed grant the cap lands in the cell's c-list and
    /// the badge flips lit on the very next paint.
    pub(super) fn android_hand_over(
        &mut self,
        cell: CellId,
        perm: AndroidPermission,
    ) -> KernelGrantOutcome {
        self.ensure_android_chrome(cell);
        let outcome = self
            .systemui_chromes
            .get_mut(&cell)
            .expect("android chrome ensured")
            .hand_over(perm);
        self.say(SystemUiCapChrome::outcome_line(&outcome));
        outcome
    }

    /// **RENDER THE SYSTEMUI CAP-CHROME** for a focused [`super::WinKindTag::AndroidCell`]
    /// window — the status-bar strip, the pull-down quick-settings shade, and the
    /// hand-over sheet, over the cell's live confined cap-chrome.
    pub(super) fn render_android_systemui_body(
        &mut self,
        cell: CellId,
        scroll: &gpui::ScrollHandle,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        self.ensure_android_chrome(cell);
        let shade_open = self.systemui_shades.contains(&cell);
        let (app_label, bar, shade, sheet) = {
            let chrome = self
                .systemui_chromes
                .get(&cell)
                .expect("android chrome ensured");
            (
                chrome.app_label().to_string(),
                chrome.status_bar(),
                chrome.quick_settings(),
                chrome.grant_sheet(),
            )
        };
        let hex = id_hex(&cell);

        // ── 1. THE STATUS-BAR STRIP — the always-visible top edge (navy, like a phone). ──
        let mut strip = div()
            .flex()
            .items_center()
            .gap_1()
            .w_full()
            .px_2()
            .py_1()
            .bg(gpui::rgb(NT_TITLE_ACTIVE))
            .text_color(gpui::rgb(NT_TITLE_TEXT))
            .text_size(px(11.0))
            .child(div().child(SharedString::from(bar.summary.clone())));
        for held in &bar.held {
            // Every status-bar pill is a LIT (held) authority — a green cap badge.
            strip = strip.child(
                div()
                    .px_1()
                    .rounded(px(3.0))
                    .bg(gpui::rgb(NT_OK))
                    .text_color(gpui::rgb(0xffffff))
                    .text_size(px(10.0))
                    .child(SharedString::from(held.clone())),
            );
        }
        // The shade toggle pulls the quick-settings roster down / snaps it back up.
        strip = strip.child(div().flex_1()).child(
            div()
                .id(SharedString::from(format!("sysui-shade-{hex}")))
                .px_1()
                .rounded(px(3.0))
                .text_size(px(10.0))
                .child(SharedString::from(if shade_open {
                    "▴ shade"
                } else {
                    "▾ shade"
                }))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.android_toggle_shade(cell);
                        cx.notify();
                    }),
                ),
        );

        // The body column: the app label, the (optional) shade, then the hand-over sheet.
        let mut body = div()
            .id(SharedString::from(format!("sysui-body-{hex}")))
            .bg(gpui::rgb(NT_PANEL))
            .flex()
            .flex_col()
            .child(strip)
            .child(
                div()
                    .px_2()
                    .py_1()
                    .text_size(px(11.0))
                    .text_color(gpui::rgb(NT_LABEL))
                    .child(SharedString::from(format!("SystemUI · {app_label}"))),
            );

        // ── 2. THE QUICK-SETTINGS SHADE — the WHOLE roster, lit ●/dim ○ + the reason. ──
        if shade_open {
            let mut shade_col = div().flex().flex_col().px_2().pb_1().child(face_section(
                "Quick Settings — every authority shown, lit ● or dim ○ (no hidden Settings tree)",
            ));
            for line in &shade {
                // `quick_settings()` rows start with the lit/dim glyph; color by it.
                let lit = line.starts_with('●');
                shade_col = shade_col.child(
                    div()
                        .py(px(1.0))
                        .text_size(px(11.0))
                        .text_color(gpui::rgb(if lit { NT_OK } else { NT_DIM }))
                        .child(SharedString::from(line.clone())),
                );
            }
            body = body
                .child(shade_col)
                .child(div().mx_2().h(px(1.0)).bg(gpui::rgb(NT_RULE)));
        }

        // ── 3. THE HAND-OVER SHEET — the dangerous declared-but-dim caps, each a tap. ──
        let mut sheet_col = div().flex().flex_col().px_2().py_1();
        if sheet.is_empty() {
            sheet_col = sheet_col.child(face_section("Hand-over sheet")).child(
                div()
                    .text_size(px(11.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child("(nothing to hand over — no declared-but-dim cap)"),
            );
        } else {
            sheet_col = sheet_col.child(face_section(
                "Hand-over sheet — tap a cap; each is a receipted Effect::GrantCapability turn, not a dialog",
            ));
            for row in &sheet {
                let perm = row.permission.clone();
                let label = row.label.clone();
                sheet_col = sheet_col.child(
                    bevel_raised(
                        div()
                            .id(SharedString::from(format!(
                                "sysui-grant-{hex}-{}",
                                label.replace([' ', '○', '●'], "")
                            )))
                            .my(px(2.0))
                            .px_2()
                            .py_1()
                            .flex()
                            .items_center()
                            .gap_2()
                            .text_size(px(11.0))
                            .text_color(gpui::rgb(NT_TEXT))
                            .child(div().child(SharedString::from(label)))
                            .child(div().flex_1())
                            .child(div().text_color(gpui::rgb(NT_WARN)).child("hand over →")),
                    )
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            this.android_hand_over(cell, perm.clone());
                            cx.notify();
                        }),
                    ),
                );
            }
        }
        body = body.child(sheet_col);

        // The SystemUI column scrolls behind a REAL NT scrollbar (shade + sheet
        // can outgrow the window; the persistent handle keeps the place).
        super::chrome::nt_scroll_face(scroll, body).into_any_element()
    }

    // ── Bake / test hooks (drive the SystemUI cap-chrome headlessly) ─────────────────

    /// Open a SystemUI cap-chrome (android-cell) window on `cell` — what double-clicking
    /// an android-cell or the menu's "Open as Android Cell" does.
    pub fn bake_open_android_cell(&mut self, cell: CellId) {
        self.open_kind(cell, super::WinKindTag::AndroidCell);
    }

    /// Pull down / snap up the quick-settings shade (what the strip's `▾ shade` does).
    pub fn bake_android_toggle_shade(&mut self, cell: CellId) {
        self.android_toggle_shade(cell);
    }

    /// The android-cell's lit (held) status-bar authorities — what the strip pills show.
    pub fn bake_android_status_held(&mut self, cell: CellId) -> Vec<String> {
        self.ensure_android_chrome(cell);
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.status_bar().held)
            .unwrap_or_default()
    }

    /// The whole quick-settings roster (the shade rows: `● NET — held …` / `○ CAMERA — …`).
    pub fn bake_android_quick_settings(&mut self, cell: CellId) -> Vec<String> {
        self.ensure_android_chrome(cell);
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.quick_settings())
            .unwrap_or_default()
    }

    /// The hand-over sheet's grant-row count (the declared-but-dim dangerous caps).
    pub fn bake_android_sheet_len(&mut self, cell: CellId) -> usize {
        self.ensure_android_chrome(cell);
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.grant_sheet().len())
            .unwrap_or(0)
    }

    /// **Tap a hand-over row** — drive the REAL `Effect::GrantCapability` for `perm` and
    /// report whether the cap landed (committed by the verified executor).
    pub fn bake_android_hand_over(&mut self, cell: CellId, perm: AndroidPermission) -> bool {
        self.android_hand_over(cell, perm).granted()
    }

    // Read-only views of an ALREADY-PAINTED android-cell's chrome (the window's first
    // paint mints it), for a bake asserting over `desk.read(cx)`.

    /// The lit (held) status-bar authorities of `cell`'s painted SystemUI chrome.
    pub fn clone_status_held(&self, cell: CellId) -> Vec<String> {
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.status_bar().held)
            .unwrap_or_default()
    }

    /// The whole quick-settings roster of `cell`'s painted SystemUI chrome.
    pub fn clone_quick_settings(&self, cell: CellId) -> Vec<String> {
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.quick_settings())
            .unwrap_or_default()
    }

    /// The hand-over sheet's grant-row count of `cell`'s painted SystemUI chrome.
    pub fn clone_sheet_len(&self, cell: CellId) -> usize {
        self.systemui_chromes
            .get(&cell)
            .map(|c| c.grant_sheet().len())
            .unwrap_or(0)
    }
}
