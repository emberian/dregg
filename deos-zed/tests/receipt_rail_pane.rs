//! THE RECEIPT-RAIL seam: the cockpit editor pane can show, live, the open
//! file's RECEIPT TIMELINE — each committed save as a chained `TurnReceipt`
//! chip — and a save through the real editor path lands its chip without the
//! host re-driving anything.
//!
//! Where `firmament_pane.rs` proves a save is a receipted turn through the
//! pane, and `editor_structure_pane.rs` proves the STRUCTURE face tracks the
//! live document, this proves the LEDGER face: the `EditorPaneView`'s third
//! tab drives a `ReceiptRail` whose snapshot tracks the REAL per-file receipt
//! history off the live firmament spine ([`FirmamentFs::history`]), and the
//! rail's `verify chain` verdict is the genuine subsequence-of-the-global-log
//! check. Drives the REAL gpui `EditorSurface` in a headless gpui app.
//!
//! Run with:
//!   cargo test --features "firmament screenshot" --test receipt_rail_pane

#![cfg(all(
    feature = "firmament",
    feature = "cockpit-surface",
    feature = "screenshot"
))]

use std::borrow::Cow;
use std::path::PathBuf;
use std::sync::Arc;

use gpui::{
    px, size, AppContext as _, HeadlessAppContext, IntoElement, PlatformTextSystem, Render,
};
use gpui_wgpu::CosmicTextSystem;

use deos_zed::cockpit_surface::{EditorSurface, ViewMode};
use deos_zed::receipt_rail::RailVerdict;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

struct PaneHolder {
    surface: EditorSurface,
}

impl Render for PaneHolder {
    fn render(
        &mut self,
        window: &mut gpui::Window,
        cx: &mut gpui::Context<Self>,
    ) -> impl IntoElement {
        self.surface.render_body(window, cx)
    }
}

#[test]
fn editor_pane_receipt_rail_tracks_the_live_ledger() {
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("load fonts");

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let path = "/deos/main.rs";
    let seed = "fn main() {\n    println!(\"before\");\n}\n";
    let edit_one = "fn main() {\n    println!(\"first receipted save\");\n}\n";
    let edit_two = "fn main() {\n    println!(\"second receipted save\");\n}\n";

    let window = cx
        .open_window(size(px(900.), px(600.)), |window, cx| {
            cx.new(|cx| {
                let surface = EditorSurface::firmament(
                    11,
                    PathBuf::from("/deos"),
                    &[(path, seed)],
                    window,
                    cx,
                )
                .expect("firmament surface mounts");
                PaneHolder { surface }
            })
        })
        .expect("headless window");

    cx.run_until_parked();

    // 1. A seed is genesis, not a turn: the rail starts EMPTY (and honestly
    //    verifies Empty), even though the file is open in the buffer.
    window
        .update(&mut cx, |holder, _window, cx| {
            let rail = holder.surface.receipt_rail(cx);
            rail.update(cx, |r, _cx| {
                assert_eq!(r.chip_count(), 0, "a seed is genesis — no chips yet");
                assert_eq!(*r.run_verify(), RailVerdict::Empty);
            });
        })
        .unwrap();

    // 2. Save through the editor's REAL save path. The pane observes the
    //    editor's notify, so the rail re-snapshots WITHOUT any host driving —
    //    the chip lands live. The status line stamps the receipt fingerprint.
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edit_one, window, cx);
                ed.save(cx).expect("save commits a turn");
            });
        })
        .unwrap();
    cx.run_until_parked();

    window
        .update(&mut cx, |holder, _window, cx| {
            let firm = holder
                .surface
                .firmament_fs()
                .expect("firmament-backed surface")
                .clone();
            let editor = holder.surface.editor().clone();
            let status = editor.read(cx).status().to_string();
            assert!(
                status.contains("⛓"),
                "the status line stamps the minted receipt fingerprint: {status}"
            );

            let rail = holder.surface.receipt_rail(cx);
            rail.update(cx, |r, _cx| {
                assert_eq!(
                    r.chip_count(),
                    1,
                    "the save's chip landed via the observe wire (no host refresh)"
                );
                // The newest chip IS the spine's last receipt — one truth,
                // two reads (the rail reads the same cell history the fs holds).
                assert_eq!(
                    r.latest_hash(),
                    firm.last_receipt().map(|rc| rc.receipt_hash()),
                    "the chip's hash is the genuine TurnReceipt hash"
                );
            });
        })
        .unwrap();

    // 3. Toggle to the LEDGER face (the third tab's host path), save again,
    //    and verify: two chips, directly chained, embedded in the global log.
    window
        .update(&mut cx, |holder, window, cx| {
            holder.surface.set_mode(ViewMode::Ledger, cx);
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edit_two, window, cx);
                ed.save(cx).expect("second save commits");
            });
        })
        .unwrap();
    cx.run_until_parked();

    window
        .update(&mut cx, |holder, _window, cx| {
            assert_eq!(
                holder.surface.mode(cx),
                ViewMode::Ledger,
                "the pane shows the ledger face"
            );
            let rail = holder.surface.receipt_rail(cx);
            rail.update(cx, |r, _cx| {
                assert_eq!(r.chip_count(), 2, "two receipted saves, two chips");
                match r.run_verify() {
                    RailVerdict::Verified {
                        direct,
                        threaded,
                        global_checked,
                    } => {
                        assert_eq!(*direct, 1, "back-to-back saves chain directly");
                        assert_eq!(*threaded, 0, "no other file's turn intervened");
                        assert!(*global_checked, "the owned spine publishes its global log");
                    }
                    other => panic!("the rail must verify: {other:?}"),
                }
            });
        })
        .unwrap();
}
