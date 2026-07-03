//! THE PROOF, BY RUNNING: the cockpit's INSPECTOR is a deos-js card — its view is GENERATED
//! from a focused cell's moldable faces, rendered to REAL gpui-component pixels, an affordance
//! fires a REAL verified turn that advances a bound field, and the inspector's OWN view is
//! EDITABLE FROM WITHIN (a receipted patch that visibly reshapes the rendered UI).
//!
//! The flow (one big-stack thread — the same harness the applet-view proof uses):
//!   1. Focus an [`InspectorCard`] on a counter cell. Its view-tree is generated from the
//!      RawFields face (a live-bound slot-0 row) + the Affordances face (an `inc` button).
//!      Render that view-source over the live focused applet → PNG #1 (the inspector, count 1).
//!   2. Fire the `inc` affordance from the inspector = a REAL cap-gated verified turn; assert
//!      the bound slot-0 advanced 1 → 2. Re-render → PNG #2 (the bound row tracked the turn).
//!   3. EDIT FROM WITHIN: relabel the "What this holds" face to "Substance" + append an "inc ×5"
//!      button — receipted patches with blame. Render the RESHAPED view-source → PNG #3, which
//!      DIFFERS from #1 (the inspector UI was rewritten from inside, accountably).

use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::card_editor::ViewPatch;
use deos_js::{Author, InspectorCard};
use dregg_cell::AuthRequired;
use gpui::AppContext;

use deos_view::headless::HeadlessRender;
use deos_view::{parse_view_tree, AppletView};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A focused cell: slot 0 holds a counter (seeded to 1 so the RawFields face surfaces it as a
/// revealed state slot → a LIVE bind row), with an `inc` affordance (Signature-gated, held).
fn counter_card() -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = 0xBE;
    let inc = Affordance {
        name: "inc".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        pk,
        [0u8; 32],
        &[(0usize, pack_u64(1))],
        vec![inc],
        AuthRequired::Signature,
    )
}

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/render-out");
    std::fs::create_dir_all(&dir).expect("create render-out dir");
    dir
}

#[test]
fn inspector_card_renders_fires_and_reshapes_from_within_to_real_gpui_pixels() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(inspector_proof_body)
        .expect("spawn big-stack render thread")
        .join()
        .expect("inspector render proof thread");
}

fn inspector_proof_body() {
    let out = out_dir();

    // ── 1. Focus the inspector → its view is GENERATED from the focused cell's faces ─────
    let card = InspectorCard::focus(
        counter_card(),
        Author(42),
        /*held=*/ AuthRequired::None,
        /*edit_authority=*/ AuthRequired::Signature,
    );
    let source_before = card.view_source();
    // The RawFields face's section title is "What this holds" and the Affordances face carries
    // the focused cell's `inc` button. NOTE: the section reads "What this holds" (not the older
    // "Cell State"): `deos_js::InspectorCard`'s generator was warmed to jargon-free titles by
    // the consumer-delight progressive-disclosure pass, and its own tests
    // (`deos-js/tests/inspector_card.rs`) codify those friendly titles. Do NOT "restore" the
    // "Cell State" wording here — this test simply hadn't been swept to the new naming.
    assert!(
        source_before.contains("What this holds") && source_before.contains("inc"),
        "the generated inspector view carries the RawFields + Affordances faces"
    );

    // Take the live focused applet so the rendered Bind rows re-read it + a Button fires it.
    let applet = card.into_card();
    let shared = Rc::new(RefCell::new(applet));

    let mut hr = HeadlessRender::boot("Lilex", &[LILEX, IBM_PLEX]).expect("boot headless gpui");

    // Render the generated inspector view-source over the live applet → PNG #1.
    let tree0 = parse_view_tree(&source_before).expect("parse the generated inspector view-tree");
    let a0 = shared.clone();
    let window = hr
        .open(520.0, 900.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a0, tree0))
        })
        .expect("open the inspector window");
    let frame0 = hr
        .capture(window.into())
        .expect("capture inspector frame 0");
    let png0 = out.join("inspector-focus.png");
    frame0.save(&png0).expect("save PNG #0");
    assert!(
        frame0.width() > 0 && frame0.height() > 0,
        "frame 0 has pixels"
    );

    // ── 2. FIRE the `inc` affordance from the inspector — a REAL verified turn ───────────
    assert_eq!(
        shared.borrow().get_u64(0),
        1,
        "the counter starts at its seed (1)"
    );
    let receipt = shared
        .borrow_mut()
        .fire("inc", 1)
        .expect("the inspector's `inc` affordance fires a verified turn");
    assert_ne!(
        receipt.receipt_hash(),
        [0u8; 32],
        "a real TurnReceipt committed"
    );
    assert_eq!(
        shared.borrow().get_u64(0),
        2,
        "the bound slot-0 row advanced 1 -> 2 (the live ledger the bind re-reads)"
    );

    // Drive the fine-grained hook (slot 0 dirtied) + re-render → PNG #2.
    let dirty = hr
        .update_root(window, |view, _w, _cx| view.on_committed_turn(&[0]))
        .expect("drive the fine-grained turn hook");
    assert!(
        dirty.contains(&deos_js::signals::BindingId(0)),
        "the inc turn dirtied the slot-0 binding the RawFields row reads"
    );
    hr.update(|cx| cx.refresh_windows());
    let frame1 = hr
        .capture(window.into())
        .expect("capture inspector frame 1");
    let png1 = out.join("inspector-fired.png");
    frame1.save(&png1).expect("save PNG #1");
    assert_ne!(
        frame0.as_raw(),
        frame1.as_raw(),
        "the rendered inspector changed after the turn (the bound count re-read 1 -> 2)"
    );

    // ── 3. EDIT FROM WITHIN — reshape the inspector's OWN view, accountably ──────────────
    // The reshape is a property of the inspector card's view-DOCUMENT (a receipted patch +
    // blame), independent of which live applet a renderer paints it over. Drive it on an
    // inspector focused on an identically-shaped cell, then render the reshaped view-source
    // over the SAME live applet the window already shares (which is now advanced to 2).
    let mut card2 = InspectorCard::focus(
        counter_card(),
        Author(42),
        AuthRequired::None,
        AuthRequired::Signature,
    );

    let edit_a = card2
        .edit_view(ViewPatch::Relabel {
            // The RawFields face's current section title (post consumer-delight pass) is
            // "What this holds"; relabeling it from within renames the face to "Substance".
            from: "What this holds".into(),
            to: "Substance".into(),
        })
        .expect("relabel the RawFields face from within");
    let edit_b = card2
        .edit_view(ViewPatch::AddButton {
            label: "inc ×5".into(),
            turn: "inc".into(),
            arg: 5,
        })
        .expect("append a button from within");

    // The reshapes are RECEIPTED PATCHES with BLAME.
    assert_ne!(
        edit_a.receipt.receipt_hash(),
        [0u8; 32],
        "relabel left a provenance receipt"
    );
    assert_ne!(
        edit_b.receipt.receipt_hash(),
        [0u8; 32],
        "add-button left a provenance receipt"
    );
    assert!(
        card2.view_blame().iter().any(|l| l.author == Author(42)),
        "the reshapes are blamed on their author"
    );
    let source_after = card2.view_source();
    assert!(
        source_after.contains("Substance"),
        "the new face label landed"
    );
    assert!(
        source_after.contains("inc \u{00d7}5"),
        "the appended button landed"
    );

    // Render the RESHAPED view-source over the SAME live applet (advanced to 2) → PNG #3
    // (differs from #1: the face relabel + the appended button reshaped the UI from within).
    let tree2 = parse_view_tree(&source_after).expect("parse the reshaped inspector view-tree");
    let a2 = shared.clone();
    let window2 = hr
        .open(520.0, 900.0, move |_w, cx| {
            cx.new(|_cx| AppletView::new(a2, tree2))
        })
        .expect("open the reshaped inspector window");
    let frame2 = hr
        .capture(window2.into())
        .expect("capture reshaped inspector frame");
    let png2 = out.join("inspector-reshaped.png");
    frame2.save(&png2).expect("save PNG #2");
    assert_ne!(
        frame0.as_raw(),
        frame2.as_raw(),
        "the inspector UI was rewritten from within (relabel + new button) — the frame differs"
    );

    println!("RENDERED INSPECTOR-CARD PNGs (real gpui-component widgets, offscreen wgpu):");
    println!("  focus    : {}", png0.display());
    println!("  fired    : {}", png1.display());
    println!("  reshaped : {}", png2.display());
    println!(
        "frame dims: {}x{} (device px, 2x scale)",
        frame0.width(),
        frame0.height()
    );
}
