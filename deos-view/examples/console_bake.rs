//! THE CONSOLE BAKE — "My Dregg Computer" through the portable ViewNode IR, painted by
//! the gpui-free WEB renderer into browser-loadable `.html`.
//!
//! This is the graphideOS portability proof for the DreggNet management console: the
//! console DreggNet serves today is server-rendered HTML strings
//! (`DreggNet/console/src/render.rs` over `model.rs::ConsoleView`) — web-only by
//! construction. Here the SAME console content is a pure data tree
//! (`deos_view::console::console_card`), so ONE model renders native gpui
//! (`render::AppletView` walks the identical tree), web (this bake), discord, and — the
//! point — the graphideOS phone, which is just a fourth walker over the same IR.
//!
//! The bake:
//!   1. Build the fixture-shaped multi-tenant demo model and CAP-SCOPE it to the demo
//!      subject (the `scope.rs`/`Owned` seam — a foreign tenant's computers/hermeses/
//!      spend must not reach the card).
//!   2. Build the card + its pre-order bind snapshot (`console_bind_values`).
//!   3. Bake BOTH disclosure projections of the ONE card: `dregg-computer.html`
//!      (simple — the clean consumer view) and `dregg-computer-adept.html` (the
//!      see-the-bones view: full cell hex revealed). Same tree, two projections,
//!      identical bind cursor.
//!   4. Assert the contract on the produced markup (scoping, honest pills, cap teeth,
//!      gauges, the live-bound receipts count, the verify-anything wire) — the bake is
//!      a proof, not just a file.
//!
//! Files land in `target/web-out/dist/` beside the other card pages, so the gallery
//! (`web_render_card`'s `index.html`) can tile it. No gpui, no SpiderMonkey — the tiny
//! `web` graph:
//!   cd deos-view && cargo run --no-default-features --features web --example console_bake

use std::path::PathBuf;

use deos_view::tree::{disclose, Disclosure};
use deos_view::{
    console_bind_values, console_card, console_slot_seeds, demo_console, render_card_document,
    render_html,
};

fn main() {
    // ── 1. The fixture-shaped model, cap-scoped to the demo subject ──────────────
    let all = demo_console();
    let model = all.scoped_to(deos_view::console::DEMO_SUBJECT);

    // ── 2. The card + its bind snapshot (pre-order, the BindValues contract) ─────
    let card = console_card(&model);
    let binds = console_bind_values(&model);

    // ── 3. Two disclosure projections of the ONE card ────────────────────────────
    let simple = disclose(&card, Disclosure::Simple);
    let adept = disclose(&card, Disclosure::Adept);
    let html_simple = render_card_document("My Dregg Computer", &simple, &binds);
    let html_adept = render_card_document("My Dregg Computer — adept", &adept, &binds);

    let dist = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/web-out/dist");
    std::fs::create_dir_all(&dist).expect("create dist dir");
    let p_simple = dist.join("dregg-computer.html");
    let p_adept = dist.join("dregg-computer-adept.html");
    std::fs::write(&p_simple, &html_simple).expect("write dregg-computer.html");
    std::fs::write(&p_adept, &html_adept).expect("write dregg-computer-adept.html");

    // ── 4. PROVE the projection (the bake is a proof, not just a file) ────────────

    // CAP-SCOPING: nothing of the other tenant survives onto the glass.
    assert!(
        !html_simple.contains("other-srv") && !html_simple.contains("other-bot"),
        "a foreign tenant's resources never reach the card"
    );

    // THE HONEST STATUS PILLS: the static bake paints the SNAPSHOT truth (the live
    // pills' case lists reserve 0, so the fallback word is the model state) — the
    // running computer says RUNNING, the sleeping one says SLEEPING.
    let frag = render_html(&simple, &binds);
    assert!(
        frag.contains(">RUNNING</span>") && frag.contains(">SLEEPING</span>"),
        "each computer's status pill paints its snapshot state, never a default"
    );
    // And each status pill carries its live slot + case map for a bound executor.
    assert!(
        frag.contains("data-cases=") && frag.contains("SLEEPING"),
        "status pills carry the value-to-word case map (the live upgrade path)"
    );

    // THE WITNESS STANCE is on the glass, amber for symbolic (never green-washed).
    assert!(
        frag.contains("FULL · PROOF-AS-YOU-GO") && frag.contains("SYMBOLIC · VERIFY LATER"),
        "each computer names its witness stance"
    );

    // THE BUDGET GAUGES: one per computer + one per hermes; and the slot-seed plan
    // covers the whole live surface (balance + 2 per vat + 3 per hermes) so a bound
    // executor seeded from it drives every gauge, live pill, and bind on this page.
    assert_eq!(
        console_slot_seeds(&model).len(),
        1 + 2 * model.computers.len() + 3 * model.hermeses.len(),
        "the seed plan covers the whole live surface"
    );
    assert_eq!(
        frag.matches("deos-gauge-track").count(),
        model.computers.len() + model.hermeses.len(),
        "one budget gauge per computer and per hermes"
    );
    assert!(
        frag.contains("settled 1,440 / 5,000 · headroom 3,560"),
        "the static bake carries the honest meter numbers beside the live gauge"
    );

    // THE LIVE-BOUND RECEIPTS COUNT: the hermes' Bind span carries its slot and paints
    // the snapshot value (5 sealed receipts).
    assert!(
        frag.contains("receipts: 5"),
        "the hermes receipts bind paints the snapshot count"
    );

    // THE CAP TEETH: a running computer's `wake` is a DIMMED row (shown, not hidden),
    // and the sleeping computer's `wake` is a real button carrying the vat.wake turn.
    assert!(
        frag.contains("deos-disabled") && frag.contains("data-turn=\"vat.wake\""),
        "cap teeth render dimmed; granted verbs carry their turn payloads"
    );
    assert!(
        frag.contains("data-turn=\"vat.fork\"")
            && frag.contains("data-turn=\"vat.explore\"")
            && frag.contains("data-turn=\"vat.verify\""),
        "fork / explore / verify affordances ride the card"
    );

    // THE MANDATE shows CAN and CANNOT both — the refused edge is on the glass.
    assert!(
        frag.contains("invoke:run_tests") && frag.contains("spawn:sub-agents"),
        "the mandate paints granted AND refused verbs"
    );
    assert!(
        frag.contains(">refused</span>"),
        "a refused action rides the receipt trail as a red row"
    );

    // THE VERIFY-ANYTHING PANEL: an input whose submit fires the console verify turn.
    assert!(
        frag.contains("data-turn=\"console.verify\"") && frag.contains("data-arg-from="),
        "the verify-anything input is wired (input to verified turn)"
    );

    // PROGRESSIVE DISCLOSURE: the full cell hex is adept-only; the bind snapshot is
    // valid for both projections (the adept detail carries no Bind).
    let full_id = &model.computers[0].cell_id;
    assert!(
        !html_simple.contains(full_id.as_str()),
        "simple projection hides the raw cell hex"
    );
    assert!(
        html_adept.contains(full_id.as_str()),
        "adept projection shows the bones"
    );
    assert!(
        html_simple.contains("$DREGG 9,968"),
        "the balance bind paints amount-grouped in the simple projection"
    );
    assert!(
        html_adept.contains("$DREGG 9,968"),
        "…and identically in the adept projection (same bind cursor)"
    );

    eprintln!("My Dregg Computer console baked (gpui-free, portable IR):");
    eprintln!("  simple projection : {}", p_simple.display());
    eprintln!("  adept projection  : {}", p_adept.display());
    eprintln!();
    eprintln!("Open either file directly in a browser. The gallery (web_render_card's");
    eprintln!("index.html in the same dist/) tiles it as 'My Dregg Computer'. The SAME");
    eprintln!("ViewNode tree renders native via render::AppletView; seed a live executor");
    eprintln!("from console_slot_seeds() and the gauges/pills/binds go live.");
}
