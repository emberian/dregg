//! THE WEB PROJECTION, BY BAKING: the SAME deos-js card view-tree that the native
//! `renders_applet_view_to_pixels` test paints to gpui pixels renders — gpui-FREE — to a
//! browser-loadable `.html`. Same DATA, two renderers ⇒ the card is renderer-INDEPENDENT.
//!
//! This mirrors the native render proof, but through the WEB renderer:
//!
//!   1. Take the EXACT JSON the SpiderMonkey engine produces for the counter card
//!      (`deos.ui.vstack(text, bind, button)`, the same shape the bridge extracts) and
//!      parse it with the SAME `parse_view_tree` the native path uses → one `ViewNode`.
//!   2. Render that tree to HTML at the bound value 0 (count: 0) → write `counter-0.html`.
//!   3. Render the IDENTICAL tree at the bound value 1 (the value a fired `inc` turn would
//!      leave) → write `counter-1.html`. The two documents DIFFER in exactly the bound
//!      span — the web `bind` re-painted, just as the native `bind` re-reads the ledger.
//!   4. Also bake the inspector-shaped card (a table of cell fields + an affordance row)
//!      → `inspector.html`, exercising every node kind through the web vocabulary.
//!
//! No gpui, no SpiderMonkey: this whole bake compiles + runs in the tiny `web` graph.
//! Open any written `.html` in a browser — the SAME card paints.

use std::path::PathBuf;

use deos_view::{
    parse_view_tree, render_card_document, render_card_live_document,
    render_doccollab_live_document, render_gallery_document, render_html,
    render_inspector_live_document, render_kvstore_live_document, render_tally_live_document,
    render_trustless_cell_document, GalleryCard, TrustlessAttestation,
};

/// The EXACT `JSON.stringify(tree)` shape the SpiderMonkey engine produces for the
/// counter card the native test drives:
///
/// ```js
/// var b = deos.ui.bind(function(){ return app.get(0); });
/// b.props.slot = 0; b.props.label = "count: ";
/// deos.ui.vstack(deos.ui.text("Counter applet"), b, deos.ui.button("+1","inc",1))
/// ```
///
/// `deos.ui.button` emits `props.onClick = { turn, arg }`; `text` emits `props.text`; the
/// tagged `bind` emits `props.slot` + `props.label`. This is byte-for-byte the engine
/// output the bridge hands the parser — we render the SAME serialized tree on the web.
const COUNTER_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Counter applet" } },
    { "kind": "bind", "props": { "slot": 0, "label": "count: " } },
    { "kind": "button", "props": { "label": "+1", "onClick": { "turn": "inc", "arg": 1 } } }
  ]
}"#;

/// THE REFLECTIVE-INSPECTOR CARD's view-tree — byte-for-byte the shape
/// `wasm/src/bindings_card.rs`'s `InspectorWorld::view_tree_json` generates from a focused
/// cell's REAL moldable faces (`deos_reflect::ReflectedCell::raw_fields` + `AffordanceSurface`),
/// for the default-seeded cell (`state[0]=7`, `state[1]=42`, `state[2]=100`). It is the
/// substance-agnostic core of the native `deos_js::inspector_card::inspector_view_for`, so this
/// is the SAME view-tree the cockpit inspector paints — fed to the WEB renderer to prove the
/// reflective surface is renderer-independent. A titled column with:
///   - a "Cell State" section: a live `Bind` row per revealed scalar slot (`state[0..2]`,
///     re-read off the ledger so a fired affordance updates the row) + a labeled `Text` per
///     structural substance (balance, nonce, id, caps, lifecycle, …);
///   - an "Affordances" section: a cap-gated `Button` per fireable affordance
///     (`tick`→state[0], `add`→state[1], `score`→state[2]).
/// (The structural-row VALUES below — balance/nonce/id — are the live in-tab cell's, re-read
/// from the wasm `InspectorWorld` after boot; the static bake here is the first paint.)
const INSPECTOR_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Inspector" } },
    { "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Cell State" } },
        { "kind": "text", "props": { "text": "balance: 1000000" } },
        { "kind": "text", "props": { "text": "nonce: 3" } },
        { "kind": "text", "props": { "text": "capabilities: 0" } },
        { "kind": "text", "props": { "text": "has_delegate: false" } },
        { "kind": "text", "props": { "text": "has_program: false" } },
        { "kind": "text", "props": { "text": "lifecycle: live" } },
        { "kind": "bind", "props": { "slot": 0, "label": "state[0]: " } },
        { "kind": "bind", "props": { "slot": 1, "label": "state[1]: " } },
        { "kind": "bind", "props": { "slot": 2, "label": "state[2]: " } }
    ] },
    { "kind": "vstack", "props": {}, "children": [
        { "kind": "text", "props": { "text": "Affordances" } },
        { "kind": "button", "props": { "label": "tick", "on_click": { "turn": "tick", "arg": 1 } } },
        { "kind": "button", "props": { "label": "add", "on_click": { "turn": "add", "arg": 1 } } },
        { "kind": "button", "props": { "label": "score", "on_click": { "turn": "score", "arg": 1 } } }
    ] }
  ]
}"#;

/// THE TALLY-BOARD CARD's view-tree — byte-for-byte the shape `wasm/src/bindings_card.rs`'s
/// `TallyWorld::view_tree_json` generates: a titled column over a `table` of `row`s, one per
/// named tally (apples/oranges/pears = slots 0/1/2). Each `row` carries a `text` label, a live
/// `bind` of its slot, and `+1`/`−1` affordance `button`s (`{turn:inc|dec, arg:slot}`). It
/// exercises the view-tree's LAYOUT nodes (`Row`/`Table`) and a multi-affordance row — surfaces
/// neither the counter nor the inspector touched — proving the FULL ViewNode vocabulary is
/// renderer-independent (the SAME tree the cockpit walks into gpui widgets, fed to the WEB
/// renderer). The static seeds below (3/1/4) are the first paint; the in-tab `TallyWorld`
/// re-reads the live values after boot.
const TALLY_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Tally board" } },
    { "kind": "table", "props": {}, "children": [
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "apples: " } },
            { "kind": "bind", "props": { "slot": 0, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 0 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 0 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "oranges: " } },
            { "kind": "bind", "props": { "slot": 1, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 1 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 1 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "pears: " } },
            { "kind": "bind", "props": { "slot": 2, "label": "" } },
            { "kind": "button", "props": { "label": "+1", "on_click": { "turn": "inc", "arg": 2 } } },
            { "kind": "button", "props": { "label": "−1", "on_click": { "turn": "dec", "arg": 2 } } }
        ] }
    ] }
  ]
}"#;

/// THE KV-STORE SERVICE-CELL CARD's view-tree — byte-for-byte the shape
/// `wasm/src/bindings_card.rs`'s `KvStoreWorld::view_tree_json` generates: a titled column with
/// a version `row` and a `table` of register rows (slots 1–4), each `row(text label, bind slot,
/// button "put", button "del")`. The `put`/`del` buttons carry `{turn: put|delete, arg: slot}`.
/// Unlike the other cards (which write a cell's OWN slots through bare `SetField`), the KV-store
/// is a SERVICE CELL: clicking `put`/`del` ROUTES the call through the store's published
/// `InterfaceDescriptor` (the verified DFA) before it desugars to the version-bump + register
/// `SetField`s — proving a published-interface service surface renders + drives in the web
/// renderer. The static seeds below (version 4; regs 10/20/30/40) are the first paint; the
/// in-tab `KvStoreWorld` re-reads the live values after boot.
const KVSTORE_CARD_JSON: &str = r#"{
  "kind": "vstack",
  "props": {},
  "children": [
    { "kind": "text", "props": { "text": "Key-Value Store — service cell" } },
    { "kind": "text", "props": { "text": "a published interface (put · delete · get) routed through the verified DFA" } },
    { "kind": "row", "props": {}, "children": [
        { "kind": "text", "props": { "text": "store version: " } },
        { "kind": "bind", "props": { "slot": 0, "label": "" } }
    ] },
    { "kind": "table", "props": {}, "children": [
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "reg 1: " } },
            { "kind": "bind", "props": { "slot": 1, "label": "" } },
            { "kind": "button", "props": { "label": "put", "on_click": { "turn": "put", "arg": 1 } } },
            { "kind": "button", "props": { "label": "del", "on_click": { "turn": "delete", "arg": 1 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "reg 2: " } },
            { "kind": "bind", "props": { "slot": 2, "label": "" } },
            { "kind": "button", "props": { "label": "put", "on_click": { "turn": "put", "arg": 2 } } },
            { "kind": "button", "props": { "label": "del", "on_click": { "turn": "delete", "arg": 2 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "reg 3: " } },
            { "kind": "bind", "props": { "slot": 3, "label": "" } },
            { "kind": "button", "props": { "label": "put", "on_click": { "turn": "put", "arg": 3 } } },
            { "kind": "button", "props": { "label": "del", "on_click": { "turn": "delete", "arg": 3 } } }
        ] },
        { "kind": "row", "props": {}, "children": [
            { "kind": "text", "props": { "text": "reg 4: " } },
            { "kind": "bind", "props": { "slot": 4, "label": "" } },
            { "kind": "button", "props": { "label": "put", "on_click": { "turn": "put", "arg": 4 } } },
            { "kind": "button", "props": { "label": "del", "on_click": { "turn": "delete", "arg": 4 } } }
        ] }
    ] }
  ]
}"#;

fn out_dir() -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/web-out");
    std::fs::create_dir_all(&dir).expect("create web-out dir");
    dir
}

fn main() {
    let out = out_dir();

    // ── 1. Parse the EXACT engine JSON with the SAME parser the native renderer uses ──
    let counter = parse_view_tree(COUNTER_CARD_JSON).expect("parse the counter card view-tree");
    let inspector =
        parse_view_tree(INSPECTOR_CARD_JSON).expect("parse the inspector card view-tree");

    // ── 2. Render the counter at the bound value 0 (the un-driven start) ─────────────
    let html0 = render_card_document("deos counter card", &counter, &[0]);
    let p0 = out.join("counter-0.html");
    std::fs::write(&p0, &html0).expect("write counter-0.html");

    // ── 3. Render the IDENTICAL tree at the bound value 1 (post-`inc`) ───────────────
    // This is the web `bind` re-paint: same view-tree, advanced model snapshot.
    let html1 = render_card_document("deos counter card", &counter, &[1]);
    let p1 = out.join("counter-1.html");
    std::fs::write(&p1, &html1).expect("write counter-1.html");

    // ── 4. Bake the reflective inspector card (the three bound slots: 7, 42, 100) ─────
    // bind_values are in tree-walk order: the three `state[i]` Bind rows → [7, 42, 100].
    let html_insp = render_card_document("deos inspector card", &inspector, &[7, 42, 100]);
    let pi = out.join("inspector.html");
    std::fs::write(&pi, &html_insp).expect("write inspector.html");

    // ── PROVE the reflective projection: the inspector's faces SURVIVED the web render ─
    // The RawFields face's structural rows + the live `Bind` rows + the cap-gated affordance
    // `Button`s all paint, carrying their real `{slot}` / `{turn, arg}` contracts.
    let frag_insp = render_html(&inspector, &[7, 42, 100]);
    assert!(
        frag_insp.contains("Inspector")
            && frag_insp.contains("Cell State")
            && frag_insp.contains("Affordances"),
        "the inspector's section titles paint (RawFields + Affordances faces)"
    );
    assert!(
        frag_insp.contains("state[0]: 7")
            && frag_insp.contains("state[1]: 42")
            && frag_insp.contains("state[2]: 100"),
        "the three live Bind rows paint their seeded slot values"
    );
    assert!(
        frag_insp.contains("data-slot=\"0\"")
            && frag_insp.contains("data-slot=\"1\"")
            && frag_insp.contains("data-slot=\"2\""),
        "each Bind row carries its own model slot (the multi-field signal sources)"
    );
    assert!(
        frag_insp.contains("balance: 1000000") && frag_insp.contains("lifecycle: live"),
        "the structural substances (balance, lifecycle) render as static rows"
    );
    assert!(
        frag_insp.contains("data-turn=\"tick\"")
            && frag_insp.contains("data-turn=\"add\"")
            && frag_insp.contains("data-turn=\"score\""),
        "each cap-gated affordance becomes a Button carrying its `{{turn}}` payload"
    );

    // ── PROVE the projection, not merely write it ────────────────────────────────────
    // The bound value PAINTS (count: 0 vs count: 1) and the affordance payload SURVIVED
    // the web projection (the button carries the engine's `{turn:"inc", arg:1}`).
    let frag0 = render_html(&counter, &[0]);
    let frag1 = render_html(&counter, &[1]);
    assert!(
        frag0.contains("count: 0"),
        "frame 0 paints the bound value 0"
    );
    assert!(
        frag1.contains("count: 1"),
        "frame 1 paints the bound value 1"
    );
    assert_ne!(
        frag0, frag1,
        "the two frames DIFFER — the bound value re-painted"
    );
    assert!(
        frag0.contains("data-turn=\"inc\"") && frag0.contains("data-arg=\"1\""),
        "the button carries the REAL affordance payload {{turn:inc, arg:1}} into the DOM"
    );
    assert!(
        frag0.contains("data-slot=\"0\""),
        "the bind carries its model slot (the signal source a browser re-read refreshes)"
    );

    // ── 5. Bake the LIVE counter page — the served, browser-native deos ──────────────
    // This page loads the playground wasm bundle (`./pkg/dregg_wasm.js`), mints an in-tab
    // `CardWorld` (the wasm analog of the native `Applet`), binds it to `window.__deosCard`,
    // and every `+1` click fires a REAL cap-gated verified turn over that embedded executor
    // — the bound value updating from the COMMITTED ledger, with a live receipt count. It
    // is baked into a `dist/` dir; the `pkg/` (wasm bundle) is copied in beside it so the
    // page is self-contained when served (`python3 -m http.server` from `dist/`).
    let dist = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/web-out/dist");
    std::fs::create_dir_all(&dist).expect("create dist dir");
    let live = render_card_live_document(
        "deos counter card — live",
        &counter,
        /*slot*/ 0,
        /*initial*/ 0,
        "./pkg/dregg_wasm.js",
    );
    let plive = dist.join("counter.html");
    std::fs::write(&plive, &live).expect("write the live counter.html");

    // ── PROVE the live page is wired (not merely written) ────────────────────────────
    assert!(
        live.contains("./pkg/dregg_wasm.js") && live.contains("import init, { CardWorld }"),
        "the live page imports the wasm bundle's `init` + `CardWorld`"
    );
    assert!(
        live.contains("new CardWorld(0, 0n)") && live.contains("window.__deosCard = card"),
        "the live page mints the in-tab verified executor and binds it for the affordance wire"
    );
    assert!(
        live.contains("card.fire(turn, arg)"),
        "the affordance wire fires the click as a real verified turn into the in-tab executor"
    );
    assert!(
        live.contains("data-turn=\"inc\"") && live.contains("data-slot=\"0\""),
        "the SAME card markup carries the affordance + bind contract the wire drives"
    );

    // ── 6. Bake the LIVE REFLECTIVE-INSPECTOR page — a cockpit surface, browser-native ──
    // The SAME gpui-free web renderer paints the inspector card's view-tree (Cell State binds
    // + structural rows + Affordance buttons), the bootstrap mints an in-tab `InspectorWorld`
    // (the wasm analog of the native inspector over a live World) seeded to [7, 42, 100], binds
    // `window.__deosCard`, and re-paints each bound row from the committed ledger. Clicking an
    // affordance (`tick`/`add`/`score`) fires a REAL cap-gated verified turn over that executor
    // and the bound field re-paints — a reflective cockpit surface running in a TAB.
    let live_insp = render_inspector_live_document(
        "deos reflective-inspector card — live",
        &inspector,
        /*bind_values (tree-walk order)*/ &[7, 42, 100],
        /*seeds*/ &[7, 42, 100],
        "./pkg/dregg_wasm.js",
    );
    let plive_insp = dist.join("inspector.html");
    std::fs::write(&plive_insp, &live_insp).expect("write the live inspector.html");

    // ── PROVE the live inspector page is wired (not merely written) ───────────────────
    assert!(
        live_insp.contains("./pkg/dregg_wasm.js")
            && live_insp.contains("import init, { InspectorWorld }"),
        "the live inspector page imports the wasm bundle's `init` + `InspectorWorld`"
    );
    assert!(
        live_insp.contains("new InspectorWorld([7n, 42n, 100n])")
            && live_insp.contains("window.__deosCard = card"),
        "the live inspector page mints the in-tab reflective executor seeded to the bound slots"
    );
    assert!(
        live_insp.contains("card.read(slot)"),
        "the live inspector re-paints each bound row from ITS slot off the committed ledger"
    );
    assert!(
        live_insp.contains("card.fire(turn, arg)"),
        "the affordance wire fires a click as a real verified turn into the in-tab executor"
    );
    assert!(
        live_insp.contains("data-slot=\"0\"")
            && live_insp.contains("data-slot=\"1\"")
            && live_insp.contains("data-slot=\"2\"")
            && live_insp.contains("data-turn=\"tick\""),
        "the SAME inspector markup carries the multi-slot bind + affordance contract the wire drives"
    );

    // ── 6b. Bake the LIVE TALLY-BOARD page — the FULL ViewNode vocabulary, browser-native ──
    // The SAME gpui-free web renderer paints the board's view-tree (a `Table` of `Row`s, each a
    // named tally with its live `Bind` value + `+1`/`−1` `Button`s — the LAYOUT nodes the
    // counter/inspector never exercised). The bootstrap mints an in-tab `TallyWorld` seeded to
    // [3, 1, 4], binds `window.__deosCard`, and re-paints each bound row from the committed
    // ledger. Clicking a `+1`/`−1` fires a REAL cap-gated verified turn over that executor (its
    // `data-arg` is the tally's SLOT, `data-turn` the direction) and that one row re-paints.
    let tally = parse_view_tree(TALLY_CARD_JSON).expect("parse the tally card view-tree");
    let live_tally = render_tally_live_document(
        "deos tally-board card — live",
        &tally,
        /*bind_values (tree-walk order)*/ &[3, 1, 4],
        /*seeds*/ &[3, 1, 4],
        "./pkg/dregg_wasm.js",
    );
    let plive_tally = dist.join("tally.html");
    std::fs::write(&plive_tally, &live_tally).expect("write the live tally.html");

    // ── PROVE the tally board exercises the LAYOUT vocabulary + is wired (not merely written) ─
    let frag_tally = render_html(&tally, &[3, 1, 4]);
    assert!(
        frag_tally.contains("deos-table") && frag_tally.matches("deos-row").count() == 3,
        "the board renders a Table of three Rows (the layout vocabulary)"
    );
    assert!(
        frag_tally.contains("apples: ")
            && frag_tally.contains("oranges: ")
            && frag_tally.contains("pears: "),
        "each Row paints its named tally's label"
    );
    assert!(
        frag_tally.contains("data-slot=\"0\" data-fmt=\"raw\" data-label=\"\">3</span>")
            && frag_tally.contains("data-slot=\"1\" data-fmt=\"raw\" data-label=\"\">1</span>")
            && frag_tally.contains("data-slot=\"2\" data-fmt=\"raw\" data-label=\"\">4</span>"),
        "each Row's Bind paints its slot's seeded value (3 / 1 / 4)"
    );
    assert!(
        frag_tally.matches("data-turn=\"inc\"").count() == 3
            && frag_tally.matches("data-turn=\"dec\"").count() == 3,
        "each Row carries BOTH affordances (+1 inc / −1 dec) — a multi-affordance row"
    );
    assert!(
        frag_tally.contains("data-arg=\"0\"")
            && frag_tally.contains("data-arg=\"1\"")
            && frag_tally.contains("data-arg=\"2\""),
        "each affordance carries its tally's SLOT index as `data-arg`"
    );
    assert!(
        live_tally.contains("import init, { TallyWorld }")
            && live_tally.contains("new TallyWorld([3n, 1n, 4n])")
            && live_tally.contains("card.read(slot)"),
        "the live tally page imports + mints the in-tab executor and re-paints each row off its slot"
    );

    // ── 6c. Bake the LIVE KV-STORE page — a SERVICE CELL invoked client-side ─────────────
    // The SAME gpui-free web renderer paints the store's view-tree (a version row + a `Table`
    // of register rows with `put`/`del` buttons). The bootstrap mints an in-tab `KvStoreWorld`
    // seeded to [10, 20, 30, 40], binds `window.__deosCard`, and re-paints each bound row from
    // the committed ledger. Clicking `put`/`del` ROUTES the call through the store's published
    // `InterfaceDescriptor` (the verified DFA) and fires a REAL cap-gated verified turn against
    // the store cell, the monotone version bumping. The status strip additionally exercises the
    // verified `Monotonic`-version guarantee (a refused rollback) and the `Serviced` `get` seam.
    let kvstore = parse_view_tree(KVSTORE_CARD_JSON).expect("parse the kvstore card view-tree");
    let live_kv = render_kvstore_live_document(
        "deos KV-store service cell — live",
        &kvstore,
        /*bind_values (tree-walk order: version, reg1..reg4)*/ &[4, 10, 20, 30, 40],
        /*seeds (reg1..reg4)*/ &[10, 20, 30, 40],
        "./pkg/dregg_wasm.js",
    );
    let plive_kv = dist.join("kvstore.html");
    std::fs::write(&plive_kv, &live_kv).expect("write the live kvstore.html");

    // ── PROVE the kvstore service-cell card renders the published-interface surface + is wired ─
    let frag_kv = render_html(&kvstore, &[4, 10, 20, 30, 40]);
    assert!(
        frag_kv.contains("Key-Value Store — service cell") && frag_kv.contains("store version: "),
        "the store card paints its title + the version row"
    );
    assert!(
        frag_kv.contains("deos-table") && frag_kv.matches("deos-row").count() == 5,
        "the store renders a version Row + a Table of four register Rows"
    );
    assert!(
        frag_kv.contains("data-slot=\"0\" data-fmt=\"raw\" data-label=\"\">4</span>")
            && frag_kv.contains("data-slot=\"1\" data-fmt=\"raw\" data-label=\"\">10</span>")
            && frag_kv.contains("data-slot=\"4\" data-fmt=\"raw\" data-label=\"\">40</span>"),
        "the version + register Binds paint their seeded values (version 4; regs 10/40)"
    );
    assert!(
        frag_kv.matches("data-turn=\"put\"").count() == 4
            && frag_kv.matches("data-turn=\"delete\"").count() == 4,
        "each register Row carries BOTH method affordances (put / del)"
    );
    assert!(
        live_kv.contains("import init, { KvStoreWorld }")
            && live_kv.contains("new KvStoreWorld([10n, 20n, 30n, 40n])")
            && live_kv.contains("card.read(slot)")
            && live_kv.contains("c.version()"),
        "the live store page imports + mints the in-tab service cell and re-paints each row + version"
    );

    // ── 6d. Bake the LIVE DOCUMENT-COLLABORATION page — Pijul/conflicts-as-objects, node-less ──
    // The in-tab `DocCollabWorld` (`wasm/src/bindings_doc.rs`) drives the WHOLE flow: a doc-cell
    // carries a base document published to its umem-heap (the fork); clicking `stitch` diverges
    // two authors off the shared tail and `merge`s them (the categorical pushout), surfacing a
    // first-class conflict HELD off-heap; the ConflictView renders the two alternatives attributed
    // side-by-side with a resolution `Button` per ready choice; clicking one collapses the conflict
    // and PUBLISHES the merged document to the doc-cell's umem-heap as a REAL verified turn (the
    // boundary `heap_root` moves, a receipt is left). The tree re-renders WHOLESALE after every
    // affordance (the SHAPE changes), so the page sets `card.viewHtml()` as the container innerHTML
    // — the SAME gpui-free web renderer, driven from the wasm side.
    let live_doc =
        render_doccollab_live_document("deos document collaboration — live", "./pkg/dregg_wasm.js");
    let plive_doc = dist.join("doccollab.html");
    std::fs::write(&plive_doc, &live_doc).expect("write the live doccollab.html");

    // ── PROVE the doc-collab page is wired (not merely written) ───────────────────────
    assert!(
        live_doc.contains("./pkg/dregg_wasm.js")
            && live_doc.contains("import init, { DocCollabWorld }"),
        "the live doc-collab page imports the wasm bundle's `init` + `DocCollabWorld`"
    );
    assert!(
        live_doc.contains("new DocCollabWorld()") && live_doc.contains("window.__deosDoc = card"),
        "the live doc-collab page mints the in-tab doc-cell verified executor"
    );
    assert!(
        live_doc.contains("window.__deosDoc.viewHtml()") && live_doc.contains("root.innerHTML"),
        "the surface re-renders wholesale from the wasm-side web renderer (the ConflictView ⇄ published doc)"
    );
    assert!(
        live_doc.contains(".fire(turn, arg)") && live_doc.contains("deos-doc-root"),
        "a delegated click fires each affordance (stitch / resolve+publish) as a real verified turn"
    );

    // ── 6e. Bake the TRUSTLESS PORTAL page — the dregg content gateway, browser-verified ──
    // The orthogonal axis to the live cards: instead of (or as well as) firing turns in the tab,
    // this page PROVES — in the browser, re-witnessing nothing — that the served card reflects a
    // GENUINE verified cell, not a server's bare claim. The SAME gpui-free renderer bakes the
    // counter card as the served content; above it a trust banner + an attestation readout; a
    // module bootstrap loads the wasm `dregg-lightclient` and runs the REAL recursive-STARK verify.
    // In `InTabDemo` mode the tab folds AND verifies a real k-turn history end-to-end (the
    // produce→serialize→verify round-trip, self-anchored); the `ServerSupplied` arm is the
    // production gateway shape (a node hands over the envelope + the client's config anchor). Until
    // the light client attests, the card is marked the server's unverified claim; on success the
    // page asserts it reflects a light-client-verified cell.
    let trustless = render_trustless_cell_document(
        "deos counter cell — trustlessly served",
        &counter,
        /*bind_values*/ &[0],
        /*openings*/ &[],
        &TrustlessAttestation::InTabDemo { k: 3, step: 7 },
        "./pkg/dregg_wasm.js",
    );
    let plive_trust = dist.join("trustless.html");
    std::fs::write(&plive_trust, &trustless).expect("write the trustless portal page");

    // ── PROVE the trustless portal is wired (not merely written) ──────────────────────
    assert!(
        trustless.contains("./pkg/dregg_wasm.js")
            && trustless.contains("import init, { verify_devnet_history"),
        "the portal imports the wasm light client's verify entry"
    );
    assert!(
        trustless.contains("produce_external_history_envelope(3, 7n)")
            && trustless.contains("genesis_vk_anchor(3, 7n)")
            && trustless.contains("verify_devnet_history(env, anchor)"),
        "the InTabDemo bootstrap folds a real 3-turn history, mints the shape anchor, and verifies"
    );
    assert!(
        trustless.contains("id=\"deos-trust\"")
            && trustless.contains("deos-unverified")
            && trustless.contains("verdict.attested"),
        "the page carries the trust banner, the unverified-by-default card, and the attest gate"
    );
    assert!(
        trustless.contains("count: 0") && trustless.contains("data-turn=\"inc\""),
        "the SAME counter card is the served content (the cell's card, rendered to HTML)"
    );

    // The ServerSupplied arm bakes the production gateway shape: a server-handed envelope JSON
    // + a config anchor, verified tab-side against that config anchor (never read off the proof).
    let trustless_srv = render_trustless_cell_document(
        "deos counter cell — gateway-served",
        &counter,
        &[0],
        &[],
        &TrustlessAttestation::ServerSupplied {
            envelope_json: r#"{"version":1,"vk_fingerprint_hex":"ab","genesis_root":[0],"final_root":[0],"chain_digest":[0],"num_turns":2,"proof_bytes_b64":""}"#,
            config_anchor_hex: &"ab".repeat(32),
        },
        "./pkg/dregg_wasm.js",
    );
    assert!(
        trustless_srv.contains("application/json\" id=\"deos-attestation\"")
            && trustless_srv.contains("const anchor = '")
            && trustless_srv.contains("verify_devnet_history(env, anchor)"),
        "the ServerSupplied arm embeds the envelope island + the config anchor and verifies against it"
    );
    assert!(
        !trustless_srv.contains("</script>\"}"),
        "the embedded envelope JSON cannot break out of its script island (no raw </script>)"
    );

    // ── 7. Bake the GALLERY / card-picker as the served home page (`/` = index.html) ──
    // Without a front door a visitor lands on one card and never finds the others. This is
    // a plain-HTML (no-wasm) landing of clickable tiles, one per live card — the
    // "click around, no comprehension needed" entry that opens each real card page.
    let gallery = render_gallery_document(
        "deos — live cards in a browser",
        &[
            GalleryCard {
                href: "counter.html",
                name: "Counter",
                blurb: "A deos-js counter card. Click +1 and the bound count advances — each \
                        click is a SetField + IncrementNonce verified turn over an in-tab \
                        executor, leaving a receipt.",
            },
            GalleryCard {
                href: "inspector.html",
                name: "Reflective Inspector",
                blurb: "A cockpit surface, in a tab. A focused cell's real moldable faces \
                        (state rows + affordances) render live; clicking tick/add/score fires a \
                        cap-gated verified turn and the bound field re-paints.",
            },
            GalleryCard {
                href: "tally.html",
                name: "Tally Board",
                blurb: "A table of named tallies, each a row with a live count and +1/−1 \
                        buttons. The full ViewNode layout vocabulary (Row + Table + a \
                        multi-affordance row); every click is a verified turn moving one tally.",
            },
            GalleryCard {
                href: "kvstore.html",
                name: "KV-Store (service cell)",
                blurb: "A cell publishing a typed interface (put · delete · get). Clicking \
                        put/del routes the call through the verified DFA before it desugars to \
                        SetField effects — a real verified turn against the store, the monotone \
                        version bumping (a rollback is refused; get is a named OFE seam).",
            },
            GalleryCard {
                href: "trustless.html",
                name: "Trustless Portal",
                blurb: "The dregg content gateway. The same card, served — but the page PROVES, \
                        in your browser and re-witnessing nothing, that it reflects a genuine \
                        verified cell. A light client checks the recursive STARK proof of the \
                        cell's whole finalized history right in the tab; until it attests, the \
                        content is marked the server's unverified claim.",
            },
            GalleryCard {
                href: "doccollab.html",
                name: "Document Collaboration",
                blurb: "Pijul, in a tab. Fork a document, diverge two authors, then stitch — the \
                        categorical pushout surfaces a first-class CONFLICT (both alternatives \
                        attributed side-by-side, held off-heap). Click to resolve and the merged \
                        document publishes to the doc-cell's umem-heap as a real verified turn — \
                        the boundary heap_root moves, a receipt is left.",
            },
            GalleryCard {
                href: "dregg-computer.html",
                name: "My Dregg Computer",
                blurb: "The DreggNet management console as a portable card: your computers \
                        (status + uptime-budget gauge + wake/sleep/fork/explore/verify), your \
                        resident hermeses (receipts + mandate + budget), your $DREGG spend, and \
                        a verify-anything panel. One ViewNode model — native gpui, web, and the \
                        graphideOS phone are just walkers. Bake it with the console_bake example.",
            },
        ],
    );
    let pgallery = dist.join("index.html");
    std::fs::write(&pgallery, &gallery).expect("write the gallery index.html");

    // ── PROVE the gallery is wired (not merely written) ───────────────────────────────
    assert!(
        gallery.contains("href=\"counter.html\"")
            && gallery.contains("href=\"inspector.html\"")
            && gallery.contains("href=\"tally.html\"")
            && gallery.contains("href=\"kvstore.html\"")
            && gallery.contains("href=\"trustless.html\"")
            && gallery.contains("href=\"doccollab.html\"")
            && gallery.contains("href=\"dregg-computer.html\""),
        "the gallery links to ALL the card pages incl. the trustless portal + the console (the card-picker)"
    );
    assert!(
        gallery.contains("Counter")
            && gallery.contains("Reflective Inspector")
            && gallery.contains("Tally Board")
            && gallery.contains("KV-Store (service cell)")
            && gallery.contains("Document Collaboration")
            && gallery.contains("My Dregg Computer"),
        "the gallery names all the cards"
    );

    eprintln!("deos-view web projection baked (gpui-free):");
    eprintln!("  counter @ count=0    : {}", p0.display());
    eprintln!("  counter @ count=1    : {}", p1.display());
    eprintln!("  inspector card       : {}", pi.display());
    eprintln!("  LIVE gallery (home)  : {}", pgallery.display());
    eprintln!("  LIVE counter page    : {}", plive.display());
    eprintln!("  LIVE inspector page  : {}", plive_insp.display());
    eprintln!("  LIVE tally page      : {}", plive_tally.display());
    eprintln!("  LIVE kvstore page    : {}", plive_kv.display());
    eprintln!("  LIVE doc-collab page : {}", plive_doc.display());
    eprintln!("  TRUSTLESS portal     : {}", plive_trust.display());
    eprintln!();
    eprintln!("To serve the LIVE deos (a card firing real cap-gated verified turns in a TAB):");
    eprintln!("  1. wasm-pack build wasm --target web --out-dir pkg --release");
    eprintln!("  2. cp -R ../wasm/pkg {}/pkg", dist.display());
    eprintln!(
        "  3. (cd {} && python3 -m http.server 8000)  # open http://localhost:8000 (the gallery)",
        dist.display()
    );
    eprintln!("     The gallery links to /counter.html and /inspector.html (the LIVE cards).");
    eprintln!(
        "Open the static .html files directly; the LIVE pages must be SERVED (module + .wasm fetch)."
    );
}
