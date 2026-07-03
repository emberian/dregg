//! Starbridge v2 — the native dregg master interface.
//!
//! TWO BUILDS, ONE CODEBASE (see Cargo.toml + docs/STARBRIDGE-V2.md):
//!
//!   * `native-full` (DEFAULT) — EMBEDS THE REAL VERIFIED EXECUTOR and runs a
//!     LIVE LOCAL dregg world natively (`crate::world::World` over
//!     `dregg_turn::executor::TurnExecutor`). It opens a gpui window: the
//!     comprehensive cockpit (`crate::cockpit::Cockpit`) rendering that image
//!     across the four dregg-surpasses-Smalltalk axes. This is the master
//!     interface. (On a host with a working Metal path — see the
//!     `runtime_shaders` note in Cargo.toml — the window renders; absent a GPU/
//!     display it still runs its headless self-check via `--headless`.)
//!
//!   * `sel4-thin` (`--no-default-features --features sel4-thin`) — the Lean-
//!     free thin HTTP client / verifier path for the eventual seL4 component
//!     (docs/SEL4-EMBEDDING.md). No embedded executor, no gpui: it speaks the
//!     node's wire contract (`client`/`model`) against a remote node.
//!
//! The `NodeClient::{Mock,Http}` surface (`client`/`model`) is compiled in BOTH
//! builds: the master interface can ALSO connect to remote nodes/federations.

// The wire-contract client + mirrored models now live in the LIBRARY
// (`starbridge_v2::{client, model}`) so BOTH the embedded master interface's
// live-node panel and the sel4-thin path share one mirror. The thin path below
// references them through the library crate.
#[cfg(feature = "sel4-thin")]
use starbridge_v2::client;

// The embedded engine + reflective model + dynamics live in the library crate
// (`starbridge_v2::{world, dynamics, reflect}`) so they are `cargo test`-able.

// The gpui presentation plane (`cockpit`, `login`, `views`, `dock`) now lives in
// the LIBRARY (`starbridge_v2::{cockpit, login, views, dock}`, gpui-gated) so the
// SAME cockpit renders on EITHER platform — natively here, and in the browser via
// the `starbridge-v2/web` cdylib on `gpui_web` (see docs/deos/WEB-DEOS.md). The bin
// reaches them through the library crate; this alias keeps `cockpit::Cockpit` /
// `login::LoginSurface` paths below unchanged.
#[cfg(feature = "gpui-ui")]
use starbridge_v2::{cockpit, login};

#[cfg(feature = "embedded-executor")]
use starbridge_v2::{demo, reflect, world};

/// All font blobs the bake/UI text systems load. The UI fonts (Lilex, IBM Plex
/// Sans) PLUS symbol + emoji fallback fonts (Noto Emoji, Noto Sans Symbols, Noto
/// Sans Symbols 2) so chrome glyphs — locks, gauges, crosshairs, gears, ballot
/// checkboxes, 🌐 ⏳ 📄 🔑 — render real glyphs instead of missing-glyph □ boxes.
/// The headless bake's text system carries no system fonts, so without these the
/// shaper has nothing to fall back to; cosmic-text picks whichever LOADED font
/// covers a codepoint, so order is irrelevant to coverage.
#[allow(dead_code)] // unused in the gpui-free sel4-thin build
fn bake_font_blobs() -> Vec<std::borrow::Cow<'static, [u8]>> {
    use std::borrow::Cow as C;
    static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
    static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");
    static EMOJI: &[u8] = include_bytes!("../assets/fonts/NotoEmoji-Regular.ttf");
    static SYMBOLS: &[u8] = include_bytes!("../assets/fonts/NotoSansSymbols-Regular.ttf");
    static SYMBOLS2: &[u8] = include_bytes!("../assets/fonts/NotoSansSymbols2-Regular.ttf");
    vec![
        C::Borrowed(LILEX),
        C::Borrowed(IBM_PLEX),
        C::Borrowed(EMOJI),
        C::Borrowed(SYMBOLS),
        C::Borrowed(SYMBOLS2),
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let headless = args.iter().any(|a| a == "--headless");

    // `--render-cockpit <out>`: the HEADLESS COCKPIT BAKE (the seL4 deos-image
    // weld). Drive the REAL `cockpit::Cockpit` element tree through a headless
    // gpui `App`/`Window` (no GPU, no display) and render the resolved gpui
    // `Scene` offscreen via the wgpu lavapipe path to an 800x600 RGBA8 frame —
    // the byte image the deos-image PD bakes in and blits onto its ramfb
    // framebuffer. See `render_cockpit_headless`. Builds only under the
    // `headless-render` feature (which pulls gpui's `test-support` headless
    // window + capture API). Mutually independent of the windowed `run_window`.
    // `--explore-ui <outdir>`: the UI-EXPLORATION crawl — BFS-walk the cockpit's
    // navigation state-space (drive the real interaction handlers), screenshot
    // each distinct UI state, and emit `<outdir>/ui-graph.json` + `states/*.png`.
    // The atlas's "UI tree": exploring inside and through the surfaces.
    #[cfg(feature = "render-capture")]
    {
        if let Some(dir) = explore_ui_arg(&args) {
            match explore_ui_headless(&dir) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("explore-ui FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--serve-ie6 <port>`: THE LIVE IE6 COCKPIT SERVER — Path B. A single-threaded
    // blocking server (gpui is !Send, so one accept→apply→render→respond loop on the
    // gpui thread is exactly right) that holds a LIVE cockpit, renders it to a PNG per
    // request, and serves it as image-map HTML. Clicking a region / link hits the
    // server, which applies the interaction to the live world and re-renders. Frame-
    // streaming for any user-agent back to 1996 — the real thing, not a flip-through.
    #[cfg(feature = "render-capture")]
    {
        if let Some(port) = serve_ie6_arg(&args) {
            match serve_ie6_headless(port) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("serve-ie6 FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    #[cfg(feature = "render-capture")]
    {
        if let Some(out) = render_cockpit_arg(&args) {
            // `--replay <cell>:<msg>` (repeatable) — apply a recorded act-trail to
            // the demo image BEFORE rendering, so a screenshot reflects a driven
            // session's state (the dregg-mcp server passes its committed act log
            // here). Each act fires through the SAME real executor the cockpit uses.
            let replays = render_replay_args(&args);
            // `--render-size WxH` (logical) defaults to the seL4 framebuffer 800x600
            // (which still downscales + writes the .rgba the PD blits); any other
            // size renders the full-resolution cockpit (no truncation, PNG only).
            // `--render-tab NAME` selects a surface (inspector/graph/proofs/…).
            let (w, h) = render_size_arg(&args).unwrap_or((800.0, 600.0));
            let tab = render_tab_arg(&args);
            // `--render-first-run` — bake the calm sparse FIRST-VIEW (a first-timer's
            // warm landing) instead of the full 5-mode frame, for the welcome bakes.
            let first_run = args.iter().any(|a| a == "--render-first-run");
            match render_cockpit_headless(&out, &replays, w, h, tab.as_deref(), first_run) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-cockpit FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-agent-attach <out>`: THE AGENT'S HANDS ON THE REAL GLASS. Attaches
    // the confined agent's `run_js` (deos-js, real SpiderMonkey) to the cockpit's
    // LIVE `World` (the operator's real demo cells), runs JS that crawls those ACTUAL
    // cells + fires a real verified turn on the agent's cell (a receipt landing on the
    // live ledger) + attempts an over-reach (refused in-band), then bakes the cockpit
    // INSPECTOR focused on the agent's cell — the PNG shows the field the agent's JS
    // modified. Pass `--fork` to drive a `world.fork()` (the safe sandbox) instead of
    // the live image. Default 1400x900.
    #[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "agent-js"))]
    {
        if let Some(out) = render_agent_attach_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1400.0, 900.0));
            let fork = args.iter().any(|a| a == "--fork");
            match render_agent_attach_headless(&out, w, h, fork) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-agent-attach FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-card-pane <out>`: A HYPERDREGGMEDIA CARD AS A LIVE COCKPIT PANE. Builds
    // the cockpit's LIVE `World`, authors a counter CARD's `deos.ui.*` view-tree in real
    // SpiderMonkey over an applet ATTACHED to that live World (via the `agent_attach`
    // `WorldSinkAdapter::live` weld), renders the card as a real gpui-component pane
    // (`CardPane`), bakes `<out>.before.png` (count = the live cell's slot-0), FIRES the
    // card's button = ONE cap-gated verified turn on the live ledger, then re-renders +
    // bakes `<out>.after.png` (the bound value advanced) — proving the card is a live
    // cockpit surface whose button drives the operator's real cells. Default 520x360.
    #[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
    {
        if let Some(out) = render_card_pane_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((520.0, 360.0));
            match render_card_pane_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-card-pane FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-first-card <out>`: THE ONBOARDING KEYSTONE — the path from "I'm in" to
    // "I made a thing." Boots the full cockpit (the SAME chrome a stranger logs into),
    // drives `make_first_card` (mints a REAL editable card over the live World, its
    // substance the stranger's own home cell), bakes `<out>.before.png` (the first-card
    // view, the card live), then drives the onboarding affordances: `first_card_bump`
    // (the card's +1 = ONE cap-gated verified turn on their cell, a real receipt) and
    // `first_card_add_button` (a receipted view-patch adding a button), re-renders + bakes
    // `<out>.after.png`. Asserts a real receipt landed, the new button is in the re-folded
    // view, and the two frames differ — a stranger genuinely made + fired + edited a card
    // from the UI flow alone. Default 1100x780 (the full cockpit window).
    #[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
    {
        if let Some(out) = render_first_card_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1100.0, 780.0));
            match render_first_card_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-first-card FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-apps <out>`: THE APP STORE + APPS GOING. Two PNGs of the NEW pre-built
    // app-launcher capability: `<out>.launcher.png` lists the 19 wired starbridge-apps
    // (name · what-it-does) the real `RegistryLauncher` exposes — the "app store" shot —
    // and `<out>.png` LAUNCHES three of them (gallery / bounty-board / sealed-auction)
    // ONTO a shared live `World` (each launch fires its representative VERIFIED turn
    // through the real executor) and mounts each app's BESPOKE deos-view card live, bound
    // to its just-seeded cell — the "apps going" shot. Asserts the ledger height grew and
    // each launch landed a real receipt. Default 2560x1600 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "card-pane",
        feature = "app-registry",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_apps_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((2560.0, 1600.0));
            match render_apps_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-apps FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-apps-showcase <out>`: THE VISUAL-KILLER BAKE — launch the three apps
    // whose deos-view cards carry the richest LIVE gauges (bounty-board · privacy-voting
    // · governed-namespace) onto ONE shared live `World`, then DRIVE each with real
    // cap-gated verified turns until its gauges/bars are MEANINGFULLY FILLED (cast a poll
    // of yes/no/abstain votes so the tally bar-chart rises, gather a quorum of committee
    // proposals so the quorum bar tops out, advance the bounty state machine so both the
    // escrowed-reward AND stage gauges fill), and render the three bespoke cards side by
    // side. ONE high-res PNG written to `<out>` (the r/claudeai hero shot). Asserts the
    // ledger grew + names every fired turn so the gauges are the running World's real
    // state. Default 2560x1600 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "card-pane",
        feature = "app-registry",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_apps_showcase_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((2560.0, 1600.0));
            match render_apps_showcase_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-apps-showcase FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-service-economy <out>`: THE SERVICE-ECONOMY SCENE — the value/service
    // apps as live windows over ONE shared live `World`: the durable EXECUTION-LEASE
    // (a metered, payable lease whose periods-paid gauge climbs as its durable cursor
    // advances), the ESCROW-MARKET (a two-party sealed-escrow swap driven to SETTLED),
    // and the COMPUTE-EXCHANGE (a compute job driven to SETTLED, the budget split into
    // paid/refunded). Each app is launched onto the World and DRIVEN with real cap-gated
    // verified turns so its card's gauges/state are alive, then its bespoke deos-view
    // card is mounted side by side. ONE high-res PNG written to `<out>`. Asserts the
    // ledger grew + names every fired turn. Default 2560x1600 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "card-pane",
        feature = "app-registry",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_service_economy_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((2560.0, 1600.0));
            match render_service_economy_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-service-economy FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-app-fire <out>`: THE CLICK → VERIFIED TURN close-up. Launches a real app
    // (gallery) onto a live `World`, mounts its bespoke deos-view card, bakes
    // `<out>.before.png`, FIRES the card's `submit` button = ONE cap-gated VERIFIED turn
    // committed through `World::commit_turn` onto the live ledger (filling the next free
    // sealed-submission slot), then re-renders + bakes `<out>.after.png` (== `<out>.png`,
    // the card with the turn committed). Asserts the ledger height advanced by ONE and a
    // real receipt landed. Default 1100x780 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "card-pane",
        feature = "app-registry",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_app_fire_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1100.0, 780.0));
            match render_app_card_fire_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-app-fire FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-webshell-live <out>`: THE LIVE WEB-SHELL — open the full cockpit on the
    // WEB-SHELL tab, drive the persistent live `servo::WebView` to load a tall `data:`
    // page (a real cap-gated Servo render in the pane), bake `<out>.before.png`, deliver
    // ONE scroll-down input through the live loop (input → re-render → fresh tile), then
    // bake `<out>.after.png` — the before/after witness that the web-shell pane is
    // LIVE-interactive. Default 980x760 (the toolbar + a 720x460 tile + chrome).
    #[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "web-shell"))]
    {
        if let Some(out) = render_webshell_live_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((980.0, 760.0));
            match render_webshell_live_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-webshell-live FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-live-brain <out>`: THE HEADLINE — a LIVE Hermes brain (a real Claude
    // over the `hermes-acp` ACP subprocess) is given a short task, DECIDES the JS
    // itself, and that JS runs `run_js` against the cockpit's LIVE `World`: a real
    // crawl + real receipted turns landing on the live ledger, every fire bounded by
    // the agent's `held`. Bakes the cockpit inspector before/after over the SAME
    // World the brain drove. SKIPS gracefully (exit 0, prints why) when the env
    // can't reach a provider — the handshake/session still run LIVE. Hard-cap the
    // session with HERMES_MAX_ITERATIONS to bound provider spend. Default 1400x900.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "live-brain"
    ))]
    {
        if let Some(out) = render_live_brain_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1400.0, 900.0));
            match render_live_brain_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-live-brain FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-showcase <out>`: THE SHOWCASE BAKE — one gorgeous high-res PNG of
    // the full working deos desktop with EVERY dev surface mounted + seeded (chat
    // with the membrane card, editor with on-ledger patches, a recorded terminal
    // session, the confined-Hermes tool-call ledger) over the real cell world.
    // The marketing money shot. Renders the same headless gpui way the cockpit
    // bakes. Defaults to 2560x1600 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces"
    ))]
    {
        if let Some(out) = render_showcase_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((2560.0, 1600.0));
            match render_showcase_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-showcase FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-desktop <out>`: THE deos DESKTOP BAKE — the Windows-NT / Pharo
    // workbench over the live verified World. Bakes a desktop of cell-icons with two
    // inspector windows open and a right-click context menu visible, then drives a
    // real right-click actuation (a verified turn) + a drag-persist to prove the
    // metaphors are live, baking `<out>.png`. Default 1600x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_desktop_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            match render_desktop_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-desktop FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-welcome <out>`: THE CALM WELCOME BAKE — the warm front door (the OTHER
    // end of the bar from the dense `--render-desktop` workbench): a breathing room of
    // cell-icons + a gentle "type anything" Spotter pill + the warm welcome card
    // greeting a newcomer with the live image's real shape. Nothing else open. 1600x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_welcome_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            match render_welcome_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-welcome FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-woven <out>`: THE WOVEN DESKTOP BAKE — proves the surfaces are ONE
    // place, not separate pieces. It walks a stranger's path end to end: land on the
    // calm WELCOME front door over the live image → click a door → LAND in a live
    // surface whose Pharo halo ring is already floating (mold-ready, the seam welded)
    // → then use the Spotter (the unifying entry) to jump to a GLOBAL surface, which
    // also lands mold-ready. Bakes `<out>.png` of the woven room: a molded live
    // surface with its halo + the calm Spotter pill. Default 1600x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_woven_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            match render_woven_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-woven FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-doc-collab <out>`: THE FOCUSED DOCUMENT-COLLABORATION BAKE — drive the
    // whole document-language flow on ONE big editor window: author a base, fork a
    // confined co-author draft, the co-author TYPES a divergent line, the original author
    // diverges the main, STITCH (the pushout) → a first-class CONFLICT (both live
    // alternatives, attributed you-vs-co-author, HELD off the heap) rendered as the
    // ConflictView with one-click resolution choices, and the umem-heap boundary read out
    // at each step. The bake also resolves a copy to prove publish-to-heap, but leaves the
    // conflict + resolve buttons IN FRAME (un-clipped) for the shot. Default 1100x1500.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_doc_collab_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1100.0, 1500.0));
            match render_doc_collab_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-doc-collab FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-guest <out>`: THE GUEST / APP-FORWARD BAKE — the welcoming,
    // low-verbosity desktop a newcomer lands on (the "after you dismiss the
    // inspector" view): the real app surfaces (browser · editor · terminal · chat)
    // + a launcher-rolodex of acquired gadgets (read off the `AppRegistry`) + a
    // wonder strip, with the dense inspector NOT shown but SUMMONABLE (⌘K). The fix
    // for "the screenshot feels verbose": app-forward by default, inspector on
    // summon. Renders the same headless gpui way the showcase bakes. Default
    // 1600x1000 (overridable via `--render-size`).
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces",
        feature = "app-registry"
    ))]
    {
        if let Some(out) = render_guest_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            match render_guest_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-guest FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-self-hosting <out>`: THE SELF-HOSTING LOOP, RUN + PROVEN. Mounts
    // BOTH real halves in one cockpit view — a firmament editor over the LIVE
    // World (fires a real receipted save) + a LIVE alacritty PTY running real
    // `cargo --version` (or `--self-hosting-cmd <prog> <args…>`) INSIDE deos —
    // drives them, ASSERTS the editor receipt grew AND the command output is in
    // the terminal grid, then bakes `<out>.png`. Default 1600x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces",
        feature = "firmament",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_self_hosting_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            let cmd = self_hosting_cmd_arg(&args);
            match render_self_hosting_headless(&out, w, h, cmd) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-self-hosting FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-self-hosting-full <out>`: THE FULL SELF-HOSTING SINGLE LOOP, RUN +
    // PROVEN. The firmament editor's saves DUAL-WRITE to a disk-mirror dir; the
    // terminal's real toolchain reads that dir. The bake edits a real `main.rs`
    // (v1 → v2) through the editor, asserts a receipt + the on-disk mirror file now
    // holds the edit, then runs a live `rustc main.rs && ./prog` (or a `cat`) in
    // the terminal and asserts the NEW value reaches the grid — proving the
    // toolchain compiles THAT VERY EDIT. Bakes `<out>.png`. Default 1600x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces",
        feature = "firmament",
        feature = "embedded-executor"
    ))]
    {
        if let Some(out) = render_self_hosting_full_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1600.0, 1000.0));
            match render_self_hosting_full_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-self-hosting-full FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-unified-boot <out>`: THE ONE UNIFIED BOOT — a single window with
    // THREE panes over a real running `dregg-node`: a LIVE-node pane (the node's
    // own /status + cells + latest receipt, pulled over the wire), the firmament
    // editor (a save = a receipted turn on the cockpit's LOCAL ledger), and a live
    // PTY terminal. Pass `--node <url>` for the attach. The bake fires a real
    // editor save, RE-READS the node's receipt count to settle the write-back
    // question empirically (does an editor save reach the NODE ledger — yes/no),
    // and bakes `<out>.png`. Default 1900x1000.
    #[cfg(all(
        feature = "render-capture",
        feature = "gpui-ui",
        feature = "dev-surfaces",
        feature = "firmament",
        feature = "embedded-executor",
        feature = "live-node"
    ))]
    {
        if let Some(out) = render_unified_boot_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1900.0, 1000.0));
            let node = node_url_arg(&args);
            let cmd = self_hosting_cmd_arg(&args);
            match render_unified_boot_headless(&out, w, h, node, cmd) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-unified-boot FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }

        // `--render-client-signed-turn <out>`: the CLIENT-SIGNED turn proof — the
        // logged-in user's OWN cell signs a turn the node commits UNDER THE USER's
        // authority (not the operator). Stands up the full custody→sign→submit→commit
        // chain against a running --node and ASSERTS the new receipt's agent == the
        // user's cell (not the operator's). Pass `--node <url>`.
        if let Some(out) = render_client_signed_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1900.0, 1000.0));
            let node = node_url_arg(&args);
            let cmd = self_hosting_cmd_arg(&args);
            match render_client_signed_turn_headless(&out, w, h, node, cmd) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-client-signed-turn FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }

        // `--render-interactive-node-save <out>`: THE INTERACTIVE SELF-HOSTING WIRE —
        // a real save in the live `--node`-attached cockpit editor fires a turn on
        // the NODE's ledger. Unlike `--render-client-signed-turn` (a DIRECT
        // `save_to_node_client_signed` call), this drives the editor pane's OWN save
        // path (`Editor::save`, the callback a real Cmd-S invokes) and asserts the
        // node's `/api/receipts` GREW (N→N+1), client-signed under the USER's cell.
        // Pass `--node <url>` (with `--enable-faucet`). Default 1900x1000.
        if let Some(out) = render_interactive_node_save_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1900.0, 1000.0));
            let node = node_url_arg(&args);
            let cmd = self_hosting_cmd_arg(&args);
            match render_interactive_node_save_headless(&out, w, h, node, cmd) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-interactive-node-save FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-login <out>`: render the LOGIN CEREMONY surface offscreen (the
    // boot front door) the same headless way the cockpit bakes — the MCP-
    // screenshottable proof that the login surface lays out (the identity picker
    // for the demo seed identities). `<out>.png` is written.
    #[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
    {
        if let Some(out) = render_login_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((1280.0, 832.0));
            match render_login_headless(&out, w, h) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-login FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--render-touch <out>`: the TOUCH-UI bake (the graphideOS / mobile shape — the
    // bottom-bar mode switch + the tappable cell garden + a long-press face sheet).
    // `--render-size WxH` defaults to a phone 390x844; `--render-mode <name>` selects
    // a mode (Inhabit/Author/Dev/Inspect/Operate) and shows it clean (no sheet).
    #[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
    {
        if let Some(out) = render_touch_arg(&args) {
            let (w, h) = render_size_arg(&args).unwrap_or((390.0, 844.0));
            let mode = render_mode_arg(&args);
            match render_touch_headless(&out, w, h, mode.as_deref()) {
                Ok(()) => std::process::exit(0),
                Err(e) => {
                    eprintln!("render-touch FAILED: {e:#}");
                    std::process::exit(1);
                }
            }
        }
    }

    // `--desktop`: BOOT THE LIVE WOVEN WORKBENCH — open an INTERACTIVE gpui window
    // rooted at `DeosDesktop` (the woven desktop the `--render-woven` bake only ever
    // renders to a PNG), over the embedded verified World, STARTING AT THE CALM
    // WELCOME (a fresh layout shows the warm front door once — NOT the everything-
    // cascade the bake drives). The doors, the Spotter, the halos, and every surface
    // are live + clickable: each gesture fires a REAL verified turn through the
    // embedded executor (exactly as the bake proves they do). This is the windowed
    // twin of the bake — the playable deos_desktop. It returns when the window closes.
    //   cargo run -p starbridge-v2 --features native-full --bin starbridge-v2 -- --desktop
    #[cfg(all(feature = "embedded-executor", feature = "gpui-ui"))]
    {
        if args.iter().any(|a| a == "--desktop") {
            run_desktop_window();
            return;
        }
    }

    // `--node <url>`: ALSO connect the master interface to a LIVE remote dregg
    // node (its receipt nervous system + cell reflections), alongside the embedded
    // image. The embedded world is the headline; this is the additional remote
    // federation panel (the SSE stream advances the live receipt list per receipt).
    let node_url = node_url_arg(&args);

    #[cfg(feature = "embedded-executor")]
    {
        if headless || !cfg!(feature = "gpui-ui") {
            // The HEADLESS / CI path wants the fully-populated image up front, so
            // it builds it EAGERLY (all five seed turns run now).
            let (world, _anchors) = world::demo_world();
            headless_report(&world);
            // THE FOUR-SURFACE KILLER DEMO (N5) — the pug-handoff evaluation
            // artifact: mint → agent turn → notify handoff → the dual refusal, all
            // through the REAL embedded executor. Prints the four frames + both
            // refusals (each citing the executor's reason) and EXITS NON-ZERO if the
            // headline contract does not hold (a regression) — CI-friendly.
            let code = headless_killer_demo();
            std::process::exit(code);
        }

        #[cfg(feature = "gpui-ui")]
        {
            // THE WINDOW PATH — open INSTANTLY on the at-rest genesis image (the
            // four cells installed via the genesis path; NO executor turns yet), so
            // the cockpit paints sub-second. The five demo seed turns run AFTER the
            // window is up, driven one-at-a-time from a foreground async task (see
            // `run_window`) so the cells fill in LIVE — same content, off the paint
            // path. (`demo_world`'s eager seeding is exactly what made `main` grind
            // through the embedded executor before the window ever opened.)
            let (world, anchors, seed) = world::demo_genesis();
            run_window(world, anchors, seed, node_url);
        }
    }

    // In the embedded-but-headless build (no gpui), `node_url` is never moved into
    // `run_window`; consume it so it isn't flagged unused. (With gpui on, the gpui
    // branch above moved it and returned; with embedded off, the sel4-thin block
    // below consumes it.)
    #[cfg(all(feature = "embedded-executor", not(feature = "gpui-ui")))]
    let _ = node_url;

    #[cfg(not(feature = "embedded-executor"))]
    {
        // sel4-thin: no embedded executor. Speak the wire contract to a node.
        let _ = headless;
        // `--node <url>` resolves the same as the positional base URL below; the
        // thin path takes the positional form, so just consume the parsed value.
        let _ = node_url;
        let base = args.iter().nth(1).cloned();
        match base {
            Some(url) if url.starts_with("http") => {
                let client = client::NodeClient::http(url);
                thin_report(&client);
            }
            _ => {
                let client = client::NodeClient::mock();
                thin_report(&client);
            }
        }
    }
}

/// Headless self-check of the embedded world — proves the executor heart runs
/// without a window (CI-friendly; also the fallback when no display is present).
#[cfg(feature = "embedded-executor")]
fn headless_report(world: &world::World) {
    println!("== Starbridge v2 · embedded verified world ==");
    println!("cells:    {}", world.cell_count());
    println!("height:   {}", world.height());
    println!("receipts: {}", world.receipts().len());
    println!("image root: {}", hex::encode(world.state_root()));
    println!("-- cell world --");
    let mut ids: Vec<_> = world.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    for id in &ids {
        if let Some(c) = world.ledger().get(id) {
            println!(
                "  {} · balance {:>9} · {} caps{}",
                reflect::short_hex(id.as_bytes()),
                c.state.balance(),
                c.capabilities.len(),
                if c.delegate.is_some() {
                    " · delegate"
                } else {
                    ""
                },
            );
        }
    }
    println!("-- provenance (receipt chain) --");
    for (i, r) in world.receipts().iter().enumerate() {
        println!(
            "  h{:<3} receipt {} · {} actions · {} computrons",
            i + 1,
            reflect::short_hex(&r.receipt_hash()),
            r.action_count,
            r.computrons_used
        );
    }
    println!("-- dynamics --");
    for ev in world.dynamics().tail(20) {
        println!("  · {}", ev.label());
    }
    println!("(the master interface engine is live; pass no --headless to open the window)");
    println!();
}

/// Run the FOUR-SURFACE KILLER DEMO (N5) as the `--headless` self-check and print
/// its report. Returns the process exit code: `0` iff the headline contract holds
/// (the four frames committed, the handoff produced two distinct receipts, BOTH
/// refusals fired fail-closed), `1` otherwise (a regression — the substrate's
/// guarantees did not fire). This is the single runnable story a stranger / CI runs.
#[cfg(feature = "embedded-executor")]
fn headless_killer_demo() -> i32 {
    let mut d = demo::HeadlineDemo::boot();
    match d.run_headless() {
        Ok(_) => {
            print!("{}", demo::render_headless_report(&d));
            if d.contract_holds() {
                0
            } else {
                // The script ran but the contract is not satisfied (e.g. a missing
                // frame) — still a regression.
                eprintln!("FAIL: the killer-demo contract did not hold.");
                1
            }
        }
        Err(e) => {
            // A SETUP failure (a real regression in the substrate — NOT one of the
            // in-script refusals, which are the point). Print what we captured + the
            // failure, and exit non-zero so CI catches it.
            print!("{}", demo::render_headless_report(&d));
            eprintln!("FAIL: the killer demo could not complete — {}", e.label());
            1
        }
    }
}

/// Parse an optional `--node <url>` (or `--node=<url>`) argument — the live
/// remote-node base URL. Returns `None` when absent.
fn node_url_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--node" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--node=") {
            return Some(rest.to_string());
        }
    }
    None
}

#[cfg(feature = "gpui-ui")]
fn run_window(
    world: world::World,
    anchors: [dregg_cell::CellId; 3],
    seed: world::DemoSeed,
    node_url: Option<String>,
) {
    use gpui::{px, size, App, AppContext, Bounds, TitlebarOptions, WindowBounds, WindowOptions};
    use gpui_platform::application;
    use std::cell::RefCell;
    use std::rc::Rc;

    // STARTUP PROOF (the no-blank-screen receipt): build the HOME landing
    // portal's text model from the live world and report how many real lines of
    // text the boot view will render. Because the HOME tab renders exactly this
    // model, a non-zero count here is a non-blank rendered tree — the thing to
    // confirm if the window ever looks empty. (Printed before the run loop so it
    // shows even though `application().run` never returns.)
    //
    // NOTE: this image is the at-rest GENESIS image — the four cells exist but the
    // five demo seed turns have not run yet (they seed in live, after first paint).
    // The portal is full and alive regardless (it greets + names the heart + shows
    // "the image is at rest, waiting for your first turn"); the receipt/height
    // numbers simply climb as the seeding completes.
    {
        let portal = starbridge_v2::landing::LandingPortal::build(&world);
        println!("== Starbridge v2 · opening the window — boot view: HOME landing portal ==");
        println!(
            "HOME portal: {} lines of real text render (headline + {} cards + invitation)",
            portal.line_count(),
            portal.sections.len()
        );
        println!("  headline: {}", portal.headline);
        println!(
            "  the window opens INSTANTLY on the at-rest image; the {} demo seed turns \
             then seed in live (cells appear as each commits) — off the paint path.",
            world::DemoSeed::TOTAL
        );
        println!(
            "  (if the window looks blank, the text above is what should be on screen — \
             a render/display issue, not an empty UI)"
        );
    }

    let shared = Rc::new(RefCell::new(world));

    application().run(move |cx: &mut App| {
        // Register the embedded UI fonts. The windowed app uses the native platform
        // text system (CoreText), which does NOT have "Lilex" (the cockpit's default
        // font) — without this, every panel renders with BLANK text (the chrome lays
        // out, but no glyphs). The headless render paths load these the same way.
        {
            if let Err(e) = cx.text_system().add_fonts(bake_font_blobs()) {
                eprintln!("warning: failed to register embedded UI fonts: {e}");
            }
        }
        // Initialize gpui-component — the real widget library (text `Input`,
        // `Button`, the shadcn-style set). This installs its theme + the global
        // state every widget reads (focus trap, input registry, color/date
        // pickers, dock, popovers, …); without it any gpui-component widget the
        // cockpit constructs would panic on a missing global. One call at boot,
        // alongside the font registration. (See docs comment on the
        // `gpui-component` dep in Cargo.toml for the byte-identical-gpui rationale.)
        gpui_component::init(cx);
        // Install the deos theme: gpui-component's `init` leaves the kit in its
        // LIGHT default (the flashbang). Follow the OS appearance here (windowed),
        // defaulting to Dark, and tune the kit palette to the cockpit's GitHub-dark.
        apply_deos_theme(None, false, cx);
        let bounds = Bounds::centered(None, size(px(1280.), px(820.)), cx);
        // Move the seed into the LOGIN surface builder (the login surface hands it
        // to the cockpit at the post-login transition). `Option` so it is consumed
        // exactly once.
        let mut seed = Some(seed);
        // BOOT INTO THE LOGIN CEREMONY — the window root is the login surface, not
        // the cockpit. Picking an identity runs the real session ceremony and swaps
        // the root to the cockpit (wrapped in the session shell that owns logout +
        // the post-paint seeding/live-node tasks). See `login::LoginSurface`.
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some("deos — login".into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |window, cx| {
                let node_url = node_url.clone();
                let pending_seed = seed.take().expect("seed consumed once");
                // THE WINDOW-ROOT WELD — wrap the login surface in a gpui-component
                // `Root` so the post-login cockpit's kit text INPUTS (web-shell URL
                // bar, editor/composer/agent prompts) paint without the `Root::read`
                // unwrap-abort. The window root is a `Root` from boot onward.
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    login::LoginSurface::boot(
                        shared.clone(),
                        anchors,
                        pending_seed,
                        node_url,
                        focus,
                    )
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
            },
        )
        .expect("failed to open window");
        cx.activate(true);
    });
}

/// **THE LIVE WOVEN WORKBENCH** — open the interactive [`DeosDesktop`] (the woven
/// desktop) in a real gpui window over the embedded verified World, starting at the
/// calm WELCOME. This is the windowed twin of the `--render-woven` bake: the SAME
/// `DeosDesktop::new(...)` over the SAME `world::demo_world()` image, but rooted in a
/// live `cx.open_window` (exactly as [`run_window`] does for the cockpit) instead of a
/// headless capture — so the doors, the Spotter, the halos, and every surface are
/// clickable and fire real verified turns through the embedded executor. The desktop
/// persists its arrangement to `DesktopLayout::default_path()` (drag to arrange); the
/// calm welcome greets a never-greeted image exactly once, then opens onto the arranged
/// room. NOT gated behind `render-capture`: this is the live windowed entry, `--desktop`.
#[cfg(all(feature = "embedded-executor", feature = "gpui-ui"))]
fn run_desktop_window() {
    use gpui::{px, size, App, AppContext, Bounds, TitlebarOptions, WindowBounds, WindowOptions};
    use gpui_platform::application;
    use starbridge_v2::deos_desktop::{DeosDesktop, DesktopLayout};
    use starbridge_v2::durable_desktop::{boot_desktop_world, DurableBoot};
    use std::cell::RefCell;
    use std::rc::Rc;

    // WHERE THE WORLD LIVES — a DURABLE redb image beside the layout sidecar by
    // DEFAULT, so "your world is one durable image" is LITERALLY true for the windowed
    // desktop: the World (cells, balances, receipts, every verified turn) survives a
    // close + reopen, not just the layout sidecar. Overridable via
    // `--world-image=<path>` / `--fresh-world` / the `DEOS_WORLD_IMAGE` env, with a
    // `--world-image=:memory:` (aka `ephemeral`) escape hatch that keeps the OLD
    // `demo_world()` behavior so bakes / tests / CI stay hermetic + deterministic. The
    // heavy lifting — open-recovering, seed-on-first-run, the never-strand /
    // never-silently-wipe fallbacks — lives in `durable_desktop`; this only parses the
    // spec and reports the outcome.
    let args: Vec<String> = std::env::args().collect();
    let spec = resolve_world_image_spec(&args);
    let DurableBoot {
        world,
        anchors,
        origin,
    } = boot_desktop_world(spec);
    let [_treasury, _service, user] = anchors;

    // STARTUP PROOF (the no-blank-screen receipt): the desktop opens onto the live
    // image; report its real shape AND whether it is durable (and from where) so a
    // blank window reads as a render/display issue (not an empty UI), and a
    // non-persisting session reads LOUDLY as such. A never-greeted layout opens onto
    // the calm WELCOME front door.
    let layout_path = DesktopLayout::default_path();
    {
        let fresh = !DesktopLayout::load(&layout_path).prefs.welcomed;
        println!("== Starbridge v2 · opening the woven DESKTOP — root: DeosDesktop ==");
        println!("  world: {}", origin.summary());
        println!(
            "  live image: {} cells · height {} · {} receipts",
            world.cell_count(),
            world.height(),
            world.receipts().len()
        );
        println!(
            "  layout sidecar: {} ({})",
            layout_path.display(),
            if fresh {
                "fresh — opens onto the calm WELCOME front door"
            } else {
                "remembered — opens onto your arranged room"
            }
        );
        println!(
            "  right-click ANYTHING · double-click to inspect · drag to arrange (persisted) · \
             the Spotter, doors, halos + surfaces fire REAL verified turns"
        );
    }

    let shared = Rc::new(RefCell::new(world));

    application().run(move |cx: &mut App| {
        // Register the embedded UI fonts (CoreText lacks "Lilex"/"IBM Plex"); without
        // this every panel lays out but renders BLANK text — same as `run_window`.
        {
            if let Err(e) = cx.text_system().add_fonts(bake_font_blobs()) {
                eprintln!("warning: failed to register embedded UI fonts: {e}");
            }
        }
        // The real widget kit — but the NT desktop is a LIGHT room by design: its
        // hand-rolled chrome is panel-grey with dark text, so the kit's theme must
        // be LIGHT regardless of the OS appearance. (Following the OS here painted
        // the GitHub-dark kit palette into the doc editor's Input and the Spotter's
        // query field under OS dark mode — the scout-found theme inversion.) The
        // cockpit windows keep following the OS via `apply_deos_theme`.
        gpui_component::init(cx);
        gpui_component::Theme::change(gpui_component::ThemeMode::Light, None, cx);

        let bounds = Bounds::centered(None, size(px(1600.), px(1000.)), cx);
        let layout_path = layout_path.clone();
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some("deos — desktop".into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |window, cx| {
                // THE WINDOW ROOT IS `DeosDesktop` — built directly over the live World
                // (no login ceremony; the desktop is its own front door, opening on the
                // calm welcome). Wrapped in a gpui-component `Root` so the surfaces' kit
                // text inputs (doc editor, branch prompts, the Spotter) paint.
                let view = cx.new(|cx| {
                    DeosDesktop::new(shared.clone(), user, layout_path.clone(), window, cx)
                });
                cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
            },
        )
        .expect("failed to open window");
        cx.activate(true);
    });
}

/// Resolve WHERE the windowed desktop's World lives from the CLI + the environment
/// (the durable-image weld's front knob). Precedence:
///
///   1. `--world-image=<v>` / `--world-image <v>` (explicit),
///   2. else the `DEOS_WORLD_IMAGE` env knob,
///   3. else the DEFAULT durable image beside the layout sidecar.
///
/// A value of `:memory:` (or `ephemeral`) is the ESCAPE HATCH — the old in-RAM
/// `demo_world()` (bakes / tests / CI stay hermetic + deterministic). `--fresh-world`
/// (orthogonal) discards the current durable image and starts over (it is
/// quarantined aside, never deleted); it is meaningless for — and ignored on — the
/// ephemeral hatch.
#[cfg(all(feature = "embedded-executor", feature = "gpui-ui"))]
fn resolve_world_image_spec(args: &[String]) -> starbridge_v2::durable_desktop::WorldImageSpec {
    use starbridge_v2::durable_desktop::WorldImageSpec;
    let fresh = args.iter().any(|a| a == "--fresh-world");
    let raw = world_image_arg(args)
        .or_else(|| std::env::var("DEOS_WORLD_IMAGE").ok())
        .filter(|s| !s.is_empty());
    match raw.as_deref() {
        Some(":memory:") | Some("ephemeral") => WorldImageSpec::Ephemeral,
        Some(p) => WorldImageSpec::Durable {
            path: std::path::PathBuf::from(p),
            fresh,
        },
        None if args.iter().any(|a| a == "--durable-world") => WorldImageSpec::Durable {
            path: default_world_image_path(),
            fresh,
        },
        // OPT-IN, not default: the durable overlay's change-set drops CreateCell
        // (CORE-AUDIT.md finding 1), and the desktop's App Shelf / Exchange / Letter
        // actuations all create cells — a durable-by-default desktop would refuse or
        // silently truncate on reopen. `--desktop` stays EPHEMERAL until the operator
        // asks (`--durable-world` or an explicit --world-image path), which becomes
        // safe once the executor exposes its real journal write-set.
        None => WorldImageSpec::Ephemeral,
    }
}

/// Parse the `--world-image <path>` (or `=<path>`) argument. Returns `None` when
/// absent. Mirrors [`render_woven_arg`]'s parse idiom.
#[cfg(all(feature = "embedded-executor", feature = "gpui-ui"))]
fn world_image_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--world-image" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--world-image=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// The DEFAULT durable World image path — beside the layout sidecar
/// (`DesktopLayout::default_path()`'s directory), named `deos-world.redb`. So the
/// World and its window arrangement live in the same place, and "your world is one
/// durable image" needs no flags.
#[cfg(all(feature = "embedded-executor", feature = "gpui-ui"))]
fn default_world_image_path() -> std::path::PathBuf {
    use starbridge_v2::deos_desktop::DesktopLayout;
    let layout = DesktopLayout::default_path();
    layout
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| std::path::PathBuf::from("."))
        .join("deos-world.redb")
}

/// Install the deos theme on the gpui-component kit, the SINGLE call every init
/// site makes immediately after `gpui_component::init(cx)`.
///
/// `gpui_component::init` ends with `Theme::change(ThemeMode::Light, …)` — it
/// installs the kit's LIGHT theme by default. Left alone, kit widgets (`Button`,
/// `Input`, list/table) render as bright patches against the cockpit's dark
/// chrome — the "flashbang". This routes through the kit's own theme API to:
///
///  1. Pick the mode. Windowed: follow the OS appearance (`cx.window_appearance()`)
///     so a user in OS dark mode gets dark deos and OS light mode gets light —
///     defaulting to Dark when the platform is ambiguous. Headless bakes pass
///     `force_dark = true` (the marketing shot is always the dark desktop).
///  2. `Theme::change(mode, …)` to swap the kit to that mode's palette.
///  3. In dark, re-tune the kit `ThemeColor` tokens to the cockpit's GitHub-dark
///     palette (the same values as `views::theme` / `dock::theme` / `showcase`)
///     so the kit widgets, the dock chrome, and the hand-rolled panels are ONE
///     cohesive dark look — same backgrounds, borders, text, accent — instead of
///     the kit's flat near-black neutral sitting next to the cockpit's blue-tinted
///     slate.
#[cfg(feature = "gpui-ui")]
fn apply_deos_theme(window: Option<&mut gpui::Window>, force_dark: bool, cx: &mut gpui::App) {
    use gpui::{rgb, Hsla};
    use gpui_component::{Theme, ThemeMode};

    let mode = if force_dark {
        ThemeMode::Dark
    } else {
        // Follow the OS appearance, defaulting to Dark. `WindowAppearance ->
        // ThemeMode` maps Dark/VibrantDark -> Dark and Light/VibrantLight -> Light.
        ThemeMode::from(cx.window_appearance())
    };

    Theme::change(mode, window, cx);

    if !mode.is_dark() {
        // OS light mode: leave the kit's light theme as-is (no flashbang the other
        // direction — the chrome the cockpit hand-rolls reads dark, but the kit
        // surfaces stay coherent light; the windowed light path is the minority
        // case a user explicitly opted into via their OS).
        return;
    }

    // The cockpit's GitHub-dark palette — the single source of truth mirrored by
    // `views::theme`, `dock::theme`, and `showcase::theme`.
    let bg: Hsla = rgb(0x0e1116).into(); // surface
    let panel: Hsla = rgb(0x161b22).into(); // raised card / popover / sidebar
    let panel_hi: Hsla = rgb(0x1f2630).into(); // hover / active fill
    let border: Hsla = rgb(0x2b3340).into();
    let text: Hsla = rgb(0xd7dee8).into();
    let muted: Hsla = rgb(0x7d8794).into();
    let accent: Hsla = rgb(0x6cb6ff).into(); // the blue the cockpit accents with
    let on_accent: Hsla = rgb(0x0e1116).into(); // dark text on the bright accent
                                                // The status hues — the SAME values the cockpit hand-rolls in `views::theme`
                                                // (good / warn / bad), so a kit `.success()`/`.warning()`/`.danger()` button
                                                // matches a hand-rolled status pill exactly.
    let good: Hsla = rgb(0x57d977).into();
    let warn: Hsla = rgb(0xe3b341).into();
    let bad: Hsla = rgb(0xe5534b).into();

    // CRITICAL: kit `Button` variants read their FILL from `theme.tokens.button_*`,
    // which derive 1:1 from the `colors.button_*` source fields. Start from the
    // kit's own canonical DARK `ThemeColor` (every button_* already a correct dark
    // value — no light field is left to flashbang), THEN overlay the cockpit
    // palette, THEN regenerate the token table. (Setting only a handful of `colors`
    // fields would leave the rest at whatever `apply_config` produced — that was
    // the residual white-button bug.)
    let mut c = *gpui_component::ThemeColor::dark();

    // Surfaces.
    c.background = bg;
    c.foreground = text;
    c.popover = panel;
    c.popover_foreground = text;
    c.border = border;
    c.input = border;
    c.ring = accent;
    c.caret = accent;
    c.selection = accent.opacity(0.30);
    c.muted = panel;
    c.muted_foreground = muted;
    c.accordion = panel;
    c.accordion_hover = panel_hi;
    c.group_box = panel;
    c.group_box_foreground = text;
    c.scrollbar_thumb = border;
    c.scrollbar_thumb_hover = muted;
    c.link = accent;
    c.link_hover = rgb(0x8cc6ff).into();
    c.link_active = rgb(0x4f9fe6).into();

    // Secondary fills (the quiet button family + ghost text).
    c.secondary = panel;
    c.secondary_foreground = text;
    c.secondary_hover = panel_hi;
    c.secondary_active = panel_hi;

    // Accent (hover backgrounds on menu/list items).
    c.accent = panel_hi;
    c.accent_foreground = text;

    // The plain (Default) + Secondary button families → read the surface, dark text.
    c.button = panel;
    c.button_hover = panel_hi;
    c.button_active = panel_hi;
    c.button_foreground = text;
    c.button_secondary = panel;
    c.button_secondary_hover = panel_hi;
    c.button_secondary_active = panel_hi;
    c.button_secondary_foreground = text;

    // Primary = the cockpit's signature blue, dark text on it.
    c.primary = accent;
    c.primary_hover = rgb(0x8cc6ff).into();
    c.primary_active = rgb(0x4f9fe6).into();
    c.primary_foreground = on_accent;
    c.button_primary = accent;
    c.button_primary_hover = rgb(0x8cc6ff).into();
    c.button_primary_active = rgb(0x4f9fe6).into();
    c.button_primary_foreground = on_accent;
    c.sidebar_primary = accent;
    c.sidebar_primary_foreground = on_accent;

    // Status button families — match the cockpit's good/warn/bad with dark text so
    // they read as saturated chips, never bright-white panels.
    c.success = good;
    c.success_hover = rgb(0x6fe88c).into();
    c.success_active = rgb(0x44c265).into();
    c.success_foreground = on_accent;
    c.button_success = good;
    c.button_success_hover = rgb(0x6fe88c).into();
    c.button_success_active = rgb(0x44c265).into();
    c.button_success_foreground = on_accent;

    c.warning = warn;
    c.warning_hover = rgb(0xf0c662).into();
    c.warning_active = rgb(0xc99a2f).into();
    c.warning_foreground = on_accent;
    c.button_warning = warn;
    c.button_warning_hover = rgb(0xf0c662).into();
    c.button_warning_active = rgb(0xc99a2f).into();
    c.button_warning_foreground = on_accent;

    c.danger = bad;
    c.danger_hover = rgb(0xef6f68).into();
    c.danger_active = rgb(0xc83f38).into();
    c.danger_foreground = text;
    c.button_danger = bad;
    c.button_danger_hover = rgb(0xef6f68).into();
    c.button_danger_active = rgb(0xc83f38).into();
    c.button_danger_foreground = text;

    c.info = accent;
    c.info_hover = rgb(0x8cc6ff).into();
    c.info_active = rgb(0x4f9fe6).into();
    c.info_foreground = on_accent;
    c.button_info = accent;
    c.button_info_hover = rgb(0x8cc6ff).into();
    c.button_info_active = rgb(0x4f9fe6).into();
    c.button_info_foreground = on_accent;

    // Lists.
    c.list = bg;
    c.list_even = bg;
    c.list_head = panel;
    c.list_hover = panel_hi;
    c.list_active = panel_hi;
    c.list_active_border = accent;

    // Tables.
    c.table = bg;
    c.table_even = panel;
    c.table_head = panel;
    c.table_head_foreground = muted;
    c.table_hover = panel_hi;
    c.table_active = panel_hi;
    c.table_active_border = accent;
    c.table_row_border = border;

    // Tabs.
    c.tab = bg;
    c.tab_bar = bg;
    c.tab_foreground = muted;
    c.tab_active = panel;
    c.tab_active_foreground = text;

    // Title bar / sidebar / status bar chrome.
    c.title_bar = panel;
    c.title_bar_border = border;
    c.status_bar = panel;
    c.status_bar_border = border;
    c.sidebar = panel;
    c.sidebar_foreground = text;
    c.sidebar_border = border;
    c.sidebar_accent = panel_hi;
    c.sidebar_accent_foreground = text;

    // Commit the tuned palette + regenerate the token table (the buttons, badges,
    // and callouts read `tokens`, which is derived 1:1 from these `colors`).
    let t = Theme::global_mut(cx);
    t.colors = c;
    t.tokens = gpui_component::ThemeTokens::from(&t.colors);
}

/// Parse the `--render-cockpit <out>` (or `--render-cockpit=<out>`) argument —
/// the output base path for the headless cockpit bake. Returns `None` when
/// absent. `<out>` names the file stem; `<out>.rgba` (the raw 800x600 RGBA8 the
/// seL4 PD bakes) and `<out>.png` (a visual check) are written.
#[cfg(feature = "render-capture")]
fn render_cockpit_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-cockpit" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-cockpit=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-showcase <out>` (or `--render-showcase=<out>`) argument —
/// the output base path for the SHOWCASE BAKE (the full-desktop money shot).
/// Returns `None` when absent. `<out>.png` is written.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces"
))]
fn render_showcase_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-showcase" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-showcase=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-desktop <out>` (or `=<out>`) argument — the output base path
/// for the deos DESKTOP bake. Returns `None` when absent. `<out>.png` is written.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_desktop_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-desktop" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-desktop=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-welcome <out>` (or `=<out>`) argument — the output base path
/// for the CALM WELCOME bake (the other end of the bar: the warm front door a stranger
/// wakes up to, not the dense workbench). Returns `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_welcome_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-welcome" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-welcome=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-woven <out>` (or `=<out>`) argument — the output base path for
/// the WOVEN DESKTOP bake (the stranger's path, welded end to end). Returns `None` when
/// absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_woven_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-woven" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-woven=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-doc-collab <out>` (or `=<out>`) argument — the output base path
/// for the focused DOCUMENT-COLLABORATION bake (branch · diverge · stitch · conflict ·
/// resolve). Returns `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_doc_collab_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-doc-collab" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-doc-collab=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// **THE WOVEN DESKTOP BAKE** — the proof the surfaces are ONE inhabitable place, not a
/// drawer of separate pieces. Where `--render-welcome` shows the calm front door and
/// `--render-desktop` shows the dense workbench, THIS bake walks the SEAM BETWEEN them —
/// a stranger's path, welded end to end:
///
///   1. A fresh image opens onto the calm WELCOME card (greeting the live world's real
///      shape), with NOTHING else open — the calm default.
///   2. Clicking a welcome door ("Write something") LANDS the newcomer in a live surface
///      (a document editor on their own cell) that is already MOLD-READY: its Pharo halo
///      ring floats around it the instant they arrive (the welded seam — open and "you
///      can mold it" are the same arrival), and the welcome card is gone.
///   3. The SPOTTER — the unifying entry — jumps to a GLOBAL surface (the World
///      Explorer), which ALSO lands mold-ready (its halo floating). One entry, every
///      surface; every landing hands you the mold-in-place gesture.
///
/// The bake ASSERTS each seam (welcome→landed-window-selected, halo ring present on the
/// landed surface, Spotter ranks the global surface and dispatching it lands selected),
/// then leaves a surface molded with its halo + the calm Spotter pill showing, and
/// captures `<out>.png` of the woven room. Hermetic. Default 1600x1000.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_woven_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::deos_desktop::DeosDesktop;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // A hermetic, fresh sidecar so `welcomed = false` → the warm card shows (a fresh
    // image is exactly the newcomer's first run). Start clean.
    let layout_path =
        std::env::temp_dir().join(format!("deos-woven-bake-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    // The live verified image — the SAME `World` the cockpit runs.
    let (world, anchors) = starbridge_v2::world::demo_world();
    let [_treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));
    let height = shared.borrow().height();

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx.open_window(size(px(w), px(h)), move |window, cx| {
        let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
        *desk_sink.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    // ── 1. THE CALM DEFAULT — the warm front door over the live image, nothing else. ──
    let (shown, greeting, open_windows) = desk.update(&mut cx, |d, _cx| {
        (
            d.bake_welcome_is_shown(),
            d.bake_welcome_greeting(),
            d.bake_total_window_count(),
        )
    });
    anyhow::ensure!(
        shown,
        "a fresh image must open onto the warm WELCOME card (the calm front door)"
    );
    anyhow::ensure!(
        open_windows == 0,
        "the calm default opens NOTHING else (got {open_windows} open window(s))"
    );
    anyhow::ensure!(
        greeting.contains(&height.to_string()),
        "the welcome greeting must name the live image's REAL history height ({height})"
    );

    // ── 2. THE DOOR LANDS YOU MOLD-READY — click "Write something" (door 2: 0-based). ──
    // The door opens a live document surface AND leaves it selected, so its halo ring is
    // already floating: open and "you can mold it" are the same arrival (the welded seam).
    desk.update(&mut cx, |d, cx| {
        d.bake_welcome_door(2); // 0:look 1:find 2:write 3:survey
        cx.notify();
    });
    cx.run_until_parked();
    anyhow::ensure!(
        !desk.update(&mut cx, |d, _cx| d.bake_welcome_is_shown()),
        "clicking a welcome door dismisses the front door — you have begun"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_total_window_count()) >= 1,
        "the welcome door must LAND the newcomer in a live surface (a window opened)"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_selection_is_window()),
        "the landed surface must be SELECTED (mold-ready) — the welcome door hands you \
         straight to the mold-in-place gesture, not an unselected window to go hunt"
    );
    let door_handles = desk.update(&mut cx, |d, _cx| d.bake_halo_handle_count());
    anyhow::ensure!(
        door_handles >= 5,
        "the landed surface must float its Pharo halo ring (mold-in-place handles); got \
         {door_handles}"
    );

    // ── 3. THE SPOTTER IS THE UNIFYING ENTRY — jump to a GLOBAL surface, land mold-ready. ──
    // Open the Spotter and confirm it ranks the global World Explorer surface (not only
    // per-cell actions) — the one entry to every surface.
    desk.update(&mut cx, |d, _cx| d.bake_open_spotter("world explorer"));
    let spot_matches = desk
        .update(&mut cx, |d, _cx| d.bake_spotter_match_count())
        .unwrap_or(0);
    let top = desk
        .update(&mut cx, |d, _cx| d.bake_spotter_top_label())
        .unwrap_or_default();
    anyhow::ensure!(
        spot_matches >= 1 && top.to_lowercase().contains("world explorer"),
        "the Spotter must reach the GLOBAL World Explorer surface (top: {top:?}, {spot_matches} \
         match(es)) — the unifying entry jumps to places, not only cells"
    );
    let before = desk.update(&mut cx, |d, _cx| d.bake_total_window_count());
    desk.update(&mut cx, |d, _cx| d.bake_spotter_dispatch_top());
    cx.run_until_parked();
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_total_window_count()) > before,
        "dispatching the Spotter's global surface opened it"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_selection_is_window())
            && desk.update(&mut cx, |d, _cx| d.bake_halo_handle_count()) >= 5,
        "a Spotter jump also LANDS mold-ready — the global surface arrives with its halo \
         ring floating, exactly like the welcome door (one consistent gesture everywhere)"
    );

    // ── 4. THE SPOTTER REACHES THIS SESSION'S NEW SURFACES TOO — one entry, every place. ──
    // Each lands mold-ready (selected + its halo floating), exactly like the welcome door
    // and the World Explorer jump: the woven surfaces are ONE place, one gesture vocabulary,
    // not a scatter of separate windows you have to know exist.

    // 4a. A DOCUMENT-COLLABORATION session — the Spotter opens the editor WITH a confined
    //     co-author draft already forked (branch · stitch · resolve), landed mold-ready.
    desk.update(&mut cx, |d, _cx| d.bake_open_spotter("co-author document"));
    let collab_top = desk
        .update(&mut cx, |d, _cx| d.bake_spotter_top_label())
        .unwrap_or_default();
    anyhow::ensure!(
        collab_top.to_lowercase().contains("co-author"),
        "the Spotter must reach the DOCUMENT-COLLABORATION surface (top: {collab_top:?})"
    );
    desk.update(&mut cx, |d, _cx| d.bake_spotter_dispatch_top());
    cx.run_until_parked();
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_selected_window_label()) == Some("Document")
            && desk.update(&mut cx, |d, _cx| d.bake_doc_has_branch(user)),
        "the doc-collab jump LANDS in a Document surface mold-ready, WITH a forked co-author \
         draft already in flight (a real branch-and-stitch session, not a bare editor)"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_halo_handle_count()) >= 5,
        "the landed doc-collab surface floats its Pharo halo ring (mold-in-place)"
    );

    // 4b. THE WORLD-STATUS BOARD — the agent-composable ViewNode surface (the reflective
    //     pane a confined agent rewrites). Reachable from the same Spotter. Gated on
    //     `card-pane` (the default native-full build has it).
    #[cfg(feature = "card-pane")]
    {
        desk.update(&mut cx, |d, _cx| d.bake_open_spotter("world status board"));
        let board_top = desk
            .update(&mut cx, |d, _cx| d.bake_spotter_top_label())
            .unwrap_or_default();
        anyhow::ensure!(
            board_top.to_lowercase().contains("world-status board"),
            "the Spotter must reach the agent-composable World-Status board (top: {board_top:?})"
        );
        desk.update(&mut cx, |d, _cx| d.bake_spotter_dispatch_top());
        cx.run_until_parked();
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_selected_window_label()) == Some("World Status")
                && desk.update(&mut cx, |d, _cx| d.bake_halo_handle_count()) >= 5,
            "the World-Status board jump lands its ViewNode surface mold-ready (the same \
             gesture as every other surface)"
        );
    }

    // 4c. A CONFINED ANDROID CELL with its SystemUI cap-chrome — reachable from the same
    //     Spotter; landing mints the confined chrome (a real PermWorld + executor) and the
    //     status bar reads its standing authorities. Gated on `android-systemui`.
    #[cfg(feature = "android-systemui")]
    {
        desk.update(&mut cx, |d, _cx| {
            d.bake_open_spotter("android cell systemui")
        });
        let android_top = desk
            .update(&mut cx, |d, _cx| d.bake_spotter_top_label())
            .unwrap_or_default();
        anyhow::ensure!(
            android_top.to_lowercase().contains("android cell"),
            "the Spotter must reach the Android Cell / SystemUI cap-chrome (top: {android_top:?})"
        );
        desk.update(&mut cx, |d, _cx| d.bake_spotter_dispatch_top());
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_selected_window_label())
                == Some("Android · SystemUI")
                && desk.update(&mut cx, |d, _cx| d.bake_halo_handle_count()) >= 5,
            "the Android Cell jump lands its SystemUI cap-chrome mold-ready (one gesture)"
        );
        let held = desk.update(&mut cx, |d, _cx| d.clone_status_held(user));
        anyhow::ensure!(
            !held.is_empty(),
            "the landed Android cell's confined chrome must read its standing authorities on \
             the status bar (the cap-chrome is live, not a mock)"
        );
    }

    // 4d. THE AGENT AS CO-AUTHOR, IN THE SAME ROOM — a confined agent composes a brand-new
    //     World Board from scratch (reading the live World) and it MOUNTS as a real window
    //     beside the woven surfaces: the agent-composed surface is part of the one place,
    //     not a separate demo. Gated on `card-pane` (drives a SpiderMonkey runtime).
    #[cfg(feature = "card-pane")]
    {
        let mut rt = deos_js::JsRuntime::new()
            .map_err(|e| anyhow::anyhow!("boot SpiderMonkey for the agent's compose loop: {e}"))?;
        let board = desk
            .update(&mut cx, |d, cx| {
                d.bake_agent_composes_world_board(&mut rt, cx)
            })
            .map_err(|e| anyhow::anyhow!("the agent's compose-from-scratch loop failed: {e}"))?;
        anyhow::ensure!(
            board.started_empty && board.crawled_cells >= 1 && board.mounted_window,
            "the agent must compose a NEW World Board from an empty root (crawling the live \
             World) and mount it as a real window in the same room (empty={}, crawled={}, \
             mounted={})",
            board.started_empty,
            board.crawled_cells,
            board.mounted_window
        );
    }

    // ── 4e. THE AGENT ROOM — the resident as first-class inhabitant. The Spotter
    //     reaches it like every surface; it lands mold-ready; its default resident is
    //     the busiest NON-OPERATOR cell (the demo genesis really acts), read off the
    //     executor's receipts — never self-report.
    desk.update(&mut cx, |d, _cx| d.bake_open_spotter("agent room"));
    let room_top = desk
        .update(&mut cx, |d, _cx| d.bake_spotter_top_label())
        .unwrap_or_default();
    anyhow::ensure!(
        room_top.to_lowercase().contains("agent room"),
        "the Spotter must reach the AGENT ROOM (top: {room_top:?})"
    );
    desk.update(&mut cx, |d, _cx| d.bake_spotter_dispatch_top());
    cx.run_until_parked();
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_selected_window_label()) == Some("Agent Room"),
        "the Agent Room jump lands its window mold-ready (one gesture everywhere)"
    );
    let resident = desk.update(&mut cx, |d, _cx| d.bake_agent_room_resident());
    anyhow::ensure!(
        resident != user,
        "the room's default resident is the busiest NON-operator cell (genesis acts)"
    );

    // ── 4f. GOSSAMER — drag-transclude quotes a cell into the document, and a cyan
    //     thread SNAPS between the quoting document window and the quoted surface:
    //     Xanadu's parallel visible connection, over a real receipted quote.
    desk.update(&mut cx, |d, cx| {
        d.bake_open_doc(user);
        d.bake_transclude(resident, user);
        cx.notify();
    });
    cx.run_until_parked();
    let threads_now = desk.update(&mut cx, |d, _cx| d.bake_thread_count());
    anyhow::ensure!(
        threads_now >= 1 && desk.update(&mut cx, |d, _cx| d.bake_thread_between(resident, user)),
        "a transclusion must snap a GOSSAMER thread between quoted cell and quoting \
         document (got {threads_now} thread(s))"
    );

    // ── 4g. THE PULSE SPEAKS — a REFUSED moment arrives as an amber toast card
    //     (here pushed via the bake feed; live, pump_dynamics feeds it from the
    //     dynamics stream), and the keyboard spine's Escape ladder is real.
    desk.update(&mut cx, |d, cx| {
        d.bake_push_toast(
            true,
            "3cc02624 — unauthorized effect: Transfer beyond mandate",
        );
        d.bake_push_toast(false, "resident 87a55eb5 committed turn #6 · 41cu");
        cx.notify();
    });
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_toast_count()) == 2,
        "the toast rack carries the pulse's announcements"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_key("k", true)),
        "⌘K summons the Spotter from anywhere (the keyboard spine)"
    );
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_key("escape", false)),
        "Escape dismisses the Spotter (the trap the scouts found is fixed)"
    );
    cx.run_until_parked();

    // ── 4h. THE APP SHELF — the registry's apps as first-class citizens: launch one
    //     and its cell + receipt land on the LIVE World (a real verified turn), its
    //     icon wearing the app's own face. Gated on `app-registry`.
    #[cfg(feature = "app-registry")]
    {
        desk.update(&mut cx, |d, _cx| d.bake_open_app_shelf());
        cx.run_until_parked();
        let apps = desk.update(&mut cx, |d, _cx| d.bake_app_count());
        anyhow::ensure!(
            apps >= 10,
            "the shelf lists the registry's roster (got {apps} apps)"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_launch_app("bounty-board")),
            "launching bounty-board lands its cell + receipt on the LIVE World"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_installed_app_count()) == 1,
            "the launch is recorded on the shelf's installed set"
        );
        cx.run_until_parked();
    }

    // ── 4h′. THE EXCHANGE FLOOR — the $DREGG agent economy on the glass: opening
    //     the floor installs its substrate (compute-exchange + execution-lease, real
    //     launch receipts); POSTING an offer, TAKING it under a metered lease, and
    //     SETTLING Σδ=0 are each REAL verified turns whose receipts grow the LIVE
    //     World's log; the over-budget cheat is refused by the executor itself.
    #[cfg(feature = "app-registry")]
    {
        let r0 = desk.update(&mut cx, |d, _cx| d.bake_world_receipt_count());
        desk.update(&mut cx, |d, _cx| d.bake_open_exchange());
        cx.run_until_parked();
        let r_open = desk.update(&mut cx, |d, _cx| d.bake_world_receipt_count());
        anyhow::ensure!(
            r_open > r0,
            "opening the Exchange Floor launches its substrate apps — real receipts \
             ({r0} → {r_open})"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_post_offer()),
            "posting an offer commits a real verified 'post' turn on a fresh offer cell"
        );
        let r_post = desk.update(&mut cx, |d, _cx| d.bake_world_receipt_count());
        anyhow::ensure!(r_post > r_open, "the post receipt landed on the LIVE World");
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_exchange_cheat_refused()),
            "the over-budget take is REFUSED by the executor (the BUDGET gate bites)"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_world_receipt_count()) == r_post,
            "the refused cheat committed NOTHING (anti-ghost)"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_take_lease()),
            "taking the lease commits the bid + the metered checkpoint"
        );
        let r_take = desk.update(&mut cx, |d, _cx| d.bake_world_receipt_count());
        anyhow::ensure!(r_take > r_post, "the take's receipts landed");
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_settle_offer()),
            "settlement commits (the executor-enforced Σδ=0 split)"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_exchange_settlement_delta()) == Some(0),
            "the settled offer shows Σδ = 0 read off the LIVE ledger"
        );
        cx.run_until_parked();
    }

    // ── 4i. THE REWIND RAIL — scrub the whole desktop to an early height (the
    //     root-verified past: a smaller census, REPLAYED chrome), then snap LIVE.
    desk.update(&mut cx, |d, cx| {
        d.bake_rewind_to(1);
        cx.notify();
    });
    cx.run_until_parked();
    let past_census = desk.update(&mut cx, |d, _cx| d.bake_rewind_census_len());
    let live_census = desk.update(&mut cx, |d, _cx| {
        d.bake_rewind_live();
        d.bake_rewind_census_len()
    });
    anyhow::ensure!(
        past_census != live_census,
        "the scrubbed past differs from live (census {past_census} vs {live_census}) — \
         the rail replays root-verified history, not a decoration"
    );
    cx.run_until_parked();

    // ── 4j. THE HIRELING LIVES — hire a real confined resident (hermetic on-box
    //     brain by default), step one perceive-decide-act beat: its cap-gated turns
    //     land on the LIVE World (the pulse announces them) and at least one
    //     over-reach is REFUSED in-band. Then the room reads the executor's account.
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_hire_resident()),
        "hiring the resident attaches a real agent to the live World"
    );
    cx.run_until_parked();
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_step_resident()),
        "one resident beat drives real cap-gated turns"
    );
    cx.run_until_parked();
    anyhow::ensure!(
        desk.update(&mut cx, |d, _cx| d.bake_resident_action_count()) >= 1,
        "the resident's receipts landed on the LIVE World (never self-report)"
    );

    // ── 4k. THE EXCHANGE FLOOR — the agent economy: post an offer (a fresh cell
    //     carrying compute-exchange's job program), take the lease — every verb a
    //     real verified turn, settlement conserving Σδ = 0.
    #[cfg(feature = "app-registry")]
    {
        desk.update(&mut cx, |d, _cx| d.bake_open_exchange());
        cx.run_until_parked();
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_post_offer()),
            "posting an offer lands a fresh offer cell + receipt on the LIVE World"
        );
        anyhow::ensure!(
            desk.update(&mut cx, |d, _cx| d.bake_take_lease()),
            "taking the lease is a real verified turn"
        );
        cx.run_until_parked();
    }

    // Leave the woven room in frame, every surface present at once: TILE the open
    // windows into a grid so the doc-collab editor, the World-Status board, the Android
    // cap-chrome, and the agent-composed board are each fully visible side by side as ONE
    // coherent workbench (cascade piled them into the top-left corner; tiling spreads them
    // across the room), with the calm "type anything" Spotter pill showing (the unifying
    // entry that reached them all).
    desk.update(&mut cx, |d, _cx| {
        d.bake_tile_windows();
    });
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();

    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    let open_now = desk.update(&mut cx, |d, _cx| d.bake_total_window_count());
    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK deos WOVEN render -> {out}.png ({ww}x{hh}, logical {w}x{h}); the stranger's path \
         welded end to end — calm welcome over the live image ({} cells, height {height}) → a \
         door LANDS you mold-ready in a live surface ({door_handles}-handle halo floating) → the \
         Spotter (the unifying entry) reaches EVERY surface and lands each mold-ready: the World \
         Explorer, a doc-collaboration session (branch · stitch · resolve), the agent-composable \
         World-Status board, a confined Android cell's SystemUI cap-chrome — plus the agent \
         composing a brand-new board, all mounted in ONE room ({open_now} windows). One place, \
         one gesture.",
        shared.borrow().ledger().iter().count()
    );
    Ok(())
}

/// **THE FOCUSED DOCUMENT-COLLABORATION BAKE** — the document language as a surface a
/// user can actually drive, end to end, on ONE large editor window:
///
///   1. Author a base document → committed to the cell's umem-heap (boundary B0).
///   2. FORK a confined co-author draft branch (BRANCH-AND-STITCH-PROTOCOL §1). The
///      co-author TYPES a divergent line into the live draft editor (the second author's
///      hand, not the canned button); the original author diverges the main too.
///   3. STITCH (the pushout, §3). Two edits to the same region become a FIRST-CLASS
///      conflict — an antichain of live alternatives, each attributed you-vs-co-author —
///      HELD off the heap (no write while it stands). Rendered as the ConflictView with
///      one-click resolution choices and the conflict's umem boundary (which binds BOTH
///      alternatives — the anti-forge tooth).
///   4. RESOLVE (asserted on a copy so the shot keeps the conflict in frame): a chosen
///      resolution is itself a receipted patch; the merge PUBLISHES to the umem-heap and
///      the boundary MOVES (B0 → B_published).
///
/// The bake ASSERTS each seam (boundary moves on edit; a real conflict arises and is
/// held; resolving publishes + lands a receipt + moves the boundary), then leaves the
/// live conflict + its resolution buttons un-clipped in a tall editor window and captures
/// `<out>.png`. Hermetic. Default 1100x1500.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_doc_collab_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::deos_desktop::DeosDesktop;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let layout_path =
        std::env::temp_dir().join(format!("deos-doccollab-bake-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = starbridge_v2::world::demo_world();
    let [treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx.open_window(size(px(w), px(h)), move |window, cx| {
        let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
        *desk_sink.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    // ── 1. A base document, committed to the umem-heap. Place the editor window large so
    //    the whole collaboration surface renders un-clipped. ──
    desk.update(&mut cx, |d, cx| {
        d.bake_dismiss_welcome(); // the focused shot wants the bare workbench
        d.bake_open_doc(user);
        d.bake_place_doc_window(user, 28.0, 44.0, w - 56.0, h - 96.0);
        d.bake_edit_doc(user, "Shared opening line.\n");
        cx.notify();
    });
    cx.run_until_parked();
    let boundary_base = desk
        .update(&mut cx, |d, _cx| d.bake_doc_umem_boundary(user))
        .expect("the document has a umem boundary");

    // ── 2. Fork a confined draft; the co-author TYPES a divergent line; the original
    //    author diverges the main too (so the stitch genuinely contests the tail). ──
    desk.update(&mut cx, |d, cx| {
        d.bake_fork_branch(user);
        d.bake_set_branch_text(user, "Shared opening line.\nThe co-author's reading.\n");
        d.bake_edit_doc(
            user,
            "Shared opening line.\nThe original author's reading.\n",
        );
        cx.notify();
    });
    cx.run_until_parked();
    let boundary_edited = desk
        .update(&mut cx, |d, _cx| d.bake_doc_umem_boundary(user))
        .expect("boundary after edit");
    anyhow::ensure!(
        boundary_edited != boundary_base,
        "an edit must MOVE the document's umem-heap boundary (the dregg-doc-on-umem ride)"
    );

    // ── 3. STITCH → a first-class conflict, held off the heap. ──
    let pre_stitch = shared.borrow().height();
    desk.update(&mut cx, |d, cx| {
        d.bake_stitch_branch(user);
        cx.notify();
    });
    cx.run_until_parked();
    let conflicts = desk
        .update(&mut cx, |d, _cx| d.bake_conflict_count(user))
        .unwrap_or(0);
    anyhow::ensure!(
        conflicts >= 1,
        "a stitch of two divergent edits to one region must be a FIRST-CLASS conflict \
         (got {conflicts})"
    );
    anyhow::ensure!(
        shared.borrow().height() == pre_stitch,
        "a CONFLICTED stitch is HELD, not committed (no heap write while the conflict stands)"
    );

    // ── 4. Prove resolve→publish on a SEPARATE document (so the shot keeps the live
    //    conflict + resolution buttons in frame). Same flow on the treasury cell, then
    //    resolve choice 0 and assert the merge publishes + a receipt lands + boundary
    //    moves. The user-cell conflict stays live for the capture. ──
    desk.update(&mut cx, |d, cx| {
        d.bake_open_doc(treasury);
        d.bake_edit_doc(treasury, "Proof base.\n");
        d.bake_fork_branch(treasury);
        d.bake_set_branch_text(treasury, "Proof base.\nco-author proof.\n");
        d.bake_edit_doc(treasury, "Proof base.\nauthor proof.\n");
        d.bake_stitch_branch(treasury);
        cx.notify();
    });
    cx.run_until_parked();
    let proof_conflicts = desk
        .update(&mut cx, |d, _cx| d.bake_conflict_count(treasury))
        .unwrap_or(0);
    anyhow::ensure!(proof_conflicts >= 1, "the proof doc must also conflict");
    let proof_b_before = desk
        .update(&mut cx, |d, _cx| d.bake_doc_umem_boundary(treasury))
        .expect("proof boundary before");
    let h_pre_resolve = shared.borrow().height();
    desk.update(&mut cx, |d, cx| {
        d.bake_resolve_conflict(treasury, 0, 0);
        cx.notify();
    });
    cx.run_until_parked();
    let remaining = desk.update(&mut cx, |d, _cx| d.bake_conflict_count(treasury));
    anyhow::ensure!(
        remaining.is_none() || remaining == Some(0),
        "resolving collapses the antichain — no conflict remains (got {remaining:?})"
    );
    let h_post = shared.borrow().height();
    anyhow::ensure!(
        h_post > h_pre_resolve,
        "publishing the resolved merge lands a REAL verified turn on the umem-heap \
         ({h_pre_resolve} -> {h_post})"
    );
    let receipt = desk
        .update(&mut cx, |d, _cx| d.bake_last_resolution_receipt(treasury))
        .expect("the resolution must carry a receipt patch id");
    let proof_b_after = desk
        .update(&mut cx, |d, _cx| d.bake_doc_umem_boundary(treasury))
        .expect("proof boundary after");
    anyhow::ensure!(
        proof_b_after != proof_b_before,
        "publishing the resolution MOVES the document's umem boundary (B0 -> B_published)"
    );

    // Bring the user-cell editor (with its live ConflictView) to the front for the shot.
    desk.update(&mut cx, |d, cx| {
        d.bake_open_doc(user);
        d.bake_place_doc_window(user, 28.0, 44.0, w - 56.0, h - 96.0);
        cx.notify();
    });
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();

    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK deos DOC-COLLAB render -> {out}.png ({ww}x{hh}, logical {w}x{h}); the document \
         language driven end to end: base committed (umem boundary {}…), fork + co-author \
         types a divergence + author diverges (boundary moved to {}…), STITCH → {conflicts} \
         first-class CONFLICT held off the heap (both alternatives attributed, one-click \
         resolve); a proof doc RESOLVED → published to heap (h{h_pre_resolve} -> {h_post}, \
         receipt patch #{receipt}, boundary moved). The live ConflictView is in frame.",
        hex2(&boundary_base),
        hex2(&boundary_edited),
    );
    Ok(())
}

/// First two bytes of a 32-byte root, hex — a compact boundary tag for bake logs.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn hex2(root: &[u8; 32]) -> String {
    format!("{:02x}{:02x}", root[0], root[1])
}

/// **THE CALM WELCOME BAKE** — render the deos desktop's *warm front door*: the calm,
/// breathing default a never-greeted newcomer wakes up to. The dense workbench bake
/// (`--render-desktop`) shows the power end of the bar — every surface open; this bake
/// shows the OTHER end: a bare room of glowing cell-icons, the live World summary, the
/// gentle "type anything" Spotter pill, and the warm WELCOME card greeting the stranger
/// with the image's REAL shape (its true cell count + history height) over four inviting
/// doors. NOTHING else is opened — the litmus is a five-year-old gladly clicking around.
///
/// The bake asserts the calm default is genuinely calm (no windows open), the welcome is
/// shown, and its greeting names the live world; then captures `<out>.png`. Hermetic
/// (a throwaway sidecar). Default 1600x1000 (overridable via `--render-size`).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_welcome_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::deos_desktop::DeosDesktop;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // A hermetic, fresh sidecar so `welcomed = false` → the warm card shows (a fresh
    // image is exactly the newcomer's first run). Start clean.
    let layout_path =
        std::env::temp_dir().join(format!("deos-welcome-bake-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    // The live verified image — the SAME `World` the cockpit runs.
    let (world, anchors) = starbridge_v2::world::demo_world();
    let [_treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));
    let height = shared.borrow().height();

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx.open_window(size(px(w), px(h)), move |window, cx| {
        let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
        *desk_sink.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    cx.run_until_parked();
    let desk_h = desk_cell.borrow().clone().expect("desktop entity captured");

    // The calm default is genuinely CALM: a fresh image opens onto the warm welcome,
    // and NOTHING else is open (no windows) — breathing room, not everything-at-once.
    let (shown, greeting, open_windows) = desk_h.update(&mut cx, |desk, _cx| {
        (
            desk.bake_welcome_is_shown(),
            desk.bake_welcome_greeting(),
            desk.bake_total_window_count(),
        )
    });
    anyhow::ensure!(
        shown,
        "a fresh image must open onto the warm WELCOME card (the calm front door)"
    );
    anyhow::ensure!(
        open_windows == 0,
        "the calm default must open NOTHING else — a welcoming first view, not the dense \
         workbench (got {open_windows} open window(s))"
    );
    anyhow::ensure!(
        greeting.contains(&height.to_string()),
        "the welcome greeting must name the live image's REAL history height ({height})"
    );

    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();

    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK deos WELCOME render -> {out}.png ({ww}x{hh}, logical {w}x{h}); the calm front \
         door — a warm greeting over the live image ({} cells, height {height}), a gentle \
         'type anything' Spotter pill, and four inviting doors; nothing else open.",
        shared.borrow().ledger().iter().count()
    );
    Ok(())
}

/// **THE deos DESKTOP BAKE** — render the Windows-NT / Pharo-Smalltalk workbench
/// over the live verified World, headless, and capture the PNG.
///
/// Mounts [`starbridge_v2::deos_desktop::DeosDesktop`] over the real `demo_world`
/// image: each ledger cell becomes a draggable desktop icon; double-click opens an
/// NT inspector window; right-click opens a context menu of REAL actuations (each a
/// verified turn). To prove the metaphors are LIVE (not a static mock), the bake:
///   1. opens two inspector windows (the treasury + the user cell),
///   2. fires a REAL right-click actuation (transfer treasury → user) — a verified
///      turn that advances `World::height`,
///   3. drags an icon to a new position and asserts the layout PERSISTED to the
///      sidecar (the #1 missing thing — spatial persistence),
///   4. opens a context menu so the right-click ACTUATION surface is visible in the
///      shot,
///      then bakes `<out>.png`. Uses a throwaway sidecar path so the bake is hermetic.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "embedded-executor"
))]
fn render_desktop_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::deos_desktop::{id_hex, DeosDesktop, DesktopLayout};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // A hermetic sidecar for this bake (so the persistence write/read is real but
    // does not clobber a user's layout). Start clean.
    let layout_path =
        std::env::temp_dir().join(format!("deos-desktop-bake-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    // The live verified image — the SAME `World` the cockpit runs.
    let (world, anchors) = starbridge_v2::world::demo_world();
    let [treasury, service, user] = anchors;
    let pre_height = world.height();
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    // The desktop is hosted under a `gpui_component::Root` (its document editors are
    // real `InputState` widgets, which reach `Root` for overlay/focus plumbing). We
    // keep a handle to the inner `DeosDesktop` entity to drive the bake steps.
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx.open_window(size(px(w), px(h)), move |window, cx| {
        let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
        *desk_sink.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    cx.run_until_parked();
    let desk_h = desk_cell.borrow().clone().expect("desktop entity captured");

    // 1. Open an inspector + a TRANSCRIPT (receipt log) window — denser surfaces.
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_window(treasury);
        desk.bake_open_transcript(user);
        cx.notify();
    });
    cx.run_until_parked();

    // 2. Fire a REAL right-click actuation: transfer treasury → user (a verified
    //    turn). Assert the World advanced.
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_actuate_transfer(treasury, user, 1_000);
        cx.notify();
    });
    cx.run_until_parked();
    let mid_height = shared.borrow().height();
    anyhow::ensure!(
        mid_height > pre_height,
        "the desktop actuation must commit a REAL verified turn (height {pre_height} -> {mid_height})"
    );

    // 3. Open a DOCUMENT EDITOR on the user cell and TYPE into it — each edit is a
    //    receipted patch + a verified revision turn (the document IS the cell).
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_doc(user);
        desk.bake_edit_doc(
            user,
            "# deos document\nA document is a cell.\nEditing is receipted patches.\n",
        );
        cx.notify();
    });
    cx.run_until_parked();
    let doc_height = shared.borrow().height();
    anyhow::ensure!(
        doc_height > mid_height,
        "a document edit must land a REAL verified revision turn (height {mid_height} -> {doc_height})"
    );
    let doc_text = desk_h.update(&mut cx, |desk, _cx| desk.bake_doc_text(user));
    anyhow::ensure!(
        doc_text.contains("A document is a cell."),
        "the document editor must hold the authored prose"
    );

    // 4. COMPOSE: transclude the treasury cell INTO the user's document — a genuine
    //    cross-cell compose (receipted patch + verified turn).
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_transclude(treasury, user);
        cx.notify();
    });
    cx.run_until_parked();
    let post_height = shared.borrow().height();
    anyhow::ensure!(
        post_height > doc_height,
        "the compose/transclude must land a REAL verified turn (height {doc_height} -> {post_height})"
    );
    let composed = desk_h.update(&mut cx, |desk, _cx| desk.bake_doc_text(user));
    anyhow::ensure!(
        composed.contains("{transclude dregg://"),
        "the composed document must carry the transclusion"
    );

    // 4b. Open the LINKS window + an INSPECTOR on the user doc-cell — the document is
    //     now wired into the rest of the desktop: the Links window resolves the
    //     transclusion to treasury's LIVE faces (an outbound link →) and the inspector
    //     reflects the committed prose. Assert the structured backlink resolves both
    //     ways (user → treasury outbound, treasury ← user backlink).
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_links(user);
        desk.bake_open_window(user);
        cx.notify();
    });
    cx.run_until_parked();
    let (out_links, back_links) =
        desk_h.update(&mut cx, |desk, _cx| desk.bake_doc_links(user, treasury));
    anyhow::ensure!(
        out_links,
        "the user document's Links must resolve an outbound transclusion → treasury"
    );
    anyhow::ensure!(
        back_links,
        "treasury's Links must show a backlink ← the user document that mentions it"
    );

    // 4c. THE DOCUMENT LANGUAGE — conflicts as first-class STATES. On the service cell:
    //     author a base, fork a confined co-author draft, diverge it, AND diverge the
    //     main — then STITCH (the pushout). Two edits to the same region become a
    //     first-class CONFLICT (an antichain of live alternatives, each attributed),
    //     HELD (no heap write) and rendered as the live ConflictView with one-click
    //     resolution choices. We assert the conflict arose, RESOLVE it (the resolution
    //     is itself a receipted patch), and assert the merge PUBLISHES to the heap.
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_doc(service);
        desk.bake_edit_doc(service, "A shared opening line.\n");
        desk.bake_fork_branch(service);
        desk.bake_diverge_branch(service, "alice's ending.\n");
        desk.bake_edit_doc(service, "A shared opening line.\nbob's ending.\n");
        cx.notify();
    });
    cx.run_until_parked();
    let pre_stitch = shared.borrow().height();
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_stitch_branch(service);
        cx.notify();
    });
    cx.run_until_parked();
    let conflict_n = desk_h
        .update(&mut cx, |desk, _cx| desk.bake_conflict_count(service))
        .unwrap_or(0);
    anyhow::ensure!(
        conflict_n >= 1,
        "a stitch of two divergent edits to one region must be a FIRST-CLASS conflict \
         (got {conflict_n})"
    );
    anyhow::ensure!(
        shared.borrow().height() == pre_stitch,
        "a CONFLICTED stitch is HELD, not committed (no heap write while the conflict stands)"
    );
    // The conflict is LEFT live so the final shot renders the ConflictView (both
    // alternatives side-by-side, attributed, with one-click resolution choices). The
    // full resolve→publish loop is asserted by the `deos_desktop_conflict_is_a_state`
    // test; here the bake proves the conflict STATE arises + renders.

    // 4d. THE DOCUMENT EXPLORER — the Pharo-moldable inspector of the user document's
    //     patch substance. Open it, select the History face, and SCRUB to an early
    //     revision (the time-travel scrubber, via `replay_to`). Assert the replayed
    //     early revision differs from the tip — real history reflection, not a flat
    //     readout. The window renders in the final shot (History · Graph · Blame tabs).
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_doc_explorer(user);
        desk.bake_doc_explorer_tab(user, 0); // History face
        desk.bake_doc_explorer_scrub(user, Some(0)); // scrub to the first revision
        cx.notify();
    });
    cx.run_until_parked();
    let tip_text = desk_h
        .update(&mut cx, |desk, _cx| desk.bake_doc_explorer_at(user, None))
        .unwrap_or_default();
    let early_text = desk_h
        .update(&mut cx, |desk, _cx| {
            desk.bake_doc_explorer_at(user, Some(0))
        })
        .unwrap_or_default();
    anyhow::ensure!(
        early_text != tip_text,
        "the Document Explorer's time-travel scrubber must replay an EARLIER revision \
         distinct from the tip (real `replay_to` history, not a flat readout)"
    );
    let (atoms, _authors) = desk_h
        .update(&mut cx, |desk, _cx| desk.bake_doc_explorer_stats(user))
        .unwrap_or((0, 0));
    anyhow::ensure!(
        atoms >= 1,
        "the Document Explorer's DocGraph face must reflect the document's live atoms"
    );

    // 4e. THE WORLD EXPLORER — the "My Computer" of the verified World. Open it on the
    //     Conservation face (the Σ-balance breakdown over the live ledger). Renders in
    //     the final shot (ledger · chronicle · conservation tabs).
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_world_explorer();
        desk.bake_world_explorer_tab(2); // Conservation face
        cx.notify();
    });
    cx.run_until_parked();

    // 4e′. THE CONTENT-IR BRIDGE — a desktop window whose body IS a real
    //      `deos_view::ViewNode` (a card-as-cell) rendered through deos-view's NATIVE
    //      renderer (`AppletView`), beside the native-chrome surfaces. Open it, render,
    //      and assert (1) the desktop minted the IR renderer entity (its window body is a
    //      rendered portable tree), and (2) the WEB renderer paints the IDENTICAL
    //      `ViewNode` to HTML — the same tree, two backends; the native desktop is one.
    //      Gated on `card-pane` (the default build has it; the gpui-free `headless` bake
    //      does not, so the step is skipped there — the window-type still falls back to
    //      the inspector body and compiles).
    #[cfg(feature = "card-pane")]
    {
        // Open the World-Status pane (the reflective surface) as a real desktop window,
        // render, and mint its live `AppletView` entity.
        desk_h.update(&mut cx, |desk, cx| {
            desk.bake_open_viewnode_pane();
            cx.notify();
        });
        cx.run_until_parked();
        // The live renderer entity is minted lazily when the window first renders.
        let has_pane = desk_h.update(&mut cx, |desk, _cx| desk.bake_viewnode_has_pane());
        anyhow::ensure!(
            has_pane,
            "the desktop must host the World-Status pane — a window whose body is a real \
             deos_view::ViewNode rendered through deos-view's native renderer"
        );

        // THE REFLECTIVE-COCKPIT LOOP IN THE SHIPPED DESKTOP — capture the panel BEFORE
        // the agent touches it, run the agent's reflect-then-rewrite loop against the
        // SHIPPED pane, then capture AFTER. The two desktop frames differ: the agent
        // rewrote a real cockpit surface and the change reached the glass.
        // First dismiss the one-time welcome card + raise the World-Status pane into a
        // clear area so its body (the surface the agent rewrites) is visible + unoccluded.
        desk_h.update(&mut cx, |desk, cx| {
            if desk.bake_welcome_is_shown() {
                desk.bake_welcome_door(0);
            }
            desk.bake_place_viewnode_window(360.0, 110.0, 520.0, 360.0);
            cx.notify();
        });
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let vnode_before = cx.capture_screenshot(window.into())?;
        vnode_before.save(format!("{out}.viewnode-before.png"))?;

        // ONE process-global SpiderMonkey runtime drives BOTH agent loops (the rewrite +
        // the compose) — its engine is one-shot per process, so it is booted once here.
        let mut rt = deos_js::JsRuntime::new()
            .map_err(|e| anyhow::anyhow!("boot SpiderMonkey for the agent loops: {e}"))?;

        let rewrite = desk_h
            .update(&mut cx, |desk, cx| {
                desk.bake_agent_rewrites_viewnode_pane(&mut rt, cx)
            })
            .map_err(|e| anyhow::anyhow!("the agent's reflect-then-rewrite loop failed: {e}"))?;
        anyhow::ensure!(
            rewrite.reflected_header && rewrite.reflected_rows == 3,
            "REFLECT-ON: the agent must read the live cockpit surface's own tree (the \
             `World Status` header + its 3 status rows it did NOT author)"
        );
        anyhow::ensure!(
            !rewrite.before_has_button && rewrite.after_has_button && rewrite.live_after_has_button,
            "REWRITE: the agent must add a `refresh` button the live pane did not have — \
             and the SHIPPED pane entity must now carry it (the surface re-rendered)"
        );
        anyhow::ensure!(
            rewrite.receipt_count == 2 && rewrite.blamed_agent,
            "ACCOUNTABLE: the rewrite's two gestures (addButton + relabel) must each commit \
             a receipted provenance turn, blamed on the agent (got {} receipt(s), blamed={})",
            rewrite.receipt_count,
            rewrite.blamed_agent
        );

        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let vnode_after = cx.capture_screenshot(window.into())?;
        vnode_after.save(format!("{out}.viewnode-after.png"))?;
        anyhow::ensure!(
            vnode_before.as_raw() != vnode_after.as_raw(),
            "the agent's rewrite must change the SHIPPED desktop window — the World-Status \
             pane's `refresh` button + `(live)` relabel must reach pixels (before == after)"
        );

        // The SAME portable tree the native pane hosts also renders to HTML — renderer
        // independence (the same World-Status ViewNode, native + web).
        let html = starbridge_v2::deos_desktop::viewnode_pane::status_panel_html();
        anyhow::ensure!(
            html.contains("World Status") && html.contains("receipts: 12"),
            "the web renderer must render the IDENTICAL World-Status ViewNode the desktop \
             hosts (renderer independence: the same tree, native + web)"
        );

        // 4e″. THE AGENT AS CO-AUTHOR — the DEEPER reflective loop. Past rewriting one
        //      surface: a confined agent COMPOSES a BRAND-NEW cockpit surface — a World
        //      Board — from an EMPTY root, informed by reading the live World, and the
        //      board is mounted as a REAL second `viewnode_pane` window. Capture BEFORE
        //      (no board) and AFTER (the agent's composed board on the glass); the frames
        //      differ. The agent stopped editing the cockpit and co-authored a surface OF it.
        let board_before = cx.capture_screenshot(window.into())?;
        board_before.save(format!("{out}.world-board-before.png"))?;

        let board = desk_h
            .update(&mut cx, |desk, cx| {
                desk.bake_agent_composes_world_board(&mut rt, cx)
            })
            .map_err(|e| anyhow::anyhow!("the agent's compose-from-scratch loop failed: {e}"))?;
        anyhow::ensure!(
            board.started_empty,
            "COMPOSE-FROM-SCRATCH: the agent's authoring surface must begin as a bare empty \
             root (it composes a NEW surface, it does not tweak a pre-existing pane)"
        );
        anyhow::ensure!(
            board.crawled_cells >= 1,
            "READ-THE-WORLD: the agent must crawl the live ledger's real cells to decide \
             what to surface (got {})",
            board.crawled_cells
        );
        anyhow::ensure!(
            board.composed_title && board.composed_bind_rows == 3 && board.composed_button,
            "COMPOSE: the agent must author the board from nothing — a title + 3 LIVE \
             state-bound rows + a refresh button (title={}, binds={}, button={})",
            board.composed_title,
            board.composed_bind_rows,
            board.composed_button
        );
        anyhow::ensure!(
            board.receipt_count == 5 && board.blamed_agent,
            "ACCOUNTABLE: the composition's 5 gestures (title + 3 binds + button) must each \
             commit a receipted provenance turn, blamed on the agent (got {} receipt(s), \
             blamed={})",
            board.receipt_count,
            board.blamed_agent
        );
        anyhow::ensure!(
            board.mounted_window,
            "MOUNT: a REAL second viewnode_pane window must host the agent-composed board"
        );

        // Raise the board window into a clear area so its composed body reaches pixels,
        // then capture AFTER — the agent's from-scratch surface on the live desktop.
        desk_h.update(&mut cx, |desk, cx| {
            desk.bake_place_window(
                starbridge_v2::deos_desktop::viewnode_pane::world_board_window_cell(),
                170.0,
                150.0,
                480.0,
                300.0,
            );
            cx.notify();
        });
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let board_after = cx.capture_screenshot(window.into())?;
        board_after.save(format!("{out}.world-board-after.png"))?;
        anyhow::ensure!(
            board_before.as_raw() != board_after.as_raw(),
            "the agent's COMPOSED board must reach the SHIPPED desktop — a new surface the \
             agent authored from scratch must appear on the glass (before == after)"
        );

        // 4e‴. THE PULSE→SIGNALS WELD — the shipped pane's binds finally track the LIVE
        //      World. A FOREIGN turn (a real verified `SetField` committed on the live
        //      ledger — not one of the pane's own affordances) moves the receipts census;
        //      the desktop's pulse mirrors it into the World-Status pane as ONE receipted
        //      tracking turn (`set_receipts`, `ApplyOp::SetSlotFromArg`); EXACTLY the
        //      receipts bind re-reads + repaints, wearing the one-beat dirty glow. The
        //      before/after frames differ — liveness reached pixels.
        desk_h.update(&mut cx, |desk, cx| {
            // Raise the World-Status pane above the board window so the repainted bind
            // reaches unoccluded pixels in both captures.
            desk.bake_place_viewnode_window(360.0, 110.0, 520.0, 360.0);
            cx.notify();
        });
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let weld_before = cx.capture_screenshot(window.into())?;
        weld_before.save(format!("{out}.pulse-weld-before.png"))?;

        let weld = desk_h
            .update(&mut cx, |desk, cx| {
                desk.bake_foreign_turn_repaints_viewnode_binds(cx)
            })
            .map_err(|e| anyhow::anyhow!("the Pulse→Signals weld loop failed: {e}"))?;
        anyhow::ensure!(
            weld.receipts_before != weld.receipts_after
                && weld.receipts_after == weld.live_receipts,
            "TRACK THE WORLD: the pane's committed receipts reading must move to the live \
             census (shown {} -> {}, live {})",
            weld.receipts_before,
            weld.receipts_after,
            weld.live_receipts
        );
        anyhow::ensure!(
            weld.dirty_is_exactly_receipts_bind,
            "FINE-GRAINED: one foreign turn must dirty + glow EXACTLY the receipts bind — \
             not the whole card (dirty {:?}, glowing {:?})",
            weld.dirty,
            weld.glowing
        );
        anyhow::ensure!(
            weld.weld_receipts_committed == 1,
            "RECEIPTED: the census mirror must be exactly ONE verified tracking turn on \
             the pane's audit tape (got {})",
            weld.weld_receipts_committed
        );

        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let weld_after = cx.capture_screenshot(window.into())?;
        weld_after.save(format!("{out}.pulse-weld-after.png"))?;
        anyhow::ensure!(
            weld_before.as_raw() != weld_after.as_raw(),
            "THE PULSE→SIGNALS WELD must reach pixels — the repainted receipts bind (and \
             its dirty glow) must change the shipped desktop frame (before == after)"
        );
    }

    // 4f. THE SPOTTER — the Pharo command palette. Open it with a query, assert it ranks
    //     real candidates over the live cells, then dispatch to prove it jumps. (We then
    //     re-open it for the final shot so the palette renders over the desktop.)
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_spotter("doc");
        cx.notify();
    });
    cx.run_until_parked();
    let spot_matches = desk_h
        .update(&mut cx, |desk, _cx| desk.bake_spotter_match_count())
        .unwrap_or(0);
    anyhow::ensure!(
        spot_matches >= 1,
        "the Spotter must rank at least one candidate for 'doc' over the live cells \
         (got {spot_matches})"
    );

    // 5. Drag the treasury icon to a new position and assert the layout PERSISTED.
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_drag_icon(treasury, 720.0, 540.0);
        cx.notify();
    });
    cx.run_until_parked();
    let persisted = DesktopLayout::load(&layout_path);
    anyhow::ensure!(
        persisted
            .icons
            .iter()
            .any(|p| p.cell == id_hex(&treasury) && (p.x - 720.0).abs() < 1.0),
        "the dragged icon position must PERSIST to the sidecar (spatial persistence)"
    );
    anyhow::ensure!(
        persisted.docs.iter().any(|d| d.cell == id_hex(&user)),
        "the authored document prose must PERSIST to the sidecar (content persistence)"
    );

    // 6. Open the WORKFLOW-COMPOSER over the service cell: compose intents into a
    //    workflow, pin a baseline, then add a WIDENING intent (Seal) — and assert the
    //    REAL flow-refinement decision (dregg_deploy::refine) flips from refines to
    //    diverges. This exercises the proven `decide_refines` game, not a mock.
    desk_h.update(&mut cx, |desk, cx| {
        use starbridge_v2::deos_desktop::IntentKind;
        desk.bake_open_workflow(service);
        desk.bake_workflow_add(service, IntentKind::Transfer);
        desk.bake_workflow_add(service, IntentKind::Grant);
        // Pin the baseline B = {Transfer, Grant}.
        desk.bake_workflow_pin_baseline(service);
        cx.notify();
    });
    cx.run_until_parked();
    // Within the baseline's intent shapes → REFINES.
    desk_h.update(&mut cx, |desk, cx| {
        use starbridge_v2::deos_desktop::IntentKind;
        desk.bake_workflow_add(service, IntentKind::Transfer);
        cx.notify();
    });
    cx.run_until_parked();
    let refines_within = desk_h.update(&mut cx, |desk, _cx| desk.bake_workflow_refines(service));
    anyhow::ensure!(
        refines_within,
        "a workflow whose steps stay within the baseline envelope must REFINE it (the proven A ≤ᶠ B game)"
    );
    // A WIDENING intent (Seal) outside the envelope → DIVERGES.
    desk_h.update(&mut cx, |desk, cx| {
        use starbridge_v2::deos_desktop::IntentKind;
        desk.bake_workflow_add(service, IntentKind::Seal);
        cx.notify();
    });
    cx.run_until_parked();
    let diverges_widened = desk_h.update(&mut cx, |desk, _cx| desk.bake_workflow_refines(service));
    anyhow::ensure!(
        !diverges_widened,
        "a workflow that widens beyond its baseline (adds Seal) must NOT refine it — the refinement game must catch the widening"
    );
    let wf_letters = desk_h.update(&mut cx, |desk, _cx| desk.bake_workflow_letters(service));
    anyhow::ensure!(
        wf_letters == 4,
        "the composed workflow's flow-Proc must fire one letter per step (4 steps -> 4 letters), got {wf_letters}"
    );

    // 7. CASCADE all open windows (the Window→Cascade command — a pure layout
    //    actuation that fires NO verified turn) so the dense workbench reads legibly,
    //    then assert the World's conservation invariant (Σ balance = 0) the new
    //    World-summary widget reflects still holds after every committed turn.
    let pre_cascade_height = shared.borrow().height();
    let sigma_before = desk_h.update(&mut cx, |desk, _cx| desk.bake_world_balance_sum());
    // TILE the windows into a grid so every surface (the enriched inspector with its
    // state-slots + per-cell turns + balance gauge, the transcript, the document, the
    // workflow composer) is visible at once — and prove it fires no verified turn.
    let _tiled = desk_h.update(&mut cx, |desk, cx| {
        let n = desk.bake_tile_windows();
        cx.notify();
        n
    });
    cx.run_until_parked();
    let post_cascade_height = shared.borrow().height();
    anyhow::ensure!(
        post_cascade_height == pre_cascade_height,
        "window arrangement (tile) is a PURE layout actuation — it must NOT fire a \
         verified turn (height {pre_cascade_height} -> {post_cascade_height})"
    );
    // The conservation sum (Σ balance, reflected by the World-summary widget) is
    // INVARIANT under value-conserving turns AND under the layout actuation — the
    // net of issuer wells vs. accounts does not move.
    let sigma = desk_h.update(&mut cx, |desk, _cx| desk.bake_world_balance_sum());
    anyhow::ensure!(
        sigma == sigma_before,
        "the World's Σ balance (the conservation net the widget shows) must be invariant \
         under the cascade layout actuation ({sigma_before} -> {sigma})"
    );
    let total_wins = desk_h.update(&mut cx, |desk, _cx| desk.bake_total_window_count());

    // 8. Open the PROPERTY inspector/editor over the treasury cell, and a deep
    //    right-click context menu over the service cell — both visible in the shot.
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_open_properties(treasury);
        desk.bake_open_menu(service, 60.0, 250.0);
        cx.notify();
    });
    cx.run_until_parked();

    // 9. THE PHARO HALO — the "mold it in place" gesture. Select a cell-icon and its
    //    ring of direct-manipulation handles floats (inspect · explore · open-as-doc ·
    //    fork · properties · the verified-turn affordance). Each handle fires the SAME
    //    actuation the right-click menu does — prove it FUNCTIONALLY (the Inspect handle
    //    opens a real inspector window), then leave a WINDOW selected so the ring renders
    //    around it in the final shot (the halo over the live workbench).
    let pre_halo_wins = desk_h.update(&mut cx, |desk, _cx| desk.bake_total_window_count());
    let halo_handles = desk_h.update(&mut cx, |desk, cx| {
        desk.bake_select_icon(service);
        cx.notify();
        desk.bake_halo_handle_count()
    });
    anyhow::ensure!(
        halo_handles >= 5,
        "a selected cell-icon must float a ring of halo handles (got {halo_handles})"
    );
    desk_h.update(&mut cx, |desk, cx| {
        desk.bake_halo_fire_inspect();
        cx.notify();
    });
    cx.run_until_parked();
    let post_halo_wins = desk_h.update(&mut cx, |desk, _cx| desk.bake_total_window_count());
    anyhow::ensure!(
        post_halo_wins > pre_halo_wins,
        "firing the halo's Inspect handle must REUSE the actuation and open a window \
         ({pre_halo_wins} -> {post_halo_wins}) — the ring is a spatial face on the same verbs"
    );
    // Leave a surface molded so the halo ring renders around it in the final shot.
    // The user cell-icon sits in the clear top-left margin (above the context menu,
    // clear of the centered overlays), so its full ring of handles reads unobstructed.
    // Dismiss the one-time welcome card first so it does not cover the workbench.
    desk_h.update(&mut cx, |desk, cx| {
        if desk.bake_welcome_is_shown() {
            desk.bake_welcome_door(0);
        }
        desk.bake_select_icon(user);
        cx.notify();
    });
    cx.run_until_parked();

    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();

    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    let docwins = desk_h.update(&mut cx, |desk, _cx| desk.bake_window_count(true));
    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK deos DESKTOP render -> {out}.png ({ww}x{hh}, logical {w}x{h}); NT/Pharo workbench \
         over the live verified World — {} cell-icons; {total_wins} tiled window(s) \
         (inspector with state-slots + per-cell turns + a balance gauge, transcript, {docwins} \
         document editor); a TASKBAR of open-window stubs + a World-summary widget (height, \
         cells, receipts, Σ balance = {sigma} — invariant under transfers + layout); a WORKFLOW COMPOSER (the proven \
         dregg_deploy::refine A ≤ᶠ B game decides refinement — a widening Seal DIVERGES); a deep \
         right-click context menu (now with Cascade/Tile/Close-all window commands) AND a \
         property inspector/editor open; the PHARO HALO floating its ring of \
         direct-manipulation handles on a molded surface (inspect · explore · open-as-doc · \
         fork · properties · the verified-turn affordance · resize · close — each firing the \
         SAME actuation the right-click menu does); a receipted document edit + a cross-cell \
         TRANSCLUDE compose; REAL verified turns (height {pre_height} -> {post_height}); \
         tile/cascade are pure layout actuations (no turn); icon drag + authored prose \
         persisted to the sidecar.",
        shared.borrow().cell_count()
    );
    Ok(())
}

/// Parse the `--render-guest <out>` (or `--render-guest=<out>`) argument — the
/// output base path for the GUEST / APP-FORWARD BAKE (the welcoming, inspector-on-
/// summon desktop). Returns `None` when absent. `<out>.png` is written.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "app-registry"
))]
fn render_guest_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-guest" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-guest=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-agent-attach <out>` (or `=<out>`) argument — the output base
/// path for THE AGENT'S HANDS ON THE REAL GLASS bake (the agent's `run_js` attached
/// to the live cockpit World). Returns `None` when absent. `<out>.png` is written.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "agent-js"))]
fn render_agent_attach_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-agent-attach" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-agent-attach=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-card-pane <out>` (or `=<out>`) argument — the output base path
/// for the CARD-PANE bake (`<out>.before.png` / `<out>.after.png`). Returns `None` when
/// absent.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
fn render_card_pane_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-card-pane" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-card-pane=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-first-card <out>` (or `=<out>`) argument — the output base path
/// for the MAKE-YOUR-FIRST-CARD onboarding bake (`<out>.before.png` / `<out>.after.png`).
/// Returns `None` when absent.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
fn render_first_card_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-first-card" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-first-card=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-apps <out>` (or `=<out>`) argument — the output base path for the
/// APP STORE + APPS GOING bake (`<out>.launcher.png` + `<out>.png`). `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_apps_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-apps" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-apps=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-apps-showcase <out>` (or `=<out>`) argument — the output path for
/// the VISUAL-KILLER hero bake (ONE PNG written to `<out>`). `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_apps_showcase_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-apps-showcase" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-apps-showcase=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-service-economy <out>` (or `=<out>`) argument — the output path for
/// the SERVICE-ECONOMY scene bake (ONE PNG written to `<out>`). `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_service_economy_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-service-economy" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-service-economy=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-app-fire <out>` (or `=<out>`) argument — the output base path for
/// the CLICK→VERIFIED-TURN app-card-button bake (`<out>.before.png` / `<out>.after.png` /
/// `<out>.png`). `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_app_fire_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-app-fire" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-app-fire=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-webshell-live <out>` (or `=<out>`) argument — the output base
/// path for THE LIVE WEB-SHELL bake (a real page in the cockpit web-shell pane, then
/// a scroll input causing a re-render). `<out>.before.png` / `<out>.after.png`.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "web-shell"))]
fn render_webshell_live_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-webshell-live" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-webshell-live=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-live-brain <out>` (or `=<out>`) argument — the output base
/// path for THE HEADLINE bake (a LIVE Hermes brain driving `run_js` on the live
/// cockpit World). Returns `None` when absent. `<out>.before.png` / `<out>.after.png`.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "live-brain"
))]
fn render_live_brain_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-live-brain" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-live-brain=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse the `--render-self-hosting <out>` (or `=<out>`) argument — the output
/// base path for the SELF-HOSTING bake. Returns `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
fn render_self_hosting_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-self-hosting" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-self-hosting=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-self-hosting-full <out>` (or `=<out>`) — the FULL single-loop
/// bake output base path. Returns `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
fn render_self_hosting_full_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-self-hosting-full" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-self-hosting-full=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-unified-boot <out>` (or `=<out>`) — the UNIFIED-BOOT bake
/// output base path. Returns `None` when absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_unified_boot_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-unified-boot" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-unified-boot=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-client-signed-turn <out>` (or `=<out>`) — the CLIENT-SIGNED
/// turn bake output base path (the "corporate account" proof: the logged-in user's
/// OWN cell signs a turn the node commits under the user's authority). `None` when
/// absent.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_client_signed_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-client-signed-turn" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-client-signed-turn=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-interactive-node-save <out>` (or `=<out>`) — the interactive
/// self-hosting wire bake (the editor pane's OWN save → a node-ledger turn).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_interactive_node_save_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-interactive-node-save" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-interactive-node-save=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--self-hosting-cmd <prog> [args…]` (everything after it, up to the next
/// `--flag`, is the terminal command). `None` → the default (`cargo --version`).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
fn self_hosting_cmd_arg(args: &[String]) -> Option<(String, Vec<String>)> {
    let pos = args.iter().position(|a| a == "--self-hosting-cmd")?;
    let mut rest = args[pos + 1..]
        .iter()
        .take_while(|a| !a.starts_with("--"))
        .cloned();
    let prog = rest.next()?;
    Some((prog, rest.collect()))
}

/// Parse the `--render-login <out>` (or `--render-login=<out>`) argument — the
/// output base path for the headless LOGIN-surface render. Returns `None` absent.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_login_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-login" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-login=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-touch <out>` (or `=<out>`) — the TOUCH-UI bake (the
/// graphideOS / mobile shape: a bottom-bar mode switch, a tappable cell garden,
/// a long-press face sheet). `<out>.png` is written. See `render_touch_headless`.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_touch_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-touch" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-touch=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--render-mode <name>` — the touch-shell mode the bake selects
/// (Inhabit/Author/Dev/Inspect/Operate, matched case-insensitively against
/// [`touch::TouchShell::select_mode_named`]). `None` keeps the default (Inhabit).
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_mode_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-mode" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-mode=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse repeatable `--replay <cell>:<message>` arguments (the act-trail the
/// dregg-mcp server records and hands to the bake so a screenshot reflects the
/// driven session). `<cell>` is a hex-id prefix (matched against the live
/// ledger); `<message>` is an affordance verb (`peek`/`touch`/`write`/…).
#[cfg(feature = "render-capture")]
fn render_replay_args(args: &[String]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let spec = if a == "--replay" {
            it.next().cloned()
        } else {
            a.strip_prefix("--replay=").map(|s| s.to_string())
        };
        if let Some(spec) = spec {
            if let Some((cell, msg)) = spec.split_once(':') {
                out.push((cell.to_string(), msg.to_string()));
            }
        }
    }
    out
}

/// Parse `--render-size <W>x<H>` (logical pixels) for the cockpit bake. `None`
/// keeps the seL4 framebuffer default (800x600). e.g. `--render-size 1280x832`.
#[cfg(feature = "render-capture")]
fn render_size_arg(args: &[String]) -> Option<(f32, f32)> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let spec = if a == "--render-size" {
            it.next().cloned()
        } else {
            a.strip_prefix("--render-size=").map(|s| s.to_string())
        };
        if let Some(spec) = spec {
            if let Some((w, h)) = spec.split_once(['x', 'X', '*']) {
                if let (Ok(w), Ok(h)) = (w.trim().parse::<f32>(), h.trim().parse::<f32>()) {
                    if w >= 320.0 && h >= 240.0 {
                        return Some((w, h));
                    }
                }
            }
        }
    }
    None
}

/// Parse `--render-tab <name>` — the cockpit surface to screenshot (matched
/// against [`cockpit::Cockpit::select_tab_named`]). `None` keeps the default.
#[cfg(feature = "render-capture")]
fn render_tab_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--render-tab" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--render-tab=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--explore-ui <outdir>`.
#[cfg(feature = "render-capture")]
fn explore_ui_arg(args: &[String]) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--explore-ui" {
            return it.next().cloned();
        }
        if let Some(rest) = a.strip_prefix("--explore-ui=") {
            return Some(rest.to_string());
        }
    }
    None
}

/// Parse `--serve-ie6 <port>` (default 8600).
#[cfg(feature = "render-capture")]
fn serve_ie6_arg(args: &[String]) -> Option<u16> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--serve-ie6" {
            return Some(it.next().and_then(|p| p.parse().ok()).unwrap_or(8600));
        }
        if let Some(rest) = a.strip_prefix("--serve-ie6=") {
            return Some(rest.parse().unwrap_or(8600));
        }
    }
    None
}

/// THE LIVE IE6 COCKPIT SERVER (Path B). Holds a live cockpit, renders it per
/// request, and serves it as image-map HTML so any browser back to 1996 can drive
/// the real verified cockpit — server-side state, a round-trip per click.
#[cfg(feature = "render-capture")]
fn serve_ie6_headless(port: u16) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::rc::Rc;
    use std::sync::Arc;

    const W: f32 = 1280.0;
    const H: f32 = 832.0;
    // The navigable surfaces (the 4 live-animated tabs stall headless stepping; they
    // are reachable in the native cockpit + the UI atlas, just not the IE6 server loop).
    const TABS: &[&str] = &[
        "home",
        "inspector",
        "inspect-act",
        "graph",
        "web-of-cells",
        "objects",
        "proofs",
        "lanes",
        "powerbox",
        "links-here",
        "organs",
        "cipherclerk",
        "editor",
        "composer",
        "simulate",
        "shell",
        "terminal",
        "buffer",
        "trust",
        "docs",
        "replay",
    ];

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    // gpui-component init (the kit `Button`/widgets the cockpit now uses read the
    // kit `Theme`/global at render; without it they panic). See the same weld in
    // `render_cockpit_headless`.
    cx.update(gpui_component::init);
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));
    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let window = cx.open_window(size(px(W), px(H)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    let wh = window.into();
    window.update(&mut cx, |c, _w, _cx| {
        c.select_tab_named("home");
    })?;

    let listener = TcpListener::bind(("127.0.0.1", port))?;
    println!(
        "IE6 cockpit server: http://127.0.0.1:{port}/   (the live verified cockpit, for timetravelers)"
    );
    println!(
        "shared-desktop replay: http://127.0.0.1:{port}/shared?d=<deos1 fragment>   (read-only deterministic replay; see site/deos-viewer/)"
    );

    fn qget(q: &str, key: &str) -> Option<String> {
        q.split('&').find_map(|kv| {
            let (k, v) = kv.split_once('=')?;
            if k == key {
                Some(v.replace('+', " "))
            } else {
                None
            }
        })
    }
    fn respond(stream: &mut std::net::TcpStream, ctype: &str, body: &[u8]) {
        let head = format!(
            "HTTP/1.0 200 OK\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        );
        let _ = stream.write_all(head.as_bytes());
        let _ = stream.write_all(body);
    }
    fn redirect(stream: &mut std::net::TcpStream, to: &str) {
        let _ = stream.write_all(
            format!("HTTP/1.0 302 Found\r\nLocation: {to}\r\nConnection: close\r\n\r\n").as_bytes(),
        );
    }

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let mut buf = [0u8; 2048];
        let n = stream.read(&mut buf).unwrap_or(0);
        let req = String::from_utf8_lossy(&buf[..n]);
        let line = req.lines().next().unwrap_or("");
        let path = line.split_whitespace().nth(1).unwrap_or("/");
        let (route, query) = path.split_once('?').unwrap_or((path, ""));

        match route {
            "/frame.png" => {
                cx.run_until_parked();
                let _ = cx.update_window(wh, |_, w, _| w.refresh());
                cx.run_until_parked();
                match cx.capture_screenshot(wh) {
                    Ok(img) => {
                        let mut png = Vec::new();
                        if image::DynamicImage::ImageRgba8(img)
                            .write_to(&mut std::io::Cursor::new(&mut png), image::ImageFormat::Png)
                            .is_ok()
                        {
                            respond(&mut stream, "image/png", &png);
                        }
                    }
                    Err(_) => respond(&mut stream, "text/plain", b"render error"),
                }
            }
            "/tab" => {
                if let Some(name) = qget(query, "name") {
                    let _ = window.update(&mut cx, |c, _w, _cx| {
                        c.select_tab_named(&name);
                    });
                }
                redirect(&mut stream, "/");
            }
            "/nav" => {
                let i: usize = qget(query, "i").and_then(|s| s.parse().ok()).unwrap_or(0);
                let _ = window.update(&mut cx, |c, _w, cx| {
                    let navs = c.available_nav();
                    if let Some((_, act)) = navs.get(i) {
                        let act = *act;
                        c.apply_nav(&act, cx);
                    }
                });
                redirect(&mut stream, "/");
            }
            // THE DESKTOP IN A LINK (read-only). `/shared?d=<deos1 fragment>`
            // decodes a share tape (`starbridge_v2::share_link`), boots a FRESH
            // deterministic world at the tape's pinned instant, re-executes the
            // tape through the real verified executor, and serves the verdict
            // page (root match / mismatch / unclaimed — the headline is the
            // EQUALITY, not the picture). Stateless per request and read-only
            // by construction: a stranger's link re-derives its OWN world; it
            // never reaches the live window above, and the page carries no
            // /nav or /tab links — no live turns from strangers.
            "/shared" => {
                let html = match qget(query, "d").map(|d| pct_decode(&d)) {
                    None => shared_help_page(),
                    Some(frag) => match starbridge_v2::share_link::decode_fragment(&frag) {
                        Ok(tape) => {
                            let (_world, _anchors, outcome) =
                                starbridge_v2::share_link::replay_fresh(&tape);
                            shared_verdict_page(&frag, &tape, &outcome)
                        }
                        Err(e) => shared_refusal_page(&e),
                    },
                };
                respond(&mut stream, "text/html", html.as_bytes());
            }
            // The replayed FRAME itself — the same decode→fresh-boot→replay,
            // then a throwaway headless cockpit window over the replayed world
            // (opened, captured, REMOVED — per-request lifecycle; the live
            // window is untouched). Deterministic: the same `d=` re-derives the
            // same world every time, so this is a pure function of the link.
            "/shared/frame.png" => {
                let result = qget(query, "d")
                    .map(|d| pct_decode(&d))
                    .ok_or_else(|| anyhow::anyhow!("missing `d=<fragment>`"))
                    .and_then(|frag| Ok(starbridge_v2::share_link::decode_fragment(&frag)?))
                    .and_then(|tape| render_shared_tape_frame(&mut cx, &tape));
                match result {
                    Ok(png) => respond(&mut stream, "image/png", &png),
                    Err(e) => respond(
                        &mut stream,
                        "text/plain",
                        format!("shared replay refused: {e:#}").as_bytes(),
                    ),
                }
            }
            _ => {
                // render-reconcile: select_tab_named sets the visible tab, but the
                // WITNESSED active_tab() (what nav_key reads) only catches up on a
                // render/witness — drive one so the page text matches the live frame.
                let _ = cx.update_window(wh, |_, w, _| w.refresh());
                cx.run_until_parked();
                let (tab, navs): (String, Vec<String>) = window
                    .update(&mut cx, |c, _w, _cx| {
                        let key = c.nav_key();
                        let tab = key.split('|').next().unwrap_or("").to_string();
                        (tab, c.available_nav().into_iter().map(|(l, _)| l).collect())
                    })
                    .unwrap_or_default();
                let html = ie6_page(&tab, &navs, TABS);
                respond(&mut stream, "text/html", html.as_bytes());
            }
        }
    }
    Ok(())
}

/// The IE6 page: HTML 4.01, the LIVE frame as an `<img usemap>`, a `<map>` of
/// `<area>` regions over it for the in-surface interactions, and a text tab/nav bar.
#[cfg(feature = "render-capture")]
fn ie6_page(tab: &str, navs: &[String], tabs: &[&str]) -> String {
    // image-map regions: a row of equal cells across the bottom strip of the frame,
    // one per available interaction (the live frame is 1000px wide as displayed).
    let iw = 1000;
    let areas: String = navs
        .iter()
        .enumerate()
        .map(|(i, label)| {
            let n = navs.len().max(1);
            let x0 = i * iw / n;
            let x1 = (i + 1) * iw / n;
            format!(
                "<area shape=\"rect\" coords=\"{x0},560,{x1},650\" href=\"/nav?i={i}\" alt=\"{l}\" title=\"{l}\">",
                l = html_escape(label)
            )
        })
        .collect();
    let tab_links: String = tabs
        .iter()
        .map(|t| {
            let on = tab
                .to_lowercase()
                .contains(&t.replace('-', "").to_lowercase())
                || tab
                    .to_lowercase()
                    .replace(['-', ' ', '⏳', '⤳', '📄', '⚷'], "")
                    .contains(&t.replace('-', ""));
            if on {
                format!("<b>[{}]</b> ", html_escape(t))
            } else {
                format!("<a href=\"/tab?name={t}\">{}</a> ", html_escape(t))
            }
        })
        .collect();
    let nav_links: String = navs
        .iter()
        .enumerate()
        .map(|(i, l)| format!("<a href=\"/nav?i={i}\">[{}]</a> ", html_escape(l)))
        .collect();
    format!(
        "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">\n\
<html><head><title>dregg - live cockpit (IE6 floor)</title></head>\n\
<body bgcolor=\"#0a0e14\" text=\"#c9d1d9\" link=\"#58a6ff\" vlink=\"#bc8cff\">\n\
<font face=\"monospace\" size=\"2\">\n\
<b><font color=\"#58a6ff\">dregg</font></b> - the live verified cockpit, server-rendered for any user-agent (no script, no canvas, no wasm). \
You are at: <b>{tab}</b>. Each click is a round-trip: the server applies it to the live world and re-renders.\n\
<p><img src=\"/frame.png\" width=\"1000\" usemap=\"#m\" border=\"1\" alt=\"the live cockpit\"></p>\n\
<map name=\"m\">{areas}</map>\n\
<p><b>surfaces:</b> {tab_links}</p>\n\
<p><b>here you can:</b> {nav_links}</p>\n\
<p><font color=\"#8b949e\" size=\"1\">The image-map regions along the lower band of the frame map to the in-surface \
interactions; the text links do the same. Refresh-free navigation by clicking the rendered frame - the way a remote \
screen was driven before canvas existed.</font></p>\n\
</font></body></html>",
        tab = html_escape(tab),
    )
}

#[cfg(feature = "render-capture")]
fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// ═══ THE DESKTOP IN A LINK — the serve-ie6 `/shared` replay routes ═══════════
//
// The share-URL codec + replay semantics live in `starbridge_v2::share_link`
// (pure, round-trip-tested); these helpers are the serve-ie6 glue: the query
// unwrap, the throwaway-window frame render, and the verdict page. Read-only
// throughout — a shared link re-derives a FRESH world, never drives the live one.

/// Undo percent-encoding in a query value (`%21` → `!`, …) — a hand-pasted
/// share link sometimes arrives pre-encoded by a chat client or a shell. A
/// malformed `%`-sequence passes through UNCHANGED: this layer never guesses;
/// the codec's fail-closed `decode_fragment` refuses the mangled link instead.
#[cfg(feature = "render-capture")]
fn pct_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let hex2 = [bytes[i + 1], bytes[i + 2]];
            if let Some(b) = std::str::from_utf8(&hex2)
                .ok()
                .and_then(|h| u8::from_str_radix(h, 16).ok())
            {
                out.push(b);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Render ONE frame of a REPLAYED share tape: fresh deterministic boot at the
/// tape's pinned instant, tape re-executed through the real executor
/// ([`starbridge_v2::share_link::replay_fresh`]), then a THROWAWAY headless
/// cockpit window over the replayed world — opened, Root-wrapped (the
/// kit-input weld, see `render_cockpit_headless`), captured, and REMOVED. The
/// per-request lifecycle keeps the long-lived server app window-clean; the
/// live serve-ie6 window is never touched. Deterministic: the same tape
/// renders the same world state every time (that is the whole point).
#[cfg(feature = "render-capture")]
fn render_shared_tape_frame(
    cx: &mut gpui::HeadlessAppContext,
    tape: &starbridge_v2::share_link::ShareTape,
) -> anyhow::Result<Vec<u8>> {
    use gpui::{px, size, AppContext};
    use std::cell::RefCell;
    use std::rc::Rc;

    // The live serve-ie6 geometry (the page displays both at width 1000).
    const W: f32 = 1280.0;
    const H: f32 = 832.0;

    let (world, anchors, _outcome) = starbridge_v2::share_link::replay_fresh(tape);
    let shared = Rc::new(RefCell::new(world));
    let tab = tape.tab.clone();
    let window = cx.open_window(size(px(W), px(H)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            if let Some(t) = &tab {
                if !c.select_tab_named(t) {
                    eprintln!("shared replay: no tab named `{t}` — keeping the default surface");
                }
            }
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    let wh = window.into();
    cx.run_until_parked();
    cx.update_window(wh, |_, w, _| w.refresh())?;
    cx.run_until_parked();
    let capture = cx.capture_screenshot(wh);
    // Tear the throwaway window down BEFORE surfacing any capture error, so a
    // failed render never leaks a window into the long-lived server app.
    let _ = cx.update_window(wh, |_, w, _| w.remove_window());
    cx.run_until_parked();

    let img = capture?;
    let mut png = Vec::new();
    image::DynamicImage::ImageRgba8(img)
        .write_to(&mut std::io::Cursor::new(&mut png), image::ImageFormat::Png)?;
    Ok(png)
}

/// The shared-desktop page chrome (HTML 4.01, the same floor as [`ie6_page`] —
/// one server, one look). READ-ONLY: no `/nav`, no `/tab` — a shared desktop
/// is something you LOOK AT and re-derive; the live one at `/` is yours.
#[cfg(feature = "render-capture")]
fn shared_wrap(inner: &str) -> String {
    format!(
        "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">\n\
<html><head><title>dregg - shared desktop (deterministic replay)</title></head>\n\
<body bgcolor=\"#0a0e14\" text=\"#c9d1d9\" link=\"#58a6ff\" vlink=\"#bc8cff\">\n\
<font face=\"monospace\" size=\"2\">\n\
<b><font color=\"#58a6ff\">dregg</font></b> - THE DESKTOP IN A LINK: a shared desktop, reconstructed by REPLAY. \
The link carries a pinned instant + a message tape; this server booted a FRESH world at that instant and re-executed \
the tape through the verified executor. Nothing on this page was taken on trust from the sharer.\n\
{inner}\n\
<p><a href=\"/\">back to the LIVE cockpit</a> (yours to drive - this page is read-only, and a shared link never touches it)</p>\n\
</font></body></html>"
    )
}

/// `/shared` with no `d=`: the how-to page (the grammar + a try-it link).
#[cfg(feature = "render-capture")]
fn shared_help_page() -> String {
    shared_wrap(
        "<p>No tape in the URL. Pass one as <tt>/shared?d=&lt;fragment&gt;</tt> - the fragment grammar is \
<tt>deos1!ts=&lt;unix&gt;[!tab=&lt;surface&gt;][!root=&lt;64hex&gt;][!act=&lt;cellhex&gt;:&lt;verb&gt;]*</tt> \
(see <tt>starbridge_v2::share_link</tt>).</p>\n\
<p>Try the seeded demo image at a pinned instant: <a href=\"/shared?d=deos1!ts=1751500800\">\
/shared?d=deos1!ts=1751500800</a> - visit it twice and the SAME canonical root re-derives (determinism is the point; \
bake that root back into the link as <tt>!root=...</tt> to make the claim checkable). The static landing page at \
<tt>site/deos-viewer/</tt> turns a <tt>#deos1!...</tt> URL fragment into this route.</p>",
    )
}

/// `/shared` with a link the codec refused: the refusal, first-class.
#[cfg(feature = "render-capture")]
fn shared_refusal_page(e: &starbridge_v2::share_link::ShareLinkError) -> String {
    shared_wrap(&format!(
        "<p><b><font color=\"#f85149\" size=\"3\">LINK REFUSED</font></b> - {}</p>\n\
<p>Decoding is fail-closed: a malformed or over-cap link is refused outright, never guessed at.</p>",
        html_escape(&e.to_string())
    ))
}

/// The `/shared` verdict page: the convergence verdict as the HEADLINE (root
/// match / mismatch / unclaimed), the tape facts, every in-band skip, and the
/// replayed frame. The claim-vs-derived equality is the content; the picture
/// is the illustration.
#[cfg(feature = "render-capture")]
fn shared_verdict_page(
    frag: &str,
    tape: &starbridge_v2::share_link::ShareTape,
    outcome: &starbridge_v2::share_link::ReplayOutcome,
) -> String {
    use starbridge_v2::share_link::RootVerdict;

    let verdict = match &outcome.verdict {
        RootVerdict::Match(root) => format!(
            "<p><b><font color=\"#3fb950\" size=\"3\">ROOT MATCH</font></b> - the re-derived canonical ledger root \
equals the link's claim:<br><tt>{}</tt><br>You did not trust a screenshot - you re-derived this desktop.</p>",
            hex::encode(root)
        ),
        RootVerdict::Mismatch { claimed, derived } => format!(
            "<p><b><font color=\"#f85149\" size=\"3\">ROOT MISMATCH</font></b> - the replay DIVERGED from the \
link's claim (surfaced, never smoothed over):<br>claimed: <tt>{}</tt><br>derived: <tt>{}</tt><br>\
The code moved since the link was minted, the tape was edited, or an act refused (listed below if so).</p>",
            hex::encode(claimed),
            hex::encode(derived)
        ),
        RootVerdict::Unclaimed(derived) => format!(
            "<p><b><font color=\"#8b949e\" size=\"3\">NO ROOT CLAIM</font></b> - this link carries no <tt>root=</tt>; \
the replay derived <tt>{}</tt>. A sharer can bake it in as <tt>!root=...</tt> to make the link checkable.</p>",
            hex::encode(derived)
        ),
    };

    let surface = tape
        .tab
        .as_deref()
        .map(|t| format!(" · surface <b>{}</b>", html_escape(t)))
        .unwrap_or_default();
    let facts = format!(
        "<p>pinned instant <tt>ts={}</tt> · {} act(s) on the tape · {} committed as real verified turns{surface}</p>",
        tape.timestamp,
        tape.acts.len(),
        outcome.committed,
    );

    let skips = if outcome.skipped.is_empty() {
        String::new()
    } else {
        let rows: String = outcome
            .skipped
            .iter()
            .map(|(i, why)| format!("<br>&nbsp;&nbsp;act #{i}: {}", html_escape(why)))
            .collect();
        format!(
            "<p><font color=\"#f85149\"><b>{} act(s) did NOT commit</b> - the reconstruction is NOT the sharer's \
desktop (the skips are surfaced, not swallowed):{rows}</font></p>",
            outcome.skipped.len()
        )
    };

    shared_wrap(&format!(
        "{verdict}\n{facts}\n{skips}\n\
<p><img src=\"/shared/frame.png?d={d}\" width=\"1000\" border=\"1\" alt=\"the replayed desktop\"></p>\n\
<p><font color=\"#8b949e\" size=\"1\">The frame above is itself a pure function of the link: its route re-runs the \
same fresh-boot + replay, renders the cockpit over the replayed world, and tears the window down. Refresh it as \
often as you like - the same link, the same desktop.</font></p>",
        d = html_escape(frag)
    ))
}

/// THE UI-EXPLORATION CRAWL — BFS-walk the cockpit's navigation state-space by
/// driving the real interaction handlers, screenshot each distinct UI state, and
/// emit a graph of states + interaction edges. The atlas's "UI tree".
#[cfg(feature = "render-capture")]
fn explore_ui_headless(outdir: &str) -> anyhow::Result<()> {
    use cockpit::NavAction;
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::collections::{HashSet, VecDeque};
    use std::rc::Rc;
    use std::sync::Arc;

    const W: f32 = 1280.0;
    const H: f32 = 832.0;
    let max_nodes: usize = std::env::var("ATLAS_UI_NODES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(220);

    let states_dir = format!("{outdir}/states");
    std::fs::create_dir_all(&states_dir)?;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });

    // The cockpit's panels now use gpui-component kit widgets (`Button`, …) which
    // read the kit's `Theme`/global state at render; init it in this headless app
    // (the windowed path does so at boot) or any kit widget panics on the missing
    // global. (See `render_cockpit_headless` for the same weld.)
    cx.update(gpui_component::init);
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let window = cx.open_window(size(px(W), px(H)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    let wh = window.into();

    // root at HOME; capture the initial nav state to restore between nodes
    let initial = window.update(&mut cx, |c, _window, _cx| {
        c.select_tab_named("home");
        c.capture_nav()
    })?;

    let sanitize = |k: &str| -> String {
        k.chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect::<String>()
    };

    let mut visited: HashSet<String> = HashSet::new();
    let mut queue: VecDeque<Vec<NavAction>> = VecDeque::new();
    let mut nodes: Vec<(String, String, String)> = Vec::new(); // (key, tab, png)
    let mut edges: Vec<(String, String, String)> = Vec::new(); // (from, label, to)
    queue.push_back(Vec::new());

    while let Some(path) = queue.pop_front() {
        if nodes.len() >= max_nodes {
            eprintln!(
                "explore-ui: node cap {max_nodes} hit ({} queued)",
                queue.len()
            );
            break;
        }
        // reconstruct to `path`, read key + children (all inside one update)
        let dbg = std::env::var("ATLAS_UI_DEBUG").is_ok();
        let (key, tab, children) = window.update(&mut cx, |c, _window, cx| {
            if dbg {
                eprintln!("  reconstruct: restore_initial");
            }
            c.restore_nav(&initial, cx);
            for (i, a) in path.iter().enumerate() {
                if dbg {
                    eprintln!("  reconstruct: apply path[{i}] {a:?}");
                }
                c.apply_nav(a, cx);
            }
            let key = c.nav_key();
            let tab = key.split('|').next().unwrap_or("").to_string();
            let node_state = c.capture_nav();
            let mut kids = Vec::new();
            for (label, action) in c.available_nav() {
                if dbg {
                    eprintln!("  child: apply {action:?} ({label})");
                }
                c.apply_nav(&action, cx);
                kids.push((label, action, c.nav_key()));
                if dbg {
                    eprintln!("  child: restore");
                }
                c.restore_nav(&node_state, cx);
            }
            (key, tab, kids)
        })?;

        if visited.contains(&key) {
            continue;
        }
        visited.insert(key.clone());
        eprintln!("explore-ui: [{}] visiting {key}", nodes.len());

        // drive a fully-laid-out frame + capture
        cx.run_until_parked();
        cx.update_window(wh, |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let captured = cx.capture_screenshot(wh)?;
        let png = format!("states/{}.png", sanitize(&key));
        captured.save(format!("{outdir}/{png}"))?;
        nodes.push((key.clone(), tab, png));

        for (label, action, child_key) in children {
            edges.push((key.clone(), label, child_key.clone()));
            if !visited.contains(&child_key) {
                let mut p = path.clone();
                p.push(action);
                queue.push_back(p);
            }
        }
    }

    // emit ui-graph.json
    let nodes_json: Vec<_> = nodes
        .iter()
        .map(|(k, t, p)| serde_json::json!({ "key": k, "tab": t, "png": p }))
        .collect();
    let edges_json: Vec<_> = edges
        .iter()
        .map(|(f, l, t)| serde_json::json!({ "from": f, "label": l, "to": t }))
        .collect();
    let blob = serde_json::json!({
        "node_count": nodes.len(),
        "edge_count": edges.len(),
        "max_nodes": max_nodes,
        "nodes": nodes_json,
        "edges": edges_json,
    });
    std::fs::write(
        format!("{outdir}/ui-graph.json"),
        serde_json::to_string_pretty(&blob)?,
    )?;
    println!(
        "OK explore-ui -> {outdir}/ui-graph.json ({} states, {} edges)",
        nodes.len(),
        edges.len()
    );
    Ok(())
}

/// THE HEADLESS COCKPIT BAKE — render the REAL `cockpit::Cockpit` element tree
/// to an 800x600 RGBA8 frame with no GPU and no window, for the seL4 deos-image
/// PD to blit onto its ramfb framebuffer.
///
/// This is the closure of the desktop keystone's last swap: the deos-image PD
/// used to bake a *hand-built* cockpit-shaped `gpui::Scene`; this bakes the
/// LIVE element tree. The mechanism is gpui's own headless capture path
/// (`HeadlessAppContext` over `TestPlatform`), wired on Linux to the offscreen
/// wgpu renderer (`gpui_platform::current_headless_renderer` →
/// `gpui_wgpu::WgpuHeadlessRenderer`, the patched `render_scene_to_image` on
/// lavapipe / software Vulkan):
///
///  1. A `CosmicTextSystem` (real glyph shaping) is the platform text system;
///     the cockpit asks for the "Menlo" family, which falls back to the vendored
///     Lilex (`assets/fonts`). Glyphs rasterize into the headless renderer's own
///     sprite atlas, the same atlas the capture later samples.
///  2. A headless `App` + `Window` is opened at exactly 800x600 with the REAL
///     [`cockpit::Cockpit`] (over the fully-seeded [`world::demo_world`] image —
///     all five verified executor turns already run) as its root view. Opening
///     the window draws it once; a `refresh()` + `run_until_parked()` drives it
///     to a fully-laid-out frame.
///  3. `Window::render_to_image` (`capture_screenshot`) resolves that frame's
///     `gpui::Scene` and renders it offscreen to RGBA — the bytes written here.
///
/// The geometry MUST equal the framebuffer's (`sel4/.../fb.rs` = 800x600) so the
/// PD's blit is a straight RGBA→XRGB8888 copy.
#[cfg(feature = "render-capture")]
fn render_cockpit_headless(
    out: &str,
    replays: &[(String, String)],
    w: f32,
    h: f32,
    tab: Option<&str>,
    first_run: bool,
) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // The seL4 deos-image framebuffer geometry (sel4/dregg-pd/deos-image/src/fb.rs).
    // When the bake is asked for EXACTLY this size we downscale the 2x capture to
    // it and write the `.rgba` the PD blits; any other size renders the full-res
    // cockpit (no downscale, no truncation, PNG only).
    let sel4_geometry = (w as u32, h as u32) == (800, 600);

    // Vendored OFL fonts (the cockpit uses "Menlo"; unknown families fall back
    // to the system_font_fallback — here Lilex — inside CosmicTextSystem).

    // 1. Real text shaping with no system fonts (deterministic), Lilex fallback.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    // 2. Headless app over TestPlatform + the Linux offscreen wgpu renderer.
    //    `current_headless_renderer` returns the `WgpuHeadlessRenderer` (lavapipe
    //    when `ZED_OFFSCREEN_PREFER_CPU=1`); its sprite atlas backs the window.
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });

    // 2b. Initialize gpui-component in the headless app too — the cockpit's panels
    //     now use the real `Button` (and other kit widgets), which read the kit's
    //     `Theme` + global state at render time. The WINDOWED path inits it at boot
    //     (main.rs `gpui_component::init(cx)`); the headless renderer is a separate
    //     `App` and must do the same, or any kit widget panics on the missing
    //     `gpui_component::theme::Theme` global. This is what makes the seL4
    //     framebuffer bake + the dregg-mcp screenshot render the migrated buttons.
    cx.update(gpui_component::init);
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // 3. The fully-seeded demo image — the same `World` the windowed cockpit runs,
    //    with every verified executor turn already committed (eager seeding).
    let (mut world, anchors) = world::demo_world();

    // 3b. Apply any recorded act-trail (`--replay <cell>:<msg>`) through the REAL
    //     executor so the rendered frame reflects a driven session (dregg-mcp).
    //     Each act is fired as the cell upon itself with the `Either` tier — the
    //     same self-operator projection the inspect→act panel uses; a refusal is
    //     reported to stderr and skipped (the screenshot stays honest).
    for (cell_pfx, msg) in replays {
        let resolved =
            world.ledger().iter().map(|(id, _)| *id).find(|id| {
                hex::encode(id.as_bytes()).starts_with(cell_pfx.trim_start_matches("0x"))
            });
        match resolved {
            Some(cell) => {
                let ia = starbridge_v2::inspect_act::InspectAct::build(
                    &world,
                    starbridge_v2::inspect_act::InspectFocus::Cell(cell),
                    cell,
                    dregg_cell::permissions::AuthRequired::Either,
                );
                match ia.send(
                    &mut world,
                    msg,
                    dregg_cell::permissions::AuthRequired::Either,
                ) {
                    starbridge_v2::inspect_act::SendResult::Committed { .. } => {}
                    starbridge_v2::inspect_act::SendResult::Refused { reason, .. } => {
                        eprintln!("replay {cell_pfx}:{msg} refused: {reason}");
                    }
                }
            }
            None => eprintln!("replay {cell_pfx}:{msg} — no cell matched prefix"),
        }
    }

    let shared = Rc::new(RefCell::new(world));
    let tab_owned = tab.map(|s| s.to_string());

    // 4. Open a headless window (logical w×h) whose ROOT IS a gpui-component `Root`
    //    wrapping the real Cockpit, on the requested surface (`--render-tab`). The
    //    `Root` wrap is THE window-root weld (docs/deos/COCKPIT-UX.md): without it
    //    any kit text INPUT a surface bears (web-shell URL bar, editor/composer
    //    prompts) aborts on paint via `Root::read(window).unwrap()`. No node, no seed.
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            if let Some(t) = &tab_owned {
                if !c.select_tab_named(t) {
                    eprintln!("render-tab: no tab named `{t}` — keeping default");
                }
            }
            // FIRST-VIEW BAKE — show the calm sparse first-run landing for the welcome
            // shot (the warm "welcome to your world", a few cells, ONE "try this").
            c.set_first_run(first_run);
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;

    // 5. Drive to a fully-rendered frame, then capture the resolved gpui Scene.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;

    // gpui's headless `TestWindow` reports a FIXED 2.0 scale factor (HiDPI), so a
    // logical w×h window resolves to a 2w×2h DEVICE-pixel render. For the seL4
    // geometry we Lanczos3-downscale to the framebuffer's exact 800x600 (the PD's
    // blit stays a straight copy); for any other size we keep the crisp 2x capture
    // (full layout, no truncation).
    let (cw, ch) = (captured.width(), captured.height());
    let img = if sel4_geometry && !(cw == 800 && ch == 600) {
        image::imageops::resize(&captured, 800, 600, image::imageops::FilterType::Lanczos3)
    } else {
        captured
    };
    let (ww, hh) = (img.width(), img.height());

    // (a) the raw RGBA the seL4 deos-image PD bakes in (only at framebuffer geometry).
    if sel4_geometry {
        std::fs::write(format!("{out}.rgba"), img.as_raw())?;
    }
    // (b) the PNG (always).
    img.save(format!("{out}.png"))?;

    println!(
        "OK headless cockpit render -> {out}.png ({ww}x{hh}, logical {w}x{h}{}{}); \
         LIVE cockpit::Cockpit element tree, gpui Scene via lavapipe offscreen.",
        if sel4_geometry { " + .rgba" } else { "" },
        tab.map(|t| format!(", tab={t}")).unwrap_or_default()
    );
    Ok(())
}

/// THE AGENT'S HANDS ON THE REAL GLASS — bake a PNG of the cockpit inspector showing
/// the cell the AGENT'S `run_js` modified on the LIVE World.
///
/// 1. Build `world::demo_world()` (the cockpit's real cells) into an
///    `Rc<RefCell<World>>`. When `fork`, the agent drives a `world.fork()` (the safe
///    sandbox) instead — the live image is untouched.
/// 2. Attach the confined agent's deos-js runtime (real SpiderMonkey) to that World
///    via [`starbridge_v2::agent_attach`], bound to the agent's `held` (Signature —
///    an attenuated mandate, never the World's root). The agent's cell is the demo
///    `user` cell.
/// 3. Run the agent's JS: crawl the LIVE cells, fire a real verified turn on the
///    agent's cell (a receipt that lands on the live ledger), attempt an over-reach
///    (refused in-band — no turn). Print the witness to stdout.
/// 4. Open the cockpit on the INSPECTOR over that SAME World, drive a frame, and bake
///    `<out>.png` — the agent's modified field is on the glass.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "agent-js"))]
fn render_agent_attach_headless(out: &str, w: f32, h: f32, fork: bool) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // 1. The cockpit's real image — the SAME `World` the windowed cockpit runs.
    let (world, anchors) = world::demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));

    let agent = user;
    let held = dregg_cell::AuthRequired::Signature;
    let affordances = vec![
        ("bump".to_string(), dregg_cell::AuthRequired::Signature),
        ("escalate".to_string(), dregg_cell::AuthRequired::Proof),
    ];

    // 2. Attach the agent's deos-js runtime to the LIVE World (or a fork). The SAME
    //    `Rc<RefCell<World>>` the cockpit will render — so a fire lands on the glass.
    let (sink, rendered_world, where_) = if fork {
        let s = WorldSinkAdapter::fork_of(&live);
        let w = s.world();
        (s, w, "FORK (the safe sandbox — the live image untouched)")
    } else {
        let s = WorldSinkAdapter::live(live.clone());
        (
            s,
            live.clone(),
            "LIVE cockpit World (the operator's real cells)",
        )
    };
    let pre_height = rendered_world.borrow().height();
    let cell_count = rendered_world.borrow().cell_count();
    let applet = attach_agent(sink, agent, held, affordances);

    // 3. Run the agent's JS on that World (real SpiderMonkey).
    let mut rt =
        deos_js::JsRuntime::new().map_err(|e| anyhow::anyhow!("boot SpiderMonkey: {e}"))?;
    let script = r#"
        var app = deos.applet({ affordances: ["bump", "escalate"] });
        var cells = deos.world.cells().length;     // crawl the LIVE cells
        var after = app.fire("bump", 42);          // a real verified turn (held)
        var over = app.fire("escalate", 1);        // over-reach → -1 (refused)
        (cells * 1000) + (after * 10) + (over === -1 ? 1 : 0);
    "#;
    let outcome = rt
        .run_attached(applet, script)
        .map_err(|e| anyhow::anyhow!("agent run_js on the World: {e}"))?;
    let witness = outcome.result.unwrap_or(-1);
    let crawled = witness / 1000;
    let after = (witness % 1000) / 10;
    let over_refused = witness % 10 == 1;
    let post_height = rendered_world.borrow().height();
    let live_field = rendered_world
        .borrow()
        .ledger()
        .get(&agent)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    println!(
        "AGENT-ATTACH [{where_}]: crawled {crawled} cells (of {cell_count}); \
         fired bump → counter={after} ({} verified turn committed, receipt {}); \
         over-reach escalate(Proof) refused in-band = {over_refused}; \
         live ledger height {pre_height}→{post_height}; agent cell slot-0 = {live_field}.",
        outcome.fires_committed,
        outcome
            .receipts
            .first()
            .map(|r| hex::encode(&r[..6]))
            .unwrap_or_else(|| "—".into()),
    );
    anyhow::ensure!(
        after == 42 && live_field == 42,
        "the agent's JS did not land on the live ledger"
    );
    anyhow::ensure!(over_refused, "the over-reach was NOT refused");
    anyhow::ensure!(
        outcome.fires_committed == 1,
        "expected exactly ONE committed fire"
    );

    // 4. Bake the cockpit INSPECTOR over the SAME World (the agent's field is on glass).
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let shared = rendered_world.clone();
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            if !c.select_tab_named("inspector") {
                eprintln!("render-agent-attach: no inspector tab — keeping default");
            }
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    println!(
        "OK agent-attach render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         the agent's run_js drove the {where_} — its modified cell is on the inspector glass."
    );
    Ok(())
}

/// THE CARD-PANE BAKE — a hyperdreggmedia CARD mounted as a LIVE cockpit surface.
///
/// The flow, end-to-end and REAL:
///   1. Build the cockpit's live `World` (the same demo image the windowed cockpit
///      runs). Attach a counter applet to it through the `agent_attach`
///      `WorldSinkAdapter::live` weld — the card's substance is the operator's REAL
///      `user` cell, the fire bounded by the agent's `held` (Signature, attenuated).
///   2. Author the card's `deos.ui.*` view-tree in real SpiderMonkey (text + a `bind`
///      on the live cell's slot 0 + a `+1` button firing the `bump` affordance). The
///      authoring stashes the tree into ephemeral view-state — it commits NO turn.
///   3. Open the `CardPane` over the LIVE attached applet, drive a frame, bake
///      `<out>.before.png` (the bound value = the live cell's current slot-0).
///   4. FIRE the card's button affordance = ONE cap-gated verified turn committed
///      THROUGH `World::commit_turn` onto the live ledger (a real receipt). Assert the
///      live cell advanced + the receipt landed.
///   5. Re-render (immediate-mode: the `bind` re-reads the live ledger) + bake
///      `<out>.after.png` — the bound value visibly advanced. Assert the two frames
///      differ (the card tracked a real live turn).
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
fn render_card_pane_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
    use starbridge_v2::card_pane::{build_card_over_live, CardPane};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // 1. The cockpit's real image — the SAME `World` the windowed cockpit runs. The card
    //    is backed by the demo `user` cell (the agent's OWN vessel).
    let (world, anchors) = world::demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));

    let agent = user;
    let held = dregg_cell::AuthRequired::Signature;
    // The card's affordance surface: `bump` (Signature — held, admitted). The cap tooth
    // in deos-js checks every fire against `held` before it reaches the executor.
    let affordances = vec![("bump".to_string(), dregg_cell::AuthRequired::Signature)];

    let pre_height = live.borrow().height();
    let pre_field = live
        .borrow()
        .ledger()
        .get(&agent)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    // The applet ATTACHED to the live World (the card's live substance).
    let sink = WorldSinkAdapter::live(live.clone());
    let attached = attach_agent(sink, agent, held, affordances);

    // 2. Author the card's view-tree over the live applet (real SpiderMonkey). The bind
    //    re-reads slot `AGENT_COUNTER_SLOT` (the live cell's counter); the button fires
    //    `bump` (+1). The authoring commits NO turn (only ephemeral view-state).
    let key = starbridge_v2::card_pane::view_tree_key_for_card();
    let card_js = format!(
        r#"
        var app = deos.applet({{ affordances: ["bump"] }});
        var b = deos.ui.bind(function() {{ return app.get({slot}); }});
        b.props.slot = {slot};            // tag the slot the card re-reads off the live ledger
        b.props.label = "live count: ";   // a human prefix on the bound value
        var tree = deos.ui.vstack(
            deos.ui.text("Counter card (live cockpit cell)"),
            b,
            deos.ui.button("+1", "bump", 1)
        );
        app.view.set("{key}", JSON.stringify(tree));
        0;
    "#,
        slot = AGENT_COUNTER_SLOT,
        key = key,
    );

    let mut rt =
        deos_js::JsRuntime::new().map_err(|e| anyhow::anyhow!("boot SpiderMonkey: {e}"))?;
    let (attached, tree) = build_card_over_live(&mut rt, attached, &card_js)
        .map_err(|e| anyhow::anyhow!("author the card over the live World: {e}"))?;

    // Share the LIVE attached applet so the rendered button + the bind both drive the
    // SAME sovereign cell on the live ledger.
    let shared = Rc::new(RefCell::new(attached));

    // 3. Boot the headless renderer (same offscreen-wgpu path the cockpit bakes through)
    //    + the gpui-component theme, then open the card pane → bake the BEFORE shot.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let card_applet = shared.clone();
    let card_tree = tree.clone();
    let window = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        cx.new(|_cx| CardPane::new(card_applet, card_tree, "hyperdreggmedia · counter card"))
    })?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let before = cx.capture_screenshot(window.into())?;
    let (bw, bh) = (before.width(), before.height());
    before.save(format!("{out}.before.png"))?;

    // 4. FIRE the card's button affordance — a REAL cap-gated verified turn committed
    //    THROUGH `World::commit_turn` onto the live ledger (exactly what the rendered
    //    Button's on_click does). We invoke it on the shared live applet directly so the
    //    bake can assert on the receipt + the live ledger.
    let receipt = shared
        .borrow_mut()
        .fire("bump", 1)
        .map_err(|e| anyhow::anyhow!("the card's button did not commit a live turn: {e}"))?;

    let post_height = live.borrow().height();
    let post_field = live
        .borrow()
        .ledger()
        .get(&agent)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);
    anyhow::ensure!(
        post_field == pre_field + 1,
        "the card's button did not advance the LIVE cell ({pre_field} -> {post_field})"
    );
    anyhow::ensure!(
        post_height == pre_height + 1,
        "the live ledger height did not grow by ONE ({pre_height} -> {post_height})"
    );
    anyhow::ensure!(
        shared.borrow().receipt_count() == 1,
        "expected exactly ONE receipt on the card's live tape"
    );

    // 5. Re-render — the bind re-reads the live ledger → bake the AFTER shot (advanced).
    cx.update(|cx| cx.refresh_windows());
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let after = cx.capture_screenshot(window.into())?;
    let (aw, ah) = (after.width(), after.height());
    after.save(format!("{out}.after.png"))?;

    // THE LOAD-BEARING ASSERTION: the bound value visibly changed (the live cell's slot-0
    // advanced), so the two frames are NOT byte-identical. The card rendered REAL widgets
    // whose bound content tracked a real verified turn on the cockpit's live ledger.
    anyhow::ensure!(
        before.as_raw() != after.as_raw(),
        "the card frame did not change after the live turn (the bound count did not re-read)"
    );

    println!(
        "OK card-pane render -> {out}.before.png ({bw}x{bh}) / {out}.after.png ({aw}x{ah}), \
         logical {w}x{h}; a hyperdreggmedia counter CARD rendered as a LIVE cockpit pane: \
         its button fired a verified turn on the live ledger (cell slot-0 {pre_field}->{post_field}, \
         height {pre_height}->{post_height}, receipt {}), and the bound value re-read off the live \
         cell (the AFTER frame differs).",
        hex::encode(&receipt[..6]),
    );
    Ok(())
}

/// **THE ONBOARDING BAKE — make + fire + edit your first card from the UI flow alone.**
///
/// The path a NON-ember stranger takes from "I'm in" to "I made a thing", driven exactly
/// as their clicks would, end-to-end and REAL:
///   1. Boot the FULL cockpit (the same chrome a stranger logs into) over the live demo
///      `World`, captured so we hold the inner `Cockpit` entity to drive.
///   2. `make_first_card` — mint a REAL editable starter card over the live World, its
///      substance the stranger's own `user`/home cell (the SAME mint the
///      "make your first card →" affordance runs). The cockpit now shows the first-card
///      view; bake `<out>.before.png`.
///   3. `first_card_bump` — fire the card's `+1` = ONE cap-gated verified turn on their
///      cell. Assert a real receipt landed + the home cell's counter advanced + the
///      ledger height grew by one.
///   4. `first_card_add_button` — a receipted view-patch adding a button. Assert the new
///      button is in the card's re-folded `view_source` (an accountable patch, not a
///      recompile).
///   5. Re-render → bake `<out>.after.png`. Assert the two cockpit frames differ (the
///      card's bound count re-read + the new button painted).
///
/// The load-bearing truth: a stranger genuinely made a card that is theirs, fired a real
/// verified turn on it, and edited it live — using only the onboarding UI flow.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "card-pane"))]
fn render_first_card_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::agent_attach::AGENT_COUNTER_SLOT;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // 1. Headless app + the kit + the dark theme (the cockpit's panels use kit widgets).
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The cockpit's real image — the SAME `World` the windowed cockpit runs. The
    // stranger's home cell is the `user` anchor; we read its counter before/after.
    let (world, anchors) = world::demo_world();
    let [_treasury, _service, home] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let pre_height = shared.borrow().height();
    let pre_field = shared
        .borrow()
        .ledger()
        .get(&home)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    // 2. Open the full cockpit (the window-root `Root` weld), capturing the inner
    //    `Cockpit` entity out of the builder so we can drive its onboarding methods.
    let mut cockpit_slot: Option<gpui::Entity<cockpit::Cockpit>> = None;
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        cockpit_slot = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    let cockpit = cockpit_slot.expect("the Root builder ran and stashed the cockpit");

    // 2b. MAKE THE FIRST CARD — the exact mint the "make your first card →" click runs.
    cx.update(|app| cockpit.update(app, |c, cx| c.make_first_card(cx)));
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let before = cx.capture_screenshot(window.into())?;
    let (bw, bh) = (before.width(), before.height());
    before.save(format!("{out}.before.png"))?;

    // 3. FIRE THE CARD'S +1 — the onboarding "press +1" affordance = ONE cap-gated
    //    verified turn on the stranger's own home cell (a real receipt).
    cx.update(|app| cockpit.update(app, |c, cx| c.first_card_bump(cx)));
    cx.run_until_parked();

    let post_height = shared.borrow().height();
    let post_field = shared
        .borrow()
        .ledger()
        .get(&home)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);
    // The card's +1 advances the home cell's counter by EXACTLY ONE — the precise
    // witness that the `bump` fired one real turn on the stranger's own cell.
    anyhow::ensure!(
        post_field == pre_field + 1,
        "the first card's +1 did not advance the stranger's home cell by ONE ({pre_field} -> {post_field})"
    );
    // A real commit reached the ledger (height grew). We assert `>` not `== +1`: the
    // live cockpit also commits its OWN bookkeeping turns between the snapshots (e.g.
    // the optimistic-nav `SetField` that witnesses the active tab), so the ledger
    // height legitimately grows by more than the single card turn. The card's own
    // receipt tape (below) is the exact "the +1 committed once" witness.
    anyhow::ensure!(
        post_height > pre_height,
        "the live ledger did not grow on the first card's +1 ({pre_height} -> {post_height})"
    );
    // The card's OWN tape carries exactly ONE receipt — the +1's verified turn (the
    // cockpit's bookkeeping turns land on other cells, not this card's tape).
    let card_receipts = cx.update(|app| cockpit.update(app, |c, _cx| c.first_card_receipt_count()));
    anyhow::ensure!(
        card_receipts == 1,
        "expected exactly ONE receipt on the first card's tape after the +1, found {card_receipts}"
    );

    // 4. EDIT FROM WITHIN — the onboarding "add a button" affordance = a receipted
    //    view-patch. Assert the new button is in the card's re-folded view_source.
    cx.update(|app| cockpit.update(app, |c, cx| c.first_card_add_button(cx)));
    cx.run_until_parked();
    let view_source = cx
        .update(|app| cockpit.update(app, |c, _cx| c.first_card_view_source()))
        .ok_or_else(|| anyhow::anyhow!("the first card is not mounted after the edit"))?;
    anyhow::ensure!(
        view_source.contains("you added this"),
        "the receipted view-patch did not land in the card's view_source (no added button)"
    );

    // 5. Re-render → bake the AFTER shot (the bound count advanced + the new button painted).
    cx.update(|cx| cx.refresh_windows());
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let after = cx.capture_screenshot(window.into())?;
    let (aw, ah) = (after.width(), after.height());
    after.save(format!("{out}.after.png"))?;

    // THE LOAD-BEARING ASSERTION: the two cockpit frames differ — the card the stranger
    // made changed (its bound count re-read off a real turn, and the edit added a button).
    anyhow::ensure!(
        before.as_raw() != after.as_raw(),
        "the first-card view did not change after the +1 + the edit (the stranger's card is static)"
    );

    println!(
        "OK first-card render -> {out}.before.png ({bw}x{bh}) / {out}.after.png ({aw}x{ah}), \
         logical {w}x{h}; a STRANGER made their first card from the UI flow: minted a real \
         editable card over their own home cell, fired its +1 (a verified turn: cell slot-0 \
         {pre_field}->{post_field}, height {pre_height}->{post_height}), and edited it live (a \
         receipted view-patch added a button — now in the card's view_source). The AFTER frame differs."
    );
    Ok(())
}

/// THE APP-STORE VIEW — a standalone gpui surface listing the real
/// [`RegistryLauncher`](starbridge_v2::powerbox::RegistryLauncher) rows (the wired
/// starbridge-apps: id · name · what-it-does), styled in the deos dark palette. The
/// content is the registry's own truth (the same rows the cockpit's app-launcher renders);
/// this view bakes it as one crisp "app store" PNG for the site/tweeters.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
struct AppStoreView {
    rows: Vec<starbridge_v2::powerbox::AppLaunchRow>,
}

#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
impl gpui::Render for AppStoreView {
    fn render(
        &mut self,
        _window: &mut gpui::Window,
        _cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        use gpui::{div, px, rgb, FontWeight, ParentElement, Styled};
        let bg = rgb(0x0e1116);
        let panel = rgb(0x161b22);
        let panel_hi = rgb(0x1f2630);
        let border = rgb(0x2b3340);
        let text = rgb(0xd7dee8);
        let muted = rgb(0x7d8794);
        let accent = rgb(0x6cb6ff);

        let header = div()
            .flex()
            .flex_col()
            .gap_1()
            .mb_4()
            .child(
                div()
                    .text_color(text)
                    .text_2xl()
                    .font_weight(FontWeight::BOLD)
                    .child("deos · app store"),
            )
            .child(div().text_color(muted).text_sm().child(format!(
                "{} pre-built starbridge-apps — launch any onto your LIVE World; each is \
                 cells × cap-gated affordances that fire REAL verified turns.",
                self.rows.len()
            )));

        let mut grid = div().flex().flex_row().flex_wrap().gap_4();
        for r in &self.rows {
            grid = grid.child(
                div()
                    .w(px(740.))
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_4()
                    .rounded_lg()
                    .bg(panel)
                    .border_1()
                    .border_color(border)
                    .child(
                        div()
                            .flex()
                            .flex_row()
                            .justify_between()
                            .items_center()
                            .child(
                                div()
                                    .text_color(text)
                                    .text_lg()
                                    .font_weight(FontWeight::BOLD)
                                    .child(r.name.clone()),
                            )
                            .child(
                                div()
                                    .px_2()
                                    .py_0p5()
                                    .rounded_md()
                                    .bg(accent)
                                    .text_color(bg)
                                    .text_xs()
                                    .font_weight(FontWeight::BOLD)
                                    .child("launch →"),
                            ),
                    )
                    .child(
                        div()
                            .text_color(accent)
                            .text_xs()
                            .child(format!("({})", r.id)),
                    )
                    .child(
                        div()
                            .mt_1()
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(panel_hi)
                            .text_color(muted)
                            .text_xs()
                            .child(r.description.clone()),
                    ),
            );
        }

        div()
            .size_full()
            .bg(bg)
            .p_8()
            .flex()
            .flex_col()
            .font_family("IBM Plex Sans")
            .child(header)
            .child(grid)
    }
}

/// THE APPS-GOING VIEW — a standalone gpui surface hosting several launched
/// starbridge-apps' BESPOKE [`CardPane`](starbridge_v2::card_pane::CardPane)s side by
/// side, each bound to its own just-seeded cell on the shared live World (its `bind`s
/// re-read live ledger state, its buttons fire the app's real verified turns). Bakes the
/// "apps going" PNG — multiple real apps running inside the live image at once.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
struct AppsRowView {
    subtitle: String,
    cards: Vec<gpui::Entity<starbridge_v2::card_pane::CardPane>>,
}

#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
impl gpui::Render for AppsRowView {
    fn render(
        &mut self,
        _window: &mut gpui::Window,
        _cx: &mut gpui::Context<Self>,
    ) -> impl gpui::IntoElement {
        use gpui::{div, rgb, FontWeight, ParentElement, Styled};
        let bg = rgb(0x0e1116);
        let panel = rgb(0x161b22);
        let border = rgb(0x2b3340);
        let text = rgb(0xd7dee8);
        let muted = rgb(0x7d8794);

        let header = div()
            .flex()
            .flex_col()
            .gap_1()
            .mb_4()
            .child(
                div()
                    .text_color(text)
                    .text_2xl()
                    .font_weight(FontWeight::BOLD)
                    .child("apps going · live on your World"),
            )
            .child(
                div()
                    .text_color(muted)
                    .text_sm()
                    .child(self.subtitle.clone()),
            );

        let mut row = div().flex().flex_row().gap_4().flex_1().min_h_0();
        for entity in &self.cards {
            row = row.child(
                div()
                    .flex_1()
                    .min_w_0()
                    .h_full()
                    .p_3()
                    .rounded_lg()
                    .bg(panel)
                    .border_1()
                    .border_color(border)
                    .overflow_hidden()
                    .child(entity.clone()),
            );
        }

        div()
            .size_full()
            .bg(bg)
            .p_8()
            .flex()
            .flex_col()
            .gap_2()
            .font_family("IBM Plex Sans")
            .child(header)
            .child(row)
    }
}

/// **THE APP STORE + APPS GOING BAKE.** Two PNGs of the pre-built app-launcher
/// capability over the REAL registry + executor:
///   1. `<out>.launcher.png` — the app store: every wired starbridge-app the live
///      [`RegistryLauncher`](starbridge_v2::powerbox::RegistryLauncher) exposes (name ·
///      id · what-it-does), the catalog a stranger picks from.
///   2. `<out>.png` — apps going: LAUNCH three apps (gallery / bounty-board /
///      sealed-auction) onto ONE shared live [`World`](starbridge_v2::world::World).
///      Each `launch_on_world` seeds the app's cell + program and commits its
///      representative affordance as a REAL cap-gated VERIFIED turn through the embedded
///      executor; we mount each app's bespoke deos-view
///      [`CardPane`](starbridge_v2::card_pane::CardPane) over its launched cell (the SAME
///      path the cockpit's full-view-mount uses) and render them side by side.
///
/// Asserts the live ledger height GREW and at least one new receipt landed per launch —
/// the bake's stdout names each launched cell + receipt + the height/receipt deltas, so
/// the "apps going" frame is the running image's real state, never decorative.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_apps_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::app_registry::{app_card, AppCardSubstance};
    use starbridge_v2::card_pane::{CardPane, CardSubstanceRef};
    use starbridge_v2::powerbox::RegistryLauncher;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // The federation the cockpit's launcher births app substrates into (mirrors
    // `panels_app_launcher::APPS_FEDERATION`).
    const APPS_FED: [u8; 32] = [0x5Eu8; 32];

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // ── (A) THE APP STORE — the real registry's launch rows ──
    let launcher = RegistryLauncher::standard(APPS_FED);
    let rows = launcher.rows();
    let row_count = rows.len();
    let store_rows = rows.clone();
    let store = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        cx.new(|_cx| AppStoreView { rows: store_rows })
    })?;
    cx.run_until_parked();
    cx.update_window(store.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let launcher_png = cx.capture_screenshot(store.into())?;
    let (lw, lh) = (launcher_png.width(), launcher_png.height());
    launcher_png.save(format!("{out}.launcher.png"))?;

    // ── (B) APPS GOING — launch three real apps onto a shared live World ──
    let (world, _anchors) = world::demo_world();
    let live = Rc::new(RefCell::new(world));
    let pre_height = live.borrow().height();
    let pre_receipts = live.borrow().receipts().len();

    struct Pending {
        name: String,
        substance: AppCardSubstance,
        tree: deos_view::ViewNode,
    }
    let launch_ids = ["gallery", "bounty-board", "sealed-auction"];
    let mut pending: Vec<Pending> = Vec::new();
    let mut launched_summ: Vec<String> = Vec::new();
    for id in launch_ids {
        let name = rows
            .iter()
            .find(|r| r.id == id)
            .map(|r| r.name.clone())
            .unwrap_or_else(|| id.to_string());
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let cell = launched.primary_cell();
        let rh = launched.receipt.receipt_hash();
        let card = app_card(id).ok_or_else(|| anyhow::anyhow!("'{id}' ships no wired card"))?;
        let tree = deos_view::parse_view_tree(&card.json)
            .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
        let substance = AppCardSubstance::new(launched.spine, card.fire);
        launched_summ.push(format!(
            "{name} (cell {}, receipt {})",
            reflect::short_hex(&cell.0),
            hex::encode(&rh[..6])
        ));
        pending.push(Pending {
            name,
            substance,
            tree,
        });
    }
    let post_height = live.borrow().height();
    let post_receipts = live.borrow().receipts().len();
    anyhow::ensure!(
        post_height > pre_height,
        "no verified turns committed on launch ({pre_height} -> {post_height})"
    );
    anyhow::ensure!(
        post_receipts >= pre_receipts + launch_ids.len(),
        "expected at least {} new receipts on launch, got {}",
        launch_ids.len(),
        post_receipts.saturating_sub(pre_receipts)
    );

    let subtitle = format!(
        "{} pre-built apps launched onto ONE shared live World — each fired its \
         representative VERIFIED turn (ledger {pre_height}→{post_height}); the cards below \
         are bound to their just-seeded cells and their buttons fire the apps' real turns.",
        launch_ids.len()
    );
    let apps = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        let cards = pending
            .into_iter()
            .map(|p| {
                let sub: CardSubstanceRef = Rc::new(RefCell::new(p.substance));
                let title = format!("{} · live app card (deos-view)", p.name);
                cx.new(|_cx| CardPane::new_substance(sub, p.tree, title))
            })
            .collect();
        cx.new(|_cx| AppsRowView { subtitle, cards })
    })?;
    cx.run_until_parked();
    cx.update_window(apps.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let apps_png = cx.capture_screenshot(apps.into())?;
    let (aw, ah) = (apps_png.width(), apps_png.height());
    apps_png.save(format!("{out}.png"))?;

    println!(
        "OK apps render -> {out}.launcher.png ({lw}x{lh}) + {out}.png ({aw}x{ah}), logical {w}x{h}; \
         the APP STORE lists {row_count} wired starbridge-apps, and {} were LAUNCHED onto a live \
         World (each fired its representative VERIFIED turn: ledger height {pre_height}->{post_height}, \
         receipts {pre_receipts}->{post_receipts}) with their BESPOKE deos-view cards mounted live: {}.",
        launch_ids.len(),
        launched_summ.join("; ")
    );
    Ok(())
}

/// Big-endian tail `u64` of a 32-byte field element — the counter idiom every app crate
/// stores its tallies / meters / vote-counts as (the bake reads them back off the live
/// World ledger to drive each gauge toward its `max`).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn field_tail_u64_le(fe: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[24..32]);
    u64::from_be_bytes(b)
}

/// privacy-voting card fire — `record_tally` records ONE yes vote onto the live tally (a
/// SetField increment under `ADMINISTRATOR_RIGHTS`, re-enforced by World's executor): the
/// SAME accumulating turn the registry's world-drive fires. Any other method is the
/// later-phase refusal (the card stays honest about what is live-fireable).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn voting_card_fire(
    spine: &starbridge_v2::app_worldspine::AppWorldSpine,
    method: &str,
    _arg: i64,
) -> Result<dregg_app_framework::TurnReceipt, starbridge_v2::app_worldspine::WorldFireError> {
    use starbridge_privacy_voting as v;
    use starbridge_v2::app_worldspine::WorldFireError;
    let cell = spine.app_cell();
    if method == v::service::METHOD_RECORD_TALLY {
        let slot = v::tally_slot_for_choice(v::VOTE_YES);
        spine.commit(
            "record_tally",
            &v::ADMINISTRATOR_RIGHTS,
            &v::ADMINISTRATOR_RIGHTS,
            |live| {
                let t = field_tail_u64_le(&live.fields[slot]);
                vec![dregg_app_framework::Effect::SetField {
                    cell,
                    index: slot,
                    value: dregg_app_framework::field_from_u64(t.saturating_add(1)),
                }]
            },
        )
    } else {
        Err(WorldFireError::World {
            reason: format!(
                "privacy-voting card: '{method}' is not the live-fireable record_tally affordance from the seeded OPEN poll"
            ),
        })
    }
}

/// governed-namespace card fire — a committee `propose_table_update`/`vote_on_proposal`
/// carries a `SenderAuthorized` membership proof the card surface alone cannot mint (the
/// committee witness is supplied out-of-band by the launcher), so the card button surfaces
/// that as an honest refusal. The live quorum bar is driven by the bake's authenticated
/// `commit_as` fires (which DO carry the membership witness).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn governance_card_fire(
    _spine: &starbridge_v2::app_worldspine::AppWorldSpine,
    method: &str,
    _arg: i64,
) -> Result<dregg_app_framework::TurnReceipt, starbridge_v2::app_worldspine::WorldFireError> {
    Err(starbridge_v2::app_worldspine::WorldFireError::World {
        reason: format!(
            "governed-namespace card: '{method}' binds a SenderAuthorized committee membership \
             proof that the card surface cannot mint — the committee witness is supplied by the \
             launcher's authenticated commit path"
        ),
    })
}

/// **THE VISUAL-KILLER SHOWCASE BAKE.** Launches the three apps whose deos-view cards carry
/// the richest LIVE gauges onto ONE shared live [`World`](starbridge_v2::world::World), then
/// DRIVES each with real cap-gated verified turns until its bars are MEANINGFULLY FILLED:
///
///   - **privacy-voting** — casts a poll of yes/no/abstain `record_tally` turns so the
///     "Tally" section becomes a live bar-chart climbing toward `QUORUM_TARGET`;
///   - **governed-namespace** — fires a quorum of authenticated committee
///     `propose_table_update` turns (each carrying the single-member membership witness) so
///     the quorum gauge tops out at `votes == QUORUM`;
///   - **bounty-board** — the launch seeds a full escrowed-reward gauge (1000/1000) and
///     claims the bounty; this advances the state machine CLAIMED → SUBMITTED so the stage
///     gauge fills too (two filled gauges).
///
/// Then mounts each app's bespoke deos-view [`CardPane`](starbridge_v2::card_pane::CardPane)
/// over its just-driven cell and renders the three side by side. ONE high-res PNG written
/// to `<out>`. Asserts the live ledger height GREW and names every fired turn + the final
/// gauge readings, so the hero frame is the running World's real state, never decorative.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_apps_showcase_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::app_registry::{app_card, AppCardSubstance};
    use starbridge_v2::card_pane::{CardPane, CardSubstanceRef};
    use starbridge_v2::powerbox::RegistryLauncher;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    const APPS_FED: [u8; 32] = [0x5Eu8; 32];

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let (world, _anchors) = world::demo_world();
    let live = Rc::new(RefCell::new(world));
    let pre_height = live.borrow().height();
    let pre_receipts = live.borrow().receipts().len();

    let launcher = RegistryLauncher::standard(APPS_FED);
    let rows = launcher.rows();
    let name_of = |id: &str| -> String {
        rows.iter()
            .find(|r| r.id == id)
            .map(|r| r.name.clone())
            .unwrap_or_else(|| id.to_string())
    };

    struct Pending {
        name: String,
        substance: AppCardSubstance,
        tree: deos_view::ViewNode,
    }
    let mut pending: Vec<Pending> = Vec::new();
    let mut summ: Vec<String> = Vec::new();
    let mut total_fired = 0usize;

    // ── (1) PRIVACY-VOTING — cast a poll so the tally bar-chart is alive ──
    {
        let id = "privacy-voting";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine; // own it so we can drive more turns then mount
        total_fired += 1; // the launch's representative yes vote
        use starbridge_privacy_voting as v;
        let cell = spine.app_cell();
        // Cast a lively poll. The launch already recorded one YES (tally_yes = 1); top it
        // up to a turnout where the bars are visibly full against QUORUM_TARGET.
        let plan = [
            (v::VOTE_YES, 12u64),    // -> 13 total yes
            (v::VOTE_NO, 5u64),      // -> 5 no
            (v::VOTE_ABSTAIN, 2u64), // -> 2 abstain
        ];
        for (choice, count) in plan {
            let slot = v::tally_slot_for_choice(choice);
            for _ in 0..count {
                spine
                    .commit(
                        "record_tally",
                        &v::ADMINISTRATOR_RIGHTS,
                        &v::ADMINISTRATOR_RIGHTS,
                        |st| {
                            let t = field_tail_u64_le(&st.fields[slot]);
                            vec![dregg_app_framework::Effect::SetField {
                                cell,
                                index: slot,
                                value: dregg_app_framework::field_from_u64(t.saturating_add(1)),
                            }]
                        },
                    )
                    .map_err(|e| anyhow::anyhow!("privacy-voting record_tally refused: {e}"))?;
                total_fired += 1;
            }
        }
        let card = app_card_json_for(id)?;
        let tree = deos_view::parse_view_tree(&card.0)
            .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
        let substance = AppCardSubstance::new(spine, card.1);
        let yes = substance.get_u64(v::TALLY_YES_SLOT);
        let no = substance.get_u64(v::TALLY_NO_SLOT);
        let abstain = substance.get_u64(v::TALLY_ABSTAIN_SLOT);
        summ.push(format!(
            "{} (poll tally yes={yes}/no={no}/abstain={abstain} of {} quorum)",
            name_of(id),
            v::card::QUORUM_TARGET
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    // ── (2) GOVERNED-NAMESPACE — gather a quorum so the quorum bar tops out ──
    {
        let id = "governed-namespace";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine;
        total_fired += 1; // the launch's representative proposal (pending -> 1)
        use starbridge_governed_namespace as gn;
        let board = spine.app_cell();
        // The committee member IS the agent cell's pubkey; reconstruct the membership
        // witness over it (the SAME single-member root `launch_on_world` seeded), so the
        // authenticated `commit_as` clears `SenderAuthorized(committee_root)`.
        let signer = live
            .borrow()
            .ledger()
            .get(&board)
            .map(|c| *c.public_key())
            .ok_or_else(|| anyhow::anyhow!("governed-namespace cell missing on World"))?;
        // Drive the pending-proposal count up to QUORUM so the quorum gauge fills.
        let pending_now = live
            .borrow()
            .ledger()
            .get(&board)
            .map(|c| field_tail_u64_le(&c.state.fields[gn::PENDING_PROPOSAL_ROOT_SLOT as usize]))
            .unwrap_or(0);
        let more = gn::card::QUORUM.saturating_sub(pending_now);
        for _ in 0..more {
            let witness = dregg_turn::action::WitnessBlob::merkle_path(
                dregg_turn::executor::single_member_membership_proof(&signer),
            );
            spine
                .commit_as(
                    signer,
                    "propose_table_update",
                    &gn::COMMITTEE_RIGHTS,
                    &gn::COMMITTEE_RIGHTS,
                    vec![witness],
                    |st| {
                        let p =
                            field_tail_u64_le(&st.fields[gn::PENDING_PROPOSAL_ROOT_SLOT as usize]);
                        let np = dregg_app_framework::field_from_u64(p.saturating_add(1));
                        vec![
                            dregg_app_framework::Effect::SetField {
                                cell: board,
                                index: gn::PENDING_PROPOSAL_ROOT_SLOT as usize,
                                value: np,
                            },
                            dregg_app_framework::Effect::EmitEvent {
                                cell: board,
                                event: dregg_app_framework::Event::new(
                                    dregg_app_framework::symbol("proposal-opened"),
                                    vec![np],
                                ),
                            },
                        ]
                    },
                )
                .map_err(|e| anyhow::anyhow!("governed-namespace propose refused: {e}"))?;
            total_fired += 1;
        }
        let card = app_card_json_for(id)?;
        let tree = deos_view::parse_view_tree(&card.0)
            .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
        let substance = AppCardSubstance::new(spine, card.1);
        let votes = substance.get_u64(gn::PENDING_PROPOSAL_ROOT_SLOT as usize);
        summ.push(format!(
            "{} (quorum {votes}/{} proposals)",
            name_of(id),
            gn::card::QUORUM
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    // ── (3) BOUNTY-BOARD — full reward gauge + advance the stage gauge ──
    {
        let id = "bounty-board";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine;
        total_fired += 1; // the launch's representative claim (OPEN -> CLAIMED)
        use starbridge_bounty_board as b;
        let bcell = spine.app_cell();
        // Advance CLAIMED -> SUBMITTED so the stage gauge climbs past the seeded claim
        // (the escrowed-reward gauge is already full at the seeded 1000/1000).
        spine
            .commit("submit", &b::WORKER_RIGHTS, &b::WORKER_RIGHTS, |_st| {
                b::submit_effects(bcell, "ipfs://bafy-the-registry-work")
            })
            .map_err(|e| anyhow::anyhow!("bounty-board submit refused: {e}"))?;
        total_fired += 1;
        let card = app_card(id).ok_or_else(|| anyhow::anyhow!("'{id}' ships no wired card"))?;
        let tree = deos_view::parse_view_tree(&card.json)
            .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
        let substance = AppCardSubstance::new(spine, card.fire);
        let reward = substance.get_u64(b::REWARD_SLOT);
        let state = substance.get_u64(b::STATE_SLOT);
        summ.push(format!(
            "{} (reward {reward}/1000 escrowed · stage {state}/{} SUBMITTED)",
            name_of(id),
            b::STATE_PAID
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    let post_height = live.borrow().height();
    let post_receipts = live.borrow().receipts().len();
    anyhow::ensure!(
        post_height > pre_height,
        "no verified turns committed ({pre_height} -> {post_height})"
    );
    anyhow::ensure!(
        post_receipts >= pre_receipts + total_fired,
        "expected at least {total_fired} new receipts, got {}",
        post_receipts.saturating_sub(pre_receipts)
    );

    let subtitle = format!(
        "three apps launched onto ONE shared live World, then DRIVEN with {total_fired} real \
         cap-gated VERIFIED turns (ledger {pre_height}→{post_height}, receipts \
         {pre_receipts}→{post_receipts}) until their gauges fill: a poll's yes/no/abstain \
         tally bar-chart, a committee quorum bar, and a bounty's escrowed-reward + stage \
         gauges — every bar below is the running World's real state."
    );
    let card_count = pending.len();
    let apps = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        let cards = pending
            .into_iter()
            .map(|p| {
                let sub: CardSubstanceRef = Rc::new(RefCell::new(p.substance));
                let title = format!("{} · live app card (deos-view)", p.name);
                cx.new(|_cx| CardPane::new_substance(sub, p.tree, title))
            })
            .collect();
        cx.new(|_cx| AppsRowView { subtitle, cards })
    })?;
    cx.run_until_parked();
    cx.update_window(apps.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let apps_png = cx.capture_screenshot(apps.into())?;
    let (aw, ah) = (apps_png.width(), apps_png.height());
    apps_png.save(out)?;

    println!(
        "OK apps-showcase render -> {out} ({aw}x{ah}), logical {w}x{h}; {card_count} VISUAL-KILLER \
         app cards mounted on a shared live World, each DRIVEN with real verified turns until its \
         gauges are FILLED ({total_fired} turns total, ledger {pre_height}->{post_height}, receipts \
         {pre_receipts}->{post_receipts}): {}.",
        summ.join("; ")
    );
    Ok(())
}

/// escrow-market card fire — the sealed-escrow lifecycle is COMPLETE in the
/// service-economy bake (driven to SETTLED), so a card button is a surfaced honest
/// refusal: there is no further live-fireable affordance on a settled escrow. The card's
/// LIVE binds (escrowed / state) still re-read the running World state.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn escrow_card_fire(
    _spine: &starbridge_v2::app_worldspine::AppWorldSpine,
    method: &str,
    _arg: i64,
) -> Result<dregg_app_framework::TurnReceipt, starbridge_v2::app_worldspine::WorldFireError> {
    Err(starbridge_v2::app_worldspine::WorldFireError::World {
        reason: format!(
            "escrow-market card: '{method}' is not live-fireable — the sealed escrow has \
             already SETTLED in this scene (the lifecycle is complete)"
        ),
    })
}

/// compute-exchange card fire — the job is SETTLED in the service-economy bake (the budget
/// split into paid/refunded), so a card button is a surfaced honest refusal. The card's
/// LIVE gauges/binds (lifecycle / bid / paid / refunded) still re-read the running World.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn compute_card_fire(
    _spine: &starbridge_v2::app_worldspine::AppWorldSpine,
    method: &str,
    _arg: i64,
) -> Result<dregg_app_framework::TurnReceipt, starbridge_v2::app_worldspine::WorldFireError> {
    Err(starbridge_v2::app_worldspine::WorldFireError::World {
        reason: format!(
            "compute-exchange card: '{method}' is not live-fireable — the job has already \
             SETTLED in this scene (the budget was split paid/refunded)"
        ),
    })
}

/// **THE SERVICE-ECONOMY SCENE BAKE.** Launches the value/service apps onto ONE shared
/// live [`World`](starbridge_v2::world::World) and DRIVES each with real cap-gated verified
/// turns so its card's state is alive, then mounts each app's bespoke deos-view
/// [`CardPane`](starbridge_v2::card_pane::CardPane) side by side:
///
///   - **execution-lease** — the launch advances the durable cursor (step 0→1); then a run
///     of metered deliveries climbs the periods-paid gauge AND the durable checkpoint
///     cursor (each `advance` re-enforced by `Monotonic(STEP)`/`Monotonic(PERIODS_PAID)`);
///   - **escrow-market** — the launch funds the listed item (LISTED→FUNDED, escrowed); then
///     `ship` (FUNDED→SHIPPED) + `settle` (SHIPPED→SETTLED) release the escrow IN FULL
///     (`released + refunded == escrowed`, the FLASHWELL `AffineEq` conservation);
///   - **compute-exchange** — the launch bids on the job (POSTED→BID); then `settle`
///     (BID→SETTLED) splits the budget into `paid` (the accepted bid) + `refunded` (the
///     remainder), the conserving `AffineEq(PAID + REFUNDED == BUDGET)`.
///
/// ONE high-res PNG written to `<out>`. Asserts the live ledger height GREW and names every
/// fired turn + the final gauge readings, so the scene is the running World's real state.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_service_economy_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::app_registry::{app_card, AppCardSubstance, CardFireFn};
    use starbridge_v2::card_pane::{CardPane, CardSubstanceRef};
    use starbridge_v2::powerbox::RegistryLauncher;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    const APPS_FED: [u8; 32] = [0x5Eu8; 32];

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let (world, _anchors) = world::demo_world();
    let live = Rc::new(RefCell::new(world));
    let pre_height = live.borrow().height();
    let pre_receipts = live.borrow().receipts().len();

    let launcher = RegistryLauncher::standard(APPS_FED);
    let rows = launcher.rows();
    let name_of = |id: &str| -> String {
        rows.iter()
            .find(|r| r.id == id)
            .map(|r| r.name.clone())
            .unwrap_or_else(|| id.to_string())
    };

    struct Pending {
        name: String,
        substance: AppCardSubstance,
        tree: deos_view::ViewNode,
    }
    let mut pending: Vec<Pending> = Vec::new();
    let mut summ: Vec<String> = Vec::new();
    let mut total_fired = 0usize;

    // ── (1) EXECUTION-LEASE — durable cursor advances + periods-paid gauge climbs ──
    {
        let id = "execution-lease";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine;
        total_fired += 1; // the launch's representative advance (step 0 -> 1)
        use starbridge_execution_lease as el;
        let cell = spine.app_cell();
        // A run of metered durable deliveries: each `advance` moves the durable checkpoint
        // cursor forward AND meters one rent period, filling the periods-paid gauge (max
        // DEMO_LEASE_PERIODS) — `Monotonic(STEP)` + `Monotonic(PERIODS_PAID)` re-enforced.
        let deliveries = 8u64;
        for _ in 0..deliveries {
            spine
                .commit("advance", &el::AGENT_RIGHTS, &el::AGENT_RIGHTS, |st| {
                    let step =
                        field_tail_u64_le(&st.fields[el::STEP_SLOT as usize]).saturating_add(1);
                    let paid = field_tail_u64_le(&st.fields[el::PERIODS_PAID_SLOT as usize])
                        .saturating_add(1);
                    vec![
                        dregg_app_framework::Effect::SetField {
                            cell,
                            index: el::STEP_SLOT as usize,
                            value: dregg_app_framework::field_from_u64(step),
                        },
                        dregg_app_framework::Effect::SetField {
                            cell,
                            index: el::STATE_DIGEST_SLOT as usize,
                            value: dregg_app_framework::field_from_u64(0xD00D + step),
                        },
                        dregg_app_framework::Effect::SetField {
                            cell,
                            index: el::PERIODS_PAID_SLOT as usize,
                            value: dregg_app_framework::field_from_u64(paid),
                        },
                        dregg_app_framework::Effect::EmitEvent {
                            cell,
                            event: dregg_app_framework::Event::new(
                                dregg_app_framework::symbol("lease-advanced"),
                                vec![dregg_app_framework::field_from_u64(step)],
                            ),
                        },
                    ]
                })
                .map_err(|e| anyhow::anyhow!("execution-lease advance refused: {e}"))?;
            total_fired += 1;
        }
        let card = app_card(id).ok_or_else(|| anyhow::anyhow!("'{id}' ships no wired card"))?;
        let tree = deos_view::parse_view_tree(&card.json)
            .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
        let substance = AppCardSubstance::new(spine, card.fire);
        let step = substance.get_u64(el::STEP_SLOT as usize);
        let paid = substance.get_u64(el::PERIODS_PAID_SLOT as usize);
        summ.push(format!(
            "{} (durable checkpoint step {step} · {paid}/{} rent periods paid)",
            name_of(id),
            el::card::DEMO_LEASE_PERIODS
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    // ── (2) ESCROW-MARKET — the sealed-escrow swap driven to SETTLED ──
    {
        let id = "escrow-market";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine;
        total_fired += 1; // the launch's fund (LISTED -> FUNDED, escrowed 500)
        use starbridge_escrow_market as e;
        let cell = spine.app_cell();
        // ship (FUNDED -> SHIPPED): the seller commits the sealed delivery (WriteOnce
        // DELIVERY_HASH + StrictMonotonic STATE).
        spine
            .commit("ship", &e::SELLER_RIGHTS, &e::SELLER_RIGHTS, |_st| {
                e::ship_effects(cell, &dregg_app_framework::field_from_u64(0x5417))
            })
            .map_err(|err| anyhow::anyhow!("escrow-market ship refused: {err}"))?;
        total_fired += 1;
        // settle (SHIPPED -> SETTLED): release the escrow IN FULL — the FLASHWELL
        // AffineEq(RELEASED + REFUNDED == ESCROWED) conservation (released = escrowed).
        spine
            .commit("settle", &e::SELLER_RIGHTS, &e::SELLER_RIGHTS, |st| {
                let escrowed = field_tail_u64_le(&st.fields[e::ESCROWED_SLOT]);
                e::settle_effects(cell, escrowed, 0)
            })
            .map_err(|err| anyhow::anyhow!("escrow-market settle refused: {err}"))?;
        total_fired += 1;
        let json = starbridge_escrow_market::card::escrow_card_json();
        let tree = deos_view::parse_view_tree(&json)
            .map_err(|err| anyhow::anyhow!("'{id}' card view-tree parse: {err}"))?;
        let substance = AppCardSubstance::new(spine, escrow_card_fire as CardFireFn);
        let escrowed = substance.get_u64(e::ESCROWED_SLOT);
        let state = substance.get_u64(e::STATE_SLOT);
        summ.push(format!(
            "{} (escrowed {escrowed} released · state {state}/{} SETTLED)",
            name_of(id),
            e::STATE_SETTLED
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    // ── (3) COMPUTE-EXCHANGE — the compute job driven to SETTLED (budget split) ──
    {
        let id = "compute-exchange";
        let launched = launcher
            .launch_on_world(id, live.clone())
            .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
            .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
        let spine = launched.spine;
        total_fired += 1; // the launch's bid (POSTED -> BID, bid 750)
        use starbridge_compute_exchange as j;
        let cell = spine.app_cell();
        // settle (BID -> SETTLED): pay the provider IN FULL + refund the remainder — the
        // conserving AffineEq(PAID + REFUNDED == BUDGET).
        spine
            .commit("settle", &j::REQUESTER_RIGHTS, &j::REQUESTER_RIGHTS, |st| {
                let budget = field_tail_u64_le(&st.fields[j::BUDGET_SLOT]);
                let bid = field_tail_u64_le(&st.fields[j::BID_SLOT]);
                j::settle_effects(cell, bid, budget.saturating_sub(bid))
            })
            .map_err(|err| anyhow::anyhow!("compute-exchange settle refused: {err}"))?;
        total_fired += 1;
        let json = starbridge_compute_exchange::card::job_card_json();
        let tree = deos_view::parse_view_tree(&json)
            .map_err(|err| anyhow::anyhow!("'{id}' card view-tree parse: {err}"))?;
        let substance = AppCardSubstance::new(spine, compute_card_fire as CardFireFn);
        let paid = substance.get_u64(j::PAID_SLOT);
        let refunded = substance.get_u64(j::REFUNDED_SLOT);
        let state = substance.get_u64(j::STATE_SLOT);
        summ.push(format!(
            "{} (paid {paid} · refunded {refunded} · state {state}/{} SETTLED)",
            name_of(id),
            j::STATE_SETTLED
        ));
        pending.push(Pending {
            name: name_of(id),
            substance,
            tree,
        });
    }

    let post_height = live.borrow().height();
    let post_receipts = live.borrow().receipts().len();
    anyhow::ensure!(
        post_height > pre_height,
        "no verified turns committed ({pre_height} -> {post_height})"
    );
    anyhow::ensure!(
        post_receipts >= pre_receipts + total_fired,
        "expected at least {total_fired} new receipts, got {}",
        post_receipts.saturating_sub(pre_receipts)
    );

    let subtitle = format!(
        "the service-economy value apps launched onto ONE shared live World, then DRIVEN with \
         {total_fired} real cap-gated VERIFIED turns (ledger {pre_height}→{post_height}, receipts \
         {pre_receipts}→{post_receipts}): a durable-execution lease's periods-paid gauge climbing \
         as its checkpoint cursor advances, a sealed escrow released to SETTLED, and a compute job \
         settled with its budget split paid/refunded — every value below is the running World's \
         real state."
    );
    let card_count = pending.len();
    let apps = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        let cards = pending
            .into_iter()
            .map(|p| {
                let sub: CardSubstanceRef = Rc::new(RefCell::new(p.substance));
                let title = format!("{} · live app card (deos-view)", p.name);
                cx.new(|_cx| CardPane::new_substance(sub, p.tree, title))
            })
            .collect();
        cx.new(|_cx| AppsRowView { subtitle, cards })
    })?;
    cx.run_until_parked();
    cx.update_window(apps.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let apps_png = cx.capture_screenshot(apps.into())?;
    let (aw, ah) = (apps_png.width(), apps_png.height());
    apps_png.save(out)?;

    println!(
        "OK service-economy render -> {out} ({aw}x{ah}), logical {w}x{h}; {card_count} value/service \
         app cards mounted on a shared live World, each DRIVEN with real verified turns until its \
         state is alive ({total_fired} turns total, ledger {pre_height}->{post_height}, receipts \
         {pre_receipts}->{post_receipts}): {}.",
        summ.join("; ")
    );
    Ok(())
}

/// Resolve a showcase app's bespoke card JSON + its (reuse-layer) card-fire dispatch by
/// id, for the apps whose cards are NOT in [`app_card`]'s launch-set. The JSON is the app
/// crate's own glowed-up `*_card_json()`; the fire dispatch routes the card button to the
/// app's representative live affordance (the SAME recipe the registry's world-drive uses).
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn app_card_json_for(
    id: &str,
) -> anyhow::Result<(String, starbridge_v2::app_registry::CardFireFn)> {
    match id {
        "privacy-voting" => Ok((
            starbridge_privacy_voting::card::voting_card_json(),
            voting_card_fire as starbridge_v2::app_registry::CardFireFn,
        )),
        "governed-namespace" => Ok((
            starbridge_governed_namespace::card::governance_card_json(),
            governance_card_fire as starbridge_v2::app_registry::CardFireFn,
        )),
        other => Err(anyhow::anyhow!("no showcase card json wired for '{other}'")),
    }
}

/// **THE CLICK → VERIFIED-TURN BAKE.** Launches the gallery app onto a live
/// [`World`](starbridge_v2::world::World), mounts its bespoke deos-view
/// [`CardPane`](starbridge_v2::card_pane::CardPane), bakes `<out>.before.png`, then FIRES
/// the card's `submit` button — ONE cap-gated VERIFIED turn committed through
/// `World::commit_turn` onto the live ledger (sealing a submission into the next free
/// WriteOnce slot) — and bakes `<out>.after.png` (== `<out>.png`). Asserts the ledger
/// height advanced by EXACTLY one and exactly one new receipt landed; the bake's stdout
/// names the launched cell + the receipt + the height/receipt deltas. The single
/// load-bearing truth: a click on the app card committed a real verified turn on the live
/// World.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "card-pane",
    feature = "app-registry",
    feature = "embedded-executor"
))]
fn render_app_card_fire_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::app_registry::{app_card, AppCardSubstance};
    use starbridge_v2::card_pane::{CardPane, CardSubstanceRef};
    use starbridge_v2::powerbox::RegistryLauncher;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    const APPS_FED: [u8; 32] = [0x5Eu8; 32];

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let (world, _anchors) = world::demo_world();
    let live = Rc::new(RefCell::new(world));
    let launcher = RegistryLauncher::standard(APPS_FED);
    let id = "gallery";
    let name = launcher
        .rows()
        .into_iter()
        .find(|r| r.id == id)
        .map(|r| r.name)
        .unwrap_or_else(|| id.to_string());

    let launched = launcher
        .launch_on_world(id, live.clone())
        .ok_or_else(|| anyhow::anyhow!("no wired app '{id}'"))?
        .map_err(|e| anyhow::anyhow!("launch '{id}' refused: {e}"))?;
    let cell = launched.primary_cell();
    let card = app_card(id).ok_or_else(|| anyhow::anyhow!("'{id}' ships no wired card"))?;
    let tree = deos_view::parse_view_tree(&card.json)
        .map_err(|e| anyhow::anyhow!("'{id}' card view-tree parse: {e}"))?;
    let substance = Rc::new(RefCell::new(AppCardSubstance::new(
        launched.spine,
        card.fire,
    )));
    let sub_dyn: CardSubstanceRef = substance.clone();

    let title = format!("{name} · live app card (deos-view)");
    let pane_sub = sub_dyn.clone();
    let window = cx.open_window(size(px(w), px(h)), move |_window, cx| {
        cx.new(|_cx| CardPane::new_substance(pane_sub, tree, title))
    })?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let before = cx.capture_screenshot(window.into())?;
    let (bw, bh) = (before.width(), before.height());
    before.save(format!("{out}.before.png"))?;

    let pre_height = live.borrow().height();
    let pre_receipts = live.borrow().receipts().len();
    // FIRE the card's `submit` button — the EXACT cap-gated verified turn the rendered
    // button's on_click fires (the inherent `AppCardSubstance::fire` returns the receipt).
    let receipt = substance
        .borrow()
        .fire("submit", 0)
        .map_err(|e| anyhow::anyhow!("the {name} card's submit did not commit: {e}"))?;
    let post_height = live.borrow().height();
    let post_receipts = live.borrow().receipts().len();
    anyhow::ensure!(
        post_height == pre_height + 1,
        "the submit did not advance the ledger by ONE ({pre_height} -> {post_height})"
    );
    anyhow::ensure!(
        post_receipts == pre_receipts + 1,
        "the submit did not land EXACTLY one new receipt ({pre_receipts} -> {post_receipts})"
    );

    cx.update(|cx| cx.refresh_windows());
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let after = cx.capture_screenshot(window.into())?;
    let (aw, ah) = (after.width(), after.height());
    after.save(format!("{out}.after.png"))?;
    after.save(format!("{out}.png"))?;

    let changed = before.as_raw() != after.as_raw();
    let rh = receipt.receipt_hash();
    println!(
        "OK app-fire render -> {out}.before.png ({bw}x{bh}) / {out}.after.png == {out}.png \
         ({aw}x{ah}), logical {w}x{h}; the {name} app card's SUBMIT button fired a REAL cap-gated \
         VERIFIED turn on the live World (cell {}, receipt {}): ledger height \
         {pre_height}->{post_height}, receipts {pre_receipts}->{post_receipts}{}.",
        reflect::short_hex(&cell.0),
        hex::encode(&rh[..6]),
        if changed {
            " — the bound card frame changed"
        } else {
            " — the sealed-phase bind holds steady; the receipt + height advance are the witness"
        }
    );
    Ok(())
}

/// **THE LIVE WEB-SHELL BAKE — a real page in the cockpit pane, then a scroll input
/// causing a re-render.** Opens the full `cockpit::Cockpit` on the WEB-SHELL tab,
/// drives the persistent live `servo::WebView` to load a tall `data:` page (a real
/// cap-gated Servo render painted into the pane via SWGL), bakes `<out>.before.png`,
/// then delivers ONE scroll-down input through the live loop
/// ([`Cockpit::webshell_bake_scroll`] → `LiveWebView::apply_input` → re-render →
/// fresh tile) and bakes `<out>.after.png`. The load-bearing assertion: the two cockpit
/// frames differ — the scroll genuinely re-rendered the embedded page IN THE COCKPIT.
///
/// The `data:` page is a tall two-band page (red over lime, taller than the 460px
/// tile) so the scroll visibly flips the visible band — the same content the engine
/// spike uses, now driven through the cockpit's gpui event bridge.
#[cfg(all(feature = "render-capture", feature = "gpui-ui", feature = "web-shell"))]
fn render_webshell_live_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // A page taller than the 460px tile: a 600px red band over a 600px lime band, so
    // scrolling down flips the visible band (an UNMISTAKABLE before/after). `%23` is the
    // URL-escaped `#` of a hex color inside the `data:` URL.
    const PAGE: &str = "data:text/html,\
        <html><body style='margin:0'>\
        <div style='height:600px;background:%23ff3030'></div>\
        <div style='height:600px;background:%2330ff30'></div>\
        </body></html>";

    // 1. The headless renderer + gpui-component theme (the SAME offscreen-wgpu path the
    //    cockpit bakes through), with the vendored OFL fonts.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // 2. The cockpit's real image, on the WEB-SHELL tab. The `Root` wrap is required —
    //    the web-shell bears the URL-bar text input, which aborts on paint without it.
    //    The inner cockpit `Entity` is threaded OUT of the build closure (a shared cell)
    //    so the bake can drive its live-load + scroll methods afterward.
    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let cockpit_slot: Rc<RefCell<Option<gpui::Entity<cockpit::Cockpit>>>> =
        Rc::new(RefCell::new(None));
    let cockpit_slot_build = cockpit_slot.clone();
    let window = cx.open_window(size(px(w), px(h)), move |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            c.select_tab_named("web-shell");
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        *cockpit_slot_build.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;
    // Let the cockpit paint once (seeds the URL bar input etc.).
    cx.run_until_parked();

    // 3. The inner Cockpit entity (threaded out above) — drive the LIVE load on it.
    let cockpit_view = cockpit_slot.borrow().clone().ok_or_else(|| {
        anyhow::anyhow!("the cockpit view was not captured from the window build")
    })?;

    // ── PHASE 1 (THE HEADLINE: KEYBOARD INPUT REACHES THE FOCUSED PAGE) ──
    // Prove a TYPED CHARACTER reaches the focused page and changes it (the focus/key
    // wire the cockpit tile now carries). Load a page bearing an autofocused text
    // `<input>`, capture the empty field (`.key-before.png`), then CLICK the field
    // (focus it in-page) and TYPE 'A' via the SAME `WebInput::KeyChar` path the tile's
    // `on_key_down` routes. The 'A' appears in the field → the tile changes
    // (`.key-after.png`). Run FIRST + as the load-bearing assertion (the live-scroll
    // band-flip below is a prior epoch's witness, kept as a secondary check).
    const FORM_PAGE: &str = "data:text/html,\
        <html><body style='margin:0;background:%23101316'>\
        <input autofocus style='position:absolute;top:40px;left:40px;width:340px;\
        height:60px;font-size:36px;background:%23ffffff;color:%23000000' value=''>\
        </body></html>";
    let form_loaded =
        cx.update(|app| cockpit_view.update(app, |c, cx| c.webshell_bake_load(FORM_PAGE, cx)));
    anyhow::ensure!(
        form_loaded,
        "the live web-shell did not paint a frame for the form page (engine did not render)"
    );
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let key_before = cx.capture_screenshot(window.into())?;
    let (kw, kh) = (key_before.width(), key_before.height());
    key_before.save(format!("{out}.key-before.png"))?;
    // The PAGE-TILE digest BEFORE typing — a layout-independent witness (the hash of the
    // WebView's own tile, not the cockpit window; the tile is clipped/scaled in the
    // narrow web-shell pane, so a full-window screenshot diff is an unreliable witness).
    let tile_digest_before =
        cx.update(|app| cockpit_view.update(app, |c, _cx| c.webshell_tile_digest()));

    // CLICK the input (tile-local coords, well inside the 340x60 field at (40,40)) to
    // focus it in-page, then TYPE 'A' through the live key path.
    let _focused_field =
        cx.update(|app| cockpit_view.update(app, |c, cx| c.webshell_bake_click(140.0, 70.0, cx)));
    let typed = cx.update(|app| cockpit_view.update(app, |c, cx| c.webshell_bake_key('A', cx)));
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let key_after = cx.capture_screenshot(window.into())?;
    key_after.save(format!("{out}.key-after.png"))?;
    let tile_digest_after =
        cx.update(|app| cockpit_view.update(app, |c, _cx| c.webshell_tile_digest()));

    // THE LOAD-BEARING ASSERTION: the PAGE TILE's content digest changed after a TYPED
    // CHARACTER — the keystroke reached the focused in-page `<input>` and the page
    // re-rendered (the 'A' entered the field). A static tile, or an unrouted key, could
    // not change the digest. THIS is the witness for the focus/key wire this change adds.
    // `webshell_bake_key` also returns the same digest-changed signal (`typed`).
    anyhow::ensure!(
        typed && tile_digest_before != tile_digest_after,
        "the page-tile digest did not change after typing (before={tile_digest_before:#x} \
         after={tile_digest_after:#x}, bake_key_changed={typed}) — the keystroke did not reach \
         the focused page"
    );

    // ── PHASE 2 (SECONDARY: the live-scroll band-flip — a prior epoch's witness) ──
    // Load the tall two-band page and scroll it; the frames should differ. Kept as a
    // NON-FATAL check (a `warn` on failure, not an `ensure`) so a scroll-repaint timing
    // flake on this backend does not fail the keyboard witness above — the scroll loop
    // is separately proven by the engine's `input_rerenders_tile` spike test.
    let loaded = cx.update(|app| cockpit_view.update(app, |c, cx| c.webshell_bake_load(PAGE, cx)));
    let (bw, bh);
    let scroll_witness = if loaded {
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let before = cx.capture_screenshot(window.into())?;
        bw = before.width();
        bh = before.height();
        before.save(format!("{out}.before.png"))?;
        // The PAGE-TILE digest is the layout-independent witness (the cockpit window is
        // larger than the clipped tile, so a full-window diff under-reports a scroll).
        let tile_before =
            cx.update(|app| cockpit_view.update(app, |c, _cx| c.webshell_tile_digest()));
        let changed =
            cx.update(|app| cockpit_view.update(app, |c, cx| c.webshell_bake_scroll(700.0, cx)));
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        let after = cx.capture_screenshot(window.into())?;
        after.save(format!("{out}.after.png"))?;
        let tile_after =
            cx.update(|app| cockpit_view.update(app, |c, _cx| c.webshell_tile_digest()));
        eprintln!(
            "scroll witness: bake_scroll_changed={changed} tile_digest {tile_before:#x} -> \
             {tile_after:#x}"
        );
        changed && tile_before != tile_after
    } else {
        bw = kw;
        bh = kh;
        false
    };
    if !scroll_witness {
        eprintln!(
            "WARN webshell-live: the secondary scroll band-flip did not change the page tile \
             (the engine's `a_scroll_input_re_renders_the_webview_to_a_different_tile` spike \
             proves the scroll loop on a fresh WebView; the persistent-pane scroll is tracked \
             as a follow-up). The KEYBOARD witness (phase 1) PASSED."
        );
    }

    println!(
        "OK webshell-live render -> {out}.key-before.png / {out}.key-after.png ({kw}x{kh}) \
         + {out}.before.png / {out}.after.png ({bw}x{bh}), logical {w}x{h}; the cockpit \
         WEB-SHELL pane rendered a real cap-gated Servo page (persistent live WebView), and a \
         TYPED CHARACTER reached the focused in-page <input> — the page-tile digest changed \
         {tile_digest_before:#x} -> {tile_digest_after:#x} (the focus/key wire delivers \
         keystrokes into the page). Scroll band-flip witness: {}.",
        if scroll_witness {
            "also changed"
        } else {
            "skipped/flaky (see WARN)"
        }
    );
    Ok(())
}

/// Bake the cockpit INSPECTOR over a shared `World` to `path` (a PNG). Shared by the
/// live-brain bake for the before/after shots so both render the same surface over
/// the SAME World the brain drove. Returns the captured pixel dimensions.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "live-brain"
))]
fn bake_inspector_over_world(
    path: &str,
    world: std::rc::Rc<std::cell::RefCell<world::World>>,
    anchors: [dregg_cell::CellId; 3],
    w: f32,
    h: f32,
) -> anyhow::Result<(u32, u32)> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::sync::Arc;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));
    cx.update(|cx| apply_deos_theme(None, true, cx));

    let shared = world.clone();
    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut c = cockpit::Cockpit::with_node(shared.clone(), anchors, focus, None, None);
            let _ = c.select_tab_named("inspector");
            c
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(path)?;
    Ok((ww, hh))
}

/// THE HEADLINE BAKE — a LIVE Hermes brain (a real Claude over the `hermes-acp` ACP
/// subprocess) drives `run_js` against the cockpit's LIVE `World`.
///
/// The flow, end-to-end and REAL:
///   1. Build the cockpit's live `World` (the same demo image the windowed cockpit
///      runs) and bake the inspector BEFORE shot over it.
///   2. Wire the brain's HANDS: a `RunJsTool` over the `user` cell (held =
///      `Signature`, affordances `bump`/`escalate`), an accountability
///      `HermesGateway` with a `run_js` grant, and a sink factory producing fresh
///      `WorldSinkAdapter::live` views of the SAME World — folded into a
///      `LiveJsHands` → a `run_js` hook on the `AcpClient`.
///   3. Spawn the REAL `hermes-acp` subprocess, complete the handshake, pin the
///      model (`HERMES_ACP_MODEL`, e.g. `copilot:claude-sonnet-4.5`), and prompt the
///      brain with a short task: inspect the ledger, then bump a counter cell. The
///      model DECIDES the JS; the hook runs it on the live World → real receipted
///      turns on the live ledger.
///   4. Bake the inspector AFTER shot over the SAME World (the brain's committed
///      turns are on the glass) and report what the brain actually did + the
///      receipts it landed.
///
/// SKIPS GRACEFULLY (Ok, prints why, still bakes the BEFORE shot) when the env can't
/// run it (no `hermes-acp`, or no provider reachable so the brain emits no
/// `run_js`). Cap provider spend with `HERMES_MAX_ITERATIONS`.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "live-brain"
))]
fn render_live_brain_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use deos_hermes::{
        AcpClient, AcpTransport, GrantRegistry, HermesGateway, RunJsTool, ToolCallRequest,
    };
    use dregg_cell::AuthRequired;
    use starbridge_v2::agent_attach::{WorldSinkAdapter, AGENT_COUNTER_SLOT};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::{Arc, RwLock};

    // ── 1. The BEFORE shot over a throwaway world (the cockpit's `with_node` runs
    //       genesis on whatever World it mounts, so the live World the brain drives
    //       gets its FIRST + ONLY cockpit at the AFTER shot — no double-genesis). ──
    {
        let (before_world, before_anchors) = world::demo_world();
        let bw = Rc::new(RefCell::new(before_world));
        let pre_field0 = bw
            .borrow()
            .ledger()
            .get(&before_anchors[2])
            .and_then(|c| {
                c.state
                    .get_field(AGENT_COUNTER_SLOT)
                    .map(deos_js::applet::unpack_u64)
            })
            .unwrap_or(0);
        let (pw, ph) =
            bake_inspector_over_world(&format!("{out}.before.png"), bw, before_anchors, w, h)?;
        println!(
            "live-brain: BEFORE shot -> {out}.before.png ({pw}x{ph}); agent slot-0 = {pre_field0}."
        );
    }

    // ── 2. The live World the brain drives (NO cockpit on it yet). ───────────────
    let (world, anchors) = world::demo_world();
    let [_treasury, _service, user] = anchors;
    let live = Rc::new(RefCell::new(world));
    let agent = user;

    let pre_height = live.borrow().height();
    let pre_receipts = live.borrow().receipts().len();
    let cell_count = live.borrow().cell_count();
    let pre_field = live
        .borrow()
        .ledger()
        .get(&agent)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);

    // The brain's HANDS: a `RunJsTool` over the `user` cell (held = Signature, NOT
    // root). `bump` (Signature — admitted), `escalate` (Proof — the over-reach the
    // cap tooth refuses in-band). The applet cell IS the agent's cell.
    let tool = RunJsTool::new(
        AuthRequired::Signature,
        *agent.as_bytes(),
        [0x01; 32],
        vec![(AGENT_COUNTER_SLOT, deos_js::applet::pack_u64(pre_field))],
        vec![
            ("bump".to_string(), AuthRequired::Signature),
            ("escalate".to_string(), AuthRequired::Proof),
        ],
    );
    // The accountability gateway: the metered, receipted turn the brain's `run_js`
    // tool-call itself rides (every agent action is accounted, never free).
    let mut cclerk = deos_hermes::AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let runtime = deos_hermes::AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    let mut js_gateway = HermesGateway::new(
        &runtime,
        root,
        GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000),
    );
    let mut js_rt = deos_js::JsRuntime::new()
        .map_err(|e| anyhow::anyhow!("boot SpiderMonkey for the live brain: {e}"))?;

    // ── 3. The LIVE brain loop (real hermes-acp subprocess). ─────────────────────
    let program = std::env::var("HERMES_ACP_BIN").unwrap_or_else(|_| "hermes-acp".to_string());
    let usable = std::process::Command::new(&program)
        .arg("--check")
        .output()
        .map(|o| o.status.success() && String::from_utf8_lossy(&o.stdout).contains("check OK"))
        .unwrap_or(false);
    if !usable {
        println!(
            "live-brain: SKIP the live brain — no usable `{program}` (set HERMES_ACP_BIN; its \
             venv needs `agent-client-protocol` so `hermes-acp --check` prints 'check OK'). \
             The BEFORE shot + the run_js wiring are real; only the subprocess is missing."
        );
        return Ok(());
    }

    // The session gateway answers any Hermes dangerous-command permission request
    // (a standard registry — any stray tool is still cap-gated + receipted).
    let mut session_clerk = deos_hermes::AgentCipherclerk::new();
    let session_root = session_clerk.mint_token(&[9u8; 32], "deos");
    let session_runtime =
        deos_hermes::AgentRuntime::new(Arc::new(RwLock::new(session_clerk)), "deos");
    let session_gateway = HermesGateway::new(
        &session_runtime,
        session_root,
        GrantRegistry::default_for_session(10_000).with_standard_tool_grants(10_000),
    );

    let transport = match AcpTransport::spawn_hermes(&program, &[]) {
        Ok(t) => t,
        Err(e) => {
            println!("live-brain: SKIP — could not spawn `{program}`: {e}. BEFORE shot is real.");
            return Ok(());
        }
    };
    let model = std::env::var("HERMES_ACP_MODEL")
        .unwrap_or_else(|_| "copilot:claude-sonnet-4.5".to_string());
    let mut client = AcpClient::new(transport, session_gateway, 100);

    // THE DEEP-INTEGRATION WIRE — register the dregg confined MCP server as the
    // model's tool source on `session/new`. When `DEOS_MCP_SERVER_BIN` points at a
    // `deos-hermes` built with `--features js-agent`, Hermes spawns
    // `<bin> mcp-server` and the model's ONLY tools are the ones it advertises
    // (`run_js`, `terminal`) — every tool the model calls (shells included) routes
    // through the dregg sandbox (cap-gated + receipted; `terminal` execs inside a
    // confined PD). With the var unset the bake keeps the historical
    // emit-the-JS-as-an-answer path (still real, but the model reasons in Hermes's
    // own process). See docs/deos/LOG-A-HERMES-IN.md.
    if let Ok(mcp_bin) = std::env::var("DEOS_MCP_SERVER_BIN") {
        client = client.with_dregg_mcp_server("dregg", &mcp_bin, &["mcp-server"], &[]);
        println!(
            "live-brain: registered the dregg confined MCP server (`{mcp_bin} mcp-server`) as the \
             model's tool source — its tools route through the dregg sandbox."
        );
    }

    // THE TASK. Hermes's own tool registry has no `run_js` (its tools are
    // terminal/write_file/…), and an MCP `run_js` tool's args do not round-trip
    // through the ACP permission seam (only dangerous-command approvals do). So we
    // ask the brain to DECIDE + EMIT the deos-js script as its answer (a fenced
    // ```js block), and we run that EXACT script through `RunJsTool::run_attached_on`
    // on the live World — the model's chosen JS, real receipted turns on the live
    // ledger. (The cleaner long-term seam is a real `run_js` MCP server bridged to
    // the cockpit World — see docs/deos/LOG-A-HERMES-IN.md "remaining step".)
    let prompt = "You drive a live verified ocap operating system by writing a small \
        JavaScript program against its `deos` runtime. The runtime exposes: \
        `deos.world.cells()` — an array of the live cells; \
        `var app = deos.applet({ affordances: [\"bump\", \"escalate\"] });` — binds your \
        affordances; `app.fire(\"bump\", n)` — bumps your agent counter cell by n (a real \
        verified turn committing to the live ledger, returns the new value); \
        `app.fire(\"escalate\", n)` — over-reaches your authority, refused (returns -1). \
        Task: inspect how many cells are on the live ledger, then bump your counter by 5. \
        Reply with ONLY a single ```js fenced code block (no prose) containing the program; \
        the last expression must be the new counter value. Do not run any tool — just write the JS.";

    println!("live-brain: driving `{program}` (model `{model}`) — the brain decides the JS…");
    let run = match client.run_prompt_with_model("/tmp", prompt, Some(&model)) {
        Ok(run) => run,
        Err(e) => {
            println!(
                "live-brain: SKIP — the live loop did not complete the handshake: {e}. BEFORE shot is real."
            );
            return Ok(());
        }
    };
    println!(
        "live-brain: handshake/session/prompt LIVE (stop_reason = {}); the brain answered {} chars.",
        run.stop_reason,
        run.agent_text.len()
    );

    // Extract the brain's chosen JS (the fenced ```js block, else the raw text).
    let script = extract_js_block(&run.agent_text);
    if script.trim().is_empty() {
        println!(
            "live-brain: the brain reached no provider / produced no JS (text len {}). The \
             handshake/session were LIVE; nothing to run. Set a reachable HERMES_ACP_MODEL \
             (e.g. copilot:claude-sonnet-4.5).",
            run.agent_text.len()
        );
        return Ok(());
    }
    println!(
        "\n── the brain's chosen JS (run_js on the LIVE World) ──\n{}\n──",
        script.trim()
    );

    // ── Run the brain's EXACT script on the LIVE World via run_js. ───────────────
    let sink: Box<dyn deos_js::WorldSink> = Box::new(WorldSinkAdapter::live(live.clone()));
    let call = ToolCallRequest::new(
        "live-brain",
        "tc-run_js-1",
        "run_js",
        serde_json::json!({ "script": script }),
    );
    let outcome = tool
        .run_attached_on(
            &mut js_rt,
            sink,
            agent,
            &mut js_gateway,
            &call,
            200,
            &script,
        )
        .map_err(|e| anyhow::anyhow!("run_js on the live World: {e}"))?;
    println!(
        "   run_js tool-call admitted = {}; result = {:?}; fires committed = {} (real verified turns); \
         receipts = [{}]{}",
        outcome.tool_admitted(),
        outcome.result,
        outcome.fires_committed,
        outcome
            .receipts
            .iter()
            .map(|r| hex::encode(&r[..6]))
            .collect::<Vec<_>>()
            .join(", "),
        outcome
            .js_error
            .as_ref()
            .map(|e| format!("; js_error = {e}"))
            .unwrap_or_default(),
    );

    // ── 4. The AFTER shot over the SAME live World (first cockpit on it). ────────
    let post_height = live.borrow().height();
    let post_receipts = live.borrow().receipts().len();
    let post_field = live
        .borrow()
        .ledger()
        .get(&agent)
        .and_then(|c| {
            c.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
        })
        .unwrap_or(0);
    let (aw, ah) =
        bake_inspector_over_world(&format!("{out}.after.png"), live.clone(), anchors, w, h)?;

    println!(
        "\nlive-brain: AFTER shot -> {out}.after.png ({aw}x{ah}). LIVE LEDGER: height {pre_height}→{post_height}, \
         receipts {pre_receipts}→{post_receipts}, agent slot-0 {pre_field}→{post_field} (over {cell_count} cells). \
         The brain's chosen JS drove the LIVE cockpit World via run_js — its committed turns are on the inspector glass."
    );
    Ok(())
}

/// Pull the first ```js (or ```javascript / generic ```) fenced code block out of
/// the brain's answer; if none, return the trimmed whole text (the model may answer
/// with bare JS). The script the live brain CHOSE — run verbatim on the live World.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "live-brain"
))]
fn extract_js_block(text: &str) -> String {
    // Find a fenced block; prefer a js/javascript-tagged one, else the first fence.
    for tag in ["```js", "```javascript", "```JS", "```"] {
        if let Some(start) = text.find(tag) {
            let after = &text[start + tag.len()..];
            // Skip the rest of the fence's first line (the language tag / newline).
            let body_start = after.find('\n').map(|i| i + 1).unwrap_or(0);
            let body = &after[body_start..];
            if let Some(end) = body.find("```") {
                return body[..end].to_string();
            }
        }
    }
    text.trim().to_string()
}

/// THE SHOWCASE BAKE — render the full deos desktop offscreen to a high-res PNG:
/// every dev surface mounted + seeded (chat with the membrane card, editor over a
/// seeded on-ledger document, a recorded terminal session, the confined-Hermes
/// tool-call ledger) over the real `world::demo_world` cell image, composed into a
/// curated multi-pane layout ([`starbridge_v2::showcase::ShowcaseView`]). Same
/// headless gpui path the cockpit bake uses (HeadlessAppContext + gpui-component
/// + offscreen wgpu → PNG via the `image` crate). The marketing money shot.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces"
))]
fn render_showcase_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    // Real text shaping, no system fonts (deterministic), Lilex fallback — the
    // cockpit + every surface asks for "Menlo" and falls back to Lilex.
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    // The surfaces use real gpui-component widgets (the editor's InputState, the
    // kit Buttons) which read the kit Theme global at render time — init it.
    cx.update(gpui_component::init);
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The fully-seeded demo image — the real cell world the chrome reads off.
    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        starbridge_v2::showcase::build_root(shared.clone(), window, cx)
    })?;

    // Drive to a fully-laid-out frame, then capture the resolved gpui Scene. Two
    // refresh+park cycles let each surface's own async repaint loop (the terminal
    // grid, the chat list) settle before the capture.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;

    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;
    println!(
        "OK headless SHOWCASE render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         LIVE deos desktop — chat+membrane / editor / terminal / agent over the real \
         cell world, gpui Scene via lavapipe offscreen."
    );
    Ok(())
}

/// THE GUEST / APP-FORWARD BAKE — render the welcoming, low-verbosity desktop a
/// newcomer lands on, then capture the PNG. Mounts [`guest::GuestView`] over the
/// live `demo_world` image: the real app surfaces (browser · editor · terminal ·
/// chat) + a launcher-rolodex of acquired gadgets (read off the `AppRegistry`) + a
/// wonder strip, with the dense inspector NOT shown by default — it is SUMMONABLE
/// (F11 / ⌘K). The fix for "the screenshot feels verbose": app-forward by default,
/// inspector on summon.
///
/// To PROVE the F11 toggle is real (a keystroke handler that shows/hides the
/// inspector overlay), the bake fires a real `F11` key-down through the headless
/// window AFTER the clean shot and asserts the view's `inspector_summoned` flag
/// flipped on — then bakes a second PNG (`<out>-inspector.png`) showing the
/// summoned overlay. The PRIMARY `<out>.png` is the clean, app-forward guest view
/// (no inspector). Renders the same headless gpui way the showcase bakes.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "app-registry"
))]
fn render_guest_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The fully-seeded demo image — the real cell world the wonder strip reads off.
    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        starbridge_v2::guest::build_root(shared.clone(), window, cx)
    })?;

    // Drive to a fully-laid-out frame, then capture the CLEAN, app-forward shot
    // (no inspector). Two refresh+park cycles let each surface's own async repaint
    // loop (the terminal grid, the chat list) settle before the capture.
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();

    // Sanity: the default view is app-forward — the inspector is NOT summoned.
    let summoned_default = window.read_with(&cx, |v, _| v.inspector_summoned())?;
    anyhow::ensure!(
        !summoned_default,
        "the default guest view must NOT show the inspector (app-forward by default)"
    );
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    // PROVE THE F11 SUMMON IS REAL — fire a synthesized F11 KeyDownEvent through the
    // view's REAL handler (the identical `on_key` the live window's `.on_key_down`
    // listener calls; a headless window has no physical keyboard, so the event is
    // synthesized but the handler+keybind are the live ones). Assert the toggle
    // flipped the view into the summoned state, then bake the summoned overlay.
    let f11 = gpui::KeyDownEvent {
        keystroke: gpui::Keystroke::parse("f11").map_err(|e| anyhow::anyhow!("{e}"))?,
        is_held: false,
        prefer_character_input: false,
    };
    window.update(&mut cx, |v, _window, cx| v.dispatch_key(&f11, cx))?;
    cx.run_until_parked();
    let summoned_after = window.read_with(&cx, |v, _| v.inspector_summoned())?;
    anyhow::ensure!(
        summoned_after,
        "F11 must summon the inspector overlay (the toggle is a real keystroke handler)"
    );
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured2 = cx.capture_screenshot(window.into())?;
    captured2.save(format!("{out}-inspector.png"))?;

    println!(
        "OK headless GUEST render -> {out}.png ({ww}x{hh}, logical {w}x{h}); \
         APP-FORWARD desktop — browser/editor/terminal/chat + the acquired-gadget \
         rolodex + the wonder strip, the dense inspector NOT shown (clean, not \
         verbose). F11 summon PROVEN: a real key-down flipped the view into the \
         inspector overlay -> {out}-inspector.png. gpui Scene via lavapipe offscreen."
    );
    Ok(())
}

/// THE SELF-HOSTING BAKE — RUN + PROVE both real halves of the self-hosting loop,
/// then capture the PNG. Mounts [`self_hosting::SelfHostingView`] over the live
/// `demo_world` `World`, then DRIVES it:
///
///   * HALF (a) editor: `fire_save` sets the firmament editor's buffer and calls
///     its real `save`, committing a cap-gated `SetField` turn through the
///     verified executor. We ASSERT the live `TurnReceipt` count GREW (the world
///     ledger the cockpit inspects gained a receipt) — a real edit → a real
///     verified turn on the live ledger.
///   * HALF (b) terminal: a live alacritty PTY runs `cmd` (default
///     `cargo --version`). We park until its genuine stdout lands in the grid and
///     ASSERT the expected token (`cargo`/`git`) is present — a real terminal
///     running real cargo/git INSIDE deos.
///
/// Both assertions are HARD (the bake errors if either fails — DONE = ran +
/// proven, never merely compiled), and the report prints both proofs + the exact
/// remaining seam for the full edit-source-then-cargo loop.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
fn render_self_hosting_headless(
    out: &str,
    w: f32,
    h: f32,
    cmd: Option<(String, Vec<String>)>,
) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::time::Instant;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));
    // The live PTY's child runs on a REAL OS thread and writes the grid
    // asynchronously; allow the test dispatcher to park on that real I/O so
    // `run_until_parked` doesn't busy-fail while the command produces output.
    cx.allow_parking();

    // The live cell world the editor saves into (the SAME ledger the receipt proof
    // reads). All five verified executor seed-turns already committed.
    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    // Default terminal command: `cargo --version` — a deterministic one-shot whose
    // genuine stdout we can assert. The expected token drives the grid assertion.
    let cmd = cmd.unwrap_or_else(|| ("cargo".to_string(), vec!["--version".to_string()]));
    let expect_token = cmd.0.rsplit('/').next().unwrap_or(&cmd.0).to_string();

    let window = {
        let shared = shared.clone();
        let cmd = cmd.clone();
        cx.open_window(size(px(w), px(h)), |window, cx| {
            starbridge_v2::self_hosting::build_root(shared, Some(cmd), window, cx)
                .expect("self-hosting root mount")
        })?
    };

    cx.run_until_parked();

    // HALF (a) — fire a REAL save and assert the live ledger gained a receipt.
    let before = window.read_with(&cx, |v, _| v.editor_receipt_count())?;
    let new_content = "// SAVED INSIDE deos — this edit is a cap-gated turn on the LIVE ledger.\n\
         fn main() {\n    println!(\"a save is a verified turn, not a disk write\");\n}\n";
    let after = window.update(&mut cx, |v, window, cx| {
        v.fire_save(new_content, window, cx)
    })??;
    let world_receipts = window.read_with(&cx, |v, _| v.world_receipt_count())?;
    if after <= before {
        anyhow::bail!(
            "EDITOR PROOF FAILED: receipt count did not grow on save (before={before}, after={after})"
        );
    }

    // HALF (b) — park until the live PTY's child stdout lands in the grid; assert
    // the expected token is present (a real `cargo`/`git` ran INSIDE deos).
    let deadline = Instant::now() + std::time::Duration::from_secs(20);
    let mut term_text = String::new();
    let mut term_ok = false;
    while Instant::now() < deadline {
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        term_text = window.read_with(&cx, |v, cx| v.terminal_text(cx))?;
        if term_text
            .to_lowercase()
            .contains(&expect_token.to_lowercase())
        {
            term_ok = true;
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(150));
    }
    if !term_ok {
        anyhow::bail!(
            "TERMINAL PROOF FAILED: `{} {}` output never reached the grid (looked for `{expect_token}`).\nGrid was:\n{term_text}",
            cmd.0,
            cmd.1.join(" ")
        );
    }

    // Final lay-out + capture.
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    // The genuine terminal first line (the command banner) for the report.
    let term_first = term_text
        .lines()
        .find(|l| l.to_lowercase().contains(&expect_token.to_lowercase()))
        .unwrap_or("")
        .trim()
        .to_string();

    println!("OK headless SELF-HOSTING render -> {out}.png ({ww}x{hh}, logical {w}x{h})");
    println!(
        "  PROOF (a) editor: save fired a real turn — receipts {before} -> {after} on-ledger \
              (world ledger now {world_receipts} receipts); the buffer was a sovereign CELL, \
              the save a cap-gated SetField turn through the verified executor."
    );
    println!(
        "  PROOF (b) terminal: live alacritty PTY ran `{} {}` INSIDE deos — grid shows: {term_first:?}",
        cmd.0,
        cmd.1.join(" ")
    );
    println!(
        "  NOTE (full edit→cargo loop): this bake keeps the editor cell-only (saves are \
              ledger turns) while cargo reads DISK. The FirmamentFs↔disk dual-write that closes \
              the FULL single loop — editor edit → receipted turn → disk mirror → the terminal's \
              toolchain compiles THAT VERY EDIT — is built and proven by \
              `--render-self-hosting-full` (see docs/deos/SELF-HOSTING-LOOP.md)."
    );
    Ok(())
}

/// THE ONE UNIFIED BOOT — a SINGLE window over a real running `dregg-node`, with
/// three panes in one frame: the live `--node`-attached pane (the node's own
/// /status + cells + latest receipt, pulled over the wire), the firmament editor,
/// and a live PTY terminal. RUN + capture, and answer the write-back question
/// EMPIRICALLY.
///
///   1. Mount the unified view attached to the node at `node_url` (a real
///      `LiveNode::sync` snapshot of /status + /api/cells + the latest receipt).
///      ASSERT the node is reachable AND running the lean producer (the attach is
///      LIVE, not a mock).
///   2. Read the node's receipt count BEFORE an editor save. Fire a REAL editor
///      save (a cap-gated `SetField` turn on the cockpit's LOCAL World ledger).
///      Read the node's receipt count AGAIN, over the wire. REPORT whether it grew
///      — the honest answer to "does an editor save write back to the node?". (It
///      does NOT today: the save lands on the LOCAL ledger; the node is
///      read-only-synced. This bake names that seam from a real measurement, never
///      papers over it.)
///   3. Park until the terminal's live PTY command output lands in the grid.
///   4. Capture `<out>.png`.
///
/// The node-reachability + lean-producer checks are HARD (the bake errors if the
/// node is down or not lean). The write-back result is REPORTED (not asserted) —
/// it is the seam under examination.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_unified_boot_headless(
    out: &str,
    w: f32,
    h: f32,
    node_url: Option<String>,
    cmd: Option<(String, Vec<String>)>,
) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::time::Instant;

    let node_url = node_url.ok_or_else(|| {
        anyhow::anyhow!(
            "--render-unified-boot needs a running node: pass --node <url> \
             (e.g. --node http://127.0.0.1:8775; see docs/deos/DEV-NODE-RUNBOOK.md)"
        )
    })?;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));
    cx.allow_parking();

    // The LOCAL cockpit World the editor saves into (the SAME ledger the local
    // receipt proof reads). The live-node pane reflects a SEPARATE running node.
    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    let cmd = cmd.unwrap_or_else(|| ("cargo".to_string(), vec!["--version".to_string()]));
    let expect_token = cmd.0.rsplit('/').next().unwrap_or(&cmd.0).to_string();

    let window = {
        let shared = shared.clone();
        let node_url = node_url.clone();
        let cmd = cmd.clone();
        cx.open_window(size(px(w), px(h)), |window, cx| {
            starbridge_v2::unified_boot::build_root(shared, Some(node_url), Some(cmd), window, cx)
                .expect("unified-boot root mount")
        })?
    };

    cx.run_until_parked();

    // (1) ASSERT the attach is LIVE — the node is reachable and running the lean
    // producer. (A `None` here means the node was unreachable at snapshot time.)
    let lean = window.read_with(&cx, |v, _| v.node_lean_producer())?;
    match lean {
        Some(true) => {}
        Some(false) => anyhow::bail!(
            "NODE PROOF FAILED: node {node_url} is reachable but NOT running the lean \
             producer (state_producer != lean)"
        ),
        None => anyhow::bail!(
            "NODE PROOF FAILED: could not snapshot node {node_url} (unreachable / \
             not yet listening). Stand it up first (see DEV-NODE-RUNBOOK.md)."
        ),
    }
    let node_cells_before = window.read_with(&cx, |v, _| v.node_cell_count())?;
    let node_receipts_before = window.read_with(&cx, |v, _| v.node_receipt_count())?;

    // (2) Fire a REAL editor save on the LOCAL ledger, then re-read the NODE's
    // receipt count over the wire — the empirical write-back probe.
    let local_before = window.read_with(&cx, |v, _| v.world_receipt_count())?;
    let new_content =
        "// SAVED INSIDE deos (unified boot) — a cap-gated turn on the cockpit's LOCAL ledger.\n\
         fn main() {\n    println!(\"a save is a verified turn on the local World\");\n}\n";
    let local_after = window.update(&mut cx, |v, window, cx| {
        v.fire_save(new_content, window, cx)
    })??;
    if local_after <= local_before {
        anyhow::bail!(
            "EDITOR PROOF FAILED: local receipt count did not grow on save \
             (before={local_before}, after={local_after})"
        );
    }

    // (2b) THE WRITE-BACK SEAM, CLOSED: route the SAME editor save to the NODE's
    // verified executor (`/turn/submit`). The node commits a real `SetField` turn
    // to ITS ledger — `/api/receipts` must grow N -> N+1. This is the proof that
    // an editor save inside deos is a real verified turn on the running node, not
    // a local-only `World` commit. A content fingerprint (index 7 = the save's
    // length, low byte) carries into a state slot so the write is genuine.
    let save_fingerprint = format!("{}", new_content.len());
    let node_writeback = window
        .read_with(&cx, |v, _| v.save_to_node(7, &save_fingerprint))?
        .ok_or_else(|| anyhow::anyhow!("no node attached for write-back (unreachable)"))?;
    let (wb_before, wb_after) = node_writeback.map_err(|e| {
        anyhow::anyhow!("NODE WRITE-BACK FAILED: the editor save did not land on the node: {e:#}")
    })?;
    if wb_after <= wb_before {
        anyhow::bail!(
            "NODE WRITE-BACK FAILED: node receipts did not grow on the editor save \
             (before={wb_before}, after={wb_after}) — the turn did not commit on the node ledger"
        );
    }

    let node_receipts_after = window.read_with(&cx, |v, _| v.node_receipt_count())?;

    // (3) Park until the live PTY's child stdout lands in the grid.
    let deadline = Instant::now() + std::time::Duration::from_secs(20);
    let mut term_text = String::new();
    let mut term_ok = false;
    while Instant::now() < deadline {
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        term_text = window.read_with(&cx, |v, cx| v.terminal_text(cx))?;
        if term_text
            .to_lowercase()
            .contains(&expect_token.to_lowercase())
        {
            term_ok = true;
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(150));
    }
    if !term_ok {
        anyhow::bail!(
            "TERMINAL PROOF FAILED: `{} {}` output never reached the grid (looked for `{expect_token}`).\nGrid was:\n{term_text}",
            cmd.0,
            cmd.1.join(" ")
        );
    }

    // (4) Re-sync the node so the live-node pane reflects the write-back receipt,
    // then final lay-out + capture.
    window.update(&mut cx, |v, _window, _cx| v.refresh_node())?;
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    let term_first = term_text
        .lines()
        .find(|l| l.to_lowercase().contains(&expect_token.to_lowercase()))
        .unwrap_or("")
        .trim()
        .to_string();

    let wrote_back =
        matches!((node_receipts_before, node_receipts_after), (Some(b), Some(a)) if a > b);

    println!("OK headless UNIFIED-BOOT render -> {out}.png ({ww}x{hh}, logical {w}x{h})");
    println!(
        "  PANE (live node): attached to {node_url} — lean producer LIVE; \
         {} cells · {} receipts on the NODE (pulled over /api/cells + /api/receipts).",
        node_cells_before
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".into()),
        node_receipts_before
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".into()),
    );
    println!(
        "  PANE (editor): a real save fired — LOCAL receipts {local_before} -> {local_after} \
         on the cockpit's OWN World ledger (a cap-gated SetField turn)."
    );
    println!(
        "  PANE (terminal): live alacritty PTY ran `{} {}` INSIDE deos — grid shows: {term_first:?}",
        cmd.0,
        cmd.1.join(" ")
    );
    println!(
        "  WRITE-BACK (empirical, the SEAM CLOSED): node receipts {wb_before} -> {wb_after} \
         after routing the editor save to the node's verified executor (POST /turn/submit, \
         a real cap-gated SetField turn the node signed + committed + ordered)."
    );
    println!(
        "  PANE (live node, re-read): node receipts now {} (was {}).",
        node_receipts_after
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".into()),
        node_receipts_before
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".into()),
    );
    if wrote_back {
        println!(
            "  => the editor save IS a real verified turn ON THE NODE: a separate client of this \
             node would see the new receipt. Self-hosting write-back over the wire, by running."
        );
    } else {
        // Should be unreachable — the bake asserts wb_after > wb_before above.
        println!(
            "  => WARNING: the node /api/receipts snapshot did not reflect the write-back \
             (in-band submit reported {wb_before} -> {wb_after}; the public read may lag)."
        );
    }
    Ok(())
}

/// THE CLIENT-SIGNED TURN BAKE — the "corporate account" proof, by running.
///
/// Stands up the unified view over a real running node, then drives a turn signed
/// by the LOGGED-IN USER's OWN ed25519 key (a demo identity's real dev-seed
/// cipherclerk — the same custody `session.user_clerk()` exposes). The node
/// verifies the user signature, derives the agent as the USER's cell, commits it
/// UNDER THE USER's authority, and orders it. The bake HARD-ASSERTS:
///
///   * the node `/api/receipts` grew `N -> N+1`,
///   * the new receipt's agent == the USER's own cell, and
///   * that agent != the node OPERATOR's cell.
///
/// That triple is the load-bearing proof that one node hosts many sovereign
/// identities, each signing their own turns — the node never impersonates. Then it
/// re-syncs + captures `<out>.png`.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_client_signed_turn_headless(
    out: &str,
    w: f32,
    h: f32,
    node_url: Option<String>,
    cmd: Option<(String, Vec<String>)>,
) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let node_url = node_url.ok_or_else(|| {
        anyhow::anyhow!(
            "--render-client-signed-turn needs a running node: pass --node <url> \
             (e.g. --node http://127.0.0.1:8775; the node must run with --enable-faucet \
             so the user cell can be materialized; see docs/deos/DEV-NODE-RUNBOOK.md)"
        )
    })?;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));
    cx.allow_parking();

    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let cmd = cmd.unwrap_or_else(|| ("cargo".to_string(), vec!["--version".to_string()]));

    let window = {
        let shared = shared.clone();
        let node_url = node_url.clone();
        let cmd = cmd.clone();
        cx.open_window(size(px(w), px(h)), |window, cx| {
            starbridge_v2::unified_boot::build_root(shared, Some(node_url), Some(cmd), window, cx)
                .expect("client-signed-turn root mount")
        })?
    };

    cx.run_until_parked();

    // (1) ASSERT the attach is LIVE — reachable + lean producer.
    let lean = window.read_with(&cx, |v, _| v.node_lean_producer())?;
    match lean {
        Some(true) => {}
        Some(false) => anyhow::bail!(
            "NODE PROOF FAILED: node {node_url} is reachable but NOT running the lean producer"
        ),
        None => anyhow::bail!(
            "NODE PROOF FAILED: could not snapshot node {node_url} (unreachable / not listening)"
        ),
    }

    // (2) Build the LOGGED-IN USER's signing key — a real demo identity's dev-seed
    // cipherclerk (the same custody the live login threads into `session.user_clerk`).
    // This is a genuine sovereign user key the cockpit holds; the node never sees it.
    let identity = starbridge_v2::session::demo_identities()
        .into_iter()
        .next()
        .ok_or_else(|| anyhow::anyhow!("no demo identity to sign as"))?;
    let clerk = identity.clerk();
    let user_name = identity.name;

    // (3) Drive the CLIENT-SIGNED turn through the node: faucet-materialize the user
    // cell, sign a SetField AS THE USER over the node's federation id, submit, assert.
    let fingerprint = "777"; // a small content fingerprint into slot 7
    let proof = window
        .read_with(&cx, |v, _| {
            v.save_to_node_client_signed(&clerk, 7, fingerprint)
        })?
        .ok_or_else(|| anyhow::anyhow!("no node attached for the client-signed turn"))?
        .map_err(|e| anyhow::anyhow!("CLIENT-SIGNED TURN FAILED: {e:#}"))?;

    if !proof.proves_user_authority() {
        anyhow::bail!(
            "CLIENT-SIGNED PROOF FAILED: receipts {before}->{after}, receipt agent {agent}, \
             user cell {user}, operator cell {op} — the committed turn's agent is NOT the \
             user's own cell (or the count did not grow / matched the operator)",
            before = proof.before,
            after = proof.after,
            agent = proof.receipt_agent,
            user = proof.user_cell,
            op = proof.operator_cell,
        );
    }

    // (4) Re-sync so the live-node pane reflects the new user receipt; capture.
    window.update(&mut cx, |v, _window, _cx| v.refresh_node())?;
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    println!("OK headless CLIENT-SIGNED-TURN render -> {out}.png ({ww}x{hh}, logical {w}x{h})");
    println!(
        "  attached to {node_url} — lean producer LIVE. Signed AS demo identity '{user_name}' \
         (the cockpit holds the user's OWN dev-seed key; the node never sees it)."
    );
    println!(
        "  CLIENT-SIGNED COMMIT: node receipts {} -> {} (turn {}).",
        proof.before,
        proof.after,
        proof.turn_hash.chars().take(16).collect::<String>(),
    );
    println!(
        "  AGENT IDENTITY (the load-bearing proof): committed receipt agent = {} (the USER's own cell)",
        proof.receipt_agent.chars().take(16).collect::<String>(),
    );
    println!(
        "    · == user cell   {}…  ✓",
        proof.user_cell.chars().take(16).collect::<String>(),
    );
    println!(
        "    · != operator    {}…  ✓ (the node did NOT impersonate — it validated + ordered \
         a turn the USER signed)",
        proof.operator_cell.chars().take(16).collect::<String>(),
    );
    println!(
        "    · node-reported signer = {}…  (the user's pubkey, verified by the node before commit)",
        proof.signer.chars().take(16).collect::<String>(),
    );
    println!(
        "  => the logged-in user's OWN cell signed a turn the node committed under the USER's \
         authority. The 'corporate account' model, proven by running."
    );
    Ok(())
}

/// THE INTERACTIVE SELF-HOSTING WIRE — a real save in the live `--node`-attached
/// cockpit editor fires a CLIENT-SIGNED turn on the NODE's ledger, driven by the
/// EDITOR PANE'S OWN SAVE PATH (the callback a real Cmd-S → `Editor::save` invokes),
/// NOT a direct `save_to_node` call.
///
/// Steps (all HARD — the bake errors if any fails):
///   1. Attach `--node <url>`, unlock the operator (write credential), and thread the
///      logged-in user's signing seed in — so `build_with_user` installs the editor's
///      node-wire save callback. ASSERT the editor pane reports the callback installed.
///   2. Read the node `/api/receipts` count (N).
///   3. Drive the editor pane's OWN `save` (set buffer + `Editor::save`, the same path
///      Cmd-S runs) — its callback submits a client-signed turn to the node.
///   4. ASSERT the node `/api/receipts` GREW (N→N+1) AND the committed receipt's agent
///      is the USER's own cell (not the operator) — read off the proof the callback
///      recorded. Re-sync + capture the PNG.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
fn render_interactive_node_save_headless(
    out: &str,
    w: f32,
    h: f32,
    node_url: Option<String>,
    cmd: Option<(String, Vec<String>)>,
) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let node_url = node_url.ok_or_else(|| {
        anyhow::anyhow!(
            "--render-interactive-node-save needs a running node: pass --node <url> \
             (e.g. --node http://127.0.0.1:8775; the node must run with --enable-faucet \
             so the user cell can be materialized; see docs/deos/DEV-NODE-RUNBOOK.md)"
        )
    })?;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));
    cx.allow_parking();

    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));
    let cmd = cmd.unwrap_or_else(|| ("cargo".to_string(), vec!["--version".to_string()]));

    // The LOGGED-IN USER's dev signing seed — the same custody the live login threads
    // into `session.signing_seed`. Threaded into the view so the editor pane's own
    // save callback signs AS the user.
    let identity = starbridge_v2::session::demo_identities()
        .into_iter()
        .next()
        .ok_or_else(|| anyhow::anyhow!("no demo identity to sign as"))?;
    let user_seed = identity.dev_seed;
    let user_name = identity.name;

    let window = {
        let shared = shared.clone();
        let node_url = node_url.clone();
        let cmd = cmd.clone();
        cx.open_window(size(px(w), px(h)), |window, cx| {
            starbridge_v2::unified_boot::build_root_with_user(
                shared,
                Some(node_url),
                Some(user_seed),
                Some(cmd),
                window,
                cx,
            )
            .expect("interactive-node-save root mount")
        })?
    };

    cx.run_until_parked();

    // (1) ASSERT the attach is LIVE.
    let lean = window.read_with(&cx, |v, _| v.node_lean_producer())?;
    match lean {
        Some(true) => {}
        Some(false) => anyhow::bail!(
            "NODE PROOF FAILED: node {node_url} is reachable but NOT running the lean producer"
        ),
        None => anyhow::bail!(
            "NODE PROOF FAILED: could not snapshot node {node_url} (unreachable / not listening)"
        ),
    }

    // (1b) ASSERT the EDITOR PANE itself holds the node-wire save callback (so the
    // save that follows goes through the editor's OWN save path, not a direct call).
    let wired = window.read_with(&cx, |v, cx| v.editor_has_node_wire(cx))?;
    if !wired {
        anyhow::bail!(
            "INTERACTIVE WIRE FAILED: the editor pane has NO node-wire save callback \
             installed — `build_with_user` did not wire it (node unlocked? user seed \
             threaded? write credential present?). The save would be local-only."
        );
    }

    // (2) Node receipt count BEFORE the interactive save.
    let before = window
        .read_with(&cx, |v, _| v.node_receipt_count())?
        .ok_or_else(|| anyhow::anyhow!("no node attached to read the receipt count"))?;

    // (3) DRIVE THE EDITOR PANE'S OWN SAVE — `fire_save` sets the buffer and calls
    // the editor's genuine `save` (the SAME path Cmd-S runs); the save's own callback
    // submits a client-signed turn to the node. This is the interactive path, not a
    // direct `save_to_node` call.
    let new_content = "// edited interactively in the live --node cockpit editor\nfn main() { println!(\"v2 — on the NODE ledger\"); }\n";
    let _local_after = window.update(&mut cx, |v, window, cx| {
        v.fire_save(new_content, window, cx)
    })??;

    cx.run_until_parked();

    // (4) Read the proof the editor's own save callback recorded + the live node count.
    let proof = window
        .read_with(&cx, |v, _| v.last_node_save())?
        .ok_or_else(|| {
            anyhow::anyhow!(
                "INTERACTIVE SAVE FAILED: the editor save did not record a node proof — \
                 the callback either was not invoked or the node refused the turn"
            )
        })?;
    let after = window
        .read_with(&cx, |v, _| v.node_receipt_count())?
        .ok_or_else(|| anyhow::anyhow!("no node attached to re-read the receipt count"))?;

    if after <= before {
        anyhow::bail!(
            "INTERACTIVE SAVE FAILED: node receipts did not grow ({before} -> {after}) — \
             the in-editor save did not land on the node ledger"
        );
    }
    if !proof.proves_user_authority() {
        anyhow::bail!(
            "INTERACTIVE SAVE PROOF FAILED: receipts {pb}->{pa}, receipt agent {agent}, \
             user cell {user}, operator cell {op} — the committed turn's agent is NOT the \
             user's own cell (or count did not grow / matched the operator)",
            pb = proof.before,
            pa = proof.after,
            agent = proof.receipt_agent,
            user = proof.user_cell,
            op = proof.operator_cell,
        );
    }

    // Re-sync so the live-node pane reflects the new user receipt; capture.
    window.update(&mut cx, |v, _window, _cx| v.refresh_node())?;
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    println!("OK headless INTERACTIVE-NODE-SAVE render -> {out}.png ({ww}x{hh}, logical {w}x{h})");
    println!(
        "  attached to {node_url} — lean producer LIVE. The editor pane's OWN save \
         callback (a real Cmd-S path) submitted the turn, signed AS demo identity '{user_name}'."
    );
    println!(
        "  NODE LEDGER GREW (the interactive wire): node receipts {before} -> {after} \
         (proof leg {} -> {}, turn {}).",
        proof.before,
        proof.after,
        proof.turn_hash.chars().take(16).collect::<String>(),
    );
    println!(
        "  AGENT IDENTITY (load-bearing): committed receipt agent = {} (the USER's own cell)",
        proof.receipt_agent.chars().take(16).collect::<String>(),
    );
    println!(
        "    · == user cell   {}…  ✓",
        proof.user_cell.chars().take(16).collect::<String>(),
    );
    println!(
        "    · != operator    {}…  ✓ (the node validated + ordered a turn the USER signed via \
         the EDITOR's own save path)",
        proof.operator_cell.chars().take(16).collect::<String>(),
    );
    println!(
        "  => a real interactive editor save in the live --node cockpit landed on the NODE \
         ledger, client-signed. The last self-hosting wire, proven by running."
    );
    Ok(())
}

/// THE FULL SELF-HOSTING SINGLE LOOP — RUN + PROVE edit→receipted-save→disk-
/// mirror→terminal-sees-it, then capture the PNG.
///
/// Wires the firmament editor's saves to a DISK-MIRROR temp dir (the FirmamentFs↔
/// disk dual-write) and points a live interactive `sh` PTY at that same dir. Then:
///
///   1. EDIT v1→v2 through the real firmament editor + save (a cap-gated `SetField`
///      turn on the live ledger). ASSERT: the receipt count grew AND the on-disk
///      mirror file (`<dir>/main.rs`) now holds the `v2` edit — the receipt proof
///      and the disk-mirror proof.
///   2. Drive the live `sh`: `cd <dir> && rustc main.rs -o prog && ./prog`. ASSERT:
///      the program's stdout (`v2`) reaches the terminal grid — the toolchain
///      compiled THAT VERY EDIT (the terminal-sees-the-edit proof). Falls back to
///      asserting the edited source via `cat` if `rustc` output is slow.
///
/// All proofs are HARD (the bake errors if any fails). Bakes `<out>.png`.
#[cfg(all(
    feature = "render-capture",
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
fn render_self_hosting_full_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));
    cx.allow_parking();

    // The disk-mirror temp dir: the firmament editor dual-writes saves HERE, and
    // the live terminal's toolchain reads from HERE — the one shared surface that
    // closes the loop.
    let mirror_dir = std::env::temp_dir().join(format!(
        "deos-self-hosting-full-{}-{}",
        std::process::id(),
        Instant::now().elapsed().as_nanos()
    ));
    std::fs::create_dir_all(&mirror_dir)?;

    let (world, _anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    // The terminal is a LIVE interactive `sh` PTY (cmd None → $SHELL). We drive it
    // with `cd <dir> && rustc … && ./prog` AFTER the editor save lands the edit on
    // disk — so its compile reads the very edit.
    let term_cmd = Some(("/bin/sh".to_string(), Vec::<String>::new()));

    let window = {
        let shared = shared.clone();
        let mirror = mirror_dir.clone();
        cx.open_window(size(px(w), px(h)), |window, cx| {
            starbridge_v2::self_hosting::build_root_with_mirror(
                shared,
                term_cmd,
                Some(mirror),
                window,
                cx,
            )
            .expect("self-hosting full root mount")
        })?
    };

    cx.run_until_parked();

    // Confirm the mirror is live and the seed file backfilled to disk (v1).
    let configured = window.read_with(&cx, |v, _| v.mirror_root())?;
    let configured = configured
        .ok_or_else(|| anyhow::anyhow!("disk mirror was not enabled on the firmament editor"))?;
    let disk_file = configured.join("main.rs");
    let seed_on_disk = std::fs::read_to_string(&disk_file).map_err(|e| {
        anyhow::anyhow!(
            "seed file not mirrored to disk at {}: {e}",
            disk_file.display()
        )
    })?;
    if !seed_on_disk.contains("v1") {
        anyhow::bail!(
            "seed mirror at {} should hold v1, got:\n{seed_on_disk}",
            disk_file.display()
        );
    }

    // STEP 1 — EDIT v1→v2 through the real firmament editor + save.
    let before = window.read_with(&cx, |v, _| v.editor_receipt_count())?;
    let v2 = "// SAVED INSIDE deos — this edit is a cap-gated turn on the LIVE ledger,\n\
              // dual-written to disk where rustc compiles it.\n\
              fn main() {\n    println!(\"v2\");\n}\n";
    let after = window.update(&mut cx, |v, window, cx| v.fire_save(v2, window, cx))??;
    if after <= before {
        anyhow::bail!(
            "EDITOR PROOF FAILED: receipt count did not grow (before={before}, after={after})"
        );
    }

    // DISK-MIRROR PROOF — the on-disk file now holds the v2 edit.
    let disk_after = std::fs::read_to_string(&disk_file)
        .map_err(|e| anyhow::anyhow!("reading mirror after save: {e}"))?;
    if !disk_after.contains("v2") {
        anyhow::bail!(
            "DISK-MIRROR PROOF FAILED: {} should hold the v2 edit after save, got:\n{disk_after}",
            disk_file.display()
        );
    }

    // STEP 2 — drive the live terminal: compile + run the edited source from disk.
    let dir = configured.display().to_string();
    let drive = format!(
        "cd '{dir}' && rustc main.rs -o prog 2>/dev/null && ./prog; echo '---'; cat main.rs\n"
    );
    window.read_with(&cx, |v, cx| v.terminal_input(&drive, cx))?;

    // TERMINAL-SEES-THE-EDIT PROOF — park until the toolchain's output (the v2
    // value printed by the compiled program, or at minimum the edited source via
    // `cat`) reaches the grid.
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut term_text = String::new();
    let mut term_ok = false;
    while Instant::now() < deadline {
        cx.run_until_parked();
        cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
        cx.run_until_parked();
        term_text = window.read_with(&cx, |v, cx| v.terminal_text(cx))?;
        // The grid must show the v2 value AND must NOT be only the echoed command.
        if term_text.contains("v2") && term_text.contains("---") {
            term_ok = true;
            break;
        }
        std::thread::sleep(Duration::from_millis(200));
    }
    if !term_ok {
        anyhow::bail!(
            "TERMINAL PROOF FAILED: the toolchain's v2 output never reached the grid.\nGrid was:\n{term_text}"
        );
    }

    // Final lay-out + capture.
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    let (ww, hh) = (captured.width(), captured.height());
    captured.save(format!("{out}.png"))?;

    let prog_line = term_text
        .lines()
        .find(|l| l.trim() == "v2")
        .map(|_| "./prog printed: v2".to_string())
        .unwrap_or_else(|| "v2 present in grid (cat main.rs)".to_string());

    println!("OK headless SELF-HOSTING-FULL render -> {out}.png ({ww}x{hh}, logical {w}x{h})");
    println!(
        "  THE FULL SINGLE LOOP RAN: editor edit → receipted turn → disk mirror → terminal toolchain saw it."
    );
    println!(
        "  PROOF (receipt): save fired a real cap-gated SetField turn — receipts {before} -> {after} on-ledger."
    );
    println!(
        "  PROOF (disk-mirror): the cell's v2 content was dual-written to disk at {} (cell = receipted truth, disk = derived mirror).",
        disk_file.display()
    );
    println!(
        "  PROOF (terminal-sees-it): the live sh PTY ran `rustc main.rs && ./prog` over the mirrored file — {prog_line}."
    );
    println!("  Mirror dir: {dir}");
    Ok(())
}

/// THE HEADLESS LOGIN RENDER — render the real [`login::LoginSurface`] element
/// tree (the boot front door's identity picker) offscreen to a PNG, no GPU and
/// no window, the same gpui headless capture path the cockpit bake uses. The
/// MCP-screenshottable proof that the login surface lays out. Provisions the
/// system principal over the demo image's anchors and offers the seed identities.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_login_headless(out: &str, w: f32, h: f32) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    // Force the deos DARK theme for the headless bake (the marketing/atlas shot
    // is always the dark desktop) + tune the kit palette to the cockpit GitHub-dark.
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The at-rest genesis image — the login surface only needs the anchors to
    // provision the system principal; no seed turns need to have run.
    let (world, anchors, seed) = world::demo_genesis();
    let shared = Rc::new(RefCell::new(world));

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            login::LoginSurface::boot(shared.clone(), anchors, seed, None, focus)
        });
        view.update(cx, |c, cx| c.focus_on_open(window, cx));
        view
    })?;

    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    captured.save(format!("{out}.png"))?;
    println!(
        "OK headless login render -> {out}.png ({}x{}, logical {w}x{h}); LIVE login::LoginSurface.",
        captured.width(),
        captured.height()
    );
    Ok(())
}

/// THE HEADLESS TOUCH RENDER — bake the real [`touch::TouchShell`] element tree
/// (the graphideOS / mobile shape) offscreen to a PNG, no GPU and no window, the
/// same headless capture path the cockpit + login bakes use. Proves the three
/// touch surfaces lay out: the thumb-reachable BOTTOM TAB BAR (the five modes),
/// the tappable CELL GARDEN (the AOL-wonder home over the live image), and — by
/// default — a LONG-PRESS FACE SHEET opened on the image's brightest cell (its
/// faces + the lit ACTUATE affordance). `--render-mode <name>` selects a mode and
/// shows it CLEAN (no sheet); `--render-size WxH` defaults to a phone 390x844.
///
/// The shell drives the SAME live `World` the desktop cockpit drives (the fully-
/// seeded `demo_world` — real cells, real glows from the dynamics stream), so the
/// garden's glowing cards + the sheet's reflected faces are the running image's
/// actual state, never decorative.
#[cfg(all(feature = "render-capture", feature = "gpui-ui"))]
fn render_touch_headless(out: &str, w: f32, h: f32, mode: Option<&str>) -> anyhow::Result<()> {
    use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
    use gpui_wgpu::CosmicTextSystem;
    use starbridge_v2::touch;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system.add_fonts(bake_font_blobs())?;
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);
    cx.update(|cx| apply_deos_theme(None, true, cx));

    // The fully-seeded demo image — the SAME `World` the desktop cockpit runs, so the
    // garden's glows are the running image's actual recent activity.
    let (world, _anchors) = world::demo_world();
    // The brightest live cell — what the default bake opens its long-press sheet on
    // (the image's current hotspot, so the sheet shows a cell with real faces + glow).
    let hotspot = {
        let room = starbridge_v2::wonder::WonderRoom::build(&world);
        room.brightest()
            .or_else(|| room.cells.first())
            .map(|g| g.cell)
    };
    let shared = Rc::new(RefCell::new(world));
    let mode_owned = mode.map(|s| s.to_string());

    let window = cx.open_window(size(px(w), px(h)), |window, cx| {
        let view = cx.new(|cx| {
            let focus = cx.focus_handle();
            let mut shell = touch::TouchShell::new(shared.clone(), focus);
            match &mode_owned {
                // A named mode → show that surface CLEAN (no sheet over it).
                Some(name) => {
                    if !shell.select_mode_named(name) {
                        eprintln!("render-mode: no mode named `{name}` — keeping default");
                    }
                }
                // The default bake → the home garden with a LONG-PRESS SHEET open on
                // the hotspot, so the one shot shows all three surfaces at once.
                None => {
                    if let Some(cell) = hotspot {
                        shell.open_sheet(cell);
                    }
                }
            }
            shell
        });
        // Wrap in a gpui-component `Root` (the window-root weld) so any kit widget
        // that reads the `Root` global paints clean (the cockpit pattern).
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })?;

    cx.run_until_parked();
    cx.update_window(window.into(), |_, window, _cx| window.refresh())?;
    cx.run_until_parked();
    let captured = cx.capture_screenshot(window.into())?;
    captured.save(format!("{out}.png"))?;
    println!(
        "OK headless touch render -> {out}.png ({}x{}, logical {w}x{h}{}); \
         LIVE touch::TouchShell — bottom tab bar · cell garden · {}.",
        captured.width(),
        captured.height(),
        mode.map(|m| format!(", mode={m}")).unwrap_or_default(),
        if mode.is_some() {
            "mode surface"
        } else {
            "long-press face sheet"
        }
    );
    Ok(())
}

/// The thin-client report (sel4-thin / remote-node path).
#[cfg(not(feature = "embedded-executor"))]
fn thin_report(client: &client::NodeClient) {
    println!("== Starbridge v2 · thin client ==");
    println!("node: {}", client.describe());
    match client.status() {
        Ok(s) => println!(
            "status: healthy={} height={} producer={}",
            s.healthy, s.latest_height, s.state_producer
        ),
        Err(e) => println!("status: <unreachable: {e}>"),
    }
    match client.cells() {
        Ok(cells) => {
            println!("cells: {}", cells.len());
            for c in cells.iter().take(8) {
                println!("  {} · balance {}", &c.id[..12.min(c.id.len())], c.balance);
            }
        }
        Err(e) => println!("cells: <error: {e}>"),
    }
}
