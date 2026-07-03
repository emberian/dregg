//! **The NT/Pharo chrome kit** — the reusable widget infrastructure of the deos
//! desktop, factored out so every surface (windows, menus, dialogs, the property
//! sheet) draws from ONE palette and ONE set of bevel/face primitives.
//!
//! This is the "reusable components" layer: the NT 3D-bevel look, the property-row
//! and section helpers, and the small render/format utilities are all here, so a
//! new window-type or dialog composes them rather than re-deriving the chrome.

use gpui::{
    div, point, px, BoxShadow, Div, FontWeight, Hsla, IntoElement, ParentElement, Pixels,
    ScrollHandle, Stateful, StatefulInteractiveElement, Styled,
};

use gpui_component::scroll::{Scrollbar, ScrollbarShow};

use dregg_types::CellId;

use super::layout::WinKindTag;

// ── The NT palette ──────────────────────────────────────────────────────────────
// Deliberately sterile / technical: a 3D-beveled gray chrome over a teal void, the
// way an NT workstation reads. Dense, not calm; detailed, not minimal.
pub const NT_DESKTOP_BG: u32 = 0x0a3a4a; // the classic teal void
pub const NT_FACE: u32 = 0xc0c0c0; // button-face gray
pub const NT_FACE_DARK: u32 = 0x9a9a9a;
pub const NT_HILIGHT: u32 = 0xffffff; // top-left bevel
pub const NT_SHADOW: u32 = 0x404040; // bottom-right bevel
pub const NT_TEXT: u32 = 0x101010;
pub const NT_TITLE_ACTIVE: u32 = 0x000080; // navy active title bar
pub const NT_TITLE_TEXT: u32 = 0xffffff;
pub const NT_ICON_LABEL: u32 = 0xf0f0f0;
pub const NT_SELECT: u32 = 0x000080;
pub const NT_MENU_HILIGHT: u32 = 0x000080;
pub const NT_DIM: u32 = 0x707070; // a disabled / unheld affordance
                                  // One coherent content-area face for every window body / explorer / dialog (the
                                  // near-white "client area" the chrome frames). Unifying it is what makes the
                                  // inspector, the explorers, and the dialogs read as ONE desktop rather than a
                                  // patchwork of slightly-different off-whites.
pub const NT_PANEL: u32 = 0xf0f0f0; // the client-area background
pub const NT_RULE: u32 = 0x808080; // a hairline rule / groove
pub const NT_LABEL: u32 = 0x505050; // a property-row key label
pub const NT_OK: u32 = 0x0a7a2a; // a held / live / conserved accent (green)
pub const NT_WARN: u32 = 0xa06000; // a well / drifted / sealed accent (amber)
pub const NT_TITLE_INACTIVE: u32 = 0x9a9a9a; // an unfocused window's title bar
pub const NT_TITLE_INACTIVE_TEXT: u32 = 0x303030;

// ── Geometry constants ────────────────────────────────────────────────────────────
pub const ICON_W: f32 = 92.0;
pub const ICON_H: f32 = 76.0;
pub const WIN_MIN_W: f32 = 280.0;
pub const WIN_MIN_H: f32 = 180.0;
pub const MENUBAR_H: f32 = 26.0;

/// The state slot a document-editor edit bumps via a real `SetField` turn — so
/// each edit advances the cell's chronicle (height + receipt) in the same breath
/// it commits the patch. Picked high (slot 14) to stay clear of the demo cells'
/// balance/model slots.
pub const DOC_REV_SLOT: usize = 14;

// ── Document prose in the committed cell heap ───────────────────────────────────────
// A document's prose is stored as field elements in the cell's `fields_map` (the
// unbounded `BTreeMap<u64, FieldElement>` committed via `fields_root`), addressed by
// **ext keys >= STATE_SLOTS(16)** so a `SetField` turn writes them through
// `set_field_ext` (`cell/src/state.rs`) — the prose is on-ledger, receipted, and
// replays from the committed state, not a sidecar.
//
// Namespace (per cell — one document per cell): a base far above the 16 fixed slots
// and far below the reserved refusal-audit ext key (`2^32`). `DOC_TEXT_BASE + 0`
// holds the byte LENGTH (LE u64 in the low 8 bytes); `DOC_TEXT_BASE + 1 + i` holds
// chunk `i` (up to [`DOC_CHUNK_BYTES`] raw UTF-8 bytes, stored verbatim — the
// `fields_map` keeps the 32 bytes byte-exact and `fields_root` binds all 32 via
// `fold_bytes32`).
pub const DOC_TEXT_BASE: u64 = 1_000_000;
/// Bytes of prose packed into one `FieldElement` (the full 32-byte value is stored
/// verbatim and committed, so all 32 carry payload).
pub const DOC_CHUNK_BYTES: usize = 32;
/// A sane ceiling on document chunks written/scanned per edit (keeps a malformed or
/// runaway document from unbounded heap writes; ~32 KiB of prose).
pub const DOC_MAX_CHUNKS: u64 = 1024;

// ── Id rendering ──────────────────────────────────────────────────────────────────

/// The full hex id of a cell (a stable layout/persistence key, and the inspector's
/// identity row). [`CellId`] carries the raw bytes; this is the canonical render.
pub fn id_hex(cell: &CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// A short legible id (first 4 bytes) — the icon caption / window-title id.
pub fn id_short(cell: &CellId) -> String {
    cell.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `Pixels` → `f32` (the field is private; the `From` impl is the supported route).
pub fn pxf(p: Pixels) -> f32 {
    f32::from(p)
}

/// A 3-letter window-kind tag — the dense, fixed-width kind glyph the taskbar stub
/// wears, and the Spotter row-badge's chip (one shared vocabulary for "what kind of
/// surface is this", wherever a surface is named in two dozen pixels). Lives in the
/// chrome kit so gpui-free presentation halves (the Spotter's row builder) can badge
/// without reaching into the desktop View.
pub fn kind_short(tag: WinKindTag) -> &'static str {
    match tag {
        WinKindTag::Inspector => "INS",
        WinKindTag::DocEditor => "DOC",
        WinKindTag::Links => "LNK",
        WinKindTag::Transcript => "LOG",
        WinKindTag::Workflow => "WFL",
        WinKindTag::AndroidCell => "AND",
        WinKindTag::DocExplorer => "DGX",
        WinKindTag::WorldExplorer => "WLD",
        WinKindTag::AgentRoom => "AGT",
        WinKindTag::AppShelf => "APP",
        WinKindTag::ExchangeFloor => "EXC",
        WinKindTag::ViewNodePane => "IR",
        WinKindTag::MatrixRoom => "MTX",
        WinKindTag::ProvenanceWalker => "PRV",
        WinKindTag::AttachWizard => "ATW",
        WinKindTag::MailRoom => "MBX",
        WinKindTag::DreggComputers => "VAT",
    }
}

// ── The bevel/face primitives (reusable NT widgets) ───────────────────────────────
//
// A faithful Windows-NT bevel is TWO-TONE: a light highlight on the top+left edges
// and a dark shadow on the bottom+right, so the face reads as physically RAISED off
// (or pressed INTO) the desktop. gpui carries a single `border_color`, so the two
// tones are painted as a pair of crisp (blur-0) inset box-shadows instead — one
// helper, applied everywhere, gives the whole desktop one coherent 3D material.

fn hsla_of(c: u32) -> Hsla {
    gpui::rgb(c).into()
}

/// A pair of crisp inset shadows forming a `w`-pixel two-tone bevel: `tl` on the
/// top-left, `br` on the bottom-right. The shared engine behind every raised/sunken
/// face.
fn bevel<E: Styled>(d: E, tl: u32, br: u32, w: f32) -> E {
    d.shadow(vec![
        BoxShadow {
            color: hsla_of(tl),
            offset: point(px(w), px(w)),
            blur_radius: px(0.0),
            spread_radius: px(0.0),
            inset: true,
        },
        BoxShadow {
            color: hsla_of(br),
            offset: point(px(-w), px(-w)),
            blur_radius: px(0.0),
            spread_radius: px(0.0),
            inset: true,
        },
    ])
}

/// The warm GLOW color for a cell's kind — the quiet "this thing is alive" hue a
/// held/live cell-icon casts on the teal void (treasury gold · well cyan · service
/// violet · account green). A small, friendly palette so a desktop of cells reads as
/// a room of glowing things, not a grid of gray boxes — the 1999-AOL delight end of
/// the same NT image.
pub fn kind_glow(kind: &str) -> u32 {
    match kind {
        "treasury" => 0xffcf4d,    // warm gold
        "issuer well" => 0x4dd0ff, // spring-cyan
        "service" => 0xb98cff,     // violet
        _ => 0x6fe08f,             // account green
    }
}

/// A RAISED bevel that also casts a soft colored OUTER halo — a cell-icon reading as
/// quietly *alive* (the glowing-room warmth) without losing its NT 3D face. The two
/// inset bevel tones plus one blurred outer glow, painted in one shadow list (gpui
/// carries a single shadow vec, so the glow rides alongside the bevel rather than
/// overwriting it).
pub fn bevel_raised_glow<E: Styled>(d: E, glow: u32) -> E {
    let halo: Hsla = gpui::rgba((glow << 8) | 0xB0).into();
    d.bg(gpui::rgb(NT_FACE)).shadow(vec![
        // The outer glow — soft, blurred, spread a touch beyond the tile.
        BoxShadow {
            color: halo,
            offset: point(px(0.0), px(0.0)),
            blur_radius: px(11.0),
            spread_radius: px(1.5),
            inset: false,
        },
        // The raised two-tone bevel face (lit top-left, shadowed bottom-right).
        BoxShadow {
            color: hsla_of(NT_HILIGHT),
            offset: point(px(2.0), px(2.0)),
            blur_radius: px(0.0),
            spread_radius: px(0.0),
            inset: true,
        },
        BoxShadow {
            color: hsla_of(NT_SHADOW),
            offset: point(px(-2.0), px(-2.0)),
            blur_radius: px(0.0),
            spread_radius: px(0.0),
            inset: true,
        },
    ])
}

/// An NT 3D bevel (RAISED) — a light face lit top-left, shadowed bottom-right (the
/// raised-button look). Generic over any [`Styled`] element so it composes onto a
/// plain `div()` or an `.id()`'d `Stateful<Div>`.
pub fn bevel_raised<E: Styled>(d: E) -> E {
    bevel(d.bg(gpui::rgb(NT_FACE)), NT_HILIGHT, NT_SHADOW, 2.0)
}

/// A SUNKEN bevel — shadowed top-left, lit bottom-right (a pressed button, a text
/// well, a list track). The inverse of [`bevel_raised`].
pub fn bevel_sunken<E: Styled>(d: E) -> E {
    bevel(d, NT_SHADOW, NT_HILIGHT, 2.0)
}

/// The WINDOW / panel frame — a raised two-tone bevel inside a thin dark outer line,
/// the way an NT window lifts off the teal void. Use for the big surfaces (windows,
/// the World widget, popups, dialogs) so they all frame the same way.
pub fn bevel_window<E: Styled>(d: E) -> E {
    bevel(
        d.bg(gpui::rgb(NT_FACE))
            .border_1()
            .border_color(gpui::rgb(0x000000)),
        NT_HILIGHT,
        NT_SHADOW,
        2.0,
    )
}

// ── The NT scroll face (a REAL scrollbar on every dense surface) ──────────────────
//
// Every dense face used to scroll blind — a naked `.overflow_y_scroll()` with no
// thumb, no position, no affordance that MORE exists below the fold. These two
// helpers wire the widget kit's real `Scrollbar` element to a desktop-owned
// [`gpui::ScrollHandle`] (see [`super::face_scroll`]), so density reads as DEPTH
// instead of truncation, and the scroll position persists like window geometry.
//
// The sibling arrangement replicates the kit's own proven `Scrollable::render`
// (gpui-component `scroll/scrollable.rs`): a relative wrapper holding the
// tracked scroll area plus the `Scrollbar` element (which lays itself out
// absolute over the wrapper and paints the thumb on the right edge). We do NOT
// use the kit's one-shot `.overflow_y_scrollbar()` wrapper: it lifts only the
// element's size refinement onto its outer div, so a face's `.flex_1()` would
// land on the inner content and break the window's column layout.

/// Wrap a window-body FACE (a `.id()`'d column, already carrying its bg/padding/
/// children — but NOT `.flex_1()/.min_h()/.overflow_y_scroll()`, which move to
/// this wrapper) into a scroll area with a real, always-visible NT scrollbar
/// tracked by `handle`. The returned wrapper takes the face's old place as the
/// window column's flexing body.
pub fn nt_scroll_face(handle: &ScrollHandle, face: Stateful<Div>) -> Div {
    div()
        .flex_1()
        .min_h(px(0.0))
        .relative()
        .child(face.size_full().overflow_y_scroll().track_scroll(handle))
        .child(nt_scrollbar(handle))
}

/// The kit scrollbar in NT dress: vertical, and ALWAYS visible — chunky,
/// permanent, honest (the NT idiom; no fade-on-idle ghosting). Mount it as the
/// last child of a relative/absolute wrapper whose inner face is tracked by the
/// same `handle` — [`nt_scroll_face`] does exactly that for the standard window
/// body; overlay faces with their own geometry (the Spotter panel, the receipt
/// console) compose it directly.
pub fn nt_scrollbar(handle: &ScrollHandle) -> Scrollbar {
    Scrollbar::vertical(handle).scrollbar_show(ScrollbarShow::Always)
}

/// Dress the widget kit's GLOBAL scrollbar theme in NT: always-visible bars
/// (`gpui_component::init` syncs `scrollbar_show` off the OS auto-hide setting —
/// exactly the ghosting NT never did), with the thumb in button-face gray riding
/// a darker track. Called once from `DeosDesktop::new`, so every mount of the
/// desktop — the live window AND the headless bakes — wears the same dress.
///
/// Scoped deliberately to the SCROLLBAR tokens (plus the token-table refresh
/// they ride): the kit-wide NT skin (radius 0, the full `ThemeColor` sheet) is
/// the theme site's concern, and this function composes under it — a fuller
/// skin landing later simply overwrites the same three fields. The per-element
/// [`nt_scrollbar`] still pins `ScrollbarShow::Always` locally, so desktop
/// scrollbars stay permanent even if another surface later swaps the global.
pub fn apply_nt_scrollbar_dress(cx: &mut gpui::App) {
    let theme = gpui_component::Theme::global_mut(cx);
    theme.scrollbar_show = ScrollbarShow::Always;
    theme.colors.scrollbar = hsla_of(NT_FACE_DARK);
    theme.colors.scrollbar_thumb = hsla_of(NT_FACE);
    theme.colors.scrollbar_thumb_hover = hsla_of(NT_HILIGHT);
    // The kit's paint path reads the derived token table for the thumb colors
    // (`cx.theme().tokens.scrollbar_thumb*`) — regenerate it so the dress lands.
    theme.tokens = gpui_component::ThemeTokens::from(&theme.colors);
}

/// A bold navy section heading inside a window/dialog body — the field-group divider,
/// drawn as a small-caps-feel label over a full-width groove rule so a dense body
/// reads as cleanly separated sections rather than a wall of rows.
pub fn face_section(title: &str) -> impl IntoElement {
    div()
        .mt_1()
        .mb_px()
        .flex()
        .flex_row()
        .items_center()
        .gap_2()
        .child(
            div()
                .flex_none()
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(NT_TITLE_ACTIVE))
                .child(title.to_string()),
        )
        .child(
            // The groove rule: a 1px shadow line over a 1px highlight line (the NT
            // engraved separator) filling the rest of the row.
            div()
                .flex_1()
                .h(px(2.0))
                .border_t_1()
                .border_color(gpui::rgb(NT_RULE)),
        )
}

/// A `key: value` property row (the dense inspector/property line).
pub fn face_row(key: &str, value: &str) -> impl IntoElement {
    div()
        .flex()
        .flex_row()
        .text_size(px(11.0))
        .child(
            div()
                .w(px(96.0))
                .text_color(gpui::rgb(NT_LABEL))
                .child(format!("{key}:")),
        )
        .child(div().flex_1().child(value.to_string()))
}

/// A `key: value` property row with a colour-keyed value — for a status/verdict line
/// (e.g. a "Live" lifecycle in green, a held/unheld marker). Same dense geometry as
/// [`face_row`] but the value carries an accent colour.
pub fn face_row_color(key: &str, value: &str, color: u32) -> impl IntoElement {
    div()
        .flex()
        .flex_row()
        .text_size(px(11.0))
        .child(
            div()
                .w(px(96.0))
                .text_color(gpui::rgb(NT_LABEL))
                .child(format!("{key}:")),
        )
        .child(
            div()
                .flex_1()
                .text_color(gpui::rgb(color))
                .child(value.to_string()),
        )
}

/// A thin horizontal bar visualising a fraction `0.0..=1.0` (a balance / fill gauge).
/// NT-dense: a sunken track with a navy fill. Read-only — pure presentation over an
/// already-computed ratio.
pub fn face_gauge(ratio: f32) -> impl IntoElement {
    let r = ratio.clamp(0.0, 1.0);
    div()
        .h(px(8.0))
        .my_1()
        .bg(gpui::rgb(NT_FACE_DARK))
        .border_1()
        .border_color(gpui::rgb(NT_SHADOW))
        .child(
            div()
                .h(px(6.0))
                .w(gpui::relative(r))
                .bg(gpui::rgb(NT_TITLE_ACTIVE)),
        )
}

// ── Glyphs (kept inside the bake font's coverage) ─────────────────────────────────
// The headless bake renders with Lilex + IBM Plex Sans; a handful of decorative
// code points (fullwidth +/=, some dingbats) fall back to tofu (▯) there. These
// constants centralize the SAFE glyphs every surface draws so a bake reads clean.
/// The window-control glyphs (minimize / restore / maximize / close) — kept to
/// code points the bake font carries (the geometric square glyphs are tofu in-bake,
/// so maximize/restore use a bracketed-box ASCII that reads as a window).
pub const GLYPH_MIN: &str = "–";
pub const GLYPH_RESTORE: &str = "[o]";
pub const GLYPH_MAX: &str = "[]";
pub const GLYPH_CLOSE: &str = "×";
/// The resize-grip glyph (a corner of slashes the font carries).
pub const GLYPH_GRIP: &str = "//";
/// The "add" / "remove" affordance markers (ASCII — fullwidth +/− are tofu in-bake).
pub const GLYPH_ADD: &str = "+";
pub const GLYPH_REMOVE: &str = "-";
/// A small right-pointing marker (the baseline/pin marker) the font carries.
pub const GLYPH_PIN: &str = ">";

// ── Numeric formatting (NT-dense numerics) ────────────────────────────────────────

/// Format a signed balance with a unicode minus and thousands grouping.
pub fn fmt_balance(b: i64) -> String {
    if b < 0 {
        format!("−{}", group(-b as u64))
    } else {
        group(b as u64)
    }
}

/// Group an integer with thousands separators.
pub fn group(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    let bytes = s.as_bytes();
    let len = bytes.len();
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}
