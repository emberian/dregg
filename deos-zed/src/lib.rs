//! # deos-zed — a real code editor as a deos surface
//!
//! deos-zed is the editor half of the self-hosting deos dev loop: it edits real
//! files inside deos, with the firmament seam ready so file I/O can later route
//! through capability-checked, receipted dregg turns instead of `std::fs`.
//!
//! ## The three pieces
//!
//! * [`fs`] — the [`Fs`](fs::Fs) seam. The ONE place deos-zed touches a
//!   filesystem. [`RealFs`](fs::RealFs) (std::fs) ships today; [`FirmamentFs`](fs::FirmamentFs)
//!   (file = cell, save = receipted turn) is the documented next-step impl. The
//!   editor depends only on the trait, so the firmament swap is one impl.
//! * [`editor`] — the [`Editor`](editor::Editor) surface: a rope-backed,
//!   syntax-highlighting code editor (gpui-component's `InputState`) whose
//!   open/save go through the seam, tracking open path + dirty state.
//! * [`file_tree`] — the [`FileTree`](file_tree::FileTree) affordance: browse a
//!   directory (via the seam) and click a file to open it into the editor.
//! * [`receipt_rail`] — the LEDGER face: the open file's verifiable save
//!   timeline as a rail of chained receipt chips (hash, height, pre→post
//!   morph, computrons), read off the REAL cell the file binds to, with a
//!   `verify chain` action embedding the rail in the spine's global log.
//!
//! ## The editor buffer IS a document-language document
//!
//! The editor's buffer is the materialized fold of a [`dregg_doc::RopeDoc`] — a
//! Pijul-shaped patch [`History`](dregg_doc::History). Opening a file starts a
//! document; each save accrues a verifiable [`Patch`](dregg_doc::Patch) (not an
//! overwrite of bytes), so the durable form is the provenance-bearing patch
//! history. [`doc_viewer`] is the inspecting face: it renders a document's BLAME /
//! timeline and its CONFLICT OBJECTS (two pens at one tail shown as both
//! alternatives + authorship, never a `<<<<<<<` text wound). See
//! [`Editor::document`](editor::Editor::document), [`Editor::blame`](editor::Editor::blame),
//! and [`DocViewer`](doc_viewer::DocViewer).
//!
//! ## Mounting in deos
//!
//! [`cockpit_surface`] holds the adapter that lets the editor live as a tab in
//! starbridge-v2's dock. See [`cockpit_surface::EditorSurface`] and the
//! ready-to-drop `starbridge-v2/src/dock/editor_surface.rs`.
//!
//! ## Approach
//!
//! This crate leans on **gpui-component's code editor** (option (a) in the
//! Zed-in-deos investigation): a rope-backed `Input` in `code_editor` mode with
//! tree-sitter highlighting (33 grammars available; rust/json/toml/markdown on
//! by default). That is the lightest capable path — Zed's full `editor` crate is
//! huge and coupled to project/lsp/multibuffer; gpui-component gives
//! open/edit/save/highlight + a file tree + a dock out of the box, on the SAME
//! gpui fork the cockpit pins, so one gpui resolves across the whole graph.

// The `Fs` seam is gpui-free — it is the ONLY surface that compiles to
// `wasm32-unknown-unknown` (the in-browser editor's executor-backed file backend;
// see `fs::firmament::FirmamentFs` under `--features firmament`). The editor /
// file-tree / doc-viewer below ride gpui and so are gated on `gui` (on by default;
// off for the wasm-shaped core build).
pub mod fs;

// The receipt rail: the module itself is always compiled — its MODEL half
// ([`ReceiptFact`](receipt_rail::ReceiptFact), [`verify_rail`](receipt_rail::verify_rail))
// is gpui-free (the `Fs` seam speaks it), while the [`ReceiptRail`](receipt_rail::ReceiptRail)
// VIEW inside is `gui`-gated like the other panes.
pub mod receipt_rail;

#[cfg(feature = "gui")]
pub mod doc_viewer;
#[cfg(feature = "gui")]
pub mod editor;
#[cfg(feature = "gui")]
pub mod file_tree;

#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;

#[cfg(feature = "screenshot")]
pub mod screenshot;

#[cfg(feature = "gui")]
pub use doc_viewer::DocViewer;
#[cfg(feature = "gui")]
pub use editor::Editor;
#[cfg(feature = "gui")]
pub use file_tree::FileTree;
pub use fs::{DirEntry, FirmamentFs, Fs, Metadata, RealFs};
#[cfg(feature = "gui")]
pub use receipt_rail::ReceiptRail;
pub use receipt_rail::{RailVerdict, ReceiptFact};
