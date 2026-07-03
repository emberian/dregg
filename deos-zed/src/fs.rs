//! The [`Fs`] seam — the ONE place deos-zed touches a filesystem.
//!
//! The editor, the file tree, and the demo NEVER call `std::fs` directly. All
//! file I/O goes through this trait. That indirection is the whole point of
//! deos-zed: today the editor edits real disk files via [`RealFs`]; tomorrow it
//! edits sovereign cells via a `FirmamentFs` (see [`firmament`]) — and that is a
//! ONE-IMPL swap, with zero changes to the editor or file-tree code.
//!
//! The trait shape mirrors Zed's `fs::Fs` (the subset an editor actually needs):
//! `load`, `save`, `read_dir`, `metadata`. We keep it small and synchronous —
//! the editor already runs file I/O on a background spawn (see
//! [`crate::editor::Editor::open`]) so a blocking `Fs` is fine, and a synchronous
//! trait is dramatically simpler to implement for a `FirmamentFs` whose `save`
//! is a receipted dregg turn.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Result;

use crate::receipt_rail::ReceiptFact;

/// Metadata about a path — the editor-relevant subset of Zed's `fs::Metadata`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Metadata {
    /// `true` if the path is a directory.
    pub is_dir: bool,
    /// `true` if the path is a symbolic link (followed paths report the target).
    pub is_symlink: bool,
    /// Size in bytes (0 for directories / when unknown).
    pub len: u64,
}

/// One entry in a directory listing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirEntry {
    /// The full path of the entry.
    pub path: PathBuf,
    /// `true` if this entry is itself a directory.
    pub is_dir: bool,
}

impl DirEntry {
    /// The final path component as a display string (e.g. `main.rs`).
    pub fn file_name(&self) -> String {
        self.path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("<?>")
            .to_string()
    }
}

/// The filesystem seam. The editor depends ONLY on this trait — never on a
/// concrete impl — so the backing store is a deployment choice, not a code
/// change. `RealFs` (std::fs) ships today; `FirmamentFs` (cell = file, save =
/// receipted turn) is the documented next step in [`firmament`].
///
/// Object-safe (`dyn Fs`) and `'static` so the editor can hold an `Arc<dyn Fs>`.
/// It is NOT `Send + Sync`: the editor + file-tree run entirely on gpui's
/// single foreground thread (gpui's `cx.spawn` runs futures on the main thread
/// and requires only `'static`, never `Send`), and the cockpit-shared
/// [`FirmamentFs::over`](firmament::FirmamentFs) variant mounts onto the live
/// `Rc<RefCell<World>>` ledger spine — itself single-threaded — so a save lands
/// on the SAME ledger the cockpit inspector reads. A `Send + Sync` bound here
/// would force a second (`Arc<Mutex<…>>`) ownership model disjoint from the live
/// World; we keep one spine.
pub trait Fs: 'static {
    /// Read a path's full contents as a UTF-8 string. The editor calls this on
    /// open. (Binary files are out of scope for a text editor.)
    fn load(&self, path: &Path) -> Result<String>;

    /// Write `content` to a path, replacing any existing contents. The editor
    /// calls this on save. For `FirmamentFs` this is the receipt-producing turn.
    fn save(&self, path: &Path, content: &str) -> Result<()>;

    /// List the immediate children of a directory (NOT recursive — the file
    /// tree expands lazily). Order is unspecified; the caller sorts.
    fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>>;

    /// Stat a path. Used to decide whether a tree entry is expandable.
    fn metadata(&self, path: &Path) -> Result<Metadata>;

    /// A short human label for which backing store is in use (shown in the
    /// editor's status line so the firmament swap is VISIBLE to the user).
    fn backend_label(&self) -> &'static str;

    /// The number of RECEIPTED saves this backend has recorded, if it has a
    /// notion of one. `RealFs` returns `None` (a disk write leaves no receipt);
    /// `FirmamentFs` returns its real on-ledger receipt count so the editor's
    /// status line can read the GENUINE `N saves · on-ledger` rather than the
    /// gpui-side document patch history. Default `None` keeps every other `Fs`
    /// impl unaffected.
    fn save_count(&self) -> Option<usize> {
        None
    }

    /// The hash of the MOST RECENT save receipt this backend recorded, if it
    /// records receipts at all. `RealFs` has none (default `None`);
    /// `FirmamentFs` returns `TurnReceipt::receipt_hash()` of its last
    /// committed save so the editor's status line can stamp the just-minted
    /// receipt fingerprint (`⛓ a1b2c3d4`) right where the save landed — the
    /// `save_count` precedent, one hash deeper. Plain `[u8; 32]` so the trait
    /// stays free of `dregg_turn` types in the non-firmament build.
    fn last_save_receipt_hash(&self) -> Option<[u8; 32]> {
        None
    }

    /// **The per-file receipt timeline** for `path`, projected to the
    /// always-compiled [`ReceiptFact`] shape — the ordered facts of every
    /// committed save that targeted this file's backing cell. The receipt
    /// rail renders and verifies exactly this. Default: empty — a backend
    /// with no receipts (`RealFs`) has no timeline, and every existing `Fs`
    /// impl is untouched. `FirmamentFs` overrides it with the REAL
    /// `history(path)` receipts off the live spine.
    fn receipt_facts_for(&self, _path: &Path) -> Vec<ReceiptFact> {
        Vec::new()
    }

    /// The backend's GLOBAL receipt log as facts, in commit order — what the
    /// rail's `verify chain` embeds the per-file timeline into (the receipt
    /// chain threads through ALL files, so verification needs the whole log).
    /// Default: empty — the rail's verdict then says "no global log
    /// published" rather than overclaiming. `FirmamentFs` overrides it when
    /// its spine publishes the log.
    fn receipt_facts(&self) -> Vec<ReceiptFact> {
        Vec::new()
    }
}

/// The real, on-disk filesystem via `std::fs`. The default backing store today.
#[derive(Clone, Default)]
pub struct RealFs;

impl RealFs {
    pub fn new() -> Self {
        RealFs
    }

    /// Convenience: a boxed `Arc<dyn Fs>` for handing to the editor.
    pub fn arc() -> Arc<dyn Fs> {
        Arc::new(RealFs)
    }
}

impl Fs for RealFs {
    fn load(&self, path: &Path) -> Result<String> {
        Ok(std::fs::read_to_string(path)?)
    }

    fn save(&self, path: &Path, content: &str) -> Result<()> {
        // Write to a sibling temp file then rename, so a crash mid-write never
        // truncates the user's file. (FirmamentFs gets atomicity for free: the
        // turn either commits or it doesn't.)
        let tmp = path.with_extension(format!(
            "{}.deos-zed-tmp",
            path.extension().and_then(|e| e.to_str()).unwrap_or("")
        ));
        std::fs::write(&tmp, content)?;
        std::fs::rename(&tmp, path)?;
        Ok(())
    }

    fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(path)? {
            let entry = entry?;
            let p = entry.path();
            let is_dir = entry.file_type().map(|t| t.is_dir()).unwrap_or(false);
            out.push(DirEntry { path: p, is_dir });
        }
        Ok(out)
    }

    fn metadata(&self, path: &Path) -> Result<Metadata> {
        let md = std::fs::symlink_metadata(path)?;
        let is_symlink = md.file_type().is_symlink();
        // Resolve through symlinks for is_dir/len so a symlinked dir expands.
        let resolved = std::fs::metadata(path).unwrap_or(md);
        Ok(Metadata {
            is_dir: resolved.is_dir(),
            is_symlink,
            len: resolved.len(),
        })
    }

    fn backend_label(&self) -> &'static str {
        "RealFs (std::fs)"
    }
}

pub mod firmament;
pub use firmament::FirmamentFs;

/// The path → cell namespace, backed by `rbg`'s capability-secure
/// `DirectoryCell` (recursive scoping, membership-scoped listing, `dregg://`
/// sturdy refs, versioned CAS). Only present with `--features firmament`.
#[cfg(feature = "firmament")]
pub mod namespace;

/// The verified-spine seam types — the [`LedgerSpine`](firmament::LedgerSpine)
/// trait a host implements over its live ledger (e.g. the cockpit's `World`) so
/// [`FirmamentFs::over`](firmament::FirmamentFs::over) mounts file-cells onto it,
/// and the self-contained [`OwnedSpine`](firmament::OwnedSpine) the headless
/// path uses. Only present with `--features firmament`.
#[cfg(feature = "firmament")]
pub use firmament::{
    host_content_write_effects, host_decode_content, host_make_editor_cell, host_make_file_cell,
    LedgerSpine, OwnedSpine,
};
