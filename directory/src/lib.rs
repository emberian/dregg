//! `pyana-directory` — Canonical named-capability directory primitive.
//!
//! # Why this crate exists
//!
//! `apps/nameservice/` and `apps/governed-namespace/` both reinvented the
//! same directory shape: a versioned `BTreeMap<Name, Entry>` with CAS
//! semantics, ACL-bound access, expiry, dispute, and (in the latter)
//! governance-mediated table swaps. The audit
//! (`PYANA-FLAWS-FROM-APPS.md` G33) prescribes:
//!
//! > Canonical name-directory primitive (`pyana-directory` crate).
//! > CapTP has `SwissTable` (swiss → live capability); no platform
//! > analog for *named* (human-readable → swiss/sturdy-ref, with rent /
//! > expiry / dispute baked in). A `pyana-directory` crate combining
//! > `SwissTable` + `Authorizer` + `EscrowManager`-backed rent +
//! > Merkle-rooted name index would replace ~80% of the nameservice and
//! > governed-namespace code.
//!
//! Companion: G32 (`Effect::RegisterName`) is a DSL-side concern; this
//! crate composes the *userspace* shape and emits standard
//! `Effect::SetField` + `Effect::EmitEvent` actions (the starbridge-app
//! stance) rather than introducing a new effect variant.
//!
//! # Public surface
//!
//! - [`Directory`] — the core trait. `register`, `lookup`, `revoke`,
//!   `discover` are its four canonical operations.
//! - [`DirectoryEntry`] — versioned binding between a name and a
//!   sturdy-ref-shaped resource handle.
//! - [`InMemoryDirectory`] — the in-process reference implementation,
//!   suitable as the cell-state backing for a `DirectoryCell`.
//! - [`DfaRoutedDirectory`] — composition with `pyana-dfa` for
//!   governance-bound atomic table swaps (the
//!   `apps/governed-namespace/` pattern). A new policy table is staged,
//!   then the entire directory atomically transitions when the
//!   governance vote passes.
//! - [`MetaDirectory`] — directory-of-directories for federation peer
//!   discovery (lifted from `rbg::directory::MetaDirectory`).
//!
//! # What this crate is NOT
//!
//! - It is not a wire protocol. The HTTP handler in
//!   `starbridge-apps/nameservice/` (or any future consumer) is the
//!   wire surface; this crate is the in-memory primitive.
//! - It is not a cell-program. Per `STORAGE-AS-CELL-PROGRAMS.md`, a
//!   directory cell is *composed* of slot-caveat constraints (`WriteOnce`
//!   for name binding, `Monotonic` for expiry) + an in-state map
//!   committed via Merkle root. This crate provides the map; the cell
//!   program lives in `starbridge-apps/nameservice/`.
//! - It does not authenticate callers. Authorization is the caller's
//!   responsibility — pass an `Authorizer` if you want ACL-bound
//!   access. The naked `Directory` trait trusts its caller.

#![forbid(unsafe_code)]

mod dfa_routed;
mod directory;
mod meta;

pub use dfa_routed::{DfaRoutedDirectory, RouteTable, RouteTableId, TableSwapError};
pub use directory::{
    Directory, DirectoryEntry, DirectoryError, EntryKind, InMemoryDirectory, Listing, Version,
};
pub use meta::{MetaDirectory, PeerHandle};

/// A sturdy-ref-shaped resource handle. Decoupled from
/// `captp::uri::PyanaUri` so this crate does not pull in the full CapTP
/// dependency just to typedef a 96-byte triple.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ResourceHandle {
    /// 32-byte federation id.
    pub federation_id: [u8; 32],
    /// 32-byte cell id.
    pub cell_id: [u8; 32],
    /// 32-byte swiss number.
    pub swiss: [u8; 32],
}

impl ResourceHandle {
    pub fn new(federation_id: [u8; 32], cell_id: [u8; 32], swiss: [u8; 32]) -> Self {
        Self {
            federation_id,
            cell_id,
            swiss,
        }
    }

    /// Encode as a CapTP-shaped URI string. Lossy: tools that need the
    /// real `captp::uri::PyanaUri` should parse this back themselves.
    pub fn to_uri(&self) -> String {
        format!(
            "pyana://{}/{}/{}",
            hex_encode(&self.federation_id),
            hex_encode(&self.cell_id),
            hex_encode(&self.swiss),
        )
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
