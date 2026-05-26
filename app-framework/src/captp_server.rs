//! CapTP server wrapper around [`SwissTable`].
//!
//! `CapTpServer` wraps a `SwissTable` to register cells as sturdy references and build
//! shareable `DreggUri` values. It is stored as an axum [`Extension`] so handlers can
//! extract it and export capabilities to incoming connections.
//!
//! # Triage (post-Lane B wire changes — 2026-05-24)
//!
//! Verified still useful and correct. The `SwissTable` API surface
//! used here (`SwissTable::export -> [u8; 32]`, `SwissTable::make_uri
//! -> Option<DreggUri>`) matches `captp/src/sturdy.rs` as of Lane B
//! (`captp/src/sturdy.rs:85, 143`). Lane B's wire changes
//! restructured `wire/src/{captp_server, hardening}.rs` (the QUIC
//! transport layer); the app-side `CapTpServer` wrapper here is the
//! *application-facing* sturdy-ref minting + revocation surface and
//! is independent of the wire-transport rewrite.
//!
//! Verdict: **(a) still useful for app-side CapTP serving**.
//! Apps that mount this carry a `CapTpServer` Extension on their
//! Router so HTTP handlers can call `server.export(cell, perms, ...)`
//! and return the resulting `DreggUri` to the requesting client. No
//! changes needed for the current wire surface; if a future wire
//! change forces `SwissTable::export` to return a `Result` (rather
//! than infallibly returning a swiss number), the change is local —
//! propagate the `Result` in `CapTpServer::export`'s signature.
//!
//! # Signature note (disagreement with brief)
//!
//! The brief stated that `SwissTable::export` returns a `DreggUri` directly. Reality:
//! `SwissTable::export` returns `[u8; 32]` (the raw swiss number). The `DreggUri` is
//! constructed separately via `SwissTable::make_uri`. `CapTpServer::export` wraps both
//! calls so callers receive the `DreggUri` as the brief expected.
//!
//! `SwissTable::export` actual signature:
//! ```text
//! pub fn export(
//!     &mut self,
//!     cell_id: CellId,
//!     permissions: AuthRequired,
//!     current_height: u64,
//!     expires_at: Option<u64>,
//! ) -> [u8; 32]
//! ```
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::captp_server::CapTpServer;
//! use dregg_captp::FederationId;
//!
//! let server = CapTpServer::new(FederationId([0xAB; 32]));
//! let uri = server.export(my_cell, AuthRequired::Signature, 100, None).await;
//! ```

use std::sync::Arc;

use tokio::sync::Mutex;

use dregg_captp::{DreggUri, FederationId, SwissTable};
use dregg_cell::{AuthRequired, CellId};

/// CapTP server: wraps a `SwissTable` to export cells as sturdy refs.
///
/// Cheap to clone — internally `Arc`-backed.
#[derive(Clone)]
pub struct CapTpServer {
    swiss: Arc<Mutex<SwissTable>>,
    federation_id: FederationId,
}

impl CapTpServer {
    /// Create a new server with an empty `SwissTable` and the given federation identity.
    pub fn new(federation_id: FederationId) -> Self {
        Self {
            swiss: Arc::new(Mutex::new(SwissTable::new())),
            federation_id,
        }
    }

    /// Create from an existing `SwissTable` (e.g., loaded from persisted state).
    pub fn with_swiss_table(swiss: SwissTable, federation_id: FederationId) -> Self {
        Self {
            swiss: Arc::new(Mutex::new(swiss)),
            federation_id,
        }
    }

    /// Export a cell as a sturdy reference.
    ///
    /// Internally calls `SwissTable::export` (returns swiss number `[u8; 32]`),
    /// then `SwissTable::make_uri` to build the full `DreggUri`.
    ///
    /// # Arguments
    ///
    /// * `cell` — the cell to export.
    /// * `permissions` — the authorization level the bearer obtains on enliven.
    /// * `current_height` — current federation block height (recorded in the entry).
    /// * `expires_at` — optional block height at which the ref expires.
    ///
    /// Returns `None` if the swiss number was not found immediately after insertion
    /// (should never happen in practice — indicates a logic error in `SwissTable`).
    pub async fn export(
        &self,
        cell: CellId,
        permissions: AuthRequired,
        current_height: u64,
        expires_at: Option<u64>,
    ) -> Option<DreggUri> {
        let mut swiss = self.swiss.lock().await;
        let swiss_num = swiss.export(cell, permissions, current_height, expires_at);
        swiss.make_uri(self.federation_id.0, &swiss_num)
    }

    /// Revoke a sturdy reference by its swiss number.
    ///
    /// Returns `true` if the entry existed and was removed.
    pub async fn revoke(&self, swiss: [u8; 32]) -> bool {
        self.swiss.lock().await.revoke(&swiss)
    }

    /// Access the underlying `SwissTable` Arc (for admin inspection or persistence).
    pub fn swiss_table(&self) -> Arc<Mutex<SwissTable>> {
        self.swiss.clone()
    }

    /// The federation ID this server is associated with.
    pub fn federation_id(&self) -> FederationId {
        self.federation_id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[tokio::test]
    async fn export_produces_valid_uri() {
        let fed = FederationId([0xBB; 32]);
        let server = CapTpServer::new(fed);
        let cell = test_cell(0xAA);

        let uri = server
            .export(cell, AuthRequired::Signature, 100, None)
            .await
            .expect("export should always return a URI");

        assert_eq!(uri.federation_id, fed.0);
        assert_eq!(uri.cell_id, cell.0);

        // URI string should be parseable.
        let uri_str = uri.to_uri_string();
        assert!(
            uri_str.starts_with("dregg://"),
            "URI starts with dregg://: {uri_str}"
        );
        let parsed = DreggUri::parse(&uri_str).unwrap();
        assert_eq!(parsed.federation_id, fed.0);
        assert_eq!(parsed.cell_id, cell.0);
    }

    #[tokio::test]
    async fn revoke_removes_entry() {
        let server = CapTpServer::new(FederationId([0x01; 32]));
        let cell = test_cell(0x02);

        let uri = server
            .export(cell, AuthRequired::None, 0, None)
            .await
            .unwrap();

        // The swiss number is encoded in the URI.
        let swiss_num = uri.swiss;
        let removed = server.revoke(swiss_num).await;
        assert!(removed);

        // Second revoke returns false (not present).
        let removed2 = server.revoke(swiss_num).await;
        assert!(!removed2);
    }
}
