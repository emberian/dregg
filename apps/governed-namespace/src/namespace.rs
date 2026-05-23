//! Namespace integration: ties together the Router, VFS, and Constitution.
//!
//! The Namespace is the top-level abstraction. It represents a governed,
//! capability-secure file hosting domain where:
//! - Routes determine access control policy
//! - Files are stored content-addressed (nameless)
//! - Route changes require democratic governance
//! - Everything is committed and provable
//!
//! ## DAO Use Case
//!
//! A DAO creates a namespace with routes:
//!   /public/*       → anyone can read/write
//!   /treasury/*     → requires 3-of-5 multisig
//!   /proposals/*    → members only
//!   /grants/*       → (added later via governance vote)
//!
//! Files uploaded to the namespace are classified by the DFA and stored
//! in the appropriate partition. The routing table commitment is the
//! "constitution" — changing it requires a governance vote.

use std::sync::Arc;

use pyana_captp::sturdy::SwissTable;
use pyana_captp::uri::PyanaUri;
use pyana_types::CellId;
use tokio::sync::RwLock;

use crate::governance::{GovernanceEngine, Participant};
use crate::routes::{Classification, RouteClass, RouteEntry, RoutingTable};
use crate::storage::{ContentHash, ContentStore, StorageError, hex};

/// The integrated namespace: routing + storage + governance + capability sharing.
#[derive(Clone)]
pub struct Namespace {
    /// Content-addressed file store.
    pub store: ContentStore,
    /// The live routing table (shared with governance).
    pub routing_table: Arc<RwLock<RoutingTable>>,
    /// Governance engine for route amendments.
    pub governance: GovernanceEngine,
    /// Swiss number table for capability sharing via pyana:// URIs.
    pub swiss_table: Arc<RwLock<SwissTable>>,
    /// Federation ID for constructing URIs.
    pub federation_id: [u8; 32],
}

/// Result of a namespace write (combines routing classification with storage receipt).
#[derive(Clone, Debug, serde::Serialize)]
pub struct NamespaceWriteResult {
    /// The content hash (address) of the stored file.
    pub hash: String,
    /// Size in bytes.
    pub size: usize,
    /// Which route prefix the file was classified under.
    pub route_prefix: String,
    /// The route classification that was applied.
    pub route_class: String,
    /// Whether this was a new write.
    pub new: bool,
}

/// Result of a namespace read.
#[derive(Clone, Debug)]
pub struct NamespaceReadResult {
    /// The file content.
    pub content: Vec<u8>,
    /// The route classification that permitted this read.
    pub route_class: String,
    /// The matched path prefix.
    pub route_prefix: String,
}

/// Errors from namespace operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamespaceError {
    /// No route matched the given path (deny by default).
    NoRoute(String),
    /// The route requires higher authorization than provided.
    Unauthorized { path: String, required: String },
    /// Storage error (not found, nullified, etc.).
    Storage(StorageError),
}

impl std::fmt::Display for NamespaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NamespaceError::NoRoute(path) => {
                write!(f, "no route matched path: {path}")
            }
            NamespaceError::Unauthorized { path, required } => {
                write!(f, "unauthorized: path {path} requires {required}")
            }
            NamespaceError::Storage(e) => write!(f, "storage error: {e}"),
        }
    }
}

/// Authorization level of the current requester.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AuthLevel {
    /// No authentication (anonymous).
    Anonymous,
    /// Authenticated member.
    Member,
    /// Administrator.
    Admin,
    /// Multisig holder (with their signature count).
    Multisig(u32),
}

impl Namespace {
    /// Create a new namespace with the given participants and default DAO routes.
    pub fn new(participants: Vec<Participant>, federation_id: [u8; 32]) -> Self {
        let routing_table = Arc::new(RwLock::new(RoutingTable::default_dao()));
        let governance = GovernanceEngine::new(participants, routing_table.clone());
        Self {
            store: ContentStore::new(),
            routing_table,
            governance,
            swiss_table: Arc::new(RwLock::new(SwissTable::new())),
            federation_id,
        }
    }

    /// Create a namespace with a custom routing table.
    pub fn with_routes(
        participants: Vec<Participant>,
        federation_id: [u8; 32],
        routes: Vec<RouteEntry>,
    ) -> Self {
        let mut table = RoutingTable::new();
        for entry in routes {
            table.add_route(entry);
        }
        let routing_table = Arc::new(RwLock::new(table));
        let governance = GovernanceEngine::new(participants, routing_table.clone());
        Self {
            store: ContentStore::new(),
            routing_table,
            governance,
            swiss_table: Arc::new(RwLock::new(SwissTable::new())),
            federation_id,
        }
    }

    /// Classify a path and check authorization.
    ///
    /// Returns the classification if the caller is authorized, otherwise an error.
    pub async fn authorize(
        &self,
        path: &str,
        auth: &AuthLevel,
    ) -> Result<Classification, NamespaceError> {
        let table = self.routing_table.read().await;
        let classification = table.classify(path);
        drop(table);

        let route = classification
            .route
            .as_ref()
            .ok_or_else(|| NamespaceError::NoRoute(path.to_string()))?;

        // Check auth level against route class.
        let authorized = match &route.class {
            RouteClass::Public => true, // Anyone
            RouteClass::MembersOnly => matches!(auth, AuthLevel::Member | AuthLevel::Admin),
            RouteClass::AdminOnly => matches!(auth, AuthLevel::Admin),
            RouteClass::Multisig { threshold } => match auth {
                AuthLevel::Admin => true,
                AuthLevel::Multisig(sigs) => sigs >= threshold,
                _ => false,
            },
            RouteClass::Custom(_) => {
                // Custom policies are admin-only by default.
                matches!(auth, AuthLevel::Admin)
            }
        };

        if !authorized {
            return Err(NamespaceError::Unauthorized {
                path: path.to_string(),
                required: route.class.label().to_string(),
            });
        }

        Ok(classification)
    }

    /// Write a file through the namespace (DFA-routed).
    ///
    /// The path determines which route prefix this file belongs to.
    /// Authorization is checked before writing.
    pub async fn write(
        &self,
        path: &str,
        content: Vec<u8>,
        content_type: Option<String>,
        auth: &AuthLevel,
    ) -> Result<NamespaceWriteResult, NamespaceError> {
        let classification = self.authorize(path, auth).await?;
        let route = classification.route.as_ref().unwrap();
        let prefix = classification.matched_prefix.as_deref().unwrap_or("/");

        let receipt = self
            .store
            .write(content, content_type, Some(prefix.to_string()))
            .await
            .map_err(NamespaceError::Storage)?;

        Ok(NamespaceWriteResult {
            hash: receipt.hash,
            size: receipt.size,
            route_prefix: prefix.to_string(),
            route_class: route.class.label().to_string(),
            new: receipt.new,
        })
    }

    /// Read a file through the namespace (DFA-routed).
    ///
    /// The path determines authorization; the hash determines content.
    pub async fn read(
        &self,
        path: &str,
        hash: &ContentHash,
        auth: &AuthLevel,
    ) -> Result<NamespaceReadResult, NamespaceError> {
        let classification = self.authorize(path, auth).await?;
        let route = classification.route.as_ref().unwrap();
        let prefix = classification.matched_prefix.as_deref().unwrap_or("/");

        let (content, _entry) = self
            .store
            .read(hash)
            .await
            .map_err(NamespaceError::Storage)?;

        Ok(NamespaceReadResult {
            content,
            route_class: route.class.label().to_string(),
            route_prefix: prefix.to_string(),
        })
    }

    /// Export a file as a shareable pyana:// URI (sturdy reference).
    ///
    /// Creates a swiss number entry that allows the URI holder to read the file.
    /// The URI encodes federation_id + cell_id (derived from hash) + swiss number.
    pub async fn share_file(&self, hash: &ContentHash) -> Result<String, NamespaceError> {
        // Verify the file exists.
        if !self.store.exists(hash).await {
            return Err(NamespaceError::Storage(StorageError::NotFound));
        }

        // Create a CellId from the content hash (the file IS the cell).
        let cell_id = CellId(*hash);

        // Export via swiss table.
        let mut swiss_table = self.swiss_table.write().await;
        let swiss = swiss_table.export(
            cell_id,
            pyana_cell::AuthRequired::None, // Bearer token = the URI itself
            0,                              // height (not used in demo)
            None,                           // no expiry
        );

        // Construct the URI.
        let uri = PyanaUri {
            federation_id: self.federation_id,
            cell_id: *hash,
            swiss,
        };

        Ok(uri.to_uri_string())
    }

    /// Get the current route table commitment hash.
    pub async fn route_commitment(&self) -> String {
        let table = self.routing_table.read().await;
        hex::encode(table.commitment())
    }

    /// Get namespace statistics.
    pub async fn stats(&self) -> NamespaceStats {
        let table = self.routing_table.read().await;
        NamespaceStats {
            file_count: self.store.file_count().await,
            nullifier_count: self.store.nullifier_count().await,
            route_count: table.len(),
            route_version: table.version,
            route_commitment: hex::encode(table.commitment()),
        }
    }
}

/// Summary statistics for the namespace.
#[derive(Clone, Debug, serde::Serialize)]
pub struct NamespaceStats {
    pub file_count: usize,
    pub nullifier_count: usize,
    pub route_count: usize,
    pub route_version: u64,
    pub route_commitment: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_participants() -> Vec<Participant> {
        vec![
            Participant {
                id: "alice".into(),
                name: None,
                weight: 1,
            },
            Participant {
                id: "bob".into(),
                name: None,
                weight: 1,
            },
            Participant {
                id: "carol".into(),
                name: None,
                weight: 1,
            },
        ]
    }

    #[tokio::test]
    async fn public_write_and_read() {
        let ns = Namespace::new(test_participants(), [0xaa; 32]);

        // Anonymous can write to /public/
        let result = ns
            .write(
                "/public/readme.txt",
                b"Hello DAO".to_vec(),
                Some("text/plain".to_string()),
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();

        assert_eq!(result.route_prefix, "/public/");
        assert_eq!(result.route_class, "public");
        assert!(result.new);

        // Anonymous can read back
        let hash = hex::decode(&result.hash).unwrap();
        let read_result = ns
            .read("/public/readme.txt", &hash, &AuthLevel::Anonymous)
            .await
            .unwrap();
        assert_eq!(read_result.content, b"Hello DAO");
    }

    #[tokio::test]
    async fn members_only_denies_anonymous() {
        let ns = Namespace::new(test_participants(), [0xbb; 32]);

        let err = ns
            .write(
                "/members/secret.txt",
                b"secret".to_vec(),
                None,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap_err();

        assert!(matches!(err, NamespaceError::Unauthorized { .. }));
    }

    #[tokio::test]
    async fn members_can_access_members_route() {
        let ns = Namespace::new(test_participants(), [0xcc; 32]);

        let result = ns
            .write(
                "/members/doc.pdf",
                b"member content".to_vec(),
                None,
                &AuthLevel::Member,
            )
            .await
            .unwrap();

        assert_eq!(result.route_class, "members_only");
    }

    #[tokio::test]
    async fn no_route_denies() {
        let ns = Namespace::new(test_participants(), [0xdd; 32]);

        let err = ns
            .write(
                "/unknown/file.txt",
                b"data".to_vec(),
                None,
                &AuthLevel::Admin,
            )
            .await
            .unwrap_err();

        assert!(matches!(err, NamespaceError::NoRoute(_)));
    }

    #[tokio::test]
    async fn share_file_produces_uri() {
        let ns = Namespace::new(test_participants(), [0xee; 32]);

        let result = ns
            .write(
                "/public/share-me.txt",
                b"shareable content".to_vec(),
                None,
                &AuthLevel::Anonymous,
            )
            .await
            .unwrap();

        let hash = hex::decode(&result.hash).unwrap();
        let uri = ns.share_file(&hash).await.unwrap();
        assert!(uri.starts_with("pyana://"));
    }

    #[tokio::test]
    async fn multisig_route_requires_threshold() {
        let ns = Namespace::new(test_participants(), [0xff; 32]);

        // 2 sigs not enough (threshold is 3)
        let err = ns
            .write(
                "/treasury/budget.csv",
                b"money".to_vec(),
                None,
                &AuthLevel::Multisig(2),
            )
            .await
            .unwrap_err();
        assert!(matches!(err, NamespaceError::Unauthorized { .. }));

        // 3 sigs is enough
        let result = ns
            .write(
                "/treasury/budget.csv",
                b"money".to_vec(),
                None,
                &AuthLevel::Multisig(3),
            )
            .await
            .unwrap();
        assert_eq!(result.route_class, "multisig");
    }
}
