//! Name resolution client: petnames, edge names, and hierarchical resolution.
//!
//! Implements the SDK-side naming protocol from the nameservice design:
//! - **PetnameDb**: local storage of petnames, edge names, and proposed name cache
//! - **Resolution algorithm**: strict priority petname > edge > proposed > hierarchical
//! - **Hierarchical resolution**: dotted names split right-to-left, traverse directories via CapTP
//! - **Serialization**: PetnameDb persisted with cipherclerk state (JSON)
//!
//! # Security Properties
//!
//! - Petnames are local-only and cannot be overridden remotely.
//! - Edge names are self-asserted by contacts; lower confidence (0.8).
//! - Proposed names come from governed directories; confidence depends on freshness/votes.
//! - Resolution provenance is always tracked so the UI can display trust indicators.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use pyana_captp::uri::PyanaUri;
use pyana_cell::CellId;

use crate::captp_client::CapTpClient;

// =============================================================================
// Name Entry Types
// =============================================================================

/// A petname: YOUR name for something. Completely local, never shared.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PetnameEntry {
    /// The human-readable label you assigned.
    pub label: String,
    /// The sturdy ref this name points to.
    pub target: PyanaUri,
    /// Epoch when you assigned this petname.
    pub assigned_at: u64,
    /// Optional notes (e.g., "alice from the hackathon").
    pub notes: Option<String>,
}

/// An edge name: what a CONTACT calls themselves. Populated from their profile cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EdgeNameEntry {
    /// The label the contact claims.
    pub label: String,
    /// The sturdy ref this name points to.
    pub target: PyanaUri,
    /// The contact who claims this name (their URI).
    pub source: PyanaUri,
    /// Epoch when this was last fetched from the contact's profile.
    pub last_refreshed: u64,
}

/// A proposed name: what the COMMUNITY calls something. Governance-voted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProposedNameEntry {
    /// The community-assigned label.
    pub label: String,
    /// The sturdy ref this name points to.
    pub target: PyanaUri,
    /// Which federation directory this came from.
    pub directory: PyanaUri,
    /// Governance vote weight at registration time.
    pub vote_weight: u64,
    /// Expiry epoch (from directory entry's expires_at).
    pub expires_at: Option<u64>,
}

// =============================================================================
// Resolution Result Types
// =============================================================================

/// Resolution result with provenance tracking.
#[derive(Clone, Debug)]
pub struct ResolvedName {
    /// The sturdy ref this name resolved to.
    pub target: PyanaUri,
    /// How this resolution was achieved.
    pub provenance: NameProvenance,
    /// Confidence: 1.0 for petnames, 0.8 for edge, varies for proposed.
    pub confidence: f64,
}

/// How a name was resolved — provenance tracking for trust indicators.
#[derive(Clone, Debug, PartialEq)]
pub enum NameProvenance {
    /// Resolved from local petname DB.
    LocalPetname,
    /// Resolved from a contact's self-claimed edge name.
    EdgeName { source: PyanaUri },
    /// Resolved from a governed federation directory.
    FederationDirectory {
        directory: PyanaUri,
        vote_weight: u64,
    },
    /// Resolved from a cross-federation meta-directory lookup.
    CrossFederation {
        home_federation: PyanaUri,
        target_federation: PyanaUri,
    },
    /// No resolution needed — raw URI passed through.
    Direct,
}

// =============================================================================
// Name Errors
// =============================================================================

/// Errors from name operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameError {
    /// Name not found in any resolution source.
    NotFound(String),
    /// Name segment validation failed.
    InvalidSegment(String),
    /// The name is already registered by someone else.
    AlreadyRegistered { name: String, owner: [u8; 32] },
    /// Insufficient computrons to pay rent.
    InsufficientFunds { required: u64, available: u64 },
    /// The name is currently disputed and frozen.
    Disputed { name: String, dispute_id: [u8; 32] },
    /// Not authorized (don't own parent name for sub-delegation, etc.)
    Unauthorized(String),
    /// Cannot traverse — intermediate segment is not a directory.
    NotADirectory { segment: String },
    /// Unknown TLD (not ".pyana").
    UnknownTld(String),
    /// Malformed hierarchical name.
    MalformedHierarchy,
    /// Empty segment in hierarchical name.
    EmptySegment,
    /// Segment exceeds maximum length.
    SegmentTooLong(usize),
    /// Network error during remote resolution.
    NetworkError(String),
    /// Federation directory is unreachable.
    DirectoryUnreachable(PyanaUri),
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(name) => write!(f, "name not found: {name}"),
            Self::InvalidSegment(msg) => write!(f, "invalid name segment: {msg}"),
            Self::AlreadyRegistered { name, .. } => write!(f, "name already registered: {name}"),
            Self::InsufficientFunds {
                required,
                available,
            } => {
                write!(f, "insufficient funds: need {required}, have {available}")
            }
            Self::Disputed { name, .. } => write!(f, "name is disputed: {name}"),
            Self::Unauthorized(msg) => write!(f, "unauthorized: {msg}"),
            Self::NotADirectory { segment } => {
                write!(f, "intermediate segment is not a directory: {segment}")
            }
            Self::UnknownTld(tld) => write!(f, "unknown TLD: {tld}"),
            Self::MalformedHierarchy => write!(f, "malformed hierarchical name"),
            Self::EmptySegment => write!(f, "empty segment in name"),
            Self::SegmentTooLong(len) => write!(f, "segment too long: {len} chars"),
            Self::NetworkError(msg) => write!(f, "network error: {msg}"),
            Self::DirectoryUnreachable(uri) => {
                write!(f, "directory unreachable: {:?}", uri)
            }
        }
    }
}

impl std::error::Error for NameError {}

// =============================================================================
// Validation
// =============================================================================

/// Maximum length of a single name segment (DNS-compatible).
const MAX_SEGMENT_LEN: usize = 63;
/// Maximum total length of a fully-qualified name (DNS-compatible).
const MAX_TOTAL_LEN: usize = 253;
/// Valid characters for name segments.
const VALID_CHARS: &str = "abcdefghijklmnopqrstuvwxyz0123456789-_";

/// Validate a name segment according to the naming rules.
pub fn validate_name_segment(segment: &str) -> Result<(), NameError> {
    if segment.is_empty() {
        return Err(NameError::EmptySegment);
    }
    if segment.len() > MAX_SEGMENT_LEN {
        return Err(NameError::SegmentTooLong(segment.len()));
    }
    if segment.starts_with('-') || segment.ends_with('-') {
        return Err(NameError::InvalidSegment(
            "cannot start/end with hyphen".into(),
        ));
    }
    if !segment.chars().all(|c| VALID_CHARS.contains(c)) {
        return Err(NameError::InvalidSegment(
            "contains invalid characters".into(),
        ));
    }
    Ok(())
}

// =============================================================================
// PetnameDb
// =============================================================================

/// Local petname database: stores petnames, edge names, and proposed name cache.
///
/// This is the cipherclerk-local naming state. It never leaves the device (except
/// via explicit export). Resolution checks this DB first before any network calls.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PetnameDb {
    /// Local petnames (YOUR names for things). Highest priority.
    petnames: HashMap<String, PetnameEntry>,
    /// Edge names (what contacts call themselves). Medium priority.
    edge_names: HashMap<String, EdgeNameEntry>,
    /// Proposed name cache (community names from directories). Lowest priority.
    proposed_cache: HashMap<String, ProposedNameEntry>,
}

impl PetnameDb {
    /// Create a new empty PetnameDb.
    pub fn new() -> Self {
        Self::default()
    }

    // =========================================================================
    // Petname operations
    // =========================================================================

    /// Set a local petname. Overwrites any existing petname with the same label.
    pub fn set_petname(&mut self, label: &str, target: PyanaUri, assigned_at: u64) {
        self.petnames.insert(
            label.to_string(),
            PetnameEntry {
                label: label.to_string(),
                target,
                assigned_at,
                notes: None,
            },
        );
    }

    /// Set a local petname with notes.
    pub fn set_petname_with_notes(
        &mut self,
        label: &str,
        target: PyanaUri,
        assigned_at: u64,
        notes: &str,
    ) {
        self.petnames.insert(
            label.to_string(),
            PetnameEntry {
                label: label.to_string(),
                target,
                assigned_at,
                notes: Some(notes.to_string()),
            },
        );
    }

    /// Remove a local petname. Returns the removed entry if it existed.
    pub fn remove_petname(&mut self, label: &str) -> Option<PetnameEntry> {
        self.petnames.remove(label)
    }

    /// Look up a petname by label.
    pub fn get_petname(&self, label: &str) -> Option<&PetnameEntry> {
        self.petnames.get(label)
    }

    /// List all local petnames.
    pub fn list_petnames(&self) -> Vec<&PetnameEntry> {
        self.petnames.values().collect()
    }

    // =========================================================================
    // Edge name operations
    // =========================================================================

    /// Insert or update an edge name (from a contact's profile).
    pub fn set_edge_name(&mut self, entry: EdgeNameEntry) {
        self.edge_names.insert(entry.label.clone(), entry);
    }

    /// Look up an edge name by label.
    pub fn get_edge_name(&self, label: &str) -> Option<&EdgeNameEntry> {
        self.edge_names.get(label)
    }

    /// Remove an edge name.
    pub fn remove_edge_name(&mut self, label: &str) -> Option<EdgeNameEntry> {
        self.edge_names.remove(label)
    }

    /// List all edge names.
    pub fn list_edge_names(&self) -> Vec<&EdgeNameEntry> {
        self.edge_names.values().collect()
    }

    // =========================================================================
    // Proposed name operations
    // =========================================================================

    /// Insert or update a proposed name in the cache.
    pub fn set_proposed(&mut self, entry: ProposedNameEntry) {
        self.proposed_cache.insert(entry.label.clone(), entry);
    }

    /// Look up a proposed name by label.
    pub fn get_proposed(&self, label: &str) -> Option<&ProposedNameEntry> {
        self.proposed_cache.get(label)
    }

    /// Remove a proposed name from the cache.
    pub fn remove_proposed(&mut self, label: &str) -> Option<ProposedNameEntry> {
        self.proposed_cache.remove(label)
    }

    /// Remove expired proposed names from the cache.
    pub fn gc_expired_proposed(&mut self, current_epoch: u64) {
        self.proposed_cache
            .retain(|_, entry| match entry.expires_at {
                Some(exp) => current_epoch < exp,
                None => true, // No expiry = keep forever
            });
    }

    // =========================================================================
    // Reverse lookup
    // =========================================================================

    /// Reverse lookup: find all petnames pointing to a given cell_id.
    pub fn reverse_lookup_petnames(&self, cell_id: &[u8; 32]) -> Vec<&PetnameEntry> {
        self.petnames
            .values()
            .filter(|entry| &entry.target.cell_id == cell_id)
            .collect()
    }

    /// Reverse lookup: find all edge names pointing to a given cell_id.
    pub fn reverse_lookup_edge_names(&self, cell_id: &[u8; 32]) -> Vec<&EdgeNameEntry> {
        self.edge_names
            .values()
            .filter(|entry| &entry.target.cell_id == cell_id)
            .collect()
    }

    // =========================================================================
    // Serialization
    // =========================================================================

    /// Serialize the PetnameDb to JSON for persistence.
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("PetnameDb serialization should not fail")
    }

    /// Deserialize a PetnameDb from JSON.
    pub fn from_json(s: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(s)
    }
}

// =============================================================================
// Name Resolver
// =============================================================================

/// The name resolver: resolves human-readable names to sturdy refs.
///
/// Holds a reference to the PetnameDb and can perform network resolution
/// via a CapTP client for hierarchical and federation directory lookups.
pub struct NameResolver<'a> {
    db: &'a PetnameDb,
    /// Current epoch for staleness/expiry calculations.
    current_epoch: u64,
    /// Staleness threshold for edge names (epochs since last refresh).
    /// Edge names older than this get reduced confidence.
    edge_staleness_threshold: u64,
}

impl<'a> NameResolver<'a> {
    /// Create a new NameResolver with the given database and current epoch.
    pub fn new(db: &'a PetnameDb, current_epoch: u64) -> Self {
        Self {
            db,
            current_epoch,
            edge_staleness_threshold: 100, // default: 100 epochs
        }
    }

    /// Set the edge name staleness threshold.
    pub fn with_staleness_threshold(mut self, threshold: u64) -> Self {
        self.edge_staleness_threshold = threshold;
        self
    }

    /// Resolve a name to a sturdy ref.
    ///
    /// Resolution order: petname > edge name > proposed name > hierarchical lookup.
    ///
    /// For simple (non-dotted) names, checks the local DB only (no network).
    /// For dotted names, performs hierarchical resolution via CapTP.
    pub async fn resolve(
        &self,
        name: &str,
        _client: &CapTpClient,
    ) -> Result<ResolvedName, NameError> {
        // Validate total name length.
        if name.len() > MAX_TOTAL_LEN {
            return Err(NameError::InvalidSegment(format!(
                "name too long: {} chars (max {})",
                name.len(),
                MAX_TOTAL_LEN
            )));
        }

        // 1. Check local petnames first (instant, no network).
        if let Some(entry) = self.db.get_petname(name) {
            return Ok(ResolvedName {
                target: entry.target,
                provenance: NameProvenance::LocalPetname,
                confidence: 1.0,
            });
        }

        // 2. Check edge name cache (local, from last contact sync).
        if let Some(edge) = self.db.get_edge_name(name) {
            let age = self.current_epoch.saturating_sub(edge.last_refreshed);
            let confidence = if age > self.edge_staleness_threshold {
                // Stale edge name: reduce confidence proportionally.
                let staleness_factor =
                    1.0 - ((age - self.edge_staleness_threshold) as f64 / 1000.0).min(0.5);
                0.8 * staleness_factor
            } else {
                0.8
            };
            return Ok(ResolvedName {
                target: edge.target,
                provenance: NameProvenance::EdgeName {
                    source: edge.source,
                },
                confidence,
            });
        }

        // 3. Check proposed name cache (local cached community names).
        if let Some(proposed) = self.db.get_proposed(name) {
            // Check expiry.
            if let Some(expires_at) = proposed.expires_at {
                if self.current_epoch >= expires_at {
                    return Err(NameError::NotFound(name.to_string()));
                }
            }
            // Confidence based on vote weight.
            let confidence = (proposed.vote_weight as f64 / 1000.0).min(0.95).max(0.5);
            return Ok(ResolvedName {
                target: proposed.target,
                provenance: NameProvenance::FederationDirectory {
                    directory: proposed.directory,
                    vote_weight: proposed.vote_weight,
                },
                confidence,
            });
        }

        // 4. If name contains dots, try hierarchical resolution.
        if name.contains('.') {
            return self.resolve_hierarchical(name).await;
        }

        // 5. Not found anywhere.
        Err(NameError::NotFound(name.to_string()))
    }

    /// Resolve a hierarchical name like "alice.federation-a.pyana".
    ///
    /// Algorithm:
    /// 1. Split on '.' from RIGHT
    /// 2. Verify TLD is "pyana"
    /// 3. The second segment is the federation name
    /// 4. Remaining segments (left) are the path within that federation's directory
    ///
    /// NOTE: Actual network traversal requires the CapTP client to enliven
    /// the federation directory and query it. This implementation validates
    /// the structure and returns a NetworkError for the actual remote lookup
    /// (which requires integration with a running federation node).
    async fn resolve_hierarchical(&self, name: &str) -> Result<ResolvedName, NameError> {
        let segments: Vec<&str> = name.split('.').collect();

        if segments.len() < 2 {
            return Err(NameError::MalformedHierarchy);
        }

        // Validate each segment.
        for seg in &segments {
            validate_name_segment(seg)?;
        }

        // The last segment must be the TLD "pyana".
        let tld = segments.last().unwrap();
        if *tld != "pyana" {
            return Err(NameError::UnknownTld(tld.to_string()));
        }

        if segments.len() < 3 {
            // Bare "federation-name.pyana" — would resolve to the federation directory itself.
            // This requires network access to the meta-directory.
            return Err(NameError::NetworkError(
                "hierarchical resolution requires network access to meta-directory".to_string(),
            ));
        }

        // segments = ["alice", "federation-a", "pyana"]
        // federation_name = "federation-a"
        // leaf_path = "alice" (or deeper nesting for "service.alice.federation-a.pyana")
        let _federation_name = segments[segments.len() - 2];
        let _leaf_segments = &segments[..segments.len() - 2];

        // Network resolution: in a real deployment, we would:
        // 1. Query the meta-directory for the federation's name directory URI
        // 2. Enliven that URI via CapTP
        // 3. Traverse sub-directories for each leaf segment (right-to-left)
        //
        // For now, return a NetworkError indicating the remote lookup is needed.
        Err(NameError::NetworkError(
            "hierarchical resolution requires active CapTP session to federation directory"
                .to_string(),
        ))
    }

    /// Parse a dotted name into its hierarchical components.
    ///
    /// Returns (leaf_segments, federation_name, tld) if valid.
    /// Example: "alice.my-fed.pyana" -> (["alice"], "my-fed", "pyana")
    pub fn parse_hierarchical(name: &str) -> Result<(Vec<&str>, &str, &str), NameError> {
        let segments: Vec<&str> = name.split('.').collect();

        if segments.len() < 2 {
            return Err(NameError::MalformedHierarchy);
        }

        let tld = segments.last().unwrap();
        if *tld != "pyana" {
            return Err(NameError::UnknownTld(tld.to_string()));
        }

        if segments.len() < 3 {
            return Err(NameError::MalformedHierarchy);
        }

        let federation_name = segments[segments.len() - 2];
        let leaf_segments = &segments[..segments.len() - 2];

        Ok((leaf_segments.to_vec(), federation_name, tld))
    }
}

// =============================================================================
// WhoisResult
// =============================================================================

/// Result from a whois (reverse) lookup.
#[derive(Clone, Debug)]
pub struct WhoisResult {
    /// The name that points to the queried target.
    pub name: String,
    /// Which category this name belongs to.
    pub provenance: NameProvenance,
    /// The directory the name lives in (if not a local petname).
    pub directory: Option<PyanaUri>,
}

// =============================================================================
// Cipherclerk Integration
// =============================================================================

/// Extension trait for AgentCipherclerk to add name resolution capabilities.
///
/// This provides the cipherclerk-level API surface for name operations.
/// The actual PetnameDb is stored in the cipherclerk state and persisted with it.
pub struct CipherclerkNames {
    /// The petname database.
    pub db: PetnameDb,
    /// Current epoch (updated by the cipherclerk on each block).
    pub current_epoch: u64,
}

impl CipherclerkNames {
    /// Create a new CipherclerkNames with an empty database.
    pub fn new() -> Self {
        Self {
            db: PetnameDb::new(),
            current_epoch: 0,
        }
    }

    /// Create from an existing PetnameDb (e.g., loaded from persistence).
    pub fn from_db(db: PetnameDb) -> Self {
        Self {
            db,
            current_epoch: 0,
        }
    }

    /// Update the current epoch.
    pub fn set_epoch(&mut self, epoch: u64) {
        self.current_epoch = epoch;
    }

    /// Assign a local petname to a sturdy ref.
    ///
    /// This is YOUR name for this thing. It never leaves your device.
    /// Overwrites any existing petname with the same label.
    pub fn set_petname(&mut self, label: &str, target: PyanaUri) -> Result<(), NameError> {
        validate_name_segment(label)?;
        self.db.set_petname(label, target, self.current_epoch);
        Ok(())
    }

    /// Remove a local petname.
    pub fn remove_petname(&mut self, label: &str) -> Result<(), NameError> {
        self.db
            .remove_petname(label)
            .ok_or_else(|| NameError::NotFound(label.to_string()))?;
        Ok(())
    }

    /// List all local petnames.
    pub fn list_petnames(&self) -> Vec<&PetnameEntry> {
        self.db.list_petnames()
    }

    /// Resolve a name using the local DB and optionally via CapTP.
    pub async fn resolve_name(
        &self,
        name: &str,
        client: &CapTpClient,
    ) -> Result<ResolvedName, NameError> {
        let resolver = NameResolver::new(&self.db, self.current_epoch);
        resolver.resolve(name, client).await
    }

    /// Register a name in the home federation's directory.
    ///
    /// In a real deployment, this submits a name registration effect to the
    /// federation via CapTP. Returns the URI of the registered name entry.
    pub async fn register_name(
        &mut self,
        name: &str,
        cell_id: CellId,
        _client: &CapTpClient,
    ) -> Result<PyanaUri, NameError> {
        validate_name_segment(name)?;

        // In production, this would:
        // 1. Calculate rent cost
        // 2. Submit Effect::RegisterName to the federation
        // 3. Receive the mount receipt
        //
        // For the SDK client, we create the target URI from the cell_id and
        // the client's federation_id.
        let target_uri = PyanaUri {
            federation_id: _client.federation_id().0,
            cell_id: cell_id.0,
            swiss: [0u8; 32], // placeholder — real swiss comes from the mount
        };

        // Auto-create a local petname for the registered name.
        self.db.set_petname(name, target_uri, self.current_epoch);

        Ok(target_uri)
    }

    /// Reverse lookup: what names point to this cell?
    ///
    /// Checks local petnames and edge names.
    pub async fn whois(
        &self,
        cell_id: CellId,
        _client: &CapTpClient,
    ) -> Result<Vec<WhoisResult>, NameError> {
        let mut results = Vec::new();

        // Check local petnames.
        for entry in self.db.reverse_lookup_petnames(&cell_id.0) {
            results.push(WhoisResult {
                name: entry.label.clone(),
                provenance: NameProvenance::LocalPetname,
                directory: None,
            });
        }

        // Check edge names.
        for entry in self.db.reverse_lookup_edge_names(&cell_id.0) {
            results.push(WhoisResult {
                name: entry.label.clone(),
                provenance: NameProvenance::EdgeName {
                    source: entry.source,
                },
                directory: None,
            });
        }

        // In production, would also query federation directory's reverse index.

        if results.is_empty() {
            return Err(NameError::NotFound(format!("cell {:?}", cell_id.0)));
        }

        Ok(results)
    }
}

impl Default for CipherclerkNames {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::captp_client::{CapTpClient, CapTpConfig};
    use pyana_captp::FederationId;

    fn test_uri(id: u8) -> PyanaUri {
        PyanaUri {
            federation_id: [id; 32],
            cell_id: [id + 1; 32],
            swiss: [id + 2; 32],
        }
    }

    fn test_config() -> CapTpConfig {
        CapTpConfig {
            federation_id: FederationId([0xAA; 32]),
            current_height: 100,
        }
    }

    fn test_client() -> CapTpClient {
        CapTpClient::new(test_config())
    }

    // =========================================================================
    // Test 1: Petname set/get/remove
    // =========================================================================

    #[test]
    fn petname_set_get_remove() {
        let mut db = PetnameDb::new();
        let target = test_uri(1);

        // Set
        db.set_petname("alice", target, 42);
        let entry = db.get_petname("alice").unwrap();
        assert_eq!(entry.label, "alice");
        assert_eq!(entry.target, target);
        assert_eq!(entry.assigned_at, 42);

        // Get non-existent
        assert!(db.get_petname("bob").is_none());

        // Remove
        let removed = db.remove_petname("alice");
        assert!(removed.is_some());
        assert!(db.get_petname("alice").is_none());

        // Remove non-existent
        let removed_again = db.remove_petname("alice");
        assert!(removed_again.is_none());
    }

    // =========================================================================
    // Test 2: Resolution priority (petname > edge > proposed)
    // =========================================================================

    #[tokio::test]
    async fn resolution_priority() {
        let mut db = PetnameDb::new();
        let client = test_client();

        let petname_target = test_uri(1);
        let edge_target = test_uri(2);
        let proposed_target = test_uri(3);

        // Add all three with the same label "alice"
        db.set_petname("alice", petname_target, 100);
        db.set_edge_name(EdgeNameEntry {
            label: "alice".to_string(),
            target: edge_target,
            source: test_uri(10),
            last_refreshed: 100,
        });
        db.set_proposed(ProposedNameEntry {
            label: "alice".to_string(),
            target: proposed_target,
            directory: test_uri(20),
            vote_weight: 500,
            expires_at: None,
        });

        let resolver = NameResolver::new(&db, 100);

        // Should resolve to petname (highest priority)
        let result = resolver.resolve("alice", &client).await.unwrap();
        assert_eq!(result.target, petname_target);
        assert_eq!(result.provenance, NameProvenance::LocalPetname);
        assert_eq!(result.confidence, 1.0);

        // Remove petname, should fall through to edge name
        db.remove_petname("alice");
        let resolver = NameResolver::new(&db, 100);
        let result = resolver.resolve("alice", &client).await.unwrap();
        assert_eq!(result.target, edge_target);
        assert!(matches!(result.provenance, NameProvenance::EdgeName { .. }));
        assert_eq!(result.confidence, 0.8);

        // Remove edge name, should fall through to proposed
        db.remove_edge_name("alice");
        let resolver = NameResolver::new(&db, 100);
        let result = resolver.resolve("alice", &client).await.unwrap();
        assert_eq!(result.target, proposed_target);
        assert!(matches!(
            result.provenance,
            NameProvenance::FederationDirectory { .. }
        ));
    }

    // =========================================================================
    // Test 3: Dotted name splits correctly for hierarchical lookup
    // =========================================================================

    #[test]
    fn dotted_name_parsing() {
        // Simple hierarchical
        let (leaves, fed, tld) = NameResolver::parse_hierarchical("alice.my-fed.pyana").unwrap();
        assert_eq!(leaves, vec!["alice"]);
        assert_eq!(fed, "my-fed");
        assert_eq!(tld, "pyana");

        // Multi-segment leaf
        let (leaves, fed, tld) =
            NameResolver::parse_hierarchical("service.alice.community.pyana").unwrap();
        assert_eq!(leaves, vec!["service", "alice"]);
        assert_eq!(fed, "community");
        assert_eq!(tld, "pyana");

        // Wrong TLD
        let err = NameResolver::parse_hierarchical("alice.my-fed.eth").unwrap_err();
        assert_eq!(err, NameError::UnknownTld("eth".to_string()));

        // Too few segments
        let err = NameResolver::parse_hierarchical("just-tld.pyana").unwrap_err();
        assert_eq!(err, NameError::MalformedHierarchy);
    }

    // =========================================================================
    // Test 4: Edge name refresh (stale = lower confidence)
    // =========================================================================

    #[tokio::test]
    async fn edge_name_staleness() {
        let mut db = PetnameDb::new();
        let client = test_client();
        let target = test_uri(5);

        db.set_edge_name(EdgeNameEntry {
            label: "bob".to_string(),
            target,
            source: test_uri(10),
            last_refreshed: 50, // refreshed at epoch 50
        });

        // At epoch 100, the edge name is 50 epochs old (within threshold of 100).
        let resolver = NameResolver::new(&db, 100);
        let result = resolver.resolve("bob", &client).await.unwrap();
        assert_eq!(result.confidence, 0.8);

        // At epoch 200, the edge name is 150 epochs old (50 epochs past threshold).
        // Staleness factor = 1.0 - (50 / 1000) = 0.95
        // Confidence = 0.8 * 0.95 = 0.76
        let resolver = NameResolver::new(&db, 200);
        let result = resolver.resolve("bob", &client).await.unwrap();
        assert!(result.confidence < 0.8);
        assert!(result.confidence > 0.7);

        // At epoch 1150, the edge name is 1100 epochs old (1000 epochs past threshold).
        // Staleness factor = 1.0 - min(1000/1000, 0.5) = 0.5
        // Confidence = 0.8 * 0.5 = 0.4
        let resolver = NameResolver::new(&db, 1150);
        let result = resolver.resolve("bob", &client).await.unwrap();
        assert_eq!(result.confidence, 0.4);
    }

    // =========================================================================
    // Test 5: Proposed name expiry
    // =========================================================================

    #[tokio::test]
    async fn proposed_name_expiry() {
        let mut db = PetnameDb::new();
        let client = test_client();
        let target = test_uri(7);

        db.set_proposed(ProposedNameEntry {
            label: "service-x".to_string(),
            target,
            directory: test_uri(20),
            vote_weight: 800,
            expires_at: Some(200),
        });

        // Before expiry — resolves fine.
        let resolver = NameResolver::new(&db, 150);
        let result = resolver.resolve("service-x", &client).await.unwrap();
        assert_eq!(result.target, target);

        // At expiry — should NOT resolve.
        let resolver = NameResolver::new(&db, 200);
        let result = resolver.resolve("service-x", &client).await;
        assert!(matches!(result, Err(NameError::NotFound(_))));

        // After expiry — should NOT resolve.
        let resolver = NameResolver::new(&db, 250);
        let result = resolver.resolve("service-x", &client).await;
        assert!(matches!(result, Err(NameError::NotFound(_))));

        // Test gc_expired_proposed
        db.gc_expired_proposed(250);
        assert!(db.get_proposed("service-x").is_none());
    }

    // =========================================================================
    // Test 6: Serialization roundtrip
    // =========================================================================

    #[test]
    fn serialization_roundtrip() {
        let mut db = PetnameDb::new();
        let target1 = test_uri(1);
        let target2 = test_uri(2);
        let target3 = test_uri(3);

        db.set_petname("alice", target1, 100);
        db.set_petname_with_notes("bob", target2, 200, "met at conference");
        db.set_edge_name(EdgeNameEntry {
            label: "carol".to_string(),
            target: target3,
            source: test_uri(10),
            last_refreshed: 150,
        });
        db.set_proposed(ProposedNameEntry {
            label: "service".to_string(),
            target: test_uri(4),
            directory: test_uri(20),
            vote_weight: 500,
            expires_at: Some(1000),
        });

        // Serialize to JSON
        let json = db.to_json();
        assert!(!json.is_empty());

        // Deserialize back
        let restored = PetnameDb::from_json(&json).unwrap();

        // Verify petnames
        let alice = restored.get_petname("alice").unwrap();
        assert_eq!(alice.target, target1);
        assert_eq!(alice.assigned_at, 100);
        assert!(alice.notes.is_none());

        let bob = restored.get_petname("bob").unwrap();
        assert_eq!(bob.target, target2);
        assert_eq!(bob.notes.as_deref(), Some("met at conference"));

        // Verify edge name
        let carol = restored.get_edge_name("carol").unwrap();
        assert_eq!(carol.target, target3);
        assert_eq!(carol.last_refreshed, 150);

        // Verify proposed name
        let service = restored.get_proposed("service").unwrap();
        assert_eq!(service.vote_weight, 500);
        assert_eq!(service.expires_at, Some(1000));
    }

    // =========================================================================
    // Test 7: whois reverse lookup
    // =========================================================================

    #[tokio::test]
    async fn whois_reverse_lookup() {
        let mut cclerk_names = CipherclerkNames::new();
        cclerk_names.set_epoch(100);
        let client = test_client();

        let target = test_uri(5);
        let cell_id = CellId(target.cell_id);

        // Set a petname pointing to this cell.
        cclerk_names.db.set_petname("alice", target, 100);

        // Set an edge name also pointing to this cell.
        cclerk_names.db.set_edge_name(EdgeNameEntry {
            label: "alice-contact".to_string(),
            target,
            source: test_uri(10),
            last_refreshed: 90,
        });

        let results = cclerk_names.whois(cell_id, &client).await.unwrap();
        assert_eq!(results.len(), 2);

        let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
        assert!(names.contains(&"alice"));
        assert!(names.contains(&"alice-contact"));
    }

    // =========================================================================
    // Test 8: Empty DB returns NameError::NotFound
    // =========================================================================

    #[tokio::test]
    async fn empty_db_not_found() {
        let db = PetnameDb::new();
        let client = test_client();
        let resolver = NameResolver::new(&db, 100);

        let result = resolver.resolve("nonexistent", &client).await;
        assert!(matches!(result, Err(NameError::NotFound(ref name)) if name == "nonexistent"));
    }

    // =========================================================================
    // Test 9: Validation rules
    // =========================================================================

    #[test]
    fn name_segment_validation() {
        // Valid segments
        assert!(validate_name_segment("alice").is_ok());
        assert!(validate_name_segment("my-service").is_ok());
        assert!(validate_name_segment("alice_bob").is_ok());
        assert!(validate_name_segment("a123").is_ok());

        // Invalid: empty
        assert_eq!(validate_name_segment(""), Err(NameError::EmptySegment));

        // Invalid: too long
        let long = "a".repeat(64);
        assert!(matches!(
            validate_name_segment(&long),
            Err(NameError::SegmentTooLong(64))
        ));

        // Invalid: starts with hyphen
        assert!(matches!(
            validate_name_segment("-alice"),
            Err(NameError::InvalidSegment(_))
        ));

        // Invalid: ends with hyphen
        assert!(matches!(
            validate_name_segment("alice-"),
            Err(NameError::InvalidSegment(_))
        ));

        // Invalid: uppercase
        assert!(matches!(
            validate_name_segment("Alice"),
            Err(NameError::InvalidSegment(_))
        ));

        // Invalid: spaces
        assert!(matches!(
            validate_name_segment("my name"),
            Err(NameError::InvalidSegment(_))
        ));
    }

    // =========================================================================
    // Test 10: CipherclerkNames set_petname validates
    // =========================================================================

    #[test]
    fn cclerk_names_validates_on_set() {
        let mut wn = CipherclerkNames::new();
        let target = test_uri(1);

        // Valid
        assert!(wn.set_petname("alice", target).is_ok());

        // Invalid (uppercase)
        assert!(wn.set_petname("Alice", target).is_err());

        // Invalid (empty)
        assert!(wn.set_petname("", target).is_err());
    }

    // =========================================================================
    // Test 11: whois on empty DB returns NotFound
    // =========================================================================

    #[tokio::test]
    async fn whois_empty_db() {
        let cclerk_names = CipherclerkNames::new();
        let client = test_client();
        let cell_id = CellId([0xFF; 32]);

        let result = cclerk_names.whois(cell_id, &client).await;
        assert!(matches!(result, Err(NameError::NotFound(_))));
    }
}
