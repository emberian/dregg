//! Scoped Intent Directories: capability-secure discovery zones for pyana.
//!
//! # Problem
//!
//! The intent engine (`intent/` crate) broadcasts intents via gossip to ALL connected
//! peers. The pool is flat and global: every node sees every intent. This doesn't scale
//! and leaks information (everyone sees what capabilities are being requested/offered).
//!
//! # Solution: Directories as Capabilities
//!
//! A directory IS a capability. Holding a reference to a directory grants authority to:
//! - List entries (discover what's available)
//! - Get entries (resolve names to sturdy refs)
//! - Post intents (scoped to this directory's participants)
//!
//! Directories map naturally to constitutions: the federation's membership set defines
//! who can see/participate in that federation's directory. Cross-directory discovery
//! uses meta-directories (yellow pages) that list other directories.
//!
//! # Design Heritage (Robigalia)
//!
//! From Robigalia's VFS:
//! - `Directory::list()` -> versioned listing (maps to: list cells in scope)
//! - `Directory::get(name, version)` -> (cap, version) (maps to: resolve name to SturdyRef)
//! - `Directory::swap(name, version, cap)` -> atomic CAS (maps to: register/update entry)
//! - Every mutation increments version (maps to: cell nonce)
//! - Directories contain directories (recursive scoping)
//!
//! # Composition with Existing Pyana Pieces
//!
//! - **Constitution membership** -> directory ACL (who can list/get/post)
//! - **SturdyRefs** (`pyana://` URIs) -> directory entries point to capabilities
//! - **Gossip topics** -> each directory has its own topic (scoped propagation)
//! - **CapTP GC** -> when all refs to a directory are dropped, the scope is dead
//! - **Factories** -> create directory cells with constrained properties

use std::collections::{BTreeMap, HashMap, HashSet};

// ---------------------------------------------------------------------------
// Type stubs (standing in for actual pyana crate types in this exploration module)
// ---------------------------------------------------------------------------

/// A 32-byte identifier for a federation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FederationId(pub [u8; 32]);

/// A 32-byte identifier for a cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CellId(pub [u8; 32]);

/// A pyana:// URI (swiss number + federation + cell).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SturdyRef {
    pub federation_id: FederationId,
    pub cell_id: CellId,
    pub swiss: [u8; 32],
}

/// Gossip topic identifier. Each directory defines its own topic for scoped propagation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GossipTopic(pub [u8; 32]);

/// Anonymous commitment ID for intent creators (from intent crate).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CommitmentId(pub [u8; 32]);

/// A member of a federation (identified by their public key hash).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemberId(pub [u8; 32]);

/// Monotonically increasing version number for directory entries.
pub type Version = u64;

/// A name in the directory namespace. Hierarchical names use `/` separators.
pub type Name = String;

// ---------------------------------------------------------------------------
// Directory Entry
// ---------------------------------------------------------------------------

/// Metadata about a directory entry, versioned for CAS semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectoryEntry {
    /// The sturdy reference this name resolves to.
    pub sturdy_ref: SturdyRef,
    /// Current version of this entry (monotonically increasing on mutation).
    pub version: Version,
    /// What kind of capability this entry represents.
    pub kind: EntryKind,
    /// Optional human-readable description (for directory listings).
    pub description: Option<String>,
    /// Tags for filtering during search (e.g., ["storage", "compute", "oracle"]).
    pub tags: Vec<String>,
    /// Federation height at which this entry was registered.
    pub registered_at: u64,
    /// Optional expiry height. After this, the entry is stale and should be GC'd.
    pub expires_at: Option<u64>,
}

/// What kind of capability an entry represents.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryKind {
    /// A service (can be invoked).
    Service,
    /// A sub-directory (recursive scoping).
    SubDirectory,
    /// A data store / oracle (can be read).
    DataSource,
    /// A factory (can create new cells/capabilities).
    Factory,
    /// A raw capability (opaque to the directory).
    Capability,
}

// ---------------------------------------------------------------------------
// Directory Cell
// ---------------------------------------------------------------------------

/// Error type for directory operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DirectoryError {
    /// The entry does not exist.
    NotFound { name: Name },
    /// Version mismatch on CAS operation (stale read).
    VersionConflict { name: Name, expected: Version, actual: Version },
    /// The caller lacks authority (not a member of this directory's scope).
    Unauthorized { member: MemberId },
    /// The directory has reached its capacity limit.
    Full { capacity: usize },
    /// The name is invalid (empty, too long, or contains forbidden characters).
    InvalidName { name: Name, reason: &'static str },
    /// The entry has expired and been GC'd.
    Expired { name: Name },
}

impl std::fmt::Display for DirectoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound { name } => write!(f, "entry not found: {name}"),
            Self::VersionConflict { name, expected, actual } => {
                write!(f, "version conflict on '{name}': expected {expected}, actual {actual}")
            }
            Self::Unauthorized { member } => {
                write!(f, "unauthorized: member {:02x}{:02x}... not in scope", member.0[0], member.0[1])
            }
            Self::Full { capacity } => write!(f, "directory full (capacity {capacity})"),
            Self::InvalidName { name, reason } => write!(f, "invalid name '{name}': {reason}"),
            Self::Expired { name } => write!(f, "entry expired: {name}"),
        }
    }
}

impl std::error::Error for DirectoryError {}

/// Maximum name length in bytes.
const MAX_NAME_LEN: usize = 256;
/// Maximum number of entries in a single directory cell.
const DEFAULT_MAX_ENTRIES: usize = 10_000;
/// Maximum number of tags per entry.
const MAX_TAGS_PER_ENTRY: usize = 16;

/// A capability-secure directory cell.
///
/// The directory cell maintains a versioned map of `Name -> DirectoryEntry`. The cell
/// itself IS a capability: only holders of a reference to this cell can list, get, or
/// mutate entries. The membership set (ACL) is derived from the federation's constitution.
///
/// # Versioning
///
/// Every mutation (swap, remove) increments the directory's global version AND the
/// per-entry version. Readers can detect stale reads by comparing versions.
///
/// # Gossip Topic Binding
///
/// Each directory cell is bound to a specific gossip topic. Intents posted to this
/// directory's scoped pool propagate ONLY on that topic. Nodes subscribe to a topic
/// only when they hold a reference to the corresponding directory.
#[derive(Clone, Debug)]
pub struct DirectoryCell {
    /// The cell ID of this directory (its identity in the blocklace).
    pub cell_id: CellId,
    /// The federation this directory belongs to.
    pub federation_id: FederationId,
    /// Global version counter (incremented on every mutation).
    pub version: Version,
    /// The entries in this directory, indexed by name.
    entries: BTreeMap<Name, DirectoryEntry>,
    /// Membership set: who is authorized to access this directory.
    /// Derived from the federation's constitution.
    members: HashSet<MemberId>,
    /// Maximum number of entries allowed.
    max_entries: usize,
    /// The gossip topic for this directory's scoped intent pool.
    pub gossip_topic: GossipTopic,
    /// Federation block height at creation.
    pub created_at: u64,
}

impl DirectoryCell {
    /// Create a new directory cell with the given membership set.
    ///
    /// The gossip topic is derived deterministically from the cell ID, ensuring that
    /// anyone who holds a reference to this directory subscribes to the same topic.
    pub fn new(
        cell_id: CellId,
        federation_id: FederationId,
        members: HashSet<MemberId>,
        created_at: u64,
    ) -> Self {
        // Derive gossip topic from cell ID (deterministic: same directory = same topic)
        let topic_bytes = blake3::derive_key("pyana-directory-gossip-topic-v1", &cell_id.0);
        Self {
            cell_id,
            federation_id,
            version: 0,
            entries: BTreeMap::new(),
            members,
            max_entries: DEFAULT_MAX_ENTRIES,
            gossip_topic: GossipTopic(topic_bytes),
            created_at,
        }
    }

    /// Create a directory with a custom capacity.
    pub fn with_capacity(
        cell_id: CellId,
        federation_id: FederationId,
        members: HashSet<MemberId>,
        created_at: u64,
        max_entries: usize,
    ) -> Self {
        let mut dir = Self::new(cell_id, federation_id, members, created_at);
        dir.max_entries = max_entries;
        dir
    }

    // -----------------------------------------------------------------------
    // Robigalia Directory trait operations
    // -----------------------------------------------------------------------

    /// List all entries in the directory.
    ///
    /// Returns a versioned listing: the directory's global version and a snapshot of
    /// all current entries. The caller can use the global version to detect if the
    /// directory has changed since their last read.
    ///
    /// Requires membership.
    pub fn list(&self, caller: MemberId) -> Result<Listing, DirectoryError> {
        self.check_membership(&caller)?;
        let entries: Vec<(Name, DirectoryEntry)> = self
            .entries
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        Ok(Listing {
            directory_version: self.version,
            entries,
        })
    }

    /// Get a specific entry by name.
    ///
    /// Returns the entry and its current version. The caller can pass this version
    /// back to `swap()` for CAS semantics.
    ///
    /// Requires membership.
    pub fn get(&self, caller: MemberId, name: &str) -> Result<&DirectoryEntry, DirectoryError> {
        self.check_membership(&caller)?;
        self.entries.get(name).ok_or_else(|| DirectoryError::NotFound {
            name: name.to_string(),
        })
    }

    /// Atomic compare-and-swap: update or insert an entry.
    ///
    /// If `expected_version` is 0, this is an insert (the name must not exist).
    /// If `expected_version` > 0, this is an update (the name must exist at that version).
    /// If `new_entry` is None, this is a remove (the entry is deleted).
    ///
    /// Requires membership.
    pub fn swap(
        &mut self,
        caller: MemberId,
        name: &str,
        expected_version: Version,
        new_entry: Option<DirectoryEntry>,
    ) -> Result<Version, DirectoryError> {
        self.check_membership(&caller)?;
        Self::validate_name(name)?;

        match (self.entries.get(name), expected_version) {
            // Insert: expected_version == 0, entry does not exist
            (None, 0) => {
                if self.entries.len() >= self.max_entries {
                    return Err(DirectoryError::Full { capacity: self.max_entries });
                }
                let entry = new_entry.ok_or_else(|| DirectoryError::NotFound {
                    name: name.to_string(),
                })?;
                self.version += 1;
                let mut entry = entry;
                entry.version = self.version;
                self.entries.insert(name.to_string(), entry);
                Ok(self.version)
            }
            // Entry exists but caller thinks it doesn't
            (Some(existing), 0) => Err(DirectoryError::VersionConflict {
                name: name.to_string(),
                expected: 0,
                actual: existing.version,
            }),
            // Entry doesn't exist but caller thinks it does
            (None, expected) => Err(DirectoryError::VersionConflict {
                name: name.to_string(),
                expected,
                actual: 0,
            }),
            // Update or remove: version must match
            (Some(existing), expected) => {
                if existing.version != expected {
                    return Err(DirectoryError::VersionConflict {
                        name: name.to_string(),
                        expected,
                        actual: existing.version,
                    });
                }
                self.version += 1;
                match new_entry {
                    Some(mut entry) => {
                        entry.version = self.version;
                        self.entries.insert(name.to_string(), entry);
                    }
                    None => {
                        // Remove
                        self.entries.remove(name);
                    }
                }
                Ok(self.version)
            }
        }
    }

    /// Register a sub-directory entry, making this directory hierarchical.
    ///
    /// The sub-directory's sturdy ref is stored as an entry with `EntryKind::SubDirectory`.
    pub fn register_subdirectory(
        &mut self,
        caller: MemberId,
        name: &str,
        sub_dir_ref: SturdyRef,
        description: Option<String>,
        current_height: u64,
    ) -> Result<Version, DirectoryError> {
        let entry = DirectoryEntry {
            sturdy_ref: sub_dir_ref,
            version: 0, // will be set by swap()
            kind: EntryKind::SubDirectory,
            description,
            tags: vec!["directory".to_string()],
            registered_at: current_height,
            expires_at: None,
        };
        self.swap(caller, name, 0, Some(entry))
    }

    // -----------------------------------------------------------------------
    // Membership management
    // -----------------------------------------------------------------------

    /// Add a member to the directory's scope.
    ///
    /// In production this would be driven by constitution changes on the blocklace.
    pub fn add_member(&mut self, member: MemberId) {
        self.members.insert(member);
    }

    /// Remove a member from the directory's scope.
    ///
    /// Their entries remain (owned by the directory, not the member), but they can
    /// no longer list/get/swap.
    pub fn remove_member(&mut self, member: MemberId) {
        self.members.remove(&member);
    }

    /// Check if a member is in scope.
    pub fn is_member(&self, member: &MemberId) -> bool {
        self.members.contains(member)
    }

    /// Get the current membership set size.
    pub fn member_count(&self) -> usize {
        self.members.len()
    }

    // -----------------------------------------------------------------------
    // Search and filtering
    // -----------------------------------------------------------------------

    /// Search entries by tag.
    ///
    /// Returns all entries that have ALL of the specified tags.
    pub fn search_by_tags(&self, caller: MemberId, tags: &[&str]) -> Result<Vec<(&Name, &DirectoryEntry)>, DirectoryError> {
        self.check_membership(&caller)?;
        let results = self
            .entries
            .iter()
            .filter(|(_, entry)| {
                tags.iter().all(|tag| entry.tags.iter().any(|t| t == tag))
            })
            .collect();
        Ok(results)
    }

    /// Search entries by kind.
    pub fn search_by_kind(&self, caller: MemberId, kind: &EntryKind) -> Result<Vec<(&Name, &DirectoryEntry)>, DirectoryError> {
        self.check_membership(&caller)?;
        let results = self
            .entries
            .iter()
            .filter(|(_, entry)| &entry.kind == kind)
            .collect();
        Ok(results)
    }

    // -----------------------------------------------------------------------
    // GC
    // -----------------------------------------------------------------------

    /// Remove expired entries. Returns the count of entries removed.
    pub fn gc_expired(&mut self, current_height: u64) -> usize {
        let before = self.entries.len();
        self.entries.retain(|_, entry| {
            match entry.expires_at {
                Some(exp) => current_height <= exp,
                None => true,
            }
        });
        let removed = before - self.entries.len();
        if removed > 0 {
            self.version += 1;
        }
        removed
    }

    /// Get the number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the directory has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    // -----------------------------------------------------------------------
    // Internal helpers
    // -----------------------------------------------------------------------

    fn check_membership(&self, member: &MemberId) -> Result<(), DirectoryError> {
        if !self.members.contains(member) {
            Err(DirectoryError::Unauthorized { member: *member })
        } else {
            Ok(())
        }
    }

    fn validate_name(name: &str) -> Result<(), DirectoryError> {
        if name.is_empty() {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: "name cannot be empty",
            });
        }
        if name.len() > MAX_NAME_LEN {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: "name exceeds maximum length",
            });
        }
        if name.contains('\0') {
            return Err(DirectoryError::InvalidName {
                name: name.to_string(),
                reason: "name cannot contain null bytes",
            });
        }
        Ok(())
    }
}

/// A versioned listing of directory entries.
#[derive(Clone, Debug)]
pub struct Listing {
    /// The directory's global version at the time of listing.
    pub directory_version: Version,
    /// All entries currently in the directory.
    pub entries: Vec<(Name, DirectoryEntry)>,
}

// ---------------------------------------------------------------------------
// Scoped Intent Pool
// ---------------------------------------------------------------------------

/// An intent scoped to a specific directory.
///
/// Unlike the global intent pool, a scoped intent is only visible to participants
/// who hold a reference to the directory that contains this pool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScopedIntent {
    /// Content-addressed ID (same as intent crate's IntentId).
    pub id: [u8; 32],
    /// The directory this intent is scoped to.
    pub directory_cell_id: CellId,
    /// What kind of intent (need/offer/query).
    pub kind: ScopedIntentKind,
    /// What capability is needed/offered (simplified MatchSpec for this exploration).
    pub match_pattern: MatchPattern,
    /// Anonymous creator commitment.
    pub creator: CommitmentId,
    /// Expiry timestamp (unix seconds).
    pub expiry: u64,
}

/// Intent kinds within a directory scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScopedIntentKind {
    /// "I need a capability matching this pattern" — requesting.
    Need,
    /// "I offer a capability matching this pattern" — advertising.
    Offer,
    /// "I'm looking for a directory entry matching this" — discovery query.
    DirectoryQuery,
}

/// Simplified match pattern for directory-scoped intents.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchPattern {
    /// Tags that the desired entry must have.
    pub required_tags: Vec<String>,
    /// Entry kind filter.
    pub required_kind: Option<EntryKind>,
    /// Name prefix filter.
    pub name_prefix: Option<String>,
    /// Custom predicate (opaque string for extensibility).
    pub custom_predicate: Option<String>,
}

/// The scoped intent pool: intents visible only within a directory scope.
///
/// Each `ScopedIntentPool` is bound to exactly one `DirectoryCell`. Intents posted here
/// propagate only over the directory's gossip topic, ensuring only members see them.
///
/// # Provable Scoping
///
/// Because the directory's membership set is known (derived from the constitution), we
/// can PROVE "this intent was only visible to N participants": the membership proof
/// at the relevant block height bounds the audience.
pub struct ScopedIntentPool {
    /// The directory cell this pool is bound to.
    directory_cell_id: CellId,
    /// The gossip topic for scoped propagation.
    gossip_topic: GossipTopic,
    /// Active intents in this scope.
    intents: HashMap<[u8; 32], ScopedIntent>,
    /// Members who are currently subscribed (subset of directory members who are online).
    subscribed_members: HashSet<MemberId>,
    /// Maximum intents in this scoped pool (smaller than global pool — it's per-scope).
    max_intents: usize,
}

/// Error type for scoped pool operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScopedPoolError {
    /// The intent has expired.
    Expired,
    /// Duplicate intent.
    Duplicate,
    /// The pool is full.
    Full,
    /// The caller is not a member of this directory scope.
    NotInScope { member: MemberId },
}

impl std::fmt::Display for ScopedPoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expired => write!(f, "scoped intent has expired"),
            Self::Duplicate => write!(f, "duplicate intent in scope"),
            Self::Full => write!(f, "scoped intent pool is full"),
            Self::NotInScope { member } => {
                write!(f, "member {:02x}{:02x}... not in directory scope", member.0[0], member.0[1])
            }
        }
    }
}

impl std::error::Error for ScopedPoolError {}

impl ScopedIntentPool {
    /// Create a new scoped intent pool bound to a directory.
    pub fn new(directory: &DirectoryCell, max_intents: usize) -> Self {
        Self {
            directory_cell_id: directory.cell_id,
            gossip_topic: directory.gossip_topic.clone(),
            intents: HashMap::new(),
            subscribed_members: HashSet::new(),
            max_intents,
        }
    }

    /// Subscribe a member to this scoped pool (they start receiving intents).
    ///
    /// Only directory members can subscribe. Returns the gossip topic they should
    /// join to receive scoped intent propagation.
    pub fn subscribe(&mut self, member: MemberId, directory: &DirectoryCell) -> Result<&GossipTopic, ScopedPoolError> {
        if !directory.is_member(&member) {
            return Err(ScopedPoolError::NotInScope { member });
        }
        self.subscribed_members.insert(member);
        Ok(&self.gossip_topic)
    }

    /// Unsubscribe a member from this scoped pool.
    pub fn unsubscribe(&mut self, member: MemberId) {
        self.subscribed_members.remove(&member);
    }

    /// Post an intent to this scoped pool.
    ///
    /// The intent will propagate only over the directory's gossip topic.
    pub fn post_intent(
        &mut self,
        intent: ScopedIntent,
        now: u64,
        directory: &DirectoryCell,
    ) -> Result<(), ScopedPoolError> {
        if now >= intent.expiry {
            return Err(ScopedPoolError::Expired);
        }
        if self.intents.contains_key(&intent.id) {
            return Err(ScopedPoolError::Duplicate);
        }
        if self.intents.len() >= self.max_intents {
            return Err(ScopedPoolError::Full);
        }
        // Verify the creator is in scope (they must hold a reference to this directory)
        // In production, this would check their subscription status or membership.
        // For now, we verify against the directory's membership set by checking if any
        // subscribed member posted it (creator commitment is anonymous, so we trust
        // that the gossip layer only propagates from subscribed peers).
        let _ = directory; // membership check happens at gossip layer
        self.intents.insert(intent.id, intent);
        Ok(())
    }

    /// Match intents against offered capabilities within this scope.
    ///
    /// Returns (intent_id, entry_name) pairs where a directory entry satisfies a Need intent.
    pub fn match_against_directory(&self, directory: &DirectoryCell, caller: MemberId) -> Result<Vec<([u8; 32], Name)>, DirectoryError> {
        let listing = directory.list(caller)?;
        let mut matches = Vec::new();

        for (id, intent) in &self.intents {
            if intent.kind != ScopedIntentKind::Need {
                continue;
            }
            for (name, entry) in &listing.entries {
                if self.pattern_matches(&intent.match_pattern, name, entry) {
                    matches.push((*id, name.clone()));
                    break; // first match per intent
                }
            }
        }

        Ok(matches)
    }

    /// Garbage collect expired intents.
    pub fn gc(&mut self, now: u64) -> usize {
        let before = self.intents.len();
        self.intents.retain(|_, intent| now < intent.expiry);
        before - self.intents.len()
    }

    /// Remove an intent (e.g., after fulfillment).
    pub fn remove_intent(&mut self, id: &[u8; 32]) -> Option<ScopedIntent> {
        self.intents.remove(id)
    }

    /// Get the gossip topic for this pool.
    pub fn topic(&self) -> &GossipTopic {
        &self.gossip_topic
    }

    /// Get the number of active intents.
    pub fn len(&self) -> usize {
        self.intents.len()
    }

    /// Returns true if the pool has no intents.
    pub fn is_empty(&self) -> bool {
        self.intents.is_empty()
    }

    /// Number of currently subscribed members.
    pub fn subscriber_count(&self) -> usize {
        self.subscribed_members.len()
    }

    /// Internal pattern matching (simplified — production would use DFA compilation).
    fn pattern_matches(&self, pattern: &MatchPattern, name: &str, entry: &DirectoryEntry) -> bool {
        // Check kind filter
        if let Some(ref required_kind) = pattern.required_kind {
            if &entry.kind != required_kind {
                return false;
            }
        }
        // Check tag filter (all required tags must be present)
        if !pattern.required_tags.iter().all(|tag| entry.tags.contains(tag)) {
            return false;
        }
        // Check name prefix
        if let Some(ref prefix) = pattern.name_prefix {
            if !name.starts_with(prefix.as_str()) {
                return false;
            }
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Meta-Directory (Yellow Pages)
// ---------------------------------------------------------------------------

/// A meta-directory: a directory whose entries point to other directories.
///
/// This enables recursive discovery: find the right directory for your domain,
/// then search within it. The meta-directory itself is a capability — you must
/// hold a reference to it to discover what scoped directories exist.
///
/// # Example hierarchy:
///
/// ```text
/// Meta-Directory (root)
///   ├── "compute/"     -> Compute Services Directory (federation A)
///   ├── "storage/"     -> Storage Providers Directory (federation B)
///   ├── "oracles/"     -> Oracle Services Directory (federation C)
///   └── "bridges/"     -> Cross-chain Bridges Directory (federated)
///        ├── "evm/"     -> EVM Bridge Directory
///        └── "cardano/" -> Cardano Bridge Directory
/// ```
///
/// Each leaf directory has its own scoped intent pool. Discovering "I need a
/// storage provider" means: get the meta-directory reference, list to find the
/// "storage/" entry, enliven that sturdy ref to get the storage directory,
/// then post a scoped intent within that directory.
pub struct MetaDirectory {
    /// The underlying directory cell (meta-directories ARE directories).
    directory: DirectoryCell,
    /// Cached sub-directory topology for fast traversal.
    /// Maps path segments to their cell IDs for hierarchical resolution.
    topology_cache: HashMap<String, CellId>,
}

impl MetaDirectory {
    /// Create a new meta-directory.
    pub fn new(
        cell_id: CellId,
        federation_id: FederationId,
        members: HashSet<MemberId>,
        created_at: u64,
    ) -> Self {
        Self {
            directory: DirectoryCell::new(cell_id, federation_id, members, created_at),
            topology_cache: HashMap::new(),
        }
    }

    /// Register a sub-directory in the meta-directory.
    ///
    /// The `path` is hierarchical: "compute/gpu" creates an entry at that path.
    /// The `directory_ref` is the sturdy ref to the sub-directory's cell.
    pub fn register_directory(
        &mut self,
        caller: MemberId,
        path: &str,
        directory_ref: SturdyRef,
        description: Option<String>,
        current_height: u64,
    ) -> Result<Version, DirectoryError> {
        // Cache the topology
        self.topology_cache.insert(path.to_string(), directory_ref.cell_id);

        self.directory.register_subdirectory(
            caller,
            path,
            directory_ref,
            description,
            current_height,
        )
    }

    /// Resolve a hierarchical path to a directory reference.
    ///
    /// Given "compute/gpu", looks up the "compute/gpu" entry and returns its sturdy ref.
    /// For multi-level resolution (each segment is a separate directory), use `resolve_path`.
    pub fn lookup(&self, caller: MemberId, path: &str) -> Result<&DirectoryEntry, DirectoryError> {
        self.directory.get(caller, path)
    }

    /// List all registered directories (top-level listing).
    pub fn list_directories(&self, caller: MemberId) -> Result<Listing, DirectoryError> {
        self.directory.list(caller)
    }

    /// Find directories by tag.
    ///
    /// Useful for "what directories offer storage services?" queries.
    pub fn find_by_tags(&self, caller: MemberId, tags: &[&str]) -> Result<Vec<(&Name, &DirectoryEntry)>, DirectoryError> {
        self.directory.search_by_tags(caller, tags)
    }

    /// Get the underlying directory cell (for gossip topic binding, etc.).
    pub fn as_directory(&self) -> &DirectoryCell {
        &self.directory
    }

    /// Get the underlying directory cell mutably.
    pub fn as_directory_mut(&mut self) -> &mut DirectoryCell {
        &mut self.directory
    }
}

// ---------------------------------------------------------------------------
// Directory Factory
// ---------------------------------------------------------------------------

/// A factory that creates new directory cells with constrained properties.
///
/// In pyana, factories create cells with guaranteed invariants. A DirectoryFactory
/// ensures that created directories:
/// - Have a bounded membership set
/// - Have a gossip topic derived from their cell ID (deterministic)
/// - Are registered in the parent meta-directory
/// - Have a maximum capacity to prevent resource exhaustion
pub struct DirectoryFactory {
    /// The meta-directory that new directories are registered in.
    meta_directory_cell_id: CellId,
    /// Federation context for new directories.
    federation_id: FederationId,
    /// Default capacity for created directories.
    default_capacity: usize,
    /// Maximum allowed members per created directory.
    max_members: usize,
    /// Counter for generating deterministic cell IDs during creation.
    creation_counter: u64,
}

impl DirectoryFactory {
    /// Create a new directory factory.
    pub fn new(
        meta_directory_cell_id: CellId,
        federation_id: FederationId,
        default_capacity: usize,
        max_members: usize,
    ) -> Self {
        Self {
            meta_directory_cell_id,
            federation_id,
            default_capacity,
            max_members,
            creation_counter: 0,
        }
    }

    /// Create a new scoped directory.
    ///
    /// Returns the new directory cell and its gossip topic. The caller is responsible
    /// for registering it in the meta-directory and distributing the sturdy ref to
    /// authorized members.
    pub fn create_directory(
        &mut self,
        members: HashSet<MemberId>,
        current_height: u64,
    ) -> Result<DirectoryCell, DirectoryFactoryError> {
        if members.len() > self.max_members {
            return Err(DirectoryFactoryError::TooManyMembers {
                requested: members.len(),
                max: self.max_members,
            });
        }
        if members.is_empty() {
            return Err(DirectoryFactoryError::EmptyMembership);
        }

        // Generate a deterministic cell ID from the factory's state
        self.creation_counter += 1;
        let cell_id = self.derive_cell_id();

        let directory = DirectoryCell::with_capacity(
            cell_id,
            self.federation_id,
            members,
            current_height,
            self.default_capacity,
        );

        Ok(directory)
    }

    /// Derive a cell ID for the next directory to be created.
    fn derive_cell_id(&self) -> CellId {
        let hash = blake3::derive_key(
            "pyana-directory-factory-cell-id-v1",
            &[
                &self.meta_directory_cell_id.0[..],
                &self.federation_id.0[..],
                &self.creation_counter.to_le_bytes()[..],
            ]
            .concat(),
        );
        CellId(hash)
    }
}

/// Errors from directory factory operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DirectoryFactoryError {
    /// Too many members requested for the directory.
    TooManyMembers { requested: usize, max: usize },
    /// Cannot create a directory with no members.
    EmptyMembership,
}

impl std::fmt::Display for DirectoryFactoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyMembers { requested, max } => {
                write!(f, "too many members: {requested} exceeds max {max}")
            }
            Self::EmptyMembership => write!(f, "cannot create directory with no members"),
        }
    }
}

impl std::error::Error for DirectoryFactoryError {}

// ---------------------------------------------------------------------------
// Gossip Topic Scoping: how directory membership maps to topic subscription
// ---------------------------------------------------------------------------

/// Manages the relationship between directory membership and gossip topic subscriptions.
///
/// When a node holds a reference to a directory, they subscribe to that directory's
/// gossip topic. When the reference is dropped (CapTP GC fires a DropRef), they
/// unsubscribe. This ensures intents only propagate to authorized participants.
///
/// # Provable Audience Bounding
///
/// Because constitution membership is attested on the blocklace, we can produce a
/// proof: "at block height H, the directory had N members. Therefore, this intent
/// posted at height H was visible to at most N parties." This is the scoping guarantee.
pub struct TopicSubscriptionManager {
    /// Maps gossip topics to the set of currently subscribed members.
    subscriptions: HashMap<GossipTopic, HashSet<MemberId>>,
    /// Maps members to the set of topics they are subscribed to.
    member_topics: HashMap<MemberId, HashSet<GossipTopic>>,
}

impl TopicSubscriptionManager {
    /// Create a new subscription manager.
    pub fn new() -> Self {
        Self {
            subscriptions: HashMap::new(),
            member_topics: HashMap::new(),
        }
    }

    /// Subscribe a member to a directory's gossip topic.
    ///
    /// Called when a member enlivens a sturdy ref to a directory cell.
    pub fn subscribe(&mut self, member: MemberId, topic: GossipTopic) {
        self.subscriptions
            .entry(topic.clone())
            .or_default()
            .insert(member);
        self.member_topics
            .entry(member)
            .or_default()
            .insert(topic);
    }

    /// Unsubscribe a member from a topic.
    ///
    /// Called when CapTP GC fires a DropRef for the directory cell, or when
    /// a member is removed from the federation's constitution.
    pub fn unsubscribe(&mut self, member: &MemberId, topic: &GossipTopic) {
        if let Some(members) = self.subscriptions.get_mut(topic) {
            members.remove(member);
            if members.is_empty() {
                self.subscriptions.remove(topic);
            }
        }
        if let Some(topics) = self.member_topics.get_mut(member) {
            topics.remove(topic);
            if topics.is_empty() {
                self.member_topics.remove(member);
            }
        }
    }

    /// Unsubscribe a member from ALL topics (e.g., when they leave the federation).
    pub fn unsubscribe_all(&mut self, member: &MemberId) {
        if let Some(topics) = self.member_topics.remove(member) {
            for topic in topics {
                if let Some(members) = self.subscriptions.get_mut(&topic) {
                    members.remove(member);
                    if members.is_empty() {
                        self.subscriptions.remove(&topic);
                    }
                }
            }
        }
    }

    /// Get the current subscriber count for a topic (= audience bound).
    pub fn audience_size(&self, topic: &GossipTopic) -> usize {
        self.subscriptions
            .get(topic)
            .map_or(0, |members| members.len())
    }

    /// Get all topics a member is subscribed to.
    pub fn member_subscriptions(&self, member: &MemberId) -> Vec<&GossipTopic> {
        self.member_topics
            .get(member)
            .map(|topics| topics.iter().collect())
            .unwrap_or_default()
    }

    /// Produce a proof statement: "at this moment, topic T has N subscribers."
    ///
    /// In production, this would be attested on the blocklace (membership proof + height).
    /// Here we return the audience bound as a provable claim.
    pub fn audience_bound_claim(&self, topic: &GossipTopic) -> AudienceBoundClaim {
        let subscriber_ids: Vec<MemberId> = self
            .subscriptions
            .get(topic)
            .map(|members| members.iter().copied().collect())
            .unwrap_or_default();
        AudienceBoundClaim {
            topic: topic.clone(),
            audience_size: subscriber_ids.len(),
            member_commitments: subscriber_ids,
        }
    }
}

/// A claim about the audience bound for a gossip topic.
///
/// This can be used to prove: "this intent was visible to at most N parties."
/// In production, this would be attested on the blocklace with a membership proof.
#[derive(Clone, Debug)]
pub struct AudienceBoundClaim {
    /// The gossip topic this claim is about.
    pub topic: GossipTopic,
    /// The number of subscribers at the time of the claim.
    pub audience_size: usize,
    /// The member IDs who were subscribed (for verification against constitution).
    pub member_commitments: Vec<MemberId>,
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // Helpers

    fn member(id: u8) -> MemberId {
        MemberId([id; 32])
    }

    fn federation() -> FederationId {
        FederationId([0xFE; 32])
    }

    fn cell(id: u8) -> CellId {
        CellId([id; 32])
    }

    fn test_sturdy_ref(cell_id: CellId) -> SturdyRef {
        SturdyRef {
            federation_id: federation(),
            cell_id,
            swiss: [0xAA; 32],
        }
    }

    fn test_entry(cell_id: CellId, kind: EntryKind, tags: &[&str]) -> DirectoryEntry {
        DirectoryEntry {
            sturdy_ref: test_sturdy_ref(cell_id),
            version: 0,
            kind,
            description: None,
            tags: tags.iter().map(|t| t.to_string()).collect(),
            registered_at: 100,
            expires_at: None,
        }
    }

    fn test_directory() -> DirectoryCell {
        let members: HashSet<MemberId> = vec![member(1), member(2), member(3)].into_iter().collect();
        DirectoryCell::new(cell(0x10), federation(), members, 100)
    }

    // --- DirectoryCell tests ---

    #[test]
    fn new_directory_is_empty_with_version_zero() {
        let dir = test_directory();
        assert!(dir.is_empty());
        assert_eq!(dir.version, 0);
        assert_eq!(dir.member_count(), 3);
    }

    #[test]
    fn swap_insert_increments_version() {
        let mut dir = test_directory();
        let entry = test_entry(cell(1), EntryKind::Service, &["compute"]);
        let v = dir.swap(member(1), "my-service", 0, Some(entry)).unwrap();
        assert_eq!(v, 1);
        assert_eq!(dir.version, 1);
        assert_eq!(dir.len(), 1);
    }

    #[test]
    fn swap_update_requires_correct_version() {
        let mut dir = test_directory();
        let entry = test_entry(cell(1), EntryKind::Service, &["compute"]);
        let v1 = dir.swap(member(1), "svc", 0, Some(entry.clone())).unwrap();

        // Update with correct version
        let entry2 = test_entry(cell(2), EntryKind::Service, &["compute", "gpu"]);
        let v2 = dir.swap(member(1), "svc", v1, Some(entry2)).unwrap();
        assert_eq!(v2, 2);

        // Update with stale version fails
        let entry3 = test_entry(cell(3), EntryKind::Service, &["storage"]);
        let err = dir.swap(member(1), "svc", v1, Some(entry3)).unwrap_err();
        assert!(matches!(err, DirectoryError::VersionConflict { .. }));
    }

    #[test]
    fn swap_remove_deletes_entry() {
        let mut dir = test_directory();
        let entry = test_entry(cell(1), EntryKind::Service, &[]);
        let v = dir.swap(member(1), "ephemeral", 0, Some(entry)).unwrap();
        assert_eq!(dir.len(), 1);

        let v2 = dir.swap(member(1), "ephemeral", v, None).unwrap();
        assert_eq!(dir.len(), 0);
        assert!(v2 > v);
    }

    #[test]
    fn unauthorized_member_rejected() {
        let dir = test_directory();
        let outsider = member(99);
        let err = dir.list(outsider).unwrap_err();
        assert!(matches!(err, DirectoryError::Unauthorized { .. }));
    }

    #[test]
    fn list_returns_all_entries() {
        let mut dir = test_directory();
        for i in 0..5u8 {
            let entry = test_entry(cell(i), EntryKind::Service, &["svc"]);
            dir.swap(member(1), &format!("service-{i}"), 0, Some(entry)).unwrap();
        }
        let listing = dir.list(member(2)).unwrap();
        assert_eq!(listing.entries.len(), 5);
        assert_eq!(listing.directory_version, 5);
    }

    #[test]
    fn get_returns_specific_entry() {
        let mut dir = test_directory();
        let entry = test_entry(cell(42), EntryKind::DataSource, &["oracle"]);
        dir.swap(member(1), "price-oracle", 0, Some(entry)).unwrap();

        let retrieved = dir.get(member(2), "price-oracle").unwrap();
        assert_eq!(retrieved.sturdy_ref.cell_id, cell(42));
        assert_eq!(retrieved.kind, EntryKind::DataSource);
    }

    #[test]
    fn get_not_found() {
        let dir = test_directory();
        let err = dir.get(member(1), "nonexistent").unwrap_err();
        assert!(matches!(err, DirectoryError::NotFound { .. }));
    }

    #[test]
    fn invalid_names_rejected() {
        let mut dir = test_directory();
        let entry = test_entry(cell(1), EntryKind::Service, &[]);

        // Empty name
        let err = dir.swap(member(1), "", 0, Some(entry.clone())).unwrap_err();
        assert!(matches!(err, DirectoryError::InvalidName { .. }));

        // Name with null byte
        let err = dir.swap(member(1), "bad\0name", 0, Some(entry.clone())).unwrap_err();
        assert!(matches!(err, DirectoryError::InvalidName { .. }));

        // Name too long
        let long_name = "x".repeat(MAX_NAME_LEN + 1);
        let err = dir.swap(member(1), &long_name, 0, Some(entry)).unwrap_err();
        assert!(matches!(err, DirectoryError::InvalidName { .. }));
    }

    #[test]
    fn capacity_limit_enforced() {
        let members: HashSet<MemberId> = vec![member(1)].into_iter().collect();
        let mut dir = DirectoryCell::with_capacity(cell(0x20), federation(), members, 0, 3);

        for i in 0..3u8 {
            let entry = test_entry(cell(i), EntryKind::Service, &[]);
            dir.swap(member(1), &format!("s{i}"), 0, Some(entry)).unwrap();
        }

        // Fourth insert should fail
        let entry = test_entry(cell(99), EntryKind::Service, &[]);
        let err = dir.swap(member(1), "overflow", 0, Some(entry)).unwrap_err();
        assert!(matches!(err, DirectoryError::Full { capacity: 3 }));
    }

    #[test]
    fn search_by_tags_filters_correctly() {
        let mut dir = test_directory();
        dir.swap(member(1), "gpu-compute", 0, Some(test_entry(cell(1), EntryKind::Service, &["compute", "gpu"]))).unwrap();
        dir.swap(member(1), "cpu-compute", 0, Some(test_entry(cell(2), EntryKind::Service, &["compute", "cpu"]))).unwrap();
        dir.swap(member(1), "storage", 0, Some(test_entry(cell(3), EntryKind::DataSource, &["storage"]))).unwrap();

        let results = dir.search_by_tags(member(1), &["compute"]).unwrap();
        assert_eq!(results.len(), 2);

        let results = dir.search_by_tags(member(1), &["compute", "gpu"]).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, "gpu-compute");
    }

    #[test]
    fn search_by_kind_filters_correctly() {
        let mut dir = test_directory();
        dir.swap(member(1), "svc1", 0, Some(test_entry(cell(1), EntryKind::Service, &[]))).unwrap();
        dir.swap(member(1), "svc2", 0, Some(test_entry(cell(2), EntryKind::Service, &[]))).unwrap();
        dir.swap(member(1), "data1", 0, Some(test_entry(cell(3), EntryKind::DataSource, &[]))).unwrap();

        let results = dir.search_by_kind(member(1), &EntryKind::Service).unwrap();
        assert_eq!(results.len(), 2);

        let results = dir.search_by_kind(member(1), &EntryKind::DataSource).unwrap();
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn gc_expired_removes_stale_entries() {
        let mut dir = test_directory();
        let mut entry1 = test_entry(cell(1), EntryKind::Service, &[]);
        entry1.expires_at = Some(200);
        let mut entry2 = test_entry(cell(2), EntryKind::Service, &[]);
        entry2.expires_at = Some(500);
        let entry3 = test_entry(cell(3), EntryKind::Service, &[]); // no expiry

        dir.swap(member(1), "short-lived", 0, Some(entry1)).unwrap();
        dir.swap(member(1), "medium-lived", 0, Some(entry2)).unwrap();
        dir.swap(member(1), "permanent", 0, Some(entry3)).unwrap();

        assert_eq!(dir.len(), 3);
        let removed = dir.gc_expired(300);
        assert_eq!(removed, 1);
        assert_eq!(dir.len(), 2);
        assert!(dir.get(member(1), "medium-lived").is_ok());
        assert!(dir.get(member(1), "permanent").is_ok());
    }

    #[test]
    fn membership_changes_affect_access() {
        let mut dir = test_directory();
        let entry = test_entry(cell(1), EntryKind::Service, &[]);
        dir.swap(member(1), "svc", 0, Some(entry)).unwrap();

        // New member can access after being added
        let new_member = member(50);
        assert!(!dir.is_member(&new_member));
        dir.add_member(new_member);
        assert!(dir.get(new_member, "svc").is_ok());

        // Removed member loses access
        dir.remove_member(new_member);
        assert!(dir.get(new_member, "svc").is_err());
    }

    #[test]
    fn gossip_topic_is_deterministic() {
        let members: HashSet<MemberId> = vec![member(1)].into_iter().collect();
        let dir1 = DirectoryCell::new(cell(0x42), federation(), members.clone(), 0);
        let dir2 = DirectoryCell::new(cell(0x42), federation(), members, 100);
        // Same cell ID -> same gossip topic, regardless of creation time
        assert_eq!(dir1.gossip_topic, dir2.gossip_topic);

        // Different cell ID -> different topic
        let members2: HashSet<MemberId> = vec![member(1)].into_iter().collect();
        let dir3 = DirectoryCell::new(cell(0x43), federation(), members2, 0);
        assert_ne!(dir1.gossip_topic, dir3.gossip_topic);
    }

    // --- ScopedIntentPool tests ---

    #[test]
    fn scoped_pool_binds_to_directory_topic() {
        let dir = test_directory();
        let pool = ScopedIntentPool::new(&dir, 100);
        assert_eq!(pool.topic(), &dir.gossip_topic);
    }

    #[test]
    fn subscribe_requires_membership() {
        let dir = test_directory();
        let mut pool = ScopedIntentPool::new(&dir, 100);

        // Member can subscribe
        let topic = pool.subscribe(member(1), &dir).unwrap();
        assert_eq!(topic, &dir.gossip_topic);
        assert_eq!(pool.subscriber_count(), 1);

        // Non-member cannot subscribe
        let err = pool.subscribe(member(99), &dir).unwrap_err();
        assert!(matches!(err, ScopedPoolError::NotInScope { .. }));
    }

    #[test]
    fn post_and_gc_intents() {
        let dir = test_directory();
        let mut pool = ScopedIntentPool::new(&dir, 100);
        pool.subscribe(member(1), &dir).unwrap();

        let intent = ScopedIntent {
            id: [0x01; 32],
            directory_cell_id: dir.cell_id,
            kind: ScopedIntentKind::Need,
            match_pattern: MatchPattern {
                required_tags: vec!["compute".to_string()],
                required_kind: Some(EntryKind::Service),
                name_prefix: None,
                custom_predicate: None,
            },
            creator: CommitmentId([0xCC; 32]),
            expiry: 500,
        };

        pool.post_intent(intent, 100, &dir).unwrap();
        assert_eq!(pool.len(), 1);

        // GC at time 600: intent expired
        let removed = pool.gc(600);
        assert_eq!(removed, 1);
        assert!(pool.is_empty());
    }

    #[test]
    fn scoped_pool_rejects_duplicates() {
        let dir = test_directory();
        let mut pool = ScopedIntentPool::new(&dir, 100);

        let intent = ScopedIntent {
            id: [0x02; 32],
            directory_cell_id: dir.cell_id,
            kind: ScopedIntentKind::Offer,
            match_pattern: MatchPattern {
                required_tags: vec![],
                required_kind: None,
                name_prefix: None,
                custom_predicate: None,
            },
            creator: CommitmentId([0xDD; 32]),
            expiry: 999,
        };

        pool.post_intent(intent.clone(), 100, &dir).unwrap();
        let err = pool.post_intent(intent, 100, &dir).unwrap_err();
        assert_eq!(err, ScopedPoolError::Duplicate);
    }

    #[test]
    fn scoped_pool_enforces_capacity() {
        let dir = test_directory();
        let mut pool = ScopedIntentPool::new(&dir, 2); // tiny pool

        for i in 0..2u8 {
            let intent = ScopedIntent {
                id: [i; 32],
                directory_cell_id: dir.cell_id,
                kind: ScopedIntentKind::Need,
                match_pattern: MatchPattern {
                    required_tags: vec![],
                    required_kind: None,
                    name_prefix: None,
                    custom_predicate: None,
                },
                creator: CommitmentId([i + 0x10; 32]),
                expiry: 999,
            };
            pool.post_intent(intent, 100, &dir).unwrap();
        }

        let overflow_intent = ScopedIntent {
            id: [0xFF; 32],
            directory_cell_id: dir.cell_id,
            kind: ScopedIntentKind::Need,
            match_pattern: MatchPattern {
                required_tags: vec![],
                required_kind: None,
                name_prefix: None,
                custom_predicate: None,
            },
            creator: CommitmentId([0xEE; 32]),
            expiry: 999,
        };
        let err = pool.post_intent(overflow_intent, 100, &dir).unwrap_err();
        assert_eq!(err, ScopedPoolError::Full);
    }

    #[test]
    fn match_against_directory_finds_entries() {
        let mut dir = test_directory();
        dir.swap(member(1), "gpu-service", 0, Some(test_entry(cell(1), EntryKind::Service, &["compute", "gpu"]))).unwrap();
        dir.swap(member(1), "storage-node", 0, Some(test_entry(cell(2), EntryKind::DataSource, &["storage"]))).unwrap();

        let mut pool = ScopedIntentPool::new(&dir, 100);

        // Post an intent needing a compute service
        let intent = ScopedIntent {
            id: [0x10; 32],
            directory_cell_id: dir.cell_id,
            kind: ScopedIntentKind::Need,
            match_pattern: MatchPattern {
                required_tags: vec!["compute".to_string()],
                required_kind: Some(EntryKind::Service),
                name_prefix: None,
                custom_predicate: None,
            },
            creator: CommitmentId([0xAA; 32]),
            expiry: 999,
        };
        pool.post_intent(intent, 100, &dir).unwrap();

        // Post an intent needing storage (shouldn't match a service)
        let intent2 = ScopedIntent {
            id: [0x20; 32],
            directory_cell_id: dir.cell_id,
            kind: ScopedIntentKind::Need,
            match_pattern: MatchPattern {
                required_tags: vec!["storage".to_string()],
                required_kind: Some(EntryKind::Service), // kind mismatch!
                name_prefix: None,
                custom_predicate: None,
            },
            creator: CommitmentId([0xBB; 32]),
            expiry: 999,
        };
        pool.post_intent(intent2, 100, &dir).unwrap();

        let matches = pool.match_against_directory(&dir, member(1)).unwrap();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].0, [0x10; 32]);
        assert_eq!(matches[0].1, "gpu-service");
    }

    // --- MetaDirectory tests ---

    #[test]
    fn meta_directory_registers_and_looks_up_subdirectories() {
        let members: HashSet<MemberId> = vec![member(1), member(2)].into_iter().collect();
        let mut meta = MetaDirectory::new(cell(0x01), federation(), members, 0);

        let compute_ref = test_sturdy_ref(cell(0x10));
        let storage_ref = test_sturdy_ref(cell(0x20));

        meta.register_directory(
            member(1),
            "compute",
            compute_ref.clone(),
            Some("Compute services".into()),
            100,
        ).unwrap();

        meta.register_directory(
            member(1),
            "storage",
            storage_ref.clone(),
            Some("Storage providers".into()),
            101,
        ).unwrap();

        // Lookup
        let entry = meta.lookup(member(2), "compute").unwrap();
        assert_eq!(entry.sturdy_ref.cell_id, cell(0x10));
        assert_eq!(entry.kind, EntryKind::SubDirectory);

        // List all
        let listing = meta.list_directories(member(2)).unwrap();
        assert_eq!(listing.entries.len(), 2);
    }

    #[test]
    fn meta_directory_unauthorized_rejected() {
        let members: HashSet<MemberId> = vec![member(1)].into_iter().collect();
        let meta = MetaDirectory::new(cell(0x01), federation(), members, 0);

        let err = meta.list_directories(member(99)).unwrap_err();
        assert!(matches!(err, DirectoryError::Unauthorized { .. }));
    }

    // --- TopicSubscriptionManager tests ---

    #[test]
    fn subscribe_and_unsubscribe() {
        let mut mgr = TopicSubscriptionManager::new();
        let topic = GossipTopic([0x42; 32]);

        mgr.subscribe(member(1), topic.clone());
        mgr.subscribe(member(2), topic.clone());
        assert_eq!(mgr.audience_size(&topic), 2);

        mgr.unsubscribe(&member(1), &topic);
        assert_eq!(mgr.audience_size(&topic), 1);

        mgr.unsubscribe(&member(2), &topic);
        assert_eq!(mgr.audience_size(&topic), 0);
    }

    #[test]
    fn unsubscribe_all_removes_from_all_topics() {
        let mut mgr = TopicSubscriptionManager::new();
        let topic_a = GossipTopic([0x0A; 32]);
        let topic_b = GossipTopic([0x0B; 32]);

        mgr.subscribe(member(1), topic_a.clone());
        mgr.subscribe(member(1), topic_b.clone());
        mgr.subscribe(member(2), topic_a.clone());

        mgr.unsubscribe_all(&member(1));
        assert_eq!(mgr.audience_size(&topic_a), 1); // only member(2) remains
        assert_eq!(mgr.audience_size(&topic_b), 0);
        assert!(mgr.member_subscriptions(&member(1)).is_empty());
    }

    #[test]
    fn audience_bound_claim_reflects_current_state() {
        let mut mgr = TopicSubscriptionManager::new();
        let topic = GossipTopic([0x77; 32]);

        mgr.subscribe(member(1), topic.clone());
        mgr.subscribe(member(2), topic.clone());
        mgr.subscribe(member(3), topic.clone());

        let claim = mgr.audience_bound_claim(&topic);
        assert_eq!(claim.audience_size, 3);
        assert_eq!(claim.member_commitments.len(), 3);
    }

    #[test]
    fn member_subscriptions_lists_topics() {
        let mut mgr = TopicSubscriptionManager::new();
        let topic_a = GossipTopic([0x0A; 32]);
        let topic_b = GossipTopic([0x0B; 32]);
        let topic_c = GossipTopic([0x0C; 32]);

        mgr.subscribe(member(1), topic_a.clone());
        mgr.subscribe(member(1), topic_b.clone());

        let subs = mgr.member_subscriptions(&member(1));
        assert_eq!(subs.len(), 2);

        // Member 2 has no subscriptions
        let subs = mgr.member_subscriptions(&member(2));
        assert!(subs.is_empty());

        let _ = topic_c; // unused, just showing it exists
    }

    // --- DirectoryFactory tests ---

    #[test]
    fn factory_creates_directories_with_unique_cell_ids() {
        let mut factory = DirectoryFactory::new(cell(0x01), federation(), 1000, 100);
        let members: HashSet<MemberId> = vec![member(1), member(2)].into_iter().collect();

        let dir1 = factory.create_directory(members.clone(), 100).unwrap();
        let dir2 = factory.create_directory(members, 200).unwrap();

        // Different cell IDs
        assert_ne!(dir1.cell_id, dir2.cell_id);
        // Different gossip topics (derived from cell ID)
        assert_ne!(dir1.gossip_topic, dir2.gossip_topic);
    }

    #[test]
    fn factory_rejects_too_many_members() {
        let mut factory = DirectoryFactory::new(cell(0x01), federation(), 1000, 3);
        let members: HashSet<MemberId> = (0..5).map(|i| member(i)).collect();

        let err = factory.create_directory(members, 100).unwrap_err();
        assert!(matches!(err, DirectoryFactoryError::TooManyMembers { .. }));
    }

    #[test]
    fn factory_rejects_empty_membership() {
        let mut factory = DirectoryFactory::new(cell(0x01), federation(), 1000, 100);
        let err = factory.create_directory(HashSet::new(), 100).unwrap_err();
        assert_eq!(err, DirectoryFactoryError::EmptyMembership);
    }

    // --- Integration: end-to-end scoped discovery flow ---

    #[test]
    fn end_to_end_scoped_discovery() {
        // 1. A meta-directory exists at the federation level
        let all_members: HashSet<MemberId> = (1..=5).map(|i| member(i)).collect();
        let mut meta = MetaDirectory::new(cell(0x01), federation(), all_members.clone(), 0);

        // 2. A factory creates a scoped "compute" directory for a subset of members
        let mut factory = DirectoryFactory::new(cell(0x01), federation(), 500, 50);
        let compute_members: HashSet<MemberId> = vec![member(1), member(2), member(3)].into_iter().collect();
        let mut compute_dir = factory.create_directory(compute_members, 100).unwrap();

        // 3. Register the compute directory in the meta-directory
        let compute_ref = SturdyRef {
            federation_id: federation(),
            cell_id: compute_dir.cell_id,
            swiss: [0xCC; 32],
        };
        meta.register_directory(member(1), "compute", compute_ref, Some("Compute services".into()), 100).unwrap();

        // 4. Providers register their services in the compute directory
        let gpu_service_ref = SturdyRef {
            federation_id: federation(),
            cell_id: cell(0x50),
            swiss: [0x50; 32],
        };
        let gpu_entry = DirectoryEntry {
            sturdy_ref: gpu_service_ref,
            version: 0,
            kind: EntryKind::Service,
            description: Some("GPU compute service, 8x A100".into()),
            tags: vec!["compute".into(), "gpu".into(), "a100".into()],
            registered_at: 101,
            expires_at: None,
        };
        compute_dir.swap(member(2), "provider-alpha/gpu", 0, Some(gpu_entry)).unwrap();

        // 5. A subscriber creates a scoped intent pool and posts a need
        let mut pool = ScopedIntentPool::new(&compute_dir, 100);
        pool.subscribe(member(1), &compute_dir).unwrap();
        pool.subscribe(member(2), &compute_dir).unwrap();

        let need_gpu = ScopedIntent {
            id: [0xAB; 32],
            directory_cell_id: compute_dir.cell_id,
            kind: ScopedIntentKind::Need,
            match_pattern: MatchPattern {
                required_tags: vec!["gpu".to_string()],
                required_kind: Some(EntryKind::Service),
                name_prefix: Some("provider-".into()),
                custom_predicate: None,
            },
            creator: CommitmentId([0x11; 32]),
            expiry: 9999,
        };
        pool.post_intent(need_gpu, 200, &compute_dir).unwrap();

        // 6. Matching: the intent finds the GPU service
        let matches = pool.match_against_directory(&compute_dir, member(1)).unwrap();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].1, "provider-alpha/gpu");

        // 7. Audience bounding: only 2 subscribers saw this intent
        let mut topic_mgr = TopicSubscriptionManager::new();
        topic_mgr.subscribe(member(1), compute_dir.gossip_topic.clone());
        topic_mgr.subscribe(member(2), compute_dir.gossip_topic.clone());

        let claim = topic_mgr.audience_bound_claim(&compute_dir.gossip_topic);
        assert_eq!(claim.audience_size, 2);
        // Provable: member(4) and member(5) NEVER saw this intent because they
        // are not subscribers of this directory's gossip topic.

        // 8. Non-members of the compute directory cannot even list its contents
        assert!(compute_dir.list(member(4)).is_err());
        assert!(compute_dir.list(member(5)).is_err());
    }
}
