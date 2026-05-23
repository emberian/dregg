# Pyana Name Service Design

## Overview

The name service sits at the intersection of three existing subsystems:

- **Governed namespace** (`apps/governed-namespace/`) — DFA-routed directories with constitutional governance, CAS-versioned mounts, authorization levels
- **Capability directories** (`rbg/src/directory.rs`) — capability-secure `DirectoryCell` with hierarchical subdirectories, `MetaDirectory` yellow pages, and gossip-scoped intent pools
- **CapTP** (`captp/`) — `pyana://` sturdy refs, swiss number tables, and the enliven/revoke lifecycle

The name service is **not** a new standalone system. It is a composition layer that unifies these pieces into a coherent naming protocol, with petnames providing the user-facing layer.

---

## 1. Architecture: Hybrid Model

```
┌─────────────────────────────────────────────────────────┐
│                    Agent Wallet (local)                  │
│                                                         │
│   ┌─────────────┐   ┌───────────────┐   ┌──────────┐  │
│   │  Petname DB │   │ Edge Name Cache│   │ Resolver │  │
│   └─────────────┘   └───────────────┘   └──────────┘  │
└────────────────────────────┬────────────────────────────┘
                             │ resolve / register
                             ▼
┌─────────────────────────────────────────────────────────┐
│           Federation Name Directory (remote)             │
│                                                         │
│   DirectoryCell<Name → SturdyRef> + governance          │
│   (governed-namespace Registry with ServiceKind::Name)  │
│   DFA router controls who can register WHERE            │
└────────────────────────────┬────────────────────────────┘
                             │ sub-directory lookup
                             ▼
┌─────────────────────────────────────────────────────────┐
│         MetaDirectory (cross-federation yellow pages)    │
│                                                         │
│   Entries: federation-name → SturdyRef to that          │
│            federation's NameDirectory                    │
└─────────────────────────────────────────────────────────┘
```

### Where each piece lives:

| Component | Location | Persistence |
|-----------|----------|-------------|
| Petname DB | Wallet (local, never leaves device) | `sdk/src/wallet.rs` state |
| Edge name cache | Wallet (local, populated from contacts) | Ephemeral, refreshed on connect |
| Federation name directory | `apps/governed-namespace` Registry cell | On-chain (blocklace) |
| Cross-federation meta-directory | `rbg/` MetaDirectory cell | On-chain (blocklace) |
| Name resolution protocol | Turn effect (`Effect::ResolveName`) | N/A (protocol) |

### Why hybrid:

- Petnames are private by definition — storing them remotely leaks your social graph.
- Edge names are self-asserted — the contact controls them, you cache them.
- Proposed/registered names require governance — they must live in the governed directory.
- Cross-federation resolution requires a meta-directory that multiple federations can reference.

---

## 2. Petname System (Zooko's Triangle)

### 2.1 Name Categories

```rust
/// A name entry in the wallet's local petname database.
/// Corresponds to one of three Zooko-triangle categories.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum NameEntry {
    /// YOUR name for something. Completely local, never shared.
    /// Source: user assigns manually or from UI suggestion.
    Petname {
        label: String,
        target: PyanaUri,
        /// When you assigned this petname.
        assigned_at: u64,
        /// Optional notes (e.g., "alice from the hackathon").
        notes: Option<String>,
    },

    /// What a CONTACT calls themselves. Populated from their profile cell.
    /// Displayed as "Alice (self-claimed)" in UI.
    /// Source: fetched from contact's profile cell on connection.
    EdgeName {
        label: String,
        target: PyanaUri,
        /// The contact who claims this name.
        source: PyanaUri,
        /// When this was last fetched from the contact's profile.
        last_refreshed: u64,
    },

    /// What the COMMUNITY calls something. Governance-voted, stored in
    /// the federation's name directory.
    /// Source: fetched from federation NameDirectory on lookup.
    ProposedName {
        label: String,
        target: PyanaUri,
        /// Which federation directory this came from.
        directory: PyanaUri,
        /// Governance vote weight at registration time.
        vote_weight: u64,
        /// Expiry epoch (from directory entry's expires_at).
        expires_at: Option<u64>,
    },
}
```

### 2.2 Resolution Priority

When the user types a name, resolution proceeds in strict priority order:

```
1. Petname (local)        — Highest priority. YOUR name = YOUR truth.
2. Edge name (contact)    — What the target calls itself.
3. Proposed name (dir)    — Community consensus name.
4. Raw CellId / URI       — Direct addressing, no resolution needed.
```

If there is a conflict (your petname for X points to CellA, but the community name "X" points to CellB), the petname wins. This is the fundamental security property: **you cannot be phished by a community vote renaming something**.

### 2.3 Resolution Algorithm

```rust
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

#[derive(Clone, Debug)]
pub enum NameProvenance {
    /// Resolved from local petname DB.
    LocalPetname,
    /// Resolved from a contact's self-claimed edge name.
    EdgeName { source: PyanaUri },
    /// Resolved from a governed federation directory.
    FederationDirectory { directory: PyanaUri, vote_weight: u64 },
    /// Resolved from a cross-federation meta-directory lookup.
    CrossFederation { home_federation: PyanaUri, target_federation: PyanaUri },
    /// No resolution needed — raw URI passed through.
    Direct,
}

impl AgentWallet {
    /// Resolve a human-readable name to a sturdy ref.
    ///
    /// Resolution order: petname > edge name > proposed name > hierarchical lookup.
    pub async fn resolve(&self, name: &str) -> Result<ResolvedName, NameError> {
        // 1. Check local petnames first (instant, no network).
        if let Some(entry) = self.petname_db.lookup(name) {
            return Ok(ResolvedName {
                target: entry.target().clone(),
                provenance: NameProvenance::LocalPetname,
                confidence: 1.0,
            });
        }

        // 2. Check edge name cache (local, from last contact sync).
        if let Some(edge) = self.edge_name_cache.lookup(name) {
            return Ok(ResolvedName {
                target: edge.target.clone(),
                provenance: NameProvenance::EdgeName { source: edge.source.clone() },
                confidence: 0.8,
            });
        }

        // 3. If name contains dots, try hierarchical resolution.
        if name.contains('.') {
            return self.resolve_hierarchical(name).await;
        }

        // 4. Query home federation's name directory.
        self.resolve_from_federation_directory(name).await
    }
}
```

---

## 3. Hierarchical Naming Scheme

### 3.1 Name Grammar

```
<name>                            → local resolution (wallet petname DB)
<name>.<federation>.pyana         → hierarchical (federation directory lookup)
<name>.<sub>.<federation>.pyana   → nested hierarchy (sub-directory traversal)
pyana://<fed>/<cell>/<swiss>      → direct addressing (no resolution)
```

### 3.2 Hierarchical Resolution

```rust
/// Resolve a hierarchical name like "alice.federation-a.pyana".
///
/// Algorithm:
/// 1. Split on '.' from RIGHT: ["pyana", "federation-a", "alice"]
/// 2. Strip TLD ("pyana")
/// 3. Resolve federation name from the meta-directory (root)
/// 4. Traverse sub-directories left-to-right for remaining segments
async fn resolve_hierarchical(&self, name: &str) -> Result<ResolvedName, NameError> {
    let segments: Vec<&str> = name.rsplitn(3, '.').collect();
    // segments for "alice.federation-a.pyana" = ["pyana", "federation-a", "alice"]

    if segments.first() != Some(&"pyana") {
        return Err(NameError::UnknownTld(segments[0].to_string()));
    }

    let federation_name = segments.get(1)
        .ok_or(NameError::MalformedHierarchy)?;
    let leaf_name = segments.get(2); // May be None for bare federation lookup

    // Step 1: Resolve federation from meta-directory.
    let federation_dir_ref = self.meta_directory_lookup(federation_name).await?;

    // Step 2: Enliven the federation's directory sturdy ref.
    let federation_dir = self.enliven_directory(federation_dir_ref).await?;

    // Step 3: Look up the leaf name in that directory.
    match leaf_name {
        Some(leaf) => {
            // May contain further dots for nested sub-directories.
            self.traverse_directory(federation_dir, leaf).await
        }
        None => {
            // Bare federation name — return the directory itself.
            Ok(ResolvedName {
                target: federation_dir_ref,
                provenance: NameProvenance::FederationDirectory {
                    directory: federation_dir_ref,
                    vote_weight: 0,
                },
                confidence: 0.9,
            })
        }
    }
}

/// Traverse nested sub-directories for multi-segment names.
///
/// For "services.alice.community.pyana":
///   - "community" resolved from meta-directory → community directory
///   - "alice" resolved from community directory → alice's sub-directory
///   - "services" resolved from alice's sub-directory → final target
async fn traverse_directory(
    &self,
    root_dir: PyanaUri,
    path: &str,
) -> Result<ResolvedName, NameError> {
    let segments: Vec<&str> = path.split('.').collect();
    let mut current_dir = root_dir;

    for (i, segment) in segments.iter().rev().enumerate() {
        let entry = self.directory_get(current_dir, segment).await?;

        if i == segments.len() - 1 {
            // Final segment — this is the target.
            return Ok(ResolvedName {
                target: entry.sturdy_ref,
                provenance: NameProvenance::FederationDirectory {
                    directory: current_dir,
                    vote_weight: entry.vote_weight.unwrap_or(0),
                },
                confidence: 0.9,
            });
        }

        // Intermediate segment — must be a sub-directory.
        if entry.kind != EntryKind::SubDirectory {
            return Err(NameError::NotADirectory {
                segment: segment.to_string(),
            });
        }
        current_dir = entry.sturdy_ref;
    }

    unreachable!()
}
```

### 3.3 Name Format Rules

```rust
/// Validation rules for name segments.
const MAX_SEGMENT_LEN: usize = 63;   // DNS-compatible
const MAX_TOTAL_LEN: usize = 253;    // DNS-compatible
const VALID_CHARS: &str = "abcdefghijklmnopqrstuvwxyz0123456789-_";

fn validate_name_segment(segment: &str) -> Result<(), NameError> {
    if segment.is_empty() {
        return Err(NameError::EmptySegment);
    }
    if segment.len() > MAX_SEGMENT_LEN {
        return Err(NameError::SegmentTooLong(segment.len()));
    }
    if segment.starts_with('-') || segment.ends_with('-') {
        return Err(NameError::InvalidSegment("cannot start/end with hyphen".into()));
    }
    if !segment.chars().all(|c| VALID_CHARS.contains(c)) {
        return Err(NameError::InvalidSegment("contains invalid characters".into()));
    }
    Ok(())
}
```

---

## 4. Name as Capability

### 4.1 Core Insight

A name registration IS a directory mount. The governed-namespace `Registry::mount()` already implements exactly this:

```rust
// From apps/governed-namespace/src/registry.rs:
pub async fn mount(
    &self,
    namespace: &Namespace,
    path: &str,
    entry: ServiceEntry,
    expected_version: u64,
    auth: &AuthLevel,
) -> Result<MountedService, RegistryError>
```

A name registration is a `mount` where:
- `path` = the name being registered (e.g., "/names/alice")
- `entry.sturdy_ref` = what the name points to
- `entry.kind` = `ServiceKind::Custom("name")` or a new `ServiceKind::Name`
- Authorization comes from the DFA router (who can register under which prefix)

### 4.2 Name Entry Extension

```rust
/// Extension to ServiceEntry for name-specific metadata.
/// Stored in the governed-namespace Registry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameRegistration {
    /// The base service entry (path, sturdy_ref, owner, version, etc.)
    pub entry: ServiceEntry,
    /// Name-specific metadata.
    pub name_meta: NameMetadata,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameMetadata {
    /// Whether this name holder can create sub-names.
    /// e.g., alice owns "alice" → can create "*.alice" entries.
    pub delegation_authority: DelegationAuthority,
    /// Profile data (edge name, avatar hash, bio, etc.)
    pub profile: Option<ProfileData>,
    /// Computron quota ID funding this name's rent.
    pub quota_id: QuotaId,
    /// Last activity epoch (for expiry tracking).
    pub last_active_epoch: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DelegationAuthority {
    /// Cannot delegate (leaf name).
    None,
    /// Can create sub-names under a prefix without governance vote.
    SubPrefix {
        /// The prefix this authority covers (e.g., "*.alice").
        prefix: String,
        /// Maximum sub-names allowed.
        max_children: u32,
        /// Current child count.
        current_children: u32,
    },
}
```

### 4.3 Sub-delegation

When Alice registers "alice" in the federation directory:

```rust
// Alice registers her top-level name (requires governance or open registration).
registry.mount(
    &namespace,
    "/names/alice",
    ServiceEntry {
        name: "alice".to_string(),
        kind: ServiceKind::Custom("name".to_string()),
        sturdy_ref: alice_cell_uri.to_uri_string(),
        owner: alice_pubkey,
        version: 0,
        tags: vec!["name".into(), "identity".into()],
        description: "Alice's identity".into(),
        registered_at: 0,
        expires_at: Some(current_epoch + RENTAL_PERIOD),
        health_endpoint: None,
    },
    0,
    &AuthLevel::Member,
).await?;

// Alice now has DelegationAuthority::SubPrefix { prefix: "/names/alice/" }
// She can mount sub-names WITHOUT a governance vote:
registry.mount(
    &namespace,
    "/names/alice/my-service",
    ServiceEntry {
        name: "my-service".to_string(),
        kind: ServiceKind::Custom("name".to_string()),
        sturdy_ref: alice_service_uri.to_uri_string(),
        owner: alice_pubkey,
        ..
    },
    0,
    &AuthLevel::Member,  // Her membership + ownership of parent = authorized
).await?;
```

This composes with the existing DFA router. The route table gains a new rule:

```
/names/<owner>/*   → owner has SubPrefix authority → authorized without governance vote
/names/<new>       → requires governance vote (or open registration + computron payment)
```

### 4.4 Holding a Name = Holding a Capability

The name itself is exported as a sturdy ref:

```rust
// The name registration produces a sturdy ref to the name entry.
// This ref IS the capability to update/delegate/transfer the name.
let name_swiss = swiss_table.export(
    name_cell_id,
    AuthRequired::Owner,
    Some(EffectMask::name_management()),  // update, delegate, transfer
    None,  // no expiry on the management cap
    current_height,
    None,  // unlimited uses
);

let name_capability_uri = PyanaUri {
    federation_id,
    cell_id: name_cell_id,
    swiss: name_swiss,
};

// Transfer the name: give someone else the management sturdy ref.
// They can now update what the name points to.
```

---

## 5. Anti-Squatting

### 5.1 Rent Model

Names are rented, not owned forever. This uses the `storage/` crate's computron model directly.

```rust
/// Name rental cost calculation.
/// Builds on storage::MeteringPolicy but with name-specific parameters.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameRentalPolicy {
    /// Base cost per epoch to hold any name (prevents zero-cost squatting).
    pub base_rent_per_epoch: u64,
    /// Per-character discount: shorter names cost MORE (premium pricing).
    /// Cost multiplier = max(1, (MAX_PREMIUM_LEN - name.len()))
    pub premium_length_threshold: usize,
    /// Cost multiplier per character below the threshold.
    pub premium_per_char: u64,
    /// Number of epochs before an unfunded name becomes reclaimable.
    pub grace_period_epochs: u64,
    /// Activity threshold: name must have at least this many resolutions
    /// per epoch to avoid "inactive" status.
    pub min_resolutions_per_epoch: u64,
}

impl NameRentalPolicy {
    pub fn default_policy() -> Self {
        Self {
            base_rent_per_epoch: 100,        // 100 computrons/epoch
            premium_length_threshold: 5,      // names <= 5 chars are premium
            premium_per_char: 200,            // 200 computrons/char for short names
            grace_period_epochs: 10,          // 10 epochs grace period
            min_resolutions_per_epoch: 0,     // no activity requirement by default
        }
    }

    /// Calculate rent for a name for N epochs.
    pub fn calculate_rent(&self, name: &str, epochs: u64) -> u64 {
        let base = self.base_rent_per_epoch * epochs;
        let premium = if name.len() < self.premium_length_threshold {
            let chars_below = (self.premium_length_threshold - name.len()) as u64;
            chars_below * self.premium_per_char * epochs
        } else {
            0
        };
        base + premium
    }
}
```

### 5.2 Expiry and Reclamation

```rust
/// Name lifecycle states.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NameStatus {
    /// Active — funded, resolvable.
    Active { funded_until_epoch: u64 },
    /// Grace period — funding lapsed, still resolvable but pending reclamation.
    Grace { grace_expires_epoch: u64 },
    /// Expired — no longer resolvable, available for re-registration.
    Expired,
    /// Disputed — frozen during conflict resolution.
    Disputed { dispute_id: [u8; 32] },
}

/// Epoch-triggered GC for expired names.
/// Runs as part of the federation's epoch processing (same as storage GC).
pub fn gc_expired_names(
    registry: &mut Registry,
    policy: &NameRentalPolicy,
    current_epoch: u64,
) -> Vec<ReclaimedName> {
    let mut reclaimed = Vec::new();

    for mounted in registry.all_services_sync() {
        if mounted.entry.kind != ServiceKind::Custom("name".to_string()) {
            continue;
        }
        if let Some(expires_at) = mounted.entry.expires_at {
            if current_epoch > expires_at + policy.grace_period_epochs {
                // Past grace period — reclaim.
                registry.unmount_unchecked(&mounted.path);
                reclaimed.push(ReclaimedName {
                    name: mounted.entry.name.clone(),
                    previous_owner: mounted.entry.owner,
                    reclaimed_at: current_epoch,
                });
            }
        }
    }

    reclaimed
}
```

### 5.3 Dispute Mechanism

Name disputes use the existing `Disputable` trait from `app-framework/src/dispute.rs`:

```rust
/// Name dispute: two parties claim the same name.
#[derive(Clone, Debug)]
pub struct NameClaim {
    /// The name being disputed.
    pub name: String,
    /// The claimant's preferred target for this name.
    pub proposed_target: PyanaUri,
    /// Evidence of prior use or legitimate claim.
    pub evidence: NameClaimEvidence,
}

#[derive(Clone, Debug)]
pub enum NameClaimEvidence {
    /// Timestamp of first registration (earlier = stronger).
    PriorRegistration { epoch: u64 },
    /// Governance vote in favor.
    GovernanceVote { proposal_id: [u8; 32], vote_weight: u64 },
    /// External attestation (e.g., DNS TXT record, ENS ownership).
    ExternalAttestation { attestation_type: String, proof: Vec<u8> },
    /// Activity proof (demonstrating active use of the name).
    ActivityProof { resolutions_last_epoch: u64 },
}

/// Implement Disputable for name conflicts.
impl Disputable for NameDirectory {
    type Claim = NameClaim;
    type Evidence = NameClaimEvidence;
    type Error = NameError;

    fn submit_claim(&mut self, claim: NameClaim) -> Result<SettlementId, NameError> {
        // Freeze the name (status -> Disputed), start dispute window.
        // ...
    }

    fn challenge(
        &mut self,
        settlement_id: SettlementId,
        challenger: CellId,
        evidence: NameClaimEvidence,
        challenger_stake: u64,
    ) -> Result<DisputeId, NameError> {
        // Accept challenge, lock stake.
        // Resolution by governance vote or automated rule.
        // ...
    }
}
```

---

## 6. Reverse Resolution

Given a `PyanaUri` or `CellId`, find what names point to it.

### 6.1 Reverse Index

```rust
/// Reverse name index: CellId → set of names pointing to it.
/// Maintained as a secondary index alongside the Registry.
#[derive(Clone, Debug, Default)]
pub struct ReverseNameIndex {
    /// Maps cell_id (from sturdy_ref) → set of (directory_uri, name) pairs.
    index: HashMap<[u8; 32], Vec<ReverseEntry>>,
}

#[derive(Clone, Debug)]
pub struct ReverseEntry {
    /// The name that points to this cell.
    pub name: String,
    /// Which directory this name lives in.
    pub directory: PyanaUri,
    /// Name category (petname/edge/proposed).
    pub category: NameCategory,
    /// Version of the name entry.
    pub version: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameCategory {
    RegisteredName,
    SubDelegated,
}

impl ReverseNameIndex {
    /// Look up all names for a given cell.
    pub fn whois(&self, cell_id: &[u8; 32]) -> Vec<&ReverseEntry> {
        self.index.get(cell_id)
            .map(|entries| entries.iter().collect())
            .unwrap_or_default()
    }

    /// Update index when a name is registered/updated.
    pub fn on_mount(&mut self, cell_id: [u8; 32], entry: ReverseEntry) {
        self.index.entry(cell_id).or_default().push(entry);
    }

    /// Update index when a name is removed.
    pub fn on_unmount(&mut self, cell_id: [u8; 32], name: &str, directory: &PyanaUri) {
        if let Some(entries) = self.index.get_mut(&cell_id) {
            entries.retain(|e| !(e.name == name && &e.directory == directory));
        }
    }
}
```

### 6.2 Wallet Integration

```rust
impl AgentWallet {
    /// Reverse lookup: what names point to this cell?
    ///
    /// Checks local petnames first, then queries federation directory.
    pub async fn whois(&self, target: &PyanaUri) -> Result<Vec<ResolvedName>, NameError> {
        let mut results = Vec::new();

        // 1. Check local petnames.
        for entry in self.petname_db.reverse_lookup(&target.cell_id) {
            results.push(ResolvedName {
                target: target.clone(),
                provenance: NameProvenance::LocalPetname,
                confidence: 1.0,
            });
        }

        // 2. Query federation directory's reverse index.
        let federation_results = self
            .query_reverse_index(target)
            .await?;
        results.extend(federation_results);

        Ok(results)
    }
}
```

---

## 7. SDK Integration

### 7.1 Wallet API Surface

```rust
impl AgentWallet {
    // =========================================================================
    // Petname Management (local, no network)
    // =========================================================================

    /// Assign a local petname to a sturdy ref.
    ///
    /// This is YOUR name for this thing. It never leaves your device.
    /// Overwrites any existing petname with the same label.
    pub fn set_petname(&mut self, label: &str, target: PyanaUri) -> Result<(), NameError> {
        validate_name_segment(label)?;
        self.petname_db.insert(label, NameEntry::Petname {
            label: label.to_string(),
            target,
            assigned_at: current_epoch(),
            notes: None,
        });
        Ok(())
    }

    /// Remove a local petname.
    pub fn remove_petname(&mut self, label: &str) -> Result<(), NameError> {
        self.petname_db.remove(label)
            .ok_or(NameError::NotFound(label.to_string()))?;
        Ok(())
    }

    /// List all local petnames.
    pub fn list_petnames(&self) -> Vec<&NameEntry> {
        self.petname_db.list_all()
    }

    // =========================================================================
    // Resolution (may involve network)
    // =========================================================================

    /// Resolve a name to a sturdy ref.
    ///
    /// Priority: petname > edge name > proposed name > hierarchical > error.
    pub async fn resolve(&self, name: &str) -> Result<ResolvedName, NameError>;

    /// Resolve with explicit provenance requirements.
    ///
    /// Use when you need to know WHERE a name came from (e.g., UI displaying
    /// trust indicators).
    pub async fn resolve_with_provenance(
        &self,
        name: &str,
        accept: &[NameProvenance],
    ) -> Result<ResolvedName, NameError>;

    // =========================================================================
    // Registration (network, governance)
    // =========================================================================

    /// Register a name in the home federation's directory.
    ///
    /// This mounts an entry in the governed namespace. May require:
    /// - Computron payment (from wallet's quota)
    /// - Governance vote (if name is contested or premium)
    /// - Member-level authorization
    ///
    /// Returns the mount receipt and the name's management capability.
    pub async fn register_name(
        &mut self,
        name: &str,
        target: &PyanaUri,
        rental_epochs: u64,
    ) -> Result<NameRegistrationReceipt, NameError> {
        validate_name_segment(name)?;

        // Calculate rent cost.
        let cost = self.name_policy.calculate_rent(name, rental_epochs);

        // Charge from wallet's quota.
        self.quota.charge(cost)?;

        // Mount in the federation's name directory.
        let entry = ServiceEntry {
            name: name.to_string(),
            kind: ServiceKind::Custom("name".to_string()),
            sturdy_ref: target.to_uri_string(),
            owner: self.public_key_bytes(),
            version: 0,
            tags: vec!["name".into()],
            description: format!("Name registration: {name}"),
            registered_at: current_epoch(),
            expires_at: Some(current_epoch() + rental_epochs),
            health_endpoint: None,
        };

        let receipt = self.federation_client
            .mount_name(name, entry)
            .await?;

        Ok(receipt)
    }

    /// Register a sub-name under a name you own (no governance vote needed).
    ///
    /// Requires: you own the parent name AND it has DelegationAuthority::SubPrefix.
    pub async fn register_subname(
        &mut self,
        parent_name: &str,
        child_label: &str,
        target: &PyanaUri,
    ) -> Result<NameRegistrationReceipt, NameError>;

    /// Renew an existing name registration (extend its rental period).
    pub async fn renew_name(
        &mut self,
        name: &str,
        additional_epochs: u64,
    ) -> Result<(), NameError>;

    /// Transfer name ownership to another party.
    /// Sends the name management capability to the recipient.
    pub async fn transfer_name(
        &mut self,
        name: &str,
        recipient: &PyanaUri,
    ) -> Result<(), NameError>;

    // =========================================================================
    // Reverse Lookup
    // =========================================================================

    /// Given a sturdy ref, find all names pointing to it.
    ///
    /// Checks local petnames first, then federation directory's reverse index.
    pub async fn whois(&self, target: &PyanaUri) -> Result<Vec<WhoisResult>, NameError>;

    // =========================================================================
    // Edge Name Management
    // =========================================================================

    /// Set your own edge name (what others see when they look you up).
    /// Stored in your profile cell, visible to anyone who has your sturdy ref.
    pub async fn set_edge_name(&mut self, name: &str) -> Result<(), NameError>;

    /// Refresh edge names from connected contacts.
    /// Fetches each contact's profile cell and updates the edge name cache.
    pub async fn refresh_edge_names(&mut self) -> Result<usize, NameError>;
}
```

### 7.2 SDK Types

```rust
/// Receipt from a successful name registration.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameRegistrationReceipt {
    /// The registered name.
    pub name: String,
    /// The sturdy ref it points to.
    pub target: PyanaUri,
    /// The management capability URI (used to update/transfer/delegate).
    pub management_cap: PyanaUri,
    /// Cost charged in computrons.
    pub cost_computrons: u64,
    /// Epoch at which this registration expires.
    pub expires_at: u64,
    /// Federation block height of registration.
    pub registered_at_height: u64,
}

/// Result from a whois (reverse) lookup.
#[derive(Clone, Debug)]
pub struct WhoisResult {
    /// The name that points to the queried target.
    pub name: String,
    /// Which category this name belongs to.
    pub provenance: NameProvenance,
    /// The directory the name lives in (if not a local petname).
    pub directory: Option<PyanaUri>,
    /// Registration epoch.
    pub registered_at: u64,
    /// Expiry epoch (None = permanent petname).
    pub expires_at: Option<u64>,
}

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
```

---

## 8. Cross-Federation Resolution

### 8.1 Federation Name Registration

Each federation registers its name directory in a shared meta-directory:

```rust
/// Cross-federation name resolution flow.
///
/// Precondition: both federations have registered their name directories
/// in a shared meta-directory (or in each other's meta-directories via
/// mutual introduction).
///
/// Resolution of "bob.federation-b.pyana" from federation A:
///
/// 1. A's wallet queries A's meta-directory for "federation-b"
/// 2. Meta-directory returns SturdyRef to B's name directory
/// 3. Wallet enlivens B's directory ref (CapTP session to B)
/// 4. Wallet queries B's directory for "bob"
/// 5. B's directory returns SturdyRef to bob's cell
/// 6. Wallet enlivens bob's sturdy ref (already has CapTP session to B)
```

### 8.2 Meta-Directory as Root

```rust
/// The root meta-directory structure for cross-federation resolution.
///
/// In production this would be a well-known cell replicated across
/// multiple federations (similar to DNS root servers). In practice,
/// each federation maintains a partial view and syncs via gossip.
///
/// Builds directly on rbg/src/directory.rs MetaDirectory.
pub struct FederationRegistry {
    /// The underlying meta-directory.
    meta: MetaDirectory,
    /// Bootstrap entries (well-known federations).
    bootstrap: Vec<(String, PyanaUri)>,
}

impl FederationRegistry {
    /// Register a federation's name directory.
    ///
    /// Requires: governance approval (this is a root-level registration).
    pub fn register_federation(
        &mut self,
        caller: MemberId,
        federation_name: &str,
        name_directory_ref: SturdyRef,
        description: Option<String>,
        current_height: u64,
    ) -> Result<Version, DirectoryError> {
        self.meta.register_directory(
            caller,
            federation_name,
            name_directory_ref,
            description,
            current_height,
        )
    }

    /// Resolve a federation name to its directory's sturdy ref.
    pub fn resolve_federation(
        &self,
        caller: MemberId,
        federation_name: &str,
    ) -> Result<&DirectoryEntry, DirectoryError> {
        self.meta.lookup(caller, federation_name)
    }
}
```

### 8.3 Cross-Federation Name Entry

```rust
/// A name entry that points across federation boundaries.
///
/// When a federation directory contains an entry whose sturdy_ref points
/// to a cell on a DIFFERENT federation, resolution requires a cross-federation
/// CapTP session. The resolver handles this transparently.
///
/// Example: federation-a's directory has:
///   "bob" → pyana://<federation-b-id>/<bob-cell-id>/<swiss>
///
/// Resolving "bob.federation-a.pyana":
///   1. Query federation-a's directory for "bob"
///   2. Get back a PyanaUri with federation_id = federation-b
///   3. Enliven requires connecting to federation-b (cross-fed CapTP)
///   4. Present swiss number to federation-b's node
///   5. Receive live reference to bob's cell
```

### 8.4 Caching and TTL

```rust
/// Cross-federation resolution cache.
///
/// Hierarchical lookups are expensive (multiple network hops).
/// Cache resolved names with a TTL derived from the directory entry's expiry.
#[derive(Clone, Debug)]
pub struct ResolutionCache {
    entries: HashMap<String, CachedResolution>,
    max_entries: usize,
}

#[derive(Clone, Debug)]
pub struct CachedResolution {
    pub result: ResolvedName,
    pub cached_at: u64,
    pub ttl_epochs: u64,
}

impl ResolutionCache {
    pub fn lookup(&self, name: &str, current_epoch: u64) -> Option<&ResolvedName> {
        self.entries.get(name).and_then(|cached| {
            if current_epoch < cached.cached_at + cached.ttl_epochs {
                Some(&cached.result)
            } else {
                None
            }
        })
    }
}
```

---

## 9. Protocol: Name Resolution as a Turn Effect

### 9.1 New Effect Variant

```rust
/// Extension to the Effect enum for name resolution.
/// Lives alongside existing effects in turn/src/lib.rs.
pub enum Effect {
    // ... existing effects ...

    /// Resolve a name to a sturdy ref within the current turn.
    ///
    /// This is a READ effect — it queries but does not mutate.
    /// The resolved URI is bound into the turn's output for use
    /// by subsequent effects in the same turn.
    ResolveName {
        /// The name to resolve (may be hierarchical).
        name: String,
        /// Which resolution sources to accept.
        accept_provenance: Vec<NameProvenance>,
    },

    /// Register a name in the federation's directory.
    ///
    /// This is a WRITE effect — it mutates the name directory.
    /// Requires sufficient computron balance and authorization.
    RegisterName {
        /// The name to register.
        name: String,
        /// What the name should point to.
        target: PyanaUri,
        /// How many epochs to prepay rent.
        rental_epochs: u64,
        /// QuotaId to charge rent from.
        quota_id: QuotaId,
    },

    /// Transfer ownership of a registered name.
    TransferName {
        /// The name to transfer.
        name: String,
        /// The new owner's public key.
        new_owner: [u8; 32],
    },

    /// Renew a name registration (extend rental period).
    RenewName {
        name: String,
        additional_epochs: u64,
        quota_id: QuotaId,
    },
}
```

---

## 10. Composition with Existing Infrastructure

### 10.1 Building Blocks Map

| Need | Existing Building Block | Location |
|------|------------------------|----------|
| Name storage | `Registry::mount()` (CAS, versioned) | `apps/governed-namespace/src/registry.rs` |
| Access control | DFA router + `AuthLevel` | `apps/governed-namespace/src/namespace.rs` |
| Hierarchical directories | `DirectoryCell` + `MetaDirectory` | `rbg/src/directory.rs` |
| Capability references | `PyanaUri` + `SwissTable` | `captp/src/uri.rs`, `captp/src/sturdy.rs` |
| Rent/cost model | `MeteringPolicy` + `QuotaCell` | `storage/src/metering.rs`, `storage/src/quota.rs` |
| Governance | `GovernanceEngine` (voting) | `apps/governed-namespace/src/governance.rs` |
| Dispute resolution | `Disputable` trait | `app-framework/src/dispute.rs` |
| Cross-federation comms | CapTP sessions + wire protocol | `captp/`, `wire/` |
| Wallet state | `AgentWallet` | `sdk/src/wallet.rs` |
| Discovery | `discover(tags)` + scoped intent pools | `registry.rs`, `rbg/src/directory.rs` |
| GC/expiry | `gc_expired()` on DirectoryCell | `rbg/src/directory.rs` |

### 10.2 What Needs to Be Built (New Code)

1. **`sdk/src/petnames.rs`** — Local petname database, edge name cache, resolution algorithm. ~300 lines.

2. **`sdk/src/name_resolver.rs`** — Hierarchical resolution, cross-federation traversal, caching. ~400 lines.

3. **`apps/governed-namespace/src/names.rs`** — Name-specific extensions to Registry: rental policy, sub-delegation authority, reverse index. ~500 lines.

4. **`turn/src/effects/name.rs`** — `ResolveName`, `RegisterName`, `TransferName`, `RenewName` effect implementations. ~200 lines.

5. **Extension to `rbg/src/directory.rs`** — Add `NameCategory` to entry metadata, reverse index maintenance hooks. ~100 lines.

### 10.3 What Does NOT Need to Be Built

- Storage/persistence for name entries: use existing `Registry` (already has BTreeMap + CAS)
- Access control: use existing DFA router (already classifies paths by auth level)
- Governance for name disputes: use existing `GovernanceEngine` + `Disputable` trait
- Cross-federation communication: use existing CapTP sessions
- Sturdy ref management: use existing `SwissTable`
- Cost metering: use existing `QuotaCell` + `MeteringPolicy`
- Directory hierarchy: use existing `MetaDirectory`

---

## 11. Example Flows

### 11.1 Alice Registers a Name

```
1. Alice calls wallet.register_name("alice", her_cell_uri, 100 /*epochs*/)
2. Wallet calculates rent: 100 epochs * (100 base + 200*0 premium) = 10,000 computrons
3. Wallet charges from Alice's QuotaCell
4. Wallet submits Effect::RegisterName to federation
5. Federation executor mounts "/names/alice" in governed-namespace Registry
6. Federation grants DelegationAuthority::SubPrefix { prefix: "/names/alice/" }
7. Wallet stores management capability URI locally
8. Alice can now be found as "alice.my-federation.pyana"
```

### 11.2 Bob Resolves "alice.my-federation.pyana"

```
1. Bob's wallet checks petname DB for "alice.my-federation.pyana" — miss
2. Bob's wallet checks edge name cache — miss
3. Name contains dots → hierarchical resolution
4. Split: ["pyana", "my-federation", "alice"]
5. Query meta-directory for "my-federation" → get SturdyRef to my-federation's name dir
6. Enliven name dir (CapTP session, may already exist)
7. Query name dir for "alice" → get alice's SturdyRef
8. Return ResolvedName { target: alice_uri, provenance: FederationDirectory }
9. Bob's wallet caches the result with TTL from the directory entry
```

### 11.3 Alice Creates Sub-Name

```
1. Alice calls wallet.register_subname("alice", "oracle", oracle_service_uri)
2. Wallet verifies Alice owns "alice" (has management cap)
3. Wallet submits Effect::RegisterName for "alice/oracle" (sub-delegation path)
4. Federation verifies DelegationAuthority on parent — authorized without vote
5. Mounts "/names/alice/oracle" in Registry
6. Resolvable as "oracle.alice.my-federation.pyana"
```

### 11.4 Name Dispute

```
1. Both Alice and Mallory try to register "popular-name"
2. Alice registers first (epoch 100)
3. Mallory submits NameClaim with GovernanceVote evidence
4. Name status transitions to Disputed
5. Governance engine opens a vote among federation members
6. If Alice wins: name stays with Alice, Mallory's stake is slashed
7. If Mallory wins: name transfers to Mallory, Alice gets grace period to update references
```

---

## 12. Security Properties

1. **Petnames cannot be overridden remotely.** Your local name for something is YOURS. No governance vote, no community consensus, no protocol message can change what "alice" means in YOUR wallet.

2. **Names are capabilities.** You cannot register a name you don't have authority for. The DFA router enforces path-based access control. Sub-delegation is explicit (must hold parent).

3. **Swiss numbers protect privacy.** Resolving a name does not reveal WHO is resolving it. The resolver presents their swiss number to the target, but the directory does not learn the resolver's identity.

4. **Rent prevents squatting.** Names without ongoing funding expire. This creates a market equilibrium where names are held only by those who value them.

5. **Disputes have stake.** Challenging a name requires locking computrons. Frivolous challenges cost the challenger.

6. **Cross-federation resolution is capability-bounded.** You can only resolve names in federations you have a meta-directory entry for. The meta-directory IS a capability — holding it = being able to discover that federation.
