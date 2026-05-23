# Vat Migration Design: Cell Teleportation Between Federations

## Summary

This document specifies the protocols for moving cells between federations (vats),
splitting one federation into two, merging two into one, and fluid trust-boundary
transitions. Each operation is decomposed into atomic protocol steps with concrete
message flows, proof requirements, and references to existing code.

---

## 1. Cell Migration (Single Cell Teleportation)

A single cell moves from federation S (source) to federation T (target). The cell's
identity (CellId, swiss number) is preserved; its federation address changes.

### 1.1 Protocol Steps

```
Phase 1: FREEZE (Source)
  S.1  Source federation receives MigrationRequest(cell_id, target_federation)
  S.2  Source marks cell as FROZEN in its ledger (reject all new turns for this cell)
  S.3  Source increments cell nonce to create a "migration nonce" (prevents replay)
  S.4  Source waits for all pending turns on this cell to either commit or abort

Phase 2: EXPORT (Source -> Target)
  S.5  Source builds CellExportBundle:
         - Full Cell struct (state, capabilities, permissions, program, vk)
         - IVC proof: accumulated proof covering all state transitions since genesis
         - Ledger MembershipProof (cell exists in source's Merkle root)
         - Constitution snapshot (source federation's current constitution)
         - ExportGcManager state: list of (FederationId, ref_count) holders
         - Swiss table entries for this cell (all active sturdy refs)
  S.6  Source signs the bundle with its federation key
  S.7  Bundle is transmitted to target (via CapTP session or out-of-band)

Phase 3: VALIDATE (Target)
  T.1  Target verifies source's federation signature on bundle
  T.2  Target verifies MembershipProof against source's known state root
  T.3  Target verifies IVC proof:
         - verify_ivc(&ivc_proof, Some(expected_initial_root))
         - OR verify_validated_ivc(&validated_proof) for full fold-validity
  T.4  Target checks cell nonce is strictly greater than any previously seen
  T.5  Target checks that source constitution was valid at export time
  T.6  Target inserts cell into its own ledger (assigns local storage)
  T.7  Target registers all swiss entries into its local SwissTable
  T.8  Target creates a MigrationReceipt (signed acknowledgment)

Phase 4: COMMIT (Bilateral)
  C.1  Target sends MigrationReceipt to source
  C.2  Source verifies target's receipt signature
  C.3  Source deletes cell from its ledger (GC sweep)
  C.4  Source emits RedirectNotice(cell_id, new_federation=T) to all holders
  C.5  Source revokes all local swiss entries for this cell

Phase 5: RE-ROUTE (Third Parties)
  R.1  Each holder receives RedirectNotice
  R.2  Holder updates its ImportGcManager: (old_federation, cell_id) -> (new_federation, cell_id)
  R.3  Holder opens CapTP session with target (if not already connected)
  R.4  Holder enlivens its existing swiss number at the target
       (swiss is preserved, so this works without re-introduction)
```

### 1.2 Proofs Required

| Proof | Statement | Generator | Verifier |
|-------|-----------|-----------|----------|
| IVC proof | "This cell's state followed valid transitions from genesis to current" | Source (via `circuit/src/ivc.rs::prove_ivc`) | Target |
| Membership proof | "Cell X is a leaf in source's ledger Merkle tree at root R" | Source (via `cell/src/ledger.rs::MembershipProof`) | Target |
| Constitution proof | "Source federation had N participants with threshold T at height H" | Source (via `blocklace/src/constitution.rs::Constitution`) | Target |
| Migration receipt | "Target accepted cell X at height H'" | Target | Source |

**STARK statements needed:**
1. **StateTransitionAir** (`circuit/src/ivc.rs`): Proves the Poseidon2 hash chain
   from initial_root through all intermediate states to current state root.
2. **EffectVmAir** (`circuit/src/effect_vm.rs`): Each turn's effects were valid
   (balance conservation, nonce increment, capability constraints).
3. **MerkleProof STARK** (`circuit/src/dsl/membership.rs`): Cell membership in
   source's ledger tree.

### 1.3 Communication Overhead

- **CellExportBundle**: ~2-5 KiB (cell state) + ~48 KiB (STARK proof) + ~1 KiB (membership proof) + ~2 KiB (constitution) + variable (swiss entries)
- **Total messages**: 4 (request, bundle, receipt, redirect broadcast)
- **Redirect broadcast**: 1 message per holder (from ExportGcManager.holders)
- **Latency**: 2 round trips (source->target->source) + broadcast

### 1.4 Atomicity

The migration can be observed in three states:
1. **Pre-migration**: Cell lives at source, all refs point to source.
2. **In-flight** (between S.2 and C.3): Cell is FROZEN at source, not yet live at target.
   During this window, the cell is unreachable (calls to it fail with "cell migrating").
3. **Post-migration**: Cell lives at target, refs re-routed.

**Safety**: A cell cannot be double-spent during migration because:
- The FREEZE prevents new turns at source (S.2)
- The target only accepts the cell after validating the full IVC proof (T.3)
- The source only deletes after receiving target's signed receipt (C.3)

**Liveness concern**: If target goes offline after receiving the bundle but before
sending the receipt, the cell is in limbo. Solution: timeout at source; after
T_MIGRATION_TIMEOUT waves without a receipt, source un-freezes and the migration
is considered failed. The target must check for a "migration cancelled" message
before accepting.

### 1.5 Third-Party References

Third parties hold sturdy refs (swiss numbers) or live CapTP imports:

- **Swiss numbers are preserved**: The same 32-byte swiss is registered at the
  target's SwissTable. Holders can enliven at the new location without re-introduction.
- **CapTP imports**: The holder's `ImportGcManager` is updated via RedirectNotice.
  The holder sends a DropRef to the source and opens a new import at the target.
- **No holder action required during migration**: The RedirectNotice is informational.
  If a holder hasn't processed it yet and sends a message to the old location,
  the source responds with a "moved permanently" error containing the new federation.

### 1.6 Privacy

- **Target learns full history**: The IVC proof's `initial_root` and `final_root` are
  public inputs. The proof itself does not reveal intermediate states (zero-knowledge),
  but the target receives the full `CellState` to host the cell.
- **Private migration** (enhancement): Instead of exporting full state, export only
  the state commitment + IVC proof. The cell runs in `CellMode::Sovereign` at the
  target, where the target only stores the 32-byte commitment. The cell owner provides
  state with each turn. This uses `cell/src/cell.rs::CellMode::Sovereign`.
- **Third parties do NOT learn migration happened** if using stealth addresses for
  the redirect channel.

---

## 2. Vat Splitting (One Federation Becomes Two)

A subset of participants form a new federation, taking some cells with them.

### 2.1 Protocol Steps

```
Phase 1: PROPOSAL (Constitutional)
  SP.1  A participant proposes SplitProposal:
          - new_federation_participants: Vec<[u8; 32]>
          - cell_partition: HashMap<CellId, DestinationFederation>
          - split_height: u64 (the height at which the split takes effect)
  SP.2  Proposal is voted on per constitution.rs rules (threshold votes)
  SP.3  Both old and new participant sets must approve (H-rule applies)

Phase 2: PARTITION (At split_height)
  SP.4  All participants stop accepting new turns at split_height
  SP.5  Each participant builds a partition proof:
          - Full ledger Merkle tree at split_height
          - For each cell going to the new federation: MembershipProof
          - Aggregate IVC proof covering all migrating cells
  SP.6  New federation initializes with:
          - Constitution: new_federation_participants, timeout_waves
          - Ledger: subset of cells from cell_partition
          - History: share the full blocklace up to split_height
  SP.7  Old federation continues with:
          - Constitution: remaining participants (updated threshold)
          - Ledger: cells NOT in cell_partition

Phase 3: REFERENCE TRANSFORM
  SP.8  For each cell staying in old federation that has c-list refs to
        cells going to new federation:
          - Near ref becomes far ref (requires CapTP session between old and new)
          - Old federation exports the departing cell via SwissTable
          - Staying cell's CapabilityRef gets annotated with federation_hint
  SP.9  For each cell going to new federation that has c-list refs to
        cells staying:
          - Same transform in reverse
  SP.10 Cross-federation CapTP sessions are established between old and new

Phase 4: NOTIFY (Third Parties)
  SP.11 For each cell that moved: RedirectNotice broadcast (same as migration)
  SP.12 For cross-federation refs: ExportGcManager entries are created
```

### 2.2 Proofs Required

| Proof | Statement |
|-------|-----------|
| Split proof (STARK) | "At height H, the ledger contained cells {A,B,C,...} which departed to federation F'" |
| Partition membership | "Each departing cell was a valid member of the original ledger at split_height" |
| Constitution validity | "The split was approved by threshold votes from both old and new participant sets" |
| History binding | "New federation's genesis state is a subset of old federation's state at split_height" |

**New STARK needed**: `SplitAir` -- proves that a set of cells with their state
roots, when removed from one Merkle tree (the old ledger) and inserted into another
(the new ledger), produce the claimed old and new roots. This is essentially a batch
membership proof + batch insertion proof.

### 2.3 Communication Overhead

- **Intra-federation**: O(n_participants * n_cells) for partition proof distribution
- **Cross-references**: 2 messages per cross-reference (export + import)
- **Third-party notifications**: 1 per external holder of any migrating cell

### 2.4 Atomicity

The split is atomic at `split_height`. Before split_height, one federation exists.
After split_height, two exist. The blocklace's finality mechanism ensures all honest
participants agree on the same split_height.

**Cannot be observed half-done** because:
- Finality at split_height is a prerequisite
- Both federations start from the same finalized state
- No turns are processed between "finality at split_height" and "split complete"

### 2.5 History

Both federations keep the full blocklace history up to split_height. After the split:
- Old federation appends to the existing blocklace
- New federation starts a new blocklace (genesis references the split point)
- The "split proof" is the genesis justification for the new federation

---

## 3. Vat Merging (Two Federations Become One)

Federations A and B merge into federation C (or B absorbs into A).

### 3.1 Protocol Steps

```
Phase 1: AGREEMENT
  M.1  Both constitutions approve MergeProposal (threshold votes in each)
  M.2  Agree on merge_height (height at which both stop independent operation)
  M.3  Agree on merged constitution (participant union, new threshold)

Phase 2: STATE MERGE (At merge_height)
  M.4  Both federations stop at merge_height
  M.5  Build merged ledger:
        - All cells from A + all cells from B
        - CellIds are globally unique (content-addressed), so no collisions
        - Combined Merkle tree (new root = hash of both subtrees)
  M.6  Collapse CapTP sessions between A and B:
        - For each cross-ref that was a far ref (via CapTP): convert to near ref
        - For each cell: remove federation_hint from CapabilityRefs to merged cells
        - ExportGcManager entries between A<->B are deleted (no longer cross-fed)
        - ImportGcManager entries between A<->B are deleted
  M.7  Merged federation C starts with:
        - Constitution: union of participants, recomputed threshold
        - Ledger: combined Merkle tree
        - History: both blocklaces up to merge_height + merge proof

Phase 3: NOTIFY
  M.8  All external parties with refs to cells in A or B receive:
        MergeNotice(old_federation=A|B, new_federation=C)
  M.9  External holders update their federation routing
```

### 3.2 Proofs Required

| Proof | Statement |
|-------|-----------|
| Merge authorization | "Both constitutions approved the merge at heights H_A and H_B" |
| State combination | "Merged ledger root R_C is the combination of R_A and R_B with no conflicts" |
| Session collapse | "All A<->B CapTP sessions were fully resolved (no pending promises)" |

**STARK statement**: The merge proof shows that the new Merkle root is a valid
combination of two subtrees. Since CellIds are content-addressed and globally unique,
there are no conflicts (same CellId in both would mean same cell -- which is a
protocol error caught during validation).

### 3.3 Atomicity

The merge is atomic at merge_height. Both federations must reach finality at their
respective merge_heights before the merge completes.

**Liveness concern**: If one federation finalizes at merge_height but the other
doesn't (e.g., it's stuck), the merge stalls. Solution: merge_height includes a
timeout; if not finalized within T_MERGE_TIMEOUT, the merge is aborted.

### 3.4 CapTP Session Collapse

When A and B merge, their bilateral CapTP sessions become meaningless:

```rust
// Existing code path (captp/src/session.rs)
// Before merge: cell X in A holds import of cell Y in B
session.imports: { Y -> ImportEntry { remote_cell_id: Y, live: true } }

// After merge: Y is now local to C, no session needed
// The import entry is converted to a local CapabilityRef in X's c-list
```

Steps:
1. For each `ImportEntry` in A's sessions with B: convert to local `CapabilityRef`
2. For each `ExportEntry` in A's GC manager for B: delete (B is now local)
3. Delete the `CapSession` between A and B entirely
4. Any pending promises (`PromiseState::Pending`) must be resolved or broken first

---

## 4. Fluid Trust Boundaries

A cell transitions between trust levels without changing identity.

### 4.1 Trust Levels

| Level | Description | Federation Size | Execution Model |
|-------|-------------|-----------------|-----------------|
| Sovereign | Your device only | n=1 | Self-execute, self-finalize |
| Optimistic | Small group, one executor | n=5, threshold=4 | Single executor + fraud proof window |
| Full Replication | Large group, all execute | n=20, threshold=14 | Every node executes every turn |

### 4.2 Upgrade: Sovereign -> Optimistic

```
U1.1  Cell owner proposes Join to an existing optimistic federation
U1.2  Existing federation votes to accept (threshold approval)
U1.3  Cell owner builds:
        - Full CellState export
        - IVC proof of all prior sovereign transitions
        - State commitment matches the sovereign history
U1.4  Federation validates IVC proof (target doesn't need to trust owner's self-reports)
U1.5  Cell is inserted into federation's ledger
U1.6  Owner's device keeps a local copy (for sovereign fallback)
U1.7  CapTP sessions updated: owner's n=1 federation becomes a participant in n=5
```

This is a **cell migration** (Section 1) where the source is an n=1 federation.

### 4.3 Upgrade: Optimistic -> Full Replication

```
U2.1  Federation governance votes to change execution model
U2.2  This is a constitutional amendment (AmendThreshold or custom proposal)
U2.3  All nodes begin executing all turns (no protocol change to the cell itself)
U2.4  The cell's state doesn't change -- only the federation's replication policy
```

This is purely a governance change (no cell movement). Uses existing
`constitution.rs::MembershipProposal::AmendThreshold`.

### 4.4 Downgrade: Full Replication -> Sovereign

```
D1.1  Owner proposes Leave from the federation (for their cells)
D1.2  Federation votes to approve departure
D1.3  Owner builds a CellExportBundle for each departing cell
D1.4  Each cell is migrated to the owner's n=1 federation (Section 1 protocol)
D1.5  Federation deletes the cells from its ledger
D1.6  Owner now operates sovereign (no consensus needed for turns)
```

This is a migration (Section 1) where the target is an n=1 federation.

### 4.5 Proofs for Trust Transitions

The critical insight: **the IVC proof compresses the cell's entire history**
regardless of what trust level it was under. A cell that was sovereign for 1000
turns, then optimistic for 500, then full-replication for 200, produces a single
IVC proof covering all 1700 turns.

```rust
// From circuit/src/ivc.rs -- the proof doesn't care about federation identity
pub struct IvcProof {
    pub initial_root: BabyBear,     // genesis
    pub final_root: BabyBear,       // current
    pub step_count: u32,            // total turns across all trust levels
    pub accumulated_hash: BabyBear, // binds entire history
    pub stark_proof: Option<StarkProof>,
}
```

---

## 5. Missing Building Blocks

### 5.1 Must Build

| Component | Description | Location |
|-----------|-------------|----------|
| `CellExportBundle` | Serializable struct containing all migration data | New: `captp/src/migration.rs` |
| `MigrationRequest` / `MigrationReceipt` | Wire messages for the migration protocol | New: `captp/src/migration.rs` |
| `RedirectNotice` | Broadcast message notifying holders of relocation | New: `captp/src/migration.rs` |
| `FreezeGuard` | Mechanism in TurnExecutor to reject turns on frozen cells | Extend: `turn/src/executor.rs` |
| `SplitAir` | STARK proving correct ledger partition | New: `circuit/src/split_air.rs` |
| `MergeAir` | STARK proving correct ledger combination | New: `circuit/src/merge_air.rs` |
| Migration-aware routing | Node routing table that handles "moved permanently" | Extend: `turn/src/routing.rs` |
| Federation-level IVC | IVC proof that covers the entire cell lifetime across federations | Extend: `circuit/src/ivc.rs` |

### 5.2 Exists But Needs Extension

| Component | What's Missing |
|-----------|---------------|
| `captp/src/gc.rs::ExportGcManager` | Bulk transfer of holder lists to new federation |
| `captp/src/handoff.rs::HandoffCertificate` | Migration-specific variant (MigrationHandoff) |
| `captp/src/session.rs::CapSession` | Session collapse operation for merges |
| `blocklace/src/constitution.rs` | SplitProposal and MergeProposal variants |
| `cell/src/cell.rs::Cell` | Serializable CellExport format with IVC proof attachment |
| `captp/src/sturdy.rs::SwissTable` | Bulk export/import of entries for migration |
| `turn/src/executor.rs::TurnExecutor` | Frozen cell detection, migration-in-progress state |
| `circuit/src/effect_vm.rs` | New effect type: `CellMigrate` (effect type 18+) |

### 5.3 Design Decisions Still Open

1. **Should the cell's CellId change after migration?** Currently CellId is
   `BLAKE3(public_key || token_id)` -- it's federation-independent. This means
   CellId can stay the same across federations. The swiss number (durable ref) also
   stays the same. Only the federation routing changes.

2. **Should migration require the cell owner's signature?** For hosted cells, the
   federation controls the cell. For sovereign cells, the owner must sign the
   migration request. Proposal: always require owner signature (even for hosted cells)
   to prevent hostile migration.

3. **Should the IVC proof cover cross-federation history?** Currently the IVC proves
   a chain of fold steps (capability attenuation). For migration, we need a broader
   proof: "this cell's state is the result of valid turns, regardless of which
   federation executed them." This may require a new AIR that proves state transitions
   (EffectVmAir) accumulated via IVC (StateTransitionAir) -- composing the two.

4. **Concurrent migration and messages**: What happens if a message is in-flight
   to a cell that just started migrating? The source must buffer (store-and-forward)
   messages arriving during the freeze window and include them in the export bundle,
   OR reject them with "cell migrating, retry at new location."

---

## 6. Concrete Data Structures (Proposed)

```rust
// captp/src/migration.rs (new file)

/// A request to migrate a cell from this federation to another.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MigrationRequest {
    /// The cell being migrated.
    pub cell_id: CellId,
    /// The target federation.
    pub target_federation: FederationId,
    /// Owner's signature authorizing the migration.
    pub owner_signature: Signature,
    /// Requested migration height (source should freeze at this height).
    pub requested_height: u64,
}

/// The full export bundle for a migrating cell.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CellExportBundle {
    /// The cell in its current state.
    pub cell: Cell,
    /// IVC proof covering the cell's full state transition history.
    pub ivc_proof: IvcProof,
    /// Merkle membership proof in the source's ledger.
    pub membership_proof: MembershipProof,
    /// Source federation's constitution at export time.
    pub source_constitution: Constitution,
    /// The height at which the cell was frozen and exported.
    pub export_height: u64,
    /// All swiss table entries for this cell (sturdy refs that should work at target).
    pub swiss_entries: Vec<([u8; 32], SwissEntry)>,
    /// Who holds references to this cell (for redirect notification).
    pub holders: Vec<(FederationId, u64)>, // (federation, ref_count)
    /// Source federation's signature over the bundle.
    pub source_signature: Signature,
    /// Messages that arrived during the freeze window (store-and-forward).
    pub buffered_messages: Vec<QueuedMessage>,
}

/// Target's acknowledgment that it accepted the cell.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MigrationReceipt {
    /// The cell that was migrated.
    pub cell_id: CellId,
    /// The target federation's ID.
    pub target_federation: FederationId,
    /// Height at which the target accepted the cell.
    pub accepted_at: u64,
    /// Target's signature over (cell_id || target_federation || accepted_at).
    pub target_signature: Signature,
}

/// Notification sent to all holders that a cell has moved.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RedirectNotice {
    /// The cell that moved.
    pub cell_id: CellId,
    /// Where it moved from.
    pub old_federation: FederationId,
    /// Where it moved to.
    pub new_federation: FederationId,
    /// Proof that the migration happened (receipt from target).
    pub receipt: MigrationReceipt,
    /// Height at which the redirect takes effect.
    pub effective_height: u64,
}

/// Split proposal for constitutional vote.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SplitProposal {
    /// Participants forming the new federation.
    pub new_participants: Vec<[u8; 32]>,
    /// Cells going to the new federation.
    pub departing_cells: Vec<CellId>,
    /// Height at which the split takes effect.
    pub split_height: u64,
    /// New federation's timeout_waves setting.
    pub new_timeout_waves: u64,
}

/// Merge proposal for constitutional vote.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MergeProposal {
    /// The other federation we're merging with.
    pub other_federation: FederationId,
    /// The other federation's constitution (for participant union).
    pub other_constitution: Constitution,
    /// Height at which both federations stop.
    pub merge_height: u64,
    /// The merged constitution (must be agreed by both sides).
    pub merged_constitution: Constitution,
}
```

---

## 7. Message Flow Diagrams

### 7.1 Single Cell Migration

```
Owner          Source Fed         Target Fed         Holder
  |                |                  |                 |
  |--MigrateReq-->|                  |                 |
  |                |--FREEZE(cell)-->|                 |
  |                |   (reject turns)|                 |
  |                |                  |                 |
  |                |---ExportBundle-->|                 |
  |                |                  |--validate()    |
  |                |                  |--insert_cell() |
  |                |<--Receipt--------|                 |
  |                |                  |                 |
  |                |--delete_cell()   |                 |
  |                |                  |                 |
  |                |---RedirectNotice--+---------------->|
  |                |                  |                 |--update_routing()
  |                |                  |                 |--enliven_at_target()
```

### 7.2 Vat Split

```
Proposer     Federation (all nodes)      New Federation (subset)
  |                |                           |
  |--SplitProp--->|                           |
  |                |--vote--->                 |
  |                |--vote--->                 |
  |                |--vote---> (threshold)     |
  |                |                           |
  |                |===SPLIT_HEIGHT===         |
  |                |                           |
  |                |--partition_proof()        |
  |                |                           |
  |                |------genesis_bundle------>|
  |                |                           |--init_federation()
  |                |                           |--start_blocklace()
  |                |                           |
  |                |<====CapTP session========>|
  |                |  (for cross-references)   |
```

---

## 8. Security Analysis

### 8.1 Preventing Double-Spend During Migration

1. **Freeze window**: No turns accepted at source after freeze height
2. **Nonce continuity**: Target validates nonce >= export nonce; source can't
   execute a turn that would advance the nonce past what the target expects
3. **IVC binding**: The IVC proof commits to the exact state at export time;
   any divergent history would produce a different accumulated_hash

### 8.2 Preventing Unauthorized Migration

1. **Owner signature**: Migration requires the cell owner's Ed25519 signature
2. **Constitutional approval**: Source federation must approve the departure
   (via `MembershipProposal::Leave` or a new `CellDepartureProposal`)
3. **Target acceptance**: Target can refuse (e.g., cell too large, untrusted source)

### 8.3 Preventing History Forgery

1. **IVC proof**: The accumulated_hash in the IVC proof commits to every
   intermediate state root. Forging a different history requires breaking
   Poseidon2 preimage resistance (128-bit security).
2. **Validated IVC**: For stronger guarantees, use `prove_validated_ivc` which
   includes per-step Merkle membership STARKs proving each fold was valid.
3. **Source signature**: The export bundle is signed by the source federation.
   Combined with the IVC proof, this gives "federation attested this history."

### 8.4 Privacy Considerations

| Scenario | What Target Learns | What Third Parties Learn |
|----------|-------------------|------------------------|
| Normal migration | Full cell state + IVC public inputs | Only that cell moved (via redirect) |
| Private migration | Only state commitment (sovereign mode) | Only that cell moved |
| Stealth migration | Nothing (owner runs own node in target) | Nothing (no redirect) |

For maximum privacy, combine sovereign mode with stealth addresses
(`cell/src/stealth.rs::StealthAddress`): the cell migrates to a new federation
under a stealth address, and old references are broken rather than redirected.

### 8.5 Liveness Requirements

| Phase | Who Must Be Online |
|-------|--------------------|
| Freeze | Source federation (threshold participants) |
| Export | Source + Target (at least one target node) |
| Validate | Target federation (threshold participants) |
| Commit | Source + Target |
| Re-route | Holders (asynchronous -- store-and-forward works) |

**Key insight**: Holders do NOT need to be online simultaneously. The RedirectNotice
is delivered via store-and-forward (`captp/src/store_forward.rs`). When a holder
comes online later, it processes queued redirects.

---

## 9. Integration with Existing Code

### 9.1 TurnExecutor Changes (`turn/src/executor.rs`)

```rust
// New field in TurnExecutor:
pub frozen_cells: HashSet<CellId>,

// In execute_turn(), before processing:
if self.frozen_cells.contains(&action.target) {
    return Err(TurnError::CellFrozen { 
        cell_id: action.target,
        reason: FreezeReason::Migration,
    });
}
```

### 9.2 Effect VM Extension (`circuit/src/effect_vm.rs`)

New effect type (selector 18):
```rust
pub const MIGRATE_CELL: usize = 18;
// Params: [target_federation_hash_lo, target_federation_hash_hi, 
//          export_height, reserved, reserved, reserved, reserved, reserved]
// Constraint: balance_after == 0 (all balance transferred with cell)
//             nonce_after == nonce_before + 1
//             state_after == state_before (state preserved, not modified)
```

### 9.3 Constitution Extension (`blocklace/src/constitution.rs`)

```rust
// New proposal variants:
pub enum MembershipProposal {
    // ... existing variants ...
    /// Approve departure of cells from this federation.
    CellDeparture {
        cells: Vec<CellId>,
        destination: FederationId,
    },
    /// Approve absorption of cells from another federation.
    CellArrival {
        cells: Vec<CellId>,
        source: FederationId,
        source_proof: Vec<u8>, // serialized CellExportBundle
    },
    /// Constitutional fork (vat split).
    Split(SplitProposal),
    /// Constitutional merge.
    Merge(MergeProposal),
}
```

### 9.4 CapTP Session Collapse (for merges)

```rust
// New method on CapSession (captp/src/session.rs):
impl CapSession {
    /// Collapse this session: convert all imports to local refs,
    /// drop all exports (they become local), break pending promises.
    /// Used during federation merge when the peer becomes local.
    pub fn collapse(self) -> Vec<(CellId, AuthRequired)> {
        // Returns all imports as local capability grants
        self.imports.values()
            .filter(|i| i.live)
            .map(|i| (i.remote_cell_id, i.permissions.clone()))
            .collect()
    }
}
```

---

## 10. Implementation Priority

1. **Phase 1** (enables single-cell migration):
   - `CellExportBundle` struct + serialization
   - `FreezeGuard` in TurnExecutor
   - Migration-aware IVC proof generation (compose EffectVM + StateTransition)
   - `RedirectNotice` + routing table update
   - Swiss table bulk export/import

2. **Phase 2** (enables trust transitions):
   - Sovereign-to-federation migration (n=1 -> n=k)
   - Federation-to-sovereign migration (n=k -> n=1)
   - IVC proof that spans federation boundaries

3. **Phase 3** (enables splits and merges):
   - `SplitAir` circuit
   - `MergeAir` circuit
   - CapTP session collapse
   - Cross-reference transform (near <-> far)
   - Constitutional proposals for Split/Merge

Each phase builds on the previous. Phase 1 alone enables the most important use
case: a user moving their agent between federations as trust requirements change.
