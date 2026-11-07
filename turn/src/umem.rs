//! umem: THE EXECUTOR-STATE BRIDGE — the live executor's state as a view of the ONE
//! universal map, and the live executor's turn as a Blum memory-op trace.
//!
//! The universal-map rotation's long pole (`.docs-history-noclaude/UNIVERSAL-MAP-ROTATION.md` §2.3/§3:
//! "the 3-verb executor-state bridge: RecordKernelState → the ONE map"). This module is
//! the Rust half of the bridge whose Lean keystone is
//! `metatheory/Dregg2/Exec/UniversalBridge.lean` (`uproj` + the three
//! `*_is_memory_program` agreement theorems):
//!
//!  1. **THE PROJECTION** ([`project_executor_state`] / [`project_ledger`]): every cell
//!     field and executor side-table entry lands at a `(domain, collection, key) ↦ value`
//!     cell of the unified address space — the same five domains as
//!     `Dregg2/Crypto/UniversalMemory.lean`'s `Domain` enum (registers · heap · caps ·
//!     nullifiers · index), with the same wire codes as `DescriptorIR2.domainCode`.
//!
//!  2. **THE TRACE EMITTER** ([`emit_trace`]): for a turn executed by the live executor,
//!     the journal (the undo log that already records every forest mutation with its
//!     prior value, in execution order) is re-read as the turn's Blum WRITE trace —
//!     per-op `(kind, addr, val, prev_val, prev_serial)` rows under the memcheck
//!     discipline (`Dregg2/Crypto/MemoryChecking.lean`). The fold of the emitted trace
//!     over the pre-state projection MUST equal the post-state projection
//!     ([`fold`] — checked eagerly; the executable shadow of the Lean agreement
//!     theorems), and every journal-recorded prior value is cross-checked against the
//!     running fold (drift between the journal and the projection refuses loudly).
//!
//! Wiring: recursion-gated, exactly like the umem circuit leg — the witness is produced
//! only when `TurnExecutor::umem_witness_enabled` is set; the live proving path is
//! untouched (v1 stays the only prover on the wire).
//!
//! ## The projection table (Rust side)
//!
//! | executor state                          | `UKey` collection        | domain     |
//! |-----------------------------------------|--------------------------|------------|
//! | cell existence (ledger membership)      | `Exist`                  | heap       |
//! | `CellState.fields[0..16]`               | `Field` (slot < 16)      | heap       |
//! | `CellState.fields_map` (keys ≥ 16)      | `Field` (slot ≥ 16)      | heap       |
//! | `CellState.balance`                     | `Balance`                | heap       |
//! | `CellState.nonce`                       | `Nonce`                  | heap       |
//! | `CellState.proved_state`                | `ProvedState`            | heap       |
//! | `Cell.lifecycle` (incl. death cert)     | `Lifecycle`              | heap       |
//! | `Cell.mode`                             | `Mode`                   | heap       |
//! | `Cell.{public_key, token_id}`           | `Identity`               | heap       |
//! | `CellState.field_visibility[slot]`      | `FieldVisibility`        | heap       |
//! | `CellState.commitments[slot]`           | `FieldCommitment`        | heap       |
//! | `CellState.swiss_table_root`            | `SwissTableRoot`         | heap       |
//! | `CellState.refcount_table_root`         | `RefcountTableRoot`      | heap       |
//! | `CellState.system_roots[i]`             | `SystemRoot`             | heap       |
//! | `CellState.heap_map` entries            | `Heap`                   | heap       |
//! | sovereign commitments                   | `SovereignCommitment`    | heap       |
//! | `Cell.capabilities` (c-list slots)      | `CapSlot`                | caps       |
//! | `Cell.capabilities` revoked-slot ghosts | `CapTombstone`           | caps       |
//! | `Cell.delegate`                         | `Delegate`               | caps       |
//! | `Cell.delegation` (snapshot)            | `DelegationSnapshot`     | caps       |
//! | `CellState.delegation_epoch`            | `DelegationEpoch`        | caps       |
//! | `Cell.permissions`                      | `Permissions`            | caps       |
//! | `Cell.verification_key`                 | `VerificationKey`        | caps       |
//! | `Cell.program` (slot-caveat registry)   | `Program`                | caps       |
//! | `factory_registry.descriptors`          | `Factory`                | caps       |
//! | `note_nullifiers`                       | `NoteNullifier`          | nullifiers |
//! | `bridged_nullifiers`                    | `BridgedNullifier`       | nullifiers |
//! | receipt log position (caller-supplied)  | `Receipt`                | index      |
//!
//! **Named exceptions** (documented non-cells, mirroring the Lean module's `registers`
//! exception):
//!  * `registers` domain — EMPTY: per-proof VM transients, never persistent state.
//!  * `CellState.fields_root` — NOT projected: it is the DERIVED commitment of
//!    `fields_map` (a boundary view in the universal-memory design, recomputed on every
//!    map write without its own journal entry; projecting it would double-count the
//!    `Field` plane).
//!  * `CellState.heap_root` — NOT projected: the DERIVED commitment (boundary) of the
//!    `Heap` plane, exactly as `fields_root` is of `Field`. The sorted-Poseidon2 root
//!    over the projected `Heap` cells equals it (`boundary_root_derived`); projecting it
//!    would double-count the heap. The committed boundary is still on the cell, and a
//!    cross-cell read binds it directly ([`open_heap_against_committed`]).
//!  * the ledger Merkle tree / root — NOT projected: derived commitment over the cells.
//!  * rate-limit counters / budget gate — NOT projected: per-window executor metering,
//!    not consensus state (they never enter the state commitment).
//!  * the receipt log — owned by the node's MMR lane, not the executor; [`receipt_op`]
//!    lets the caller append the index-domain write when composing a whole-turn witness
//!    (the Lean side carries it as `RecChainedState.log`; adapter (b)
//!    `index_boundary_mroot_derived` covers its boundary commitment).

use std::collections::BTreeMap;

use dregg_cell::{
    Cell, CellId, FactoryRegistry, Ledger,
    capability::{CapabilityRef, CapabilitySet},
    lifecycle::CellLifecycle,
    nullifier_set::NullifierSet,
    state::STATE_SLOTS,
};

use crate::journal::JournalEntry;
use dregg_cell_crypto::note_bridge::BridgedNullifierSet;

/// The five state domains — wire codes IDENTICAL to the Lean
/// `DescriptorIR2.domainCode` (registers 0 · heap 1 · caps 2 · nullifiers 3 · index 4).
#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum UDomain {
    /// Per-proof VM register file — EMPTY in the persistent projection by design.
    Registers = 0,
    /// Per-cell record state (existence, fields, balances, lifecycle, roots).
    Heap = 1,
    /// Authority state (c-lists, delegation, permissions, programs, factories).
    Caps = 2,
    /// Insert-only sets (note nullifiers, bridged nullifiers).
    Nullifiers = 3,
    /// The append-only receipt index (the MMR-committed log).
    Index = 4,
    /// **Working / service memory (UMEM-PRIMITIVE.md §3, Stage D).** A service
    /// cell's (or the interpreter's, or a long-running effect's) TRANSIENT scratch.
    /// It participates in the ONE memcheck trace — so it is consistent for free
    /// (`universal_memory_sound`) — but, exactly like `Registers`, it is NEVER
    /// emitted by [`project_cell`]/[`project_ledger`]/[`project_executor_state`],
    /// so its boundary root never enters the state commitment and it costs nothing
    /// on the consensus path. A dedicated tag (distinct from `Registers`) so a
    /// service / the interpreter gets its OWN non-aliasing scratch
    /// (tag isolation: `consistentFrom_filter`). Its boundary is derivable on
    /// demand ([`working_umem_root`], the §4 checkpoint) but never published.
    Working = 5,
}

impl UDomain {
    /// The wire code (the circuit's domain column value).
    pub fn code(self) -> u32 {
        self as u32
    }
}

/// The structured in-domain key — one constructor per state plane (the Rust twin of the
/// Lean `UniversalBridge.UKey`). The deployed realization is
/// `addr = hash[domain_tag, collection_id, key]`; the constructor IS that triple's
/// abstract content.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, serde::Serialize, serde::Deserialize)]
pub enum UKey {
    // -- heap domain --------------------------------------------------------
    /// Cell existence (ledger membership bit).
    Exist(CellId),
    /// A cell record field: slots `< 16` are `fields[]`, slots `≥ 16` are `fields_map`.
    Field { cell: CellId, slot: u64 },
    /// The cell's signed balance.
    Balance(CellId),
    /// The cell's action nonce.
    Nonce(CellId),
    /// The proved-state flag.
    ProvedState(CellId),
    /// The whole lifecycle object (Live/Sealed/Destroyed…, death certificate included —
    /// the Lean table splits `lifecycle`/`deathCert`; the Rust collection carries the
    /// one canonical object, split at rotation lockstep).
    Lifecycle(CellId),
    /// Hosted/Sovereign mode.
    Mode(CellId),
    /// The cell's immutable identity pair `(public_key, token_id)`.
    Identity(CellId),
    /// Per-slot field visibility.
    FieldVisibility { cell: CellId, slot: u64 },
    /// Per-slot field commitment (for non-public fields).
    FieldCommitment { cell: CellId, slot: u64 },
    /// The CapTP swiss-table root carried in cell state.
    SwissTableRoot(CellId),
    /// The CapTP refcount-table root carried in cell state.
    RefcountTableRoot(CellId),
    /// One `system_roots` sub-block cell.
    SystemRoot { cell: CellId, index: u64 },
    /// The committed openable sorted-Poseidon2 heap root carried in cell state.
    /// NOT projected by `project_cell` (it is the DERIVED commitment of the
    /// `Heap` plane — see the module header's "Named exceptions"); retained as an
    /// address for the reify consistency check and verifier-supplied boundaries.
    HeapRoot(CellId),
    /// One entry of the cell's openable heap — the `(collection, key) → value`
    /// map whose committed boundary is the derived `heap_root`. This is the
    /// per-cell umem made first-class: a heap access projects to a genuine umem
    /// cell, and the derived sorted-Poseidon2 root over all `Heap` cells of one
    /// cell EQUALS that cell's committed `heap_root` (the boundary). A cross-cell
    /// read binds another cell's committed `heap_root` as an init image and opens
    /// a key here (see [`open_heap_against_committed`]).
    Heap {
        cell: CellId,
        collection: u32,
        key: u32,
    },
    /// A sovereign cell's 32-byte state commitment.
    SovereignCommitment(CellId),
    // -- caps domain --------------------------------------------------------
    /// One c-list slot of a cell (the capability table).
    CapSlot { cell: CellId, slot: u32 },
    /// The delegation parent pointer.
    Delegate(CellId),
    /// The delegation snapshot (`DelegatedRef`).
    DelegationSnapshot(CellId),
    /// The parent-side delegation epoch counter.
    DelegationEpoch(CellId),
    /// The block height at which the cell's state was last committed.
    CommittedHeight(CellId),
    /// The cell's permissions object.
    Permissions(CellId),
    /// The cell's verification key.
    VerificationKey(CellId),
    /// The cell's program (the slot-caveat registry a factory installs).
    Program(CellId),
    /// A published factory descriptor, keyed by factory VK hash.
    Factory([u8; 32]),
    // -- nullifiers domain (insert-only sets) -------------------------------
    /// A local note-spend nullifier.
    NoteNullifier([u8; 32]),
    /// An inbound cross-federation bridged nullifier.
    BridgedNullifier([u8; 32]),
    // -- index domain --------------------------------------------------------
    /// The receipt log at a chronological position (caller-supplied; see module docs).
    Receipt(u64),
    // -- working domain (transient service/interpreter scratch) --------------
    /// One `(collection, key)` cell of a service cell's (or the interpreter's)
    /// TRANSIENT working umem (UMEM-PRIMITIVE.md §3, Stage D). Keyed by the owning
    /// `service` so two services get disjoint, non-aliasing scratch. NEVER
    /// projected from persistent state — it lives only in the trace; its derivable
    /// boundary root ([`working_umem_root`]) is the §4 checkpoint and is never
    /// committed. (Added last so existing `UKey` ordering is undisturbed.)
    Working {
        service: CellId,
        collection: u32,
        key: u32,
    },
    // -- caps domain (revoked-slot ghost leaves) ----------------------------
    /// A capability TOMBSTONE: a revoked slot whose ghost ZERO leaf the deployed
    /// canonical `cap_root` KEEPS at the revoked slot's sorted position (the
    /// cap-crown revoke reconciliation — `CapabilitySet::revoke` records the slot
    /// in `tombstones`, and `compute_canonical_capability_root_felt` folds its
    /// `slot_hash` as a ghost leaf). The live `CapSlot` plane drops a revoked cap
    /// entirely, so without this plane the projection's derived `cap_root` would
    /// not reproduce the deployed root for a revoked cell (the former reify
    /// residual #3). Projecting the tombstoned slot lets
    /// [`derive_record_kernel_boundary`] re-fold the SAME ghost leaves the
    /// deployed root carries. Value-less (a `UVal::Present` marker — the slot is
    /// the whole content); the leaf digest the root folds is the ZERO sentinel,
    /// not a value. (Added last so existing `UKey` ordering is undisturbed.)
    CapTombstone { cell: CellId, slot: u32 },
}

impl UKey {
    /// The domain this key lives in (the projection table's right column).
    pub fn domain(&self) -> UDomain {
        match self {
            UKey::Exist(_)
            | UKey::Field { .. }
            | UKey::Balance(_)
            | UKey::Nonce(_)
            | UKey::ProvedState(_)
            | UKey::Lifecycle(_)
            | UKey::Mode(_)
            | UKey::Identity(_)
            | UKey::FieldVisibility { .. }
            | UKey::FieldCommitment { .. }
            | UKey::SwissTableRoot(_)
            | UKey::RefcountTableRoot(_)
            | UKey::SystemRoot { .. }
            | UKey::HeapRoot(_)
            | UKey::Heap { .. }
            | UKey::SovereignCommitment(_)
            | UKey::CommittedHeight(_) => UDomain::Heap,
            UKey::CapSlot { .. }
            | UKey::Delegate(_)
            | UKey::DelegationSnapshot(_)
            | UKey::DelegationEpoch(_)
            | UKey::Permissions(_)
            | UKey::VerificationKey(_)
            | UKey::Program(_)
            | UKey::CapTombstone { .. }
            | UKey::Factory(_) => UDomain::Caps,
            UKey::NoteNullifier(_) | UKey::BridgedNullifier(_) => UDomain::Nullifiers,
            UKey::Receipt(_) => UDomain::Index,
            UKey::Working { .. } => UDomain::Working,
        }
    }

    /// The cell a heap/caps-plane key belongs to (`None` for non-cell planes). Used to
    /// expand a `CreateCell` journal entry into the born cell's full bundle.
    pub fn cell(&self) -> Option<CellId> {
        match self {
            UKey::Exist(c)
            | UKey::Balance(c)
            | UKey::Nonce(c)
            | UKey::ProvedState(c)
            | UKey::Lifecycle(c)
            | UKey::Mode(c)
            | UKey::Identity(c)
            | UKey::SwissTableRoot(c)
            | UKey::RefcountTableRoot(c)
            | UKey::HeapRoot(c)
            | UKey::SovereignCommitment(c)
            | UKey::Delegate(c)
            | UKey::DelegationSnapshot(c)
            | UKey::DelegationEpoch(c)
            | UKey::CommittedHeight(c)
            | UKey::Permissions(c)
            | UKey::VerificationKey(c)
            | UKey::Program(c) => Some(*c),
            UKey::Field { cell, .. }
            | UKey::FieldVisibility { cell, .. }
            | UKey::FieldCommitment { cell, .. }
            | UKey::SystemRoot { cell, .. }
            | UKey::Heap { cell, .. }
            | UKey::CapTombstone { cell, .. }
            | UKey::CapSlot { cell, .. } => Some(*cell),
            UKey::Factory(_)
            | UKey::NoteNullifier(_)
            | UKey::BridgedNullifier(_)
            | UKey::Receipt(_)
            // Working scratch is TRANSIENT, not part of any cell's persistent
            // bundle — a `CreateCell` birth must NOT pull it in (it is keyed by an
            // owning service for namespacing only, like `Registers` it projects to
            // nothing). So it reports no owning cell.
            | UKey::Working { .. } => None,
        }
    }
}

/// A universal-memory cell VALUE. Plane-typed for debuggability; structured objects
/// (permissions, capability refs, lifecycle, programs…) carry their canonical JSON bytes
/// (deterministic: serde emits struct fields in declaration order).
#[derive(Clone, PartialEq, Eq, Debug, serde::Serialize, serde::Deserialize)]
pub enum UVal {
    /// Set-membership planes (existence, nullifiers): present.
    Present,
    /// Signed scalar (balance).
    Int(i64),
    /// Unsigned scalar (nonce, epochs, positions).
    U64(u64),
    /// Boolean flags (proved_state).
    Bool(bool),
    /// 32-byte values (field elements, roots, commitments).
    Bytes32([u8; 32]),
    /// Canonical JSON of a structured value.
    Blob(Vec<u8>),
    /// **A value that IS another umem's boundary root (UMEM-PRIMITIVE.md §5,
    /// Stage D).** A `UmemRef` makes one umem hold, at a key, the committed root
    /// of ANOTHER umem — the composable construct. Reading "through" the ref
    /// (binding the outer root, then binding the child root it names) is the
    /// recursive open ([`open_through_umem_ref`]): two independent
    /// `boundary_init_root_bound` applications, the keystone composed with itself.
    /// Distinct from `Bytes32` only by INTENT (it names another umem rather than a
    /// field element); the byte content is the child's sorted-Poseidon2 root.
    UmemRef([u8; 32]),
}

fn json<T: serde::Serialize>(t: &T) -> UVal {
    UVal::Blob(serde_json::to_vec(t).expect("umem: canonical JSON encoding"))
}

/// The projection image: present cells only (`absent = not in the map`, exactly the
/// Lean `Option`-cell encoding with `none` dropped).
pub type UProjection = BTreeMap<UKey, UVal>;

/// **THE CHECKED NON-PROJECTION INVARIANT (UMEM-PRIMITIVE.md §3).** The
/// persistent projection NEVER emits a `Working`-domain key. A `Working` cell
/// rides the ONE memcheck trace — so it is consistent for free
/// (`universal_memory_sound`) — but, exactly like `Registers`, its boundary root
/// must never enter the state commitment: it is transient service/interpreter
/// scratch, not consensus state. That guarantee was previously load-bearing only
/// by the Rust FACT that [`project_cell`]/[`project_ledger`]/
/// [`project_executor_state`] happen to never construct a `UKey::Working` — a
/// comment, not a checked property. This makes it CHECKED: if anyone later wires a
/// `Working` cell into a projection, it fires here (in debug/test builds) rather
/// than silently entering a committed boundary.
#[inline]
fn debug_assert_no_working(proj: &UProjection) {
    debug_assert!(
        !proj.keys().any(|k| k.domain() == UDomain::Working),
        "umem soundness: a persistent projection must NEVER carry a Working-domain \
         key — Working is transient trace-only scratch whose boundary is never \
         published into the state commitment (see UMEM-PRIMITIVE.md §3)"
    );
}

/// Project one cell's planes into the universal address space.
pub fn project_cell(cell: &Cell, out: &mut UProjection) {
    let id = cell.id();
    out.insert(UKey::Exist(id), UVal::Present);
    for slot in 0..STATE_SLOTS {
        out.insert(
            UKey::Field {
                cell: id,
                slot: slot as u64,
            },
            UVal::Bytes32(cell.state.fields[slot]),
        );
        out.insert(
            UKey::FieldVisibility {
                cell: id,
                slot: slot as u64,
            },
            json(&cell.state.field_visibility[slot]),
        );
        if let Some(c) = cell.state.commitments[slot] {
            out.insert(
                UKey::FieldCommitment {
                    cell: id,
                    slot: slot as u64,
                },
                UVal::Bytes32(c),
            );
        }
    }
    for (k, v) in cell.state.fields_map.iter() {
        out.insert(UKey::Field { cell: id, slot: *k }, UVal::Bytes32(*v));
    }
    out.insert(UKey::Balance(id), UVal::Int(cell.state.balance()));
    out.insert(UKey::Nonce(id), UVal::U64(cell.state.nonce()));
    out.insert(UKey::ProvedState(id), UVal::Bool(cell.state.proved_state()));
    out.insert(UKey::Lifecycle(id), json(&cell.lifecycle));
    out.insert(UKey::Mode(id), json(&cell.mode));
    out.insert(UKey::Identity(id), {
        let mut bytes = Vec::with_capacity(64);
        bytes.extend_from_slice(cell.public_key());
        bytes.extend_from_slice(cell.token_id());
        UVal::Blob(bytes)
    });
    out.insert(
        UKey::SwissTableRoot(id),
        UVal::Bytes32(cell.state.swiss_table_root),
    );
    out.insert(
        UKey::RefcountTableRoot(id),
        UVal::Bytes32(cell.state.refcount_table_root),
    );
    for (i, root) in cell.state.system_roots.iter().enumerate() {
        out.insert(
            UKey::SystemRoot {
                cell: id,
                index: i as u64,
            },
            UVal::Bytes32(*root),
        );
    }
    // The per-cell heap made a first-class umem (UMEM-PRIMITIVE.md §2, Stage A):
    // one `Heap{cell, collection, key}` cell per `heap_map` entry. The committed
    // `heap_root` is the DERIVED commitment over these preimage cells (the sorted-
    // Poseidon2 root EQUALS `cell.state.heap_root` by `compute_heap_root` /
    // `boundary_root_derived`), so — exactly like `fields_root` over the `Field`
    // plane — it is NOT projected here (projecting both would double-count the
    // heap and make every heap write also move a derived-root cell). This is a
    // refactor of WHERE the commitment is read (the preimage), not WHAT it commits.
    for ((collection, key), value) in cell.state.heap_map.iter() {
        out.insert(
            UKey::Heap {
                cell: id,
                collection: *collection,
                key: *key,
            },
            UVal::Bytes32(*value),
        );
    }
    out.insert(
        UKey::CommittedHeight(id),
        UVal::U64(cell.state.committed_height()),
    );
    // -- caps domain planes --
    for cap in cell.capabilities.iter() {
        out.insert(
            UKey::CapSlot {
                cell: id,
                slot: cap.slot,
            },
            json(cap),
        );
    }
    // The revoked-slot TOMBSTONE plane (UMEM-PRIMITIVE reify residual #3, now
    // closed for the boundary derivation): one `CapTombstone{cell, slot}` cell
    // per tombstoned slot, so the canonical `cap_root`'s ghost ZERO leaves are
    // re-derivable from the projection. The live `CapSlot` plane carries only
    // live caps; this plane carries exactly the revoked slots the deployed root
    // folds as ghosts (`compute_canonical_capability_root_felt`'s
    // `tombstoned_slots`). A cell that has never revoked emits none — byte-
    // identical to the former tombstone-free projection.
    for slot in cell.capabilities.tombstoned_slots() {
        out.insert(UKey::CapTombstone { cell: id, slot }, UVal::Present);
    }
    if let Some(parent) = cell.delegate {
        out.insert(UKey::Delegate(id), UVal::Bytes32(parent.0));
    }
    if let Some(delegation) = &cell.delegation {
        out.insert(UKey::DelegationSnapshot(id), json(delegation));
    }
    out.insert(
        UKey::DelegationEpoch(id),
        UVal::U64(cell.state.delegation_epoch()),
    );
    out.insert(UKey::Permissions(id), json(&cell.permissions));
    if let Some(vk) = &cell.verification_key {
        out.insert(UKey::VerificationKey(id), json(vk));
    }
    out.insert(UKey::Program(id), json(&cell.program));
    // SOUNDNESS: this projection of a persistent cell must carry no Working cell.
    debug_assert_no_working(out);
}

/// Project the whole ledger (hosted cells + sovereign commitments).
pub fn project_ledger(ledger: &Ledger) -> UProjection {
    let mut out = UProjection::new();
    for (_, cell) in ledger.iter() {
        project_cell(cell, &mut out);
    }
    for (id, commitment) in ledger.iter_sovereign_commitments() {
        out.insert(UKey::SovereignCommitment(*id), UVal::Bytes32(*commitment));
    }
    debug_assert_no_working(&out);
    out
}

/// Project the FULL executor state: the ledger + the executor-owned side tables
/// (note nullifiers, bridged nullifiers, the factory registry).
pub fn project_executor_state(
    ledger: &Ledger,
    note_nullifiers: &NullifierSet,
    bridged_nullifiers: &BridgedNullifierSet,
    factories: &FactoryRegistry,
) -> UProjection {
    let mut out = project_ledger(ledger);
    for n in note_nullifiers.iter() {
        out.insert(UKey::NoteNullifier(n.0), UVal::Present);
    }
    for n in bridged_nullifiers.iter() {
        out.insert(UKey::BridgedNullifier(*n), UVal::Present);
    }
    for (vk, desc) in factories.descriptors.iter() {
        out.insert(UKey::Factory(*vk), json(desc));
    }
    debug_assert_no_working(&out);
    out
}

// ===========================================================================
// THE 3-VERB EXECUTOR BRIDGE — the AUTHORITATIVE per-effect RecordKernelState
// projection (`UNIVERSAL-MAP-ROTATION.md` §2.3: "RecordKernelState → the ONE
// universal map"; `VerbCompression.lean:87-89`, "rides THE ONE ROTATION").
//
// [`project_executor_state`] / `TurnExecutor::umem_snapshot` produce the
// WHOLE-executor OBSERVATION surface (the witness lane, recursion-gated off).
// THIS is the per-effect ANCHOR a 3-verb circuit's differential gauntlets agree
// with: one cell's `RecordKernelState` (its before/after `Cell`) IS its
// universal-map projection, and the per-domain BOUNDARY roots DERIVED from that
// projection reproduce — value-for-value — the per-map-table representation the
// deployed commitment already carries (`cell.state.fields_root`,
// `cell.state.heap_root`, the canonical `cap_root`). The projection is the
// AUTHORITATIVE state representation; the committed map roots are DERIVED views
// over it, not an independent source of truth.
//
// This is the `boundary_root_derived` shadow at the PER-EFFECT level (the Lean
// keystone `metatheory/Dregg2/Crypto/UniversalMemory.lean:416`): a 3-verb
// circuit proving against THIS projection agrees with the deployed per-map-table
// roots BY CONSTRUCTION, so the differential never has to localize a divergence
// to "which root is right" — both compute the same object. VK-RISK-FREE: this
// is the executor's state PROJECTION + its representation, no descriptor / wire
// / VK change, and the `umem_witness_enabled` gate is untouched (these are pure
// functions over a `Cell`, not the prover path).
// ===========================================================================

/// **THE AUTHORITATIVE per-effect `RecordKernelState` projection** — one cell's
/// committed state (the rotated per-effect descriptor's per-cell before/after
/// block, `rotation_witness::produce`'s input) projected into the ONE universal
/// address space. The single-cell entry of [`project_cell`], named to mark it
/// THE per-effect anchor the 3-verb gauntlets point at. Pure: no ledger, no
/// journal, no gate.
pub fn project_record_kernel_state(cell: &Cell) -> UProjection {
    let mut out = UProjection::new();
    project_cell(cell, &mut out);
    out
}

/// The per-domain BOUNDARY roots DERIVED from a `RecordKernelState` projection —
/// the derived views the deployed commitment carries as its per-map-table roots.
/// Each is folded purely from the projection's cells (no access to the source
/// `Cell`'s stored roots), so equality with the cell's committed roots is a
/// genuine `boundary_root_derived` agreement, not a tautology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordKernelBoundary {
    /// The openable sorted-Poseidon2 root over the `Field` plane's OVERFLOW
    /// entries (slot ≥ `STATE_SLOTS`, the `fields_map`) — the deployed
    /// `cell.state.fields_root`.
    pub fields_root: [u8; 32],
    /// The openable sorted-Poseidon2 root over the `Heap` plane — the deployed
    /// `cell.state.heap_root`.
    pub heap_root: [u8; 32],
    /// The canonical FAITHFUL 8-felt capability root over the `CapSlot` plane's LIVE
    /// caps PLUS the `CapTombstone` plane's revoked ghost slots — the deployed
    /// `compute_canonical_capability_root_8(&cell.capabilities)` `Digest8` the
    /// EffectVM 8-felt `cap_root` column GROUP carries. Revoked cells are now
    /// faithful: the tombstone plane re-derives the deployed root's ghost ZERO
    /// leaves (the former reify residual #3).
    pub cap_root: [dregg_circuit::field::BabyBear; 8],
}

/// Derive the per-domain boundary roots from a `RecordKernelState` projection of
/// `cell` — fold each plane's projected cells through the SAME sorted-Poseidon2
/// machinery the deployed commitment uses (`compute_fields_root`,
/// `compute_heap_root`, the `cap_root` tree). The `Field` plane is split at
/// `STATE_SLOTS`: direct slots `< 16` are the register-file fields (not part of
/// `fields_root`); overflow slots `≥ 16` are the openable `fields_map`.
pub fn derive_record_kernel_boundary(proj: &UProjection, cell: CellId) -> RecordKernelBoundary {
    let mut fields_map: BTreeMap<u64, [u8; 32]> = BTreeMap::new();
    let mut heap_map: BTreeMap<(u32, u32), [u8; 32]> = BTreeMap::new();
    let mut cap_leaves: Vec<dregg_circuit::cap_root::CapLeaf> = Vec::new();
    let mut tombstone_keys: Vec<dregg_circuit::field::BabyBear> = Vec::new();
    for (k, v) in proj.iter() {
        match k {
            UKey::Field { cell: kc, slot } if *kc == cell && *slot >= STATE_SLOTS as u64 => {
                if let UVal::Bytes32(b) = v {
                    fields_map.insert(*slot, *b);
                }
            }
            UKey::Heap {
                cell: kc,
                collection,
                key,
            } if *kc == cell => {
                if let UVal::Bytes32(b) = v {
                    heap_map.insert((*collection, *key), *b);
                }
            }
            UKey::CapSlot { cell: kc, .. } if *kc == cell => {
                // The blob is the canonical JSON of the live `CapabilityRef`
                // (carrying its real `slot`, so `cap_ref_to_leaf`'s `slot_hash`
                // sort key is faithful regardless of slot contiguity).
                if let Ok(cap) = decode_blob::<CapabilityRef>(k, v) {
                    cap_leaves.push(dregg_cell::commitment::cap_ref_to_leaf(&cap));
                }
            }
            UKey::CapTombstone { cell: kc, slot } if *kc == cell => {
                // The revoked slot's ghost: fold its `slot_hash` (the SAME sort
                // key `cap_ref_to_leaf` uses) as a tombstone key, exactly as the
                // deployed `compute_canonical_capability_root_felt` does over
                // `tombstoned_slots`.
                tombstone_keys.push(dregg_circuit::cap_root::slot_hash(*slot));
            }
            _ => {}
        }
    }
    RecordKernelBoundary {
        fields_root: dregg_cell::state::compute_fields_root(&fields_map),
        heap_root: dregg_cell::state::compute_heap_root(&heap_map),
        // The revoked-slot tombstone plane (above) re-derives the SAME ghost ZERO
        // leaves the deployed root keeps, so the derived `cap_root` reproduces
        // `compute_canonical_capability_root_felt` even for a revoked cell — the
        // former reify residual #3, now closed for the boundary derivation. The
        // leaf/tombstone set order is irrelevant: the sorted-Poseidon2 tree
        // canonicalizes by sort key.
        cap_root: dregg_circuit::cap_root::compute_capability_root_with_tombstones(
            cap_leaves,
            &tombstone_keys,
        )
        .limbs(),
    }
}

/// A per-map-table BOUNDARY disagreement: a root DERIVED from the universal-map
/// projection does not equal the deployed per-map-table representation the cell
/// carries — the bridge's anti-drift tooth, named by plane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryDisagreement {
    /// The derived `fields_root` ≠ the cell's committed `fields_root`.
    FieldsRoot {
        /// The cell's committed `state.fields_root`.
        committed: [u8; 32],
        /// The root re-derived from the projected `Field` (slot ≥ 16) plane.
        derived: [u8; 32],
    },
    /// The derived `heap_root` ≠ the cell's committed `heap_root`.
    HeapRoot {
        /// The cell's committed `state.heap_root`.
        committed: [u8; 32],
        /// The root re-derived from the projected `Heap` plane.
        derived: [u8; 32],
    },
    /// The derived `cap_root` ≠ the cell's canonical capability root.
    CapRoot {
        /// `compute_canonical_capability_root_8(&cell.capabilities)` (`Digest8`).
        committed: [dregg_circuit::field::BabyBear; 8],
        /// The 8-felt root re-derived from the projected `CapSlot` plane.
        derived: [dregg_circuit::field::BabyBear; 8],
    },
}

impl std::fmt::Display for BoundaryDisagreement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundaryDisagreement::FieldsRoot { committed, derived } => write!(
                f,
                "RecordKernelState boundary: committed fields_root {committed:?} != \
                 root derived from the projected Field(slot>=16) plane {derived:?}"
            ),
            BoundaryDisagreement::HeapRoot { committed, derived } => write!(
                f,
                "RecordKernelState boundary: committed heap_root {committed:?} != \
                 root derived from the projected Heap plane {derived:?}"
            ),
            BoundaryDisagreement::CapRoot { committed, derived } => write!(
                f,
                "RecordKernelState boundary: canonical cap_root {committed:?} != \
                 root derived from the projected CapSlot plane {derived:?}"
            ),
        }
    }
}

impl std::error::Error for BoundaryDisagreement {}

/// **THE 3-VERB EXECUTOR BRIDGE AGREEMENT** — project a cell's `RecordKernelState`
/// into the ONE universal map ([`project_record_kernel_state`]), derive the
/// per-domain boundary roots from that projection alone
/// ([`derive_record_kernel_boundary`]), and CHECK each equals the deployed
/// per-map-table representation the cell carries. On agreement the universal-map
/// projection IS an authoritative representation of the cell's committed map
/// roots — the anchor a umem / 3-verb circuit's differential gauntlets bind to;
/// a disagreement names the plane that drifted ([`BoundaryDisagreement`]).
///
/// **The faithful class is now TOTAL over the openable planes — revoked cells
/// included.** A revoked slot leaves a ghost ZERO leaf in the deployed `cap_root`
/// (the cap-crown reconciliation); the live `CapSlot` plane drops it, but the
/// `CapTombstone` plane carries it, so [`derive_record_kernel_boundary`] re-folds
/// the SAME ghosts the deployed root keeps and the derived `cap_root` matches
/// even after a revoke (the former reify residual #3, closed here for the
/// boundary). The `fields_root` and `heap_root` planes are ALWAYS faithful
/// (openable sorted-Poseidon2 maps with no dropped state). The 3-verb gauntlet
/// lanes (transfer / set-field / set-heap / grant / attenuate / revoke) all
/// agree.
pub fn record_kernel_boundary_agrees(
    cell: &Cell,
) -> Result<RecordKernelBoundary, BoundaryDisagreement> {
    let proj = project_record_kernel_state(cell);
    let derived = derive_record_kernel_boundary(&proj, cell.id());
    if derived.fields_root != cell.state.fields_root.to_bytes32() {
        return Err(BoundaryDisagreement::FieldsRoot {
            committed: cell.state.fields_root.to_bytes32(),
            derived: derived.fields_root,
        });
    }
    if derived.heap_root != cell.state.heap_root.to_bytes32() {
        return Err(BoundaryDisagreement::HeapRoot {
            committed: cell.state.heap_root.to_bytes32(),
            derived: derived.heap_root,
        });
    }
    let committed_cap =
        dregg_cell::commitment::compute_canonical_capability_root_8(&cell.capabilities);
    if derived.cap_root != committed_cap {
        return Err(BoundaryDisagreement::CapRoot {
            committed: committed_cap.limbs(),
            derived: derived.cap_root,
        });
    }
    Ok(derived)
}

/// The binding refused: a cell's projected `Heap` preimage does not reproduce
/// the committed `heap_root` it was bound against — the Rust shadow of the
/// keystone's anti-forgery tooth `boundary_init_root_bound`
/// (`metatheory/Dregg2/Crypto/UniversalMemory.lean:475`): a tampered init image
/// produces a different sorted-Poseidon2 leaf list, hence a different root,
/// hence the pin refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeapBindError {
    /// The cell whose heap was being bound.
    pub cell: CellId,
    /// The committed `heap_root` supplied as the init image's boundary.
    pub committed: [u8; 32],
    /// The root re-derived from the projected `Heap` preimage (≠ `committed`).
    pub derived: [u8; 32],
}

impl std::fmt::Display for HeapBindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "umem heap bind refused for cell {:?}: committed root {:?} != \
             root derived from projected Heap preimage {:?}",
            self.cell, self.committed, self.derived
        )
    }
}

impl std::error::Error for HeapBindError {}

/// **THE CROSS-CELL HEAP READ** — bind another cell's committed `heap_root` as an
/// init image and open one `(collection, key)`. This is the keystone's first
/// cross-cell consumer (UMEM-PRIMITIVE §2, Stage A): a reader opens cell `cell`'s
/// heap from a projection `proj` while pinning it to a `committed` root.
///
/// The init binding is the Rust shadow of `boundary_init_root_bound`: the heap's
/// projected preimage is re-folded into its sorted-Poseidon2 root
/// (`compute_heap_root`); if that does not equal the committed root the read
/// REFUSES ([`HeapBindError`]) — a tampered image cannot keep the published root.
/// On a sound binding the key is opened: `Ok(Some(value))` if present,
/// `Ok(None)` if absent (the Merkle-path-free freshness leg).
pub fn open_heap_against_committed(
    proj: &UProjection,
    cell: CellId,
    committed: [u8; 32],
    collection: u32,
    key: u32,
) -> Result<Option<[u8; 32]>, HeapBindError> {
    let mut heap: BTreeMap<(u32, u32), [u8; 32]> = BTreeMap::new();
    let mut requested: Option<[u8; 32]> = None;
    for (k, v) in proj.iter() {
        if let UKey::Heap {
            cell: kc,
            collection: c,
            key: kk,
        } = k
        {
            if *kc == cell {
                let value = match v {
                    UVal::Bytes32(b) => *b,
                    // a malformed plane cannot reproduce the committed root, so
                    // the binding will refuse below; record a zero placeholder.
                    _ => [0u8; 32],
                };
                heap.insert((*c, *kk), value);
                if *c == collection && *kk == key {
                    requested = Some(value);
                }
            }
        }
    }
    let derived = dregg_cell::state::compute_heap_root(&heap);
    if derived != committed {
        return Err(HeapBindError {
            cell,
            committed,
            derived,
        });
    }
    Ok(requested)
}

/// The 32-byte content a working-umem cell folds into its boundary root: a
/// `UmemRef` (the composable case — the value IS a child root) or a raw
/// `Bytes32`. Any other shape cannot reproduce the committed root, so it folds
/// as a zero placeholder and the binding refuses below.
fn working_cell_bytes(v: &UVal) -> [u8; 32] {
    match v {
        UVal::UmemRef(b) | UVal::Bytes32(b) => *b,
        _ => [0u8; 32],
    }
}

/// **THE WORKING-UMEM BOUNDARY (UMEM-PRIMITIVE.md §3/§5, Stage D).** Derive, on
/// demand, the sorted-Poseidon2 root over one `service`'s `Working`-domain cells
/// in `proj` — the §4 checkpoint of a transient working/service umem. This root
/// is NEVER published into the state commitment (the `Working` domain is never
/// projected from persistent state, exactly like `Registers`); it exists only so
/// a working umem can be bound as an init image when a reader opens "through" it
/// ([`open_through_umem_ref`]). The fold uses the SAME `compute_heap_root` as the
/// per-cell heap, so a working-umem-of-roots binds by exactly the keystone's
/// `boundary_init_root_bound` tooth.
pub fn working_umem_root(proj: &UProjection, service: CellId) -> [u8; 32] {
    let mut map: BTreeMap<(u32, u32), [u8; 32]> = BTreeMap::new();
    for (k, v) in proj.iter() {
        if let UKey::Working {
            service: s,
            collection,
            key,
        } = k
        {
            if *s == service {
                map.insert((*collection, *key), working_cell_bytes(v));
            }
        }
    }
    dregg_cell::state::compute_heap_root(&map)
}

/// Why a recursive open through a `UmemRef` refused — each variant names the
/// LEVEL whose boundary binding failed (the Rust shadow of an independent
/// `boundary_init_root_bound` application per level).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursiveOpenError {
    /// LEVEL 1: the outer service umem's projected `Working` preimage does not
    /// reproduce the committed root it was bound against (a tampered outer image).
    OuterBindRefused {
        /// The service whose working umem was bound.
        service: CellId,
        /// The committed boundary root supplied for level 1.
        committed: [u8; 32],
        /// The root re-derived from the projected `Working` preimage (≠ committed).
        derived: [u8; 32],
    },
    /// The outer umem holds no cell at the ref address — there is no child to
    /// descend into.
    RefMissing {
        service: CellId,
        collection: u32,
        key: u32,
    },
    /// The outer umem's cell at the ref address is present but is NOT a
    /// `UVal::UmemRef` (it does not name a child umem to open through).
    RefNotAUmemRef {
        service: CellId,
        collection: u32,
        key: u32,
    },
    /// LEVEL 2: the child cell's projected `Heap` preimage does not reproduce the
    /// root the outer `UmemRef` named (a tampered child image).
    ChildBindRefused(HeapBindError),
}

impl std::fmt::Display for RecursiveOpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RecursiveOpenError::OuterBindRefused {
                service,
                committed,
                derived,
            } => write!(
                f,
                "recursive open: outer service umem {service:?} bind refused — \
                 committed root {committed:?} != root derived from the projected \
                 Working preimage {derived:?}"
            ),
            RecursiveOpenError::RefMissing {
                service,
                collection,
                key,
            } => write!(
                f,
                "recursive open: outer umem {service:?} holds no cell at ref \
                 ({collection}, {key})"
            ),
            RecursiveOpenError::RefNotAUmemRef {
                service,
                collection,
                key,
            } => write!(
                f,
                "recursive open: outer umem {service:?} cell at ({collection}, \
                 {key}) is not a UmemRef"
            ),
            RecursiveOpenError::ChildBindRefused(e) => {
                write!(f, "recursive open: child level — {e}")
            }
        }
    }
}

impl std::error::Error for RecursiveOpenError {}

/// **THE RECURSIVE OPEN — composable umems (UMEM-PRIMITIVE.md §5, Stage D).**
/// Open a child cell's heap *through* a service cell's working umem-of-roots:
///
///  1. **LEVEL 1** — bind the outer service umem's committed boundary
///     (`service_committed`) as an init image: re-fold its `Working` preimage
///     into a sorted-Poseidon2 root ([`working_umem_root`]) and refuse if it does
///     not equal `service_committed` (the Rust shadow of `boundary_init_root_bound`
///     at the outer level). Then read the child root the outer umem holds at
///     `(ref_collection, ref_key)` — it MUST be a [`UVal::UmemRef`].
///  2. **LEVEL 2** — bind that child root as the child cell's heap init image and
///     open `(child_collection, child_key)` ([`open_heap_against_committed`] — the
///     SAME keystone tooth, applied a second time).
///
/// Two independent `boundary_init_root_bound` applications: the keystone composed
/// with itself, soundness compositional for free. The levels CANNOT alias —
/// the outer cells live in the `Working` domain and the child cells in the `Heap`
/// domain, disjoint by tag (`consistentFrom_filter`). A tamper at either level
/// derives a different root and the matching bind refuses.
///
/// `Ok(Some(v))` if the child key is present, `Ok(None)` if absent (the
/// Merkle-path-free freshness leg), `Err` naming the level that refused.
#[allow(clippy::too_many_arguments)]
pub fn open_through_umem_ref(
    proj: &UProjection,
    service: CellId,
    service_committed: [u8; 32],
    ref_collection: u32,
    ref_key: u32,
    child_cell: CellId,
    child_collection: u32,
    child_key: u32,
) -> Result<Option<[u8; 32]>, RecursiveOpenError> {
    // LEVEL 1 — bind the outer service umem's committed boundary root.
    let outer_derived = working_umem_root(proj, service);
    if outer_derived != service_committed {
        return Err(RecursiveOpenError::OuterBindRefused {
            service,
            committed: service_committed,
            derived: outer_derived,
        });
    }
    // Read the child umem-ref the bound outer umem names at the ref address.
    let child_root = match proj.get(&UKey::Working {
        service,
        collection: ref_collection,
        key: ref_key,
    }) {
        Some(UVal::UmemRef(r)) => *r,
        Some(_) => {
            return Err(RecursiveOpenError::RefNotAUmemRef {
                service,
                collection: ref_collection,
                key: ref_key,
            });
        }
        None => {
            return Err(RecursiveOpenError::RefMissing {
                service,
                collection: ref_collection,
                key: ref_key,
            });
        }
    };
    // LEVEL 2 — bind the child cell's heap against the root the ref named, open.
    open_heap_against_committed(proj, child_cell, child_root, child_collection, child_key)
        .map_err(RecursiveOpenError::ChildBindRefused)
}

/// Memory-op kind (the memcheck `Kind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize, serde::Deserialize)]
pub enum UmemKind {
    /// A read (returns and re-claims the current cell).
    Read,
    /// A write (installs `val` over the claimed `prev_val`).
    Write,
}

/// One Blum trace op against the unified address space. `val`/`prev_val` are
/// `Option`-cells (`None` = absent), exactly the Lean `Op (UAddr UKey) (Option ℤ)` /
/// the circuit's `(present, value)` encoding. The op at trace position `i` carries
/// serial `i + 1` (positional, as the circuit assembly computes it); `prev_serial` is
/// the serial of the previous touch of the same address (`0` = the init boundary).
#[derive(Clone, PartialEq, Eq, Debug, serde::Serialize, serde::Deserialize)]
pub struct UmemOp {
    /// Read or write.
    pub kind: UmemKind,
    /// The structured address (domain = `key.domain()`).
    pub key: UKey,
    /// The cell value after the op (for a read: the value returned).
    pub val: Option<UVal>,
    /// The claimed previous cell value.
    pub prev_val: Option<UVal>,
    /// The claimed previous serial (`0` = init boundary).
    pub prev_serial: u64,
}

/// The per-turn universal-memory witness the executor can now produce: the pre/post
/// projections plus the Blum op trace whose fold connects them (the executable shadow
/// of the Lean `*_is_memory_program` agreement theorems).
#[derive(Clone, Debug)]
pub struct UmemTurnWitness {
    /// The projection of the executor state at the journal window's start (post
    /// fee/nonce phase — the forest execution's pre-state).
    pub pre: UProjection,
    /// The Blum write trace of the forest execution, in journal (= execution) order.
    pub ops: Vec<UmemOp>,
    /// The projection at the journal window's end (before fee distribution).
    pub post: UProjection,
    /// How many ops were synthesized from the pre/post diff because no journal entry
    /// named their address (state surfaces whose effects don't journal per-address
    /// yet). `0` for the transfer / set-field / capability lanes.
    pub synthesized: usize,
}

/// The REAL memory semantics, independently implemented (the `MemoryChecking.step`
/// fold): a write installs its value (absent = remove), a read changes nothing.
pub fn fold(pre: &UProjection, ops: &[UmemOp]) -> UProjection {
    let mut m = pre.clone();
    for op in ops {
        if let UmemKind::Write = op.kind {
            match &op.val {
                Some(v) => {
                    m.insert(op.key.clone(), v.clone());
                }
                None => {
                    m.remove(&op.key);
                }
            }
        }
    }
    m
}

/// The per-op memcheck discipline: `prev_serial` strictly below the op's own positional
/// serial, and a read returns exactly its claimed previous value.
pub fn disciplined(ops: &[UmemOp]) -> bool {
    ops.iter().enumerate().all(|(i, op)| {
        op.prev_serial < (i as u64) + 1 && (op.kind != UmemKind::Read || op.val == op.prev_val)
    })
}

/// The index-domain write for the turn's receipt at log position `position` (the caller
/// owns the log — see module docs). `prev_val = None`: the position is fresh
/// (append-only log).
pub fn receipt_op(position: u64, receipt_hash: [u8; 32]) -> UmemOp {
    UmemOp {
        kind: UmemKind::Write,
        key: UKey::Receipt(position),
        val: Some(UVal::Bytes32(receipt_hash)),
        prev_val: None,
        prev_serial: 0,
    }
}

// ============================================================================
// THE UMEM BOUNDARY PRODUCER — `UmemTurnWitness` → a REAL `UMemBoundaryWitness`.
//
// The deployed-plumbing piece that lets the SDK/IVC prover be handed a REAL (non-`default`)
// universal-memory boundary witness. Until now the `UmemTurnWitness → UMemBoundaryWitness`
// lowering lived only as test-local helpers (`circuit/tests/effect_vm_umem_real_turn.rs`'s
// `lower`, `effect_vm_umem_cohort.rs`'s `build_umem_form`); this is the library function the
// rotation-flip's Rank 4 routes the deployed prover through (the prover-switch is the NEXT
// sequenced, gated step — this producer is VK-risk-free in isolation).
//
// The lowering uses the deployed Rank-1 address/value CODECS (`heap_addr` for the heap/field
// planes, `slot_hash` for the caps plane, `fold_bytes32`/`fold_bytes` for nullifiers and
// structured values — `metatheory/Dregg2/Crypto/UMemCodec.lean`, `a2217919`), so the produced
// boundary carries REAL structured `(domain, key)` addresses and value felts (not the
// per-proof dense relabeling). The `(domain, key)` address is the literal pair — the domain is
// its own bus coordinate (`UMemOpSpec.domain`), so the in-domain key carries `hash[coll, key]`.
//
// The producer reads the turn's Blum WRITE trace (`UmemTurnWitness::ops`) as the per-op main
// rows and the turn's PRE projection (`UmemTurnWitness::pre`) as the per-domain boundary's init
// image — exactly the triple `prove_vm_descriptor2_umem` consumes. The fold square
// (`fold(pre, ops) == post`) and the memcheck discipline the executor already guarantees carry
// straight into the multiset balance: each address's init is emitted once by the boundary at
// serial 0, every op claims either that init (`prev_serial == 0`) or a prior op's installed
// value, and the codec is a deterministic function so equal values encode to equal felts.

use dregg_circuit::cap_root::{fold_bytes32, slot_hash};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemKind, UMemBoundaryWitness, UMemOpSpec, VmConstraint2,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::heap_root::heap_addr;
use dregg_circuit::lean_descriptor_air::LeanExpr;

/// Field-plane collection tag (the user-field map lives under one logical collection).
const UMEM_FIELD_COLL: u32 = 0xF1E1;
/// Balance scalar tag (the economic register made a umem cell).
const UMEM_BALANCE_COLL: u32 = 0xBA1A;
/// Nonce scalar tag.
const UMEM_NONCE_COLL: u32 = 0x0CE0;

/// Fold a low `u64` into a key felt limb (the in-domain `key` argument of `heap_addr`).
fn umem_key_limb_v1(x: u64) -> BabyBear {
    BabyBear::new((x % (BABYBEAR_P as u64)) as u32)
}

/// Horner fold of canonical bytes into a felt (the Rank-1 value-codec shape: a field image of
/// the value; `Bytes32` rides the deployed `fold_bytes32`). Nonzero seed so the empty value is
/// distinct from absence.
fn umem_fold_bytes_v1(bytes: &[u8]) -> BabyBear {
    let mut acc = BabyBear::ONE;
    let mul = BabyBear::new(0x1000_0193); // FNV-ish field multiplier
    for &b in bytes {
        acc = acc * mul + BabyBear::new(b as u32 + 1);
    }
    acc
}

/// The owning cell folded into a felt (the universal-map address is per-CELL: unlike a single
/// cell's own heap, the unified address space holds every cell, so the cell identity is part of
/// the address — two cells' balances are distinct `(domain, key)` cells).
fn umem_cell_felt_v1(c: &CellId) -> BabyBear {
    fold_bytes32(c.as_bytes())
}

/// The deployed-codec structured `(domain code, in-domain key felt)` of a projected address —
/// Rank-1's `uaddrEnc` shape with the domain split out as its own column. Cell-plane keys fold
/// the owning cell into the address (via the deployed `heap_addr` hash) so the universal map's
/// per-cell cells never alias across cells.
pub fn umem_key_addr_v1(k: &UKey) -> (u32, BabyBear) {
    let domain = k.domain().code();
    let key = match k {
        UKey::Heap {
            cell,
            collection,
            key,
        } => heap_addr(
            umem_cell_felt_v1(cell),
            heap_addr(BabyBear::new(*collection), BabyBear::new(*key)),
        ),
        UKey::Field { cell, slot } => heap_addr(
            umem_cell_felt_v1(cell),
            heap_addr(BabyBear::new(UMEM_FIELD_COLL), umem_key_limb_v1(*slot)),
        ),
        UKey::Balance(cell) => heap_addr(
            umem_cell_felt_v1(cell),
            heap_addr(BabyBear::new(UMEM_BALANCE_COLL), BabyBear::ZERO),
        ),
        UKey::Nonce(cell) => heap_addr(
            umem_cell_felt_v1(cell),
            heap_addr(BabyBear::new(UMEM_NONCE_COLL), BabyBear::ZERO),
        ),
        UKey::CapSlot { cell, slot } => heap_addr(umem_cell_felt_v1(cell), slot_hash(*slot)),
        UKey::NoteNullifier(b) | UKey::BridgedNullifier(b) => fold_bytes32(b),
        // Any other projected address: a deterministic injective felt over its canonical
        // serialization (which carries the owning cell). The planes above are the ones the
        // cohort effects touch on the hot path; the fallback keeps the producer total over the
        // whole `UKey` space.
        other => umem_fold_bytes_v1(&serde_json::to_vec(other).expect("ukey serializes")),
    };
    (domain, key)
}

/// The `(present, value)` felt pair of an optional cell — `none ↦ (0, 0)`, the canonical absent
/// encoding the umem grammar pins.
pub fn umem_val_felt_v1(v: Option<&UVal>) -> (BabyBear, BabyBear) {
    match v {
        None => (BabyBear::ZERO, BabyBear::ZERO),
        Some(UVal::Bytes32(b)) | Some(UVal::UmemRef(b)) => (BabyBear::ONE, fold_bytes32(b)),
        Some(other) => (
            BabyBear::ONE,
            umem_fold_bytes_v1(&serde_json::to_vec(other).expect("uval serializes")),
        ),
    }
}

/// The IR-v2 universal-memory proving inputs the producer derives from a turn's
/// [`UmemTurnWitness`]: the umem-form descriptor, the per-op main trace, and the REAL
/// [`UMemBoundaryWitness`](dregg_circuit::descriptor_ir2::UMemBoundaryWitness). The deployed
/// `prove_vm_descriptor2_umem` consumes the triple (`&descriptor, &rows, &[]/* PIs */,
/// &MemBoundaryWitness::default(), &[]/* map heaps */, &boundary`).
#[derive(Clone, Debug)]
pub struct UmemProvingInputsV1 {
    /// The umem-form descriptor: one `UMemOp` constraint per touched domain, guarded by its
    /// own indicator column.
    pub descriptor: EffectVmDescriptor2,
    /// One main row per Blum op (key · present · value · prev_present · prev_value · prev_serial
    /// + the per-domain guard columns), padded to a power of two.
    pub rows: Vec<Vec<BabyBear>>,
    /// The REAL universal-memory boundary: the turn's touched `(domain, key)` addresses with
    /// their PRE-state cells as the init image.
    pub boundary: UMemBoundaryWitness,
}

/// **THE PRODUCER** — derive the REAL universal-memory proving inputs (descriptor + per-op
/// trace + [`UMemBoundaryWitness`](dregg_circuit::descriptor_ir2::UMemBoundaryWitness)) from a
/// turn's [`UmemTurnWitness`]. The boundary is non-`default`: it carries the turn's genuine
/// touched addresses (under the deployed codecs) with their pre-state init image, so the
/// SDK/IVC prover can be handed a real boundary instead of `UMemBoundaryWitness::default()`.
///
/// `Err` if the address codec collides (two distinct `UKey`s lowering to the same
/// `(domain, key)` felt — caught so the strict-increasing boundary stays sound), if the VALUE
/// codec collides at one address (see [`admit_value_v2`]), or the trace is empty.
pub fn umem_proving_inputs_v1(witness: &UmemTurnWitness) -> Result<UmemProvingInputsV1, String> {
    umem_proving_inputs_from_v1(&witness.pre, &witness.ops)
}

/// **THE VALUE HALF OF THE PRODUCER'S INJECTIVITY GATE — and the production caller of the
/// faithful UMEM-V2 codec.**
///
/// [`umem_proving_inputs_from_v1`] has gated ADDRESS injectivity since it was written: two
/// distinct `UKey`s lowering to one `(domain, key)` felt is refused, "else the boundary's
/// strict-increasing requirement (and the multiset balance) is unsound". The same felt-plane
/// argument applies to the OTHER coordinate and was not gated at all, so this is the missing
/// half of an existing gate rather than a new policy.
///
/// # What the felt plane cannot see
///
/// [`umem_val_felt_v1`] lowers `Option<&UVal>` to `(present, value)`, TWO felts, and it is
/// many-to-one on the source in three independent ways:
///
/// 1. **Variant erasure, cost 0.** `Some(Bytes32(b))` and `Some(UmemRef(b))` share the arm
///    `(ONE, fold_bytes32(b))` — literally the same match arm. They are not the same value:
///    [`UVal::UmemRef`]'s own doc says it "names another umem rather than a field element" and
///    [`open_through_umem_ref`] treats its bytes as a CHILD UMEM'S COMMITTED ROOT. So a plain
///    32-byte field element and a claimed child-umem root are indistinguishable in the committed
///    trace. Every other variant collapses through `serde_json` into one Horner fold, so
///    `Int`/`U64`/`Bool`/`Blob` separate only by whatever their JSON happens to be.
/// 2. **The `+p` chunk alias, cost 0.** `fold_bytes32` is `hash_many(bytes32_to_8_limbs(b))` and
///    `bytes32_to_8_limbs` is a per-4-byte-chunk `u32 % p` projection with `2p < 2^32`, so for
///    53.1% of chunk values `v` and `v + p` are DIFFERENT bytes with an IDENTICAL limb —
///    constructed by one addition, no search. `cap_root::fold_bytes32`'s own doc states this.
/// 3. **The one-felt squeeze, `2^15.45`.** Even with an injective encoder the image is one
///    BabyBear: `log2 p = 30.906891`, so a birthday collision over unaliased preimages costs
///    `2^(30.906891/2) = 2^15.4534` ≈ 44,900 evaluations. COLLISION, not second preimage — the
///    producer of a trace chooses both sides.
///
/// # Why that matters, stated at the resolution the code supports
///
/// The umem AIR decides a fact about FELT ROWS: that the trace is a consistent offline-checked
/// memory over `(domain, key)`. The host then reads those rows back as TYPED SOURCES — and
/// [`reify_cell`] genuinely dispatches on the variant (`expect_bytes32`, `expected Int`,
/// `expected U64`). That inference step is sound only if the lowering is injective ON THE SOURCES
/// THIS TRACE CONTAINS. Where it is not, a read-after-write that the AIR certifies as consistent
/// can be a `Bytes32` write answered by a `UmemRef` read.
///
/// ⚠ **This is a producer-side refusal, so it is an HONESTY gate, not a soundness one, and the
/// address half above has exactly the same character.** A prover who does not call the producer
/// is not stopped by it. What it does buy is that no trace the deployed cohort generators
/// ([`umem_cohort_proving_inputs_from`], [`umem_cohort_multidomain_proving_inputs_from`]) hand to
/// `prove_vm_descriptor2_umem` can carry an alias the committed rows cannot express — the
/// producer refuses instead of emitting rows whose source reading is ambiguous. Closing it on the
/// VERIFYING side is the wire widening, which is a Lean emit epoch and is priced in the UMEM-V2
/// section below.
///
/// # Distinctness is V2's, deliberately
///
/// The gate's notion of "two distinct sources" is [`UValV2`] equality — presence, variant tag,
/// exact byte length, exact `u16` payload limbs — not an ad-hoc one. That is the same object the
/// future wire epoch commits, so this refuses exactly the pairs that epoch will separate, and it
/// cannot drift from it.
///
/// ⚠ It takes the ENCODING and deliberately **not** V2's `UMEM_V2_MAX_BLOB_BYTES` ceiling — see
/// [`UValV2::encode_canonical`] for why inheriting it would have turned this collision fix into an
/// availability cliff on any cell with a large `Program` or `VerificationKey` plane. This gate
/// therefore refuses **only** aliases: it never refuses on size, and it can only turn an
/// already-emittable trace into an error, never the reverse.
fn admit_value_v2(
    by_cell: &mut BTreeMap<((u32, u32), (u32, u32)), UValV2>,
    addr: (u32, BabyBear),
    source: Option<&UVal>,
) -> Result<(), String> {
    let faithful = UValV2::encode_canonical(source);
    let (present, value) = umem_val_felt_v1(source);
    let coord = (
        (addr.0, addr.1.as_u32()),
        (present.as_u32(), value.as_u32()),
    );
    match by_cell.get(&coord) {
        Some(prev) if prev != &faithful => Err(format!(
            "umem producer: VALUE codec collision at (domain {}, key {}) — two DISTINCT sources \
             lower to the one-felt cell (present {}, value {}): V2 variant {} / {} source bytes \
             against V2 variant {} / {} source bytes. The committed row cannot tell them apart, \
             so a read of one would be certified against a write of the other.",
            addr.0,
            addr.1.as_u32(),
            present.as_u32(),
            value.as_u32(),
            prev.variant(),
            prev.source_byte_len(),
            faithful.variant(),
            faithful.source_byte_len(),
        )),
        _ => {
            by_cell.insert(coord, faithful);
            Ok(())
        }
    }
}

/// Compatibility producer over an explicit pre-state projection and op trace.
/// This preserves the arbitrary-domain descriptor API. Production fixed-cohort adapters
/// instead consume the shared checked witness metadata directly, without constructing AIR.
/// Address/value admission and row/boundary construction are identical on both paths.
pub fn umem_proving_inputs_from_v1(
    pre: &UProjection,
    ops: &[UmemOp],
) -> Result<UmemProvingInputsV1, String> {
    let UmemWitnessInputsV1 {
        domains,
        rows,
        boundary,
    } = umem_witness_inputs_from_v1(pre, ops)?;
    // Preserve the arbitrary-domain write-form descriptor. A disciplined read is a
    // same-value write (val == prev_val) under this journal-derived trace convention.
    let constraints: Vec<VmConstraint2> = domains
        .iter()
        .enumerate()
        .map(|(i, d)| {
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(6 + i),
                domain: *d,
                key: LeanExpr::Var(0),
                present: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                prev_present: LeanExpr::Var(3),
                prev_value: LeanExpr::Var(4),
                prev_serial: LeanExpr::Var(5),
                kind: MemKind::Write,
            })
        })
        .collect();

    let descriptor = EffectVmDescriptor2 {
        name: "umem-turn-boundary".to_string(),
        trace_width: 6 + domains.len(),
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };

    Ok(UmemProvingInputsV1 {
        descriptor,
        rows,
        boundary,
    })
}

/// Checked witness data shared by the compatibility producer and emitted-cohort adapters.
/// `domains[i]` names guard column `6 + i`; codes are sorted and unique.
struct UmemWitnessInputsV1 {
    domains: Vec<u32>,
    rows: Vec<Vec<BabyBear>>,
    boundary: UMemBoundaryWitness,
}

/// Derive witness data without authoring a descriptor. Both address and value admission
/// remain on every cohort path, including the pre-state cells in the boundary.
fn umem_witness_inputs_from_v1(
    pre: &UProjection,
    ops: &[UmemOp],
) -> Result<UmemWitnessInputsV1, String> {
    if ops.is_empty() {
        return Err("umem producer: empty op trace (no boundary to derive)".into());
    }

    // Per-address codec + injectivity: distinct `UKey`s MUST lower to distinct `(domain, key)`
    // felts, else the boundary's strict-increasing requirement (and the multiset balance) is
    // unsound. Fail closed on a collision.
    let mut by_addr: BTreeMap<(u32, u32), UKey> = BTreeMap::new();
    let mut touched: BTreeMap<UKey, (u32, BabyBear)> = BTreeMap::new();
    // The VALUE half of the same gate — see [`admit_value_v2`] for what the felt plane cannot
    // see and why the distinctness relation is the faithful V2 encoding's.
    let mut by_cell: BTreeMap<((u32, u32), (u32, u32)), UValV2> = BTreeMap::new();
    for op in ops {
        let (d, key) = umem_key_addr_v1(&op.key);
        match by_addr.get(&(d, key.as_u32())) {
            Some(prev) if prev != &op.key => {
                return Err(format!(
                    "umem producer: address codec collision — {prev:?} and {:?} both lower to \
                     (domain {d}, key {})",
                    op.key,
                    key.as_u32()
                ));
            }
            _ => {
                by_addr.insert((d, key.as_u32()), op.key.clone());
            }
        }
        // Both endpoints of every row ride the felt plane, so both are admitted.
        admit_value_v2(&mut by_cell, (d, key), op.val.as_ref())?;
        admit_value_v2(&mut by_cell, (d, key), op.prev_val.as_ref())?;
        touched.entry(op.key.clone()).or_insert((d, key));
    }
    // ...and so does each touched address's PRE-state cell, which becomes `boundary.init_vals`.
    for (k, (d, key)) in &touched {
        admit_value_v2(&mut by_cell, (*d, *key), pre.get(k))?;
    }

    // Sorted metadata determines guard columns for the existing emitted cohort shapes.
    // The compatibility wrapper alone turns these domains into UMemOp constraints.
    let mut domains: Vec<u32> = touched.values().map(|(d, _)| *d).collect();
    domains.sort_unstable();
    domains.dedup();
    let guard_col: BTreeMap<u32, usize> = domains
        .iter()
        .enumerate()
        .map(|(i, d)| (*d, 6 + i))
        .collect();
    let width = 6 + domains.len();

    // One main row per Blum op (in execution order), padded to a power of two with guards off.
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(ops.len());
    for op in ops {
        let (d, key) = umem_key_addr_v1(&op.key);
        let (present, value) = umem_val_felt_v1(op.val.as_ref());
        let (prev_present, prev_value) = umem_val_felt_v1(op.prev_val.as_ref());
        let mut row = vec![BabyBear::ZERO; width];
        row[0] = key;
        row[1] = present;
        row[2] = value;
        row[3] = prev_present;
        row[4] = prev_value;
        row[5] = BabyBear::new(op.prev_serial as u32);
        row[guard_col[&d]] = BabyBear::ONE;
        rows.push(row);
    }
    let height = rows.len().next_power_of_two().max(4);
    while rows.len() < height {
        rows.push(vec![BabyBear::ZERO; width]);
    }

    // The boundary: every touched address (strict-increasing by `(domain, key)`), with its
    // PRE-state cell as the init image.
    let mut addrs: Vec<(u32, BabyBear, Option<BabyBear>)> = touched
        .iter()
        .map(|(k, (d, key))| {
            let (present, value) = umem_val_felt_v1(pre.get(k));
            let init = if present == BabyBear::ONE {
                Some(value)
            } else {
                None
            };
            (*d, *key, init)
        })
        .collect();
    addrs.sort_by_key(|(d, k, _)| (*d, k.as_u32()));
    let boundary = UMemBoundaryWitness {
        addrs: addrs.iter().map(|(d, k, _)| (*d, *k)).collect(),
        init_vals: addrs.iter().map(|(_, _, v)| *v).collect(),
    };

    Ok(UmemWitnessInputsV1 {
        domains,
        rows,
        boundary,
    })
}

// The five `umem_*` / `UmemProvingInputs` compatibility aliases that stood here (a type alias
// plus four one-line forwards to the `_v1` names) are DELETED. Measured 2026-08-06: they had
// ZERO consumers between them except one test import, which now names `umem_proving_inputs_from_v1`
// directly. This repo's rule is that a no-op kept for compatibility is worse than one that does
// something, because the next reader trusts it — and here the un-suffixed spellings were exactly
// the ones a new call site would reach for while believing the width question was settled.

// ============================================================================
// UMEM-V2 FAITHFUL SOURCE MODEL
//
// V1 lowers an address and a value to one BabyBear each. It detects collisions
// inside one witness, but the wire representation itself cannot distinguish
// sources which reduce to the same field element. V2 is deliberately a new
// schema rather than a reinterpretation of V1: every source component remains
// visible as canonical 16-bit limbs. The later descriptor/VK epoch can permute
// these exact limbs and authenticate complete init/final boundary images.
// These types deliberately do NOT derive `Deserialize`: private fields are the
// canonical-construction wall, and serde derive would bypass presence/tag/
// length/padding validation. Phase B must introduce an explicitly validated
// protocol decoder together with its versioned wire schema.
//
// ⚑ V2 HAS A PRODUCTION CALLER AS OF 2026-08-06, AND IT IS NOT THE WIRE.
//
// `admit_value_v2` (above) is it: the shared checked witness derivation
// `umem_witness_inputs_from_v1`, called by both cohort generators and the compatibility producer,
// decides "are these two sources the same value?" by `UValV2` equality, and REFUSES a trace in which two distinct V2 sources land on one
// `(address, present, value)` felt cell. Until then V2 was a faithful codec with no caller, i.e.
// it was protecting nothing; the test file that says so in its own docblock is
// `turn/tests/umem_v2_faithful_codec.rs`.
//
// ⚑ WHAT ADOPTING V2 ON THE WIRE COSTS — priced, not deferred as unpriceable.
//
// The producer role above cost no emit because a REFUSAL is always in the host's gift: it changes
// no accepted trace's rows. Making the VERIFIER see V2's limbs is a different act, and it is a
// Lean-authored AIR change plus a VK epoch. The bill, read off the code rather than estimated:
//
//   * `DescriptorIR2`'s `UMemOp` — `circuit/src/descriptor_ir2.rs:688` `UMemOpSpec` types `key`,
//     `value`, `prev_value` as ONE `LeanExpr` each. V2 is 22 `u16` address limbs and a
//     4-limb-header + variable payload value. The Lean side (`Dregg2/Circuit/DescriptorIR2.lean`
//     and the `EffectVmEmitUMemCohort` / `EffectVmEmitUMemCohortMulti` emitters) is the author of
//     that shape; Rust only consumes it. So this is Lean work, not a Rust widening.
//   * The row geometry moves from width 7 (single-domain cohort: `key · present · value ·
//     prev_present · prev_value · prev_serial · guard`) to width `22 + header + payload + guard`,
//     and the multi-domain cohort's `6 + #domains` moves with it. A variable-length value payload
//     cannot back ONE committed VK, so the value limbs need a FIXED chunk ceiling chosen in Lean
//     — that choice is the real design content of the epoch, not the encoding.
//   * Re-emit: `circuit/descriptors/umem-cohort-*-staged-registry.tsv` and every registry row
//     that carries a `UMemOp`, then the VK, then a `VK-REGEN-LOG` row, then a re-genesis.
//   * The ENDIANNESS flip rides the same epoch: `UAddrV2::from_key` reads its source through
//     `bytes32_to_u16_be` while the canonical codec (`docs/DESIGN-canonical-byte-felt-codec.md`
//     §2.5, `dregg_codec::Limbs16`, the deployed `exact_nullifier_aafi::raw_to_u16_le`) is
//     little-endian. Pinned by `umem_v2_address_is_big_endian_the_one_divergence_from_the_canonical_le_codec`.
//     ⚠ That test's stated reason #3 for the flip being free — "V2 has no production caller" — is
//     now FALSE for values (the gate above) and still TRUE for addresses (`UAddrV2::from_key` has
//     no production caller). Flipping the address endianness today still costs nothing.

/// UMEM-V2 fixed address width: domain tag + variant tag + one exact 32-byte
/// source + one exact 64-bit argument block.
pub const UMEM_V2_ADDR_LIMBS: usize = 22;

/// Maximum canonical structured value accepted by the V2 host model. Blob
/// values are carried exactly, not Horner-folded; the explicit 64-KiB ceiling
/// bounds allocation and gives the circuit epoch a stable chunking limit.
pub const UMEM_V2_MAX_BLOB_BYTES: usize = 64 * 1024;

/// Host-side operation ceiling for one V2 turn witness. The future wire epoch
/// may choose a lower circuit geometry, but no untrusted caller can make this
/// correctness oracle replay an unbounded vector.
pub const UMEM_V2_MAX_OPS: usize = 65_536;

/// Host-side complete-image ceiling. This is deliberately much larger than one
/// practical proof cohort; scalable Phase-B paths will use authenticated
/// membership/non-membership rather than materializing a million-cell image.
pub const UMEM_V2_MAX_BOUNDARY_ENTRIES: usize = 1_048_576;

/// The four-limb header of a V2 value: presence, variant, byte-length high 16,
/// byte-length low 16.
pub const UMEM_V2_VALUE_HEADER_LIMBS: usize = 4;

/// Stable, source-level constructor tags for [`UKey`]. These are protocol
/// numbers for UMEM-V2, independent of Rust/serde enum discriminants.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u16)]
pub enum UKeyVariantV2 {
    Exist = 1,
    Field = 2,
    Balance = 3,
    Nonce = 4,
    ProvedState = 5,
    Lifecycle = 6,
    Mode = 7,
    Identity = 8,
    FieldVisibility = 9,
    FieldCommitment = 10,
    SwissTableRoot = 11,
    RefcountTableRoot = 12,
    SystemRoot = 13,
    HeapRoot = 14,
    Heap = 15,
    SovereignCommitment = 16,
    CapSlot = 17,
    Delegate = 18,
    DelegationSnapshot = 19,
    DelegationEpoch = 20,
    CommittedHeight = 21,
    Permissions = 22,
    VerificationKey = 23,
    Program = 24,
    Factory = 25,
    NoteNullifier = 26,
    BridgedNullifier = 27,
    Receipt = 28,
    Working = 29,
    CapTombstone = 30,
}

/// Stable UMEM-V2 value tags. Presence is an independent header limb, so
/// absence cannot alias any present value (including a zero-length blob).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u16)]
pub enum UValVariantV2 {
    Absent = 0,
    Present = 1,
    Int = 2,
    U64 = 3,
    Bool = 4,
    Bytes32 = 5,
    Blob = 6,
    UmemRef = 7,
}

/// Stable access-kind tags for the V2 permutation row.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u16)]
pub enum UmemKindV2 {
    Read = 0,
    Write = 1,
}

fn bytes32_to_u16_be(source: &[u8; 32]) -> [u16; 16] {
    let mut out = [0u16; 16];
    for (dst, pair) in out.iter_mut().zip(source.chunks_exact(2)) {
        *dst = u16::from_be_bytes([pair[0], pair[1]]);
    }
    out
}

fn u64_to_u16_be(source: u64) -> [u16; 4] {
    let bytes = source.to_be_bytes();
    [
        u16::from_be_bytes([bytes[0], bytes[1]]),
        u16::from_be_bytes([bytes[2], bytes[3]]),
        u16::from_be_bytes([bytes[4], bytes[5]]),
        u16::from_be_bytes([bytes[6], bytes[7]]),
    ]
}

fn u32_pair_to_u16_be(first: u32, second: u32) -> [u16; 4] {
    let a = first.to_be_bytes();
    let b = second.to_be_bytes();
    [
        u16::from_be_bytes([a[0], a[1]]),
        u16::from_be_bytes([a[2], a[3]]),
        u16::from_be_bytes([b[0], b[1]]),
        u16::from_be_bytes([b[2], b[3]]),
    ]
}

/// A faithful UMEM-V2 address. Derived ordering is the canonical raw-source
/// lexicographic order over `(domain, variant, source32 limbs, argument limbs)`;
/// no hash image or field reduction participates.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct UAddrV2 {
    domain: u16,
    variant: u16,
    source32: [u16; 16],
    arguments: [u16; 4],
}

impl UAddrV2 {
    /// Exact source encoding of one structured key.
    pub fn from_key(key: &UKey) -> Self {
        let domain = key.domain().code() as u16;
        let mut source32 = [0u16; 16];
        let mut arguments = [0u16; 4];

        let (variant, cell_or_source) = match key {
            UKey::Exist(cell) => (UKeyVariantV2::Exist, Some(cell.as_bytes())),
            UKey::Field { cell, slot } => {
                arguments = u64_to_u16_be(*slot);
                (UKeyVariantV2::Field, Some(cell.as_bytes()))
            }
            UKey::Balance(cell) => (UKeyVariantV2::Balance, Some(cell.as_bytes())),
            UKey::Nonce(cell) => (UKeyVariantV2::Nonce, Some(cell.as_bytes())),
            UKey::ProvedState(cell) => (UKeyVariantV2::ProvedState, Some(cell.as_bytes())),
            UKey::Lifecycle(cell) => (UKeyVariantV2::Lifecycle, Some(cell.as_bytes())),
            UKey::Mode(cell) => (UKeyVariantV2::Mode, Some(cell.as_bytes())),
            UKey::Identity(cell) => (UKeyVariantV2::Identity, Some(cell.as_bytes())),
            UKey::FieldVisibility { cell, slot } => {
                arguments = u64_to_u16_be(*slot);
                (UKeyVariantV2::FieldVisibility, Some(cell.as_bytes()))
            }
            UKey::FieldCommitment { cell, slot } => {
                arguments = u64_to_u16_be(*slot);
                (UKeyVariantV2::FieldCommitment, Some(cell.as_bytes()))
            }
            UKey::SwissTableRoot(cell) => (UKeyVariantV2::SwissTableRoot, Some(cell.as_bytes())),
            UKey::RefcountTableRoot(cell) => {
                (UKeyVariantV2::RefcountTableRoot, Some(cell.as_bytes()))
            }
            UKey::SystemRoot { cell, index } => {
                arguments = u64_to_u16_be(*index);
                (UKeyVariantV2::SystemRoot, Some(cell.as_bytes()))
            }
            UKey::HeapRoot(cell) => (UKeyVariantV2::HeapRoot, Some(cell.as_bytes())),
            UKey::Heap {
                cell,
                collection,
                key,
            } => {
                arguments = u32_pair_to_u16_be(*collection, *key);
                (UKeyVariantV2::Heap, Some(cell.as_bytes()))
            }
            UKey::SovereignCommitment(cell) => {
                (UKeyVariantV2::SovereignCommitment, Some(cell.as_bytes()))
            }
            UKey::CapSlot { cell, slot } => {
                arguments = u32_pair_to_u16_be(*slot, 0);
                (UKeyVariantV2::CapSlot, Some(cell.as_bytes()))
            }
            UKey::Delegate(cell) => (UKeyVariantV2::Delegate, Some(cell.as_bytes())),
            UKey::DelegationSnapshot(cell) => {
                (UKeyVariantV2::DelegationSnapshot, Some(cell.as_bytes()))
            }
            UKey::DelegationEpoch(cell) => (UKeyVariantV2::DelegationEpoch, Some(cell.as_bytes())),
            UKey::CommittedHeight(cell) => (UKeyVariantV2::CommittedHeight, Some(cell.as_bytes())),
            UKey::Permissions(cell) => (UKeyVariantV2::Permissions, Some(cell.as_bytes())),
            UKey::VerificationKey(cell) => (UKeyVariantV2::VerificationKey, Some(cell.as_bytes())),
            UKey::Program(cell) => (UKeyVariantV2::Program, Some(cell.as_bytes())),
            UKey::Factory(source) => (UKeyVariantV2::Factory, Some(source)),
            UKey::NoteNullifier(source) => (UKeyVariantV2::NoteNullifier, Some(source)),
            UKey::BridgedNullifier(source) => (UKeyVariantV2::BridgedNullifier, Some(source)),
            UKey::Receipt(position) => {
                arguments = u64_to_u16_be(*position);
                (UKeyVariantV2::Receipt, None)
            }
            UKey::Working {
                service,
                collection,
                key,
            } => {
                arguments = u32_pair_to_u16_be(*collection, *key);
                (UKeyVariantV2::Working, Some(service.as_bytes()))
            }
            UKey::CapTombstone { cell, slot } => {
                arguments = u32_pair_to_u16_be(*slot, 0);
                (UKeyVariantV2::CapTombstone, Some(cell.as_bytes()))
            }
        };
        if let Some(source) = cell_or_source {
            source32 = bytes32_to_u16_be(source);
        }
        Self {
            domain,
            variant: variant as u16,
            source32,
            arguments,
        }
    }

    /// Canonical fixed-width limb image, suitable for a wide permutation/sort.
    pub fn limbs(self) -> [u16; UMEM_V2_ADDR_LIMBS] {
        let mut out = [0u16; UMEM_V2_ADDR_LIMBS];
        out[0] = self.domain;
        out[1] = self.variant;
        out[2..18].copy_from_slice(&self.source32);
        out[18..22].copy_from_slice(&self.arguments);
        out
    }

    pub const fn domain(self) -> u16 {
        self.domain
    }

    pub const fn variant(self) -> u16 {
        self.variant
    }
}

fn pack_bytes_u16_be(source: &[u8]) -> Box<[u16]> {
    let mut out = Vec::with_capacity(source.len().div_ceil(2));
    for pair in source.chunks(2) {
        out.push(u16::from_be_bytes([
            pair[0],
            pair.get(1).copied().unwrap_or(0),
        ]));
    }
    out.into_boxed_slice()
}

fn validate_v2_value_bound(value: Option<&UVal>) -> Result<(), UmemV2Error> {
    if let Some(UVal::Blob(blob)) = value
        && blob.len() > UMEM_V2_MAX_BLOB_BYTES
    {
        return Err(UmemV2Error::BlobTooLarge {
            len: blob.len(),
            max: UMEM_V2_MAX_BLOB_BYTES,
        });
    }
    Ok(())
}

/// A faithful, bounded optional UMEM-V2 value. All fields are private so only
/// canonical encodings can be constructed: an odd final source byte always
/// occupies the high half of its last limb and the unused low half is zero.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct UValV2 {
    presence: u16,
    variant: u16,
    source_byte_len: u32,
    payload: Box<[u16]>,
}

impl UValV2 {
    /// Encode an optional source value without reduction or type erasure, subject to the
    /// [`UMEM_V2_MAX_BLOB_BYTES`] admission.
    pub fn try_from_value(value: Option<&UVal>) -> Result<Self, UmemV2Error> {
        validate_v2_value_bound(value)?;
        Ok(Self::encode_canonical(value))
    }

    /// **The canonical encoding WITHOUT the blob ceiling** — the same bytes
    /// [`UValV2::try_from_value`] produces, minus its size admission.
    ///
    /// The two are deliberately separate concerns and this split exists so a caller cannot
    /// acquire one by asking for the other:
    ///
    /// * the CANONICAL ENCODING is what makes two sources distinguishable (presence, variant tag,
    ///   exact byte length, exact `u16` payload limbs);
    /// * [`UMEM_V2_MAX_BLOB_BYTES`] is a **host-model replay ceiling** — its own doc says it
    ///   "bounds allocation and gives the circuit epoch a stable chunking limit" for
    ///   [`UmemBoundaryV2::from_full_image`], which materialises a whole image.
    ///
    /// ⚠ **The producer's value gate ([`admit_value_v2`]) MUST NOT inherit that ceiling**, and
    /// this is the reason the split is not cosmetic: `project_cell` stores a cell's `Program` and
    /// `VerificationKey` planes as `json(...)` → `UVal::Blob`, neither of which is bounded by
    /// 64 KiB. Routing the deployed producer through `try_from_value` would therefore have made a
    /// SOUNDNESS gate refuse honest turns on any cell with a large program or VK — an availability
    /// cliff introduced by a fix for a collision. The gate needs the encoding, not the ceiling.
    pub fn encode_canonical(value: Option<&UVal>) -> Self {
        let (presence, variant, source): (u16, UValVariantV2, Vec<u8>) = match value {
            None => (0, UValVariantV2::Absent, Vec::new()),
            Some(UVal::Present) => (1, UValVariantV2::Present, Vec::new()),
            Some(UVal::Int(v)) => (1, UValVariantV2::Int, v.to_be_bytes().to_vec()),
            Some(UVal::U64(v)) => (1, UValVariantV2::U64, v.to_be_bytes().to_vec()),
            Some(UVal::Bool(v)) => (1, UValVariantV2::Bool, vec![u8::from(*v)]),
            Some(UVal::Bytes32(v)) => (1, UValVariantV2::Bytes32, v.to_vec()),
            Some(UVal::Blob(v)) => (1, UValVariantV2::Blob, v.clone()),
            Some(UVal::UmemRef(v)) => (1, UValVariantV2::UmemRef, v.to_vec()),
        };
        // A umem value at or past 4 GiB is not a reachable input (it would have to be a single
        // `UVal` already materialised in the projection); fail loudly rather than truncate the
        // length limb, which would alias two sources.
        let source_byte_len = u32::try_from(source.len()).expect("a umem value fits u32 bytes");
        Self {
            presence,
            variant: variant as u16,
            source_byte_len,
            payload: pack_bytes_u16_be(&source),
        }
    }

    pub const fn presence(&self) -> u16 {
        self.presence
    }

    pub const fn variant(&self) -> u16 {
        self.variant
    }

    pub const fn source_byte_len(&self) -> u32 {
        self.source_byte_len
    }

    pub fn payload(&self) -> &[u16] {
        &self.payload
    }

    /// Header followed by the exact source payload limbs. This is the canonical
    /// sequence the V2 permutation and boundary-root leaf will authenticate.
    pub fn canonical_limbs(&self) -> Vec<u16> {
        let mut out = Vec::with_capacity(UMEM_V2_VALUE_HEADER_LIMBS + self.payload.len());
        out.push(self.presence);
        out.push(self.variant);
        out.push((self.source_byte_len >> 16) as u16);
        out.push(self.source_byte_len as u16);
        out.extend_from_slice(&self.payload);
        out
    }

    /// Recover the exact source bytes (the inverse of the canonical packing).
    pub fn source_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.payload.len() * 2);
        for limb in &self.payload {
            out.extend_from_slice(&limb.to_be_bytes());
        }
        out.truncate(self.source_byte_len as usize);
        out
    }
}

/// One exact UMEM-V2 permutation row. Both serials retain all 64 source bits;
/// V1's `prev_serial as u32` truncation is intentionally not reproduced.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UmemOpV2 {
    pub kind: UmemKindV2,
    pub addr: UAddrV2,
    pub value: UValV2,
    pub prev_value: UValV2,
    serial: [u16; 4],
    prev_serial: [u16; 4],
}

impl UmemOpV2 {
    fn try_from_op(index: usize, op: &UmemOp) -> Result<Self, UmemV2Error> {
        Ok(Self {
            kind: match op.kind {
                UmemKind::Read => UmemKindV2::Read,
                UmemKind::Write => UmemKindV2::Write,
            },
            addr: UAddrV2::from_key(&op.key),
            value: UValV2::try_from_value(op.val.as_ref())?,
            prev_value: UValV2::try_from_value(op.prev_val.as_ref())?,
            serial: u64_to_u16_be(index as u64 + 1),
            prev_serial: u64_to_u16_be(op.prev_serial),
        })
    }

    pub const fn serial_limbs(&self) -> [u16; 4] {
        self.serial
    }

    pub const fn prev_serial_limbs(&self) -> [u16; 4] {
        self.prev_serial
    }
}

/// One address in the complete V2 boundary image, carrying both endpoint
/// values. The final value is not witness-declared independently: the producer
/// obtains it by exact replay of the structured operations.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UmemBoundaryEntryV2 {
    pub addr: UAddrV2,
    pub init: UValV2,
    pub final_value: UValV2,
}

/// The complete UMEM-V2 init/final image, canonically sorted by faithful raw
/// address. Unlike V1's touched-address witness, this model includes the union
/// of every address in the pre and replayed-final projections. Phase B will
/// authenticate these endpoints (or replace the materialized image with exact
/// membership/non-membership paths) and bind them to rotated public roots.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UmemBoundaryV2 {
    entries: Vec<UmemBoundaryEntryV2>,
}

/// Exact V2 permutation rows plus the complete init/final correctness-oracle
/// image. This is additive host substrate, not yet proof authority: Phase B
/// must authenticate the endpoint roots and weld every row to host semantics.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UmemTraceV2 {
    ops: Vec<UmemOpV2>,
    boundary: UmemBoundaryV2,
}

impl UmemTraceV2 {
    pub fn from_witness(witness: &UmemTurnWitness) -> Result<Self, UmemV2Error> {
        let boundary = UmemBoundaryV2::from_witness(witness)?;
        let ops = witness
            .ops
            .iter()
            .enumerate()
            .map(|(index, op)| UmemOpV2::try_from_op(index, op))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { ops, boundary })
    }

    pub fn ops(&self) -> &[UmemOpV2] {
        &self.ops
    }

    pub const fn boundary(&self) -> &UmemBoundaryV2 {
        &self.boundary
    }
}

impl UmemBoundaryV2 {
    /// Canonicalize a complete image and refuse repeated raw addresses. This is
    /// public primarily for descriptor/proof assembly and hostile duplicate
    /// tests; normal turn code should use [`UmemBoundaryV2::from_witness`].
    pub fn try_from_entries(mut entries: Vec<UmemBoundaryEntryV2>) -> Result<Self, UmemV2Error> {
        if entries.len() > UMEM_V2_MAX_BOUNDARY_ENTRIES {
            return Err(UmemV2Error::BoundaryTooLarge {
                len: entries.len(),
                max: UMEM_V2_MAX_BOUNDARY_ENTRIES,
            });
        }
        entries.sort_by_key(|entry| entry.addr);
        for pair in entries.windows(2) {
            if pair[0].addr == pair[1].addr {
                return Err(UmemV2Error::DuplicateAddress(pair[0].addr));
            }
        }
        Ok(Self { entries })
    }

    /// Build the full endpoint image after checking exact prior-value and
    /// prior-serial claims and replaying every operation.
    pub fn from_full_image(pre: &UProjection, ops: &[UmemOp]) -> Result<Self, UmemV2Error> {
        if ops.is_empty() {
            return Err(UmemV2Error::EmptyTrace);
        }
        if ops.len() > UMEM_V2_MAX_OPS {
            return Err(UmemV2Error::TooManyOperations {
                len: ops.len(),
                max: UMEM_V2_MAX_OPS,
            });
        }
        if pre.len() > UMEM_V2_MAX_BOUNDARY_ENTRIES {
            return Err(UmemV2Error::BoundaryTooLarge {
                len: pre.len(),
                max: UMEM_V2_MAX_BOUNDARY_ENTRIES,
            });
        }
        for value in pre.values() {
            validate_v2_value_bound(Some(value))?;
        }
        for op in ops {
            validate_v2_value_bound(op.val.as_ref())?;
            validate_v2_value_bound(op.prev_val.as_ref())?;
        }

        let mut current: BTreeMap<UKey, Option<UVal>> = BTreeMap::new();
        let mut last_serial: BTreeMap<UKey, u64> = BTreeMap::new();
        for (index, op) in ops.iter().enumerate() {
            let expected_value = current
                .get(&op.key)
                .cloned()
                .unwrap_or_else(|| pre.get(&op.key).cloned());
            if op.prev_val != expected_value {
                return Err(UmemV2Error::PreviousValueMismatch {
                    index,
                    key: op.key.clone(),
                });
            }
            let expected_serial = last_serial.get(&op.key).copied().unwrap_or(0);
            if op.prev_serial != expected_serial {
                return Err(UmemV2Error::PreviousSerialMismatch {
                    index,
                    key: op.key.clone(),
                    expected: expected_serial,
                    actual: op.prev_serial,
                });
            }
            if op.kind == UmemKind::Read && op.val != expected_value {
                return Err(UmemV2Error::ReadValueMismatch {
                    index,
                    key: op.key.clone(),
                });
            }
            if op.kind == UmemKind::Write {
                current.insert(op.key.clone(), op.val.clone());
            }
            last_serial.insert(op.key.clone(), index as u64 + 1);
        }

        let final_image = fold(pre, ops);
        let mut all_keys: Vec<UKey> = pre
            .keys()
            .chain(final_image.keys())
            .chain(ops.iter().map(|op| &op.key))
            .cloned()
            .collect();
        all_keys.sort();
        all_keys.dedup();
        if all_keys.len() > UMEM_V2_MAX_BOUNDARY_ENTRIES {
            return Err(UmemV2Error::BoundaryTooLarge {
                len: all_keys.len(),
                max: UMEM_V2_MAX_BOUNDARY_ENTRIES,
            });
        }

        // This map is an executable injectivity gate. It should be unreachable
        // for the exact source layout, but keeps future schema extensions from
        // silently reusing a tag/field position.
        let mut encoded_keys: BTreeMap<UAddrV2, UKey> = BTreeMap::new();
        let mut entries = Vec::with_capacity(all_keys.len());
        for key in all_keys {
            let addr = UAddrV2::from_key(&key);
            if let Some(previous) = encoded_keys.insert(addr, key.clone())
                && previous != key
            {
                return Err(UmemV2Error::AddressCollision {
                    addr,
                    first: previous,
                    second: key,
                });
            }
            entries.push(UmemBoundaryEntryV2 {
                addr,
                init: UValV2::try_from_value(pre.get(&key))?,
                final_value: UValV2::try_from_value(final_image.get(&key))?,
            });
        }
        Self::try_from_entries(entries)
    }

    /// Build from an executor witness and require its declared post projection
    /// to equal the exact replay, rather than trusting the co-located post image.
    pub fn from_witness(witness: &UmemTurnWitness) -> Result<Self, UmemV2Error> {
        // Validate the operation/image/value bounds before replaying the
        // caller-supplied trace.  `from_full_image` performs that fail-closed
        // admission and its own replay; only after admission do we independently
        // compare the co-located post image.
        let boundary = Self::from_full_image(&witness.pre, &witness.ops)?;
        if fold(&witness.pre, &witness.ops) != witness.post {
            return Err(UmemV2Error::PostReplayMismatch);
        }
        Ok(boundary)
    }

    pub fn entries(&self) -> &[UmemBoundaryEntryV2] {
        &self.entries
    }
}

/// Fail-closed UMEM-V2 construction errors.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UmemV2Error {
    EmptyTrace,
    BlobTooLarge {
        len: usize,
        max: usize,
    },
    TooManyOperations {
        len: usize,
        max: usize,
    },
    BoundaryTooLarge {
        len: usize,
        max: usize,
    },
    DuplicateAddress(UAddrV2),
    AddressCollision {
        addr: UAddrV2,
        first: UKey,
        second: UKey,
    },
    PreviousValueMismatch {
        index: usize,
        key: UKey,
    },
    PreviousSerialMismatch {
        index: usize,
        key: UKey,
        expected: u64,
        actual: u64,
    },
    ReadValueMismatch {
        index: usize,
        key: UKey,
    },
    PostReplayMismatch,
}

impl std::fmt::Display for UmemV2Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyTrace => write!(f, "umem-v2: empty operation trace"),
            Self::BlobTooLarge { len, max } => {
                write!(f, "umem-v2: blob length {len} exceeds bound {max}")
            }
            Self::TooManyOperations { len, max } => {
                write!(f, "umem-v2: operation count {len} exceeds bound {max}")
            }
            Self::BoundaryTooLarge { len, max } => {
                write!(f, "umem-v2: boundary size {len} exceeds bound {max}")
            }
            Self::DuplicateAddress(addr) => {
                write!(f, "umem-v2: duplicate boundary address {addr:?}")
            }
            Self::AddressCollision {
                addr,
                first,
                second,
            } => write!(
                f,
                "umem-v2: schema collision at {addr:?}: {first:?} aliases {second:?}"
            ),
            Self::PreviousValueMismatch { index, key } => write!(
                f,
                "umem-v2: op {index} prior value does not match replay at {key:?}"
            ),
            Self::PreviousSerialMismatch {
                index,
                key,
                expected,
                actual,
            } => write!(
                f,
                "umem-v2: op {index} prior serial {actual} != replay {expected} at {key:?}"
            ),
            Self::ReadValueMismatch { index, key } => write!(
                f,
                "umem-v2: read op {index} does not return replay value at {key:?}"
            ),
            Self::PostReplayMismatch => {
                write!(f, "umem-v2: declared post image differs from exact replay")
            }
        }
    }
}

impl std::error::Error for UmemV2Error {}

/// The FIXED per-effect COHORT proving inputs: the single-domain width-7 rows + the real
/// [`UMemBoundaryWitness`] the deployed single-domain WELD consumes
/// ([`dregg_circuit::effect_vm_descriptors::weld_umem_into_wide_descriptor`] — the `umemOp` the
/// Lean `EffectVmEmitUMemCohort.umemCohortDesc` models). A variable-shape AIR cannot back ONE
/// committed VK, so the deployed umem form is the FIXED cohort (per-effect, single-domain,
/// width-7, ONE `umemOp` guarded at column 6); a real multi-effect / multi-cell turn proves as
/// per-effect fixed-cohort legs (one per effect-touch), exactly as the deployed rotated prover
/// already routes one descriptor per leg ([`dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect`]).
#[derive(Clone, Debug)]
pub struct UmemCohortProvingInputs {
    /// The single domain code every op in this leg touches — MUST equal the resolved cohort
    /// descriptor's baked-in `domain` (the caller fails closed on a mismatch).
    pub domain: u32,
    /// Width-7 cohort rows: `0 key · 1 present · 2 value · 3 prev_present · 4 prev_value ·
    /// 5 prev_serial · 6 guard`. Byte-identical to the single-domain producer rows.
    pub rows: Vec<Vec<BabyBear>>,
    /// The REAL universal-memory boundary for this single-domain leg (touched addresses with
    /// their PRE-state init image).
    pub boundary: UMemBoundaryWitness,
}

/// **THE FIXED-COHORT TRACE GENERATOR** — bridge one effect-leg's umem op trace into the FIXED
/// per-effect cohort form the deployed-form umem prover ([`prove_vm_descriptor2_umem`]) accepts.
///
/// Shares checked row and boundary derivation with the arbitrary-domain compatibility
/// producer. The single domain comes from explicit sorted metadata, not from inspecting a
/// temporary Rust-authored descriptor. Multi-domain legs fail closed here and use the
/// multi-domain adapter. The domain remains available to callers for cohort selection,
/// shape checks and weld construction.
///
/// `Err` if the leg is empty, the address codec collides, or the leg is multi-domain.
///
/// [`prove_vm_descriptor2_umem`]: dregg_circuit::descriptor_ir2::prove_vm_descriptor2_umem
pub fn umem_cohort_proving_inputs_from(
    pre: &UProjection,
    ops: &[UmemOp],
) -> Result<UmemCohortProvingInputs, String> {
    let inputs = umem_witness_inputs_from_v1(pre, ops)?;
    if inputs.domains.len() != 1 {
        return Err(format!(
            "umem cohort generator: leg touches {} domains (producer width {}); the fixed cohort \
             descriptor is single-domain (width 7) — multi-domain effects stay on the per-map path",
            inputs.domains.len(),
            6 + inputs.domains.len()
        ));
    }
    let domain = inputs.domains[0];
    Ok(UmemCohortProvingInputs {
        domain,
        rows: inputs.rows,
        boundary: inputs.boundary,
    })
}

/// The FIXED per-effect MULTI-DOMAIN cohort proving inputs: the producer's multi-domain rows +
/// the real [`UMemBoundaryWitness`] the deployed-form FIXED multi-domain cohort descriptor
/// (`circuit/descriptors/umem-cohort-multidomain-v1-staged-registry.tsv`, the Lean
/// `EffectVmEmitUMemCohortMulti.umemCohortMultiRegistry`) consumes, plus the touched domains in
/// COLUMN order (guard column `6 + i` for the `i`-th domain, the producer's sorted-domain-code
/// order). Completes the cohort to the effects whose state touch spans MORE THAN ONE domain in one
/// effect (the NOTE/BRIDGE economic verbs — a `nullifiers`-domain freshness insert + a
/// `heap`-domain balance write), on which [`umem_cohort_proving_inputs_from`] fails closed.
#[derive(Clone, Debug)]
pub struct UmemCohortMultiProvingInputs {
    /// The touched domain codes in COLUMN order (guard column `6 + i`). MUST equal the resolved
    /// multi-domain cohort descriptor's per-op domains in order (the caller fails closed on a
    /// mismatch — the descriptor carries the FIXED domain set its committed VK backs).
    pub domains: Vec<u32>,
    /// Width-`6 + #domains` cohort rows: `0 key · 1 present · 2 value · 3 prev_present ·
    /// 4 prev_value · 5 prev_serial` shared, `6 + i` the per-domain guard. Byte-identical to the
    /// producer rows.
    pub rows: Vec<Vec<BabyBear>>,
    /// The REAL universal-memory boundary for this multi-domain leg (touched addresses across all
    /// domains with their PRE-state init image).
    pub boundary: UMemBoundaryWitness,
}

/// **THE FIXED MULTI-DOMAIN COHORT TRACE GENERATOR** — bridge one effect-leg's multi-domain umem op
/// trace into the FIXED per-effect multi-domain cohort form the deployed-form umem prover
/// ([`prove_vm_descriptor2_umem`]) accepts. Unlike [`umem_cohort_proving_inputs_from`] (which fails
/// closed on a multi-domain leg), this generator yields checked rows and boundary directly.
/// The sorted domain metadata fixes guard columns `6 + i` without constructing a temporary
/// descriptor. The ordered domain set remains available to callers for cohort selection,
/// shape checks and weld construction.
///
/// `Err` if the leg is empty, the address codec collides, or the leg touches FEWER than two domains
/// (a single-domain leg belongs on the width-7 cohort — [`umem_cohort_proving_inputs_from`]).
///
/// [`prove_vm_descriptor2_umem`]: dregg_circuit::descriptor_ir2::prove_vm_descriptor2_umem
pub fn umem_cohort_multidomain_proving_inputs_from(
    pre: &UProjection,
    ops: &[UmemOp],
) -> Result<UmemCohortMultiProvingInputs, String> {
    let UmemWitnessInputsV1 {
        domains,
        rows,
        boundary,
    } = umem_witness_inputs_from_v1(pre, ops)?;
    if domains.len() < 2 {
        return Err(format!(
            "umem multi-domain cohort generator: leg touches {} domain(s) (producer width {}); the \
             multi-domain cohort is for effects spanning >1 domain — a single-domain leg uses the \
             width-7 cohort (umem_cohort_proving_inputs_from)",
            domains.len(),
            6 + domains.len()
        ));
    }
    Ok(UmemCohortMultiProvingInputs {
        domains,
        rows,
        boundary,
    })
}

/// The pre→post projection DIFF as a Blum write trace: every address whose value changed
/// (insert / update / delete), emitted as a same-transition [`UmemOp::Write`] with the PRE
/// value as `prev_val` and `prev_serial == 0` (each touched address is opened once against the
/// init image). The canonical key-union diff the welded-cohort legs lower — sharing it keeps the
/// producer's row/boundary derivation in lockstep with its callers (no hand-inlined twin to
/// drift).
pub fn project_diff_ops(pre: &UProjection, post: &UProjection) -> Vec<UmemOp> {
    let mut keys: Vec<UKey> = pre.keys().chain(post.keys()).cloned().collect();
    keys.sort();
    keys.dedup();
    let mut ops = Vec::new();
    for k in keys {
        let a = pre.get(&k);
        let b = post.get(&k);
        if a != b {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k,
                val: b.cloned(),
                prev_val: a.cloned(),
                prev_serial: 0,
            });
        }
    }
    ops
}

/// A journal entry's address touches: `(key, recorded_prev)` where
/// `recorded_prev = Some(cell)` when the journal recorded the prior value
/// (`Some(None)` = recorded-absent, e.g. a fresh capability slot) and `None` when the
/// entry doesn't carry it (the emitter falls back to the running fold value, which the
/// memory semantics guarantees is the truth whenever the trace is genuine).
enum Touch {
    At(UKey, Option<Option<UVal>>),
    /// A `CreateCell` bundle birth: expanded against the post-state into every plane of
    /// the born cell (all with recorded-absent prevs — the freshness gate).
    CreateCell(CellId),
}

fn touches_of_entry(e: &JournalEntry) -> Vec<Touch> {
    match e {
        // PQ identity is committed through the cell authority residue, outside
        // the current universal-memory key planes.  The Effect-VM bridge
        // refuses to claim a proved RotatePqIdentity row until that authority
        // plane exists; the runtime journal still provides atomic rollback and
        // durable touched-cell capture.
        JournalEntry::SetPqIdentity { .. } => Vec::new(),
        JournalEntry::SetField {
            cell,
            index,
            old_value,
            ..
        } => vec![Touch::At(
            UKey::Field {
                cell: *cell,
                slot: *index,
            },
            Some(old_value.map(|v| UVal::Bytes32(v))),
        )],
        JournalEntry::SetBalance { cell, old_balance } => vec![Touch::At(
            UKey::Balance(*cell),
            Some(Some(UVal::Int(*old_balance))),
        )],
        JournalEntry::SetNonce { cell, old_nonce } => vec![Touch::At(
            UKey::Nonce(*cell),
            Some(Some(UVal::U64(*old_nonce))),
        )],
        JournalEntry::GrantCapability { cell, slot } => vec![Touch::At(
            UKey::CapSlot {
                cell: *cell,
                slot: *slot,
            },
            Some(None), // a grant claims a FRESH slot
        )],
        JournalEntry::RevokeCapability { cell, old_cap } => vec![
            // the live slot is removed (prev = the revoked cap json, post = absent)
            Touch::At(
                UKey::CapSlot {
                    cell: *cell,
                    slot: old_cap.slot,
                },
                Some(Some(json(old_cap))),
            ),
            // AND its ghost tombstone is recorded (prev = absent, post = Present) —
            // the deployed `cap_root` keeps a ZERO leaf at the revoked slot, so the
            // projection's tombstone plane must carry it (see `CapTombstone`).
            Touch::At(
                UKey::CapTombstone {
                    cell: *cell,
                    slot: old_cap.slot,
                },
                Some(None),
            ),
        ],
        JournalEntry::SetHeap {
            cell,
            collection,
            key,
            old_value,
        } => vec![Touch::At(
            UKey::Heap {
                cell: *cell,
                collection: *collection,
                key: *key,
            },
            Some(old_value.map(UVal::Bytes32)),
        )],
        JournalEntry::CreateCell { cell } => vec![Touch::CreateCell(*cell)],
        JournalEntry::SetProvedState { cell, old_value } => vec![Touch::At(
            UKey::ProvedState(*cell),
            Some(Some(UVal::Bool(*old_value))),
        )],
        JournalEntry::SetPermissions {
            cell,
            old_permissions,
        } => vec![Touch::At(
            UKey::Permissions(*cell),
            Some(Some(json(old_permissions))),
        )],
        JournalEntry::SetVerificationKey { cell, old_vk } => vec![Touch::At(
            UKey::VerificationKey(*cell),
            Some(old_vk.as_ref().map(json)),
        )],
        JournalEntry::SetProgram { cell, old_program } => vec![Touch::At(
            UKey::Program(*cell),
            Some(Some(json(old_program))),
        )],
        JournalEntry::SetDelegation {
            cell,
            old_delegation,
        } => vec![Touch::At(
            UKey::DelegationSnapshot(*cell),
            Some(old_delegation.as_ref().map(json)),
        )],
        JournalEntry::SetDelegationEpoch { cell, old_epoch } => vec![Touch::At(
            UKey::DelegationEpoch(*cell),
            Some(Some(UVal::U64(*old_epoch))),
        )],
        JournalEntry::SetCommittedHeight { cell, old_height } => vec![Touch::At(
            UKey::CommittedHeight(*cell),
            Some(Some(UVal::U64(*old_height))),
        )],
        JournalEntry::SetLifecycle {
            cell,
            old_lifecycle,
        } => {
            // a lifecycle transition can also be a destroy — same plane (the lifecycle
            // object carries the death certificate; see the projection table).
            let _: &CellLifecycle = old_lifecycle;
            vec![Touch::At(
                UKey::Lifecycle(*cell),
                Some(Some(json(old_lifecycle))),
            )]
        }
        JournalEntry::AttenuateCapability { cell, slot, .. } => vec![Touch::At(
            UKey::CapSlot {
                cell: *cell,
                slot: *slot,
            },
            None, // partial old fields recorded; prev = the running fold value
        )],
        JournalEntry::NoteNullifierInserted { nullifier } => vec![Touch::At(
            UKey::NoteNullifier(nullifier.0),
            Some(None), // freshness IS the double-spend gate
        )],
        JournalEntry::BridgedNullifierInserted { nullifier } => {
            vec![Touch::At(UKey::BridgedNullifier(*nullifier), Some(None))]
        }
        // Markers / receipt-surface entries: no state cell. `NoteCommitmentInserted`
        // is a no-touch marker for now: the commitments accumulator is committed via
        // the rotated `commitments_root` group, but is not yet a umem-projected domain
        // (`project_executor_state` does not walk `note_commitments`), so emitting a
        // touch here would break the agreement square. A NAMED SEAM, like the heap
        // domain's staged wiring — the CREATE-side dual of `UKey::NoteNullifier`.
        // `RevocationInserted` is the same NAMED SEAM on the revocation side: the
        // `note_revoked` accumulator commits via the rotated `revoked_root` group but
        // `project_executor_state` does not walk it, so it too is a no-touch marker.
        JournalEntry::NoteSpend
        | JournalEntry::NoteCreate
        | JournalEntry::NoteCommitmentInserted { .. }
        | JournalEntry::ReactiveRegistrySnapshot { .. }
        | JournalEntry::ReactiveNullifierInserted { .. }
        | JournalEntry::RevocationInserted { .. }
        // A shielded-note append into `note_shielded` commits via its own
        // accumulator root8() (L1 carrier limb), not walked by
        // `project_executor_state` — a no-touch marker like its siblings.
        | JournalEntry::ShieldedNoteInserted { .. } => vec![],
        JournalEntry::EventEmitted { .. } => vec![],
        // NAMED SEAM: a MakeSovereign REMOVES a hosted cell (lifts its whole state
        // out of the ledger). That is a multi-key erasure (every UKey of the cell
        // goes absent) with no single-`Touch` representation, and hosted-cell
        // removal is not yet a umem-projected domain — like the note-accumulator
        // markers above. No touch is emitted (matching the pre-tombstone behavior,
        // where make_sovereign journaled nothing at all), so the umem agreement
        // square does not cover MakeSovereign turns. The durable-recovery soundness
        // of the removal is carried by `CommitRecord.removed` / `cell_overlay_since`
        // (bug #57), independent of the umem projection.
        JournalEntry::MakeSovereign { .. } => vec![],
    }
}

/// **THE TRACE EMITTER** — re-read the executed turn's journal as its Blum write trace.
///
/// Guarantees on success:
///  * `fold(pre, ops) == post` (the agreement square, checked here — the executable
///    shadow of the Lean `*_is_memory_program` keystones);
///  * `disciplined(&ops)` (the per-op memcheck discipline);
///  * every journal-recorded prior value MATCHED the running fold (journal ⟷ projection
///    drift refuses loudly with a named address);
///  * `synthesized` counts diff-covered addresses no journal entry named (state
///    surfaces that mutate without per-address journaling — `0` on the
///    transfer/set-field/capability lanes).
pub(crate) fn emit_trace(
    pre: &UProjection,
    post: &UProjection,
    entries: &[JournalEntry],
) -> Result<UmemTurnWitness, String> {
    // 1. Expand journal entries into ordered address touches.
    let mut touches: Vec<(UKey, Option<Option<UVal>>)> = Vec::new();
    for e in entries {
        for t in touches_of_entry(e) {
            match t {
                Touch::At(k, p) => touches.push((k, p)),
                Touch::CreateCell(cell) => {
                    // the bundle birth: every post-state plane of the born cell, each
                    // with a recorded-absent prev (the freshness gate; Lean
                    // `createTrace` claims `prevVal = none` for the same reason).
                    for (k, _) in post.iter() {
                        if k.cell() == Some(cell) {
                            touches.push((k.clone(), Some(None)));
                        }
                    }
                }
            }
        }
    }

    // 2. Per-address touch positions, in order.
    let mut positions: BTreeMap<UKey, Vec<usize>> = BTreeMap::new();
    for (i, (k, _)) in touches.iter().enumerate() {
        positions.entry(k.clone()).or_default().push(i);
    }

    // 3. Emit ops: prev = recorded prior (cross-checked) or the running fold value;
    //    val = the NEXT touch's recorded prior, or the post-state cell for the last
    //    touch of each address.
    let mut current: BTreeMap<UKey, Option<UVal>> = BTreeMap::new();
    let mut last_serial: BTreeMap<UKey, u64> = BTreeMap::new();
    let mut ops: Vec<UmemOp> = Vec::new();
    for (i, (k, recorded_prev)) in touches.iter().enumerate() {
        let fold_prev: Option<UVal> = match current.get(k) {
            Some(v) => v.clone(),
            None => pre.get(k).cloned(),
        };
        let prev_val = match recorded_prev {
            Some(recorded) => {
                if *recorded != fold_prev {
                    return Err(format!(
                        "umem trace drift at {k:?}: journal recorded prior {recorded:?} \
                         but the projection fold carries {fold_prev:?}"
                    ));
                }
                recorded.clone()
            }
            None => fold_prev,
        };
        let my_positions = &positions[k];
        let my_idx = my_positions
            .iter()
            .position(|p| *p == i)
            .expect("position index");
        let val: Option<UVal> = if my_idx + 1 < my_positions.len() {
            // the next touch's recorded prior is this op's installed value when known;
            // otherwise install the post value (a sound coarsening: the fold agrees).
            match &touches[my_positions[my_idx + 1]].1 {
                Some(recorded_next) => recorded_next.clone(),
                None => post.get(k).cloned(),
            }
        } else {
            post.get(k).cloned()
        };
        let prev_serial = last_serial.get(k).copied().unwrap_or(0);
        last_serial.insert(k.clone(), (i as u64) + 1);
        current.insert(k.clone(), val.clone());
        ops.push(UmemOp {
            kind: UmemKind::Write,
            key: k.clone(),
            val,
            prev_val,
            prev_serial,
        });
    }

    // 4. Coverage: any pre/post difference not named by the journal becomes a
    //    synthesized trailing write (totality), counted honestly.
    let mut synthesized = 0usize;
    let mut diff_keys: Vec<UKey> = Vec::new();
    for (k, v) in post.iter() {
        if pre.get(k) != Some(v) && !positions.contains_key(k) {
            diff_keys.push(k.clone());
        }
    }
    for (k, _) in pre.iter() {
        if !post.contains_key(k) && !positions.contains_key(k) {
            diff_keys.push(k.clone());
        }
    }
    diff_keys.sort();
    diff_keys.dedup();
    for k in diff_keys {
        let serial_base = ops.len() as u64;
        let _ = serial_base;
        ops.push(UmemOp {
            kind: UmemKind::Write,
            key: k.clone(),
            val: post.get(&k).cloned(),
            prev_val: pre.get(&k).cloned(),
            prev_serial: last_serial.get(&k).copied().unwrap_or(0),
        });
        synthesized += 1;
    }

    // 5. THE AGREEMENT CHECK: fold(pre, ops) == post — refuse on any mismatch.
    let folded = fold(pre, &ops);
    if &folded != post {
        let mut mismatches = Vec::new();
        for (k, v) in post.iter() {
            if folded.get(k) != Some(v) {
                mismatches.push(format!("{k:?}: post {v:?} vs fold {:?}", folded.get(k)));
            }
        }
        for (k, v) in folded.iter() {
            if !post.contains_key(k) {
                mismatches.push(format!("{k:?}: fold {v:?} vs post absent"));
            }
        }
        return Err(format!(
            "umem fold/post disagreement ({} addresses): {}",
            mismatches.len(),
            mismatches.join("; ")
        ));
    }
    debug_assert!(disciplined(&ops));

    Ok(UmemTurnWitness {
        pre: pre.clone(),
        ops,
        post: post.clone(),
        synthesized,
    })
}

// ===========================================================================
// THE REIFY DIRECTION — the inverse of `project_cell` / `project_ledger`.
//
// `reify_cell` materializes one cell's projected planes back into a live
// `Cell`, RE-DERIVING the deliberately-dropped commitments from the kept
// planes (it does not store them): the user-field-map root (`fields_root`,
// re-derived from the `Field { slot ≥ 16 }` plane), the heap root, the leaf
// caches, and — at the ledger level — the Merkle tree/root (which `Ledger`
// already rebuilds lazily on demand). This closes the time-travel `reify_seam`
// (`turn/tests/umem_time_travel.rs`): a witnessed `UProjection` boundary lifts
// back to a byte-identical `Ledger`.
//
// ## The round-trip law and its faithful class
//
// `reify_ledger(project_ledger(L)) == L` holds for every cell whose state is
// expressible by the projection address space — the FAITHFUL CLASS. The
// projection is value-lossless over that class, and `reify` re-derives the rest.
//
// ## The named residual (the planes the projection does NOT carry — honest)
//
// `project_cell` is injective on the value planes it carries, but it does NOT
// emit a `UKey` for three cell sub-states. A cell that exercises one of these
// carries state the boundary cannot reconstruct, so `reify_cell` REFUSES with a
// precise [`ReifyError`] rather than silently round-tripping a lie:
//
//  1. **`Cell.interfaces`** — the exposed typed-interface vector. No `UKey`
//     plane carries it. ⇒ [`ReifyError::InterfacesNotProjected`].
//
// **Closed (UMEM-PRIMITIVE §2, Stage A): `CellState.heap_map`.** The per-cell
// heap is now a first-class umem plane — every `(collection, key) → value` entry
// projects to a `Heap{cell, collection, key}` cell, so `reify_cell` rebuilds the
// `heap_map` from that preimage and RE-DERIVES `heap_root` (the boundary). A
// non-empty heap is now in the faithful class; `HeapNotProjected` survives only
// for an internally-inconsistent projection (committed boundary ≠ re-derived).
//
// **Closed (reify residuals #3/#4): `CapabilitySet.tombstones` +
// `next_slot`.** A revoke drops the cap from the `CapSlot` plane AND emits one
// `CapTombstone{cell, slot}` ghost (`project_cell`), so BOTH planes carry the
// full c-list shape. `reify_cell` reads the live caps AND the tombstone ghosts
// and hands them to `CapabilitySet::reconstruct`, which restores the
// NON-CONTIGUOUS live slots and re-derives `next_slot = max(live, tombstoned) +
// 1` — so a REVOKED cell round-trips byte-identically (matching the boundary
// the `CapTombstone` plane already proves via `record_kernel_boundary_agrees`).
// `CapTombstonesNotProjected` / `CapNextSlotUnrecoverable` are retained as
// precise diagnostics but are no longer reachable for a revoked cell.
//
// The faithful class is exactly the cells with no interfaces (any heap, any cap
// revocation gap is fine). The time-travel boundary lands in this class for the
// transfer / set-field / set-heap / grant / revoke lanes the prototype proves
// over; the residual is the burn-down for extending the projection to carry an
// interface plane.
//
// Per-window executor metering (`FactoryRegistry::{creation_counts,
// current_epoch}`, rate-limit counters) is NOT reconstructed and NOT part of
// the round-trip law — it is documented non-consensus state (the "Named
// exceptions" in this module's header) that never enters a state commitment.

/// Why a `UProjection` could not be reified into a byte-identical state — each
/// variant names a value plane the projection deliberately does not carry (the
/// honest residual of the `reify_seam`; see the module section above).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReifyError {
    /// The `Identity` blob for a cell is missing or malformed (the projection
    /// carries `public_key ‖ token_id` as a 64-byte blob; without it the cell's
    /// content-addressed id cannot be reconstructed).
    MissingIdentity(CellId),
    /// A structured-blob plane failed to decode (corrupt projection).
    BlobDecode { key: UKey, detail: String },
    /// A plane carried a `UVal` of the wrong shape for its `UKey`.
    ValueShape { key: UKey, detail: String },
    /// The reconstructed `(public_key, token_id)` does not hash to the cell id
    /// the projection keyed it under (the content-address invariant broke).
    IdentityMismatch { expected: CellId, derived: CellId },
    /// The committed `HeapRoot` boundary does not equal the root re-derived from
    /// the projected `Heap` preimage — an internally-inconsistent projection (a
    /// tampered boundary). (Formerly "heap not projected": the per-cell heap is
    /// now a first-class umem plane, so the preimage IS carried — UMEM-PRIMITIVE
    /// §2, Stage A — and this fires only on a genuine boundary/preimage mismatch.)
    HeapNotProjected(CellId),
    /// The cell exposes typed interfaces, which no `UKey` plane carries
    /// (residual #2).
    InterfacesNotProjected(CellId),
    /// Retained diagnostic (residual #3, now CLOSED): the `CapTombstone` plane
    /// carries revoked slots, so `reify_cell` reconstructs them via
    /// [`CapabilitySet::reconstruct`] — no longer reachable for a revoked cell.
    CapTombstonesNotProjected(CellId),
    /// Retained diagnostic (residual #4, now CLOSED): `next_slot` is re-derived
    /// as `max(live, tombstoned) + 1` from the `CapSlot` + `CapTombstone`
    /// planes, so a revocation gap is recoverable — no longer reachable.
    CapNextSlotUnrecoverable(CellId),
}

impl std::fmt::Display for ReifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReifyError::MissingIdentity(c) => {
                write!(f, "reify: missing/short Identity blob for cell {c:?}")
            }
            ReifyError::BlobDecode { key, detail } => {
                write!(f, "reify: blob decode failed at {key:?}: {detail}")
            }
            ReifyError::ValueShape { key, detail } => {
                write!(f, "reify: wrong UVal shape at {key:?}: {detail}")
            }
            ReifyError::IdentityMismatch { expected, derived } => write!(
                f,
                "reify: identity mismatch — projection keyed {expected:?} but \
                 derive_raw(pk, token) = {derived:?}"
            ),
            ReifyError::HeapNotProjected(c) => write!(
                f,
                "reify: cell {c:?} committed heap_root != root re-derived from the \
                 projected Heap preimage (inconsistent boundary)"
            ),
            ReifyError::InterfacesNotProjected(c) => write!(
                f,
                "reify: cell {c:?} exposes interfaces; no UKey plane carries \
                 them (reify_seam residual #2)"
            ),
            ReifyError::CapTombstonesNotProjected(c) => write!(
                f,
                "reify: cell {c:?} carries cap tombstones; the CapSlot plane \
                 drops revoked slots (reify_seam residual #3)"
            ),
            ReifyError::CapNextSlotUnrecoverable(c) => write!(
                f,
                "reify: cell {c:?} next_slot exceeds the live high-water mark; \
                 a revocation gap cannot be recovered (reify_seam residual #4)"
            ),
        }
    }
}

impl std::error::Error for ReifyError {}

fn decode_blob<T: serde::de::DeserializeOwned>(key: &UKey, val: &UVal) -> Result<T, ReifyError> {
    match val {
        UVal::Blob(bytes) => serde_json::from_slice(bytes).map_err(|e| ReifyError::BlobDecode {
            key: key.clone(),
            detail: e.to_string(),
        }),
        other => Err(ReifyError::ValueShape {
            key: key.clone(),
            detail: format!("expected Blob, got {other:?}"),
        }),
    }
}

fn expect_bytes32(key: &UKey, val: &UVal) -> Result<[u8; 32], ReifyError> {
    match val {
        UVal::Bytes32(b) => Ok(*b),
        other => Err(ReifyError::ValueShape {
            key: key.clone(),
            detail: format!("expected Bytes32, got {other:?}"),
        }),
    }
}

/// **REIFY ONE CELL** — the inverse of [`project_cell`]. Reads the cell's
/// projected planes out of `proj` and rebuilds a live [`Cell`], RE-DERIVING the
/// dropped commitments (`fields_root` from the `Field { slot ≥ 16 }` plane, the
/// leaf/cap caches) from the kept planes — it never reads a stored commitment
/// for them.
///
/// Refuses (with a precise [`ReifyError`]) when the cell's state needs a plane
/// the projection does not carry (interfaces) — the honest residual of the
/// `reify_seam`. Revoked cells now round-trip: the `CapTombstone` plane carries
/// the revoked slots, so `reify_cell` reconstructs a non-contiguous c-list with
/// the correct post-revoke `next_slot` (residuals #3/#4 closed). See the module
/// section above.
///
/// `cell` must be present in `proj` (i.e. `UKey::Exist(cell)` ↦ `Present`); the
/// caller (`reify_ledger`) walks the `Exist` plane to find the cell set.
pub fn reify_cell(cell: CellId, proj: &UProjection) -> Result<Cell, ReifyError> {
    // -- identity: rebuild (pk, token_id) and re-derive the content address. --
    let id_key = UKey::Identity(cell);
    let (pk, token_id) = match proj.get(&id_key) {
        Some(UVal::Blob(bytes)) if bytes.len() == 64 => {
            let mut pk = [0u8; 32];
            let mut token = [0u8; 32];
            pk.copy_from_slice(&bytes[..32]);
            token.copy_from_slice(&bytes[32..]);
            (pk, token)
        }
        _ => return Err(ReifyError::MissingIdentity(cell)),
    };
    let derived = CellId::derive_raw(&pk, &token_id);
    if derived != cell {
        return Err(ReifyError::IdentityMismatch {
            expected: cell,
            derived,
        });
    }

    // -- scalar heap planes (balance seeds the constructor). --
    let balance = match proj.get(&UKey::Balance(cell)) {
        Some(UVal::Int(b)) => *b,
        Some(other) => {
            return Err(ReifyError::ValueShape {
                key: UKey::Balance(cell),
                detail: format!("expected Int, got {other:?}"),
            });
        }
        None => 0,
    };
    let mut c = Cell::with_balance(pk, token_id, balance);

    if let Some(v) = proj.get(&UKey::Nonce(cell)) {
        match v {
            UVal::U64(n) => c.state.set_nonce(*n),
            other => {
                return Err(ReifyError::ValueShape {
                    key: UKey::Nonce(cell),
                    detail: format!("expected U64, got {other:?}"),
                });
            }
        }
    }
    if let Some(UVal::Bool(b)) = proj.get(&UKey::ProvedState(cell)) {
        c.state.set_proved_state(*b);
    }
    if let Some(UVal::U64(e)) = proj.get(&UKey::DelegationEpoch(cell)) {
        c.state.set_delegation_epoch(*e);
    }
    if let Some(UVal::U64(h)) = proj.get(&UKey::CommittedHeight(cell)) {
        c.state.set_committed_height(*h);
    }

    // -- fixed field slots, visibility, per-slot commitments. --
    for slot in 0..STATE_SLOTS {
        let fk = UKey::Field {
            cell,
            slot: slot as u64,
        };
        if let Some(v) = proj.get(&fk) {
            c.state.fields[slot] = expect_bytes32(&fk, v)?;
        }
        let vk = UKey::FieldVisibility {
            cell,
            slot: slot as u64,
        };
        if let Some(v) = proj.get(&vk) {
            c.state.field_visibility[slot] = decode_blob(&vk, v)?;
        }
        let ck = UKey::FieldCommitment {
            cell,
            slot: slot as u64,
        };
        c.state.commitments[slot] = match proj.get(&ck) {
            Some(v) => Some(expect_bytes32(&ck, v)?),
            None => None,
        };
    }

    // -- the overflow user-field MAP (keys ≥ STATE_SLOTS): rebuild the map,
    //    then RE-DERIVE `fields_root` from it (don't store the dropped root). --
    let mut overflow: BTreeMap<u64, [u8; 32]> = BTreeMap::new();
    for (k, v) in proj.range(UKey::Field { cell, slot: 0 }..) {
        match k {
            UKey::Field { cell: kc, slot } if *kc == cell => {
                if *slot >= STATE_SLOTS as u64 {
                    overflow.insert(*slot, expect_bytes32(k, v)?);
                }
            }
            // BTreeMap order: once the key leaves this cell's Field run, stop.
            _ => break,
        }
    }
    c.state.fields_map = overflow;
    c.state.reseal_fields_root(); // re-derive the dropped `fields_root`.

    // -- the kept root planes (these ARE projected, byte-for-byte). --
    if let Some(v) = proj.get(&UKey::SwissTableRoot(cell)) {
        c.state.swiss_table_root = expect_bytes32(&UKey::SwissTableRoot(cell), v)?;
    }
    if let Some(v) = proj.get(&UKey::RefcountTableRoot(cell)) {
        c.state.refcount_table_root = expect_bytes32(&UKey::RefcountTableRoot(cell), v)?;
    }
    for i in 0..c.state.system_roots.len() {
        let sk = UKey::SystemRoot {
            cell,
            index: i as u64,
        };
        if let Some(v) = proj.get(&sk) {
            c.state.system_roots[i] = expect_bytes32(&sk, v)?;
        }
    }
    // -- the openable HEAP (UMEM-PRIMITIVE.md §2, Stage A): rebuild `heap_map`
    //    from the projected `Heap` plane, then RE-DERIVE `heap_root` from it
    //    (the boundary is the committed `HeapRoot` plane; the preimage is now
    //    carried, closing the former reify_seam residual #1). --
    let mut heap: BTreeMap<(u32, u32), [u8; 32]> = BTreeMap::new();
    for (k, v) in proj.iter() {
        if let UKey::Heap {
            cell: kc,
            collection,
            key,
        } = k
        {
            if *kc == cell {
                heap.insert((*collection, *key), expect_bytes32(k, v)?);
            }
        }
    }
    c.state.heap_map = heap;
    c.state.reseal_heap_root(); // re-derive the boundary from the preimage.
    // The committed `HeapRoot` plane (when carried) MUST equal the root
    // re-derived from the projected preimage; otherwise the projection is
    // internally inconsistent (a tampered boundary) and we refuse rather than
    // round-trip a heap whose preimage does not reproduce the committed root.
    if let Some(v) = proj.get(&UKey::HeapRoot(cell)) {
        let committed = expect_bytes32(&UKey::HeapRoot(cell), v)?;
        if committed != c.state.heap_root.to_bytes32() {
            return Err(ReifyError::HeapNotProjected(cell));
        }
    }

    // -- lifecycle / mode / permissions / vk / program (structured blobs). --
    if let Some(v) = proj.get(&UKey::Lifecycle(cell)) {
        c.lifecycle = decode_blob(&UKey::Lifecycle(cell), v)?;
    }
    if let Some(v) = proj.get(&UKey::Mode(cell)) {
        c.mode = decode_blob(&UKey::Mode(cell), v)?;
    }
    if let Some(v) = proj.get(&UKey::Permissions(cell)) {
        c.permissions = decode_blob(&UKey::Permissions(cell), v)?;
    }
    c.verification_key = match proj.get(&UKey::VerificationKey(cell)) {
        Some(v) => Some(decode_blob(&UKey::VerificationKey(cell), v)?),
        None => None,
    };
    if let Some(v) = proj.get(&UKey::Program(cell)) {
        c.program = decode_blob(&UKey::Program(cell), v)?;
    }

    // -- delegation pointer + snapshot. --
    c.delegate = match proj.get(&UKey::Delegate(cell)) {
        Some(v) => Some(CellId(expect_bytes32(&UKey::Delegate(cell), v)?)),
        None => None,
    };
    c.delegation = match proj.get(&UKey::DelegationSnapshot(cell)) {
        Some(v) => Some(decode_blob(&UKey::DelegationSnapshot(cell), v)?),
        None => None,
    };

    // -- capabilities (the caps-domain `CapSlot` + `CapTombstone` planes):
    //    reinstall the LIVE caps at their ORIGINAL slots and re-derive the
    //    revoked-slot tombstones from the `CapTombstone` plane. A revoke drops
    //    the cap from `CapSlot` AND emits one `CapTombstone{cell, slot}` ghost
    //    (`project_cell`), so BOTH planes together carry the full c-list shape:
    //    `CapabilitySet::reconstruct` restores non-contiguous live slots and
    //    sets `next_slot = max(live, tombstoned) + 1`, round-tripping a revoked
    //    cell byte-identically (the former reify_seam residuals #3/#4, closed). --
    let mut caps: Vec<CapabilityRef> = Vec::new();
    let mut cap_tombstones: Vec<u32> = Vec::new();
    for (k, v) in proj.iter() {
        match k {
            UKey::CapSlot { cell: kc, slot: _ } if *kc == cell => {
                caps.push(decode_blob(k, v)?);
            }
            UKey::CapTombstone { cell: kc, slot } if *kc == cell => {
                cap_tombstones.push(*slot);
            }
            _ => {}
        }
    }
    c.capabilities = CapabilitySet::reconstruct(caps, cap_tombstones);

    // -- residual guards: interfaces are not projected. The `Cell` type no longer
    // carries a typed-interface vector (the field was lifted out of the kernel cell),
    // so a reified cell exposes none by construction — the guard is vacuously held.
    // (`ReifyError::InterfacesNotProjected` is retained for a future projection
    // extension that would re-introduce a fillable interface plane.)

    Ok(c)
}

/// **REIFY THE LEDGER** — the inverse of [`project_ledger`]. Rebuilds every
/// present cell (walking the `Exist` plane) and the sovereign-commitment table,
/// inserting into a fresh [`Ledger`]. The Merkle tree/root is NOT reconstructed
/// here: `Ledger` rebuilds it lazily on the next `root()` — the dropped ledger
/// commitment is re-derived on demand, exactly the projection's documented
/// "derived commitment over the cells" non-cell.
///
/// `reify_ledger(project_ledger(L)) == L` for every `L` in the faithful class
/// (see the module section above); a cell outside it yields a precise
/// [`ReifyError`].
pub fn reify_ledger(proj: &UProjection) -> Result<Ledger, ReifyError> {
    let mut ledger = Ledger::new();
    for (k, _) in proj.iter() {
        if let UKey::Exist(cell) = k {
            let c = reify_cell(*cell, proj)?;
            // `insert_cell` re-derives membership + marks the tree dirty; the
            // root materializes lazily when next asked for.
            ledger.insert_cell(c).map_err(|e| ReifyError::BlobDecode {
                key: UKey::Exist(*cell),
                detail: format!("ledger insert: {e:?}"),
            })?;
        }
    }
    for (k, v) in proj.iter() {
        if let UKey::SovereignCommitment(cell) = k {
            let commitment = expect_bytes32(k, v)?;
            ledger
                .register_sovereign_cell(*cell, commitment)
                .map_err(|e| ReifyError::BlobDecode {
                    key: UKey::SovereignCommitment(*cell),
                    detail: format!("sovereign register: {e:?}"),
                })?;
        }
    }
    Ok(ledger)
}

/// **REIFY THE FULL EXECUTOR STATE** — the inverse of
/// [`project_executor_state`]: rebuilds the ledger plus the executor-owned side
/// tables (note nullifiers, bridged nullifiers, factory descriptors) the
/// projection carries. Per-window factory metering (`creation_counts`,
/// `current_epoch`) is NOT reconstructed — it is documented non-consensus
/// metering, so the returned registry carries only the descriptors (its
/// metering resets to default).
pub fn reify_executor_state(
    proj: &UProjection,
) -> Result<(Ledger, NullifierSet, BridgedNullifierSet, FactoryRegistry), ReifyError> {
    let ledger = reify_ledger(proj)?;
    let mut note_nullifiers = NullifierSet::new();
    let mut bridged_nullifiers = BridgedNullifierSet::new();
    let mut factories = FactoryRegistry::new();
    for (k, v) in proj.iter() {
        match k {
            UKey::NoteNullifier(n) => {
                // STAGE-D GAP (reported): the universal-memory projection stores
                // `UKey::NoteNullifier(n) → UVal::Present` — it does NOT carry the
                // spent-note value, so a reconstruction here CANNOT rebuild a
                // `root8()` matching the committed accumulator (INV-3). Recording
                // `0` reconstructs correct MEMBERSHIP (double-spend still holds)
                // but a WRONG felt-root. Closing this needs the projection schema
                // to carry the value (e.g. `UVal::NullifierValue(u64)`) — the
                // Stage-D persistence/reconstruction work.
                let _ = note_nullifiers.insert(dregg_cell::note::Nullifier(*n), 0);
            }
            UKey::BridgedNullifier(n) => {
                let _ = bridged_nullifiers.insert(*n);
            }
            UKey::Factory(vk) => {
                let desc = decode_blob(k, v)?;
                factories.descriptors.insert(*vk, desc);
            }
            _ => {}
        }
    }
    Ok((ledger, note_nullifiers, bridged_nullifiers, factories))
}

// ===========================================================================
// STAGE A — the per-cell heap as a first-class umem (UMEM-PRIMITIVE.md §2).
//
// These in-crate tests exercise the `emit_trace` bridge (which is `pub(crate)`)
// over a `JournalEntry::SetHeap` heap write, the projection of `heap_map` into
// the `Heap` plane, and the cross-cell read (`open_heap_against_committed`) that
// binds another cell's committed `heap_root` as an init image — the keystone's
// first cross-cell consumer.
// ===========================================================================
#[cfg(test)]
mod heap_stage_a_tests {
    use super::*;
    use crate::journal::JournalEntry;
    use dregg_cell::Cell;

    fn heap_cell(seed: u8) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(37);
        Cell::with_balance(pk, [0u8; 32], 0)
    }

    fn bytes(n: u8) -> [u8; 32] {
        let mut b = [0u8; 32];
        b[0] = n;
        b
    }

    /// The projection carries one `Heap` cell per `heap_map` entry, and the
    /// sorted-Poseidon2 root re-derived over those cells EQUALS the cell's
    /// committed `heap_root` (the boundary). The derived root is a refactor of
    /// WHERE the commitment is read, not WHAT it commits.
    #[test]
    fn heap_projection_derives_committed_root() {
        let mut cell = heap_cell(1);
        cell.state.set_heap(7, 3, bytes(42));
        cell.state.set_heap(7, 9, bytes(7));
        cell.state.set_heap(2, 1, bytes(99));
        let id = cell.id();
        let committed = cell.state.heap_root.to_bytes32();

        let mut proj = UProjection::new();
        project_cell(&cell, &mut proj);

        // every heap_map entry is a genuine umem cell.
        let mut rebuilt: BTreeMap<(u32, u32), [u8; 32]> = BTreeMap::new();
        for (k, v) in proj.iter() {
            if let UKey::Heap {
                cell: kc,
                collection,
                key,
            } = k
            {
                assert_eq!(*kc, id, "heap cell keyed under the owning cell");
                match v {
                    UVal::Bytes32(b) => {
                        rebuilt.insert((*collection, *key), *b);
                    }
                    other => panic!("heap cell must be Bytes32, got {other:?}"),
                }
            }
        }
        assert_eq!(rebuilt.len(), 3, "all three heap entries projected");

        // the derived boundary EQUALS the committed boundary.
        let derived = dregg_cell::state::compute_heap_root(&rebuilt);
        assert_eq!(
            derived, committed,
            "derived sorted-Poseidon2 root over the Heap plane must equal the \
             committed heap_root"
        );
        // the derived boundary is NOT separately projected (it is the derived
        // commitment of the Heap plane, like fields_root over Field).
        assert_eq!(
            proj.get(&UKey::HeapRoot(id)),
            None,
            "heap_root is the derived commitment, not a separate projected cell"
        );
    }

    /// A heap write journaled as `JournalEntry::SetHeap` is re-read as a genuine
    /// umem WRITE row in the heap domain; the fold over the pre-projection equals
    /// the post-projection, the trace is disciplined, and no op is synthesized
    /// (the journal NAMES the heap address).
    #[test]
    fn heap_write_emits_genuine_umem_row() {
        let mut cell = heap_cell(2);
        let id = cell.id();

        // pre-state: empty heap.
        let mut pre = UProjection::new();
        project_cell(&cell, &mut pre);

        // apply the heap write (the out-of-band mutation the live producer will
        // one day journal) and capture the post-state.
        let value = bytes(55);
        cell.state.set_heap(4, 8, value);
        let mut post = UProjection::new();
        project_cell(&cell, &mut post);

        // the journal entry the producer emits on a heap write.
        let entry = JournalEntry::SetHeap {
            cell: id,
            collection: 4,
            key: 8,
            old_value: None, // the (4,8) key was absent before this turn.
        };

        let w = emit_trace(&pre, &post, std::slice::from_ref(&entry))
            .expect("heap-write bridge must produce a witness");

        // the agreement square + discipline + no synthesized ops.
        assert_eq!(fold(&w.pre, &w.ops), w.post, "the agreement square holds");
        assert!(disciplined(&w.ops), "the trace is disciplined");
        assert_eq!(w.synthesized, 0, "the journal names the heap address");

        // a genuine WRITE row at the Heap key, absent -> value.
        let row = w
            .ops
            .iter()
            .find(|op| {
                matches!(
                    op.key,
                    UKey::Heap {
                        collection: 4,
                        key: 8,
                        ..
                    }
                )
            })
            .expect("a Heap write row must be emitted");
        assert_eq!(row.kind, UmemKind::Write);
        assert_eq!(row.prev_val, None, "the key was absent before the write");
        assert_eq!(row.val, Some(UVal::Bytes32(value)), "the written value");

        // the derived commitment (heap_root) is not a projected cell; the Heap
        // plane is the truth and the post-state carries the written entry.
        assert_eq!(post.get(&UKey::HeapRoot(id)), None);
        assert_eq!(
            post.get(&UKey::Heap {
                cell: id,
                collection: 4,
                key: 8
            }),
            Some(&UVal::Bytes32(value))
        );

        // NON-VACUITY: a tampered installed value breaks the fold/post square.
        let mut tampered = w.ops.clone();
        for op in tampered.iter_mut() {
            if matches!(
                op.key,
                UKey::Heap {
                    collection: 4,
                    key: 8,
                    ..
                }
            ) {
                op.val = Some(UVal::Bytes32(bytes(0xFF)));
            }
        }
        assert_ne!(
            fold(&pre, &tampered),
            post,
            "a tampered heap write must break the agreement square (non-vacuous)"
        );
    }

    /// THE CROSS-CELL READ — a reader binds cell B's committed `heap_root` as an
    /// init image and opens a key. A sound binding opens the value; a tampered
    /// projected preimage produces a different root, so the binding REFUSES (the
    /// Rust shadow of the keystone's `boundary_init_root_bound`).
    #[test]
    fn cross_cell_read_binds_committed_heap_root() {
        // cell B holds a heap; its heap_root is the committed boundary.
        let mut b = heap_cell(3);
        b.state.set_heap(1, 2, bytes(42));
        b.state.set_heap(1, 5, bytes(13));
        let b_id = b.id();
        let committed = b.state.heap_root.to_bytes32();

        let mut proj = UProjection::new();
        project_cell(&b, &mut proj);

        // a sound binding opens a present key and reports absence Merkle-free.
        assert_eq!(
            open_heap_against_committed(&proj, b_id, committed, 1, 2),
            Ok(Some(bytes(42))),
            "binding the committed root opens the present key"
        );
        assert_eq!(
            open_heap_against_committed(&proj, b_id, committed, 1, 99),
            Ok(None),
            "an absent key opens to None (the freshness leg)"
        );

        // TAMPER: a forged value in the projected preimage yields a different
        // derived root, so the init binding refuses (anti-forgery tooth).
        let mut forged = proj.clone();
        forged.insert(
            UKey::Heap {
                cell: b_id,
                collection: 1,
                key: 2,
            },
            UVal::Bytes32(bytes(0xAA)),
        );
        let err = open_heap_against_committed(&forged, b_id, committed, 1, 2)
            .expect_err("a tampered init image must fail the published root");
        assert_eq!(err.cell, b_id);
        assert_eq!(err.committed, committed);
        assert_ne!(
            err.derived, committed,
            "the tampered image derives a different root"
        );
    }
}

#[cfg(test)]
mod working_non_projection_tests {
    //! The CHECKED form of the `Working`-domain non-projection invariant
    //! (UMEM-PRIMITIVE.md §3): `Working` rides the memcheck trace (consistent for
    //! free) but is NEVER emitted by `project_cell`/`project_ledger`/
    //! `project_executor_state` into a committed boundary. Previously guarded only
    //! by the Rust fact that those functions never construct a `UKey::Working`;
    //! now a `debug_assert_no_working` guard fires if that breaks, and this test
    //! pins it from the outside.
    use super::*;
    use dregg_cell::{Cell, Ledger, note::Nullifier, nullifier_set::NullifierSet};
    use dregg_cell_crypto::note_bridge::BridgedNullifierSet;

    fn cell_seeded(seed: u8) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(37);
        Cell::with_balance(pk, [0u8; 32], 1000 + seed as i64)
    }

    fn bytes(n: u8) -> [u8; 32] {
        let mut b = [0u8; 32];
        b[0] = n;
        b
    }

    fn count_working(proj: &UProjection) -> usize {
        proj.keys()
            .filter(|k| k.domain() == UDomain::Working)
            .count()
    }

    /// A populated executor state: two cells (with fields + heap entries + a
    /// balance), note + bridged nullifiers, projected three ways. None of the
    /// three projection functions emits a single `Working`-domain key.
    #[test]
    fn projections_never_emit_working() {
        // -- two populated cells, one with heap entries. --
        let mut a = cell_seeded(1);
        a.state.fields[0] = bytes(7);
        a.state.set_heap(3, 4, bytes(11));
        a.state.set_heap(3, 9, bytes(22));
        let mut b = cell_seeded(2);
        b.state.fields[2] = bytes(9);

        let mut ledger = Ledger::new();
        ledger.insert_cell(a.clone()).unwrap();
        ledger.insert_cell(b.clone()).unwrap();

        // project_cell over each populated cell — no Working.
        let mut per_cell = UProjection::new();
        project_cell(&a, &mut per_cell);
        project_cell(&b, &mut per_cell);
        assert!(
            !per_cell.is_empty(),
            "the per-cell projection is genuinely populated"
        );
        assert_eq!(
            count_working(&per_cell),
            0,
            "project_cell must emit no Working-domain key"
        );

        // project_ledger over the populated ledger — no Working.
        let ledger_proj = project_ledger(&ledger);
        assert!(!ledger_proj.is_empty());
        assert_eq!(
            count_working(&ledger_proj),
            0,
            "project_ledger must emit no Working-domain key"
        );

        // project_executor_state over ledger + side tables — no Working.
        let mut note_nullifiers = NullifierSet::new();
        note_nullifiers.insert(Nullifier(bytes(0xA1)), 100).unwrap();
        note_nullifiers.insert(Nullifier(bytes(0xA2)), 200).unwrap();
        let mut bridged_nullifiers = BridgedNullifierSet::new();
        bridged_nullifiers.insert(bytes(0xB1)).unwrap();
        let factories = FactoryRegistry::new();

        let full =
            project_executor_state(&ledger, &note_nullifiers, &bridged_nullifiers, &factories);
        assert!(full.len() > ledger_proj.len(), "side tables added cells");
        assert_eq!(
            count_working(&full),
            0,
            "project_executor_state must emit no Working-domain key"
        );
    }

    /// THE LOAD-BEARING DISTINCTION: a `Working` cell is carried by the memcheck
    /// FOLD (it is genuine trace-resident state, consistent for free) yet NEVER
    /// appears in the projected boundary. We fold `Working` WRITE ops over the
    /// real projection — the folded image carries them — but the projection
    /// functions, re-run over the same persistent state, still emit zero. So a
    /// transient scratch lives in the trace but is never published.
    #[test]
    fn working_rides_the_trace_but_never_the_boundary() {
        let cell = cell_seeded(3);
        let service = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();

        // the persistent boundary — Working-free by the invariant.
        let pre = project_ledger(&ledger);
        assert_eq!(count_working(&pre), 0, "the boundary carries no Working");

        // a memcheck trace that WRITES two Working scratch cells (the transient
        // service umem the §3 design rides on the ONE trace).
        let ops = vec![
            UmemOp {
                kind: UmemKind::Write,
                key: UKey::Working {
                    service,
                    collection: 1,
                    key: 0,
                },
                val: Some(UVal::Bytes32(bytes(0x55))),
                prev_val: None,
                prev_serial: 0,
            },
            UmemOp {
                kind: UmemKind::Write,
                key: UKey::Working {
                    service,
                    collection: 1,
                    key: 1,
                },
                val: Some(UVal::UmemRef(bytes(0x66))),
                prev_val: None,
                prev_serial: 0,
            },
        ];
        assert!(disciplined(&ops), "the Working trace is disciplined");

        // the FOLD carries the Working cells — they are genuine trace state.
        let folded = fold(&pre, &ops);
        assert_eq!(
            count_working(&folded),
            2,
            "the memcheck fold carries the Working scratch cells (consistent for free)"
        );
        // and their boundary is derivable on demand (the §4 checkpoint) — yet it
        // is never published.
        let _checkpoint = working_umem_root(&folded, service);

        // CRUCIAL: re-projecting the SAME persistent state still emits zero
        // Working — the scratch never crossed into a committed boundary.
        let re = project_ledger(&ledger);
        assert_eq!(
            count_working(&re),
            0,
            "Working stays trace-only; the projection never publishes it"
        );
    }
}
