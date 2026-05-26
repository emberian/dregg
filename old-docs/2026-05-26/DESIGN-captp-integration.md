# DESIGN: CapTP Integration

**Status:** Draft — committed direction
**Scope:** Wire `captp/` crate, `wire/src/server.rs` CapTP state, and the four AIR
variants (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`) into the
runtime `Effect` enum, the `ActionBuilder`, the federation state, and the
Effect-VM honesty pass. Make CapTP a first-class, provable feature.

This document is the contract between Stage 2 (AIR honesty pass) and Stage 7
(runtime emitters) of `EFFECT-VM-SHAPE-A.md`, plus the federation-state changes
needed to make the AIR constraints non-tautological.

---

## 1. Current state survey

CapTP-relevant code lives in **four** layers. The state of each layer is
summarised below.

### 1.1 The `captp/` crate (offline data structures + protocol logic)

`captp/src/lib.rs:1-162` — the crate root. Re-exports the protocol pieces and
defines `FederationId([u8;32])` and `StrandId = [u8;32]`. The doc-comment
declares mixed trust: session/swiss/GC are executor-trusted; handoff certificates
and store-and-forward envelopes are trustless once signed.

Submodules:

- `captp/src/uri.rs:1-221` — `DreggUri { federation_id, cell_id, swiss }` plus
  `dregg://` string codec. **Complete.**
- `captp/src/sturdy.rs:1-365` — `SwissTable`: `HashMap<[u8;32], SwissEntry>`
  with `export`, `export_with_options`, `enliven`, `revoke`, `peek`, `make_uri`.
  `SwissEntry` holds `cell_id`, `permissions: AuthRequired`, `allowed_effects`,
  `expires_at`, `created_at`, `max_uses`, `use_count`. **Complete in-memory; not
  Merkleized.**
- `captp/src/session.rs:1-345` — `CapSession`: per-peer `exports`/`imports`/
  `promises` maps + `epoch: u64`. Supports `peer_strand: Option<StrandId>` for
  the unified-lace migration. **Complete.**
- `captp/src/gc.rs:1-716` — `ExportGcManager`, `ImportGcManager`, `DropMessage`,
  `DropResult { StillHeld, CanRevoke, Invalid }`, `SessionId = u64`.
  `record_export_with_session(cell_id, fed, height, session_id)` and
  `process_drop_with_session` enforce that drops match the session that created
  the export. **Complete; in-memory; not committed.**
- `captp/src/handoff.rs:1-721` — `HandoffCertificate` (signed by introducer),
  `HandoffPresentation` (recipient signs the nonce), `validate_handoff`
  function that checks both signatures + swiss lookup + expiry + known-federation
  membership. **Complete and cryptographically sound, but the "known-federation"
  set is just a `Vec<FederationId>` passed in, not a Merkleized commitment.**
- `captp/src/store_forward.rs:1-1546` — X25519-encrypted relay envelopes for
  offline delivery. Tangential to the AIR question.
- `captp/src/pipeline.rs:1-1136` — promise pipelining (`PipelineRegistry`,
  `PipelineWireMessage`, `PipelinedAction`).

### 1.2 The `wire/` crate (network transport)

`wire/src/message.rs:240-346` — `WireMessage` variants:

- `CapHello { group_id, initial_exports }` — opens a session, allocates an epoch.
- `CapGoodbye { group_id, reason }` — tears down.
- `EnlivenSturdyRef { uri_bytes, requester_height }` / `EnlivenResponse
  { success, cell_id, permissions_tag, error }`.
- `DropRemoteRef { from_strand, cell_id, session_epoch }`.
- `PipelinedMsg { target_promise_id, ... }`.
- `PresentHandoff { presentation_bytes, introducer_pk }` /
  `HandoffAccepted { routing_token, cell_id, permissions_tag }`.

`wire/src/server.rs:895-981` — `CapTpState { sessions, swiss_table, export_gc,
known_federations, current_height, next_session_epoch }`. The peer-role machinery
at `:719-822` gates CapTP messages behind `PeerRole::Member | CapTpPeer`.
`process_introduction_exports` (`:947-974`) records 3-party introduction exports
in `ExportGcManager` from a receipt.

The CapTP message handler at `wire/src/server.rs:2243-2350+` (CapHello,
CapGoodbye, EnlivenSturdyRef, DropRemoteRef, PresentHandoff) is **fully wired**
at the wire layer. It calls `swiss_table.enliven`, `export_gc.process_drop`, and
`validate_handoff` directly — **bypassing the executor and AIR.**

### 1.3 The `circuit/` crate (AIR)

`circuit/src/effect_vm.rs:489-539` defines the four CapTP variants in the AIR
`Effect` enum:

- `ExportSturdyRef { cell_id, permissions, random_seed, export_counter }`
- `EnlivenRef { swiss_number, presenter_id, expected_cell_id, expected_permissions }`
- `DropRef { cell_id, holder_federation, current_refcount }`
- `ValidateHandoff { certificate_hash, recipient_pk, introducer_pk, approved_set_root }`

Selectors: `circuit/src/effect_vm.rs:134-140`. Param column layout:
`circuit/src/effect_vm.rs:264-297`. Constraint definitions in
`circuit/src/effect_vm.rs:1563-1769`. Trace generation in
`circuit/src/effect_vm.rs:2840-2925`. Same logic mirrored in `effect_interp.rs:786-927`.

What the constraints currently prove (per `EFFECT-VM-SHAPE-A.md` line 39-42):

| Variant            | Status                                              |
|--------------------|-----------------------------------------------------|
| `ExportSturdyRef`  | OK except `export_counter` is unbound from `field[7]` |
| `EnlivenRef`       | Tautology: `aux[0] == hash(swiss, hash(cell, perms))` where `aux[0]` is set by the executor to that exact value |
| `DropRef`          | OK except `holder_federation` is unbound from any refcount table; `field[5]` decrement is unkeyed |
| `ValidateHandoff`  | Tautology: `aux[0] == hash(cert_hash, approved_root)` — the "approved_set_root" PI is not connected to any committed state |

### 1.4 The runtime `turn::Effect` enum

`turn/src/action.rs:221-...` lists the 41 runtime Effect variants. **None of
them are CapTP variants.** No `ExportSturdyRef`, no `EnlivenRef`, no `DropRef`,
no `ValidateHandoff`. Turn-executor logic at `turn/src/executor.rs:1362+`
(`convert_turn_effects_to_vm`) therefore can never produce a CapTP AIR row.

`turn/src/builder.rs:149-...` `ActionBuilder` has no CapTP helpers.

### 1.5 The application + SDK layers

- `app-framework/src/captp_server.rs:1-161` — `CapTpServer` wraps `SwissTable`
  in an `Arc<Mutex<...>>` and exposes `export` and `revoke`. **Imperative,
  in-memory, not connected to either the runtime executor or the AIR. Mounted
  as an axum `Extension`.**
- `sdk/src/captp_client.rs:1-733` — `CapTpClient { config, swiss_table,
  pipeline_registry, sessions }`. Methods: `export_sturdy_ref`, `enliven`,
  `enliven_uri`, `create_handoff`. **Client-side; wraps `captp/` directly.**
- `cli/src/commands/cap.rs:102+` — `enliven(uri)` command.
- `teasting/src/captp_sim.rs`, `teasting/tests/effect_vm_captp.rs`,
  `tests/src/captp_effects_pipeline.rs`, etc. — extensive simulation harnesses
  that exercise the AIR variants directly with synthesised `Effect::Export*`
  values.

### 1.6 Summary of the gap

| Layer                | ExportSturdyRef | EnlivenRef | DropRef | ValidateHandoff |
|---------------------|-----------------|-----------|---------|-----------------|
| `wire/` message     | yes (`EnlivenSturdyRef`) | yes | yes (`DropRemoteRef`) | yes (`PresentHandoff`) |
| `captp/` logic      | `SwissTable::export` | `SwissTable::enliven` | `ExportGcManager::process_drop` | `validate_handoff` fn |
| `wire/` server hook | yes — handler calls SwissTable directly | yes | yes | yes |
| runtime `Effect`    | **NO**           | **NO**     | **NO**  | **NO**           |
| `ActionBuilder`     | **NO**           | **NO**     | **NO**  | **NO**           |
| AIR variant         | yes (partly bound) | tautology | unbound | tautology       |
| committed state     | **NO** (in-mem only) | **NO**   | **NO**  | **NO**           |

The wire handlers and the AIR exist as two parallel universes that don't talk.
The committed federation state never sees the swiss table or the approved-set
root.

---

## 2. CapTP protocol quick-reference

Distilled from the OCapN spec (https://github.com/ocapn/ocapn) and the E
heritage. Terms used throughout the rest of this doc.

- **Vat** — a unit of synchronous execution holding capabilities. In dregg, a
  vat ≈ a federation (BFT consensus group), or equivalently a *strand* in the
  unified-lace model (`captp/src/lib.rs:135`).
- **Live ref** — an in-session handle to a capability. Cheap, transient,
  represented by a cell ID plus a session-keyed routing slot in
  `CapSession::imports` / `CapSession::exports`.
- **Sturdy ref** — a persistent, serializable capability identifier. In OCapN
  this is `ocapn://<vat>/<swiss>`. In dregg it is `dregg://<federation>/<cell>/<swiss>`
  (`captp/src/uri.rs`). The bearer of a valid sturdy ref can ask the target
  to mint a live ref via the *enliven* operation.
- **Swiss number** — a 32-byte unguessable random secret (`getrandom::fill` in
  `captp/src/sturdy.rs:92`). Possession of the swiss IS authorisation. The
  vat's swiss table maps swiss → `SwissEntry { cell_id, permissions, ... }`.
- **3-vat handoff (introduction)** — Alice wants Bob to be able to talk to
  Carol. Alice gives Bob a signed *gift* (handoff certificate) saying
  "introducer = Alice, recipient = Bob, target = Carol's cell, swiss = X".
  Bob redeems the gift at Carol's vat (`PresentHandoff`); Carol checks the
  signature and the swiss in her table, then issues Bob a live ref.
- **Promise pipelining** — `E <- E <- foo()` style. Cross-federation pipelined
  sends are handled by `captp/src/pipeline.rs` and `WireMessage::PipelinedMsg`.
  Out of scope here.
- **Distributed GC** — exporters track which remote vats hold refs to their
  cells; importers send `DropRemoteRef` when they release. This is the
  reference-counting half of `captp/src/gc.rs`.

Important constraint we will lean on heavily: **swiss numbers are the only
unforgeable secret.** Everything else (cert payloads, sturdy URIs) is just
ciphertext-grade until paired with a swiss number known to the target.

---

## 3. Runtime emitter design

Add four variants to `turn::Effect` (in `turn/src/action.rs`), four
`ActionBuilder` methods (in `turn/src/builder.rs`), and four projection arms
in `Self::convert_turn_effects_to_vm` (`turn/src/executor.rs:1362`).

### 3.1 Runtime `Effect` additions

```rust
// turn/src/action.rs — extend enum Effect

/// Export a cell as a sturdy reference.
///
/// The executor:
/// 1. Verifies the caller has authority over `cell` (cell owner or
///    DelegationMode::ParentsOwn parent with EXPORT capability).
/// 2. Generates a swiss number deterministically:
///       swiss = blake3("dregg-swiss-v1" || federation_id || cell || counter || random_seed)
///    where `counter` is `cell.state.fields[7]` interpreted as u64 LE.
/// 3. Inserts the entry into the federation's `swiss_table` and bumps
///    `cell.state.fields[7]`.
/// 4. Updates the cell's `swiss_table_root` commitment (see §4).
/// 5. Emits an `IntroductionExport` for the receipt so the wire layer's
///    `process_introduction_exports` can register the GC entry.
ExportSturdyRef {
    cell: CellId,
    permissions: AuthRequired,
    /// Optional restricted effect mask.
    allowed_effects: Option<EffectMask>,
    /// Optional expiry (federation block height).
    expires_at: Option<u64>,
    /// Optional use limit.
    max_uses: Option<u32>,
    /// 32-byte entropy. The actual swiss number is derived from this
    /// plus the export counter (see executor logic above). Including the
    /// seed in the effect makes the receipt deterministic and replayable.
    random_seed: [u8; 32],
},

/// Enliven a sturdy ref into a live ref on the target cell.
EnlivenRef {
    /// Cell being enlivened (extracted from the URI).
    target_cell: CellId,
    /// The swiss number being presented.
    swiss: [u8; 32],
    /// The strand/cell of the presenter (gets the live ref).
    presenter: CellId,
    /// Witness data: Merkle proof of `(swiss, SwissEntry)` membership in
    /// the target cell's `swiss_table_root`.
    membership_proof: SwissMembershipProof,
},

/// Drop a live ref / decrement the cross-federation refcount.
DropRef {
    /// The exported cell whose ref is being dropped.
    target_cell: CellId,
    /// The federation/strand that is dropping (the holder).
    holder: StrandId,
    /// Session epoch under which the original export occurred.
    session_epoch: u64,
    /// Witness: Merkle proof of `(holder, RefCount)` in the cell's
    /// `refcount_table_root`.
    refcount_proof: RefcountMembershipProof,
},

/// Validate and accept a handoff presentation, materialising a routing entry.
ValidateHandoff {
    /// Target cell named in the certificate.
    target_cell: CellId,
    /// The handoff presentation (certificate + recipient signature).
    presentation: HandoffPresentation,
    /// Witness: Merkle proof that `(introducer_pk, recipient_pk, swiss)`
    /// is a member of the federation's `approved_handoffs_root`.
    approved_proof: ApprovedHandoffProof,
},
```

Two new supporting types live in `turn/src/captp_witness.rs` (new file):
```rust
pub struct SwissMembershipProof {
    pub leaf_hash: [u8; 32],     // Poseidon2(swiss || cell || perms || nonce)
    pub path: Vec<[u8; 32]>,     // sibling hashes bottom-up
    pub directions: u64,         // packed left/right bits
}

pub struct RefcountMembershipProof {
    pub leaf_hash: [u8; 32],     // Poseidon2(holder || refcount || session_epoch)
    pub path: Vec<[u8; 32]>,
    pub directions: u64,
}

pub struct ApprovedHandoffProof {
    pub leaf_hash: [u8; 32],     // Poseidon2(certificate.signing_message_hash || recipient_pk)
    pub path: Vec<[u8; 32]>,
    pub directions: u64,
}
```

### 3.2 `ActionBuilder` helpers

`turn/src/builder.rs` gains, alongside `set_field`, `transfer`, etc.:

```rust
pub fn export_sturdy_ref(&mut self, cell: CellId, permissions: AuthRequired)
    -> &mut Self;
pub fn export_sturdy_ref_with_options(&mut self, cell: CellId,
    permissions: AuthRequired, allowed_effects: Option<EffectMask>,
    expires_at: Option<u64>, max_uses: Option<u32>) -> &mut Self;

pub fn enliven_ref(&mut self, target: CellId, swiss: [u8; 32],
    presenter: CellId, proof: SwissMembershipProof) -> &mut Self;

pub fn drop_ref(&mut self, target: CellId, holder: StrandId,
    session_epoch: u64, proof: RefcountMembershipProof) -> &mut Self;

pub fn validate_handoff(&mut self, target: CellId,
    presentation: HandoffPresentation, proof: ApprovedHandoffProof) -> &mut Self;
```

### 3.3 Executor mutation

In `turn/src/executor.rs::apply_effect` (the per-Effect dispatch — currently
where `Effect::Transfer` etc. live), the four new arms:

- `ExportSturdyRef`:
  - Auth check (caller has EXPORT cap, cell is not frozen, not sovereign-locked).
  - Compute `swiss = poseidon2(domain, fed_id, cell_id, counter, random_seed)`.
  - Insert `SwissEntry` into the federation's swiss table.
  - Recompute the target cell's `swiss_table_root` (an `incremental Merkle root`
    over swiss entries; see §4.1).
  - Update `cell.state.fields[7]` with `counter + 1` (binds AIR's old/new f7
    pair to actual swiss-table-state transition).
  - Append `IntroductionExport { target: cell, recipient: STRAND_OF_HOLDER }`
    to the turn's intro-export list so `CapTpState::process_introduction_exports`
    can record the GC entry on commit.

- `EnlivenRef`:
  - Verify the membership proof against the target cell's `swiss_table_root`.
  - Verify expiry / max-uses against the entry in the proof.
  - Increment the entry's `use_count` (this changes the leaf hash → swiss
    table root rotates → recompute `swiss_table_root`).
  - Increment `cell.state.fields[6]` (use_count surface for AIR).
  - Issue a live-ref token: emit a `GrantCapability` sub-effect that places
    a routing entry into the presenter's c-list (this also exercises the
    existing `cap_root` constraint).

- `DropRef`:
  - Verify the refcount proof against the target cell's `refcount_table_root`.
  - Verify `current_refcount > 0`.
  - Verify `session_epoch == entry.session_id`.
  - Decrement the refcount; remove the leaf if it hits zero.
  - Update `refcount_table_root` and `cell.state.fields[5]` (refcount surface
    for AIR).

- `ValidateHandoff`:
  - Verify both signatures via the existing `validate_handoff` function path
    (off-chain verification still happens — the AIR proves *only set
    membership*, not Ed25519, see §6).
  - Verify the membership proof against the federation's
    `approved_handoffs_root`.
  - Mint a fresh routing token; store routing-entry leaf into the target
    cell's `cap_root` (the existing AIR constraint already updates `cap_root`
    via `hash_2_to_1(old_cap, hash_2_to_1(recipient_pk, cert_hash))`; that
    becomes meaningful once tied to a real approved root).

### 3.4 Projection (`convert_turn_effects_to_vm`)

Each runtime variant projects to exactly one AIR Effect:

```rust
Effect::ExportSturdyRef { cell, permissions, random_seed, .. } if cell == cell_id => {
    let counter = read_field7_as_u32(state_before);
    vm_effects.push(VmEffect::ExportSturdyRef {
        cell_id: hash_to_bb_full(&cell.0),   // Poseidon2-based, not truncating
        permissions: perms_to_bb(permissions),
        random_seed: hash_to_bb_full(random_seed),
        export_counter: counter,
    });
}
// EnlivenRef, DropRef, ValidateHandoff: structurally similar, with the
// proof's leaf_hash / membership witness piped into aux[0..] columns.
```

The projection is total once Stage 1 of EFFECT-VM-SHAPE-A lands; for now
each arm produces exactly one VM effect with no NoOp loss.

---

## 4. Fixing the tautological AIR constraints

The fundamental problem in the existing AIR is that the executor witnesses
the *result of a computation it already did*, with no binding to any
committed state. The fix in both cases is the same: introduce a Merkleized
table whose root is a committed column in the cell's (or federation's) state.

### 4.1 `EnlivenRef`: swiss-table Merkle binding

**Where the root lives.** Add a `swiss_table_root: [u8; 32]` column to
`dregg_cell::CellState` (`cell/src/state.rs:34-57`). It is included in
`compute_canonical_state_commitment` (the cell-fix work referenced in
EFFECT-VM-SHAPE-A Stage 1). The root is initialised to the empty-tree hash;
it is updated whenever `ExportSturdyRef` or `EnlivenRef` runs.

The tree is a depth-32 sparse Merkle tree keyed by `swiss[0..32]` (treated as
a 256-bit path), with leaves `Poseidon2(swiss || cell_id || permissions ||
expires_at || max_uses || use_count)`. Empty positions hash to a known
sentinel. This is the same primitive shape used by the existing capability
root.

**New AIR columns / params.** No new state columns beyond `swiss_table_root`,
but the EnlivenRef variant needs a wider aux witness for the Merkle path:

```
PARAM[ENLIVEN_SWISS]            // swiss number (existing)
PARAM[ENLIVEN_CELL_ID]          // existing
PARAM[ENLIVEN_PERMISSIONS]      // existing
PARAM[ENLIVEN_USE_COUNT_BEFORE] // NEW — the use_count being witnessed
PARAM[ENLIVEN_USE_COUNT_AFTER]  // NEW — constrained to BEFORE+1

AUX[0..32]                      // Merkle path siblings (32 levels)
AUX[32]                         // packed direction bits
AUX[33]                         // leaf_hash_before
AUX[34]                         // leaf_hash_after
AUX[35]                         // swiss_table_root_before
AUX[36]                         // swiss_table_root_after
```

(The current 11-aux budget is too tight; this is part of the AIR width growth
already on the table in Stage 1.)

**New constraints:**
1. `aux[33] == Poseidon2(swiss || cell_id || perms || use_count_before)` —
   bind the leaf.
2. `aux[34] == Poseidon2(swiss || cell_id || perms || use_count_after)` —
   bind the updated leaf.
3. `use_count_after - use_count_before - 1 == 0` — monotonic increment.
4. `aux[35] == merkle_root(aux[33], aux[0..32], dirs)` — root_before contains
   the old leaf.
5. `aux[36] == merkle_root(aux[34], aux[0..32], dirs)` — same path, updated
   leaf, gives root_after.
6. `aux[35] == swiss_table_root in state_before` — bind to committed state.
7. `aux[36] == swiss_table_root in state_after` — bind to committed state.

This is non-tautological: the prover must know a swiss number such that *the
committed swiss_table_root* contains an entry for it. Without that, no
witness exists.

`ExportSturdyRef` gets the same Merkle-update treatment (insert), reusing the
same aux columns: old leaf is the empty sentinel, new leaf is the freshly
created `SwissEntry`. The existing `swiss = hash(cell_id, hash(random_seed,
counter))` binding stays; the counter is additionally bound to `field[7]`
(Stage 2 fix from EFFECT-VM-SHAPE-A).

### 4.2 `ValidateHandoff`: approved-handoffs Merkle binding

**Where the root lives.** Federation-scoped, not cell-scoped. Add an
`approved_handoffs_root: [u8; 32]` to the federation state (next to
`federation_root` in `node/src/state.rs:53` `NodeState` / the executor's
federation-state struct). The root is committed in `dregg_circuit::pi::PI`
as a new public input `pi::APPROVED_HANDOFFS_ROOT` (4 BabyBears once Stage 1
widens commitments).

**Provenance of entries.** When the target federation accepts a
`HandoffCertificate` *off-chain* (the `validate_handoff` Ed25519/signature
check at `captp/src/handoff.rs:366-414`), it computes
`leaf = Poseidon2(introducer_pk || recipient_pk || target_cell || swiss ||
nonce)` and inserts that leaf into the approved-handoffs tree. The insertion
itself is **not** in-AIR — it is a federation-state mutation that happens at
the same time as the off-chain signature check. The AIR then proves
"recipient presented a certificate already approved by this federation."

The reason for the split: Ed25519 in-AIR is expensive. Off-chain signature
validation by the federation's BFT majority is cheap and sufficient because
the federation is the trust root for that root.

**New AIR columns / params:**

```
PARAM[HANDOFF_CERT_HASH]              // existing
PARAM[HANDOFF_RECIPIENT_PK]           // existing
PARAM[HANDOFF_INTRODUCER_PK]          // existing
PARAM[HANDOFF_APPROVED_SET_ROOT]      // existing (now actually bound to PI)
PARAM[HANDOFF_NONCE]                  // NEW — the cert nonce
PARAM[HANDOFF_TARGET_CELL]            // NEW — the target cell id

AUX[0..32]                            // Merkle path siblings
AUX[32]                               // direction bits
AUX[33]                               // leaf hash (membership)
```

**New constraints:**
1. `aux[33] == Poseidon2(introducer_pk || recipient_pk || target_cell ||
   swiss || nonce)`.
2. `merkle_root(aux[33], aux[0..32], dirs) == HANDOFF_APPROVED_SET_ROOT`.
3. `HANDOFF_APPROVED_SET_ROOT == pi::APPROVED_HANDOFFS_ROOT` — bind PI param
   to global PI input.
4. The cap-root update stays as-is: `new_cap_root = hash(old, hash(recipient_pk,
   cert_hash))`. This is the routing-entry creation.

Plus a **single-use** binding: see §9 below.

### 4.3 `DropRef`: refcount-table Merkle binding

**Where the root lives.** Per-cell. Add `refcount_table_root: [u8; 32]` to
`CellState`, keyed by `holder_strand` (`[u8;32]`), value
`Poseidon2(holder || refcount || session_epoch || last_activity)`.

This mirrors `captp/src/gc.rs::ExportEntry::holders: HashMap<FederationId,
RefCount>`. The in-memory map becomes a committed Merkle tree.

**Constraints:**
1. `aux_leaf_before == Poseidon2(holder || rc_before || epoch || activity_before)`.
2. `rc_before > 0` (existing inverse-trick, already correct).
3. `rc_after = rc_before - 1`.
4. `aux_leaf_after == Poseidon2(holder || rc_after || epoch || activity_before)`
   *or* the empty sentinel if `rc_after == 0` (gated by a selector subterm).
5. `merkle_root(leaf_before, path) == old refcount_table_root`.
6. `merkle_root(leaf_after, path) == new refcount_table_root`.
7. `holder_param == param.holder_federation` (already in AIR, just unbound;
   becomes bound to the Merkle key).
8. `field[5]` constraint: `new_f5 - old_f5 + 1 == 0` stays — it now reflects
   the *total* refcount for the cell, which equals the sum of all leaves'
   refcounts. To make this tractable we maintain `total_refs` redundantly as
   `field[5]` and constrain it to decrement by one per `DropRef`. (The full
   tree-sum constraint is intractable in a single-row AIR; redundant
   `total_refs` is the right tradeoff.)

---

## 5. Live ref ↔ sturdy ref lifecycle

End-to-end walk, showing each step's runtime + AIR + wire layer:

1. **Alice exports.** Alice's cclerk calls `CapTpClient::export_sturdy_ref`,
   which builds a `TurnBuilder` with one `ActionBuilder::export_sturdy_ref`
   action targeting Alice's federation's swiss-keeper cell.
   - Runtime: `Effect::ExportSturdyRef` runs in the executor. Alice's
     federation's swiss table gains the new entry. `swiss_table_root` rotates.
   - AIR: `Effect::ExportSturdyRef` produces a row with the new leaf inserted
     into the Merkle tree (old leaf = empty sentinel, new leaf = the entry).
   - Wire: when the turn is committed, the federation's `CapTpState` notes
     the export (via `process_introduction_exports`-style hook if there is a
     recipient federation, or via a local-only mark if not).
   - Output: `DreggUri { federation_id, cell_id, swiss }`, serialized to a
     `dregg://...` string. Alice can paste this anywhere.

2. **Out-of-band transmission.** Alice gives Bob the URI string. Could be QR
   code, email, BLE, file. Not a wire concern; not an AIR concern.

3. **Bob enlivens (potentially much later, new session).**
   - Bob's cclerk parses the URI, computes the Merkle path against Alice's
     federation's current `swiss_table_root` (queried via the wire layer's
     existing read APIs).
   - Bob's cclerk sends a turn to Alice's federation targeting the
     swiss-keeper cell with `ActionBuilder::enliven_ref(target, swiss,
     presenter=Bob's strand, proof=...)`.
   - Alternative path (today): Bob sends `WireMessage::EnlivenSturdyRef`,
     the server processes it imperatively. **In the new design this path
     becomes a wrapper: the server constructs the turn on Bob's behalf and
     submits it through the executor.** The imperative shortcut is removed.
   - Runtime: `Effect::EnlivenRef` runs. The proof is verified.
     `cell.state.fields[6]` increments. The swiss-table-root rotates (to
     reflect the bumped use_count). An `Effect::GrantCapability` is appended
     to give Bob's c-list a routing entry.
   - AIR: `Effect::EnlivenRef` row + `Effect::GrantCapability` row.
   - Output: Bob holds a live ref — a `CapabilityRef` in his c-list pointing
     to Alice's cell.

4. **Bob exercises.** Bob issues a turn targeting Alice's cell using the
   live ref as `Authorization::Breadstuff(token)` or
   `Authorization::Proof(...)`. The c-list lookup in
   `turn/src/executor.rs`'s authorization check confirms Bob has the routing
   entry. No new AIR variant needed — this exercises the existing turn
   auth path.

5. **Bob drops.** Bob's cclerk (or the GC sweeper) calls
   `ActionBuilder::drop_ref(target, holder=Bob's strand, session_epoch,
   refcount_proof)`. The runtime decrements; AIR proves it.
   - Wire: the existing `DropRemoteRef` message is now produced *as a result
     of committing a `DropRef` turn*, not as a hand-rolled side channel.

**Where the refcounts live.** Per-cell, in the committed `refcount_table_root`
defined in §4.3. The federation-level `CapTpState::export_gc`
(`wire/src/server.rs:902`) becomes a *cache* of that committed state, not the
source of truth. The source of truth is the cell's state.

---

## 6. Handoff lifecycle (3-vat introduction)

Alice introduces Bob to Carol.

1. **Alice asks Carol for a swiss.** Alice sends an
   `ActionBuilder::export_sturdy_ref` turn to Carol's federation, targeting
   the cell Alice wants Bob to be able to talk to. This is exactly the
   ExportSturdyRef path above. The swiss number lands in Carol's swiss table
   and her `swiss_table_root` rotates.
   - Note: this requires Alice to have export authority on Carol's cell.
     In the OCapN model, that authority is exactly the live ref Alice already
     holds.

2. **Alice signs a handoff certificate.** Alice's cclerk calls
   `HandoffCertificate::create(introducer_key=Alice, introducer_fed=A,
   target_fed=C, target_cell=Carol's cell, recipient_pk=Bob, ..., swiss=X)`
   (`captp/src/handoff.rs:142-177`). The cert is serialised to a
   `dregg-handoff:...` string. **No runtime / AIR involvement.**

3. **Alice transmits the cert to Bob** (out-of-band, like a sturdy ref).

4. **Alice tells Carol "Bob is approved."** Either (a) the cert is forwarded
   to Carol immediately and she adds it to her approved set, or (b) Carol
   maintains an *open admission* mode where any cert signed by a federation
   in her `known_federations` list is auto-approved on presentation.
   - **Recommendation: (b) for low friction.** The federation-state mutation
     happens at presentation time. The federation's BFT majority verifies the
     Ed25519 signature on the cert, then inserts the corresponding leaf into
     `approved_handoffs_root`. This insertion is part of the same turn that
     contains the `ValidateHandoff` effect.

5. **Bob redeems at Carol's federation.** Bob's cclerk calls
   `ActionBuilder::validate_handoff(target=Carol's cell, presentation=...,
   proof=...)`.
   - Wire: Bob sends `WireMessage::PresentHandoff { presentation_bytes,
     introducer_pk }`. Carol's server validates the signatures (off-chain),
     extends `approved_handoffs_root` with the new cert leaf, then submits
     a turn containing the `Effect::ValidateHandoff`.
   - Runtime: signature checks already passed off-chain (they had to, to
     add to the approved root). The executor verifies the Merkle proof
     against the freshly-updated root.
   - AIR: `Effect::ValidateHandoff` row proves membership; updates `cap_root`
     with the routing entry.

6. **Carol's cell now has a routing entry for Bob.** Subsequent turns from
   Bob to Carol's cell authorize via the c-list lookup. The handoff is
   complete.

**Sub-step: enliven inside handoff.** Step 5 implicitly enlivens the swiss
that Alice exported in step 1. Two designs:
- **Option A:** the `ValidateHandoff` effect also bumps the swiss-table-root
  (i.e., one turn, two Merkle updates in one row — needs aux budget but is
  feasible).
- **Option B:** `ValidateHandoff` and `EnlivenRef` are separate runtime
  effects in the same turn, two rows.

**Recommendation: Option B.** Two clean variants, each with their own
single-purpose AIR row. The turn becomes:
1. `Effect::EnlivenRef { target=Carol's cell, swiss, presenter=Bob }`
2. `Effect::ValidateHandoff { target=Carol's cell, presentation, proof }`

The two effects act on different roots (swiss-table-root vs cap-root) so they
don't conflict; the executor runs them in order.

---

## 7. Federation-level CapTP

`dregg`'s twist: vats are BFT-replicated federations, not single processes.
Sessions and refs cross federation boundaries.

### 7.1 Intra-federation CapTP

The trivial case: both cells live in the same federation. The federation
maintains the swiss table, the approved-handoffs root, and the per-cell
refcount trees as part of its consensus-replicated state. All AIR proofs
verify against state that the verifier already has. **Done; no wire layer
involvement.** The session abstraction is unnecessary for intra-federation
exchanges — use direct turn-commit instead.

### 7.2 Inter-federation CapTP

Alice in federation A, Carol in federation C, Bob in federation B. Three
trust domains.

**Source of truth for `swiss_table_root`:** Carol's federation C. The root
is a public input to AIR proofs about Carol's cell. When Alice in A wants to
prove she enlivened correctly, she needs to verify *against C's current
root* — but A doesn't have C's state.

Two paths, depending on the operation:

- **Operations on a cell happen at that cell's home federation.** When Bob
  enlivens Alice's sturdy ref for Carol's cell, the EnlivenRef turn runs at
  C. C's executor has C's swiss_table_root. C's AIR proof is verifiable by
  anyone with C's state commitments. Bob never has to prove anything against
  A's state.

- **Cross-federation receipts.** A's federation observes the EnlivenRef
  receipt from C (via the bridge / blocklace replication pattern from
  `bridge/`). A's `ExportGcManager` records that B holds a ref, so that
  later `DropRef` messages can be validated. The receipt-relay path uses
  existing bridge primitives (`bridge/src/mina.rs`-style attestations or
  the blocklace cross-reference mechanism in `blocklace/src/cross_reference.rs`).

**The wire layer's role.** `wire/src/captp.rs` does not exist as a separate
file today; CapTP wire messages are in `wire/src/message.rs` and the
handler is in `wire/src/server.rs`. The CapTP wire layer should:

1. Carry the existing `CapHello`/`CapGoodbye`/`EnlivenSturdyRef`/
   `DropRemoteRef`/`PresentHandoff`/`HandoffAccepted` messages between
   federation gateways.
2. **For each incoming CapTP wire message, translate it into a turn
   submission against the local federation's executor**, rather than
   mutating `CapTpState` directly. This is the key change. The
   imperative shortcut (`wire/src/server.rs:2289-2350`) becomes a *turn
   builder*.
3. The receipt of that turn (with its AIR proof) is what gets returned to
   the remote peer. So `EnlivenResponse` ends up carrying a `Receipt` (with
   STARK proof), not just `success: bool`.

This unifies CapTP with the rest of the protocol: every cross-federation
authority-changing operation is a proven turn.

### 7.3 Federation handoff (cross-federation introductions)

The handoff certificate in `captp/src/handoff.rs` already supports this
natively (`introducer: FederationId`, `target_federation: FederationId`,
recipient is just a public key). The change: the target federation's
`approved_handoffs_root` now becomes a committed root that other federations
can attest to.

For the *introducer* federation (A) to be able to forward a handoff to the
*target* federation (C) on behalf of a recipient in (B), all three
federations need to be in some shared trust mesh. The existing
`known_federations` list in `wire/src/server.rs:903` is the precursor;
it should evolve into a committed `trusted_federations_root` that
`ValidateHandoff` cross-checks (as a future Stage). For now, treating
`known_federations` as an admin-managed list is acceptable; the AIR
constraint only proves the cert is in the approved root, regardless of how
the federation came to approve it.

---

## 8. Integration with `EFFECT-VM-SHAPE-A.md`

Mapping this work onto the existing Shape A stages.

### 8.1 Stage 1 (foundation: widened commitment, total projection)

This work *depends on* Stage 1 because:
- The AIR fixes in §4 require 4-BabyBear state commitments to fit the new
  Merkle roots (`swiss_table_root`, `refcount_table_root`) without aliasing.
- The projection in §3.4 assumes the totalised `convert_turn_effects_to_vm`
  shape introduced in Stage 1.

No new work for Stage 1 from this design — just additional fields to include
in `compute_canonical_state_commitment`:
- `CellState::swiss_table_root: [u8; 32]`
- `CellState::refcount_table_root: [u8; 32]`
- Federation-level `approved_handoffs_root` joins PI alongside
  `federation_root`.

### 8.2 Stage 2 (honesty pass)

The four CapTP variants are Stage 2 work:
- `ValidateHandoff`: implement §4.2 (real approved-set Merkle proof).
- `EnlivenRef`: implement §4.1 (real swiss-table Merkle proof + use_count
  bound).
- `DropRef`: implement §4.3 (real refcount-table Merkle proof; bind
  `holder_federation` param to the Merkle key).
- `ExportSturdyRef`: bind `param.export_counter == old_f7` (small fix
  per EFFECT-VM-SHAPE-A line 39), plus add the Merkle-insert path.

Add adversarial tests for each: prover tries to claim membership in a fake
root, prover tries to enliven without the swiss, prover tries to drop with
the wrong epoch.

### 8.3 Stage 3 (Group B — new variants)

No new AIR variants needed for CapTP — all four already exist. **Stage 3 is
not on the CapTP critical path.**

### 8.4 Stage 7 (runtime emitters for AIR-only orphans)

This is the primary new work this design specifies:
- Add the four runtime `Effect` variants (§3.1).
- Add the four `ActionBuilder` helpers (§3.2).
- Implement the four executor arms (§3.3).
- Implement the four projection arms (§3.4).
- New file `turn/src/captp_witness.rs` (the proof types).
- New file `turn/src/captp_state.rs` for the per-federation in-memory state
  helpers (swiss table + refcount tree + approved-handoffs tree wrappers).

Wire-layer rework (§7.2): convert the imperative handlers in
`wire/src/server.rs:2243-2350` to turn-submission paths. This is best done
*after* Stage 7 has stable runtime emitters — call it **Stage 7b**.

### 8.5 Estimated effort

- Stage 2 CapTP-honesty: ~2 days (Merkle wiring; new aux columns).
- Stage 7 runtime emitters: ~3 days (parallel to Stage 7 main body).
- Stage 7b wire rework: ~2 days.

Total: ~7 days of focused opus work on top of the 25–30 days for the full
Shape A plan.

---

## 9. Adversarial considerations

Each attack vector and the design's response.

### 9.1 Forged sturdy ref to a cell not owned

**Attack:** Mallory calls `ActionBuilder::export_sturdy_ref(cell=alice_cell, ...)`.

**Defence:** `Effect::ExportSturdyRef` authorisation check in the executor
requires the caller to hold EXPORT capability on the target cell. The cell's
c-list / `cap_root` is consulted (same path as any other cell-mutating
effect). No new mechanism — the existing auth machinery handles it.

**AIR-level reinforcement:** the AIR doesn't prove the auth check (that's
the turn-executor's job, and the turn signature covers the action), but it
*does* prove the swiss-table insert. A forged ExportSturdyRef row would have
to update a cell-state column the prover doesn't legitimately own, which is
caught by the boundary-pinning constraints on `cell_id`.

### 9.2 Enliven a sturdy ref after the cell is destroyed/migrated

**Attack:** Alice exports cell X as a sturdy ref. Alice destroys cell X (or
calls `MakeSovereign`, or migrates to another federation). Bob tries to
enliven.

**Defence:**
- Destroyed: the cell no longer exists in the federation state. The swiss
  table either lives in the destroyed cell (gone) or in a per-federation
  table tied to the cell's lifecycle. **Design choice:** swiss table lives
  in the cell's state, so destruction wipes it. EnlivenRef can't produce a
  membership proof against a non-existent cell.
- `MakeSovereign`: a sovereign cell still exists; its `swiss_table_root`
  remains valid. Sovereignty doesn't break sturdy refs. (This is intentional
  — sovereignty is about who controls upgrades, not about ref hygiene.)
- Migration: when a cell migrates between federations, its
  `swiss_table_root` migrates with it. The new federation honours the
  existing sturdy refs. Cross-federation migration is currently scaffolded
  in `turn/src/executor.rs` (`CellMigrationManager`); migrating swiss roots
  is a new constraint to add there.

### 9.3 Sturdy ref replay

**Attack:** Bob enlivens, uses the ref, then enlivens again, then again.

**Defence:** `SwissEntry::max_uses` + `SwissEntry::expires_at` (already
present in `captp/src/sturdy.rs:42-60`). The use_count is per-entry and
bound into the leaf hash, so the AIR can prove "this enliven was the Nth use
where N < max_uses." For one-time-use sturdy refs, set `max_uses: Some(1)`
at export time.

**Replay across sessions:** the swiss number is the secret; whoever has it
can enliven. Sharing the sturdy URI shares authority. This is the OCapN
model and is by design. To restrict to a specific recipient, use a handoff
certificate instead (which binds to `recipient_pk`).

### 9.4 Handoff certificate replay

**Attack:** Bob presents the same handoff certificate twice.

**Defence:** Two layers.
- Layer 1 (off-chain): `HandoffCertificate::nonce: [u8; 32]` is in the
  signing message. The federation maintains a `seen_handoff_nonces` set
  (already alluded to in `HandoffError::ReplayDetected` at
  `captp/src/handoff.rs:55-58`). Second presentation fails the off-chain
  check.
- Layer 2 (AIR): the approved-handoffs tree is a *consumed-on-use* structure.
  When `ValidateHandoff` proves membership of leaf
  `Poseidon2(introducer_pk || recipient_pk || target_cell || swiss || nonce)`,
  the executor *removes* that leaf in the same step (leaf becomes the empty
  sentinel). The AIR proves the removal: old root contains the leaf, new
  root contains the sentinel at the same path. This is the *single-use
  Merkle root* the task specs as the answer.

This means re-presenting the same cert produces a non-membership witness,
which the AIR cannot satisfy. **Hard cryptographic single-use guarantee.**

### 9.5 Stale-epoch DropRef

**Attack:** Bob's federation B sends a DropRef from session epoch N for a
ref granted in epoch N+1. The drop would tank the refcount erroneously.

**Defence:** Already handled in `ExportGcManager::process_drop_with_session`
(`captp/src/gc.rs`). The leaf in `refcount_table_root` includes
`session_epoch`; the AIR constraint requires `param.session_epoch ==
leaf.session_epoch`. Stale epochs fail Merkle membership.

### 9.6 Approved-handoffs root forgery

**Attack:** Mallory (a Byzantine federation member) tries to commit a turn
where `approved_handoffs_root` jumps to a value containing certs that were
never approved.

**Defence:** `approved_handoffs_root` is part of the federation's BFT-
replicated state. Mutations to it require BFT consensus (≥ ⅔ honest
attestations). A single Byzantine node cannot rotate the root. This is the
same trust assumption as the rest of federation state.

**Soundness:** an honest federation member can verify root mutations by
re-running the off-chain signature checks. If a proposed block adds a cert
to `approved_handoffs_root` without a valid introducer signature, honest
nodes vote against the block.

### 9.7 Holder-key forgery in refcount table

**Attack:** Mallory's federation X claims a refcount on Alice's cell that
they never received an introduction for.

**Defence:** `refcount_table_root` leaves are only inserted by
`ExportSturdyRef` / `ValidateHandoff` effects, which themselves require
authority over the target cell. A federation can't unilaterally insert a
leaf into another federation's cell's refcount table. The refcount table
mutates only as a side-effect of authority-granting turns from the cell's
home federation.

### 9.8 Sturdy-ref enliven from a presenter without the swiss

**Attack:** Eve sees the swiss number on the wire (e.g., from a leaked log)
and enlivens.

**Defence:** This is *not* an attack against the protocol — the swiss
number IS the bearer secret. Whoever has it has the authority. **Mitigation
is operational, not protocol-level:** transmit swiss numbers over
encrypted channels, use short-lived sturdy refs, prefer handoff certificates
(which bind to a recipient public key) when the recipient is known.

### 9.9 AIR-side: tautology slipping back in

**Attack:** A future PR weakens an AIR constraint to take the membership
root from aux instead of param/PI.

**Defence:** Adversarial regression tests, one per variant:
- `enliven_ref_with_arbitrary_root_rejected`: prover supplies a real
  Merkle proof against a root they invented; verifier rejects because
  the PI root doesn't match.
- `validate_handoff_replay_rejected`: prover presents the same cert
  twice; second turn fails because the leaf was removed.
- `drop_ref_wrong_epoch_rejected`: prover uses session_epoch = N when the
  committed leaf has epoch = N+1.

These tests gate Stage 2 merging. (`tests/src/captp_effects_pipeline.rs`
is the natural home.)

---

## 10. Open design questions

1. **Cell-state vs federation-state for `swiss_table_root`.** This design
   puts it per-cell. Alternative: a single per-federation swiss table,
   keyed by `(cell_id, swiss)`. Per-cell is more local and migration-
   friendly; per-federation is fewer Merkle roots. **Recommendation: per-
   cell.**
2. **Live-ref representation.** Currently a `CapabilityRef` in the
   recipient's c-list. Should there be a distinct `LiveRefSlot` type?
   **Recommendation: no — keep using `CapabilityRef` so existing c-list
   machinery transparently supports CapTP-issued refs.**
3. **In-AIR Ed25519 for handoffs.** Alternative to off-chain-then-Merkle:
   verify the introducer signature inside the AIR. ~30k constraints per
   verification. **Recommendation: defer; off-chain-then-Merkle is
   sufficient for the federation trust model.** Revisit when single-vat
   cipherclerks need to verify handoffs without federation trust.
4. **Garbage collection of `approved_handoffs_root` leaves.** Leaves
   consumed on ValidateHandoff. What about expired-but-unused certs?
   **Recommendation: a periodic sweep effect (`PruneHandoffs`) that
   removes expired leaves; added in a later stage.**
5. **`SturdyRef → LiveRef` cache.** Should the wire layer cache successful
   enlivens to avoid re-proving the Merkle path? **Recommendation: yes,
   per-session in `CapSession::imports`, but the cache is advisory — the
   first cross-federation hop after a session restart re-proves.**

---

## 11. Implementation order

A safe sequencing for the actual PRs:

1. **PR 1: cell state extensions.** Add `swiss_table_root` and
   `refcount_table_root` to `CellState`. Add `approved_handoffs_root` to
   federation/PI. Plumb through `compute_canonical_state_commitment`.
   Zero behaviour change; all roots start empty.
2. **PR 2: runtime emitters.** Add the four `turn::Effect` variants, the
   four `ActionBuilder` helpers, the executor arms, and the projection
   arms. No AIR changes yet — projection emits the (still-tautological)
   existing AIR variants. Behaviour is honest at the runtime level.
3. **PR 3: AIR honesty.** Implement §4.1, §4.2, §4.3. New aux columns; new
   Merkle constraints; adversarial tests. **This is the critical PR.**
4. **PR 4: wire-layer rework.** Convert `wire/src/server.rs` CapTP handlers
   to turn-submission. `EnlivenResponse` now carries a receipt.
5. **PR 5: handoff single-use.** Add the consume-on-use leaf removal to
   `ValidateHandoff`. Adversarial replay test gates merge.
6. **PR 6: migration interop.** Make `CellMigrationManager` migrate
   swiss/refcount roots along with the cell.

PRs 1–3 are blocking for the EFFECT-VM-SHAPE-A Stage 2 honesty milestone.
PRs 4–6 are post-Stage-7 polish.

---

## 12. References

Code:
- `captp/src/lib.rs:1-162` — crate root
- `captp/src/sturdy.rs:67-214` — `SwissTable`
- `captp/src/handoff.rs:104-414` — `HandoffCertificate`, `validate_handoff`
- `captp/src/session.rs:23-220` — `CapSession`
- `captp/src/gc.rs:38-200` — `ExportGcManager`, `RefCount`
- `wire/src/message.rs:240-346` — CapTP wire variants
- `wire/src/server.rs:895-981, 2243-2350` — `CapTpState`, handlers
- `circuit/src/effect_vm.rs:489-539, 1563-1769, 2840-2925` — AIR variants
- `circuit/src/effect_interp.rs:786-927` — interp mirror
- `app-framework/src/captp_server.rs:1-161` — axum wrapper
- `sdk/src/captp_client.rs:1-733` — client SDK
- `turn/src/action.rs:221-...` — runtime `Effect` (no CapTP variants today)
- `turn/src/builder.rs:149-...` — `ActionBuilder` (no CapTP helpers today)
- `turn/src/executor.rs:1362-...` — `convert_turn_effects_to_vm`
- `EFFECT-VM-SHAPE-A.md` — the master plan this design extends
- `REVIEW-effect-vm.md` — the protocol review that identified the orphans

Specs:
- OCapN: https://github.com/ocapn/ocapn
- Spritely Goblins (E-tradition reference impl):
  https://spritely.institute/goblins/
- Mark Miller, "Robust Composition" thesis — the canonical sturdy-ref/
  handoff semantics.
