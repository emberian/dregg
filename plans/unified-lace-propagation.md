# Unified Lace Propagation Plan

All 6 phases of the unified blocklace migration are complete (199 tests pass).
The `blocklace` crate now exposes:

- `ReferenceGroup` + `tau_unified` (replaces per-federation ordering)
- `GovernedReferenceGroup` + `GovernanceMode` (replaces Constitution-only membership)
- `Subscription` (interest-based dissemination)
- `DelegationManager` (executor delegation)
- `FabricAddress` / `GroupId` / `StrandId` (replaces FederationId as routing target)
- `CrossReference` / `DagDeliveredProof` (cross-group DAG references)
- `FederationId` (backward-compat type in `blocklace::addressing`)

This document catalogs every place in the codebase that still assumes the OLD
model (separate federations, FederationId everywhere) and what needs to change.

---

## captp/ (Capability Transport Protocol)

### Summary
CapTP defines its OWN `FederationId` struct at `captp/src/lib.rs:112`. In the
new model, CapTP sessions are between STRANDS (bilateral), addressed by StrandId
or FabricAddress. The "federation" a capability belongs to is just a GroupId.

### Instances

| File | Lines | What | New Model | Difficulty | Priority |
|------|-------|------|-----------|------------|----------|
| `lib.rs` | 112-138 | `pub struct FederationId` definition | Keep as compat alias; add doc note saying "equivalent to GroupId in unified model" | trivial | done |
| `gc.rs` | 51, 98-200 | `ExportGcManager.holders: HashMap<FederationId, RefCount>` | Should key by StrandId or FabricAddress (the HOLDER's strand, not their "federation") | moderate | can-wait |
| `gc.rs` | 270, 290-351 | `ImportGcManager.imports: HashMap<(FederationId, CellId), ImportEntry>` | Key by (StrandId, CellId) | moderate | can-wait |
| `handoff.rs` | 99, 136, 362 | `introducer: FederationId`, `known_federations: &[FederationId]` | Introducer is a StrandId; known set becomes known GroupIds | moderate | can-wait |
| `pipeline.rs` | 61, 95, 271, 360, 425-688 | `sender: FederationId`, `notify_federation`, outbox keyed by FederationId | All should be StrandId (pipeline is bilateral) | moderate | can-wait |
| `store_forward.rs` | 50, 76, 135, 653, 768-872 | `destination: FederationId`, queues keyed by FederationId | Destination is a FabricAddress; queues keyed by StrandId | major | can-wait |
| `sturdy.rs` | 143, 146 | `make_uri(federation_id: [u8; 32], ...)` | Parameter name stays (URI format is stable) but doc updated | trivial | done |
| `uri.rs` | 67, 92 | `federation_id: [u8; 32]` field in PyanaUri | Keep field (wire format stable); add doc alias "group_id" | trivial | done |

### Strategy
Add a doc comment and type alias re-export at `captp/src/lib.rs` bridging
`FederationId` to the blocklace concept. No structural change yet.

---

## wire/ (Wire Protocol)

### Summary
WireMessage variants use `federation_id: [u8; 32]` and `federation_root: [u8; 32]`
throughout. The server tracks `PeerRole::CapTpPeer { federation_id }` and
`federation_root` for authentication. `federation_bridge.rs` connects to the
`pyana_federation` crate (behind a feature flag).

### Instances

| File | Lines | What | New Model | Difficulty | Priority |
|------|-------|------|-----------|------------|----------|
| `message.rs` | 114, 217, 236, 247, 282, 309 | WireMessage variants with `federation_root` / `federation_id` | Wire format is stable; fields can be aliased semantically | trivial | cosmetic |
| `server.rs` | 459, 480-549 | `WireState.federation_root` | Becomes "group commitment root" (same bytes, different name) | trivial | cosmetic |
| `server.rs` | 735, 805 | `PeerRole::CapTpPeer { federation_id }` | Should become `CapTpPeer { strand_id }` or `{ group_id }` | moderate | can-wait |
| `server.rs` | 890, 896, 942 | `CapTpSessionManager.sessions: HashMap<FederationId, CapSession>`, `known_federations` | Key by StrandId; known_federations becomes known_groups | moderate | can-wait |
| `server.rs` | 1679, 1797, 2236-2239 | CapHello message handling uses federation_id | Rename in next wire protocol version | moderate | can-wait |
| `federation_bridge.rs` | all | Feature-gated bridge to `pyana_federation` | Entire module is legacy; will be replaced by cross-reference DAG proofs | major | can-wait |
| `codec.rs` | 233 | Test fixture with `federation_root` | Test-only; cosmetic | trivial | cosmetic |
| `hardening.rs` | 316, 490, 561 | `federation_id` in test/hardening code | Test-only; cosmetic | trivial | cosmetic |
| `auth.rs` | 488, 493, 536 | Test fixtures with `federation_id` | Test-only; cosmetic | trivial | cosmetic |
| `bin/cross_node_auth.rs` | 91-520 | `compute_federation_root`, federation root matching logic | Demo binary; rename in v2 | moderate | cosmetic |

### Strategy
Add compatibility type aliases in `wire/src/lib.rs`. The wire format is frozen
(changing field names would be a breaking protocol change). In v2 of the protocol,
fields will be renamed.

---

## turn/ (Turn Executor)

### Summary
TurnExecutor has `local_federation_id: [u8; 32]` and
`trusted_federation_roots: Vec<AttestedRoot>`. These are used for cross-federation
note bridging (destination binding, source root verification).

### Instances

| File | Lines | What | New Model | Difficulty | Priority |
|------|-------|------|-----------|------------|----------|
| `executor.rs` | 518-521 | `trusted_federation_roots`, `local_federation_id` fields | Become `trusted_group_roots` and `local_group_id` (same semantics, just renaming) | trivial | must-fix-now |
| `executor.rs` | 808-819 | `set_trusted_federation_roots`, `set_local_federation_id` methods | Add aliases that call through | trivial | done |
| `executor.rs` | 1566, 1906, 2716-2721, 2980 | Uses `self.local_federation_id` in signing messages | Internal usage; rename field later, keep behavior | trivial | can-wait |
| `executor.rs` | 3135-3223 | `compute_signing_message(action, federation_id)` | Parameter name is semantic but private; add doc | trivial | cosmetic |
| `executor.rs` | 3674-3713 | `dest_federation` in bridge effect processing | Moderate refactor when bridges use GroupId | moderate | can-wait |
| `action.rs` | 874, 925-970 | `destination_federation`, `federation_root` in action types | Rename in next action version | moderate | can-wait |
| `pending.rs` | 65, 100, 458-725 | `federation_id: Option<[u8; 32]>`, `BrokenReason::FederationUnreachable` | Rename to `group_id`, `GroupUnreachable` | trivial | can-wait |

### Strategy
Add deprecated aliases for the old method names. The field types are all `[u8; 32]`
so the underlying semantics don't change -- only the NAME changes from "federation"
to "group". This is safe to do incrementally.

---

## sdk/ (SDK / Wallet)

### Summary
The SDK uses `federation_id` in RuntimeConfig and wallet's
`compute_federation_root_bb` / `register_with_federation` / `deregister_from_federation`.

### Instances

| File | Lines | What | New Model | Difficulty | Priority |
|------|-------|------|-----------|------------|----------|
| `runtime.rs` | 236, 434, 474, 529 | `federation_id` field in RuntimeConfig, used in signing | Same bytes, rename to `group_id` | trivial | can-wait |
| `wallet.rs` | 979-996 | `federation_tree` parameter name | Cosmetic rename | trivial | cosmetic |
| `wallet.rs` | 1982-2245 | `compute_federation_root_bb`, `federation_root`, `federation_root_bb` | Internal to proof generation; rename later | moderate | can-wait |
| `wallet.rs` | 4115-4208 | `register_with_federation`, `deregister_from_federation` (feature-gated) | These hit the node HTTP API; rename when node API changes | moderate | can-wait |

### Strategy
The wallet's "federation root" computation is really computing the GROUP's Merkle
root. No semantic change needed, just cosmetic renaming when ready.

---

## node/ (Node Binary)

### Summary
The node's `bridge.rs` manages cross-federation connections: `RemoteFederation`,
`connected_federations()`, relay tasks that exchange roots with remote peers.

### Instances

| File | Lines | What | New Model | Difficulty | Priority |
|------|-------|------|-----------|------------|----------|
| `bridge.rs` | 83, 125-627 | `RemoteFederation`, `remote_federations` HashMap, `cross_federation_revocations` | Becomes `RemoteGroup`, `remote_groups`, `cross_group_revocations` | moderate | can-wait |
| `bridge.rs` | 165-312 | `connect_to_remote_federation(federation_id, ...)` | Rename to `connect_to_remote_group` | moderate | can-wait |
| `bridge.rs` | 445-495 | `subscribe_receipt`, `latest_remote_root`, `connected_federations`, `revocations_for` | Rename parameters | trivial | can-wait |
| `bridge.rs` | 647-831 | `relay_incoming_task` function with `federation_id` parameter | Rename parameter | trivial | can-wait |

### Strategy
The node bridge module is the most semantically "federation-centric" code. In
the new model, a "remote group" is just another reference group on the shared DAG,
so the relay pattern changes fundamentally (blocks from remote groups appear in the
same blocklace via cross-references). However, the BRIDGE pattern (relay roots,
exchange revocations) still makes sense for groups on SEPARATE physical networks.
This should be renamed but the architecture stays until cross-reference dissemination
replaces it.

---

## Trivial Fixes Applied

1. **`captp/src/lib.rs`** -- Added doc comment explaining FederationId = GroupId
   in the unified model.

2. **`blocklace/src/addressing.rs`** -- Already has `FederationId` + backward-compat
   functions (`federation_to_fabric`, `fabric_to_federation`). No change needed.

3. **`turn/src/executor.rs`** -- Added `set_local_group_id` and
   `set_trusted_group_roots` as aliases for the old methods.

---

## Migration Order

1. **Phase A (now)**: Add doc comments + type aliases. No behavior change.
2. **Phase B (next sprint)**: Rename `PeerRole::CapTpPeer { federation_id }` to
   `{ group_id }` in wire protocol v2. Update CapTP GC keys to StrandId.
3. **Phase C (after B)**: Replace `node/src/bridge.rs` relay pattern with
   cross-reference dissemination from blocklace.
4. **Phase D (last)**: Remove `FederationId` compat types once all consumers
   are migrated.
