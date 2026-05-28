# Effect Wiring Completeness Audit

**Date:** 2026-05-25  
**Scope:** All 52 `Effect` variants in `turn/src/action.rs`  
**Method:** Static read-only analysis of local tree only. No cargo runs.  
**Dimensions:**  
- **(a) Receipt entry** — does the Effect's hash appear in `TurnReceipt.effects_hash`?  
- **(b) Data binding** — are the Effect's semantic fields (not just discriminant) bound into `receipt_hash`?  
- **(c) AIR projection** — does the Effect project to a non-NoOp `VmEffect` in `effect_vm_bridge.rs`?  
- **(d) Wire/event observable side-effect** — does the Effect emit a wire-level / gossip / `emitted_events` observable beyond the receipt itself?  

---

## §1 Method and Scope

### Effect Enumeration

The 52 variants were enumerated by reading `turn/src/action.rs` lines 578–1237.

### Dimension A — Receipt Entry

`TurnReceipt.effects_hash` is computed at `turn/src/executor/finalize.rs:492–502` as `BLAKE3(effect.hash() for all effects in the call forest)`. Every effect that executes without error is hashed by `Effect::hash()` (action.rs:1575–2338). Therefore **all 52 variants receive a receipt entry** provided the turn commits. The `effects_hash` is bound into `receipt_hash` at `turn/src/turn.rs:625`.

### Dimension B — Data Binding

`Effect::hash()` is an exhaustive match (no `_` arm). Every variant hashes its discriminant byte plus all semantic fields. Verified by reading the match at action.rs:1574–2337.

### Dimension C — AIR Projection

`turn/src/executor/effect_vm_bridge.rs` contains the `collect_effects` closure (lines 18–958). It has an explicit match arm for each projected effect, with a `_ =>` catch-all at line 952–957 that silently drops unmatched effects. Effects with no explicit arm produce no `VmEffect` row (the catch-all is reached). If `vm_effects` ends up empty, one `VmEffect::NoOp` is pushed (line 977).

### Dimension D — Wire/Event Observable

`TurnReceipt.emitted_events` captures `JournalEntry::EventEmitted` entries (finalize.rs:760–773). Only `Effect::EmitEvent` writes this journal entry (apply.rs:74–76 → `apply_emit_event`). Wire-level, `wire/src/server.rs` `ServerEvent` enum (lines 1294–1322) has only: `ConnectionAccepted`, `HelloReceived`, `TokenPresented`, `RevocationSubmitted`, `NonMembershipRequested`, `ConnectionError`. **No TurnCommitted, no EmittedEvent, no per-Effect wire message.** Observable side-effects beyond receipt/gossip flow only exist for: `EmitEvent` (emitted_events on receipt), `Introduce` (routing_directives + introduction_exports on receipt, consumed by node for GC and routing), and CapTP effects (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`) which drive wire messages (`CapHello`, `EnlivenSturdyRef`/`EnlivenResponse`, `DropRemoteRef`, `PresentHandoff`/`HandoffAccepted`) constructed by the wire layer *before* the Effect is submitted as a Turn.

---

## §2 Per-Effect Matrix

Legend: ✓ = wired, ~ = partial/synthetic, ✗ = absent, N/A = not applicable

| # | Variant | (a) Receipt | (b) Data Binding | (c) AIR Projection | (d) Observable | Notes |
|---|---------|-------------|------------------|--------------------|----------------|-------|
| 1 | `SetField` | ✓ | ✓ cell+index+value (action.rs:1578–1583) | ✓ `VmEffect::SetField` (bridge:62–67) `cell==cell_id` guard | ✗ | Cross-cell arm falls to catch-all |
| 2 | `Transfer` | ✓ | ✓ from+to+amount (action.rs:1584–1589) | ✓ `VmEffect::Transfer` (bridge:49–61) from/to guards | ✗ | |
| 3 | `GrantCapability` | ✓ | ✓ from+to+cap.target+cap.slot (action.rs:1590–1596) | ✓ `VmEffect::GrantCapability` (bridge:68–73) `to==cell_id` guard | ✗ | from-side not projected |
| 4 | `RevokeCapability` | ✓ | ✓ cell+slot (action.rs:1597–1601) | ✓ `VmEffect::RevokeCapability` (bridge:412–421) `cell==cell_id` guard | ✗ | |
| 5 | `EmitEvent` | ✓ | ✓ cell+topic+data (action.rs:1602–1609) | ✓ `VmEffect::EmitEvent` (bridge:453–495) full 8-felt topic+payload | ✓ `emitted_events` on receipt; caught by journal | |
| 6 | `IncrementNonce` | ✓ | ✓ cell (action.rs:1610–1613) — discriminant+cell only; this is by design for a nonce | ✗ NoOp (bridge:90–92, 525–527 both comment "implicit in row continuity") | ✗ | NoOp-by-design; §5 analysis |
| 7 | `CreateCell` | ✓ | ✓ pk+token_id+balance (action.rs:1614–1623) | ✓ `VmEffect::CreateCell` (bridge:422–438) create_hash | ✗ | |
| 8 | `SetPermissions` | ✓ | ✓ cell+8 permission fields (action.rs:1624–1664) | ✓ `VmEffect::SetPermissions` (bridge:387–398) permissions_hash; `cell==cell_id` guard | ✗ | Cross-cell falls to catch-all |
| 9 | `SetVerificationKey` | ✓ | ✓ cell+vk.data (action.rs:1665–1674) | ✓ `VmEffect::SetVerificationKey` (bridge:399–411) vk_hash; `cell==cell_id` guard | ✗ | |
| 10 | `NoteSpend` | ✓ | ✓ nullifier+root+value+asset_type+proof+opt_vc (action.rs:1675–1698) | ✓ `VmEffect::NoteSpend` (bridge:74–81) nullifier+value (4-byte truncation note below) | ✗ | nullifier is 4-byte-truncated in AIR |
| 11 | `NoteCreate` | ✓ | ✓ commitment+value+asset_type+encrypted_note+opt_vc+opt_rp (action.rs:1699–1732) | ✓ `VmEffect::NoteCreate` (bridge:82–89) commitment+value (4-byte truncation) | ✗ | |
| 12 | `CreateSealPair` | ✓ | ✓ sealer_holder+unsealer_holder (action.rs:1733–1739) | ✓ `VmEffect::CreateSealPair` (bridge:439–452) pair_hash | ✗ | |
| 13 | `Seal` | ✓ | ✓ pair_id+cap.target+cap.slot (action.rs:1741–1749) | ~ `VmEffect::Seal` (bridge:344–352) field_idx = low 3 bits of pair_id[0] — semantic binding of capability is lost | ✗ | **Near-miss aliasing §4** |
| 14 | `Unseal` | ✓ | ✓ sealed_box.pair_id+ephemeral_public+commitment+nonce+recipient (action.rs:1750–1759) | ~ `VmEffect::Unseal` (bridge:354–363) field_idx+brand from postcard-hash of sealed_box — lossy | ✗ | **Near-miss aliasing §4** |
| 15 | `SpawnWithDelegation` | ✓ | ✓ child_pk+child_token_id+max_staleness (action.rs:2008–2017) | ✓ `VmEffect::SpawnWithDelegation` (bridge:496–511) spawn_hash | ✗ | |
| 16 | `RefreshDelegation` | ✓ | ~ discriminant only (action.rs:2018–2019) — only a domain byte | ✓ `VmEffect::RefreshDelegation` (bridge:513–517) no params | ✗ | Minimal data binding; sufficient since epoch lives in cell state |
| 17 | `RevokeDelegation` | ✓ | ✓ child (action.rs:2021–2023) | ✓ `VmEffect::RevokeDelegation` (bridge:518–524) child_hash | ✗ | |
| 18 | `BridgeMint` | ✓ | ✓ nullifier+dest_commitment+value+asset_type+source_root (action.rs:1761–1769) | ✓ `VmEffect::BridgeMint` (bridge:529–555) value_lo+mint_hash+value_full; 30-bit trunc fixed | ✗ | |
| 19 | `BridgeLock` | ✓ | ✓ nullifier+destination+value+asset_type+timeout_height+proof (action.rs:1770–1786) | ✓ `VmEffect::BridgeLock` (bridge:557–578) value_lo+lock_hash+value_full; timeout_height not in VmEffect hash | ✗ | timeout_height absent from AIR lock_hash |
| 20 | `BridgeFinalize` | ✓ | ✓ nullifier+receipt fields (action.rs:1787–1793) | ✓ `VmEffect::BridgeFinalize` (bridge:579–590) finalize_hash | ✗ | |
| 21 | `BridgeCancel` | ✓ | ✓ nullifier (action.rs:1795–1798) | ✓ `VmEffect::BridgeCancel` (bridge:591–597) nullifier_hash | ✗ | |
| 22 | `Introduce` | ✓ | ✓ introducer+recipient+target+permissions (action.rs:1799–1829) | ✓ `VmEffect::Introduce` (bridge:598–630) intro_hash | ✓ routing_directives + introduction_exports on receipt (finalize.rs:774–823) |  |
| 23 | `PipelinedSend` | ✓ | ✓ target.source_turn+target.output_slot+action.hash() (action.rs:1831–1835) | ✓ `VmEffect::PipelinedSend` (bridge:631–643) send_hash | ✗ | Wire-level delivery is async/future |
| 24 | `CreateObligation` | ✓ | ✓ beneficiary+deadline_height+stake+stake_amount+condition (action.rs:1837–1879) | ✓ `VmEffect::CreateObligation` (bridge:309–325) stake_amount+obligation_id+beneficiary_hash | ✗ | |
| 25 | `FulfillObligation` | ✓ | ✓ obligation_id+proof (action.rs:1881–1912) | ~ `VmEffect::FulfillObligation` (bridge:327–336) stake_return=0 (hardcoded sentinel) | ✗ | **stake_return not bound; §3** |
| 26 | `SlashObligation` | ✓ | ✓ obligation_id (action.rs:1913–1915) | ~ `VmEffect::SlashObligation` (bridge:337–343) stake_amount=0, beneficiary_hash=cell_id synthetic | ✗ | **stake_amount not bound; §3** |
| 27 | `CreateEscrow` | ✓ | ✓ cell+recipient+amount+condition+timeout+escrow_id (action.rs:1917–1946) | ✓ `VmEffect::CreateEscrow` (bridge:644–667) amount_lo+escrow_hash+amount_full; cell==cell_id guard | ✗ | |
| 28 | `ReleaseEscrow` | ✓ | ✓ escrow_id+opt_proof (action.rs:1948–1957) | ✓ `VmEffect::ReleaseEscrow` (bridge:668–673) escrow_id_hash | ✗ | |
| 29 | `RefundEscrow` | ✓ | ✓ escrow_id (action.rs:1959–1961) | ✓ `VmEffect::RefundEscrow` (bridge:675–679) escrow_id_hash | ✗ | |
| 30 | `CreateCommittedEscrow` | ✓ | ✓ creator_commit+recipient_commit+value_commit+condition_commit+timeout+escrow_id+range_proof+amount (action.rs:1963–1983) | ✓ `VmEffect::CreateCommittedEscrow` (bridge:681–699) commit_hash (4-field Pedersen) | ✗ | |
| 31 | `ReleaseCommittedEscrow` | ✓ | ✓ escrow_id+claim_auth.cell_id+blinding+signature+recipient (action.rs:1984–1995) | ✓ `VmEffect::ReleaseCommittedEscrow` (bridge:701–715) commit_hash(escrow_id+recipient) | ✗ | claim_auth.blinding+sig not in commit_hash |
| 32 | `RefundCommittedEscrow` | ✓ | ✓ escrow_id+claim_auth+creator (action.rs:1996–2007) | ✓ `VmEffect::RefundCommittedEscrow` (bridge:716–727) commit_hash(escrow_id+creator) | ✗ | claim_auth fields not in commit_hash |
| 33 | `ExerciseViaCapability` | ✓ | ✓ cap_slot+inner_effects (action.rs:2025–2033) | ✓ `VmEffect::ExerciseViaCapability` (bridge:728–745) exercise_hash(cap_slot+inner_hashes) | ✗ | |
| 34 | `MakeSovereign` | ✓ | ✓ cell (action.rs:2035–2037) | ✓ `VmEffect::MakeSovereign` (bridge:364–366) `cell==cell_id` guard | ✗ | |
| 35 | `CreateCellFromFactory` | ✓ | ✓ factory_vk+owner_pk+token_id+params.mode+program_vk+initial_fields+initial_caps (action.rs:2039–2071) | ✓ `VmEffect::CreateCellFromFactory` (bridge:367–376) factory_vk+child_vk_derived | ✗ | |
| 36 | `QueueAllocate` | ✓ | ✓ capacity+opt_program_vk (action.rs:2072–2087) | ✓ `VmEffect::AllocateQueue` (bridge:93–103) capacity+owner_quota_id+cost_per_slot | ✗ | |
| 37 | `QueueEnqueue` | ✓ | ✓ queue+message_hash+deposit (action.rs:2088–2097) | ✓ `VmEffect::EnqueueMessage` (bridge:104–141) message_hash+deposit+sender_id+queue_len+program_vk | ✗ | |
| 38 | `QueueDequeue` | ✓ | ✓ queue (action.rs:2098–2101) | ~ `VmEffect::DequeueMessage` (bridge:143–185) expected_message_hash = synthetic DREGG_DEQUEUE_HEAD/v1 domain tag; BLOCK1-BIND comment notes "CLOSED-PARTIALLY" | ✗ | **Dequeue head hash synthetic; §3** |
| 39 | `QueueResize` | ✓ | ✓ queue+new_capacity (action.rs:2102–2109) | ✓ `VmEffect::ResizeQueue` (bridge:187–211) new_capacity+queue_id+cost+old_capacity | ✗ | |
| 40 | `QueueAtomicTx` | ✓ | ✓ operations (action.rs:2110–2131) | ✓ `VmEffect::AtomicQueueTx` (bridge:213–278) tx_hash+combined_old_root+combined_new_root+net_deposit | ✗ | |
| 41 | `QueuePipelineStep` | ✓ | ✓ pipeline_id+source+sinks (action.rs:2132–2144) | ~ `VmEffect::PipelineStep` (bridge:279–302) source_new/sink_new = synthetic `hash_2_to_1(root, pipeline_id)` placeholder | ✗ | |
| 42 | `ExportSturdyRef` | ✓ | ✓ swiss_number+target+permissions (action.rs:2146–2178) | ✓ `VmEffect::ExportSturdyRef` (bridge:756–829) cell_id+permissions+random_seed+export_counter; `target==cell_id` guard | ✓ Wire layer sends `CapHello`/initiates `EnlivenSturdyRef` flow |
| 43 | `EnlivenRef` | ✓ | ✓ swiss_number+bearer+expected_cell_id+expected_permissions (action.rs:2179–2210) | ✓ `VmEffect::EnlivenRef` (bridge:830–877) swiss_bb+presenter_bb+expected_cell_id_bb+permissions_bb; `bearer==cell_id` guard | ✓ `EnlivenResponse` wire msg |
| 44 | `DropRef` | ✓ | ✓ ref_id (action.rs:2211–2214) | ✓ `VmEffect::DropRef` (bridge:878–908) cell_id+holder_federation+current_refcount from ledger | ✓ `DropRemoteRef` wire msg |
| 45 | `Refusal` | ✓ | ✓ cell+offered_action_commitment+refusal_reason+proof_witness_index (action.rs:2312–2337) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |
| 46 | `ValidateHandoff` | ✓ | ✓ cert_hash+recipient_pk+introducer_pk (action.rs:2215–2224) | ✓ `VmEffect::ValidateHandoff` (bridge:909–950) cert_bb+recipient_pk_bb+introducer_pk_bb+approved_set_root=ZERO | ✓ `HandoffAccepted` wire msg |
| 47 | `CellSeal` | ✓ | ✓ target+reason (action.rs:2225–2229) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |
| 48 | `CellUnseal` | ✓ | ✓ target (action.rs:2230–2232) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |
| 49 | `CellDestroy` | ✓ | ✓ target+certificate.certificate_hash() (action.rs:2234–2243) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |
| 50 | `Burn` | ✓ | ✓ target+slot+amount (action.rs:2244–2253); `was_burn=true` bound into receipt_hash | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection; was_burn disclosure is receipt-only** |
| 51 | `AttenuateCapability` | ✓ | ✓ cell+slot+narrower_permissions+narrower_effects+narrower_expiry (action.rs:2254–2303) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |
| 52 | `ReceiptArchive` | ✓ | ✓ prefix_end_height+checkpoint.checkpoint_hash() (action.rs:2304–2311) | ✗ **Falls to catch-all** (no bridge arm) | ✗ | **Gap: no AIR projection** |

---

## §3 Categorical Gaps

### Gap G1 — 7 Effects with Zero AIR Projection (Silver-Vision lifecycle variants)

The following 7 variants have **no arm** in `effect_vm_bridge.rs` and fall to the `_ =>` catch-all at line 952. They produce no `VmEffect` row. When any of these is the only effect in a turn, the bridge returns `[NoOp]`.

| Variant | Missing arm |
|---------|------------|
| `Refusal` | bridge lines 952–957 |
| `CellSeal` | bridge lines 952–957 |
| `CellUnseal` | bridge lines 952–957 |
| `CellDestroy` | bridge lines 952–957 |
| `Burn` | bridge lines 952–957 |
| `AttenuateCapability` | bridge lines 952–957 |
| `ReceiptArchive` | bridge lines 952–957 |

**Severity:** These 7 effects mutate real ledger state (lifecycle flags, balances, c-list narrowing, archival metadata) but their STARK proof is `NoOp`. A verifier proving a turn that contains only `Burn` or `CellDestroy` sees no difference from a no-op turn in the circuit.

### Gap G2 — Synthetic/Lossy Projections (Partial Dimension C)

The following effects project to a real `VmEffect` but with synthetic or lossy data that weakens the constraint:

| Variant | Synthetic element | Evidence |
|---------|-------------------|----------|
| `Seal` | `field_idx = pair_id[0] & 0x7` — 3 bits of pair_id, capability field lost | bridge:344–352 |
| `Unseal` | `field_idx` + `brand` from postcard-hash of sealed_box; capability recovery lost | bridge:354–363 |
| `FulfillObligation` | `stake_return = 0` hardcoded; AIR cannot constrain returned amount | bridge:327–336 |
| `SlashObligation` | `stake_amount = 0`, `beneficiary_hash = cell_id` synthetic (not the actual beneficiary) | bridge:337–343 |
| `QueueDequeue` | `expected_message_hash` = synthetic domain-tagged BLAKE3 of queue+qlen; actual head not bound | bridge:143–185 |
| `QueuePipelineStep` | `source_new/sink_new` = synthetic `hash_2_to_1(root, pipeline_id)` placeholder | bridge:279–302 |
| `ReleaseCommittedEscrow` | `commit_hash` omits `claim_auth.blinding` and `claim_auth.signature` | bridge:701–715 |
| `RefundCommittedEscrow` | Same: claim_auth fields not in commit_hash | bridge:716–727 |

### Gap G3 — Wire/Event Observability Absent for Most Effects

`wire/src/server.rs`'s `ServerEvent` (line 1294) covers only 5 event types: connection, hello, token, revocation, non-membership. No `TurnCommitted` event, no `EffectApplied` event. The receipt's `emitted_events` field carries only `Effect::EmitEvent` payloads; all other 51 effect types produce **zero observable side-effect** at the wire/gossip layer beyond the receipt hash chain. Apps that want to observe `Burn`, `CellDestroy`, or `AttenuateCapability` must re-execute the receipt from the chain — there is no push-notification path.

### Gap G4 — `IncrementNonce` NoOp by Design (see §5)

`IncrementNonce` is explicitly skipped in the bridge (line 90–92, 525–527) because nonce increments are handled by row-to-row continuity. This is architecturally intentional but requires the AIR's continuity constraint to be airtight.

### Gap G5 — 4-byte Truncation in NoteSpend/NoteCreate

`NoteSpend.nullifier` and `NoteCreate.commitment` are both 32-byte values projected to 4-byte BabyBear felts via `hash_to_bb` (bridge:37–44). The REVIEW comment at bridge:26–36 explicitly acknowledges this: "many distinct effects collapse to the same circuit-side identifier." The BLOCK1-BIND fix note says the coordinated 8-BabyBear widening is "purely a circuit PI-layout change" pending a coordinated landing.

---

## §4 Near-Miss Aliasing Analysis

The three flagged near-misses from issue #100:

### 4.1 Burn → Transfer

`Burn` does **not** project to `VmEffect::Transfer`. It falls to the catch-all (Gap G1). The `was_burn` flag in `TurnReceipt` (turn.rs:610, `receipt_hash` bound at turn.rs:687) is the only cryptographic commitment to the burn having occurred. There is no AIR constraint proving the balance actually decreased by `amount`. **This is a real gap, not just a near-miss.**

### 4.2 CellDestroy → SetPermissions

`CellDestroy` does **not** project to `VmEffect::SetPermissions`. It falls to the catch-all (Gap G1). The lifecycle transition is applied via `apply_cell_destroy` (apply.rs:4157–4188) and journaled via `JournalEntry::SetLifecycle` (finalize.rs:615), but the `LedgerDelta` comment at finalize.rs:613–616 says lifecycle changes are "rollback-only — no separate LedgerDelta field today." There is no AIR row proving the cell entered `Destroyed` state. **Real gap.**

### 4.3 AttenuateCapability → RevokeCapability

`AttenuateCapability` does **not** project to `VmEffect::RevokeCapability`. It falls to the catch-all (Gap G1). Attenuation is applied via `apply_attenuate_capability` (apply.rs:4251–4313) which narrows an in-place c-list entry using `CapabilitySet::attenuate_in_place`. The journal entry `JournalEntry::AttenuateCapability` (finalize.rs:615) is again rollback-only. No AIR row proves the capability was narrowed, not revoked and re-granted with wider permissions. **Real gap.**

**Summary:** All three "near-miss" descriptions from #100 are actually genuine gaps. None of the three aliases to another real `VmEffect`; all three fall to the catch-all. The audit finds 7 total catch-all variants (the 3 above plus `CellSeal`, `CellUnseal`, `Refusal`, `ReceiptArchive`).

---

## §5 IncrementNonce NoOp-by-Design Analysis

### Code Evidence

- bridge.rs:90–92: `Effect::IncrementNonce { cell } if cell == cell_id => { // Nonce increment is implicit in the VM (row-to-row). }`
- bridge.rs:525–527: `Effect::IncrementNonce { cell } if cell == cell_id => { // No AIR effect needed — nonce increments are implicit in the row-to-row continuity. Skip to avoid a NoOp. }`

### Safety Assessment

**Safe, provided:** The AIR's row-to-row continuity constraint enforces that between any two consecutive effect rows for the same cell, `nonce[i+1] == nonce[i] + 1`. This is the standard design for a ZK VM: the nonce doesn't need its own selector row because every non-NoOp row implicitly increments the nonce counter.

**Risk:** If the continuity constraint has a gap (e.g., is not enforced at the proof boundary between turns), a prover could submit a turn with `IncrementNonce` and prove it without actually incrementing. The executor's nonce check at execute.rs:58–66 is the first-line guard; the AIR's continuity is the proof-side guard. Both must hold.

**Verdict:** The design is architecturally sound. The nonce-monotonicity is enforced at the protocol level (execute.rs nonce check) and at the AIR level (row continuity). The skip in the bridge is intentional and not a wiring gap in dimension (c) — it is an explicit design choice documented at both bridge sites.

**Caveat:** Cross-cell `IncrementNonce` (where `cell != cell_id`) falls to the catch-all at line 952. If an action contains `Effect::IncrementNonce { cell: other_cell }`, that increment is journaled by `apply_increment_nonce` on the other cell but produces no AIR row for the proving cell. This is consistent with the cross-cell pattern: the other cell has its own proof.

---

## §6 Wire/Event Observability Gaps

### What IS observable at the wire layer

| Effect | Observable mechanism |
|--------|----------------------|
| `EmitEvent` | `TurnReceipt.emitted_events` (finalize.rs:760–773); node WebSocket broadcasts `NodeEvent::Receipt{hash}` (state.rs:46) |
| `Introduce` | `TurnReceipt.routing_directives` + `introduction_exports` (finalize.rs:774–823); consumed by node layer for routing table + GC |
| `ExportSturdyRef` | Wire layer builds `CapHello` / `EnlivenSturdyRef` *before* submitting the Turn; direct `WireMessage` to peer |
| `EnlivenRef` | `WireMessage::EnlivenResponse` |
| `DropRef` | `WireMessage::DropRemoteRef` |
| `ValidateHandoff` | `WireMessage::HandoffAccepted` |

### What is NOT observable (effects invisible to subscribers)

The following 46 effects produce **no wire-level notification**. Apps observing these must poll the receipt chain or re-execute the turn:

`SetField`, `Transfer`, `GrantCapability`, `RevokeCapability`, `IncrementNonce`, `CreateCell`, `SetPermissions`, `SetVerificationKey`, `NoteSpend`, `NoteCreate`, `CreateSealPair`, `Seal`, `Unseal`, `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`, `BridgeMint`, `BridgeLock`, `BridgeFinalize`, `BridgeCancel`, `PipelinedSend`, `CreateObligation`, `FulfillObligation`, `SlashObligation`, `CreateEscrow`, `ReleaseEscrow`, `RefundEscrow`, `CreateCommittedEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow`, `ExerciseViaCapability`, `MakeSovereign`, `CreateCellFromFactory`, `QueueAllocate`, `QueueEnqueue`, `QueueDequeue`, `QueueResize`, `QueueAtomicTx`, `QueuePipelineStep`, `Refusal`, `CellSeal`, `CellUnseal`, `CellDestroy`, `Burn`, `AttenuateCapability`, `ReceiptArchive`

**Most critical invisible effects:** `Burn` (supply change invisible without receipt re-execution), `CellDestroy` (cell death invisible), `AttenuateCapability` (security narrowing invisible), `CellSeal` (cell locked, invisible to dependent callers).

### NodeEvent::Receipt

`wire/src/server.rs` does not directly emit receipts. `node/src/state.rs:46` emits `NodeEvent::Receipt { hash: String }` — only the hash, not the full receipt body. Apps must fetch the full receipt separately to discover which effects occurred. There is no push of `emitted_events` content.

---

## §7 Top 5 Highest-Leverage Closures

### Closure 1 (Highest impact): Add AIR bridge arms for the 7 catch-all lifecycle effects

**Files:** `turn/src/executor/effect_vm_bridge.rs`  
**Variants:** `Burn`, `CellDestroy`, `CellSeal`, `CellUnseal`, `AttenuateCapability`, `ReceiptArchive`, `Refusal`  
**Impact:** These 7 variants currently produce STARK proofs that are provably the same as a no-op turn. A malicious executor can prove a `Burn` without actually burning. While the executor re-execution guard exists, the proof loses its purpose for these effects. `Burn` is the most critical because it changes token supply.  
**Effort:** Each needs a new `VmEffect` variant in `circuit/src/effect_vm/effect.rs` + an AIR arm + a bridge arm. `Burn` is the simplest (amount + target hash). `CellSeal/Unseal/Destroy` need lifecycle selector constraints.

### Closure 2: Fix `FulfillObligation.stake_return = 0` and `SlashObligation.stake_amount = 0`

**Files:** `turn/src/executor/effect_vm_bridge.rs:327–343`  
**Impact:** A prover fulfilling an obligation can claim `stake_return = 0` and pass the AIR's balance-credit check with zero credit. The executor applies the real credit, but the STARK proof doesn't constrain it. This means obligation fulfillment/slashing proofs are not binding on the stake amounts.  
**Effort:** Requires plumbing the obligation ledger (or a lookup into the ledger at bridge time) to source the real `stake_return` and `stake_amount`. The bridge already has ledger access (`&Ledger` is passed to `convert_turn_effects_to_vm`).

### Closure 3: Fix `QueueDequeue` synthetic head hash

**Files:** `turn/src/executor/effect_vm_bridge.rs:143–185`  
**Impact:** The dequeue AIR row proves a synthetic `DREGG_DEQUEUE_HEAD/v1 || queue_id || qlen` hash, not the actual message being dequeued. A prover can dequeue any message and prove a valid dequeue. The bridge comment (lines 148–164) explicitly labels this "CLOSED-PARTIALLY."  
**Effort:** Requires binding the real queue head hash. Path (a) from the comment: store head commitment in `cell.state.fields` slot at enqueue time (executor + AIR co-evolution). This is the architecturally clean fix.

### Closure 4: Widen NoteSpend/NoteCreate nullifier/commitment from 4 bytes to 8 BabyBears

**Files:** `turn/src/executor/effect_vm_bridge.rs:37–44, 74–89`; `circuit/src/effect_vm/`  
**Impact:** The `hash_to_bb` 4-byte truncation means ~4 billion distinct nullifiers hash to at most ~2 billion distinct circuit values. Two notes with different nullifiers can produce the same AIR PI. The BLOCK1-BIND coordinated fix is documented (bridge:26–36) but not landed.  
**Effort:** Requires widening both the runtime projection and the AIR PI layout simultaneously. A coordinated landing.

### Closure 5: Add `NodeEvent::EffectsApplied` to wire/gossip for high-priority effects

**Files:** `node/src/state.rs`, `wire/src/server.rs`  
**Impact:** 46 effects are currently invisible to subscribers without receipt polling. Adding a push event carrying at minimum the discriminant set of effects that ran (Burn, CellDestroy, Transfer, etc.) would allow apps to react without polling.  
**Effort:** Add `NodeEvent::EffectsApplied { turn_hash, agent, effect_kinds: Vec<u8> }` to node/src/state.rs. Emit from blocklace_sync.rs after commit. Does not require changing the wire protocol.

---

## Summary Counts

| Dimension | Count of FULLY wired effects |
|-----------|------------------------------|
| (a) Receipt entry | 52 / 52 |
| (b) Data binding | 52 / 52 (all fields hashed in `Effect::hash()`) |
| (c) AIR projection (non-NoOp, non-synthetic) | 37 / 52 |
| (c) AIR projection (zero/catch-all) | 7 / 52 |
| (c) AIR projection (synthetic/lossy) | 8 / 52 |
| (d) Wire/event observable | 6 / 52 |
| Fully wired across all 4 dimensions | 6 / 52 |

The 6 fully wired effects (all 4 dimensions) are: `EmitEvent`, `Introduce`, `ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`.
