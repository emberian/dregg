# AUDIT: pyana CapTP / distributed-semantics layer

**Scope.** `captp/` (whole crate), `wire/src/server.rs` CapTP handlers, `wire/src/captp_routing.rs`, `wire/src/message.rs` CapTP variants, `sdk/src/captp_client.rs`. Read-only.

**Verdict in one line.** The *data structures* for OCapN-shaped distributed computation are in place and individually well-tested. The *wiring* between them — the layer where bytes become CapTP semantics — is largely a stub. Several core distributed-semantics features (three-party handoff in the cross-federation sense, promise pipelining over the wire, distributed GC across an actual disconnect, Turn-mediated capability invocation) are not connected end-to-end. The federation-mirror state mutates correctly on a single node; cross-node propagation is mostly absent.

---

## 1. Three-party handoff

The `HandoffCertificate` / `HandoffPresentation` pair is implemented carefully and the validation flow is sound — but only in the **local-introducer** topology, not the OCapN Alice→Bob→Carol topology.

### The data structures (captp/src/handoff.rs)

- `HandoffCertificate` (handoff.rs:104–134): introducer-signed bearer-shaped statement naming `target_federation`, `target_cell`, `recipient_pk`, `permissions`, `allowed_effects`, optional `expires_at` / `max_uses`, a 32-byte `nonce`, and the pre-registered `swiss` number at the target.
- `signing_message` (handoff.rs:183–231) is properly domain-separated (`b"pyana-handoff-cert-v1"`) and covers every load-bearing field. The `AUDIT[P2]` comment at handoff.rs:98–103 acknowledges public-field tampering risk but correctly notes the verify-and-consume flow protects against it.
- `HandoffPresentation` (handoff.rs:295–336) wraps the cert with a recipient-signed `presentation_message` that includes nonce + target_cell + target_federation, domain-separated `b"pyana-handoff-present-v1"`. This binds the recipient's key to *this* cert, defeating cert-theft.
- `validate_handoff` (handoff.rs:366–414) performs all five checks in order: introducer sig → recipient sig → introducer-is-known → expiry → swiss-enliven (which also handles max-uses via `SwissTable::enliven`).

### The sequence, as wired

Wire handler at `wire/src/server.rs:2509–2571`:

1. `PresentHandoff { presentation_bytes, introducer_pk }` arrives.
2. Postcard-decoded to a `HandoffPresentation`.
3. `validate_handoff` is called against the target's `swiss_table` and `known_federations` list.
4. On success, the target builds an `Effect::ValidateHandoff { cert_hash = blake3(presentation_bytes) }`, pushes a `Turn` onto `pending_captp_turns` (server.rs:2552–2559), and responds with `HandoffAccepted { routing_token, cell_id, permissions_tag }`.

### What's sound

- **Signatures are real.** Both signature checks happen before any state change. Tampering tests in `captp_client.rs` (`enliven_with_proof_rejects_tampered_cert`, `enliven_with_proof_rejects_wrong_recipient`, `enliven_with_proof_rejects_uri_mismatch`, `enliven_with_proof_rejects_expired`, captp_client.rs:855–994) exercise the four reject paths.
- **Bearer-token swap.** The certificate is bound to `recipient_pk`, so a passive eavesdropper of the cert (QR-photo, email-snoop) cannot present it. Test `wrong_recipient_rejected` (handoff.rs:531–544) confirms.
- **One-time / N-use limits** ride on `SwissTable::enliven`'s `use_count`. Test `max_uses_exhausted` (handoff.rs:560–602) confirms a second presentation fails with `MaxUsesExhausted`.

### Gaps in three-party handoff

**GAP-1 (high): the API only models the "Alice introduces Bob to a cell *on Alice*" topology, not the OCapN Alice→Bob→Carol topology.** Look at `CapTpClient::create_handoff` (sdk/src/captp_client.rs:461–492):

```rust
HandoffCertificate::create(
    signing_key,
    self.config.federation_id,
    self.config.federation_id, // target is also us (local delegation)
    ...
)
```

The introducer's federation and the target federation are *hardcoded* to the same value. There is no SDK entry point for "I, Alice on federation A, want to introduce Bob (on B) to Carol (on C)" — which is the entire point of the three-party handoff in the E/Goblins/OCapN sense. The wire-layer side accepts certs where `cert.introducer ≠ self.federation` (the `known_federations` check at handoff.rs:386 is the only gate), so the *receiving* side could handle a true three-party cert if one existed; but no client-side code constructs one.

**GAP-2 (medium): no nonce registry.** `HandoffError::ReplayDetected` (handoff.rs:57) is defined and never raised. There is no nonce-seen set anywhere in `captp/` or `wire/`. The only replay defense is `max_uses` decrementing on `SwissTable::enliven`. A cert with `max_uses = None` (the default in `create_handoff` when callers pass `None` — sdk/src/captp_client.rs:478) is effectively replayable until the underlying swiss is revoked. (The `enliven_with_proof` SDK path also doesn't check or update a nonce ledger.)

**GAP-3 (low): the `introducer_pk` arrives as a wire parameter.** In `WireMessage::PresentHandoff { presentation_bytes, introducer_pk }` (message.rs:331–336), `introducer_pk` is supplied by the recipient. The receiver uses *that* pk to verify the cert signature. This is fine *if* the recipient also independently knows the introducer's public key (via `known_federations` lookup) — but the actual wire handler doesn't cross-check that the supplied `introducer_pk` corresponds to `cert.introducer` (server.rs:2509–2571 just calls `validate_handoff` with whatever pk the wire message provided). `validate_handoff` checks `known_federations.contains(&cert.introducer)` (handoff.rs:386), but never checks that `introducer_pk` derives from `cert.introducer`. **A malicious peer could send `(cert_with_fed_X_introducer, my_own_pk)`, sign the cert with their own key, and pass the signature check** — provided `FederationId X` is in `known_federations`. The `FederationId` → `PublicKey` mapping is missing from the validation path. (See open question 1.)

---

## 2. Promise pipelining

The `PipelineRegistry` and `CrossFedPipelineBridge` (captp/src/pipeline.rs) are well-implemented as *local* data structures. The wire layer is a no-op stub. The SDK exposes a pipelining API that doesn't actually do remote dispatch.

### The local primitives

`PipelineRegistry` (pipeline.rs:137–333):
- `create_promise` allocates a new id, marks it Pending.
- `pipeline_message` (pipeline.rs:174–198) queues a `PipelinedMessage` against a Pending promise, errors on Broken, lets Fulfilled queue (the caller is supposed to drain).
- `resolve_promise` flips state to Fulfilled and returns the queued messages (the executor is expected to deliver them as turns).
- `break_promise` (pipeline.rs:223–259) flips state to Broken and produces `BrokenPromiseNotification` for every queued message that has a `result_promise_id`. Recursion handles transitive breakage.
- `pipeline_chain` (pipeline.rs:269–317) builds N-step chains correctly, with intermediate promises linked.

These pieces are correct in isolation and well-tested (pipeline.rs:704–1136 has 15 tests covering all the edge cases — resolve, break, cascade, chain breakage, etc.).

`CrossFedPipelineBridge` (pipeline.rs:425–698) extends to per-peer registries, with `drain_outbox` to produce wire messages.

### Where it falls apart: nothing dispatches the outbox

```text
grep -rn "drain_outbox\|CrossFedPipelineBridge" wire/ sdk/ node/
→  wire/src/server.rs:2498:  // CrossFedPipelineBridge for eventual delivery.   (a comment)
```

`CrossFedPipelineBridge` is **not instantiated anywhere outside its own tests**. `drain_outbox` is never called. Wire messages of variant `PipelineWireMessage` (pipeline.rs:349–396) are defined but never sent or received — `WireMessage` (message.rs) has only a flat `PipelinedMsg` variant, not the four-variant `PipelineWireMessage` enum.

### SDK side: pipeline is a local-only sink

`CapTpClient::pipeline` (captp_client.rs:512–537) and `CapTpClient::pipeline_to` (captp_client.rs:543–566) both call `PipelineRegistry::pipeline_chain` / `pipeline_message` on a **local** `Arc<Mutex<PipelineRegistry>>`. There is no wire send. Nothing leaves the process.

`LiveRef::send` and `LiveRef::pipeline` (captp_client.rs:143–166) confirm this in their own docstrings:

```
// AUDIT FINDING C-2: this method allocates a promise id in the local pipeline
// registry but does *not* yet enqueue the `action` argument for wire delivery.
```

`LiveRef::pipeline` literally calls `self.send(action)` — they are identical (captp_client.rs:162–166). SDK-REVIEW.md's note about `LiveRef::send` silently dropping its argument is **confirmed** and applies equally to `pipeline`.

### The wire's PipelinedMsg handler

`WireMessage::PipelinedMsg` arriving at the server (server.rs:2458–2507) does session-epoch validation, then:

```rust
// Silently accept and queue — pipeline delivery is async.
// In a full implementation, this would be dispatched to the
// CrossFedPipelineBridge for eventual delivery.
let _ = (target_promise_id, method, args, authorization, result_promise_id);
None
```

It discards every field. Receipt of `PipelinedMsg` is effectively a no-op except for telling the sender "OK, session checks pass."

### Gaps in promise pipelining

**GAP-4 (high): there is no end-to-end pipeline.** A client cannot pipeline a follow-up onto an unresolved promise to a remote peer. Both ends are stubs. The SDK queues locally; the server discards.

**GAP-5 (medium): no transport-side broken-promise propagation.** If a remote disappears, no `WireMessage::PromiseBroken` exists in `WireMessage` (message.rs has Enliven/Drop/Handoff/CapHello/CapGoodbye/PipelinedMsg — no broken-promise variant; `PipelineWireMessage::PromiseBroken` at pipeline.rs:380–385 is unused). `CapSession::break_promise` (session.rs:201–209) exists but no code path calls it on disconnect (see §4).

---

## 3. Swiss tables / sturdy refs — bearer or attested?

**Plain sturdy refs are pure bearer.** A `PyanaUri` is `{federation_id, cell_id, swiss}` (uri.rs:71–77). Enlivening is just a lookup:

```rust
// server.rs:2350
match captp.swiss_table.enliven(&uri.swiss, current_height) { ... }
```

`SwissTable::enliven` (sturdy.rs:159–182) does no signature check. It just checks: does the swiss exist? expired? max_uses exhausted? — increments and returns the entry. Anyone holding the swiss bytes can present them. The lib.rs trust-model comment is explicit: "The swiss number is a bearer secret — possession IS authorization" (lib.rs:11–13). Test `out_of_band_scenario` (handoff.rs:675–720) treats it that way.

**Attested form exists but is opt-in.** `enliven_with_proof` (captp_client.rs:353–400) layers a verified `HandoffCertificate` over the bearer swiss. This is the "attested" mode and is the only path where permissions are bound by a signature rather than caller claim — see the careful warning at captp_client.rs:300–322 about `enliven` accepting *caller-supplied* permissions with no remote attestation. This is correctly called out in the docs.

**Gap-6 (low): no rotation / forward-secrecy for bearer swiss.** Once a swiss number is in a backup, log, or pcap, it's a permanent bearer until `revoke_export` is called. There is no key rolling or per-session derivation. The bearer model is the design — but worth noting that there is also no offline-revocation mechanism (the SwissTable lives on a single node; if that node restarts without the table, every URI suddenly NotFound, no graceful continuation).

---

## 4. Promise resolution / breakage on disconnect

**This is mostly absent.** Track what happens when a peer disconnects:

1. `wire/src/server.rs` connection loop: on TCP error or codec error, the handler `break`s out of the read loop (server.rs:1741–1748 and 2335). On exit, `shutdown.unregister_connection()` runs (server.rs:1865).
2. **No teardown of `CapSession` happens.** The session stays in `captp.sessions` until the peer sends `CapGoodbye` (which they cannot do, having disconnected). New connections from the same peer call `CapHello` which allocates a new epoch and *replaces* the session (server.rs:2278–2282), so a fresh handshake works, but the stale session lingers indefinitely.
3. **No promises are broken.** `CapSession::break_promise` (session.rs:201–209) exists and is unit-tested but is not called from any disconnect path.
4. **No `BrokenPromiseNotification` is sent to local waiters.** The `CrossFedPipelineBridge::break_local_promise` plumbing (pipeline.rs:644–662) is unused.
5. The bearer `LiveRef` SDK type does call `gc_manager.local_ref_dropped` on `Drop` (captp_client.rs:182–191), generating a `DropMessage` — but **nothing dispatches that message to the wire**. It's returned from `release()` (captp_client.rs:172–180) and discarded by the implicit `drop`.

### Gaps

**GAP-7 (high): the disconnect → broken-promise cascade is not wired.** A client awaiting a remote promise on a disconnected peer will wait forever on the SDK side and the server retains stale session state.

**GAP-8 (medium): `LiveRef::drop` produces a `DropMessage` that's silently discarded.** Distributed GC's import side (sdk/src/captp_client.rs:182–191) generates the right message; nothing sends it. See §5.

---

## 5. Distributed GC

The data structures are right; the network never sees them.

### What's there

- `ExportGcManager` (gc.rs:78–305): per-cell, per-holder ref counts, with **session-id binding** (gc.rs:39–47 — `RefCount::session_id`) so a Byzantine peer cannot drop a counter that was incremented under a different session epoch. This is the right shape; tests at gc.rs:608–690 cover the cross-session attack.
- `ImportGcManager` (gc.rs:334–408): per-(federation, cell) refcount; when local refs hit 0, returns a `DropMessage` for the wire to send.
- Wire side `WireMessage::DropRemoteRef` (message.rs:285–299) carries `{from_strand, cell_id, session_epoch}` and the server processes it through `process_drop_with_session` (server.rs:2390–2456). This part *is* wired and even has stage-7 turn-routing.

### What's not

**GAP-9 (high): the import side never sends.** `ImportGcManager::local_ref_dropped` returns a `DropMessage`, but in the SDK `LiveRef`'s `Drop::drop` and `release` methods, the returned `Option<DropMessage>` is **discarded without being sent over the wire**:

```rust
// captp_client.rs:182–191
impl Drop for LiveRef {
    fn drop(&mut self) {
        if !self.dropped {
            self.dropped = true;
            if let Ok(mut gc) = self.gc_manager.lock() {
                gc.local_ref_dropped(self.federation_id, self.cell_id);  // <- return value dropped
            }
        }
    }
}
```

There is no client→server transmission of `WireMessage::DropRemoteRef` anywhere in the SDK. So although the export side correctly receives and processes drops (when somehow sent), nothing on a real client ever sends them.

**GAP-10 (medium): no idle-export proactive sweep on the wire.** `ExportGcManager::stale_exports` and `gc_sweep` (gc.rs:219–248) exist and work; nothing in the wire/node layer calls them. Exports leak even with the in-place facility.

**GAP-11 (low): `process_introduction_exports` (server.rs:973–1000) registers exports under `session_id = sessions.get(recipient_fed).map(|s| s.epoch).unwrap_or(0)`.** Falling back to 0 means an introduction export to a peer with no active session is recorded with session 0; any later drop must also use session 0 to match. That's a foot-gun if a session is later established (the session epoch will be ≥1; legitimate drops won't validate). It's a latent bug, not a current attack.

---

## 6. Cross-federation CapTP

**Within one federation only, in practice.**

Evidence:

- `CapTpClient::create_handoff` hardcodes `target_federation = self.config.federation_id` (captp_client.rs:482–483). No cross-federation cert can be created via the SDK.
- `EventualRef::target_federation` is stored (captp_client.rs:67–71) but never used to route a wire send — there's no wire send at all (§2).
- `PyanaUri::federation_id` exists in the URI (uri.rs:74) but `EnlivenSturdyRef` arrives at whichever node received the TCP connection and is enlivened against *that* node's `swiss_table` (server.rs:2333, 2350). There is no router that says "this URI is for federation X, forward it." If you connect to the wrong node, you get `NotFound` regardless of whether the URI is valid at some peer node.
- `known_federations` (server.rs:906) is the only cross-fed primitive in the wire layer, and it's used solely for `validate_handoff` to gate introducer trust. It's a `Vec` with no provisioning code visible in this audit's scope.

The trust-model docstring at lib.rs:5–15 acknowledges this: it describes federations as plural but the integration is single-node.

### Federation pluralization vs. blocklace addressing

The crate is mid-migration to the "unified lace model" (lib.rs:113–135) where `FederationId` is being recast as `GroupId` and a `StrandId` type alias has appeared. Most code still keys by `FederationId`. The migration is incomplete — comments like `TODO(unified-lace)` (gc.rs:14–16, pipeline.rs:40–42, handoff.rs:30–31) flag the dual-naming. Not a soundness issue, but the bilateral-strand-vs-group-federation distinction relevant to cross-federation routing is half-built.

---

## 7. Composition with Turn signing

**This is the most surprising finding. CapTP-derived Turns are constructed but unsigned, would fail authorization if executed, and are never executed anyway.**

### What the wire layer does

`build_captp_turn` (wire/src/captp_routing.rs:43–75) creates a `Turn` with:

```rust
authorization: Authorization::Unchecked,
agent: <node's local cell>,    // the federation gateway, not the originating user
nonce: 0,                       // placeholder
fee: 0,
// no signature on the Turn itself anywhere
```

The docstring (captp_routing.rs:30–42) says: *"the authorization is `Unchecked` for wire-layer routing: the cryptographic legitimacy of the operation was already established off-band (the swiss number presented, the handoff signature verified, etc.). The receipt-chain and AIR proof carry the state-transition evidence forward."*

These Turns are pushed onto `CapTpState::pending_captp_turns` (server.rs:2304, 2368, 2447, 2559) — four pushers, one per CapTP wire message.

### What happens next: nothing

`drain_pending_captp_turns` (server.rs:947–949) exists but `grep -rn drain_pending_captp_turns` returns only the definition itself. **No node code drains the queue.** The Turns accumulate forever and are never executed.

### And if they were?

`TurnExecutor::execute` would reject them. The authorization-check at executor.rs:3961–3968:

```rust
Authorization::Unchecked => Err((
    TurnError::PermissionDenied {
        cell: action.target,
        action: action_name.to_string(),
        required: AuthRequired::Either,
    },
    path.to_vec(),
)),
```

`Authorization::Unchecked` is uniformly an error. So even if the queue were drained, the receipts would not commit.

### What the design intent was

`DESIGN-captp-integration.md §7.2` and the captp_routing.rs comments (lines 1–23) describe a receipt-chain that *mirrors* CapTP mutations: every `EnlivenRef` / `DropRef` / `ExportSturdyRef` / `ValidateHandoff` on the federation's swiss-table should also produce a `Turn` whose `Effect::*` is committed on-chain. The federation-mirror mutation happens immediately (today); the receipt-side is supposed to drain afterward.

### So who signs?

- **The originating CapTP sender** signs nothing at the Turn layer. They signed the handoff cert (introducer) or hold the bearer swiss; that's it.
- **The receiving federation's executor** *can* sign committed receipts (executor.rs:608–621, `executor_signing_key`), populating `TurnReceipt::executor_signature`. But this is on the receipt, not the Turn.
- **The constructed CapTP Turn itself is unsigned.** It is not wrapped in a `SignedTurn` (sdk/src/cipherclerk.rs:843–852). It has no signature field at all (turn.rs:69–130 — `Turn` has no signature; signatures live on `SignedTurn`).

### Gaps

**GAP-12 (high): the receipt-mirror loop is not closed.** Wire CapTP handlers build Turns, push them, and nobody runs them. The mirror invariant "every CapTP mutation has a corresponding on-chain receipt" is structurally aspired to but operationally violated.

**GAP-13 (high): if the loop were closed, `Authorization::Unchecked` rejection would fire.** Either the executor needs a privileged path for federation-internal CapTP routing turns, or the wire-builder needs to attach a real authorization (e.g., a `Bearer` referencing the swiss number, or a federation-signed `Signature` from the node's identity), or these Turns should be admitted as a separate ledger type with a different verifier.

**GAP-14 (medium): the chain of responsibility between sender, gateway, and ledger is undocumented.** When a user agent in federation A enlivens a cap in federation B, *whose key* should sign the resulting B-side Turn? Today: nobody's. The user has no on-chain identity at B; the gateway has identity but no authorization model for "I am acting on behalf of a remote bearer who showed me a swiss"; and the receipt-side `executor_signature` proves only that B's executor ran the turn, not that the bearer was authentic. See open question 5.

---

## Bonus findings (not in the question, surfaced en route)

- **B-1.** `wire/src/server.rs:2509–2571` calls `validate_handoff` with `introducer_pk` taken directly from the wire message, not looked up by `cert.introducer` ∈ `known_federations`. Confirms GAP-3 — this means `known_federations` checks only the federation-id token, not that the supplied key is the *right* key for that federation. A `FederationId → PublicKey` registry is missing.
- **B-2.** `HandoffError::ReplayDetected` is defined and never raised anywhere in the codebase. Either delete the variant or add a nonce ledger.
- **B-3.** `store_forward.rs` and `MessageRelay` are not referenced in `wire/`, `sdk/`, or `node/` — the offline mailbox path is built and untested-against-the-network. Not in original question scope but worth flagging given the OCapN comparison.
- **B-4.** `lib.rs:9–15` claims executor honesty as an assumption for swiss-table maintenance, but the swiss-table mirror lives on each node's wire layer (`CapTpState`), not in the executor. The trust-model docstring is misaligned with where the data actually sits.

---

## Open questions for designer

1. **How is `FederationId → PublicKey` supposed to be resolved?** `validate_handoff` accepts a pk on every call and trusts the caller. Either the caller (wire handler) needs a registry, or the cert should carry the introducer pk and `FederationId` should be derived from it (`FederationId(pk.0)` already appears in tests — handoff.rs:427).

2. **Is the three-party (cross-federation) handoff topology intended for v1, or is "introducer == target" the design?** The wire-side `validate_handoff` accepts the cross-fed shape, but the SDK can only build the local shape. If cross-fed is intended, what does pre-registering a swiss at a *remote* federation look like? (The introducer needs an authenticated way to call `SwissTable::export` on a different node.)

3. **What is the intended dispatch path for `CrossFedPipelineBridge::drain_outbox`?** The bridge produces wire messages but there's no `PipelineWireMessage` variant in `WireMessage`. Should `PipelineWireMessage` be inlined into `WireMessage`, or wrapped in a `PipelinedMsg`-like envelope, or is the design to expose a separate transport (HTTP, gossip)?

4. **What should the wire layer do on TCP disconnect?** Today: nothing — the `CapSession` lingers, no promises are broken. Should disconnect trigger `CapSession::break_promise` for all pending promises and a wire-level `PromiseBroken` to peers that had pipelined messages routed through us?

5. **Who signs the CapTP receipt-mirror Turn?** Three options visible:
   - (a) The federation gateway cell, with a node-internal signing key, and the executor admits this via a special `Authorization::Federation` variant.
   - (b) The receipt is unsigned at the Turn level but the `executor_signature` on the *receipt* is the sole binding (today's `executor_signing_key` path).
   - (c) The remote agent supplies a signature for the receiving-federation gateway to forward.
   The current code reads as if (a) was intended (the wire builds the Turn with the node's CellId as agent) but `Authorization::Unchecked` is left in place, which (a) cannot use. Pick one and wire it.

6. **Is `pending_captp_turns` meant to be drained by the node's tick loop, or is the wire layer supposed to call `TurnExecutor::execute` directly?** Neither happens today. The wire layer has no executor; the node has both but no integration code.

7. **Should `LiveRef::send`/`pipeline` be removed until wire dispatch lands?** Both have docstrings honestly admitting they drop the action. Callers can mistake `EventualRef` for "something will happen." A `todo!()` or explicit `unimplemented!()` would force the issue rather than silently lose actions.

8. **Should plain bearer-swiss enliven (without a HandoffCertificate) be allowed across federations, or only within?** Bearer secrets in transit (URIs in emails) defeat OCapN's three-party security goals — but the system supports them. The trust model needs to say "bearer URIs are local-only; cross-federation requires a HandoffCertificate."

9. **What is the relationship between `FederationId` (current) and `StrandId` (Phase B migration)?** Six `TODO(unified-lace)` markers appear across `captp/`; the wire is still federation-keyed; the migration is half-done. Where on the priority list does this sit?

---

## Tally

| Topic | Local data structures | Wire integration | End-to-end |
|---|---|---|---|
| Sturdy refs / swiss tables | OK | OK (`Enliven`) | Bearer-only flow works one-node |
| Handoff cert | OK | OK (`PresentHandoff`) | Same-federation only |
| Three-party (Alice→Bob→Carol) | OK (types) | partial | **No** (GAP-1) |
| Promise pipelining | OK (15 tests) | **stub** | **No** (GAP-4) |
| Distributed GC export | OK (session-bound) | OK (server-side) | Receives but no senders |
| Distributed GC import | OK | **drop dropped** | **No** (GAP-9) |
| Disconnect → broken promise | primitive exists | not called | **No** (GAP-7) |
| Cross-federation routing | n/a | absent | **No** (§6) |
| CapTP → Turn mirror | builder exists | pushes queue | **No drainer** (GAP-12); also rejected if drained (GAP-13) |
| Store-and-forward | exists | unreferenced | **No** (B-3) |

The components are individually sound and well-tested. The composition is missing.
