# Silver Vision — End-to-End Verification

**Date:** 2026-05-24. **Status:** design (read-only on code; one new
`.md` committed). **Companion docs:**
[`AUDIT-distributed-semantics.md`](AUDIT-distributed-semantics.md),
[`AUDIT-turn-executor.md`](AUDIT-turn-executor.md),
[`AUDIT-federation.md`](AUDIT-federation.md),
[`AUDIT-nullifiers.md`](AUDIT-nullifiers.md),
[`AUDIT-protocol-composition.md`](AUDIT-protocol-composition.md),
[`AUDIT-cclerk.md`](AUDIT-cclerk.md),
[`AUDIT-node.md`](AUDIT-node.md),
[`KIMCHI-SURVEY.md`](KIMCHI-SURVEY.md),
[`STARBRIDGE-APPS-PLAN.md`](STARBRIDGE-APPS-PLAN.md),
[`WITNESSED-RECEIPT-CHAIN-DESIGN.md`](WITNESSED-RECEIPT-CHAIN-DESIGN.md),
[`demo/two-ai-handoff/`](demo/two-ai-handoff/).

The Silver Vision (see `~/.claude/.../memory/project-silver-and-golden-visions.md`)
is the *integration-complete* pre-algebraic state of dregg: every loop
closed, every primitive called by something. Today's demo
(`demo/two-ai-handoff/`) exercises a same-federation bearer-cap path
with a standalone STARK verifier. The unmet bar is **cross-federation**:
two nodes, two committees, a bearer cap that physically traverses a
CapTP wire boundary and produces an on-ledger receipt at the receiving
federation that the sending federation can later either trust (cheap)
or replay (expensive).

This document designs that demo. It is the verification spec for the
Silver Vision — the bench against which "Silver lands" is judged.

The demo is **two federations, one bearer cap, one CapTP delivery, one
Turn at the receiver, one receipt, one AttestedRoot, one
WitnessedReceipt chain export, one independent verifier verdict.**

---

## §0. Setup: who lives where

| Identity | Federation | Cell | Node |
|---|---|---|---|
| Alice (introducer) | F1 | `alice_cell` on F1 | Node A (`dregg-node` instance #1) |
| F1's committee | F1 | — | Node A holds threshold-share-0 (single-node committee for demo simplicity, threshold=1) |
| Bob (recipient) | F2 | `bob_cell` on F2 | Node B (`dregg-node` instance #2) |
| F2's committee | F2 | — | Node B holds threshold-share-0 |
| Charlie (verifier) | — | — | standalone `dregg-verifier` binary, no node, no shared state |

Demo physical layout: three processes (Node A, Node B, Charlie), all
local; OS pipes / files for out-of-band; QUIC/TCP for CapTP wire
between Node A and Node B.

- `federation_id_F1 = BLAKE3("dregg-fed-id-v1" || sorted_pubkeys || epoch=0)` (from `node/src/genesis.rs:133`, lane D output).
- `federation_id_F2` derived the same way over F2's committee.
- Alice's `alice_cell` is created on F1 by the genesis path; her cipherclerk's
  `signing_key` (Ed25519) is `pk_A`.
- Bob's `bob_cell` is created on F2 by F2's genesis; his cclerk key is
  `pk_B`.
- The two committees register each other's pubkeys out-of-band before
  the demo starts (the "bilateral by design" trust root from the
  cross-federation bridge test at
  `federation/tests/cross_federation_bridge_receipt.rs`).

---

## §1. The end-to-end story

Narrative, time-ordered. Every Effect, every Turn, every receipt, every
signature, every federation attestation, every wire message is named.
Square brackets `[#]` cross-reference the lane that enables the step
(see §2).

### Step 0 — Bootstrapping (out-of-band, off-demo)

0.0 — Operator starts Node A with `genesis-F1.json` (committee pk-A,
threshold=1). Node A computes
`federation_id_F1 = BLAKE3("dregg-fed-id-v1" || pk_A || 0)` and emits
`AttestedRoot_F1@h=0` over its empty ledger. [lane **D**]

0.1 — Operator starts Node B with `genesis-F2.json` (committee pk-B,
threshold=1), `federation_id_F2 = BLAKE3(...pk_B...)`. Emits
`AttestedRoot_F2@h=0`. [lane **D**]

0.2 — Out-of-band, each operator writes the *other* federation's
committee descriptor to their local `known_federations.json`. Node A
trusts F2's pk; Node B trusts F1's pk. (The demo driver script does
this via a shared file-system step, not a network handshake — the
"out-of-band" channel.)

0.3 — Operator on Node B records F2's URL/endpoint in Node A's
`peers.json` so Node A can dial F2 over CapTP wire. [lane **B**]

### Step 1 — Alice creates the bearer cap on F1

1.0 — Alice's cclerk (running in process inside Node A, owned by the
operator) constructs a `Turn`:
- `agent = alice_cell`
- `effects = [Effect::CreateBearerCap { ... }]` — but actually, in the
  current shape, this is implicit: the cclerk calls
  `SwissTable::export(swiss, recipient=bob_pk_anchor)` to register a
  swiss entry on Node A's local `CapTpState`, *then* builds a
  `HandoffCertificate` (`captp/src/handoff.rs:104-134`) over
  `{target_federation: F2, target_cell: bob_cell, recipient_pk: pk_B,
  permissions: TRANSFER_ONLY, allowed_effects: {Effect::Transfer
  mask}, nonce: rand, max_uses: 1, swiss: registered_swiss_number}`,
  signed by `pk_A`.
  - The `target_federation` here is **F2**, not F1. This is the
    three-party / cross-federation shape that
    `AUDIT-distributed-semantics.md` GAP-1 calls out as missing today.
    Lane **A** + a small SDK addition (per audit's open question 2)
    add an SDK builder for it.
- `authorization = Authorization::Signature(pk_A, sig over the
  Action)`. No `Unchecked` anywhere. [lane **C** ensures cclerk-based
  signature shows up; per `AUDIT-protocol-composition.md` §Seam 1.]
- Cipherclerk signs the SignedTurn. Alice's executor runs it; ledger writes
  `alice_cell.state.fields[7] += 1` (export counter, per
  `turn/src/executor.rs:7247-7325`) and journals `ExportSturdyRef`.
- Receipt R1 is emitted: `turn_hash=t1, federation_id=F1,
  previous_receipt_hash=None (genesis), effects_hash, ...,
  executor_signature=sig_executor_F1`. Optionally a STARK proof over
  the `EffectVm::ExportSturdyRef` row (per
  `node/src/mcp.rs::generate_effect_vm_proof`).

1.1 — Alice serializes the `HandoffCertificate` plus the F2-bound
`DreggUri { federation_id: F2, cell_id: bob_cell, swiss: <swiss_at_F1> }`
to a `dregg-handoff:` compact string. (Today's
`tool_create_bearer_cap` builds a signature but not a URI — closing
gap is the lane-A + SDK work flagged in
`demo/two-ai-handoff/README.md` Blocker 2.) Writes it to
`state/handoff.uri`.

**Subtle point** about the swiss number: bearer caps are
introducer-anchored. The swiss entry sits on **Node A** (the
introducer's node), not Node B. F2 doesn't know about this swiss
until it sees the certificate. When Bob exercises, his node sends a
CapTP wire message *to Node A* carrying the cert. Node A validates,
consumes the swiss, and routes the *Turn* construction to Node B —
because the cert's `target_federation = F2`. So Node A is the
authorizer; Node B is the executor. (Alternative topology: swiss
pre-registered at F2 via a CapTP `ExportSturdyRef` setup round. The
demo uses the introducer-anchored shape because it requires no
prior wire connection.)

1.2 — Receipt R1 enters Node A's blocklace as `Payload::Turn(serialized
turn_t1)`. After tau ordering (`blocklace/src/ordering.rs:410-482`), it
finalizes. Node A's executor commits the in-memory ledger. The
blocklace emits `BlocklaceTurnReceipt { block_id_b1, turn_data_t1,
... }` to subscribers (`blocklace/src/dregg_bridge.rs:175-201`).

1.3 — F1's "federation receipt lift" produces a
`FederationReceiptBody { turn_hash: t1, block_height: 1, block_hash:
b1, agent: alice_cell, pre_state_hash, post_state_hash, effects_hash,
previous_receipt_hash: None }`, computes `body_hash`, signs it with
F1's threshold (n=1; degenerate aggregate). Result:
`FederationReceipt_F1@t1`. [lane **D** — this is the lift seam 6 from
`AUDIT-protocol-composition.md`, currently unwired.]

1.4 — Node A periodically emits `AttestedRoot_F1@h=1` over
`(revocation_tree_root, note_tree_root, nullifier_set_root)`. The
attested root binds *which blocklace block* via the F3 fix from
`AUDIT-federation.md` — adding `blocklace_finality: { block_id: b1,
round, tau_index }` to `AttestedRoot::signing_message`. [lane **D**.]

### Step 2 — Alice transmits the URI to Bob (out-of-band)

2.0 — Demo driver `cp state/handoff.uri state/bob-inbox/handoff.uri`.
This is the "out-of-band channel"; in reality it'd be email/QR/Signal.
No code change required.

### Step 3 — Bob enlivens, then exercises

3.0 — Bob's cclerk (running in Node B) reads
`state/bob-inbox/handoff.uri`, parses the compact form into
`(HandoffCertificate, DreggUri{federation_id: F2, ...})`. **The
URI's federation_id is F2** — Bob's local federation. The swiss
number's home, however, is on Node A. Bob's cclerk:

  a. Builds a `HandoffPresentation` (`captp/src/handoff.rs:295-336`) by
     signing the `presentation_message` (`dregg-handoff-present-v1` ||
     cert.nonce || target_cell || target_federation) with `pk_B`.
  b. Opens (or reuses) a CapTP wire session to Node A (the introducer).
     Hardening layer (`wire/src/hardening.rs`) charges a token-bucket
     cost of 2 for `PresentHandoff`.
  c. Sends `WireMessage::PresentHandoff { presentation_bytes,
     introducer_pk: pk_A }`. [lane **B** — wire delivery confirmed
     landed.]

3.1 — Node A receives `PresentHandoff` (`wire/src/server.rs:2509-2607`):
- Validates the cert: introducer sig under `pk_A` matches, recipient
  sig under `pk_B` matches, `pk_A` cross-checks against
  `known_federations[F1].pubkey` (closing GAP-3 from
  `AUDIT-distributed-semantics.md`, dependent on lane B and the
  small `FederationId → PublicKey` registry on the wire), not
  expired, swiss exists and `max_uses` not exhausted.
- Builds a `ValidateHandoff` effect on Node A's local cell state
  (counter bump). Pushes a Turn t2_A onto Node A's
  `pending_captp_turns` queue. [lane **A** — the previously stub
  drainer in `wire/src/server.rs:1382` now actually runs and feeds
  the executor.]
- Returns `WireMessage::HandoffAccepted { routing_token, cell_id:
  bob_cell, permissions_tag: TRANSFER_ONLY }` to Node B.
- **Critical new behavior post lane A:** when the cert's
  `target_federation == F2 ≠ self_federation == F1`, Node A
  *additionally* forwards the validated presentation to Node B
  via a new `WireMessage::DeliverCapTpHandoff { cert, sender_pk:
  pk_B, sender_signature_over_target_turn }` (or, equivalently,
  Node A just acknowledges and Bob's node constructs the receiving
  Turn locally, knowing the cert is now consumed at F1). The
  cleaner shape — what the lane needs — is for Node A to *return*
  a one-shot delivery token bound to the consumed swiss; Bob then
  builds the F2-side Turn carrying the cert as
  `Authorization::CapTpDelivered`.

3.2 — Bob's cclerk, holding `Authorization::CapTpDelivered { handoff_cert,
introducer_pk: pk_A, sender_pk: pk_B, sender_signature: sig over
captp_delivered_signing_message(cert.nonce, agent=bob_cell,
target=bob_cell, turn_nonce=1, effects=[Effect::Transfer { from:
alice_cell, to: bob_cell, amount: 100 }]) }`, builds Turn t2_B:
- `agent = bob_cell`
- `effects = [Effect::Transfer { from: alice_cell, to: bob_cell,
  amount: 100 }]`
- `authorization = Authorization::CapTpDelivered { ... }` (the
  variant in-flight at `turn/src/action.rs:141-153`)
- `nonce = 1`, `previous_receipt_hash = R_genesis_F2` (Bob's chain
  head, threaded via the cipherclerk's `last_receipt_hash`, closing P0-3
  from `AUDIT-turn-executor.md` — depends on lane C cclerk
  threading the receipt hash).
- Signs the SignedTurn under `pk_B`.

3.3 — Bob submits t2_B to Node B's executor. Node B's
`verify_authorization` (`turn/src/executor.rs:4138`) sees
`Authorization::CapTpDelivered { handoff_cert, introducer_pk,
sender_pk, sender_signature }`:
- Verifies introducer signature on `handoff_cert` under
  `introducer_pk`.
- Cross-checks `introducer_pk` derives from `handoff_cert.introducer`
  (== F1) by looking up `known_federations[F1].pubkey == pk_A`.
- Verifies `sender_signature` over the canonical
  `captp_delivered_signing_message(cert.nonce, agent, target,
  turn_nonce, effects)` under `sender_pk`.
- Checks `sender_pk == handoff_cert.recipient_pk`.
- Checks `handoff_cert.target_federation == self_federation == F2`.
- Checks `handoff_cert.target_cell == agent == bob_cell` (or the
  Transfer's `to` cell matches the target).
- Checks `handoff_cert.allowed_effects` mask covers `Effect::Transfer`.
- Replay check: `handoff_cert.nonce` is recorded in a per-cell
  nullifier-shaped "consumed certs" set (closes GAP-2 from
  `AUDIT-distributed-semantics.md`, partly via lane **F redux**'s
  nullifier set production wiring).

3.4 — Authorization OK. Executor applies `Effect::Transfer`:
- `bob_cell.balance += 100`
- `alice_cell` is **not in Node B's ledger** — it's a F1-side cell.
  The executor treats it as a "remote stub" (the demo's current
  pattern, see `demo/two-ai-handoff/bob.py` pre-funded stub at
  1,000,000). The decrement `alice_cell.balance -= 100` happens on
  the *stub* (so Node B's view of alice_cell drops to 999,900). The
  real settlement against F1's ledger is async — see Step 5.
- Journal entries: `BalanceDelta(bob_cell, +100)`,
  `BalanceDelta(alice_cell_stub, -100)`,
  `ConsumedCert(cert.nonce)`.

3.5 — Receipt R2 (Bob's): `turn_hash: t2_B`, `federation_id: F2`,
`previous_receipt_hash: R_genesis_F2`, `pre_state_hash`,
`post_state_hash`, `effects_hash`, `agent: bob_cell`,
`executor_signature: sig_executor_F2 over
canonical_executor_signed_message(t2_B, pre, post, ts) ||
federation_id_F2 || agent || previous_receipt_hash` (closes F2 from
`AUDIT-federation.md` — depends on lane D's signature widening).

3.6 — Effect-VM proof for t2_B: bob_cell's per-cell trace contains
one `VmEffect::Transfer { amount: 100, direction: 0 (credit) }` row.
The 32-byte truncation gap (`AUDIT-turn-executor.md` P1-2,
`AUDIT-protocol-composition.md` Seam 4) is unchanged in Silver —
amount fits in 4 bytes, so for the demo the proof is meaningful.
STARK proof bytes + public inputs stored alongside R2.

3.7 — t2_B enters Node B's blocklace as a `Payload::Turn`. Tau
finalizes it at block b2 on F2. `BlocklaceTurnReceipt` emitted.

3.8 — F2's federation receipt lift produces
`FederationReceiptBody_F2@t2_B`, signs under F2's threshold, emits
`FederationReceipt_F2@t2_B`. [lane **D**.]

3.9 — Node B emits `AttestedRoot_F2@h=2` carrying `merkle_root,
nullifier_set_root` (now non-empty, post-F-redux: `cert.nonce` is in
the consumed-cert nullifier set), `blocklace_finality: { block_id:
b2, ... }`. Signed by F2's committee. [lane **D** + lane **F
redux**.]

### Step 4 — F1 ↔ F2 attestation exchange

4.0 — Node A pulls `AttestedRoot_F2@h=2` from Node B (CapTP wire,
`WireMessage::RequestAttestedRoot` / `WireMessage::AttestedRoot`,
already wired per `wire/src/server.rs:2288` and 2960). Verifies the
QC against F2's committee descriptor (registered in 0.2). Stores it
as F1-side evidence of "F2 says block b2 finalized at h=2 with these
roots." [lane **B** for the wire delivery; lane **D** for the
committee-bound verification.]

4.1 — Node B symmetrically pulls `AttestedRoot_F1@h=1` from Node A.
Same flow in reverse. (Optional for the demo; not load-bearing
because F1 is the cert-issuer and doesn't *need* to attest the
delivery — but in steady state both sides exchange.)

### Step 5 — Bob's WitnessedReceipt chain export

5.0 — Bob's cclerk exports a `Vec<WitnessedReceipt>` of length 1 (or
more, if seeded with genesis): each entry pairs R2 with the
EffectVm STARK proof + public inputs + `WitnessBundle { pre_state,
effects, context, secrets: [] }` per
[`WITNESSED-RECEIPT-CHAIN-DESIGN.md`](WITNESSED-RECEIPT-CHAIN-DESIGN.md)
§2. Strategy A (in-line) — no encryption.

5.1 — The export *additionally* carries:
  - The original `HandoffCertificate` (signed by pk_A, F1's identity).
  - `AttestedRoot_F1@h=1` (so the verifier can later check "F1's
    committee attests F1 was at height 1 with this root, and Alice's
    grant turn is part of F1's blocklace at b1").
  - `AttestedRoot_F2@h=2` (binding R2 to F2's blocklace at b2).
  - F2's `FederationReceipt_F2@t2_B` (the BLS aggregate over the
    receipt body, per `federation/src/receipt.rs:122-227`).

5.2 — This bundle is the **cross-federation Silver Vision artifact**:
a verifier with both committee pubkeys (pre-registered) can verify
the entire path without trusting either node's executor.

### Step 6 — Charlie verifies

6.0 — `dregg-verifier` (standalone binary,
`demo/two-ai-handoff/charlie.py` shells to it) takes the bundle on
stdin. It does, in order:

  i. Verify F1's signature on the `HandoffCertificate` under
     F1's committee pubkey (cert.introducer == F1, look up pk_A in
     known_federations).
  ii. Verify F2's signature on the `HandoffPresentation` (recipient
      sig over presentation_message).
  iii. Verify the EffectVm STARK proof against the public inputs
       (scope-1, current `dregg-verifier` does this).
  iv. Replay scope-2: take `WitnessBundle.pre_state` and
      `WitnessBundle.effects`, call
      `generate_effect_vm_trace_ext(pre_state, effects, context)`,
      check the derived PI matches the recorded PI, re-verify the
      proof (per `WITNESSED-RECEIPT-CHAIN-DESIGN.md` §5).
  v. Verify F1's `AttestedRoot_F1@h=1` quorum signature under F1's
     committee.
  vi. Verify F2's `AttestedRoot_F2@h=2` quorum under F2's committee.
  vii. Verify F2's `FederationReceipt_F2@t2_B` quorum.
  viii. **Cross-link**: confirm
        `FederationReceipt_F2.body.turn_hash == R2.turn_hash`;
        confirm `R2.federation_id == F2`; confirm
        `R2.previous_receipt_hash` matches the prior receipt's hash
        (genesis at chain head); confirm
        `Authorization::CapTpDelivered.handoff_cert.nonce ==
        cert.nonce` (linking R2 to the F1-issued cert).

6.1 — If every check passes, Charlie prints `PASS` and exits 0. **The
Silver Vision holds end-to-end.**

---

## §2. What each in-flight lane contributes

| Lane | Topic | Step(s) it enables | Was unwired | Wired after |
|---|---|---|---|---|
| **A** (CapTP→Turn drainer) | `pending_captp_turns` drained into executor; `Authorization::CapTpDelivered` honored. | 3.1, 3.3, 3.4 | No code drained `pending_captp_turns` (`AUDIT-distributed-semantics.md` GAP-12); even drained, `Unchecked` was rejected by executor (GAP-13). | Drainer wired; `Authorization::CapTpDelivered` verified by executor at `executor.rs:4138`. |
| **B** (CapTP wire delivery, **LANDED**) | TLS+QUIC frames; `PresentHandoff`, `EnlivenSturdyRef`, `DropRemoteRef`, `AttestedRoot` request/response carried between nodes. | 3.0, 3.1, 4.0, 4.1 | `WireMessage` variants existed but server handlers were partial or noops. | Wire hardening (`wire/src/hardening.rs`) + handlers in `wire/src/server.rs:2288-2960` deliver these in both directions; rate-limited, heartbeat-watched, graceful shutdown emits `CapGoodbye`. |
| **C** (app-framework cclerk, **LANDED**) | App code holds a real `AgentCipherclerk` instead of `[0u8; 64]` placeholder signatures. | 1.0, 1.1, 3.2 | Apps reach past SDK with placeholder sigs (`AUDIT-protocol-composition.md` Seam 1; `AUDIT-cclerk.md` P1-1). | App-framework integrates `AgentCipherclerk`; `Authorization::Signature(pk, sig)` is real; SDK `cclerk.make_turn`, `make_action` are used. |
| **D** (federation + blocklace) | `federation_id = H(committee_pubkeys || epoch)`; `AttestedRoot` carries `blocklace_finality`; `FederationReceipt` lift on commit; F2 fix (federation_id in executor signing message). | 0.0, 0.1, 1.3, 1.4, 3.5, 3.8, 3.9 | `federation_id` was 16 random bytes (`AUDIT-federation.md` F1); `AttestedRoot` had no blocklace binding (F3); `FederationReceipt` had no production producer (F7); executor signature was federation-agnostic (F2). | All four closures land; `node/src/genesis.rs:133` already does the H-derivation; the lift seam 6 from `AUDIT-protocol-composition.md` is the remaining call site. |
| **F redux** (nullifier production + privacy) | Consumed-cert nullifier set populated; `Authorization::CapTpDelivered.handoff_cert.nonce` recorded in F2's `NullifierSet`; `nullifier_set_root` non-empty in `AttestedRoot_F2`. | 3.3 (replay check), 3.4 (journal), 3.9 (root). | `NullifierSet` populated only in wasm sim (`AUDIT-nullifiers.md` §3); `JournalEntry::NoteSpend` discarded on commit; certs had no replay defense (`AUDIT-distributed-semantics.md` GAP-2). | `store/src/lib.rs:578` (`spend_note_atomic`) is the redb path; lane wires it from `journal.rs:440-451` on commit; cert nonces use the same primitive. |
| **γ.2** (bilateral binding) | Cross-cell algebraic binding: `bob_cell`'s `+100` row is proof-system-equal to `alice_cell_stub`'s `-100` row. | 3.6 (per-cell), 6.0.iii–iv | Today's per-cell proofs are independent; cross-cell coherence is executor-trusted (`AUDIT-protocol-composition.md` Seam 9; `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`). | Aggregator AIR proves the two rows project from one shared `Effect::Transfer`; `aggregate_membership` on `WitnessedReceipt` populated. **For the Silver demo, γ.2 is *optional* (Silver is trust-based and accepts executor glue), but having it land closes the bridge-boundary gap from Step 3.4's note.** Without γ.2, Step 6.0.viii's `R2.federation_id == F2` + `R2.executor_signature` is the only binding that says alice_cell_stub really lost 100; that's the executor-trust assumption Silver is willing to make. |

The Silver Vision *runs* without γ.2. γ.2 is the entry point to Golden;
its absence is exactly what the Silver/Golden split was coined to
preserve.

### What's not a lane but is required

- **SDK builder for cross-federation handoff** (`AUDIT-distributed-semantics.md`
  open question 2). Today `CapTpClient::create_handoff` hardcodes
  `target_federation = self.config.federation_id`. We need a
  `create_cross_fed_handoff(target_federation, target_cell, recipient_pk,
  permissions, allowed_effects, ...)` SDK entry. **This is the only
  net-new code item not covered by any in-flight lane.** Estimated:
  ~30 LOC in `sdk/src/captp_client.rs`.
- **Bearer-cap URI compact form** (`demo/two-ai-handoff/README.md` Blocker 2).
  `dregg_create_bearer_cap` currently emits a signature, not a URI. We
  need `SwissTable::export` integration on the MCP path. Lane A
  arguably covers this; if not, it's another ~50 LOC.
- **`FederationId → PublicKey` registry on the wire**
  (`AUDIT-distributed-semantics.md` GAP-3). Today `validate_handoff`
  accepts the introducer_pk from the wire message without checking it
  matches the registered committee key for `cert.introducer`. Lane D's
  committee-binding work needs to expose a lookup. ~20 LOC.
- **Receipt-chain `previous_receipt_hash` threading in the cclerk**
  (`AUDIT-turn-executor.md` P0-3; `AUDIT-cclerk.md` P3-6;
  `demo/two-ai-handoff/README.md` Blocker 7). Lane C ought to thread
  this; if it didn't, it's ~50 LOC in the cipherclerk's turn-builder path.

---

## §3. What's still unwired even after all lanes land

Honest gaps. These do **not** block the Silver demo from running, but
they affect what the verifier can claim.

### 3.1 — `WitnessedReceipt` export does not include the cross-fed `AttestedRoot` by default

`WitnessedReceipt` (per `WITNESSED-RECEIPT-CHAIN-DESIGN.md` §2) carries
`receipt + proof + witness`. It does **not** carry the
`AttestedRoot_F1@h=1` that the verifier needs in Step 6.0.v to verify
the cert is rooted in F1's finalized state. The export format is
extensible; we need a wrapper type for the cross-federation case:

```rust
pub struct CrossFedReceiptBundle {
    /// The receiving federation's chain (Bob's WitnessedReceipts).
    pub recipient_chain: Vec<WitnessedReceipt>,
    /// The sending federation's attested root at cert-issuance height.
    pub issuer_attested_root: AttestedRoot,
    /// The receiving federation's attested root at receipt height.
    pub recipient_attested_root: AttestedRoot,
    /// The handoff certificate that linked them.
    pub cross_fed_cert: HandoffCertificate,
    /// (Optional) Federation-level receipt for additional binding.
    pub recipient_federation_receipt: Option<FederationReceipt>,
}
```

This type does not exist today. ~80 LOC plus serde + a verifier
sub-routine. Estimated effort to add: half a day. Not blocking — the
demo can stitch the artifacts together with a Python wrapper before
the type lands.

### 3.2 — No wire route for proactive `AttestedRoot` push

Today Node A *responds* to `WireMessage::RequestAttestedRoot` from
Node B (`wire/src/server.rs:2288-2294`), but it does not *push*. So in
the demo, Step 4.0 has Node A *pulling* from Node B. That works, but
in steady state, federations would want to push their latest roots to
peers that subscribed to them. There is a `PeerMessage::AttestedRootUpdate`
gossip message (`node/src/gossip.rs:78`), but that's intra-federation,
not cross-federation. Not a Silver blocker; Golden territory.

### 3.3 — What if Bob's node doesn't have Alice's committee pubkeys registered?

Step 0.2 (out-of-band committee registration) is the trust root. If
the operator forgets, every step that touches `known_federations[F1]`
fails: Node A's `validate_handoff` would still pass (the cert is from
itself), but Node B's executor in Step 3.3 cannot verify
`introducer_pk` derives from `handoff_cert.introducer == F1` because
F1 is not in `known_federations`. Result: Bob's turn rejects with
`UnknownFederation`. **This is the correct fail-closed behavior.**
The demo's setup script makes the registration explicit; production
needs a separate "federation discovery" story (out of scope).

### 3.4 — `alice_cell` settlement on F1 is async and not in the demo

After Step 3.4, F2 believes `alice_cell.balance -= 100`. But F1 hasn't
been told. The bearer cap's exercise on F2 is a *claim*; the actual
settlement on F1 is a separate Turn that:
- Alice's node A executes once it sees `AttestedRoot_F2@h=2` carrying
  R2's effects_hash (or `FederationReceipt_F2@t2_B`).
- The settlement Turn debits `alice_cell` on F1 and emits a "cap
  exercised, balance reconciled" event.
- This is the Stage 9 bridge-settlement flow; **not in the Silver demo**.
- The Silver demo treats `alice_cell` on F2 as a stub (the demo's
  current "pre-funded remote stub" pattern). The verifier accepts that
  F2's view of alice_cell is a stub; F1's view is the truth-of-record.

The reason we can defer: Silver Vision is *trust-based*. F2 believes
F1 will eventually settle because F1's executor is presumed honest.
Golden Vision needs algebraic settlement: a STARK proof on F1 of
"alice_cell.balance reduced by 100 because of this cert that F2
attests was exercised at h=2." That's γ.2-shaped.

### 3.5 — Cert revocation across federations

If F1 revokes Alice's grant cap *after* she issued the bearer cert but
*before* Bob exercises, Node B's executor has no way to know. The
`RevocationChannelSet` (`token/src/revocation.rs`) is per-federation;
cross-fed revocation requires the issuing federation to push a
revocation root to peers (subscription model). Not a Silver blocker;
the cert has `expires_at` and `max_uses: 1` defenses.

### 3.6 — `BlindedQueue::consume_private` not in the demo flow

The lane F redux description names "BlindedQueue::consume_private
verifies its spending proof" as a privacy-wiring gap. The Silver demo
above doesn't touch blinded queues — it's a vanilla `Effect::Transfer`.
For the Silver demo to *also* exercise privacy, we'd need a variant
where Alice's grant covers `Effect::NoteSpend + NoteCreate` rather
than `Transfer`, and Bob exercises the cap on a private-transfer path.
Useful for a Silver+Privacy variant; not required for Silver baseline.

### 3.7 — Sovereign-cell proof-carrying turns

`MakeSovereign` + sovereign cells with their own STARK proofs
(`turn/src/executor.rs:928-1054`'s `verify_and_commit_proof` path) are
not exercised in this demo. The demo uses hosted cells. Silver
*supports* sovereign cells via lane D + γ.2; the demo just doesn't
exercise that path. Add a "Silver+Sovereign" variant later.

### 3.8 — Mutex poisoning and `Authorization::Unchecked` carve-outs

`AUDIT-turn-executor.md` P1-5 and P1-4 are background hygiene: if the
demo node panics inside an executor mutex (e.g. mid-turn OOM), the
node halts. Not exploited in the demo. Similarly the `Unchecked`
authorization is still emitted by `wire/src/captp_routing.rs:48` for
CapTP-routing turns (the mirror-state-only turn that Node A pushes for
its own `ValidateHandoff` mirror in Step 3.1). Those turns mutate only
counter fields on Node A's own cell; not security-load-bearing for
Silver. The "no Unchecked anywhere" goal needs an explicit carve-out
list (per `AUDIT-protocol-composition.md` Composition Verdict).

### 3.9 — `chain/src/withdraw.rs` parallel nullifier definition

`AUDIT-nullifiers.md` §1f flags two parallel note-nullifier
derivations differing in domain string. Silver demo uses
`cell/src/note.rs` only; `withdraw.rs` is unused. Either delete or
document — Silver hygiene, not a runner.

### 3.10 — Determinism for scope-3 replay

`WITNESSED-RECEIPT-CHAIN-DESIGN.md` §1 case (3) "Re-execute the turn"
requires the executor to be deterministic (no clock reads, no gossip
side effects). Today the executor reads the federation clock at commit
time and pipelined sends touch the wider gossip log. The Silver demo
uses scope-2 (re-derive trace + verify), which doesn't need
determinism. Scope-3 is Golden.

---

## §4. The test/demo: `demo/silver-vision-e2e/run.sh`

Concrete shape. Path: `demo/silver-vision-e2e/`. Layout mirrors
`demo/two-ai-handoff/`.

### 4.1 Directory layout

```
demo/silver-vision-e2e/
├── run.sh                    # orchestrator (this section)
├── README.md                 # narrative (mirrors §1 above)
├── expected.json             # post-conditions
├── alice.py                  # drives Node A via MCP
├── bob.py                    # drives Node B via MCP
├── charlie.py                # drives dregg-verifier
├── setup_federations.sh      # genesis + committee cross-registration
├── state/                    # scratch (cleaned by run.sh)
│   ├── F1/                   # Node A data dir + genesis.json
│   ├── F2/                   # Node B data dir + genesis.json
│   ├── known/                # cross-registered committee descriptors
│   ├── handoff.uri           # the bearer cap, written by alice.py
│   ├── bob-inbox/handoff.uri # symlinked / copied (the "out-of-band channel")
│   ├── grant.proof.json      # Alice's grant proof (optional, EffectVm)
│   ├── exercise.proof.json   # Bob's exercise proof (EffectVm)
│   ├── attested_F1.json      # AttestedRoot_F1@h=1
│   ├── attested_F2.json      # AttestedRoot_F2@h=2
│   ├── fed_receipt_F2.json   # FederationReceipt over R2
│   ├── bundle.json           # CrossFedReceiptBundle (§3.1 type, demo-stitched)
│   └── logs/                 # per-process stderr
```

### 4.2 `setup_federations.sh`

```bash
#!/usr/bin/env bash
set -euo pipefail

# (1) genesis F1
$NODE_BIN genesis \
  --name F1 \
  --data-dir state/F1 \
  --committee-key state/F1/committee.key \
  --threshold 1

# (2) genesis F2
$NODE_BIN genesis \
  --name F2 \
  --data-dir state/F2 \
  --committee-key state/F2/committee.key \
  --threshold 1

# (3) cross-register committees out-of-band
mkdir -p state/known
cp state/F1/federation_descriptor.json state/known/F1.json
cp state/F2/federation_descriptor.json state/known/F2.json
$NODE_BIN register-federation --data-dir state/F1 --descriptor state/known/F2.json
$NODE_BIN register-federation --data-dir state/F2 --descriptor state/known/F1.json
```

`register-federation` is an additive CLI; today's `--bind 0.0.0.0`
config knob plus genesis already produce the descriptor file. The
binary needs a one-shot subcommand to ingest a peer descriptor and
write it to `known_federations.json`. Estimated: ~40 LOC in
`node/src/main.rs`.

### 4.3 `run.sh` (sketch — ~15 numbered steps)

```bash
#!/usr/bin/env bash
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# step 0a: build
cargo build -p dregg-node -p dregg-verifier | tee state/logs/build.log

# step 0b: clean + genesis + cross-register
rm -rf state/F1 state/F2 state/known state/bob-inbox state/*.json
mkdir -p state/bob-inbox state/logs
./setup_federations.sh

# step 0c: start nodes
$NODE_BIN run --data-dir state/F1 --bind 127.0.0.1:7811 --peer 127.0.0.1:7822 &
NODE_A_PID=$!
$NODE_BIN run --data-dir state/F2 --bind 127.0.0.1:7822 --peer 127.0.0.1:7811 &
NODE_B_PID=$!
trap "kill $NODE_A_PID $NODE_B_PID 2>/dev/null" EXIT
sleep 2  # wait for handshake

# step 1: alice creates bearer cap targeting F2 + bob_cell (CROSS-FED HANDOFF)
ALICE_OUT=$(python3 alice.py \
    --node-bin $NODE_BIN \
    --node-endpoint 127.0.0.1:7811 \
    --target-federation $(cat state/known/F2.json | jq -r .federation_id) \
    --bob-pk $(cat state/known/F2.json | jq -r .operator_pk) \
    --amount 100 \
    --state-dir state/)
echo "$ALICE_OUT" | jq . > state/alice.json
# writes state/handoff.uri, state/attested_F1.json, state/grant.proof.json

# step 2: out-of-band channel
cp state/handoff.uri state/bob-inbox/handoff.uri

# step 3: bob enlivens + exercises (CapTpDelivered authorization)
BOB_OUT=$(python3 bob.py \
    --node-bin $NODE_BIN \
    --node-endpoint 127.0.0.1:7822 \
    --introducer-endpoint 127.0.0.1:7811 \
    --uri-file state/bob-inbox/handoff.uri \
    --state-dir state/)
echo "$BOB_OUT" | jq . > state/bob.json
# writes state/exercise.proof.json, state/attested_F2.json, state/fed_receipt_F2.json

# step 4: explicit attested-root exchange (informational; bob.py + alice.py
# already pulled what they need at step 1/3)

# step 5: bob exports the CrossFedReceiptBundle
python3 bob.py --mode export-bundle --state-dir state/ > state/bundle.json

# step 6: charlie verifies
CHARLIE_OUT=$(python3 charlie.py \
    --verifier-bin $VERIFIER_BIN \
    --bundle state/bundle.json \
    --known-F1 state/known/F1.json \
    --known-F2 state/known/F2.json)
echo "$CHARLIE_OUT" | jq . > state/charlie.json

# step 7..15: assert post-conditions (see expected.json)
PASS=1
for check in \
    '.cert_introducer_sig_verified' \
    '.cert_recipient_sig_verified' \
    '.effect_vm_proof_verified' \
    '.witness_chain_replay_verified' \
    '.attested_root_F1_verified' \
    '.attested_root_F2_verified' \
    '.federation_receipt_F2_verified' \
    '.cross_link_cert_to_receipt' \
    '.bob_cell_credited_100' \
    '.alice_stub_debited_100' \
    '.cert_nonce_in_nullifier_set' \
    '.attested_root_F2_blocklace_bound' \
    '.executor_signature_includes_federation_id'
do
    val=$(jq -r "$check" state/charlie.json)
    if [ "$val" = "true" ]; then
        echo "PASS  $check"
    else
        echo "FAIL  $check"
        PASS=0
    fi
done

[ $PASS -eq 1 ] && echo "PASS — Silver Vision end-to-end" || (echo "FAIL"; exit 1)
```

### 4.4 `expected.json`

```json
{
  "scenario": "alice_F1 grants TRANSFER_ONLY(100) cross-fed to bob_F2 via bearer cap",
  "transfer_amount": 100,
  "must_pass": [
    "cert_introducer_sig_verified",
    "cert_recipient_sig_verified",
    "effect_vm_proof_verified",
    "witness_chain_replay_verified",
    "attested_root_F1_verified",
    "attested_root_F2_verified",
    "federation_receipt_F2_verified",
    "cross_link_cert_to_receipt",
    "bob_cell_credited_100",
    "alice_stub_debited_100",
    "cert_nonce_in_nullifier_set",
    "attested_root_F2_blocklace_bound",
    "executor_signature_includes_federation_id"
  ],
  "must_not_pass": [
    "cert_replayable_after_consumption",
    "tampered_handoff_cert_accepted",
    "missing_committee_key_accepted",
    "wrong_federation_id_in_turn_accepted"
  ]
}
```

The `must_not_pass` list is critical: it's the negative-test set the
verifier should reject. Each is a one-line variation of the demo:
- `cert_replayable_after_consumption`: re-submit Bob's exercise turn;
  expect rejection because cert.nonce is in F2's nullifier set.
- `tampered_handoff_cert_accepted`: flip a byte in
  `handoff_cert.allowed_effects`, re-sign with a *different* key;
  expect Charlie to reject.
- `missing_committee_key_accepted`: drop F1 from
  `state/known/F1.json`; expect Bob's executor to reject the
  delivery at Step 3.3.
- `wrong_federation_id_in_turn_accepted`: edit R2 to claim
  `federation_id: F1`; expect Charlie to detect the executor_signature
  mismatch (depends on lane D's F2 fix).

### 4.5 `alice.py`, `bob.py`, `charlie.py`

Modeled directly on `demo/two-ai-handoff/*.py`. Net changes vs. the
two-AI demo:

- `alice.py` adds `--target-federation` and `--bob-pk` from F2's
  descriptor (instead of using its own federation_id). Calls a new
  MCP tool `dregg_create_cross_fed_bearer_cap`.
- `bob.py` adds `--introducer-endpoint` (where to send `PresentHandoff`)
  and consumes the cert into `Authorization::CapTpDelivered` instead
  of `Bearer`. Also pulls `AttestedRoot_F1` from Node A and
  `FederationReceipt` from Node B.
- `charlie.py` accepts a `CrossFedReceiptBundle` JSON and shells to
  `dregg-verifier verify-cross-fed-bundle --bundle path --known-F1 path
  --known-F2 path`. The verifier needs a new subcommand that does the
  8-step check from §1 Step 6.

### 4.6 Assertions in plain language

A demo run prints:

```
[silver-demo] step 0  — genesis F1 + F2, cross-register committees
[silver-demo] step 1  — alice grants 100-TRANSFER_ONLY cap (cross-fed, F1→F2)
[silver-demo] step 2  — uri delivered out-of-band
[silver-demo] step 3  — bob enlivens at F1 (introducer), exercises at F2 (target)
[silver-demo] step 4  — attested roots exchanged
[silver-demo] step 5  — bob exports CrossFedReceiptBundle
[silver-demo] step 6  — charlie verifies (8 checks)
[silver-demo] PASS    — Silver Vision end-to-end
```

---

## §5. What we'd need to add to make this demo run

Delta from `demo/two-ai-handoff/` (today) to `demo/silver-vision-e2e/`
(this design):

### 5.1 Already covered by in-flight lanes

- **Two-node infra**: `dregg-node` already runs as a daemon; today's
  two-AI demo runs two `dregg-node mcp` processes for prover/verifier
  but only *one* `dregg-node run` for the ledger. The silver demo
  needs two `dregg-node run`s with peering. Lane B's wire delivery
  enables this; `--peer` CLI flag may need adding (~10 LOC).

- **`Authorization::CapTpDelivered`** lands as part of lane A. The
  variant is already declared in `turn/src/action.rs:141-153`; the
  executor verify path is at `executor.rs:4138`. Both will be active
  post-lane-A.

- **`federation_id = H(committee_pubkeys)`** is in
  `node/src/genesis.rs:133` already; lane D ensures it's enforced
  end-to-end (executor's `local_federation_id` derived from the
  same).

- **`AttestedRoot` blocklace binding** comes with lane D. Adds the
  `blocklace_finality: { block_id, round, tau_index }` field to
  `types/src/lib.rs::AttestedRoot` (F3 from `AUDIT-federation.md`).

- **`FederationReceipt` production** lands as part of lane D (seam 6
  from `AUDIT-protocol-composition.md`). The cipherclerk's
  `append_receipt` path or the executor's commit path triggers
  `FederationReceipt::with_threshold_qc(...)`.

- **Receipt-chain `previous_receipt_hash`** lands as part of lane C
  (cclerk threads it through every turn-builder method, closing
  `AUDIT-cclerk.md` P3-6 and `AUDIT-turn-executor.md` P0-3).

- **App-framework signed actions** land as part of lane C
  (`[0u8; 64]` placeholders are gone; `Authorization::Signature(pk,
  sig)` is real).

- **Cert-nonce nullifier set** lands as part of lane F redux:
  cert.nonce is recorded in a per-federation `NullifierSet` on
  exercise; the `nullifier_set_root` field of `AttestedRoot_F2` is
  non-empty.

### 5.2 Net-new work outside the in-flight lanes

The delta below is the **honest extra work** beyond the four lanes.

1. **SDK: cross-federation handoff builder** —
   `sdk/src/captp_client.rs::create_cross_fed_handoff(target_federation,
   target_cell, recipient_pk, permissions, allowed_effects,
   expires_at, max_uses)`. ~30 LOC. (`AUDIT-distributed-semantics.md`
   open question 2.)

2. **MCP tool: `dregg_create_cross_fed_bearer_cap`** —
   `node/src/mcp.rs`. Wraps the SDK builder. Emits a
   `dregg-handoff:` URI containing the cert + URI tuple. Closes
   `demo/two-ai-handoff/README.md` Blocker 2 in its cross-fed form.
   ~80 LOC.

3. **Wire: `FederationId → PublicKey` registry lookup in `validate_handoff`** —
   `wire/src/server.rs::PresentHandoff` handler. Replace the
   wire-supplied `introducer_pk` with a lookup against
   `known_federations[cert.introducer]`. Closes
   `AUDIT-distributed-semantics.md` GAP-3. ~20 LOC.

4. **`CrossFedReceiptBundle` type + serde** — new file
   `turn/src/cross_fed_bundle.rs` (or in
   `witnessed_receipt.rs`). Carries the chain + both `AttestedRoot`s
   + the cert + optional `FederationReceipt`. ~80 LOC.

5. **`dregg-verifier verify-cross-fed-bundle` subcommand** —
   `verifier/src/bin/main.rs`. Reads bundle JSON, performs the
   8-step verification from §1 Step 6, prints a JSON verdict. ~150
   LOC.

6. **`dregg-node register-federation` CLI** — one-shot subcommand
   to ingest a peer's federation descriptor and write to
   `known_federations.json`. ~40 LOC in `node/src/main.rs`.

7. **`dregg-node run --peer <addr>` CLI** — already exists in some
   form; verify it triggers a CapTP wire connection. If not, ~10
   LOC.

8. **The demo scripts**: `setup_federations.sh`, `alice.py`,
   `bob.py`, `charlie.py`, `run.sh`, `README.md`, `expected.json`.
   ~600 LOC total in Python and bash.

**Total net-new code outside lanes: ~410 LOC of Rust + ~600 LOC of
demo scripts.**

### 5.3 Optional polish (post-Silver, pre-Golden)

- Multi-node committees (n=4, threshold=3) rather than n=1. Lane D
  primitives already support this; the demo just uses n=1 for
  simplicity.
- Multi-turn chains: have Alice and Bob each do *several* turns so
  the `WitnessedReceipt` chain is non-trivial.
- `BlindedQueue::consume_private` variant of the demo (Silver+Privacy)
  exercises the F-redux nullifier path on note spends rather than
  certs.
- Sovereign-cell variant (Silver+Sovereign): Alice's cell is sovereign
  and her grant turn carries an `execution_proof`.
- IVC-compressed history: post-export, run `dregg_compress_history`
  on Bob's chain and have Charlie verify the compressed proof
  alongside the per-receipt proofs.

None of these are required to call the Silver Vision "verified".

---

## §6. Open questions

The lanes leave these unresolved. Each blocks Silver only if the
answer is "no, we haven't decided" — pick a default and ship.

### 6.1 — Where does cert-nonce live in F2's nullifier set?

Lane F redux records `cert.nonce` somewhere to prevent replay
(Step 3.3 check). Options:
- (a) A new per-federation `consumed_certs: NullifierSet` field on
  Node B's `CapTpState` or a sibling structure. Distinct from
  `BridgedNullifierSet` (which is cross-bridge double-mint, not
  cert-replay). Bound by `AttestedRoot.nullifier_set_root`?
- (b) Reuse `BridgedNullifierSet` with the cert.nonce as the
  nullifier value. Conceptual stretch (a cert isn't a bridge), but
  it reuses the rollback-journal path.
- (c) A per-cell `consumed_cert_nonces: BTreeSet` on the agent cell.
  Local; not committed in `AttestedRoot.nullifier_set_root`. Cheap
  but external verifier can't check it without the full chain.

Recommendation: **(a)**, with the new set committed in
`AttestedRoot.nullifier_set_root` (alongside the note-nullifier
contributions). Closes both `AUDIT-distributed-semantics.md` GAP-2
and `AUDIT-nullifiers.md` §3.

### 6.2 — Who produces the `FederationReceipt`? When?

`AUDIT-federation.md` open question 3 lists three options:
- (a) After every turn — costs one BLS aggregation per turn.
- (b) Per block — batch the `body_hash`es.
- (c) Only on cross-federation hand-off — produce on-demand.

The demo only needs one `FederationReceipt` (over R2 at Step 3.8).
Option (c) is the cheapest and matches the demo. Production probably
wants (b). Pick (c) for the demo, document (b) as the steady-state
plan.

### 6.3 — How does the SDK know which federation_id to bind on the
*exercise* side?

Bob's cclerk at Step 3.2 builds a turn with
`Authorization::CapTpDelivered`. The cipherclerk's `compute_signing_message`
includes `local_federation_id` — which is F2 (Bob's home). Good. But
the **action signing** also binds federation_id (per
`turn/src/executor.rs:4445`'s `compute_signing_message`). Is the
action-level binding to F2 or to F1?

Recommendation: **F2** (Bob's home federation, where the turn
executes). F1's binding is captured by the `handoff_cert.introducer`
+ introducer signature inside `Authorization::CapTpDelivered`, which
the F2 executor verifies. Document this clearly in the
`CapTpDelivered` doc-comments.

### 6.4 — `FederationReceipt` vs `WitnessedReceipt` in the export bundle

§3.1 sketches `CrossFedReceiptBundle` as carrying both
`WitnessedReceipt`s (per-turn STARK proofs + witness) and
`FederationReceipt` (BLS aggregate over the body). Are both
required? Trade-off:
- `FederationReceipt` is small (~200 bytes), opaque to Charlie
  unless he has F2's committee descriptor — but that's the bilateral
  registration assumption.
- `WitnessedReceipt` is big (~30-100 KB) but lets Charlie
  *scope-2 replay* without trusting F2.

Recommendation: **both**, with `FederationReceipt` as the cheap
trust path (Charlie can early-exit on a verified
`FederationReceipt` if he chooses to trust F2's committee) and
`WitnessedReceipt` as the expensive replay path (Charlie can
recompute the trace from scratch if he doesn't). The
`dregg-verifier` subcommand offers both modes via a `--mode
trust|replay` flag.

### 6.5 — What does `dregg-verifier` actually do with `AttestedRoot.merkle_root`?

`AttestedRoot` carries `merkle_root` (the revocation-tree root,
primarily). For the Silver demo, the verifier *displays* the root but
does not check anything against it — the demo doesn't exercise
revocation. The check should be inert-but-present so the wiring is
honest. Document it; don't gate the demo on it.

### 6.6 — Cross-federation gossip vs CapTP

Today's wire layer talks CapTP between nodes (per
`wire/src/server.rs:2509-2607`). Federation-level metadata
(`AttestedRoot`, `FederationReceipt`, committee changes) also rides
the wire (per `wire/src/server.rs:2288-2960`). Are these the same
session? The same connection? `AUDIT-protocol-composition.md` Seam 8
suggests yes — wire is the unified transport — but the gossip layer
(`node/src/gossip.rs`) is intra-federation. Cross-federation gossip
("F1 broadcasts new attested roots to F2's subscribers") is not
yet a thing. For the demo, *pull* is sufficient (Step 4.0); *push*
is a future enhancement.

### 6.7 — How does Charlie know which `AttestedRoot` of F2 to verify against?

Step 6.0.vi has Charlie verify `AttestedRoot_F2@h=2`. But why h=2?
The bundle should include the AttestedRoot at the height *covering*
R2's block. If R2 finalized in block b2 at h=2, then
`AttestedRoot_F2@h=2` is the smallest root that includes R2. The
verifier should check `r2.height ≤ attested_root_F2.height` and the
`blocklace_finality.block_id == b2` (per the F3 fix). This is
straightforward; just document the invariant.

### 6.8 — `Authorization::CapTpDelivered` and the `effects_hash` truncation

`Authorization::CapTpDelivered.sender_signature` is over a message
that includes `effects` (`action.rs:244-262`). The signing message
postcard-encodes the effects. The receiver's `verify_authorization`
recomputes the same postcard-encoding. But the **EffectVm proof**
sees effects via the truncated `field_element_to_bb` path
(`AUDIT-protocol-composition.md` Seam 4 — 32→4 byte truncation).
The signature and the proof bind to different views of the same
effects. Is this OK?

Yes for Silver: the signature is the load-bearing binding (any
in-flight tampering invalidates it); the proof's truncation is a
*proof system* limitation, not a security gap (proof verifies the
truncated equivalence class, signature verifies the exact bytes).
The two together pin the effects down. Document; don't fix.

### 6.9 — When does the demo run? Local-only?

Production-shaped: two `dregg-node run` instances bind different
loopback ports. No QUIC NAT traversal needed; no TLS certificates
(devnet flag). The "out-of-band" channel is a file in shared
`state/`. Realistic enough; mirrors the two-AI demo's posture.

Future: a "two-machine" variant runs Node A and Node B on different
hosts. Requires TLS, requires real peering. Out of scope.

---

## §7. Estimated time-to-ship

Once the four in-flight lanes (A, B/landed, C/landed, D, F redux) plus
γ.2 (optional) land, how long until the Silver demo runs?

### 7.1 Inventory of remaining work

After all lanes land, the residue is:

| Item | Effort | Owner-ish |
|---|---|---|
| SDK cross-fed handoff builder (§5.2.1) | ~30 LOC | SDK |
| MCP `dregg_create_cross_fed_bearer_cap` tool (§5.2.2) | ~80 LOC | Node |
| Wire `validate_handoff` registry lookup (§5.2.3) | ~20 LOC | Wire |
| `CrossFedReceiptBundle` type + serde (§5.2.4) | ~80 LOC | Turn |
| `dregg-verifier verify-cross-fed-bundle` (§5.2.5) | ~150 LOC | Verifier |
| `dregg-node register-federation` CLI (§5.2.6) | ~40 LOC | Node |
| `dregg-node run --peer` polish (§5.2.7) | ~10 LOC | Node |
| Demo scripts (§5.2.8) | ~600 LOC Python/bash | Demo |
| README + expected.json (§4) | ~150 LOC | Demo |

Total: **~410 LOC Rust + ~750 LOC Python/bash + docs.**

### 7.2 Critical path

- Lane A (CapTP→Turn drainer) gates Steps 3.1, 3.3. **Hard prerequisite.**
- Lane D (federation+blocklace) gates Steps 0, 1.3, 1.4, 3.5, 3.8, 3.9.
  Federation_id derivation already lands (genesis.rs:133); the lift
  seam 6 + executor-signature-includes-federation_id are the remaining
  pieces. **Hard prerequisite.**
- Lane F redux gates Step 3.3 replay defense and 3.9 nullifier_set_root.
  Could ship demo without it by accepting cert-replay as a known gap;
  not recommended. **Soft prerequisite — recommended.**
- Lane B (wire) and C (cclerk) already landed per the user's note;
  green.
- γ.2 is **not** on the critical path. Silver is trust-based; the
  cross-cell algebraic binding is a Golden Vision concern. The
  bridge-boundary trust gradient is acknowledged but unfixed for
  Silver.

### 7.3 Honest week-scale estimate

Assuming the four lanes land cleanly (no integration surprises) and
one engineer working on this:

| Phase | Estimate |
|---|---|
| Lanes land + integrate | 1-2 weeks (depends on lane state at land-time) |
| §5.2 net-new Rust (~410 LOC) | 3-5 days |
| Demo scripts + assertions (~750 LOC) | 2-3 days |
| Negative tests (4 must-not-pass) | 1-2 days |
| Debug the integration (real cross-fed flows always surprise) | 3-5 days |
| Write up + commit | 1 day |

**Honest estimate: 3-4 weeks of one engineer post-lane-land.**

With two engineers in parallel (one on Rust, one on demo scripts):
**2-3 weeks.**

If lanes haven't fully landed yet at start: add 1-2 weeks of lane
shepherding.

### 7.4 What could shorten this

- **Skip γ.2.** Already planned; no change.
- **Skip lane F redux.** Accept cert-replay as a known caveat in the
  demo. Saves 0 net days (lane is in flight anyway); risks a hole in
  the demo's narrative.
- **Single-node committees (n=1).** Already planned in §4; saves
  threshold-aggregation complexity for the demo. Lane D produces real
  threshold aggregations for n>1 in production; the demo just
  exercises n=1.
- **Defer `CrossFedReceiptBundle` type to a Python wrapper.**
  The Python demo can stitch `WitnessedReceipt`s + `AttestedRoot`s
  + cert + `FederationReceipt` into a JSON object; the Rust type comes
  later. Saves ~80 LOC of Rust + serde + tests, adds ~30 LOC of
  Python.
- **Skip `dregg-verifier verify-cross-fed-bundle`** — do the cross-
  fed verification in `charlie.py` via Python crypto. Loses the
  "separate binary, separate crate deps" property the two-AI demo
  has. Not recommended.

### 7.5 What could lengthen this

- Hidden integration issues at the lane boundaries (e.g.
  `Authorization::CapTpDelivered` verification surfacing a `Turn::hash`
  binding gap from `AUDIT-turn-executor.md` P1-1 / P2-1).
- The `FederationReceipt` lift seam (6) discovers it needs to be
  blocklace-aware (block_height, block_hash come from where? the
  receipt is emitted *before* blocklace finalizes, so we'd need a
  two-phase lift). 1-2 weeks of design.
- The `AttestedRoot` `blocklace_finality` field landing requires AIR
  changes in `circuit/` to bind the new PI. If the destination
  federation tries to *prove* the binding (rather than just attest
  it via threshold), this is γ-shaped work.
- Cross-federation discovery surprises: the demo assumes
  pre-registered committees, but production needs first-contact. The
  demo can punt; if anyone asks "how does this scale to N
  federations", we admit it's bilateral by design.

### 7.6 Bottom line

**3-4 weeks from "all lanes land" to "demo runs green and a separate
binary verifier accepts the bundle."**

That is the honest week-scale estimate. It is consistent with the
two-AI demo timeline (which has been in scaffolding for ~2 months
and is currently at "scaffolding green; some blockers remain"
status — the silver-vision demo is structurally similar plus
cross-federation, so ~2-4x the demo-scripting work, ~1.5x the
Rust work).

If this estimate is to be wrong, the most likely direction is
**longer**, not shorter — the bilateral registration + cross-
federation wire flow has not been exercised end-to-end yet, and
integration surprises are guaranteed.

---

## §8. Coda — what Silver buying us, what it isn't

The Silver Vision demo is **integration-complete**. After it runs:

- We can claim: "dregg is a cross-federation distributed-objects
  system with bearer caps that survive wire transit, executor-signed
  receipts, BLS-threshold federation attestations, and a standalone
  scope-2 verifier."
- We **cannot** claim: "the joint state across both federations is
  algebraically provable." That's Golden.
- We **cannot** claim: "alice_cell's debit on F1 is verifiably tied
  to bob_cell's credit on F2." That's also Golden (γ.2 + bridge
  settlement).
- We **can** claim: "the executor on F2 produced a signed receipt
  that an independent process verified; the cert it consumed was
  signed by F1's committee; F1's committee attested the cert's
  origin in their finalized state; F2's committee attested the
  receipt's existence in their finalized state."

That's a real distributed-objects system with bilateral federation
trust. It's not a folded DAG of proofs — but the loops are closed,
the placeholders are gone, and every primitive is called by
something.

That is what Silver was coined to mean. The demo is the bench.

---

*~ EOF (~840 lines)*
