# AUDIT: pyana federation

What it is, what's real, and where the seams creak.

Read-only. Read `AUDIT-morpheus-federation-blocklace.md` first — it draws the
boundary between the **dead Morpheus BFT simulator** in
`pyana_federation::{node, transport}` and the **live primitives** in
`pyana_federation::{solo, threshold, threshold_decrypt, checkpoint, revocation,
epoch, receipt, types}`. This audit is about the *live* primitives.

Files inspected (absolute paths):

- `/Users/ember/dev/breadstuffs/federation/Cargo.toml`
- `/Users/ember/dev/breadstuffs/federation/src/lib.rs`
- `/Users/ember/dev/breadstuffs/federation/src/types.rs`
- `/Users/ember/dev/breadstuffs/federation/src/threshold.rs`
- `/Users/ember/dev/breadstuffs/federation/src/receipt.rs`
- `/Users/ember/dev/breadstuffs/federation/src/checkpoint.rs`
- `/Users/ember/dev/breadstuffs/federation/src/epoch.rs`
- `/Users/ember/dev/breadstuffs/federation/src/solo.rs`
- `/Users/ember/dev/breadstuffs/federation/src/node.rs` (lines 820–895 — live AttestedRoot construction)
- `/Users/ember/dev/breadstuffs/federation/tests/cross_federation_bridge_receipt.rs`
- `/Users/ember/dev/breadstuffs/types/src/lib.rs` (lines 187–399 — canonical `AttestedRoot`, `ThresholdQC`)
- `/Users/ember/dev/breadstuffs/turn/src/turn.rs` (lines 70–512 — `Turn`, `TurnReceipt`, signing messages)
- `/Users/ember/dev/breadstuffs/turn/src/executor.rs` (lines 521, 998, 4417–4505 — `local_federation_id`, signing messages)
- `/Users/ember/dev/breadstuffs/turn/src/composer.rs` (line 158, 196 — partial signing also binds federation_id)
- `/Users/ember/dev/breadstuffs/node/src/genesis.rs` (lines 30–171 — where federation_id is born)
- `/Users/ember/dev/breadstuffs/node/src/blocklace_sync.rs:1197` — sets `local_federation_id` on executor
- `/Users/ember/dev/breadstuffs/hints/src/lib.rs` (BLS12-381 confirmation), `/Users/ember/dev/breadstuffs/hints/src/snark/mod.rs:27`

---

## 1. What *is* a federation, in code?

There is **no single `Federation` type that means the canonical thing**. The
word is overloaded across at least four disjoint definitions.

| Name                                              | Where                                            | What it is                                              |
| ------------------------------------------------- | ------------------------------------------------ | ------------------------------------------------------- |
| `pyana_federation::node::Federation`              | `federation/src/node.rs:900–`                    | Morpheus simulator harness. Dead path (see prior audit) |
| `pyana_federation::threshold::FederationCommittee`| `federation/src/threshold.rs:37`                 | Live BLS threshold context (members + KZG universe)     |
| `pyana_federation::FederationMode { Full, Solo }` | `federation/src/solo.rs:34`                      | Runtime mode flag                                       |
| `federation_id: [u8; 32]`                         | `turn::TurnReceipt`, `federation::FederationReceipt`, `wallet`, `executor` | Opaque tag identifying *which* federation |

The closest thing to a canonical "this is a federation" is the **pair**
`(federation_id: [u8;32], FederationCommittee)`. But — and this is the
load-bearing seam — *nothing in the code derives one from the other.* See §10
finding F1.

The genesis path (`node/src/genesis.rs:53–55`) creates the `federation_id` like
this:

```rust
let mut federation_id_bytes = [0u8; 16];
getrandom::fill(&mut federation_id_bytes).expect("getrandom failed");
let federation_id = hex_encode(&federation_id_bytes);
```

A 16-byte random string, hex-encoded. It is **not** a hash of the committee
public keys, the threshold, or any structural commitment. Anyone running the
genesis tool can mint any number of "federations" with identical committees,
and any committee can re-key without changing its `federation_id`. The receipt
binding (`federation_id` → committee) is sustained only by out-of-band
configuration.

---

## 2. Membership — joining, leaving, expulsion, the roster

### Live representation

- **Genesis roster**: `GenesisConfig` (`node/src/genesis.rs:30–37`) — JSON
  on disk, containing `validators: Vec<{name, public_key, xmss_root}>`. Loaded
  at boot. **Not on-chain.**
- **Epoch roster (proposed)**: `federation/src/epoch.rs:30–56`. `EpochConfig`
  carries `members: Vec<ValidatorInfo>`, `threshold: usize`, `current_epoch`.
  Membership change pipeline:
  1. `PendingMembershipChanges::request_join` / `request_leave`
     (lines 504–528) — in-memory queue.
  2. `propose_epoch_transition` (line 199) — proposes an `EpochTransition`
     bundling adds/removes + a *placeholder* QC attestation (line 245:
     `votes: Vec::new()`).
  3. Old-epoch validators sign `EpochTransition::signing_message`
     (line 86 — `pyana-epoch-transition-v1 || from_epoch || to_epoch ||
     new_threshold || added... || removed...`).
  4. `verify_epoch_transition` (line 314) checks the QC's *count* ≥
     `old_config.threshold` AND each vote's Ed25519 signature against the
     listed `voter_id`.
  5. `apply_epoch_transition` (line 260) mutates the config in place.
- **Checkpoint roster (attested)**: `Checkpoint` (`federation/src/checkpoint.rs:24`)
  carries `federation_members: Vec<PublicKey>` and a QC. This is the only
  *attested* roster, but it is bound only to the checkpoint's block height,
  not to a published, replayable transcript.

### Joining

`PendingMembershipChanges::request_join` accepts any `ValidatorInfo` — no
threshold approval is required to be added to the **pending** list. Approval
happens implicitly when the epoch-boundary QC over the `EpochTransition` is
collected. There is no per-join admission process beyond "the proposer
included you".

### Leaving

Symmetric: `request_leave(pubkey)` is purely advisory; takes effect at the
next epoch boundary when the transition QC carries it.

### Expulsion

**Not in the federation crate at all.** Equivocation / Byzantine-fault
detection lives in `pyana-blocklace`: `blocklace/src/constitution.rs:11`
documents "Auto-eviction: equivocation proofs immediately remove the
equivocator." `federation/src/` has zero references to `slash`,
`equivocation`, or `expel`. So expulsion is owned by the blocklace
constitution, and it is the blocklace's job to push that change into the
next epoch — but `epoch.rs` has no API consuming a blocklace-emitted
equivocation proof. The connection is conceptual, not wired.

### Is the roster on-chain?

No. The roster is:

- in `genesis.json` at startup,
- in process memory thereafter (`EpochConfig`, `EpochHistory`),
- *snapshotted* into a `Checkpoint` periodically (default every 1000 blocks).

The checkpoint is the closest thing to a published roster, but verifiers must
already have a `FederationCommittee` to verify the checkpoint's QC, which is
a chicken-and-egg situation for first-contact. See F3.

---

## 3. BLS threshold signatures — what they really are

### Library

`hints` (workspace path `/Users/ember/dev/breadstuffs/hints/`). Real BLS12-381
on `ark_bls12_381::Bls12_381` (`hints/src/snark/mod.rs:27`). Pairings are real
Ate pairings (`Curve::pairing(...)`, lines 114, 188, 229). Signatures are
hash-to-G2 (`utils::hash_to_g2`), aggregation is summation in G2Projective.
This is **a genuine weighted-threshold BLS aggregate signature scheme** with
KZG-based polynomial commitments for the "weight" / "approved-set"
attestation. The output of `committee.aggregate(...)` is one constant-size
group element + a tiny KZG proof, regardless of committee size. Verified by
`test_constant_size_regardless_of_committee` (`federation/src/threshold.rs:482`).

### Keygen — DKG or trusted dealer?

**Neither — each party generates its BLS keypair locally.**
`MemberSecret::generate` (`federation/src/threshold.rs:305`) calls
`hints::generate_keypair`, which is just `sk ← F::rand(rng); pk ← g^sk`. There
is no distributed key generation, no Shamir splitting, no proactive
refresh. The "threshold" property comes entirely from the *signature
aggregation* layer (you can't produce an aggregate with weight ≥ T without
≥ T parties signing), not from the *key* layer.

This is fine for what it is, but verbiage in `lib.rs:34` ("**Threshold QC**
(preferred): A single constant-size BLS aggregate signature") makes it sound
fancier. It is BLS aggregate-with-weight-attestation, with regular per-party
keys. No party holds a share of a master key.

### KZG trusted setup

Two paths:

- **`new_with_eth_setup`** (`threshold.rs:181`) — uses
  `hints::setup_eth` which deserializes the Ethereum KZG ceremony's powers
  of tau. Capped at 64-degree (so ≤ 63 federation members). This is the
  prod-grade audit path.
- **`new` / `new_with_rng`** (`threshold.rs:143–163`) — `GlobalData::new(...,
  &mut OsRng)`. The party that ran setup **knows the toxic waste** for the
  duration of the process and can in principle forge KZG openings. In a
  multi-process / multi-node federation, somebody has to ship the KZG params
  to everyone else; whoever generated them retains the trapdoor. This is
  *not* called out as a security caveat in the docstring (line 138–142).

### Threshold

`threshold: u64` is passed in by the caller, stored as a field element
(`F::from(threshold)`), and embedded *inside the aggregate signature*
(`ThresholdQC.signature.threshold`). Deserialization re-extracts it
(`from_bytes` line 348–353). So a QC self-asserts what threshold it was
aggregated against; verification trusts the committee object's local
threshold via `committee.verify(...)` → `verify_aggregate` (verifier-side
threshold check happens in the KZG SNARK, see `hints/src/lib.rs:188`).

### Padding & the "dummy" key

`from_global_data` (`threshold.rs:202–246`) requires hints to have exactly
`domain_size − 1` parties where `domain_size = next_pow2(n+1)`. For e.g.
n=4 members, that's 7 parties — 3 of them padded with `BlsSecretKey::dummy()`
and weight 0. The dummy key is `F::from(-1i64)` (`hints/src/lib.rs:29`),
**a publicly known scalar shared across all federations using this path**.
Weight 0 should make the dummies non-counting, but having a known-key party
in every universe is structurally awkward and would deserve a clear
"why this is safe" comment. None exists.

---

## 4. AttestedRoot — what does it actually attest?

Canonical definition lives in `types/src/lib.rs:199–218`, re-exported by
federation. Fields:

```rust
AttestedRoot {
    merkle_root: [u8; 32],          // primary: revocation-tree Merkle root
    note_tree_root: Option<[u8; 32]>,
    nullifier_set_root: Option<[u8; 32]>,
    height: u64,                     // block height
    timestamp: i64,
    quorum_signatures: Vec<(PublicKey, Signature)>,  // Ed25519 fallback
    threshold_qc: Option<ThresholdQC>,                // BLS aggregate (opaque)
    threshold: usize,
}
```

Signed message (`signing_message`, `types/src/lib.rs:308`):

```
"pyana-attested-root-v1" || merkle_root
                         || (0x00 | 0x01 || note_tree_root)
                         || (0x00 | 0x01 || nullifier_set_root)
                         || height_le || timestamp_le
```

So an `AttestedRoot` attests to **a tuple of three Merkle roots** (revocation
tree, note commitment tree, nullifier set) **at a specific block height and
wall-clock time**. It does **not** include:

- the federation_id,
- the committee descriptor / `committee_epoch`,
- any reference to a specific blocklace block / DAG position,
- the pre-state from which the roots were derived.

Notable subtlety: `federation/src/node.rs:854–866` (`update_attested_root`)
mints the `AttestedRoot` *separately* from the consensus QC: the QC was over
the **vote_message** `pyana-federation-vote-v1 || block_hash || height ||
view`, but the `AttestedRoot` signatures must be over the
`pyana-attested-root-v1` message. The comment (lines 832–845) explicitly
says callers must collect a *fresh* set of signatures over the attested-root
signing message — they cannot reuse the consensus votes. This is
implementation-correct, but it means an `AttestedRoot` is a **second,
parallel attestation** that costs an extra signing round on top of consensus.

---

## 5. FederationReceipt vs TurnReceipt

These are **disjoint types** at different layers.

### `pyana_turn::TurnReceipt` (`turn/src/turn.rs:337–409`)

Produced **per turn** by the local executor. Bound fields (in `receipt_hash`,
lines 414–479):

```
"pyana-receipt-v2" || turn_hash || forest_hash || pre_state_hash
                  || post_state_hash || timestamp || effects_hash
                  || computrons_used || action_count || agent
                  || federation_id      // <-- bound!
                  || previous_receipt_hash
                  || routing_directives + derivation_records + ...
```

Optional `executor_signature` over a *narrower* message
(`canonical_executor_signed_message`, line 503):

```
"executor-receipt-sig-v1:" || turn_hash || pre_state_hash
                          || post_state_hash || timestamp_le
```

**`federation_id` is NOT in this narrower signing message.** It is in
`receipt_hash`, which the signature does not directly cover. So the executor
signature is over `(turn_hash, pre, post, ts)` — a verifier that only checks
the executor signature cannot rule out a different `federation_id` being
asserted in the receipt body. The mitigation, per the comment, is that
verifiers should reconstruct `receipt_hash` and check its consistency
elsewhere; but the *signature* alone is federation-agnostic. See F2.

### `pyana_federation::FederationReceipt` (`federation/src/receipt.rs:122–227`)

Produced when the **federation as a whole** wants to attest "we, the
committee, ratify the (turn, pre→post) state transition for this agent".
Body:

```rust
FederationReceiptBody {
    turn_hash, block_height, block_hash, agent, nonce,
    pre_state_hash, post_state_hash, effects_hash,
    previous_receipt_hash,
}
```

`body_hash` (line 67) is BLAKE3-derive-key("pyana-fed-receipt-body-v1", ...).
The QC (BLS `ThresholdQC` or Ed25519 fallback) signs **`body_hash`**.

Critical: `FederationReceipt` carries `federation_id` and `committee_epoch`
as outer fields (lines 126, 129) but these are **NOT inside `body_hash`**.
Only `body` is hashed; `federation_id` and `committee_epoch` are
adjacent-but-unsigned tags. An attacker who can re-route a receipt can edit
the `federation_id` field with no effect on the QC's verifiability —
because the verifier uses the *runtime-passed* `committee` to verify, the
caller is solely responsible for picking the right committee given those
tags. There is no mechanism in `verify` (line 186) to enforce
`federation_id ↔ committee` consistency. See F1.

### When is each produced?

- `TurnReceipt`: on every turn, by the local executor, regardless of mode.
- `FederationReceipt`: not produced *automatically* anywhere in the live
  node path. The struct exists, the BLS aggregation path works, the
  cross-federation bridge integration test (§7) builds them by hand. But
  `node/src/blocklace_sync.rs`, `node/src/api.rs`, `wire/src/server.rs`
  do not call `FederationReceipt::with_threshold_qc` or
  `with_vote_signatures`. The plumbing wiring `FederationReceipt` into the
  live turn-commit pipeline is **not present.** It is currently a
  primitives-only feature with a unit-test cross-federation bridge
  scenario.

---

## 6. Composition with blocklace

**The federation's attested root is NOT tied to a specific blocklace
position.** Evidence:

- `grep -rn "AttestedRoot\|FederationReceipt" blocklace/src/` → 0 matches.
- `grep -rn "blocklace_height\|blocklace.*attest" federation/src/` → 0 matches.
- `AttestedRoot` carries `height: u64` and `timestamp: i64`, but there is
  no field tying it to a specific blocklace block hash, DAG round, or
  finality position.
- `Checkpoint` carries `height: u64` and a `QuorumCertificate`, but the QC
  is over the checkpoint's *content_hash*, which itself does not include
  any blocklace block reference (`checkpoint.rs:97–111`).

This is the dominant smell. The federation crate was clearly *designed*
around a synchronous BFT (Morpheus) where `height` was a tight block
sequence the federation itself produced. With blocklace as the live
consensus, `height: u64` and the blocklace's DAG positions are different
totally-ordered sequences, and nothing in the live code threads the
blocklace's notion of finality / block_id into the federation's
attestation. Two `AttestedRoot`s with the same `height` could in principle
come from different blocklace forks, and the verifier would have no way to
tell.

The `RevocationBlock` type (`types.rs:58`) does have `block_hash` /
`prev_hash`, but that's the *federation's internal* notion of a block —
the Morpheus simulator's — not the blocklace block. They are decoupled.

---

## 7. Composition with Turn signing — is T6 closed?

T6 (`EXECUTOR-HONESTY-AUDIT.md:128`): "replay a turn from another federation".

**Action-layer signing: closed.**
`TurnExecutor::compute_signing_message` (`turn/src/executor.rs:4445`):

```rust
hasher.update(b"pyana-action-v1:");
hasher.update(federation_id);
// ... action fields
```

and `compute_partial_signing_message` (line 4499) symmetrically binds
`federation_id` for multi-signer partial-sig flows. The wallet at
`sdk/src/wallet.rs:2406, 2445` takes `federation_id` and calls these. So an
action signed for federation A cannot be replayed inside federation B's
executor — assuming both executors have correct `local_federation_id`s.

**Receipt-layer signing: PARTIALLY closed.**
`TurnReceipt::receipt_hash` (line 414) DOES include `federation_id` — so the
receipt's content-addressed identity is federation-bound.
`canonical_executor_signed_message` (line 503) does NOT include
`federation_id`. So a `TurnReceipt` is federation-bound by its hash but the
executor's optional signature is over a `(turn_hash, pre, post, ts)` quartet
that is federation-agnostic. The same executor signature could be lifted
onto a receipt with a different `federation_id` — without invalidating the
signature — as long as `turn_hash` and the state-pair match.

For the executor signature to actually catch a federation-rewrite, a
verifier must independently recompute `receipt_hash` and check that it is
consistent with the carried `federation_id` field. As long as that is done,
T6 stays closed. It is a *brittle* closure — better to add `federation_id`
into `canonical_executor_signed_message`. See F2.

`FederationReceipt` similarly has `federation_id` adjacent-but-unsigned
(§5).

---

## 8. Cross-federation interaction

There is one real cross-federation scenario in the code, exercised by
`federation/tests/cross_federation_bridge_receipt.rs`. It works as follows:

- Two federations A and B each construct their own `FederationCommittee`
  with `generate_test_committee(4, threshold=4)`.
- A locks a note, signs the `BridgeReceiptEnvelope::Locked` body_hash with
  A's BLS threshold → `ThresholdQC`. Sends to B.
- B verifies A's QC against **A's committee** (which B has registered
  out-of-band: "Both federations register each other's committees out of
  band (the trust root in this layer — bilateral by design)" — test
  doc line 31–34).
- B builds a `Witnessed` envelope, signs with B's committee, returns.
- A finalizes. Phase log on both sides converges.

The bridge envelope (`pyana_cell::note_bridge::BridgeReceiptEnvelope`)
carries `src_federation`, `dst_federation`, and
`previous_phase_receipt_hash`. The phase log enforces monotone advancement
(test `cross_federation_replay_rejected_after_finalize`).

So cross-federation interaction is *possible* and *tested*, but its trust
model is explicitly **bilateral out-of-band committee registration**. There
is no on-chain federation registry, no light-client discovery, no
recursive proof of "fed B finalized this and here's a self-contained
proof". B must already have A's committee bytes locally.

---

## 9. Federation faults

### Liveness — threshold of nodes goes offline

The crate has **no live mechanism** for this. `solo::FederationMode::Solo`
exists (`solo.rs:34`) as a degraded-mode flag, but the transition Full →
Solo is not automatic — it's a CLI/config choice at boot. There is no code
that detects "we are below threshold" and demotes. The blocklace's
finality_tests have liveness scenarios; the federation crate does not.

### Safety — committee signs a bad root

Nothing detects this. `AttestedRoot::is_valid` is structural; the
BLS-verified path (`verify_attested_root_with_committee`) just confirms
"≥ threshold members signed this root over its canonical message". If
threshold members collude to attest a wrong `merkle_root`, the federation
has no recourse — there is no fork-choice rule, no audit trail diffing
against blocklace-finalized state, no slashing. The only thing that
detects this is the blocklace's own equivocation detection on a
*different* layer (block proposer equivocation), which does not see the
attested-root attestation at all.

### Slashing

None. Zero matches for `slash`, `penalty`, `bond` in `federation/src/`.

### Fork choice

None in `federation/`. Blocklace handles fork choice via tau ordering on
the DAG; federation does not have its own.

---

## 10. Test coverage

In the federation crate:

- `threshold.rs:404–530` — 6 BLS threshold unit tests (sign+verify,
  below-threshold rejection, wrong-message rejection, serialization
  round-trip, constant size, all-sign).
- `receipt.rs:233–377` — 6 receipt tests (body hash domain-separated,
  threshold receipt verifies / fails below threshold / fails on wrong
  body, votes receipt verifies / fails on unknown signer / rejects
  duplicate signer).
- `checkpoint.rs:257–390` — 5 checkpoint tests.
- `epoch.rs:584–866` — 11 epoch tests including signature verification.
- `tests/cross_federation_bridge_receipt.rs` — 2 tests (happy-path roundtrip,
  late-refund replay rejection after finalize).

Adversarial tests *present*:

- `test_threshold_not_met` — aggregation must fail below threshold. Tests
  the *aggregation* refuses; does not test "what if a malicious aggregator
  bypasses aggregation and forges". The hints crate itself is the trust
  root for that.
- `test_threshold_wrong_message_fails_verification` — wrong-message
  rejection.
- `threshold_receipt_fails_on_wrong_body` — receipt over body A doesn't
  satisfy body B.
- `votes_receipt_rejects_duplicate_signer` — Ed25519 duplicate-key
  replay.
- `cross_federation_replay_rejected_after_finalize` — phase log monotone
  property.

Adversarial tests *missing*:

- **Cross-federation receipt swap.** Take a valid `FederationReceipt` from
  federation A, mutate `federation_id` to B's, leave QC and `committee_epoch`
  intact. Does any callable verifier reject it? Today `FederationReceipt::
  verify` doesn't, because the caller picks the committee. There should be
  a higher-layer test asserting "if we registered A's committee under
  fed_id A and B's under fed_id B, a receipt tagged A but signed by B's
  committee is rejected when looked up via fed_id". The plumbing for
  that lookup doesn't exist (F1), so this test cannot be written yet —
  which is itself the finding.
- **Threshold-edge n=1, 2.** `generate_test_committee(1, 1)` and
  `(2, 2)` aren't covered; hints' power-of-2 domain may behave oddly at
  the edge.
- **Epoch-transition signature forgery.** `verify_epoch_transition` checks
  signatures, but no test attempts to forge an attestation by inserting a
  bogus signer; the existing `test_epoch_transition_requires_attestation`
  only tests empty vs proper.
- **`AttestedRoot` truncated/forged threshold_qc.**
  `types/src/lib.rs:566` has a `truncated_qc` case, but only at the
  structural-validity level — no test attempts to deserialize the
  truncated bytes against a `FederationCommittee` and observe the failure
  through the full path.
- **Old committee_epoch reuse.** Stale receipts: a receipt signed by
  epoch-N committee, presented in epoch-N+1 after key rotation, must
  be rejected. No test, because `committee_epoch` is currently not
  enforced anywhere (F4).
- **Solo→Full rejoin conflict.** `solo.rs` documents a rejoin protocol but
  has no test for "two solo nodes sequenced conflicting nullifier logs
  during a partition".

---

## Findings (terse)

- **F1 — Federation identity is unbound.** `federation_id` is 16 random
  bytes from genesis (`node/src/genesis.rs:53`). It is not a commitment
  to the committee. `FederationReceipt::verify` takes `committee` as a
  parameter and never checks `committee ↔ federation_id`. There is no
  `CommitteeRegistry: HashMap<(federation_id, committee_epoch),
  FederationCommittee>` and no API on `FederationCommittee` to compute
  its canonical id. **Fix**: derive `federation_id = BLAKE3("pyana-fed-id-v1"
  || serialize(committee.universe.verifier_key) || committee_epoch)` and
  enforce on verify.

- **F2 — Executor signature is federation-agnostic.**
  `Turn::canonical_executor_signed_message` omits `federation_id`. The
  field is in `receipt_hash` but not in the message the executor signs.
  Closure relies on the verifier independently recomputing
  `receipt_hash`. **Fix**: include `federation_id` (and
  `previous_receipt_hash` and `agent`) in the canonical message.

- **F3 — AttestedRoot is decoupled from blocklace.** The live consensus
  is blocklace (Cordial Miners DAG, tau ordering); the federation's
  attested root carries only `height: u64` and `timestamp`, with no
  reference to a specific blocklace block hash, DAG round, or finality
  certificate. Two attested roots at the same `height` from different
  blocklace forks would be indistinguishable to a verifier. **Fix**: add
  `blocklace_finality: { block_id, round, tau_index }` to AttestedRoot
  and bind it in `signing_message`.

- **F4 — committee_epoch is decorative.** Present on
  `FederationReceipt` (line 129), serialized, but never consulted in
  verification. No epoch→committee lookup. Old-epoch receipts can be
  presented under a new-epoch committee with no automatic rejection.

- **F5 — KZG setup trust is undocumented.** `FederationCommittee::new`
  silently uses `OsRng` for KZG params, meaning whichever node ran
  `new()` knows the toxic waste. Other nodes must trust them or re-do
  setup. Production should mandate `new_with_eth_setup`. Docstring
  doesn't warn.

- **F6 — Dummy padding key is publicly known.** `BlsSecretKey::dummy()`
  is `F::from(-1)`. Every committee with `num_members + 1` not a
  power of 2 includes this known-key party at weight 0. Should at
  minimum carry an `# Invariants` doc on `from_global_data` explaining
  why weight-0 dummies are safe (because the SNARK proof binds weights,
  and a dummy contribution adds 0 to the aggregated weight). Today
  there is no such note.

- **F7 — `FederationReceipt` is unwired.** The type exists, BLS path
  works, cross-federation test passes — but no live code path
  (`node`, `blocklace_sync`, `wire`, `api`) produces a
  `FederationReceipt` after a turn. It's a beautifully-tested
  primitives library nobody currently calls in production.

- **F8 — No fault response inside `federation/`.** Equivocation,
  partition, malicious-attestation handling all live in blocklace
  or not at all. The federation has no `slash`, no `expel`-on-
  attestation-fork, no automated demotion to solo on partition. The
  Morpheus dead-code paths had pacemakers and view-change; the live
  primitives do not.

- **F9 — Crate naming is misleading.** Per the prior morpheus audit,
  the crate should be split into `pyana-federation-utils` (live) and
  the Morpheus simulator (dead/test-only). Today `lib.rs:60` still
  re-exports `ConsensusOrchestrator`, `Federation`, etc., which gives
  the impression these are part of the live federation API. They are
  not on the live node path.

- **F10 — `update_attested_root` requires a second signing round.**
  Because `vote_message` (consensus QC) and
  `AttestedRoot::signing_message` are different domain-separated
  messages, the node has to collect a *fresh* set of signatures over
  the attested-root preimage after consensus finalizes
  (`node.rs:832–845`). Doable but doubles the signing rounds per
  block. Could be unified by making `vote_message` cover the
  attested-root preimage directly, or by using BLS aggregation across
  both messages at once.

---

## Design verdict

The federation **primitives** (`threshold`, `receipt`, `epoch`,
`checkpoint`, `solo`) are individually well-shaped: real BLS12-381
weighted-threshold aggregation via `hints`, constant-size QCs,
domain-separated signing messages, duplicate-signer rejection in the
Ed25519 fallback, and explicit weight-0 padding so the BLS universe size
is decoupled from real-member count. The **system-level federation**, by
contrast, is a half-wired construct: `federation_id` is a random 16-byte
tag rather than a commitment to the committee, `committee_epoch` is
serialized but never consulted, the attested-root carries no blocklace
finality binding, `FederationReceipt` is unused in production, and fault
response is delegated to a sibling crate (blocklace) with no plumbing.
This crate is mid-refactor: the Morpheus simulator died, blocklace took
the consensus seat, and the primitives that survived have not yet been
re-bound to the new substrate. As primitives, B+; as a coherent federation
abstraction, C — it needs F1, F3, F4, F7 done before "federation" means a
single composable thing in this codebase.

---

## Open questions for designer

1. **Should `federation_id` be a commitment to the committee?** If so, who
   computes it canonically and where does it live? (Proposed:
   `FederationCommittee::canonical_id()` → BLAKE3 of verifier key.)

2. **Is the attested-root supposed to be blocklace-bound?** If yes, what's
   the binding — block_id, finality certificate, tau-index? If no, what
   prevents fork-attestation ambiguity?

3. **When should `FederationReceipt` actually get produced?** After every
   turn (cost: BLS aggregation per turn)? Per block (batch the
   `body_hash`es)? Only on cross-federation hand-off?

4. **Is `committee_epoch` meant to gate verification?** If yes, where does
   the `(federation_id, committee_epoch) → FederationCommittee` registry
   live, and how is it bootstrapped at first contact?

5. **Who owns expulsion?** Blocklace's constitution detects equivocation
   and emits proofs; epoch.rs has no consumer for those proofs. Should
   `apply_epoch_transition` accept an "expulsion certificate" instead of
   relying on the next proposer to remember to drop the equivocator?

6. **Why two signing rounds per block** (vote_message AND
   attested-root signing_message)? Can we collapse them by making the
   consensus vote cover the attested-root preimage directly?

7. **Production KZG path.** Should `FederationCommittee::new` be marked
   `#[cfg(test)]` and only `new_with_eth_setup` shipped in release? The
   current API silently uses an OS-RNG ceremony that nobody else can
   verify.

8. **Solo→Full transition.** The `FederationMode` flag is set at boot.
   Should there be an automatic demote-to-solo when below threshold,
   and a re-promotion protocol? The rejoin protocol in `solo.rs` is
   commented but not wired into a controller.

9. **Is the Morpheus-shaped `node::Federation` test harness still
   needed?** It's 1000+ lines of dead simulator. Deleting it would
   eliminate the "is this the real federation?" confusion that
   prompted this audit.

10. **Should `FederationCommittee` carry its own `committee_epoch`
    field**, so that `committee.verify(qc, msg)` can be checked against
    the `(receipt.committee_epoch, committee.epoch)` pair internally,
    rather than the caller manually selecting the right committee?
