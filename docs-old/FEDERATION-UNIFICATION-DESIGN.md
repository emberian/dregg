# Federation Unification Design

A designer-level proposal for collapsing the four disjoint "federation"
concepts identified in `AUDIT-federation.md` into a single canonical type.

Read first: `AUDIT-federation.md` (the four concepts and where they live),
`AUDIT-morpheus-federation-blocklace.md` (which Morpheus paths are dead),
`AUDIT-blocklace-consensus.md` (live consensus substrate),
`AUDIT-distributed-semantics.md` (cross-fed CapTP trust model).

This document is read-only on code. It proposes a Rust shape, a migration
order, and the open questions a designer has to answer before any code
changes. Where I don't know, I say so.

---

## §1. What a Federation *is*

The canonical definition the unified type should embody:

> A **Federation** is a *committee of nodes* that (a) collectively run a
> blocklace, (b) attest shared ledger roots via BLS threshold signatures
> over a domain-separated message, and (c) ratify each other's Turns
> through a quorum certificate over a `FederationReceiptBody`.

Five things follow from that definition.

1. **A federation is identified by its committee.** Not by a random tag.
   Two federations with the same committee public keys at the same epoch
   *are the same federation*. The `federation_id` is `H(committee_pubkeys
   || epoch)` — the work Lane D (see `federation/src/identity.rs`) already
   landed via `derive_federation_id_with_epoch`. The id is a *commitment*,
   not a name.

2. **A federation has exactly one mode of operation: committee BFT.** The
   `FederationMode { Full, Solo }` flag is a quorum-arithmetic special case
   ("Solo" = "committee of one, threshold = 1"), not a runtime mode. A
   committee of one is degenerate-but-well-defined: the single member's
   signature *is* the quorum certificate. There is nothing additional to
   model.

3. **A federation owns a blocklace.** The blocklace is the substrate over
   which committee members produce blocks. The federation's `committee` is
   the set of `StrandId`s authorized to write to that blocklace. Today the
   blocklace's `GovernedReferenceGroup` (`blocklace/src/constitution.rs`)
   carries this set; the federation type should be the canonical owner and
   the blocklace should consult it via reference rather than holding a
   parallel copy.

4. **A federation produces two kinds of receipt.**
   - **`TurnReceipt`** (per turn, by the local executor) — locally
     produced, federation-tagged via `federation_id` in the receipt hash.
   - **`FederationReceipt`** (committee-attested, optional) — when the
     committee as a whole ratifies a state transition; this is the
     cross-federation hand-off currency (`AUDIT-federation.md` §5).

   The unified type doesn't have to *produce* either, but it has to provide
   the verifier-side context (`committee`, `committee_epoch`, `known_keys`,
   `threshold`) that both receipts require.

5. **A federation rotates.** Membership changes (`join`, `leave`, expel)
   produce a new `committee_epoch`, which produces a new `federation_id`.
   The *blocklace continuity* across epochs is what gives the federation
   its identity-over-time; the `federation_id` itself is per-epoch and
   does not preserve identity across rotations. (This is a deliberate
   choice; §7 explains the alternative.)

Things a Federation is **not**:

- Not the Morpheus `node::Federation` BFT simulator harness. That is dead
  code (per `AUDIT-morpheus-federation-blocklace.md`); it survives only
  because some tests still import it. The unified type explicitly does
  *not* model views, pacemakers, leaders, or any synchronous-BFT
  primitive — the blocklace owns ordering.
- Not a `FederationMode` flag. Solo collapses into "committee of one".
- Not a 16-byte random tag. The tag is derived from the committee.
- Not a cross-federation registry. That is a separate type
  (`KnownFederations`, see §5/§8).

---

## §2. The unified type

```rust
/// A federation: a committee of nodes attesting a blocklace.
///
/// The canonical owner of (federation_id, committee, blocklace, epoch).
/// Everywhere code currently passes around `(federation_id: [u8;32],
/// FederationCommittee, FederationMode, threshold)` as four parameters,
/// it should accept `&Federation` instead.
pub struct Federation {
    /// Sorted Ed25519 public keys of committee members. The substrate
    /// over which `federation_id` is derived. Sorting is enforced by
    /// the constructor; `members` is read-only after construction.
    members: Vec<PublicKey>,

    /// BLS threshold context for constant-size aggregate signatures
    /// (`hints` universe + KZG params). `None` for solo / pre-bootstrap
    /// federations that haven't run BLS setup yet; in that case the
    /// only available `ReceiptQc` flavor is `Votes` (Ed25519 fallback).
    bls_committee: Option<FederationCommittee>,

    /// Current committee epoch. Bumped by `apply_epoch_transition`.
    /// Part of the federation_id preimage; rotating it mints a fresh id.
    epoch: u64,

    /// Minimum unique signers (or BLS aggregate weight) required for a
    /// valid quorum certificate. Derived from `quorum_threshold(members.len())`
    /// by default; can be overridden for n=1 (Solo) or governance experiments.
    threshold: u32,

    /// Cached id = H(sorted(members) || epoch). Recomputed by `rebuild_id()`
    /// after any membership / epoch change; never set by callers directly.
    id: FederationId,

    /// The blocklace this federation produces. Federations and blocklaces
    /// are 1-to-1; the federation owns the blocklace's reference group
    /// set, the constitution, the equivocation policy. Stored as `Arc`
    /// so verifiers can hold a handle without owning the live writer.
    blocklace: Arc<Blocklace>,

    /// Local node's seat in this federation, if any. `None` for
    /// verifier-only federations (e.g. an entry in `KnownFederations`
    /// that we want to verify receipts from but are not a member of).
    /// Carries the local Ed25519 signing key and (optionally) the local
    /// BLS `MemberSecret`. Kept separate so a `Federation` value can be
    /// freely cloned across threads without leaking secrets.
    local_seat: Option<LocalSeat>,
}

/// The local node's membership in this federation.
pub struct LocalSeat {
    /// Index in `Federation::members` (after sorting).
    pub index: usize,
    /// Local Ed25519 signing key.
    pub signing_key: SigningKey,
    /// Local BLS member secret, present when `bls_committee.is_some()`.
    pub bls_secret: Option<MemberSecret>,
}

impl Federation {
    /// Construct from a committee. Sorts members internally; recomputes id.
    pub fn from_committee(
        members: Vec<PublicKey>,
        epoch: u64,
        threshold: u32,
        blocklace: Arc<Blocklace>,
        bls_committee: Option<FederationCommittee>,
        local_seat: Option<LocalSeat>,
    ) -> Self { /* ... */ }

    /// Solo: committee of one. Convenience constructor.
    pub fn solo(member: PublicKey, blocklace: Arc<Blocklace>, local_seat: LocalSeat) -> Self {
        Self::from_committee(vec![member], 0, 1, blocklace, None, Some(local_seat))
    }

    pub fn id(&self) -> FederationId { self.id }
    pub fn members(&self) -> &[PublicKey] { &self.members }
    pub fn epoch(&self) -> u64 { self.epoch }
    pub fn threshold(&self) -> u32 { self.threshold }
    pub fn bls_committee(&self) -> Option<&FederationCommittee> { self.bls_committee.as_ref() }
    pub fn blocklace(&self) -> &Arc<Blocklace> { &self.blocklace }
    pub fn local_seat(&self) -> Option<&LocalSeat> { self.local_seat.as_ref() }

    /// Are we operating in degenerate-committee mode?
    pub fn is_solo(&self) -> bool { self.members.len() == 1 }

    /// Verify a FederationReceipt against this federation's committee + epoch.
    /// Replaces the current `FederationReceipt::verify(committee, known_keys,
    /// threshold, expected_epoch)` four-parameter API.
    pub fn verify_receipt(&self, receipt: &FederationReceipt) -> bool {
        receipt.verify(
            self.bls_committee.as_ref(),
            &self.members,
            self.threshold as usize,
            self.epoch,
        )
    }

    /// Verify an AttestedRoot against this federation's committee.
    pub fn verify_attested_root(&self, root: &AttestedRoot) -> bool {
        root.is_valid(&self.members) // delegates to types/src/lib.rs:305
    }

    /// Produce the message an executor signs when producing a Turn in this
    /// federation. Today this is `TurnExecutor::compute_signing_message`
    /// which takes `&local_federation_id`; the moral equivalent on the
    /// unified type binds federation context explicitly.
    pub fn turn_signing_message(&self, action: &Action) -> Vec<u8> { /* ... */ }
}
```

Notes on the shape:

- **`id` is cached, not authoritative.** The authoritative source is
  `H(members || epoch)`. The cache exists so hot paths (CapTP routing
  keyed by `FederationId`) don't pay BLAKE3 per lookup. A debug-asserted
  invariant in `from_committee` (and a private `rebuild_id` for epoch
  transitions) keeps the cache honest.
- **`bls_committee` is optional.** Today `FederationCommittee::new`
  silently uses `OsRng` for KZG setup, meaning whichever node ran it
  knows the toxic waste (audit F5). The unified type *allows* a
  federation to exist without a BLS committee — solo nodes and pre-BLS
  bootstrap federations — falling back to Ed25519 vote aggregation
  (`ReceiptQc::Votes`). This is honest about the staging order: a
  federation can exist before its BLS ceremony has been run.
- **`blocklace: Arc<Blocklace>` is the controversial choice.** The
  alternative is for `Federation` to be a pure attestation context with
  no reference to the blocklace, and a separate `FederatedBlocklace`
  struct that holds both. I argue the embedded `Arc` is right: every
  federation produces *exactly one* blocklace, and every blocklace
  belongs to *exactly one* federation, so the 1-to-1 binding belongs in
  the type system. See open question §7.Q1.
- **`local_seat: Option<LocalSeat>`.** Cleanly separates "I am a member
  of this federation" from "I have this federation's committee
  registered for verification". The latter is the common case for
  cross-federation CapTP; it should not require holding a fake signing
  key. This is the unification of `local_federation_id` (today bolted
  onto `TurnExecutor`, executor.rs:523) with the federation registry.

---

## §3. What dies, what survives

| Today | Disposition | Where it goes |
| --- | --- | --- |
| `dregg_federation::node::Federation` (Morpheus simulator) | **DIES.** | Deleted with the Morpheus crate split (`AUDIT-federation.md` F9). The name `Federation` is freed for re-use. |
| `dregg_federation::threshold::FederationCommittee` | **SURVIVES, embedded.** | Becomes an optional field of the new `Federation`. Public API surface narrows: callers no longer construct it directly except in genesis / epoch transitions. |
| `dregg_federation::FederationMode { Full, Solo }` | **DIES.** | Replaced by `Federation::is_solo()` which is `members.len() == 1`. `effective_quorum_threshold(mode, n)` is replaced by the `threshold` field. `NullifierLog` and the rejoin protocol stay (they are solo-mode operational concerns), but they consume `&Federation` instead of `FederationMode`. |
| `federation_id: [u8; 32]` | **SURVIVES, becomes derived.** | Stays as the wire-level identifier and HashMap key (CapTP routing, blocklace addressing). But the canonical source of truth is `Federation::id() -> FederationId`, which is `H(members \|\| epoch)`. Direct construction of a `FederationId` from arbitrary bytes survives only on the deserialization path (a receipt arrives carrying one, we look it up in `KnownFederations`). |
| `local_federation_id: [u8; 32]` on `TurnExecutor` | **DIES.** | Replaced by `executor.federation: Arc<Federation>`. The executor takes a federation handle at construction; signing messages bind `federation.id()`. |
| `FederationReceipt::verify(committee, known_keys, threshold, expected_epoch)` | **SURVIVES with a wrapper.** | The raw four-parameter form stays for serde / wire-layer use, but a method `Federation::verify_receipt(&self, &FederationReceipt) -> bool` is the canonical caller-facing API. |
| `node::state::known_federation_keys: Vec<PublicKey>` | **DIES.** | Replaced by `node::state::federation: Arc<Federation>` (own federation) and `node::state::known_federations: KnownFederations` (others). The current pair of fields conflates "the keys I use for *my* federation's verification" with "the keys I happen to know about for any federation"; the unified shape separates them. |
| `wire::server::CapTpState::known_federations: Vec<FederationId>` | **SURVIVES, gains shape.** | Becomes `KnownFederations` (§8): id → committee mapping, not just a list of ids. The current `Vec<FederationId>` is sufficient for routing but cannot verify any cross-fed receipt without out-of-band committee lookup. |
| `dregg_federation::epoch::EpochConfig` | **MERGES INTO `Federation`.** | The `members`, `threshold`, `current_epoch` fields are exactly the unified type. The `EpochTransition` machinery survives as `Federation::apply_epoch_transition(&mut self, ...)`. `EpochHistory` survives as a sidecar (it is a verifiability concern, not a runtime-state concern). |
| `dregg_federation::checkpoint::Checkpoint` | **SURVIVES, gains binding.** | Today `Checkpoint::federation_members` is a snapshotted roster with no binding to a federation id. Becomes `Checkpoint::federation_id + epoch`, with members re-derivable by looking up `KnownFederations[id]`. Saves bytes; tightens binding. |

Net code change: roughly **+400 LOC** for the new `Federation` type and
its constructors, **−1500 LOC** for the Morpheus dead code (already
flagged by Lane D), **−~100 LOC** of small adapter cleanups around the
`(federation_id, FederationCommittee, FederationMode, threshold)`
tuple-passing sites. Net delta ≈ **−1200 LOC**, with the gain concentrated
in `federation/src/lib.rs` (a single `pub use Federation` instead of
five exports).

---

## §4. Composition with blocklace

This is the load-bearing seam. Today (`AUDIT-federation.md` §6) the
attested root carries `height: u64` and `timestamp: i64` with no
reference to a specific blocklace block — two attested roots at the same
`height` from different blocklace forks would be indistinguishable. Lane
D is fixing this with `blocklace_block_id` and `finality_round` on
`AttestedRoot` (already visible in `types/src/lib.rs:218–226`); the
unified `Federation` type should make this binding canonical end-to-end.

### Binding rules

1. **`Federation` owns exactly one `Blocklace`.** The 1-to-1 binding is
   enforced by the type (the `Arc<Blocklace>` field). A node that participates
   in two federations holds two `Federation` values, each pointing at its
   own blocklace.

2. **Every `AttestedRoot` produced via this federation MUST set
   `blocklace_block_id` and `finality_round` to a block in
   `Federation::blocklace()`.** This is enforced at construction time:
   ```rust
   impl Federation {
       pub fn build_attested_root(
           &self,
           merkle_root: [u8; 32],
           note_tree_root: Option<[u8; 32]>,
           nullifier_set_root: Option<[u8; 32]>,
           block_id: BlockId,
           ...
       ) -> Result<AttestedRootBuilder, FederationError> {
           let block = self.blocklace.get_block(&block_id)
               .ok_or(FederationError::UnknownBlock)?;
           let round = self.blocklace.finality_round_of(&block_id)
               .ok_or(FederationError::NotFinalized)?;
           Ok(AttestedRootBuilder::new(merkle_root, ..., block_id, round))
       }
   }
   ```
   The `Builder` then collects signatures from members; nothing in the
   public API allows constructing a free-floating `AttestedRoot` without
   going through the federation. (Today `AttestedRoot::new_legacy` exists
   for tests; we keep it `#[doc(hidden)]` and `#[cfg(test)]`-only.)

3. **`FederationReceipt::body` includes `block_id` and `block_height`
   from a single blocklace.** Today the body has `block_height` only
   (`federation/src/receipt.rs`, `FederationReceiptBody`). Adding
   `block_id: [u8; 32]` to the body closes the same fork-ambiguity gap
   at the receipt layer. The unified `Federation::build_federation_receipt`
   constructor enforces this.

4. **`AttestedRoot::signing_message` binds `federation_id`.** Currently
   it does not (`types/src/lib.rs:348`); it binds only roots, height,
   timestamp, block_id, round. The unified design adds
   `federation_id` to the signing message preimage so that a verifier
   who reconstructs the message can detect cross-federation attestation
   swaps without needing to consult any out-of-band state. This is the
   exact same fix as audit F2 applied to attested roots.

### What this kills

- The "consensus QC vs attested-root signing round" duplication
  (audit F10): with the unified type, both messages bind the same
  `(federation_id, block_id)` pair, and the same BLS aggregation can
  cover both with one set of partial signatures.
- The "checkpoint roster has no chain-of-trust" problem: a checkpoint
  references `federation_id + epoch`, and the receiver looks up
  `KnownFederations[id]` to obtain the verifying committee. No more
  bootstrap chicken-and-egg in the checkpoint itself; the chicken-and-egg
  moves to `KnownFederations` first-contact (§8).

---

## §5. Composition with CapTP

Cross-federation CapTP today (`AUDIT-distributed-semantics.md` and
`federation/tests/cross_federation_bridge_receipt.rs`) works as follows:
two federations A and B each construct their own `FederationCommittee`;
to verify a receipt B receives from A, B must already have A's committee
registered "out of band". The trust root is bilateral by design — there
is no on-chain federation registry, no light-client discovery.

The unified design keeps the bilateral-trust-root architecture but
gives it a single canonical home: **`KnownFederations`**.

```rust
pub struct KnownFederations {
    /// All federations we know about (including possibly our own).
    /// Keyed by id; an id collision is a hash collision and panics in debug.
    entries: HashMap<FederationId, Arc<Federation>>,
}

impl KnownFederations {
    /// Register a federation we want to verify receipts from.
    /// The federation must have its `local_seat = None` unless we are a
    /// member of it.
    pub fn register(&mut self, fed: Arc<Federation>) -> Result<(), KnownFedError> { /* ... */ }

    /// Look up a federation by id. Returns None if we don't know about it.
    pub fn get(&self, id: &FederationId) -> Option<&Arc<Federation>>;

    /// Verify a `FederationReceipt` by looking up its federation_id.
    /// Replaces the pattern "caller manually picks the committee".
    pub fn verify_receipt(&self, receipt: &FederationReceipt) -> bool {
        match self.get(&FederationId(receipt.federation_id)) {
            Some(fed) => fed.verify_receipt(receipt),
            None => false, // unknown federation == cannot verify
        }
    }

    /// Verify any `AttestedRoot`, looking up the federation by the
    /// id bound in the signing message (post-§4 binding).
    pub fn verify_attested_root(&self, root: &AttestedRoot, fed_id: &FederationId) -> bool;
}
```

The CapTP layer (`wire/src/server.rs:907`) replaces its
`known_federations: Vec<FederationId>` with `Arc<RwLock<KnownFederations>>`.
The current bare-list form was sufficient for *routing* (knowing which
peer addresses are valid) but cannot *verify* any cross-federation
receipt without separately stored committees; the unified shape gives
both at once.

### First contact

The unification does not solve the first-contact bootstrap problem. A
federation that has never seen another federation has no way to verify
that federation's receipts without an out-of-band trust step (a
hardcoded genesis registry, a manual `KnownFederations::register`, a
TOFU on first handshake). The unified type makes the trust step
*explicit* — `register` requires the caller to provide a full
`Federation` value, which means the caller must have obtained the
committee public keys through some trusted channel — but doesn't reduce
the size of the manual trust footprint. See §7.Q5.

---

## §6. Migration path

The migration is staged so the test suite stays green at every step. No
"big bang" rewrite. Steps are sequenced; each is reviewable on its own.

### Step 1: introduce the unified type alongside the existing four (~250 LOC)

- New file `federation/src/federation.rs` with the `Federation` struct
  exactly as proposed in §2, plus constructors and the `id() / members()
  / verify_receipt()` accessors. No code outside the federation crate
  uses it yet.
- Add `Federation::from_legacy(committee, mode, threshold, federation_id,
  blocklace)` — a wide adapter constructor that takes today's four
  parameters and packages them up. This is the bridge used by every
  call site during migration.
- Re-export `pub use federation::Federation` from `federation/src/lib.rs`.

**Tests:** new unit tests for the unified type's constructors and
`is_solo()` arithmetic. Existing tests untouched.

### Step 2: introduce `KnownFederations` (~120 LOC)

- New file `federation/src/registry.rs`.
- `KnownFederations::register / get / verify_receipt /
  verify_attested_root` as in §5.
- Wire into `node::state::State` as a new `known_federations:
  KnownFederations` field, populated at startup from `genesis.json`
  (the local federation) plus any operator-configured peer federations.
- The existing `state::known_federation_keys: Vec<PublicKey>` is **not
  yet removed** — it co-exists with the registry-derived form.

**Tests:** registry round-trip, duplicate-id detection, lookup-miss
returns `false` on verify.

### Step 3: rewrite executor + receipt sites to consume the unified type (~300 LOC, mechanical)

- `TurnExecutor::new(...)` gains an `Arc<Federation>` parameter and
  drops `local_federation_id: [u8; 32]`. Internal users of
  `self.local_federation_id` become `self.federation.id().0`.
- `TurnExecutor::compute_signing_message(action, &federation_id)` becomes
  `TurnExecutor::compute_signing_message(action, &self.federation)` and
  internally pulls the id.
- `TurnExecutor::canonical_executor_signed_message` (turn/src/turn.rs:503)
  starts including `federation_id` in its signing preimage — this is
  audit F2's fix, landed naturally because the executor now has a
  `&Federation` and including its id is one line. This is a wire-format
  break; we bump the domain separator from `executor-receipt-sig-v1`
  to `executor-receipt-sig-v2`.
- `FederationReceipt::verify` keeps its raw four-parameter form (for
  serde/wire callers) but every in-tree caller switches to
  `KnownFederations::verify_receipt(&receipt)`. ~10 call sites,
  mechanical.

**Tests:** the entire receipt test suite must still pass. The signing
message bump produces test fixture rewrites (`receipt.rs:233–377`,
`cross_federation_bridge_receipt.rs`) — annoying but mechanical.

### Step 4: rewrite genesis + blocklace_sync to construct `Federation` (~150 LOC)

- `node::genesis::run_genesis` produces a `genesis.json` that includes a
  serialized `Federation` (members + epoch + threshold + blocklace
  genesis block id), instead of separate `validators / federation_id /
  threshold / committee_epoch` fields.
- `node::blocklace_sync::initialize` constructs an `Arc<Federation>` from
  `genesis.json` and threads it through `TurnExecutor::new`.
- `node::state::known_federation_keys` is **removed**; callers consume
  `state.federation.members()` instead. ~30 call sites, mechanical.

**Tests:** the integration suite (`integration_test.rs`,
`devnet_smoke_test.rs`) must come up cleanly. Genesis file format
change is a devnet break; existing devnet directories must be
re-generated. Production has no devnet so this is purely a developer-
experience tax.

### Step 5: collapse `FederationMode` and `effective_quorum_threshold` (~80 LOC)

- `FederationMode { Full, Solo }` is deleted from `solo.rs`. Callers that
  switch on it (mostly logging and CLI rendering) switch on
  `federation.is_solo()` instead.
- `effective_quorum_threshold(mode, n)` is deleted; replaced by
  `federation.threshold()`.
- `NullifierLog` and the solo rejoin protocol are kept; they consume
  `&Federation` instead of `FederationMode`. The "solo-mode-only"
  branches become "if federation.is_solo()" branches.
- The CLI `--federation-mode {full|solo}` flag is removed. Solo is
  detected from the committee size in `genesis.json`.

**Tests:** the solo-mode tests in `solo.rs` and the
`solo_rejoin_protocol.rs` integration test must still pass.

### Step 6: delete the Morpheus simulator (~1500 LOC removed)

- `federation/src/node.rs` (the dead Morpheus paths — `Federation`,
  `FederationNode`, `ConsensusOrchestrator`, `ConsensusState`,
  `PendingStateRoots`, `ReconfigurationProposal`, `ReconfigurationVotes`)
  is deleted.
- The crate name `Federation` is now free for the unified type
  (which has been sitting in `federation::federation::Federation`
  through steps 1–5); the re-export is updated to point at the new type.
- Any test that imported the simulator harness either moves to using the
  real blocklace (`test_blocklace.rs`-style fixtures) or is deleted as
  redundant.

**Tests:** if step 6 breaks a test, that test was testing the simulator,
not the federation. The fix is to delete it or rewrite it against the
real substrate.

### Step 7: wire `Federation::verify_attested_root` into the live path (~120 LOC)

- `node::blocklace_sync` calls `state.federation.verify_attested_root(&root)`
  instead of inline `root.is_valid(&known_keys)`.
- `wire::server::CapTpState::known_federations: Vec<FederationId>` is
  replaced by `Arc<RwLock<KnownFederations>>`; cross-fed receipt
  validation goes through `known_feds.verify_receipt(&receipt)`.

**Tests:** the cross-federation bridge test
(`federation/tests/cross_federation_bridge_receipt.rs`) is rewritten to
use `KnownFederations::register` on both sides instead of the manual
committee-passing it does today (lines 31–34 of that test).

### Step 8: the F2 signing-message tightening (~20 LOC)

- `AttestedRoot::signing_message` is bumped to `dregg-attested-root-v3`
  and includes `federation_id` in the preimage. Last wire-format change
  in the migration.

**Tests:** all signing fixtures need a one-line update.

### Total

Roughly **+700 LOC** added (unified type, registry, wiring),
**−1500 LOC** removed (Morpheus), **~600 LOC** mechanically rewritten
(executor parameter, state, blocklace_sync, genesis, ~40 call sites
across the crates). Net diff: ~**−800 LOC**, with a much sharper type.

### Sequencing constraints

Steps 1–2 are independent and can land in parallel. Steps 3–5 must be
sequential (each makes the next a clean diff). Step 6 must come after
steps 1–5 (it requires the simulator to have no in-tree consumers).
Step 7 must come after steps 2 and 3. Step 8 is independent of
everything else and can land first or last; I'd land it last because
it's the smallest piece of behavior change with the largest fixture
impact.

---

## §7. Open questions for the designer

These are the hard calls the design doesn't unilaterally make. Each one
could go either way, and the resolution should be made before code lands.

### Q1. Does `Federation` own the blocklace, or just reference it?

The design in §2 has `blocklace: Arc<Blocklace>` as a field of
`Federation`. The alternative is for `Federation` to be a pure
attestation context with no blocklace reference, and a separate
`FederatedBlocklace { federation: Arc<Federation>, blocklace: Arc<Blocklace> }`
type for the live writer.

**Argument for embedding:** the 1-to-1 binding is real (a federation
produces exactly one blocklace), the type system should reflect it, and
otherwise every call site that has a `Federation` and wants to verify
"is this block in this federation's blocklace?" needs to pass both
parameters.

**Argument against:** `Blocklace` is a mutable, growing structure; a
verifier-only `Federation` (no `local_seat`) doesn't need to hold the
blocklace at all. Carrying the `Arc` even for verifier-only federations
is wasteful, and forces the blocklace's API to be `Sync`-friendly in
ways it might not want to be.

I lean toward embedding, but this is the single biggest decision in the
design and deserves a designer's call.

### Q2. Membership ops at the type level — `join`, `leave`, `expel`?

§1 says the federation rotates via `apply_epoch_transition`. Should
that method live on `Federation`, or on a separate `FederationGovernance`
controller that mutates a `Federation`?

**Argument for on-type:** `Federation::apply_epoch_transition(&mut self,
transition: EpochTransition)` is a clean API; the federation contains
all the state needed to apply.

**Argument for separate controller:** apply-time signature verification
requires consulting the *previous epoch's* committee, which is on the
`Federation` itself — circular if you're mutating in place. Also,
epoch transitions touch the blocklace (a new committee writes the
transition block) so they're not pure federation operations.

I'd put the verification helper on `Federation` (it's pure) and the
state mutation on a `FederationController { fed: Arc<RwLock<Federation>>,
... }` that orchestrates the blocklace-block-write + committee-rebuild
+ epoch-bump as one transaction.

### Q3. Does `Federation` carry the local BLS keyshare?

§2 puts it in `LocalSeat::bls_secret: Option<MemberSecret>`. Alternative:
keep BLS secrets in a separate `KeyManager` that the executor holds, and
`Federation` is purely about public material.

**Argument for embedding:** colocates "everything you need to sign as
this federation member" in one place. Constructors enforce that
`bls_secret.is_some()` implies `bls_committee.is_some()`.

**Argument against:** `Federation` becomes secret-bearing, which means
it can't be freely cloned across threads / logged / serialized. Secrets
ought to live in a key-management layer with explicit zeroize and audit.

I'd embed for the v1 migration (the secrets are already scattered around
in `MemberSecret` instances passed by reference today; embedding doesn't
make them less secure) and split out into a `KeyManager` later if a
real HSM integration appears. v1 doesn't ship to anyone holding real
keys; the simplification is worth it.

### Q4. Identity-over-time across epoch rotations

§1.5 says the `federation_id` is per-epoch — rotating membership produces
a new id. This is the right *cryptographic* choice (an old-epoch receipt
must not pass under a new-epoch committee), but it makes the federation
"the same federation" only by convention.

An alternative is a two-level id: a long-lived `federation_chain_id`
(set at genesis, never changes) plus a per-epoch `committee_id`. CapTP
routing and HashMap keys could use either. Receipts would bind both.

I lean toward keeping the single per-epoch id and letting "this is the
same federation over time" be a property of the blocklace continuity
(the blocklace's genesis block is the same across all epochs of one
federation). But this is genuinely a designer's call — the two-level id
is more honest about the conceptual model.

### Q5. First contact / bootstrap trust for `KnownFederations`

§5 doesn't solve the first-contact problem. Options:

- **Genesis hardcoded registry.** Every node ships with a hardcoded set
  of known federation public keys. Sufficient for federation-of-trust
  topologies (e.g. a handful of named partner federations).
- **DNS-style discovery.** Federation ids resolve via DNS TXT records to
  committee key bundles. Cheap-but-trust-DNS.
- **TOFU on first handshake.** First time we see a federation, we ask
  the operator to confirm a fingerprint. SSH-style.
- **On-chain registry (in some root federation).** A "registry of
  registries" federation that publishes everyone else's committees.
  Recursive trust root problem.

The unified `KnownFederations` type doesn't have to pick — it just
provides the storage. But somebody has to pick before we can do
unattended cross-federation CapTP, and the right answer probably
depends on the deployment model (cooperatives of named federations vs
permissionless mesh).

### Q6. What about the `dregg-blocklace::GovernedReferenceGroup` overlap?

The blocklace crate has its own notion of "who is allowed to write to
this blocklace" (`GovernedReferenceGroup`,
`blocklace/src/constitution.rs`). This overlaps substantially with
`Federation::members`. Today they are parallel data structures; nothing
enforces that `governed_reference_group.members ==
federation.members()`.

Option A: `Federation::members()` is *the* source, and
`GovernedReferenceGroup` becomes a thin view over `&Federation`.

Option B: `GovernedReferenceGroup` stays as the lower-layer construct
(blocklace doesn't depend on federation), and `Federation` is *defined
in terms of* its `GovernedReferenceGroup` (`Federation::members()` is a
delegating accessor).

I lean toward Option B for layering hygiene (blocklace shouldn't depend
on federation), with a documented invariant that constructors enforce.
But a designer should look at the actual import graph and decide.

### Q7. Where does the `BLS-to-Ed25519` correspondence live?

A federation member has *both* an Ed25519 key (for action signing,
TurnReceipt executor signatures, AttestedRoot quorum sigs) *and* a BLS
key (for FederationReceipt threshold aggregation). Today these are two
disjoint data structures with no enforced correspondence:
`Federation::members: Vec<PublicKey>` is Ed25519,
`Federation::bls_committee` carries the BLS public keys, and nothing
checks that "member at index i" has the BLS key at index i.

Should we (a) carry a single `Vec<MemberEntry>` where each `MemberEntry`
binds Ed25519 + BLS by position, or (b) carry the two separately and
just trust the indexing convention?

I'd carry them separately for v1 (option b) — it matches the wire
format and the current code, and the indexing convention is already
the actual invariant. v2 could promote to a unified `MemberEntry`
once we have a story for key rotation that updates both keys atomically.

### Q8. Solo→Full auto-promotion

`AUDIT-federation.md` §9 notes there's no automatic demotion to solo when
below threshold, and the rejoin protocol in `solo.rs` is commented but
not wired into a controller. The unified type makes "solo" not a mode
but a committee size — but it doesn't speak to *dynamic* committee
resizing.

I'd say: the unified `Federation` is **immutable per epoch**.
"Demotion" is just "the next epoch transition reduces members to 1".
"Promotion" is the inverse. Wiring this to be automatic (rather than
operator-initiated) is a separate controller-layer concern outside the
unified type. The `solo.rs` rejoin protocol stays as a controller-layer
script.

---

## §8. The `KnownFederations` registry

This is the type the cross-federation CapTP layer has been wanting
since the bridge integration test was written. Today the registry-shaped
hole is filled by:

- `wire::server::CapTpState::known_federations: Vec<FederationId>` — id
  list, no committee material.
- `node::state::known_federation_keys: Vec<PublicKey>` — *one
  federation's* keys, no federation_id binding.
- Out-of-band registration in tests
  (`cross_federation_bridge_receipt.rs` lines 31–34 — "Both federations
  register each other's committees out of band").

The unified shape:

```rust
pub struct KnownFederations {
    entries: HashMap<FederationId, Arc<Federation>>,
    /// Persistence backend; `None` for in-memory-only (tests).
    /// In production, persisted to the data directory alongside the
    /// blocklace WAL.
    persist: Option<Arc<dyn KnownFedsStore>>,
}

pub trait KnownFedsStore: Send + Sync {
    fn load(&self) -> Result<Vec<Federation>, StoreError>;
    fn append(&self, fed: &Federation) -> Result<(), StoreError>;
    fn remove(&self, id: &FederationId) -> Result<(), StoreError>;
}
```

### Where it lives

- **One per node.** Held in `node::state::State::known_federations:
  Arc<RwLock<KnownFederations>>`.
- **Threaded into CapTP.** `wire::server::CapTpState` gets a clone of
  the same `Arc<RwLock<KnownFederations>>` (replacing its
  `Vec<FederationId>`).
- **Threaded into the blocklace verifier.** When the blocklace
  fast-syncs from a peer (`blocklace_sync`), it consults
  `known_federations` to verify any cross-federation attestations
  embedded in the sync stream.

### Persistence

- Stored at `$DATA_DIR/known_federations/`. One JSON-or-CBOR file per
  federation (named by `federation_id.hex().json`), containing the
  serialized `Federation` (members + epoch + threshold; the BLS
  committee is reconstructed lazily from the members + a shared KZG
  setup, *or* serialized verbatim if we want offline verification).
- Append-only by convention. Removing a federation requires an
  operator action; we don't auto-expire.

### Sync

- **Not auto-synced in v1.** Operator registers each federation manually
  (CLI: `dregg node add-federation <federation.json>`).
- **v2 candidate:** federations gossip their own committee public keys
  signed by the current committee, so a new node coming up can pull
  its operator-confirmed peers' committees from any of them. This is
  the "DKIM-for-federations" pattern.

### Self-registration

The node's own federation is also registered in `KnownFederations`
(with `local_seat = Some(...)`). This makes "verify a receipt from any
federation" a single lookup, with no special case for "my own".
`node::state::State::federation()` is a sugar method that returns
`known_federations.get_local().unwrap()`.

### Invariants

- `entries[id].id() == id` for all `id` — checked on `register`.
- At most one entry has `local_seat = Some(...)` — checked on
  `register`. (A node is a member of at most one federation at a time;
  this is a current architectural assumption and is worth preserving.)
- An entry can be replaced by a higher-epoch entry with the same
  `federation_chain_id` (if we adopt §7.Q4 option B) — supports
  observing epoch rotations of registered peer federations.

### Open question — see §7.Q5

The trust story for *first registration* is unsolved by this type. The
type just provides the storage and lookup; the trust is at the
operator-action / DNS / TOFU layer above.

---

## Summary

| What | Today | After |
| --- | --- | --- |
| **Identity** | 16 random bytes from `getrandom` (legacy; Lane D fixing) | `H(sorted(members) \|\| epoch)`, derived |
| **Committee** | `FederationCommittee` (BLS context only) | Field of `Federation`; Ed25519 members are the primary identity, BLS is optional auxiliary |
| **Mode** | `FederationMode { Full, Solo }` enum | Deleted; `is_solo()` derives from `members.len() == 1` |
| **Type** | Four concepts in four files (`node::Federation`, `threshold::FederationCommittee`, `FederationMode`, raw `federation_id`) | One `Federation` struct in `federation/src/federation.rs` |
| **Receipt verification** | `verify(committee, known_keys, threshold, expected_epoch)` four-parameter | `federation.verify_receipt(&receipt)` or `known_feds.verify_receipt(&receipt)` |
| **Cross-fed registry** | `Vec<FederationId>` for routing + parallel out-of-band committee storage | `KnownFederations: HashMap<FederationId, Arc<Federation>>` |
| **Blocklace binding** | `AttestedRoot.height` only; no block_id; Lane D adding it | `Federation` owns `Arc<Blocklace>`; constructors enforce binding |
| **Morpheus simulator** | 1500 LOC of dead code re-exported as `Federation` | Deleted |

The net effect: "federation" becomes one word that names one type that
owns one blocklace and produces one kind of attestation; first contact
between federations goes through one registry; verification goes
through one method. The audit's F1, F2, F4, F7 close as natural
consequences of the unification rather than as separate patches. F3 is
made canonical (already partly landed). F8, F9, F10 remain as
controller-layer / cleanup concerns that the type unification doesn't
address but no longer obscures.
