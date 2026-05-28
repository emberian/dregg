# STARBRIDGE-APPS-PLAN — `starbridge-apps/` as the post-`apps/` userspace

**Date:** 2026-05-24. **Status:** design only. **Author lane:** design
(no code changes outside this document). **Companion docs:**
`APPS-AS-USERSPACE-AUDIT.md` (the 16-primitive Tier-1/2/3 ranking),
`SDK-REVIEW.md` (the as-is SDK surface), `DREGG-FLAWS-FROM-APPS.md`
(bug catalogue), `site/STUDIO.md` (the runtime substrate the site
agent is cooking), `apps/README.md` (the "BE WARY" disclaimer on the
current `apps/`).

This document proposes the `starbridge-apps/` directory as the
successor to `apps/`, and lays out:

- what the in-browser **Starbridge** environment actually is today
  (site, wasm, extension cclerk);
- which apps survive the transition;
- what each surviving app looks like when rebuilt from
  **dregg-native primitives only** — Effects, CellPrograms,
  Authorizations, Capabilities, Factories, DSL caveats — rather than
  the use-case-first style that drove `apps/`;
- the cargo-workspace shape of `starbridge-apps/`;
- the order to build them in;
- and the questions only the designer can answer.

The brief's hard rule remains in force: **the answer is never
`Effect::FooApp`.** When an app wants a domain Effect, the missing
primitive is the *generic* one (Caveat, StateConstraint,
Authorization, Factory) it would compose from.

---

## §1. Discovery — where Starbridge currently lives

### 1.1 The Starbridge surface in the repo

Search for `starbridge` (case-insensitive) returns five real
hits, all in `site/`:

| File | Role |
|---|---|
| `site/STUDIO.md` (348 LoC) | Design doc. Names three Studio surfaces: Playground / Explorer / **Starbridge**. Defines the `Runtime` interface, URI scheme, time cursor, snapshot import/export. |
| `site/src/starbridge.html` (88 LoC) | Page chrome. Topbar (runtime picker, URI input, Go/Snapshot, cursor scrubber). Three-pane body: object tree, inspector, raw-JSON. Mounts `<dregg-app>` and bootstraps `_includes/studio/starbridge.js`. |
| `site/src/_includes/studio/starbridge.js` (411 LoC) | Page-specific orchestration. Loads `runtimes.js` registry, instantiates the active runtime, drives the cursor, mounts `<dregg-${kind}>` inspectors via URI dispatch. Exposes `window.__starbridge` for tests. |
| `site/src/_includes/studio/runtime-in-memory.js` | Owns the wasm handle from `/pkg/dregg_wasm.js`, exposes the `Runtime` contract. |
| `site/src/_includes/studio/{runtimes.js, context.js, inspectors.js, uri.js, ...}` | Inspector registry, URI parser, runtime kinds enumeration, `<dregg-app>` context provider. |

**State of play (paraphrasing `STUDIO.md`):**

> All three Studio surfaces are the same IDE, fed by different data
> sources. Playground = `InMemoryRuntime` (wasm, owner authority).
> Explorer = `RemoteRuntime` (live federation node, read-only).
> Starbridge = **user-selected** — including write authority to a
> live node, in-browser branching, time-cursor scrubbing, fault
> injection, debugger.

Starbridge is therefore a *power-user* viewport, not a fresh stack.
The page-chrome is already shipped; the runtime substrate is
*partially* shipped (in-memory works, remote is a stub, recorded
deferred). The inspectors registry exists; only `<dregg-cell>` is
wired end-to-end (per STUDIO.md §9, Phase 0).

### 1.2 The wasm in-browser node

`wasm/` builds a `pkg/dregg_wasm.js` ESM module that the site loads
at `/pkg/`. Source layout (4886 LoC):

| File | LoC | Role |
|---|---|---|
| `wasm/src/lib.rs` | 1914 | `#[wasm_bindgen]` exports for crypto primitives: token mint/attenuate/verify, STARK prove/verify, predicate proofs, Merkle membership/non-membership, Datalog, Poseidon, Schnorr, committed thresholds, intent hashing, `blake3_hash`. |
| `wasm/src/runtime.rs` | 487 | `DreggRuntime` — full in-browser distributed-system simulation. Real `dregg_sdk::AgentCipherclerk`, real `dregg_cell::Ledger`, real `dregg_turn::TurnExecutor`, `NullifierSet`, `IntentPool`, `RevocationChannelSet`, `ConditionalTurn`s, multi-agent. **No mocks.** All cryptographic paths exercise the canonical sdk implementations. (Federation is **not** in wasm — `dregg_federation` pulls tokio/crossbeam and doesn't cross-compile; inspectors show "awaiting wasm32 federation support".) |
| `wasm/src/bindings.rs` | 1260 | Index-based wasm handles around `DreggRuntime` (so JS can hold opaque `runtime_id` handles instead of crossing the wasm boundary with rich types). |
| `wasm/src/privacy.rs` | 1225 | Stealth-meta-address / private-transfer / anonymous-presentation bindings. |

**What this gives a starbridge-app:**

- A real-but-in-memory dregg node, sitting in browser linear memory,
  driving the same code-path that native CLIs use. `create_agent`,
  `create_cell`, `execute_turn`, `advance_height`, `post_intent`,
  `match_intents`, `register_conditional`, `submit_conditional`.
- A `serializeHistory() → Uint8Array` snapshot path (per
  STUDIO.md §8) — postcard-encoded, round-trippable into a
  `dregg-node` instance on disk.
- All STARK proving and verification (Plonky3 BabyBear) compiled to
  wasm32. Real proofs, real signatures, real Pedersen commitments —
  not JS reimplementations.

What it doesn't give: federation gossip, CapTP wire transport
(QUIC), persistent storage. Browsers can't open QUIC sockets, so any
live federation interaction must go through a *relayed* runtime —
proposed in STUDIO.md as a future `RelayedRuntime` (out of scope of
this plan).

### 1.3 The extension cclerk surface

`extension/` is the `dregg` browser extension. Public API surface
(`extension/src/page.ts`, the `window.dregg` object frozen in the
page context after content-script injection):

```ts
interface DreggAPI {
  // identity & permissioning
  isConnected(); canAuthorize(req); authorize(req); provision(token);
  on(event, cb); off(event, cb);

  // signing & turns
  signTurn(turnSpec); queryBalance();

  // intents & private value
  postIntent(matchSpec, opts); postEncryptedIntent(matchSpec, opts);
  getStealthAddress(); privateTransfer(amount, asset, stealthMeta);

  // capabilities
  createBearerCap(targetCellHex, action, expiry);
  verifyBearerCap(...);
  shareCapability(cellId); acceptCapability(uri);
  createHandoff(cellId, recipientPk);

  // factories  ← THE EXTENSION ALREADY EXPOSES FACTORY CREATION
  createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance);
  verifyProvenance(cellVkHex, knownFactoryVks);

  // cells & sovereignty
  makeCellSovereign(cellIdHex); peerExchange(receiverCellHex, amount);

  // proofs
  composeProofs(proofs[], mode); // and/or/chain/aggregate

  // namespace / mount
  mountService(path, opts); discoverServices(tags); resolvePath(path);

  // content storage
  storageWrite(data); storageRead(hash); storageQuota();

  // node config & federation
  getNodeConfig(); setNodeConfig(cfg);
  federationStatus();

  // governance
  proposeRoutes(routes); voteOnProposal(proposalId, approve);
}
```

Events: `ready`, `authorization`, `revoked`, `stealthNoteReceived`,
`privateTransfer`, `intentFulfilled`, `privacyModeChanged`.

**This is the integration surface starbridge-apps consume.** Three
things to notice:

1. **`createFromFactory` is *already* a first-class cclerk method.**
   The extension already speaks the factory vocabulary
   (`factoryVk`, `paramHash`, `verifyProvenance`). Starbridge-apps
   should lean on it — see §5.
2. **`signTurn` takes a `turnSpec`, not a `Turn`.** The cclerk
   *constructs* and signs; the page never holds raw private keys.
   This forces a clean separation: app code builds `turnSpec`
   descriptors; cclerk does authorization + signing + submission.
3. **`postIntent` / `postEncryptedIntent` are cclerk primitives, not
   app primitives.** Intent matching is part of the platform; apps
   produce intent shapes.

The site also ships an extension-download page at
`site/extension/index.html` (with `dregg-cipherclerk.zip`) — installation
is one click for Starbridge users.

### 1.4 What "Starbridge for an app" means

Pulling it together — a starbridge-app is a web surface that:

1. Loads `/pkg/dregg_wasm.js` (the in-browser node) for local
   simulation / preview / time-travel.
2. Talks to `window.dregg` (the extension cclerk) for real
   identity, signing, capability brokerage, intent posting.
3. Optionally talks to a live federation node via the Studio's
   `RemoteRuntime` for production data.
4. Renders state via the Studio's URI-addressable inspector system
   (`<dregg-cell uri="dregg://cell/..." />`) — *the same components*
   the Playground and Explorer use.
5. Has its own page chrome and domain UI, but **its inspectors,
   runtime context, signal-based reactivity, and debugger are all
   shared with the Studio**.

So a "starbridge-app" is not a separate stack. It's a *page* (or set
of pages) that mounts the Studio runtime and contributes
**domain-specific inspectors and turn-builder presets** to the shared
inspector registry.

---

## §2. Migration ledger

Apps retained, with current state and target shape. "Userspace-gap
blockers" reference the Tier rankings in
`APPS-AS-USERSPACE-AUDIT.md` §7.1.

| App | Path today | What it does | Current primitives used | `dregg`-native composition | Userspace-gap blockers |
|---|---|---|---|---|---|
| **governed-namespace** | `apps/governed-namespace/` | DAO-governed routing table + capability-secure file storage; propose/vote/amend routes via constitutional threshold; mount caps at paths; discover by tags; resolve to sturdy refs. | DFA route classifier, content-addressed storage, `dregg_storage::namespace_mount`, threshold voting (in-app); HTTP/JSON. *Some* real cell/turn use. | (a) DAO = sovereign cell whose state holds `(route_table_root, voter_root, proposal_root)`. (b) Each route is a `Capability` mounted on the namespace cell with `Caveat::PathPrefix` attenuation. (c) Proposals are sub-cells produced by a *governance factory* (`FactoryDescriptor` constrains: outcome can only be Accept/Reject; threshold = N). (d) Vote turns: `Effect::SetField(proposal.votes[i] = 1)` gated by a `Caveat::VoterRoll` capability. (e) Amendment: atomic turn `Effect::SetField(route_table_root = new_root)` requiring threshold-witness across N caveat-discharges. (f) Files = nameless content-addressed blob (`Effect::BindBlob`, G23) on the namespace cell. | Tier 1 #1 (transition constraint for monotone proposal-id counter); Tier 1 #3 (`AuthenticatedRequest<C>`); Tier 1 #4 (federation clock for proposal expiry); Tier 2 #7 (`dregg-credentials` for voter eligibility); Tier 3 #15 (`Effect::BindBlob`). |
| **gallery (= auction)** | `apps/gallery/` | NFT-style art auctions: commit-reveal bids, royalty splits, anti-sniping, provenance chain, private-Vickrey (4195 LoC dead). | Imports `Effect::Transfer / CreateEscrow / ReleaseEscrow / SetField`; constructs but doesn't always execute. STARK match-AIR is freestanding. | (a) Per-artwork sovereign cell, state = `(artist_commit, creation_height, owner_cap_id, provenance_root, blob_hash)`. (b) `Effect::BindBlob` for the image. (c) Per-auction cell from an **auction factory** (`FactoryDescriptor` fixes the program VK = "commit-reveal auction state machine"; param hash bakes in commit/reveal windows). (d) Bids are per-bid escrow cells with `EscrowCondition::PredicateSatisfied(auction.winner == me)`. (e) Settlement = single atomic multi-cell turn: `ReleaseEscrow + RevokeCapability + GrantCapability + SetField(provenance_root)`. (f) Royalty splits = `StateConstraint::SumEqualsAcross` over the settlement turn. (g) Anti-sniping = `StateConstraint::FieldDeltaInRange` on the deadline. | Tier 1 #1 (transition constraints — anti-sniping, royalty conservation); Tier 1 #2 (`PredicateSatisfied` impl); Tier 1 #3 (auth extractor); Tier 1 #5 (`Effect::ClaimSlot` for unique-ownership); Tier 2 #6 (paired escrow); Tier 3 #11 (subscription/streaming for live bid feed); Tier 3 #14 (coordinator key for private Vickrey). |
| **bounty-board** | `apps/bounty-board/` | Privacy-preserving work marketplace; anonymous claim/deliver/pay; ZK qualification proofs; STARK delivery proof; sybil resistance via stake. | `app-framework::ConditionalTurn`, `EscrowManager`; `dregg_intent::matcher::HeldCapability`; `bridge::present` (qualification proofs). | (a) Per-bounty sovereign cell, state = `(reward_note_root, qualification_spec_hash, deadline, claim_commitment_root, status)`. (b) Claim = `Effect::CreateNote (bond)` + `Effect::QueueEnqueue (claim_queue, worker_commitment)`. (c) Delivery = STARK delivery proof presented in a `Effect::ReleaseEscrow { condition: ProofPresented { circuit_id, expected_pi } }` (G3 fix). (d) Payment = private note minted to worker's stealth address (`getStealthAddress`); spent via nullifier later. (e) Reputation = `bridge::present::BridgePresentationProof` over the worker's IVC receipt chain ("I have ≥N completed bounties"). | Tier 1 #2 (`PredicateSatisfied`); Tier 1 #4 (clock for deadlines); Tier 1 #5 (`Effect::ClaimSlot` for nullifier-based dedup); Tier 2 #7 (`dregg-credentials` for IVC standing); Tier 3 #13 (attester registry for qualification issuers). |
| **nameservice** | `apps/nameservice/` | Hierarchical names, rent, sub-delegation, dispute, cross-fed resolution. **The most dregg-native-shaped of the retained apps; in `apps/` it is effectively decorative (uses zero real primitives).** | Effectively *nothing* real; HTTP server over `BTreeMap`. | (a) Per-name sovereign cell from a **name factory** (`FactoryDescriptor` constrains the program VK = rent state machine; param hash bakes the namespace prefix). (b) Rent = `Effect::Transfer + StateConstraint::FieldDelta(expiry, +epoch_len)`. (c) Sub-delegation = `Caveat::ResourcePrefix { name_prefix }` attenuation on the owner cap. (d) Dispute = paired escrow (challenger stake vs. owner stake), resolved by a `EscrowCondition::PredicateSatisfied` on a `dispute_resolution` cell. (e) Reverse-index = a federation-attested `CommittedMap<TargetUri, NameId>` cell. (f) Cross-fed = CapTP `EnlivenRef + Send(method="resolve", args=[name])` into the remote registry's sturdy ref. | Tier 1 #1 (FieldDelta for rent); Tier 1 #4 (clock for expiry); Tier 2 #6 (paired escrow for dispute); Tier 2 #10 (`CommittedMap<K,V>` for the reverse index); Tier 1 #5 (slot-set for unique-name registration). |
| **privacy-voting** | `apps/privacy-voting/` | Anonymous voting: ZK eligibility, commit-reveal ballots, nullifier-based double-vote prevention, tally. | `cclerk::DelegatedToken` (wrong — bearer where it should be ZK); local blake3 commitments (wrong — should be Poseidon2); `BlindedQueue` mounted but unconsumed. | (a) Per-proposal sovereign cell with state = `(phase, commit_root, reveal_root, tally_root, eligibility_root, coordinator_pk_commit)`. (b) Voter eligibility = `Presented<EligibilityProof>` axum extractor (G30) consuming a `BridgePresentationProof`. (c) Commit = `Effect::QueueEnqueue(commits_queue, Poseidon2(option ‖ randomness))` + `Effect::ClaimSlot(domain=proposal_id, key=nullifier)`. (d) Reveal = `Effect::QueueDequeue + Effect::SetField(tally[option] += 1)` gated by `Caveat::RevealWindow`. (e) Tally = STARK reference circuit (G28) over `reveal_root`. (f) Coercion-resistance = `Effect::EncryptedTo { coordinator_id, … }` (G29). | Tier 1 #5 (`Effect::ClaimSlot` — the headline primitive); Tier 1 #3 (`Presented<P>`); Tier 2 #7 (`dregg-credentials` lift); Tier 3 #14 (coordinator-key threshold-decrypt); Tier 3 #12 (`BlindedQueue` payload return G41). |
| **identity** | `apps/identity/` | Verifiable credentials: issue / present / revoke; selective disclosure; predicate proofs ("age ≥ 18"); non-revocation STARK; anonymous ring presentations. **Already the most dregg-native of the apps audited** — `bridge::present` is the canonical primitive. | Real use of `circuit/src/dsl/predicates`, `dsl/membership`, `dsl/revocation`, `poseidon2`. Doesn't use the macaroon system at all. | (a) Per-issuer sovereign cell from an **issuer factory** (`FactoryDescriptor` pins the credential schema). (b) Credential issuance = `Effect::QueueEnqueue` of a credential commitment onto the holder's inbox queue (encrypted). (c) Holder stores `Credential` locally; never publishes it. (d) Presentation = `BridgePresentationProof` (already correct shape) submitted through the `Presented<P>` extractor. (e) Revocation = sorted Merkle tree on the issuer cell; non-revocation = STARK proof of non-membership. (f) Anonymous ring = `prove_blinded_membership_dsl` (exists). | Tier 1 #3 (auth/extractor); Tier 2 #7 (lift `bridge::present` to `dregg-credentials`); Tier 3 #13 (issuer attester registry). The least gap-blocked app. |
| **compute-exchange** | `apps/compute-exchange/` | "Advanced demo": temporal predicate proofs + intent matching for a GPU/agent-compute marketplace. Sealed-bid orders, dual escrow (payment + SLA bond), commit-reveal fulfillment, STARK delivery proof, optimistic dispute window. | Real `circuit::temporal_predicate_dsl::TemporalPredicateAir`, `intent::matcher`, `dispute::OptimisticSettlement`. | See §3.7 — gets its own design sketch. | Tier 1 #1, #2, #4, #5; Tier 2 #6 (paired escrow — payment+SLA); Tier 2 #9 (math gadget for SLA penalty pro-rata); Tier 3 #13 (oracle / attester for clock & delivery confirmation). The most ambitious. |
| **discord-bot** | `apps/discord-bot/` → moves to **`./discord-bot/`** (toplevel) | 19 slash commands; custodial cclerk; transfers; gallery bidding; DeFi (swap/lend/borrow — being deleted); orderbook trading (being deleted); credentials; federation status; block explorer; presence attestation (dischargeable caveat). | Reasonably real: `captp_client.rs`, `discord_caps.rs`, `presence.rs`, `devnet.rs`. Already the cleanest "non-decorative" dregg app (per `apps/README.md`: "we love dregg-discord-bot"). | Not a starbridge-app at all — it's a *long-running daemon*, not a web surface. Lives at toplevel. `dregg`-native shape: same as today (CapTP client + cclerk + intent posting). Once amm/lending/orderbook are removed from `apps/`, the discord-bot's command set shrinks; surviving commands target the remaining starbridge-apps (gallery, identity, governed-namespace, bounty-board, nameservice). | Tier 1 #3 (auth — for the bot's authorization-on-behalf-of-users flow); not much else. |
| **subscription** (provisional) | `apps/subscription/` | Recurring debit of subscriber → creator; `cclerk::DelegatedToken`-backed authorization envelope; epoch-keyed dedup. **The first audited app that *actually* used a real SDK primitive non-decoratively** (`receive_signed_delegation`). | Real `cclerk::receive_signed_delegation`, `DelegatedToken`; in-process `HashMap<(PublicKey, u64), u64>` for epoch dedup; wall-clock as epoch source. | (a) Per-subscription sovereign cell from a **subscription factory** (`FactoryDescriptor` pins: program VK = "delegated-debit state machine"; constraint vocabulary includes `MonotoneIncreasing(epoch)`). (b) Debit = `Effect::Transfer` with `Authorization = DelegatedToken` (already works). (c) Epoch dedup = `Effect::ClaimSlot(domain=subscription_id, key=epoch_hash)`. (d) Cancellation = `Effect::RevokeCapability` on the delegated debit cap. (e) Delivery of subscriber-only content = `Caveat::SubscriptionActive` on a content-access cap. | Tier 1 #4 (federation clock — the load-bearing fix); Tier 1 #5 (slot-set for epoch dedup, replaces the in-process HashMap). Decision: **include as a starbridge-app** — it's a clean storage-layer + delegation example and exercises factories + capability attenuation well. |

Apps **dropped** (per the brief): `amm`, `lending`, `orderbook`,
`stablecoin`, `dao-treasury`, `prediction-market`. See §4.

---

## §3. Per-app starbridge design sketches

Each sketch covers: dregg primitives composed, where Factories help,
what Starbridge UI surfaces are needed, demo vs. real version.

### 3.1 `nameservice` (recommended **first** build)

**Why first.** Already the cleanest dregg-native shape on paper (the
APPS-AS-USERSPACE-AUDIT §1.3 reads like a build spec). Touches every
shared primitive once — sovereign cells, factories, capability
attenuation, escrow, transition constraints — without being so
ambitious it gets blocked by missing primitives. It's the *paint by
numbers* exemplar for the rest.

**`dregg` primitives composed.**

- `Effect::CreateCell` via `create_from_factory(name_factory_vk,
  owner_pk, 0)`.
- `Effect::Transfer(rent_amount, treasury_cell)` + a per-name
  transition predicate.
- `Caveat::ResourcePrefix { name_prefix }` (new, but a generic
  caveat — see APPS-AS-USERSPACE-AUDIT §1.4(e)) on the owner cap.
- `Effect::GrantCapability` / `Effect::RevokeCapability` for transfer.
- `Effect::QueueEnqueue` / `Effect::QueueDequeue` for the dispute
  evidence queue.
- `EscrowCondition::PredicateSatisfied` for dispute resolution.
- CapTP `share_capability` / `accept_capability` for cross-fed.

**Where Factories help.**

A single `NameFactory` descriptor pins:
- `child_program_vk = NAMESERVICE_NAME_PROGRAM_VK` (the rent + ownership state machine).
- `mode = Sovereign`.
- `capability_template = [owner_cap, renew_cap, transfer_cap, sub_delegate_cap]`.
- `field_constraints = [
     FieldDelta(expiry, +epoch_len),   // rent-extension
     MonotoneIncreasing(name_hash),    // immutable identity
     SumEquals([rent_paid, balance], total),
   ]`.
- `creation_budget = 10_000` (rate-limits Sybil registration).

Anyone can inspect the descriptor and verify, just from the
factory_vk, what kind of cell will be produced and what its
invariants are. **This is the "constructor transparency" the
factory abstraction was built for.**

**Starbridge UI surfaces.**

- `<dregg-name-registry uri="dregg://cell/{registry_id}">` — list all
  registered names, click-through to each name cell.
- `<dregg-name uri="dregg://cell/{name_cell_id}">` — show
  `(name, target, expiry, owner_cap_id, sub-delegations)`. Renew /
  transfer / sub-delegate buttons gated on
  `runtime.caps.mutate`.
- Domain-specific turn-builder presets: `register_name(name, target,
  rent_years)`, `renew(name, years)`, `transfer(name, to_pk)`,
  `sub_delegate(name, prefix, recipient)`.
- Debug view: the cell's `field_constraints` evaluation trace at the
  cursor's height (Tier-1 #1 transition predicates are observable).

**Demo version** (3 days, blocked on Tier 1 #1 only):
- One factory deployed at boot.
- Single-federation; no cross-fed.
- Rent uses the in-browser `DreggRuntime` clock (manual `advance +1`).
- No dispute flow; just register / renew / transfer.

**Real version** (3 weeks, blocked on Tier 1 #1, #4, #5; Tier 2 #6, #10):
- Federation-attested clock for rent expiry.
- Paired-escrow dispute resolution.
- Reverse-index via `CommittedMap`.
- Cross-fed `alice@other-fed` resolution via CapTP.

### 3.2 `identity`

**Why nearly-first.** Already exercises real DSL primitives
(`predicates`, `membership`, `revocation`, `poseidon2`). The
remaining work is mostly *moving* code out of `apps/identity` and
into `dregg-credentials` (Tier 2 #7), then writing the Starbridge
UI on top of the already-correct cryptography.

**`dregg` primitives composed.**

- `bridge::present::BridgePresentationProof` (already canonical).
- `circuit::dsl::predicates::prove_predicate_dsl` / verify.
- `circuit::dsl::membership::prove_blinded_membership_dsl`.
- `circuit::dsl::revocation::non_revocation_dsl_circuit`.
- `Effect::QueueEnqueue` for credential delivery (encrypted inbox).
- `Presented<P>` extractor (new — Tier 2 #7).

**Where Factories help.**

An `IssuerFactory` descriptor pins the credential schema:
- `child_program_vk = ISSUER_PROGRAM_VK`.
- `creation_params.schema_hash` = the credential's
  Poseidon2-hashed schema (attribute names + types).
- `field_constraints = [Immutable(schema_hash), MonotoneIncreasing(issued_count)]`.

Two issuers with the same schema have the same `child_vk`
(deterministic). Verifiers can validate "credential was issued by
*some* issuer holding schema X" without trusting individual issuers.

**Starbridge UI surfaces.**

- `<dregg-issuer uri="...">` — schema, issued count, revocation root.
- `<dregg-credential uri="...">` — attributes (selective disclosure
  preview), present-via-proof flow.
- `<dregg-presentation-builder>` — wizard: pick credential → pick
  attributes to disclose → pick predicates → generate proof.
- Debugger view: STARK proof trace, predicate AIR columns.

**Demo version**: single issuer in-browser; one credential schema
("verified human"); one verifier endpoint; predicate = "I hold
*a* credential from issuer X".

**Real version**: federated issuer registry (attester registry,
Tier 3 #13); selective disclosure UI; non-revocation proofs;
anonymous ring presentations across multiple issuers.

### 3.3 `governed-namespace`

**`dregg` primitives composed.**

- Sovereign **DAO cell** from a `DaoFactory` descriptor:
  - `child_program_vk = DAO_GOVERNANCE_PROGRAM_VK`.
  - State slots: `(route_table_root, voter_root, proposal_root,
    threshold, current_epoch)`.
  - `field_constraints = [
      MonotoneIncreasing(proposal_root),
      MonotoneIncreasing(current_epoch),
      Immutable(threshold),       // amendable only via meta-proposal
    ]`.
- Per-proposal sub-cell from a `ProposalFactory`:
  - State: `(proposal_id, payload_hash, votes_for, votes_against,
    deadline, status)`.
  - Constraints: `MonotoneIncreasing(votes_for)`,
    `MonotoneIncreasing(votes_against)`, `Immutable(payload_hash)`.
- `Effect::SetField(proposal.votes_for += 1)` gated by
  `Caveat::VoterRoll` discharge proving membership.
- Atomic enactment: a single turn
  `Effect::SetField(dao.route_table_root = new_root)` with a
  threshold-discharge attestation (M-of-N voter caveats).
- `Effect::BindBlob(file_blob_hash, storage_uri)` for content-addressed file storage.

**Starbridge UI surfaces.**

- `<dregg-dao uri="...">` — route table, proposal list, members.
- `<dregg-proposal uri="...">` — voting widget gated on caps.mutate
  AND voter caveat being held in the cclerk.
- `<dregg-route-table uri="...">` — DFA visualization (already a
  thing in the discord-bot's block-explorer; lift the rendering).
- Debug view: route classification trace ("input path X → DFA states
  → class Y").

**Demo version**: in-browser DAO with 3 voters; propose-vote-enact
loop; one file mount.

**Real version**: full federation; multi-cell turn composition for
atomic route changes; file blobs via real `dregg-storage::BlobStore`.

### 3.4 `gallery` (the auction)

**`dregg` primitives composed.**

- Per-artwork sovereign cell from `ArtworkFactory` (pins:
  `Immutable(artist_commit)`, `MonotoneIncreasing(provenance_root)`,
  `BindBlob(image_hash)`).
- Per-auction cell from `AuctionFactory` (pins the commit-reveal
  state machine VK; param_hash includes commit/reveal window
  lengths; `field_constraints` enforce phase transitions and
  `FieldDeltaInRange(deadline, 0, K)` for anti-sniping).
- Per-bid escrow cell with `EscrowCondition::PredicateSatisfied(auction.winner == this_bidder)`.
- Settlement turn (atomic, multi-cell):
  - `Effect::ReleaseEscrow (winning_bid)`
  - `Effect::Transfer (artist_share)`, `Effect::Transfer (platform_share)`, `Effect::Transfer (prior_owner_share)`
  - `Effect::RevokeCapability (old_owner_cap)`
  - `Effect::GrantCapability (winner gets owner_cap)`
  - `Effect::SetField (provenance_root = Poseidon2(old, transfer))`
  - `StateConstraint::SumEqualsAcross([winning_bid], [artist, platform, prior_owner])` enforces royalty split.
- `Effect::ClaimSlot(domain=artwork_id, key=owner_cap_id)` enforces unique ownership.

**Where Factories shine.** Royalty splits and anti-sniping windows
are baked into the `param_hash` at auction-creation time, so they
can't be tampered with later. **An auction created from a factory
with `param_hash = H` has provably exactly those parameters** — the
factory is the constructor transparency the audit's "NFT-shaped
unique ownership" gap (§4.4(a)) wanted.

**Starbridge UI surfaces.**

- `<dregg-artwork uri="...">` — image (from blob), provenance chain
  walk, current owner.
- `<dregg-auction uri="...">` — phase indicator, time remaining,
  commitment count, reveal count, top-of-book commitment.
- `<dregg-bid-builder>` — commit / reveal flows.
- Live updates: subscribe to `dregg://cell/{auction_id}` for state
  changes (Tier 3 #11).

**Demo version**: single-bidder auction, no anti-sniping, no
royalty (just winner → artist transfer), trust in-browser clock for
phase advance.

**Real version**: multi-bidder, anti-sniping, royalty splits,
private-Vickrey (Tier 3 #14 dependent), federation-clock-driven
phase advance.

### 3.5 `bounty-board`

**`dregg` primitives composed.**

- Per-bounty sovereign cell from `BountyFactory`:
  - State: `(reward_note_root, qualification_hash, deadline, claim_root, status)`.
  - Constraints: `MonotoneIncreasing(claim_root)`,
    `Immutable(qualification_hash)`,
    `FieldGteHeight(deadline, 0)` (deadline always in the future at create-time).
- Claim = `Effect::QueueEnqueue(claim_queue, worker_commitment)` +
  `Effect::CreateNote (bond)`.
- Anonymity:
  `worker_commitment = Poseidon2(worker_secret, bounty_id, randomness)`.
- Qualification = `BridgePresentationProof` over the worker's
  receipt-chain IVC ("I have ≥N completed bounties").
- Delivery = STARK proof presented via
  `EscrowCondition::ProofPresented { circuit_id, expected_pi }`.
  Release = `Effect::Transfer` to a stealth address.
- Sybil resistance: `Caveat::Bond { amount, slashing_condition }` on the
  bounty cell's claim capability.

**Where Factories help.** `BountyFactory` is parameterized by
`qualification_hash`, so high-value bounties use a different
`child_vk` from low-value ones — **the factory tier itself becomes
the trust signal**, with no per-bounty config drift.

**Starbridge UI.**

- `<dregg-bounty-board uri="...">` — list of open bounties, filter by
  qualification tier.
- `<dregg-bounty uri="...">` — reward, deadline, claim count
  (anonymous), delivery status.
- `<dregg-bounty-claim-builder>` — anonymous claim wizard
  (generates `worker_commitment`, posts bond, registers in claim
  queue).
- Debug view: nullifier set, claim queue, delivery proof trace.

**Demo version**: single-bounty, no qualification proofs, manual
delivery verification (operator-signed), in-browser worker
identities.

**Real version**: federated; IVC-based qualifications; STARK
delivery proofs; private notes for payment; cross-federation
reputation portability (an open question, see §7).

### 3.6 `privacy-voting`

**`dregg` primitives composed.**

- Per-proposal sovereign cell from a `VotingFactory`:
  - State: `(phase, commit_root, reveal_root, tally_root, eligibility_root, coord_pk_commit)`.
  - Constraints: `MonotoneIncreasing(commit_root)`,
    `MonotoneIncreasing(reveal_root)`,
    `MonotoneIncreasing(tally_root)`,
    phase transitions gated by `FieldGteHeight(phase_change_height, 0)`.
- Eligibility = `BridgePresentationProof` consumed by
  `Presented<EligibilityProof>` extractor.
- Commit = `Effect::QueueEnqueue(commits_queue, Poseidon2(option ‖ r))`
  + `Effect::ClaimSlot(domain=proposal_id, key=nullifier)`.
- Reveal = `Effect::QueueDequeue` returning the original payload
  (Tier 3 #12 — needs `BlindedQueue::Consumed { nullifier, payload }`).
- Tally = STARK reference circuit (G28, new — sums per-option counts
  over `reveal_root`).
- Coercion-resistance / re-voting = `Effect::EncryptedTo {
  coordinator_id, ... }` (Tier 3 #14).

**Where Factories help.** A `VotingFactory` per electorate (with
`eligibility_root` baked in) means voters can verify they're
participating in a real, descriptor-pinned election — not a phishing
proposal.

**Starbridge UI.**

- `<dregg-proposal uri="...">` — question, options, phase, tally
  (after reveal closes).
- `<dregg-vote-builder>` — generates commitment, posts via cipherclerk's
  `postEncryptedIntent` or `signTurn`.
- `<dregg-tally-proof uri="...">` — STARK verifier for the tally
  proof.
- Debug view: nullifier set, commit/reveal/tally roots evolution.

**Demo version**: single-issue, single-round, public eligibility
(any cclerk can vote), no coordinator-decrypt, hardcoded reveal
height.

**Real version**: federated eligibility (issuer registry, Tier 3
#13); MACI-style coordinator decrypt; multi-round; coercion
resistance.

### 3.7 `compute-exchange` — the advanced demo

The brief asks for a concrete sketch of **temporal predicate proofs +
intent matching**. Here:

**Domain.** Buyers post jobs requesting `(gpu_count ≥ N, ram ≥ M,
deadline_height = H)`; sellers respond with offerings matching
those constraints; matching atomically locks (payment escrow,
seller SLA bond); on delivery, payment releases on a STARK proof
the work was done; on SLA violation (e.g., job took too long),
buyer slashes the SLA bond.

**`dregg` primitives composed.**

1. **Posting a job = posting an intent.**

   ```rust
   cclerk.post_encrypted_intent(MatchSpec {
       action: "compute-job",
       predicates: vec![
           PredicateRequirement::Gte { field: "gpu_count", value: 4 },
           PredicateRequirement::Gte { field: "ram_gb", value: 32 },
           PredicateRequirement::Temporal {
               // Temporal predicate: "the seller's average uptime over
               // the past 100 blocks is ≥ 0.95" — proven by the seller
               // via a STARK on their attestation history.
               kind: TemporalGte,
               metric: "uptime",
               window: 100,
               threshold: 0.95,
           },
       ],
       min_budget: 1_000_000,
       deadline_height: current_height + 1000,
   }, opts);
   ```

   The intent is encrypted to candidate sellers' stealth addresses.

2. **Seller responds with a `TemporalPredicateProof`.**

   The temporal predicate AIR (`circuit/src/temporal_predicate_dsl.rs`)
   already exists. The seller proves "over the last 100 blocks, my
   uptime metric was ≥ 0.95". The proof is bound to a public input
   that includes the *seller's commitment* + *the window end-height*
   (which is the buyer's `current_height`). This makes the proof
   non-replayable (a fresh window each time).

3. **Intent matcher selects the lowest-cost matching seller.**

   `dregg_intent::matcher::match_intent` runs the buyer's predicate
   set against seller offerings. Each predicate requirement is
   discharged by a proof attached to the seller's response. The
   matcher publishes a `MatchResult`; the buyer signs a
   `FulfillmentTurn` that:

4. **Atomic locks via paired escrow (Tier 2 #6).**

   - `Effect::CreateEscrow { from: buyer, amount: payment, condition: EscrowCondition::ProofPresented { circuit_id: DELIVERY_VK, expected_pi: job_hash } }`
   - `Effect::CreateEscrow { from: seller, amount: bond, condition: EscrowCondition::PredicateSatisfied(job.delivered == true && job.deadline_height ≥ current_height) }`

   Bound together by a shared `swap_id` (γ.2 cross-cell binding from
   `STAGE-7-GAMMA-2-PI-DESIGN.md`).

5. **Delivery = STARK delivery proof (already exists at `apps/compute-exchange/src/delivery_verification.rs`, 780 LOC of DSL circuit). Release flows automatically.**

6. **SLA violation = optimistic dispute.** Use `app-framework/src/dispute::OptimisticSettlement` (already exists). After delivery deadline, buyer can challenge by posting evidence; arbiter (or threshold of federation nodes) issues a decision; slash distribution via `compute_slash_distribution`.

**Where Factories shine.**

- A `ComputeOfferingFactory` per SLA tier (`bronze`, `silver`,
  `gold`), each baking different `field_constraints` (uptime
  thresholds, bond sizes). Buyers select tier; the factory_vk is
  the trust signal.
- A `JobFactory` per buyer organization (param_hash includes the
  buyer's payment-account root); enables per-organization
  accounting without per-job custom code.

**Starbridge UI surfaces.**

- `<dregg-job-board uri="...">` — list of open jobs, filter by
  predicates.
- `<dregg-job-builder>` — wizard: pick predicates (GPU count, RAM,
  uptime, deadline) → preview matching seller pool → post intent.
- `<dregg-seller-response>` — temporal-predicate proof visualizer
  (show the trace columns, the window endpoints, the threshold).
- `<dregg-delivery-proof>` — DSL circuit visualizer for the
  delivery proof.
- `<dregg-dispute>` — optimistic settlement state machine view.

**Demo version** (1 month, blocked on Tier 1 + Tier 2 #6 + #7):
- Single seller, single buyer in-browser.
- Pre-computed temporal predicate proof (cached); matcher selects
  on a single GTE predicate.
- Paired-escrow simulation in the wasm runtime; no real federation
  binding.
- Delivery proof = the existing 780 LoC DSL circuit, run in-browser.
- No dispute window.

**Real version** (2-3 months, blocked on full Tier 1+2 plus a real
relayed runtime to talk to a federation):
- Multi-seller, encrypted intent matching, real temporal proofs.
- γ.2-bound paired escrow.
- Optimistic dispute window with evidence + arbiter.
- Cross-federation seller pool.

**Compute-exchange is the integration test for the whole platform.**
Pretty much every Tier-1 primitive lights up here. Build last.

### 3.8 `subscription` (provisional starbridge-app)

Already audited as the first app using a real SDK primitive. The
storage-layer-ness comes from `dregg-storage::inbox::CapInbox` for
delivery of subscriber-only content.

**`dregg` primitives composed.**

- Per-subscription sovereign cell from `SubscriptionFactory` (pins
  the debit-state-machine VK; param_hash includes tier and price).
- Authorized debit = `Authorization::DelegatedToken` (already works
  end-to-end in the SDK).
- Recurring debit = `Effect::Transfer` gated by
  `Caveat::EpochWindow(current_epoch == subscription.epoch + 1)`.
- Idempotency = `Effect::ClaimSlot(domain=subscription_id, key=epoch)` — fixes the in-process HashMap.
- Content delivery = `dregg-storage::inbox::CapInbox::receive_at` from creator → subscriber.
- Cancellation = `Effect::RevokeCapability` on the delegated debit cap.

**Where Factories help.** A `SubscriptionFactory` per tier — `basic`,
`pro`, `enterprise` — each with a distinct `param_hash`. Subscribers
can audit the tier they're signing up for by inspecting the
descriptor.

**Starbridge UI.**

- `<dregg-subscription uri="...">` — tier, next debit height, cap
  status.
- `<dregg-creator-dashboard>` — active subscribers (anonymous
  commitments only), total recurring revenue.
- `<dregg-delegate-debit>` — UI to install the debit envelope.

**Demo / real split.** Demo: in-browser two-agent, manual epoch
advance. Real: federation clock, real inbox delivery.

---

## §4. Retirement plan for `apps/`

### 4.1 Delete outright (slop list)

These are use-case-first explorations that don't survive the
"rebuild from primitives only" rule. Designer-confirmed dropped:

- `apps/amm/` — constant-product market maker. Special-cased
  circuit (29 columns); no primitive sharing with other apps.
- `apps/lending/` — utilization-based interest, health-factor
  constraint. Same shape as stablecoin CDP; specialized circuits.
- `apps/orderbook/` — limit-order matching with commit-reveal.
  Heavy app-specific AIR (152-322 in `circuit.rs`); the abstract
  shape "two-party atomic swap" is the Tier-2 #6 primitive, which
  belongs *in the platform*, not in an app.
- `apps/stablecoin/` — CDP with oracle. Specialized 14-column
  circuit; oracle pattern wants Tier 3 #13 in the platform.
- `apps/dao-treasury/` — DAO treasury (multisig). Subsumed by
  `governed-namespace` (which is the better-designed DAO surface).
- `apps/prediction-market/` — bet + oracle resolution. The same
  shape as voting + a tally circuit; absent a strong reason to keep
  it as a distinct demo, drop. (See §7 — possibly resurrect later.)

**Action:** remove from workspace `[members]`, `git rm -r apps/X`.
Do not preserve any of these in `starbridge-apps/`.

### 4.2 Mine for lessons before deleting

- `apps/orderbook/src/circuit.rs` (152-322) — the match-priority
  AIR sketch. Worth extracting into a design note for the eventual
  Tier 3 priority-queue primitive (APPS-AS-USERSPACE-AUDIT §2.4(c)).
- `apps/orderbook/src/blinded_bids.rs` — `FairDistributionEndpoint`
  pattern; this is approximately what `dregg-storage::BlindedQueue`
  *should* expose. Lift into a storage example.
- `apps/stablecoin/src/circuit.rs` — the 14-column CDP circuit is
  an instance of `StateConstraint::ExpressionEquals` (Tier 2 #9).
  Keep as a *DSL test case*, not an app.
- `apps/gallery/src/private_vickrey.rs` (4195 LOC, currently dead).
  **Don't migrate yet.** It's a research artifact that reinvents
  threshold decryption + garbled circuits. Promote the techniques
  into `coord/` (Tier 3 #14) when there's a real demand; let this
  file stay in git history as the design exploration it is.
- `apps/prediction-market/src/lib.rs` — the "positional oracle
  feed" sketch (KZG stand-in). Extract into the eventual Tier 3 #13
  (attester registry) design note.
- `apps/lending/src/circuit.rs` — iterated-interest IVC sketch.
  Worth extracting as an IVC example in the docs.

Each "lesson" is a paragraph in a per-app `LESSON.md` inside the
crate at deletion time. Then `git rm`.

### 4.3 `apps/discord-bot/` → `./discord-bot/`

Toplevel. Action steps (DO NOT execute now — other lanes are
touching `apps/`):

```bash
# When the apps/ disruption window opens:
git mv apps/discord-bot discord-bot
# Then update /Users/ember/dev/breadstuffs/Cargo.toml:
# - replace "apps/discord-bot" with "discord-bot" in [workspace] members
# Plus any direct `path = "../discord-bot"` references in adjacent crates
# (currently none — discord-bot only depends inward).
```

Commit message: `move discord-bot to toplevel (it is a daemon, not a starbridge-app)`.

Slash-command set should shrink in the same PR: drop `swap`,
`lend`, `borrow`, `orderbook-buy`, `orderbook-sell` (they target
the dropped apps). Surviving commands: cclerk ops, gallery bid,
identity present/verify, governed-namespace mount/discover,
bounty-board claim, nameservice register/resolve, federation
status, block explorer, presence.

---

## §5. New `starbridge-apps/` directory shape

```
starbridge-apps/
├── README.md                    # ← short doc: "what is a starbridge-app, how to build one"
├── Cargo.toml                   # ← workspace marker (could be virtual)
├── shared/
│   ├── inspectors/              # ← Preact components published as ES modules
│   │   ├── name.js
│   │   ├── auction.js
│   │   ├── proposal.js
│   │   ├── ...
│   │   └── index.js             # ← registers all via window.dregg.register
│   ├── turn-builders/           # ← JS preset turn-builder modules (per app)
│   │   ├── nameservice.js
│   │   ├── gallery.js
│   │   ├── ...
│   └── factories/               # ← FactoryDescriptors checked in as JSON
│       ├── name_factory.json
│       ├── auction_factory.json
│       ├── dao_factory.json
│       ├── ...
├── nameservice/
│   ├── Cargo.toml               # ← uses app-framework for HTTP (if needed) + dregg-sdk
│   ├── src/
│   │   └── lib.rs               # ← FactoryDescriptor builders, turn helpers, server (thin)
│   ├── pages/                   # ← site-fragment pages, mounted under /starbridge-apps/nameservice/
│   │   └── index.html
│   └── README.md
├── identity/
│   └── ...
├── governed-namespace/
│   └── ...
├── gallery/
│   └── ...
├── bounty-board/
│   └── ...
├── privacy-voting/
│   └── ...
├── compute-exchange/
│   └── ...
└── subscription/
    └── ...
```

### 5.1 Cargo workspace

Each starbridge-app is a Rust crate that depends on:

- `dregg-sdk` (the canonical cclerk/identity/cell surface).
- `dregg-app-framework` (the HTTP/server glue *when an app needs a
  back-end* — most starbridge-apps don't, because the in-browser
  node + extension cclerk handle the work).
- `dregg-storage` (where storage-layer primitives are needed — e.g.,
  `BlobStore`, `CapInbox`, `BlindedQueue`).
- `dregg-cell` (for `FactoryDescriptor` construction).
- `dregg-turn` (for `Effect` enum, `TurnBuilder`).

**Critically:** each app exports a `FACTORY_DESCRIPTORS: &[FactoryDescriptor]`
or equivalent compile-time-baked artifact. The wasm
runtime preloads these at startup so that
`window.dregg.createFromFactory` can resolve `factory_vk` strings
into real descriptors.

### 5.2 Workspace member integration

Either:

**Option A (preferred):** add `starbridge-apps/*` paths to the
existing `Cargo.toml` `[workspace].members`. One workspace, one
target dir, all of dregg-sdk's compile artifacts cached.

```toml
members = [
  ...existing...,
  "starbridge-apps/nameservice",
  "starbridge-apps/identity",
  "starbridge-apps/governed-namespace",
  "starbridge-apps/gallery",
  "starbridge-apps/bounty-board",
  "starbridge-apps/privacy-voting",
  "starbridge-apps/compute-exchange",
  "starbridge-apps/subscription",
]
```

**Option B:** `starbridge-apps/` is its own workspace, included via
`exclude = [...]` in the root. Useful if starbridge-apps want
their own MSRV / lockfile / dependency strategy (e.g., trimmer deps
for wasm). Defer this decision until at least one app is built.

### 5.3 Composition with `app-framework`

Lane C is currently wiring `app-framework` with a cclerk handle —
this is the natural integration point. The shape:

```rust
// dregg-app-framework now exposes:
pub struct StarbridgeAppContext {
    pub cclerk: AgentCipherclerk,                   // identity / signing
    pub ledger: Arc<RwLock<Ledger>>,           // shared in-process state (back-end mode)
    pub executor: Arc<RwLock<TurnExecutor>>,
    pub factories: FactoryRegistry,            // descriptors loaded at startup
    pub federation_clock: Arc<dyn FederationClock>, // Tier 1 #4
}

impl StarbridgeAppContext {
    pub fn register_factory(&mut self, desc: FactoryDescriptor) -> [u8; 32] { ... }
    pub fn make_action(&self, target: CellId, method: &str, effects: Vec<Effect>) -> Action { ... }
    pub fn sign_and_submit(&self, action: Action) -> Result<TurnReceipt, _> { ... }
    // ...
}
```

Each starbridge-app crate exposes a single function:

```rust
pub fn register(ctx: &mut StarbridgeAppContext) -> RegisteredApp {
    // 1. Deploy factories.
    // 2. Register HTTP routes (if any).
    // 3. Return descriptors of routes, factory_vks, and frontend assets.
}
```

The host (`dregg-node`, a back-end aggregator binary, or the wasm
runtime in browser-only mode) calls `register` for each starbridge-app
it hosts. Per-app crates become *libraries*; the binary is a thin
aggregator.

### 5.4 Composition with `wasm/`

The wasm runtime preloads the workspace's `FACTORY_DESCRIPTORS`
constant at startup. **No app-specific code goes into wasm/.**
Instead, the wasm runtime is *generic* — it knows about Effect,
Cell, Turn, Factory, Authorization — and the apps are just
*data* (factory descriptors + frontend code + turn-builder
presets).

This is what makes "starbridge-apps are dregg-native from day 0"
load-bearing: an app's Rust crate is mostly factory-descriptor
construction and turn-builder helpers. The behavior is in the
state-constraint vocabulary and the factory-pinned program VKs;
the wasm runtime executes that uniformly.

### 5.5 Site composition

Each starbridge-app under `starbridge-apps/<name>/pages/` is a
fragment that the site build picks up under
`/starbridge-apps/<name>/`. The site's existing
`_layouts/default.html` chrome wraps it; the page mounts a
`<dregg-app>` context (per `site/STUDIO.md` §6) configured for that
app, and imports the app's `inspectors.js` and `turn-builders.js`
from `/starbridge-apps/<name>/`.

The Starbridge **page itself** (`site/src/starbridge.html`) stays as
the general-purpose debugger / explorer for *any* dregg URI. Each
starbridge-app is its own pretty UI on top.

---

## §6. Order of operations

Recommended build sequence — earliest to last:

1. **`nameservice`** (Week 1-2). Cleanest userspace match.
   Validates the factory-descriptor + transition-constraint
   integration. **Blocked on:** Tier 1 #1 (transition constraints).
   *Risk if Tier 1 #1 slips:* implement a `Custom` constraint shim
   per name cell, document the gap, ship the app anyway.

2. **`identity`** (Week 2-4, parallel with #1's tail). Crypto
   already works; this is mostly lifting `bridge::present` →
   `dregg-credentials` (Tier 2 #7). **Blocked on:** nothing
   gating — can proceed independently. *Output:* the
   `dregg-credentials` crate that the rest of the apps need.

3. **`subscription`** (Week 3-4). Smallest scope; validates the
   storage-layer + delegated-token + epoch-claim composition.
   **Blocked on:** Tier 1 #4 (clock), Tier 1 #5 (ClaimSlot).

4. **`governed-namespace`** (Week 4-6). Validates multi-party
   threshold protocols (M-of-N caveats, atomic enactment turns).
   **Blocked on:** Tier 1 #1; Tier 3 #15 (`BindBlob`) for files.

5. **`bounty-board`** (Week 5-7). Validates ZK qualification
   proofs at the `Presented<P>` extractor + anonymous-payment flow.
   **Blocked on:** identity (Tier 2 #7) for IVC standing proofs.

6. **`gallery`** (Week 6-9). Atomic settlement + royalty splits +
   anti-sniping. **Blocked on:** Tier 1 #1, #5; Tier 2 #6 (paired
   escrow). *This is where γ.2 bilateral binding becomes
   load-bearing.*

7. **`privacy-voting`** (Week 7-10). Validates ClaimSlot + blinded
   queues + tally circuit. **Blocked on:** Tier 1 #5; Tier 3 #14
   (coordinator-key for coercion-resistance) if real version
   targeted. Demo version unblocks earlier.

8. **`compute-exchange`** (Week 9-13). The integration test.
   **Blocked on:** essentially every Tier 1 + Tier 2 primitive,
   plus relayed-runtime for live federation talk. Build last; it's
   the validation that the platform is complete enough to host a
   real, complex, privacy-preserving marketplace.

In parallel to #1-2: the **shared inspector library** in
`starbridge-apps/shared/inspectors/`. Each app contributes its
domain inspectors as they're built; the next app reuses what's
already in the registry. By the time we hit `compute-exchange`, the
inspector library is mature enough that the app is "mostly UI
config and factory descriptors."

---

## §7. Open questions for the designer

The questions only you can answer from this point:

1. **Workspace shape: A or B?** Single root workspace (Option A in
   §5.2) shares deps and compile artifacts; multi-workspace (B)
   isolates starbridge-apps' deps from the dregg core. Default: A
   until there's a concrete reason to split.

2. **In-browser-only vs. server-side hybrid.** Some apps (gallery
   with live bidding, bounty-board with public board) want a
   long-lived *server* that aggregates state. Others (nameservice,
   identity) can be entirely client-side over a federation node.
   **Question:** is the goal that *every* starbridge-app run with no
   per-app server (just `dregg-node` + browser), or do some get to
   keep an aggregator? The audit suggests "no per-app servers
   ever," but governed-namespace's file storage benefits from a
   persistent host.

3. **Frontend tech stack lock-in.** STUDIO.md fixes
   Preact + signals + htm. Starbridge-apps must follow the same
   choice; do we *codify* this (a starbridge-apps style guide that
   bans React/Vue/Svelte/etc.) or stay flexible?

4. **Factory governance.** Each starbridge-app ships a set of
   `FactoryDescriptor`s. Who can *upgrade* them post-deploy?
   - If immutable: every upgrade is a new factory_vk, and
     old-cell-from-old-factory becomes legacy state.
   - If mutable: needs a governance flow (governed-namespace style
     DAO over the factory registry).
   Decision affects how `verifyProvenance` is used by apps over time.

5. **`apps/prediction-market/` — drop or fold?** Dropped per the
   brief, but the *use case* (commit-reveal bets + oracle
   resolution + pro-rata payout) is approximately
   `privacy-voting` + Tier 3 #13 attester. Worth resurrecting as a
   thin "voting+payout" extension once both land? Or genuinely gone
   forever?

6. **Cross-federation reputation.** Bounty-board's standing-proof
   (IVC over a worker's receipt chain) is per-federation. If a
   worker has reputation on federation A and applies to a bounty on
   federation B, what's the bridging story? Federation-to-federation
   credential acceptance is not yet specified.

7. **Subscription as a starbridge-app.** I've included it (§3.8),
   but it's a borderline call — it's not a UI-first app, it's a
   *recurring-payment primitive*. Alternative: extract the
   recurring-debit pattern into `dregg-storage` as a building
   block, and don't ship subscription as its own starbridge-app.
   Decision pending.

8. **discord-bot's surviving command set.** The brief
   moves it toplevel but doesn't say what commands stay. Suggested
   in §4.3, but the trim is opinionated; confirm.

9. **`dregg-credentials` crate scope.** Lifting `bridge::present`
   is Tier 2 #7. The natural home is a new crate `dregg-credentials`
   at toplevel. Does this displace `bridge/` entirely, or coexist
   (with `bridge/` retaining macaroon-specific bits)?

10. **Page-chrome reuse vs. domain skinning.** Starbridge-apps can
    either look-and-feel exactly like the Studio's Starbridge page
    (uniform debugging vibe), or have their own visual identity
    (gallery looks like an art gallery; bounty-board looks like a job
    board). The Studio runtime substrate is the *same*; the chrome is
    where they diverge. Confirm: starbridge-apps get their own visual
    identity within the Studio component grammar, not strict
    Starbridge debugger styling.

11. **Compute-exchange depth.** §3.7 sketches it as a deep
    integration test. Does the demo version need to ship a UI for
    "watching the temporal predicate proof being verified", or is
    the proof an opaque check the UI just renders as "verified ✓"?
    The proof inspector is interesting *as a debugging surface* but
    probably overkill for end-user product shape.

12. **Naming.** "starbridge-apps" is fine as a directory name.
    The brand name for what users see — "`dregg` Studio apps"? "`dregg`
    apps"? "Starbridge apps"? The Studio is a development IDE; an
    end-user buying art on the gallery probably shouldn't see the
    word "Starbridge" anywhere. Confirm naming for the
    user-visible / dev-visible split.

---

## Appendix A — Tier-1 primitives this plan depends on

Reproducing the prioritization from `APPS-AS-USERSPACE-AUDIT.md`
§7.1 for ease of cross-reference, with which starbridge-app each
blocks:

| # | Primitive | Apps blocked |
|---|---|---|
| 1 | Transition-aware `StateConstraint` (`FieldDelta`, `FieldDeltaInRange`, `MonotoneIncreasing`, `FieldGteHeight`, `SumEqualsAcross`) | nameservice, gallery, governed-namespace, subscription, privacy-voting, bounty-board, compute-exchange |
| 2 | `EscrowCondition::PredicateSatisfied` implementation | gallery, bounty-board, nameservice, compute-exchange |
| 3 | `AuthenticatedRequest<C>` axum extractor | all |
| 4 | Federation clock | nameservice, gallery, governed-namespace, subscription, privacy-voting, bounty-board, compute-exchange |
| 5 | `Effect::ClaimSlot { domain, key, proof }` | nameservice (unique-name), gallery (unique-owner), privacy-voting, subscription, compute-exchange |
| 6 (Tier 2) | Paired escrow / atomic swap pattern | nameservice (dispute), gallery (settlement), compute-exchange (payment+SLA) |
| 7 (Tier 2) | `dregg-credentials` crate + `Presented<P>` extractor | identity (provides it), bounty-board, privacy-voting, governed-namespace, gallery (gated auctions) |

The minimum platform work to unblock starbridge-apps to "80%
userspace": **Tier 1 in full + Tier 2 #6 and #7.** ~4-6 weeks per
the audit's estimate. That platform work proceeds in parallel with
nameservice + identity (which can be built against the existing
primitives with workarounds).

---

## Appendix B — File inventory for this plan

Files read or grepped while writing this plan:

- `APPS-AS-USERSPACE-AUDIT.md` (989 lines, in full)
- `SDK-REVIEW.md` (301 lines, in full)
- `site/STUDIO.md` (348 lines, in full)
- `site/src/starbridge.html` (88 lines, in full)
- `site/src/_includes/studio/starbridge.js` (411 lines, in full)
- `wasm/src/runtime.rs` (487 lines, header read)
- `wasm/src/lib.rs` (1914 lines, surface inventory)
- `extension/src/page.ts` (~320 lines, API surface)
- `apps/governed-namespace/src/main.rs` (header)
- `apps/bounty-board/src/{lib.rs,main.rs}` (headers)
- `apps/identity/CLAUDIT.md`, `apps/subscription/CLAUDIT.md`,
  `apps/compute-exchange/CLAUDIT.md`, `apps/gallery/CLAUDIT.md` (scope sections)
- `apps/README.md`, `apps/DESIGN_NOTES.md` (in full)
- `cell/src/factory.rs` (head + structure)
- `sdk/src/cipherclerk.rs` lines 4927-5050 (factory deploy/create methods)
- `Cargo.toml` (workspace members)
- `circuit/src/temporal_predicate_dsl.rs` (header)
- `intent/src/fulfillment.rs` (matcher integration points)

No code changes outside this document.
