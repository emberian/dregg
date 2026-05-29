# gaps-2-distributed — the ACTUAL dregg vs the dregg2 design

> **Scope:** coverage of the *distributed / networking / economic / market / product*
> surfaces of the real Rust codebase against `dregg2.md` (+ `00-synthesis.md`).
> Verdict per item: **CAPTURED** (dregg2 absorbs it) · **PARTIAL** (gestured-at, real
> machinery uncaptured) · **MISSING** (no presence in dregg2) · **SUPERSEDED** (dregg2
> deliberately replaces/deletes it). "where-in-dregg2" = section it lives (or should).
>
> **Headline:** dregg2 is a beautiful, complete account of the *soundness core* (turn /
> conservation / authority / await / proof) and a *faithful* account of CapTP-as-CDT.
> It is almost **silent** on two whole load-bearing strata that exist as tens of
> thousands of lines of real code: **(1) the economic/fee machinery**, and **(2) the
> product/agent/app surface** (the MCP server, app-framework, starbridge apps, node,
> relay, gossip transport). dregg2 treats both as `[F]` one-liners. The user's
> expectation ("much is missing") is correct — but it is missing *upward* (product) and
> *sideways* (economics, transport), not in the core.

---

## (a) CapTP — `captp/` (5.1k LoC: session, sturdy, handoff, gc, uri, pipeline, store_forward)

| Item | Verdict | Note | dregg2 |
|---|---|---|---|
| Caps-across-net = CDT≡biscuit graph | **CAPTURED** | The central identity; cleanest part of dregg2. | §1.1, §3 |
| Promise pipelining (`pipeline.rs`, E-order, queue-on-unresolved-promise) | **PARTIAL** | Real cross-fed pipelining + broken-promise propagation exists; dregg2's await family (§4) has the *types* (zkpromise face) but **never models pipelining / message-queueing-on-promise / latency-collapse**. The E-order semantics are uncaptured. | §4 (await), should extend |
| 3rd-party handoff certs (`handoff.rs`: introducer-signs, offline, swiss-pre-reg, use-count) | **PARTIAL** | dregg2's discharge/3rd-party-caveat face (§4 row "discharge") is the *authority* analog, but the **network-layer handoff cert** (offline, out-of-band, recipient-bound, expiry+use-count) is a concrete protocol dregg2 doesn't name. The §3 discharge story is about caveats, not live-ref transfer. | §4, §3 |
| Distributed GC (`gc.rs`: export/import refcount, DropRef, session-validated drops, stale-sweep) | **MISSING** | **Genuinely absent from dregg2.** There is no reference-counting / drop-protocol / liveness-reclamation story anywhere. dregg2's coinductive cell "never bottoms out" (§1.3) — but real distributed caps need GC. Note the in-code `TODO(unified-lace)`: GC should key on StrandId not FederationId — even the code knows this is unfinished. | nowhere |
| Session lifecycle (`session.rs`: export/import tables, promise states, epochs, strands, disconnect) | **PARTIAL** | dregg2 names the "live CapTP session" as a caps-as-caps mediator island (synthesis §2.2) but does **not** model session establishment / epoch / reconnect / abort / the import-disconnect path. The vat boundary is theorized; the session *state machine* is not. | §1.1, §3 |
| Sturdyrefs (`sturdy.rs`) + store-and-forward (`store_forward.rs`) | **PARTIAL** | Sturdyref ≈ "an `Obs` badge that leaves the vat" / biscuit (§3) — partially captured. Store-and-forward (offline delivery) is **uncaptured**. | §3 |

**(a) bottom line:** distributed **GC is fully MISSING**; session-lifecycle, pipelining,
and the handoff *protocol* are PARTIAL (their *authority faces* are captured, their
*operational machinery* is not).

---

## (b) Networking / consensus stack — `blocklace/` (10.9k), `coord/` (6.3k), `net/` (4.8k), `node/` (24.2k), `federation/` (8.1k), `bridge/` (10.3k), `wire/` (9.1k)

| Item | Verdict | Note | dregg2 |
|---|---|---|---|
| Finality menu (causal / ack-threshold / τ-BFT / constitutional) | **CAPTURED** | dregg2's §2.2 4-tier menu maps directly onto `blocklace/{finality,ordering,constitution}.rs`; the I-confluence side-condition is a genuine addition. Best-captured non-core item. | §2.2 |
| Blocklace as CRDT / dissemination / cross-ref / multi-group | **PARTIAL** | The *law* (Merkle-CRDT, τ-per-group) is captured (§2.2). The **dissemination protocol**, `cross_reference.rs`, multi-group routing, `dregg_bridge.rs` are concrete machinery dregg2 abstracts away. | §2.2 |
| Plumtree gossip transport (`net/src/gossip.rs`: eager/lazy, IHAVE/GRAFT/PRUNE, anti-entropy, signed envelopes) | **MISSING** | dregg2 says "gossiped across hosts" (§1.1) as a *primitive*. The **actual gossip transport** — Plumtree spanning-tree, lazy-push, anti-entropy digest exchange — is entirely uncaptured. This is the wire by which the CDT propagates. | §1.1 (assumed) |
| The node itself (`node/`: MCP server, `blocklace_sync` 115k, `api` 252k, `relay_service`, `ws`, `multi_group`, genesis) | **MISSING** | **The running daemon — 24k LoC, the largest crate — has no presence in dregg2.** No host/vat *process* model, no sync protocol, no API surface, no genesis/bootstrap. dregg2's "host = trust-root" (synthesis §2.1) is a *concept*; the node is its *implementation* and is absent. | nowhere |
| Relay service (`relay_service.rs`: bonded operators, hosted inboxes, store-fwd, fees, GC, dequeue proofs) | **MISSING** | A whole **economic infrastructure role** (operators bond computrons, charge fees, prove delivery) — uncaptured, and ties into the missing economics (c). | nowhere |
| `coord/` (causal counters, 2PC atomic, Stingray bounded counters / shared budget) | **MISSING** | The **cross-silo coordination + 2PC + Stingray fast-unlock** layer is absent from dregg2. The budget piece is the economics gate (see c). Atomic cross-cell turns are flagged as a *gap* in synthesis §6.3 but the existing `coord/atomic.rs` 2PC machinery isn't acknowledged. | nowhere |
| `federation/` (threshold decrypt, epochs, committee identity, checkpoint, cross-fed bundles) | **SUPERSEDED (partly)** | synthesis §2.1 *explicitly* re-roots trust from federation-committee → host. So committee-`federation_id` is superseded — but **threshold decryption** (used by trustless intent, d) and **checkpoint/cross-fed-bundle transport** are live machinery with no replacement named. | synthesis §2.1 |
| `bridge/` (Mina, Midnight observer, present/authorize/convert/delta) | **MISSING** | Cross-chain interop (Midnight primary per memory) — **no interop/bridge story in dregg2 at all**. The whole external-chain surface is uncaptured. | nowhere |
| `wire/` (codec, connection, DFA router, captp_routing, hardening, cross-node auth) | **MISSING** | The transport/framing/routing layer — uncaptured (dregg2 stays at the semantic altitude). | nowhere |

**(b) bottom line:** the **finality menu is captured**; almost **all concrete transport
and process machinery is MISSING** — Plumtree gossip, the node daemon + sync, the relay,
`coord`'s 2PC/Stingray, the cross-chain bridge, and `wire`. dregg2 describes the *law*
the network obeys, not the network.

---

## (c) ECONOMICS — `coord/budget.rs`, `app-framework/fee_policy.rs`, `turn/executor/execute.rs`, `cell/value_commitment.rs`

| Item | Verdict | Note | dregg2 |
|---|---|---|---|
| Per-asset value conservation (Pedersen sum-to-zero, range, asset-tag) | **CAPTURED** | dregg2 §6.1 "the second rib" / §2.1 mint-burn generators **is** `cell/value_commitment.rs`. The strongest economics capture. | §2.1, §6.1 |
| Multi-asset (`AssetId`, per-asset generators, `FeePolicy` multi-asset pricing) | **PARTIAL** | §2.1 says "folded *per-asset*" — the conservation side is captured; **multi-asset *fee pricing*** (`FeePolicy::with_asset`, bps + min-fee per accepted asset) is not. | §6.1 |
| **Computrons** (`ComputronBudget`, metered execution, `computrons_used` in receipt) | **MISSING** | dregg2 **never mentions computrons / gas / metering.** Execution cost — the unit the whole system charges in — is absent. | nowhere |
| **Fee distribution** (50% proposer / 30% treasury / 20% burn, in `execute.rs:851`) | **MISSING** | A concrete, implemented **monetary policy** (proposer reward / treasury / burn split) — **nowhere** in dregg2. This is the system's incentive layer. | nowhere |
| **The budget gate** (`budget_gate` cell: tentative-debit → commit/refund, Stingray slices across silos) | **MISSING** | The **spend-authorization mechanism** (bounded-counter slices, fast-unlock on abort, `slice = balance·(f+1)/(2f+1)`) — a sophisticated Byzantine-safe distributed-spend primitive — is **entirely uncaptured**. | nowhere |
| Conservation *accounting* as ledger discipline (fee deducted Phase 1, never rolled back; refund on abort) | **PARTIAL** | dregg2's "abort = conservation-preserving refund" (§4) gestures at it; the **ledger-level fee/nonce/distribution delta** discipline is not modeled. | §4 |
| Relay/operator/solver-bond economics (`relay_service`, `intent/bond.rs` slashing escrow) | **MISSING** | Bonded-operator and bonded-solver-with-slashing economic games — uncaptured. | nowhere |

**(c) bottom line — THE BIG ONE:** the **full economic/fee model is NOT captured — only
gestured at.** dregg2 captures *conservation* (the value-rib, §6.1) beautifully but
mistakes conservation for economics. **Computrons, the 50/30/20 fee split,
treasury/proposer/burn monetary policy, the Stingray budget gate, and all
bonding/slashing/operator games are MISSING.** dregg2's "value rib" makes a badge
value-*bearing*; it says nothing about who *pays*, who *earns*, or how spend is
*authorized across silos*. **This stratum must be absorbed — it is the incentive spine.**

---

## (d) The intent ENGINE — `intent/` (20.7k LoC: solver, matcher, trustless, commit_reveal, exchange, bond, delay_pool, generalized, pir, partial_fill, cross_fed)

| Item | Verdict | Note | dregg2 |
|---|---|---|---|
| Intent = ∃-resolver-await + bounded solver | **CAPTURED** | dregg2 §4 ("intent face = ∃ filler"; "matcher is bounded pluggable untrusted plugin"; "no_general_matcher via HOU⪯GeneralMatch"; "WDP NP-hard, no PTAS") is a *faithful, excellent* capture of `solver.rs` + `matcher.rs` + `generalized.rs`. | §4 |
| VERIFY/FIND seam at matching | **CAPTURED** | §4 nails it; sharpest articulation in the whole doc. | §4 |
| **Trustless batch+consensus** (`trustless.rs`: 7-layer SUBMIT→BATCH→DECRYPT→SOLVE→PROVE→SELECT→SETTLE) | **PARTIAL** | dregg2's "bounded solver emitting checkable witness" covers SOLVE+PROVE+VERIFY. But the **batch-auction protocol** — consensus-determined batch boundaries, open solver competition, challenge windows, atomic compound-turn settlement — is **market machinery dregg2 doesn't model.** | §4 (should extend) |
| **Commit-reveal anti-front-running** (`commit_reveal_fulfillment.rs` + threshold-encrypted intents in `trustless.rs`) | **MISSING** | dregg2 says **nothing** about front-running or its defenses. Both layers (gossip-level commit-reveal + threshold-encrypt-the-batch-so-no-one-reads-early) are absent. For a market, this is a primary property. | nowhere |
| **Exchange / market / CoW ring trades** (`exchange.rs`, `solver.rs` Johnson-cycle ring solver, auctions) | **PARTIAL** | The *ring solver* is captured as "the bounded pluggable matcher" (§4). The **market/auction framing** (CoW, multi-asset exchange, the MCP `list_auctions`/`place_bid`) is not. | §4 |
| **Solver bonds + slashing** (`bond.rs`: escrow, lock, slash-for-underperformance) | **MISSING** | Incentive-compat machinery (bond, challenge-window slash) — uncaptured (and economic, see c). | nowhere |
| Delay-pool, partial-fill, PIR, generalized heterogeneous matching, cross-fed intents | **MISSING** | A family of real solver features (`delay_pool.rs`, `partial_fill.rs`, `pir.rs`, `generalized.rs`, `cross_fed.rs`) — none surface in dregg2. | nowhere |

**(d) bottom line:** the **intent *primitive* (∃-await + bounded solver + VERIFY/FIND) is
the best-captured thing in dregg2.** But the **market machinery around it is largely
MISSING**: the trustless batch-auction protocol, **commit-reveal + threshold-encrypt
anti-front-running**, solver bonds/slashing, and the exchange/auction surface. dregg2
has the resolver; it doesn't have the *market*.

---

## (e) The AGENT / PRODUCT / APP layer — `node/src/mcp.rs` (323k, 46 tools), `app-framework/` (6.9k), `starbridge-apps/` (8 apps, ~6k+), `sdk/` (18.9k), `wasm/` (11.3k), demos

| Item | Verdict | Note | dregg2 |
|---|---|---|---|
| The MCP server as the agent interface (46 `dregg_*` tools: authorize, submit_turn, post_intent, place_bid, create_agent, grant/revoke, prove_*, …) | **MISSING** | **The actual agent-facing product — how an AI *uses* dregg — has zero presence in dregg2.** dregg2 §6.2 mentions "the agent/zkRPC product" in *one `[F]` sentence* (zkRPC = a turn whose return projection is a proof-carrying `Obs`). The 46-tool MCP surface that *exists and works* is uncaptured. | §6.2 (one line) |
| zkRPC / return-projection (request→response, settled-call await face) | **PARTIAL** | dregg2 §6.2 *designs* this as forward-work (a return projection + settled-call await face) — but it's framed as **future design**, not recognizing that submit/authorize/read round-trips already exist in MCP/SDK. The *theory* is ahead of the doc's awareness of the *product*. | §6.2 |
| `app-framework/` (Axum server, AppCipherclerk, escrow, dispute, fee, ring-trade, blinded/queue/inbox endpoints, middleware, batch executor) | **MISSING** | An **entire application framework** (HTTP app server + escrow/dispute/fee lifecycle helpers + capability middleware) — uncaptured. This is how you *build a dregg app*. | nowhere |
| `starbridge-apps/` (nameservice, identity, subscription, governed-namespace, bounty-board, compute-exchange, gallery, privacy-voting) | **MISSING** | **Eight working apps** — concrete proof the platform hosts products — none referenced. (Some surface via the MCP `register_name`/`register_service` tools.) | nowhere |
| `sdk/` + `wasm/` (client, runtime, cipherclerk, captp_client, full_turn_proof, privacy, mnemonic; wasm bindings) | **SUPERSEDED** | synthesis §9 decision #3 explicitly **freezes** sdk/wasm/playground/discord-bot as "working v1 demo, rebuild later against the certified core." So *correctly* superseded — but note nothing replaces it yet. | synthesis §9.3 |
| Working demos (two-ai-handoff, sdk-consensus) | **PARTIAL** | The two-AI handoff demo (real STARK proofs) is the existence-proof the whole vision works; synthesis §9.3 freezes it. Captured-as-frozen. | synthesis §9.3 |

**(e) bottom line — THE OTHER BIG ONE:** the **product/app surface is almost entirely
MISSING from dregg2**, condensed into a single `[F]` "agent/zkRPC product" sentence
(§6.2). The MCP server (the *actual* agent interface), the app-framework, and 8 working
starbridge apps are the platform's *reason to exist* and have no design presence. The
sdk/wasm layer is correctly SUPERSEDED-pending-rebuild, but **nothing in dregg2 specifies
what the rebuilt agent/zkRPC product surface should be** beyond the one-line return-projection idea.

---

## TOP genuinely-MISSING / under-captured things dregg2 must absorb

1. **The whole economic stratum (c).** Computrons (metering unit), the **50/30/20
   proposer/treasury/burn fee distribution** (implemented monetary policy), the
   **Stingray budget gate** (Byzantine-safe cross-silo spend authorization), and all
   bonding/slashing/operator-fee games. dregg2 captures *conservation* (value-rib) and
   mistakes it for economics. **The incentive spine is absent.**

2. **The agent/product surface (e).** The 46-tool **MCP server** (the real agent
   interface), the **app-framework**, and **8 working apps** are compressed to one `[F]`
   line. dregg2 must specify the zkRPC/agent product as a first-class layer, not a coda.

3. **Distributed GC (a).** No reference-counting / drop-protocol / liveness-reclamation
   anywhere — a hard requirement for caps-across-the-net the coinductive "never bottoms
   out" framing actively obscures.

4. **Anti-front-running market machinery (d).** Commit-reveal + threshold-encrypted
   batch auctions, solver bonds/slashing, challenge windows. dregg2 has the intent
   *resolver* but not the *market* it lives in.

5. **The node + transport (b).** The Plumtree gossip transport, the running node daemon
   (largest crate, sync protocol, API), the relay service, `coord`'s 2PC, and the
   cross-chain bridge. dregg2 describes the law the network obeys, never the network.
