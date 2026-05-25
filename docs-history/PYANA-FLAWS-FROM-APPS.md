# PYANA-FLAWS-FROM-APPS.md

**Scope:** Pyana-platform-level flaws surfaced by auditing all 10 apps in batches 1+2 (2026-05-24).

- **Batch 1**: `bounty-board`, `lending`, `orderbook`, `stablecoin`
- **Batch 2**: `nameservice`, `identity`, `subscription`, `compute-exchange`, `gallery`, `privacy-voting`

Per-app detail is in `apps/<name>/CLAUDIT.md` (6298 LOC across 10 files). Verdicts: **all 10 BROKEN**. Cumulative P0 count ≥ 60. Spot-verified P0 cites at end of document.

**Method:** Cross-cutting synthesis across the ten CLAUDIT.md files; corroborated against `AUDIT-cell.md`, `AUDIT-circuit.md`, `AUDIT-turn-executor.md`, `AUDIT-wallet.md`, `AUDIT-dsl.md`, `AUDIT-sdk-rest.md`, `AUDIT-node.md`, `AUDIT-extension.md`, `AUDIT-wasm.md`.

## The punchline

> **None of the 10 audited apps actually use the Effect VM, TurnExecutor, or wallet sealed-value notes as the primary execution path.** They are aspirational facades. Where they touch primitives at all, they reproduce the same witness-without-constraint anti-pattern documented in `AUDIT-circuit.md`. The most damning finding is *not* a primitive flaw — it's that **Pyana provides no paved path that an app developer could plausibly follow**. Each app reinvents auth, identity binding, proof verification, escrow, supply conservation, time, and nullifier management from scratch. Each one does it badly.

The bad news: the apps are broken. The good news: they are broken *consistently*, in ways that point to a finite set of missing primitives + framework scaffolding. The cell/turn/EffectVM model is sound; the layer above it (`pyana-app-framework`, opinionated defaults, well-paved patterns, reusable extractors) is thin or absent.

## The 10 apps in one table

| App | LOC (CLAUDIT) | Verdict | Headline P0 |
|---|---|---|---|
| bounty-board | 445 | BROKEN | Escrow release silently falls back to `blake3(bounty_id)` as fake receipt; no payment moves. 8 P0s. |
| lending | 634 | BROKEN | Zero Pyana primitive usage; sentinel `0xAA/0xBB/0xCC` identities; STARK proofs decorative; no oracle. 4 P0s, 10 P1s. |
| orderbook | 389 | BROKEN | Hardcoded trader id; STARK AIR missing priority constraints; settlement effects never submitted. 7 P0s, 13 P1s. |
| stablecoin | 455 | BROKEN | CDP `diff_high_bit` unconstrained — CDPs may be unbacked. Oracle key `[0x01u8;32]` in source. 5 P0s. |
| nameservice | 1229 | BROKEN | Owner keys publicly leaked in every whois/list; anyone transfers any name in O(N) requests; cross-fed resolver returns the *remote nameservice URI* as the resolution. 5 P0s. |
| identity | 756 | BROKEN | `Credential` has no signature field — anyone forges any credential. `/presentations/verify` trusts a `verified: bool` set on the holder. 6 P0s. |
| subscription | 687 | BROKEN | Epoch is request-body (no clock); no subscription nullifier; in-memory `HashMap` is only anti-double-bill. **First app to use a primitive non-decoratively** (`receive_signed_delegation` actually verifies). 5 P0s. |
| compute-exchange | 612 | BROKEN | Settlement escrows stored in app-local `ContentStore`, never sent to engine; `release_escrow`/`refund_escrow` return `bool` and every call site discards it. 8 P0s. |
| gallery | 628 | BROKEN | Frontend's "blake3" is FNV-prime mixing (so honest UI users forfeit escrow); 4195-LOC `private_vickrey.rs` is unwired; `Effect::Transfer { from: artist, to: artist }` is a no-op self-transfer. 9 P0s. |
| privacy-voting | 463 | BROKEN | Voting authority trivially deanonymizes every vote because the "disjoint" `voted` and `committed` maps are written in the same critical section. Tally is `for/+=` in Rust. No STARK anywhere. 8 P0s. |

## The meta-flaw: missing well-paved paths

Every app does the same things, badly:

1. **Hardcoded sentinel `CellId([0xAA;32])` for "the caller"** (lending, orderbook, stablecoin, gallery, identity, compute-exchange, nameservice, subscription, privacy-voting). Mutation endpoints have no notion of *who* is calling.
2. **Decorative ZK proof pipeline.** Proofs generated and discarded (stablecoin mint/repay drops proof bytes; identity verify is server-to-self lookup; bounty-board never wires a `ProofVerifier`; compute-exchange `release_escrow` returns `bool` that's discarded; gallery's settlement aborts in `ReleaseEscrow`).
3. **Roll-your-own auth that doesn't work** (bounty-board: string-compare against publicly-readable cell hex; nameservice: `owner` in request body, leaked in whois; identity: no signature on credentials; compute-exchange: `signature` field parsed and discarded; subscription: `sender_hex` self-declared).
4. **Pseudo-escrow.** "Escrow" is a `HashMap` keyed by ID; balances never debited. The bookkeeping flag transitions to "Paid"/"Finalized"/"Released" but no value moves.
5. **Cross-cell value accounting is purely additive Rust.** No app uses the wallet's sealed-value `HeldToken` discipline; supply drifts silently (stablecoin's `total_supply: u64 +=` desyncs from per-position `debt_amount`).
6. **Time is whatever the request body says it is.** Subscription's epoch, nameservice's clock (hardcoded to 1, so rent is decorative), stablecoin's oracle timestamp, lending's collateral price — all caller-supplied with no federation-attested clock.
7. **Frontend calls endpoints that don't exist.** Stablecoin, identity, gallery — the JS surface is independent of the Rust surface.

These are not 60+ bugs across 10 apps — they are a small number of missing platform features showing up dozens of times.

## Primitive gaps (G1–G30)

Synthesized from all 10 CLAUDIT.md `Pyana-level flaws surfaced` sections, deduplicated, organized by theme, ranked by load-bearingness. G1–G15 from batch 1 are kept stable; G16–G30 are batch-2 additions.

### Theme A — Framework / auth / identity binding (the highest-leverage tier)

#### G1. `pyana-app-framework`: `AuthenticatedRequest<C: Capability>` axum extractor.

Every app surfaces this. HTTP handler maps a signed request to "this came from `cell_id`, who holds capability `C` over resource `R`". `SignedAuthorizer` exists in `app-framework/src/authorizer.rs:90-146` but no extractor wraps it. With this in place, **the 4+ "anyone can impersonate anyone" P0s across every single app collapse to one fix.** Cross-references: nameservice P0-1, identity P0-2, gallery P0-6, compute-exchange P0-2, lending sentinel identities, orderbook hardcoded trader, stablecoin mutation endpoints, subscription P0-1.

#### G19. `InboxEndpoint` must authenticate `sender_hex` (sibling of G1).

`app-framework/src/inbox_endpoint.rs:211-227`: `sender_hex` is whatever the client says. Every app using `InboxEndpoint` (subscription, lending, bounty-board, compute-exchange) inherits this. Concrete shape: `InboxEndpoint` requires an Ed25519 signature over `(content_hash, sender_pk, deposit, enqueued_at)` and verifies `sender_pk == signer`.

#### G30. `PresentedRequest<P: Presentation>` extractor (sibling of G1, for ZK presentations).

Privacy-voting and identity both need a verified-ZK-presentation extractor where no plaintext credential leaves the holder. Without this, every privacy app reduces to bearer-token replay.

#### G2. `Engine::default_proof_verifier()` — no app should construct an engine without one.

`PyanaEngine::new()` constructs with no verifier; apps using `EscrowCondition::ProofPresented` silently fall through (bounty-board P0-4 verified: fake `blake3(bounty_id)` receipt substituted, bounty marked Paid). The framework should refuse construction without a verifier, or default to a real one and document overrides.

#### G3. `EscrowCondition::ProofPresented { verification_key: [u8; 32] }` is the wrong shape.

A 32-byte VK is not what STARK circuits use. Needs either (a) a `CircuitDescriptor` hash + expected `Vec<PublicInput>`, or (b) a structured `EscrowProof { circuit: CircuitId, public_inputs: Vec<BabyBear>, proof_bytes: Vec<u8> }`.

#### G18. `EscrowCondition::PredicateSatisfied` is declared but unimplemented in the executor.

`turn/src/escrow.rs:53-56` defines the variant; `turn/src/executor.rs:4847-4988` handles only `ProofPresented` and `SignedByAll`. Apps that want richer escrow conditions (compute-exchange's SLA bond) have no expressible primitive.

#### G20. `BatchExecutor` trait can't thread external state into `execute_batch`.

Subscription and lending both surfaced this. Concrete shape: `BatchExecutor::execute_batch<Ctx>(&mut self, batch: Vec<…>, ctx: &mut Ctx)` with an associated `Ctx` type.

### Theme B — Time / scheduling / clock (entirely missing today)

#### G16. `FederationClock` primitive in `pyana-app-framework`.

`EffectVmContext.current_block_height` exists at the platform layer but no app-facing API. Apps that need recurrence (subscription), expiry (lending, escrow), epochs (nameservice rent, voting phases) re-roll `SystemTime::now()` or request-body epochs — local, unsignable, unverifiable. Shape: `Clock` trait, `FederationClock` impl fetching federation-signed height, `MockClock` for tests. **Surfaced by:** subscription S2, nameservice N5, lending, orderbook, stablecoin oracle timestamp, gallery anti-sniping.

#### G25. Scheduled-effect primitive (`Effect::FireAt`).

The Effect VM is reactive: every effect fires now. There is no `Effect::FireAt { at_height, effect }`. Apps that need recurring (subscription) or delayed (escrow refund timeout, auction phase advance) currently require external keepers or just don't. Two shapes: (a) per-cell `scheduled_effects: BinaryHeap<(height, Effect)>` consumed at turn time, (b) federation-side scheduled-turn queue. **Recommended (b) for subscription-shape workloads.**

#### G37. `Effect::AdvancePhase` / `Effect::TimedTransition`.

Gallery's `advance_phase` is a Rust-side op outside any turn; voting phase advances are admin-button (privacy-voting F5). An `Effect::AdvancePhase { resource, from_phase, to_phase }` whose AIR enforces the height precondition would let observers verify "auction X advanced to Reveal at block H" without operator trust.

### Theme C — Nullifiers / value / accounting

#### G17. Subscription-nullifier / `Effect::ClaimSlot { domain, key }`.

Pyana has `Effect::NoteSpend { nullifier, … }` for one-shot spends and `BlindedQueue` per-dequeue nullifiers, but no general `(domain, key) → spent` Merkle set primitive with a federation-published root. Subscription debits, bounty claims, voting nullifiers, and recurring-claim flows all want this. Generalizes `NoteSpend`.

#### G5. Supply-conservation primitive.

The Effect VM proves per-cell deltas; atomic turns aggregate them. No primitive says "for asset X, sum of all unspent notes' face values equals the registered supply." Stablecoin needs this; orderbook escrow needs this; any token needs this. Shape: `Effect::SupplyRegister { asset_id }` + an AIR constraint linking it to per-cell deltas + periodic federation-attested supply commitment.

#### G4. DSL: first-class range checks + lookup tables.

`circuit/src/dsl/circuit.rs:82-130` has no `RangeCheck { col, n_bits }` and no lookup-table machinery. **Without range checks, any economic invariant involving integer comparison is unsound at the BabyBear boundary.** Stablecoin's `diff_high_bit` is the canonical example: declared `Binary` + `== 0`, but nothing binds it to the high bit of `col::DIFF` — prover writes whatever they want, CDP is unbacked. **Same anti-pattern in:** lending interest circuit, orderbook STARK AIR, compute-exchange compute-SLA AIR, identity `AttributeValue::Text` 4-byte truncation, identity predicate symbol 4-byte truncation. *This is the most reproduced circuit-design bug across the codebase.*

#### G21. NFT-style unique-ownership effect.

Pyana has fungible `Effect::Transfer` and `Effect::GrantCapability`. Neither cleanly expresses "exactly one cell holds this resource at a time, transferable." Gallery currently does `Effect::Transfer { from: artist, to: artist, amount: 1 }` as a no-op self-transfer. Shape: `Effect::TransferUniqueCap { resource_id, from, to }` with executor invariant "exactly one cell holds the cap for resource_id."

#### G22. Royalty-split effect.

Settlement needs to split a payment across (artist, royalty, fee). Today this is "several Transfer effects in one Turn" with no enforcement that the splits sum to the input or match a per-resource schedule. Shape: `Effect::SplitTransfer { from, splits: [(to, bps)], total }` with AIR constraint `sum(bps) == 10000`.

### Theme D — Identity / credentials / attestations

#### G7. Oracle primitive. **(Hold for user — design TBD; the user has reserved oracle design.)**

Every app needs price/data oracles and rolls its own. Stablecoin embeds `[0x01u8; 32]` literal signing key in source. Lending has no oracle at all. Shape TBD by user.

#### G26. Trusted-attester registry (generalizes G7).

Subscription's premium issuer is a single `PublicKey`. Same shape applies to KYC issuers, identity verifiers, federation-recognized oracles, governance auditors. A typed registry with categories (`kyc | oracle | credential | governance | …`) and per-category rotation policies.

#### G31. Promote `bridge::present` to a top-level "Pyana credentials" module.

`bridge/src/present.rs::BridgePresentationBuilder` + `macaroon/` already implement what `apps/identity/` claims to do, *correctly*, with federation-bound issuer membership and real STARK presentation. The identity app reinvents a strict subset, badly. Promote this to documented `pyana-credentials` and deprecate the app's reinvention.

#### G39. Non-revocation circuit must bind credential hash, not just root.

`pyana_circuit::dsl::revocation` has `pi::REVOCATION_ROOT` as the only PI. A holder can substitute a different non-revoked hash and the verifier cannot tell (identity P1-6). **Fix:** add `pi::REVOCATION_HASH` as a second PI bound to the trace column carrying the queried hash.

#### G40. `compute_fact_commitment(fact_hash, state_root)` accepts any `state_root` with no algebraic binding.

`predicates/base.rs:424`. The verifier sees `fact_commitment` and trusts it without knowing which credential it came from. **Fix coupling:** verifier independently recomputes `fact_commitment` from a signed credential commitment, passes that as PI.

### Theme E — Names / directories

#### G32. `Effect::RegisterName` doesn't exist yet (`DESIGN-dsl.md` §3.11 calls it out as "NEW VARIANT").

Until it lands, no app can correctly express "register a name" as a turn. **Blocks** nameservice and governed-namespace. **High priority for DSL Phase F.** Cite: `DESIGN-dsl.md:498-509` (proposal), `:1141` (migration task).

#### G33. Canonical name-directory primitive (`pyana-directory` crate).

CapTP has `SwissTable` (swiss → live capability); no platform analog for *named* (human-readable → swiss/sturdy-ref, with rent / expiry / dispute baked in). A `pyana-directory` crate combining `SwissTable` + `Authorizer` + `EscrowManager`-backed rent + Merkle-rooted name index would replace ~80% of the nameservice and governed-namespace code.

#### G34. CapTP high-level `resolve(name) -> PyanaUri` client API.

`captp/src/session.rs`, `captp/src/sturdy.rs` provide only low-level swiss-table primitives. A `CapTpClient::call_method(uri, method_name, args)` would make cross-fed resolution writable in 10 lines.

#### G35. `AuctionedNamespace` primitive.

Nameservice's premium-tier scheme (1-3 chars = 1000/epoch, etc.) is a per-app convention. ENS uses Vickrey for short names; Handshake runs a real Vickrey. Pyana has neither. Without a platform-level primitive, every name-shaped app re-rolls.

#### G36. `FederationPeerDirectory` primitive.

`MetaDirectory` (cross-fed name table) has no auth model. Need a platform "trusted peer federation" registry that nameservice (and any cross-fed app) plugs into.

### Theme F — Blobs / content / multi-party privacy

#### G23. Content-addressed blob primitive.

Galleries, bounty-board, DAO governance, identity-credential apps all need "this blob is bytes B, hash(B) = h, h is committed to the cell." No `Effect::BindBlob { cell, blob_hash, storage_uri }`. Every app reinvents this or skips it.

#### G24. Federation-mediated multi-party protocol primitive.

Private-Vickrey (gallery) and MACI-style voting require the federation to collectively garble / OT / threshold-decrypt. Gallery's `FederationGarblingNode` assumes a coordinator that doesn't exist.

#### G29. Coordinator-key primitive (MACI-style).

Pyana has federation key material in `coord/` but no app-facing primitive for "encrypt to a coordinator who decrypts only inside a STARK." Privacy-voting F4. Required for coercion-resistance and anti-collusion.

#### G27. Bulletin-board primitive.

`pyana-storage` has `BlindedQueue`, `ProgrammableQueue`, `Inbox`, `DataflowQueue` — but nothing shaped like an append-only, federation-attested bulletin with per-leaf inclusion proofs. Voting needs it; whistleblower-style flows need it; any commit-reveal needs it.

#### G28. Tally circuit reference.

Trivial circuit, prevalent need (voting, polling, surveys, prediction-market resolution). Should live in `circuit/src/dsl/predicates/`. Without it, every poll rolls a Rust `for/+=` loop (privacy-voting tally).

#### G8. Fair-ordering / batch-auction primitive (CowSwap-shaped).

`BlindedQueue` exists; no canonical batch auction / uniform clearing. Orderbook, compute-exchange matcher both want this.

#### G9. Sealed-bid sealed-execution.

Penumbra-style sealed orders. Requires G29 to expose threshold keys to apps.

#### G15. Verifiable-matcher reference circuit.

A project-provided STARK for batch matching (zkAMM-shaped) would prevent every orderbook-/auction-shaped app from rolling its own broken AIR (orderbook P0-3 verified; compute-exchange too).

### Theme G — Composition / effects

#### G11. Effect-VM gaps for app workflows.

- No `Effect::Cancel` (orderbook cancel "proof" is symmetric hash of public data).
- No `Effect::OrderbookSubmit` or composable higher-level effects.
- `Effect::CreateObligation` / `FulfillObligation` / `SlashObligation` have no Effect-VM row → obligation histories unprovable in-STARK. Lending needs this.
- `pyana_storage::BlindedQueue` produces nullifiers but no `Effect` consumes them (orderbook bypasses executor).

#### G38. `TurnComposer` API for multi-effect atomic turns.

Gallery, orderbook, lending, stablecoin, AMM all need "settlement = compose multiple cell mutations atomically." The multi-CallTree `call_forest` primitive exists but cross-cell signature semantics are murky and undocumented.

#### G10. Globally-anchored IVC standing-proof primitive.

`IvcBuilder` exists; what's missing is anchoring chains to a federation-attested registry root. Bounty-board P0-8 (standing proofs unanchored, trivially forgeable) and compute-exchange reputation both surfaced this.

### Theme H — Hygiene / honesty

#### G12. `InboxMessage::Encrypted` must actually be encrypted.

Tagged byte vector with no enforcement. Honest version: `InboxMessage::EncryptedTo<PublicKey>` constructible only via `encrypt_to(pk, plaintext)`. **Reinstated by:** identity PY-5, subscription S6.

#### G6. Sovereign-cell state-commitment hygiene (already in `AUDIT-cell.md` P0-2).

The three-disjoint-state-commitment-schemes problem + the 32→4 byte truncation from `AUDIT-circuit.md` P1-1. *Block sovereign-cell promotion as the app model* until these are fixed.

#### G13. Rebasing token primitive (optional).

Stablecoin design space includes rebasing assets. No primitive expresses "balance = face × accumulated_index."

#### G14. Emergency-pause primitive.

No primitive for "halt all mint operations across all cells." Tail-risk response = take federation offline.

#### G41. `BlindedQueue` payload return channel.

Per identity PY-4: the queue proves "a slot was consumed" but doesn't deliver the per-commitment payload. Add `Consumed { nullifier, payload }` variant, or document queue as budget-only and require a separate inbox-keyed-by-commitment delivery.

#### G42. OpenAPI / schema codegen for app frontends.

Stablecoin, identity, gallery all surfaced "frontend calls endpoints that don't exist with wrong body shapes." A typed `pyana-sdk-ts` generated from `apps/<x>/src/server.rs` route definitions would prevent silent drift.

#### G43. Token caveat enforcement helper.

`Attenuation.services` / `BudgetSpec.window` / `DelegatedToken.restrictions` are decorative unless the verifier explicitly checks them. Provide `enforce_attenuation(&token, &expected_caveats)`.

## What's *not* broken (calibration)

- Wallet sealed-value `HeldToken` is correct; apps simply ignore it.
- Effect VM AIR state-commitment chain *is* correctly bound (per `AUDIT-circuit.md` summary). The 24-effect set covers the right surface; gaps above are *additions*.
- `BlindedQueue`, `IvcBuilder`, `EscrowManager`, `Authorizer`, `ProgrammableQueue` exist and mostly work.
- `pyana-dsl` produces real circuits for real backends. The flaw is constraint vocabulary (G4) + the apps' tendency to write the same witness-vs-constraint bug it doesn't help them avoid.
- `subscription` is the **first audited app to use a Pyana primitive non-decoratively** (`receive_signed_delegation` actually verifies). Existence proof that apps *can* use the primitives correctly when the developer commits to it.
- `bridge/src/present.rs::BridgePresentationBuilder` + `macaroon/` are correct reference implementations of what apps *should* do (identity audit finding).

## The four lenses, applied across all 10 apps

Per the user's framing (`memory/project-apps-audit-framing.md`).

**Lens 1 — off-chain potential.** Every audited app could be ≥90% sovereign:
- bounty-board ~85% (per-issuer / per-worker cells; only global completion registry root needs federation attestation)
- lending ~85% (per-position cells; oracle + global supply on-chain)
- orderbook ~85% (per-trader cells; fair-ordering batch + nullifiers on-chain)
- stablecoin ~90% (per-CDP cells; oracle + global supply on-chain)
- nameservice ~70% (named directory inherently shared; per-name cells off-chain)
- identity ~99% (credential issuance and presentation fully off-chain; only revocation roots and issuer registry on-chain)
- subscription ~95% (per-subscription cells; clock + nullifier on-chain)
- compute-exchange ~80% (per-offering cells; settlement + dispute on-chain)
- gallery ~98% (blobs content-addressed off-chain; only ownership transfers on-chain)
- privacy-voting ~95% (vote preparation fully local; only bulletin-board + tally finalization on-chain)

**Lens 2 — what's verifiable anyway.** With G4 (range checks) + G6 (state-commitment hygiene), per-cell state transitions are presentable. Standing claims (reputation, CDP history) via G10 IVC anchoring. Credentials via G31 (`bridge::present`). Tally via G28.

**Lens 3 — what truly needs on-chain.** Across all apps, a small set:
- **Federation clock** (G16) — universal dependency
- **Asset supply commitments** (G5) — for any tokenized value
- **Nullifier sets / claim slots** (G17) — anti-double-spend / anti-double-claim
- **Oracle attestations** (G7) — when shared external data is needed
- **Settlement orderings** (G8, G15, G27) — orderbook, voting, auctions
- **Registry roots** (G10, G26, G36) — IVC anchoring, attester registries, peer federations
- **Name directory** (G33, G32) — the *one* genuinely shared namespace primitive

**Lens 4 — does cell/turn/EffectVM hold?** **Yes, but the framework around it doesn't.** The model bends gracefully to every audited workload. What's missing is (a) the app-framework scaffolding to make adoption viable (Theme A), (b) primitives for time (Theme B), nullifiers (Theme C), and credentials (Theme D), (c) directory / bulletin-board / threshold-key services (Themes E, F), and (d) the latent state-commitment hygiene fixes from `AUDIT-cell.md` / `AUDIT-circuit.md`.

The strongest finding from batch 2 is **time / scheduling is a categorical absence**, not a per-app oversight. Subscription was the first to surface it because subscription is *defined* by time, but lending, nameservice, orderbook, stablecoin, gallery, and voting all hit it in less obvious ways.

## What to do next (recommendation)

Prioritized by leverage. **Bold = unblocks multiple apps.**

1. **G1 (auth extractor) — the single highest-leverage fix.** Collapses 20+ P0s across all 10 apps to one fix.
2. **G16 (FederationClock) — universal dependency.** Subscription, lending, nameservice, gallery, voting all blocked on this.
3. **G2 + G3 + G18 (default verifier, escrow shape, predicate impl) — unlock escrow-as-real-payment** across bounty-board, compute-exchange, gallery, lending.
4. **G4 (DSL range checks).** Until apps can express `assert col ∈ [0, 2^n)`, every economic AIR will reproduce the `diff_high_bit` bug. Already present in stablecoin, lending, orderbook, compute-exchange.
5. **G17 (nullifier / ClaimSlot).** Generalizes `NoteSpend` for subscription, voting, bounty claims.
6. **G31 (promote `bridge::present` to `pyana-credentials`).** Cheap; deprecates the broken identity-app reinvention.
7. **G32 + G33 (Effect::RegisterName + pyana-directory).** Unblocks nameservice and governed-namespace.
8. **Discord-bot (9k LOC, largest unaudited app)** — likely surfaces the most CapTP / messaging gaps.
9. **Remaining apps** (amm, prediction-market, governed-namespace, dao-treasury) — audit to confirm the pattern is universal, then move to platform work. (`discord-bot` moved to toplevel `/discord-bot`.)

## Open questions for the user

1. **Is the apps-as-aspirational-facade pattern intentional?** (Deliberate "HTTP shape first, primitives later"?) If yes, this audit is a checklist. If no, the apps are misleading reference material.
2. **Should `pyana-app-framework` be promoted to a "well-paved-path" layer?** Opinionated defaults, refuse-to-construct-without-verifier, axum extractors, schema-generated TS SDK?
3. **G4 (DSL range checks)** — planned lookup-table backend (LogUp / Plookup)?
4. **G5 (supply conservation)** — per-asset or global supply table?
5. **G16 (FederationClock)** — block height as source of truth, or a richer epoch concept layered on top?
6. **G17 (ClaimSlot)** — generalize `NoteSpend`, or new effect entirely?
7. **Should decorative-proof patterns be removed from apps** until they actually verify? (Worse than honest absence: false-advertised security.)
8. **`Effect::RegisterName` (G32) timeline** — when does DSL Phase F land?

## Methodology / verification

This document synthesizes all 10 batch-1 and batch-2 CLAUDIT.md files. Before publishing, the following P0 cites were spot-verified by ember directly against source:

**Batch 1:**
- `apps/lending/src/server.rs:253,279,416` — sentinel CellIds: **CONFIRMED.**
- `apps/orderbook/src/server.rs:220` — hardcoded trader `CellId([0xAA;32])`: **CONFIRMED.**
- `apps/stablecoin/src/server.rs:52,449` — `let oracle_key = [0x01u8; 32]`: **CONFIRMED.**
- `apps/bounty-board/src/main.rs:723-725` — escrow release fallback to `*blake3::hash(&bounty_id).as_bytes()`: **CONFIRMED verbatim.**
- `apps/stablecoin/src/circuit.rs:151-240` — `diff_high_bit` Binary + `== 0`, no constraint binding to high bit of `col::DIFF`: **CONFIRMED.**
- `apps/bounty-board` — no `ProofVerifier` configured: **CONFIRMED** (zero grep hits).

**Batch 2:**
- `apps/privacy-voting/src/server.rs:343-356` — "DISJOINT" comment at :344, but `ps.committed.insert(commitment)` and `ps.voted.insert(voter_pk)` both in same critical section (lines 355-356): **CONFIRMED.** Operator print between lines reveals every `(voter, vote)` pair.
- `apps/nameservice/src/registry.rs:18` — `pub type PyanaUri = String;` (the real `captp::uri::PyanaUri` never imported): **CONFIRMED.**
- `apps/identity/src/credential.rs:25-33` — `pub struct Credential` has `issuer_id`, `holder_id`, attributes but NO `signature` field: **CONFIRMED.**
- `apps/gallery/frontend/bid.js:162-183` — `function blake3Hash(data)` is actually FNV-prime mixing (`* 0x01000193`), not BLAKE3: **CONFIRMED.**
- `apps/compute-exchange/src/state.rs:315,342` — `release_escrow`/`refund_escrow` return `bool`; `main.rs:967,971,1054,1057` call sites discard return value; `build_release_escrow_effect` exists at `settlement.rs:220` but isn't routed to an executor: **CONFIRMED.**

Findings in this document are credible at the cite level. The cross-cutting synthesis above is the audit's editorial layer.
