# dregg — the new world

What dregg is, in its current shape (2026-05-24), after a season of substrate work. This document captures the design coherence — what we call it, what its layers do, and how they compose. It is not a tutorial; it is the design story.

## Tagline

**dregg is becoming a proof-carrying capability mesh.**

It composes:
- **Distributed object substrate** (OCapN lineage — sturdy refs, attenuable caps, three-party handoff, swiss-table fast routing, distributed GC).
- **Atomic state transitions** (Turns batch Effects; the Effect VM AIR proves them; receipts certify; WitnessedReceipt chains replay).
- **Federated BFT consensus** (blocklace DAG with constitutional ordering; BLS threshold attestation; cross-federation interaction by mutual registration).
- **Programmable predicates** (slot caveats, `WitnessedPredicate` kinds, DFA-as-caveat, all under one composable vocabulary).
- **Cross-cell algebra** (γ.2 bilateral binding — Transfer/Grant/Introduce prove their algebraic agreement across the two cells' proofs).
- **Trustless intent matching** (real Shamir threshold decryption + ChaCha20-Poly1305; predicate-attested; bond-escrowed).
- **Federation-bypass primitive** (`peer_exchange` for direct sovereign-cell ↔ sovereign-cell signed state transitions; no federation in the trust path).

The kernel is OCapN-like capability transport + STARK-attested state transitions. The shell is everything that makes the kernel composable, governable, and verifiable.

## Two visions

**Silver Vision** is the *pre-algebraic* form — every component integrates, every loop closes, every receipt is signed and replayable. Trust-based by construction (executors are presumed honest), but the *substrate* required for the next step is in place. This is still in motion; `SILVER-DEBT.md` is the active ledger for places where the implementation falls short of that statement.

**Golden Vision** is the *folded mesh* form — recursive aggregation collapses the entire DAG of cells' interactions into one STARK statement: "the mesh up to here is internally consistent and re-derivable from witness data." Plonky3 recursion (Golden-Edge Block 1) is the substrate; γ.2 Phase 2 (joint aggregation AIR) is the first concrete step.

Silver makes Golden meaningful: there is nothing to constrain algebraically until the loops complete.

## Layers (substrate up)

### Cells, capabilities, and identity

- **Cell** — a unit of programmable state with an owning key. State is a `Vec<FieldElement>` (slots); behavior is governed by a `CellProgram` (`None` | `Predicate(Vec<StateConstraint>)` | `Cases(Vec<TransitionCase>)`). Sovereign cells self-manage state; hosted cells are state-mediated by an executor.
- **Capability** — a reference to a cell-method composition, attenuable. Faceted caps narrow permissions; sealed caps gate visibility; bearer caps grant exercise without identity.
- **CapTP wire transport** — sturdy refs (durable; bearer-shaped), swiss-table fast routing (per-session promise IDs), `HandoffCertificate` (Alice→Bob→Carol three-party handoff, cross-federation), `PipelinedMsg` (promise pipelining over the wire).
- **`Authorization::CapTpDelivered`** — the new authorization variant proving a turn arrived via a verified CapTP handoff. Carries `{handoff_cert, introducer_pk, sender_pk, sender_signature}`. The executor's `verify_captp_delivered` checks introducer-sig + sender-sig + cert freshness; the turn applies as if signed.
- **Cipherclerk** (`AgentCipherclerk` in the SDK; `AppCipherclerk` is the narrow framework handle) — the agent-side *cryptographic clerk*. It holds signing keys, authorization tokens, the receipt chain, the stealth keypair, and presents credentials/proofs on the Principal's behalf. The name borrows from Greg Egan's *Polis* and its descendants (Diaspora, Schild's Ladder), where a citizen's cipherclerk is the autonomous component that manages their cryptographic identity and capability handles. The legacy term was "cclerk"; that connoted value storage, but a dregg cipherclerk's authority is mostly *capabilities*, not balances — so the rename is permanent and the old name remains as a deprecation-free alias during the migration window.

### Turns, effects, the Effect VM

- **Effect** — a state-mutation primitive. 46+ variants (`SetField`, `Transfer`, `Grant`, `Introduce`, `SpendNote`, `CreateCellFromFactory`, `EmitEvent`, …).
- **Turn** — an atomic batch of `Action`s, each with a target cell, method, effect sequence, preconditions, and authorization. Hashed canonically via `Turn::hash` v3 (covers actor, nonce, effects_hash, federation_id, sovereign_witnesses, custom_program_proofs, witness_blobs, …).
- **`TurnExecutor`** — applies turns to a ledger; verifies authorization + cell-program enforcement + conservation + sovereign witnesses; emits receipts.
- **Effect VM AIR** — ~151-column STARK circuit proving the trace of an entire turn. PI includes `TURN_HASH_BASE[4]`, `EFFECTS_HASH_GLOBAL_BASE[4]`, `ACTOR_NONCE`, `PREVIOUS_RECEIPT_HASH_BASE[4]`, `IS_AGENT_CELL`, plus γ.2 cross-cell accumulator roots and (when present) sovereign-witness binding. Each effect variant has a per-row encoding; honest variants project full 4-felt commitments, but a handful still use placeholder/truncated values (tracked as work-in-progress).
- **WitnessedReceipt** — receipt + STARK proof + public_inputs + optional `WitnessBundle`. Scope-1 = proof verifies; scope-2 = inline witness data allows AIR re-execution by any verifier.

### Predicates everywhere — one vocabulary

The unifying insight is that dregg has **many places** where "this thing is allowed" is expressed (slot caveats, action preconditions, capability caveats, authorization), and they all want the same predicate language.

- **`StateConstraint`** (21+ variants) — declared on cell programs, evaluated per state transition. Vocabulary: `FieldEquals/Gte/Lte/Delta/DeltaInRange/GteHeight/LteHeight`, `WriteOnce/Immutable/Monotonic/StrictMonotonic/MonotonicSequence`, `BoundedBy`, `SumEquals/SumEqualsAcross`, `SenderAuthorized` (against a Merkle set root), `CapabilityUniqueness`, `RateLimit/RateLimitBySum`, `TemporalGate`, `PreimageGate`, `AllowedTransitions`, `AnyOf` (single-level disjunction over simples), `BoundDelta` (cross-cell γ.2 hook), `TemporalPredicate`, `Witnessed(WitnessedPredicate)`, `Custom { ir_hash, descriptor, reads }`.
- **`Precondition`** (per-action, snapshot-time) — `SlotEquals`, `SlotZero`, `NonceAtLeast`, and `Witnessed(WitnessedPredicate)`. One shared `EvalContext { block_height, timestamp, current_epoch, sender, sender_epoch_count, revealed_preimage }`. The `cell/preconditions` and `turn/preconditions` surfaces collapsed into one in this season.
- **`CapabilityCaveat`** — caps composed with `FacetConstraint` and `Witnessed(WitnessedPredicate)`.
- **`WitnessedPredicate { kind, commitment, input_ref, proof_witness_index }`** — the unification. `kind` ∈ {`Dfa`, `TemporalPredicate`, `BlindedSet`, `MerkleMembership`, `Custom { vk_hash }`}. `input_ref` ∈ {`Slot`, `Witness`, `PublicInput`, `SigningMessage`}. The `WitnessedPredicateKindRegistry` (mirrors the macaroon `CaveatType` ID-range precedent) maps `kind` to a verifier. **The same predicate vocabulary serves slot caveats ("does the transition have shape X") and authorization ("is the caller entitled to drive this") — distinguished by `input_ref`**.
- **`Action::witness_blobs: Vec<WitnessBlob>`** — the canonical carrier that every witnessed predicate dispatches against. `Turn::hash` v3 covers it.

### Authorization

Six modes (after this season):
- `Signature(Ed25519)` — actor signs canonical signing message
- `Proof(SealedTurnProof)` — turn arrives proven valid
- `Breadstuff(hash)` — preimage gates the action
- `Bearer(BearerCap, sig)` — bearer-cap delegation
- **`CapTpDelivered { handoff_cert, introducer_pk, sender_pk, sender_signature }`** — *new*; CapTP-delivered turn's authorization is the bound message-delivery proof
- **`Custom { predicate: WitnessedPredicate }`** — *new*; app-defined auth modes (multisig, DAO-quorum, time-locked, capability-conditional, compute-attested) plug in via the `WitnessedPredicate` kind registry

`AuthRequired::Custom { vk_hash }` lets a cell declare *which* kind of custom auth its capability requires. The Authorization::Custom design (`AUTHORIZATION-CUSTOM-DESIGN.md`) lays out Phase 1 (variant + verifier routing), Phase 2 (compute-exchange / multisig pilots), Phase 3 (eventual collapse — not scheduled).

### Federation and consensus

- **`Federation`** (unified after this season) — `{ members, bls_committee: Option, epoch, threshold, id, blocklace: Arc<Blocklace>, local_seat: Option<LocalSeat> }`. Subsumes the four prior disjoint concepts (`FederationCommittee`, `FederationMode`, opaque random `federation_id`, the dead Morpheus simulator).
- **`federation_id = H(committee_pubkeys)`** — cryptographic, not nominal. Genesis can't fabricate it.
- **`AttestedRoot` v3** — signed preimage now binds `federation_id` + `blocklace_block_id` + `finality_round` (alongside the prior `merkle_root`, `note_tree_root`, `nullifier_set_root`, `height`, `timestamp`). Closes T6 (cross-federation replay) algebraically.
- **`FederationReceipt`** — produced by the live node path (no longer tests-only). Threshold-signed via BLS over `ark_bls12_381`.
- **`KnownFederations`** registry — `node::state::known_federations: HashMap<FederationId, Federation>`, persisted at `<data-dir>/known_federations/<federation_id>.json`. Replaces the prior flat `known_federation_keys: Vec<PublicKey>`. Self-registers the local federation. CapTP routing consumes via `sync_known_federations(&registry)`. First-contact registration via the `dregg-node register-federation` CLI.
- **Blocklace** — DAG-shaped BFT consensus (Cordial Miners + Blocklace data structure + Constitutional Consensus). 199 unit tests covering CRDT/safety/liveness/equivocation. The "what does this node know" data structure; the federation's role is to attest to its state.

### Cross-cell algebra (γ.2 — bilateral binding)

Single-cell proofs say "Alice's cclerk correctly applied N effects to Alice's state." They say nothing about whether Bob's state updated consistently. **γ.2 fixes this** for three primitive cross-cell effect families:

- **Transfer** (symmetric: A debits = B credits): `transfer_id = Poseidon2("γ-transfer", from_cell, to_cell, amount, sender_nonce)`.
- **Grant** (asymmetric: A grants cap to B): `grant_id = Poseidon2("γ-grant", from_cell, to_cell, cap_target, permissions, expiry)`.
- **Introduce** (three-party CapTP handoff: A→B→C): `intro_id = Poseidon2("γ-intro", introducer, introducee, target_cell)`.

Each cell's WitnessedReceipt PI exposes an `outgoing_<kind>_root` and `incoming_<kind>_root` — Merkle accumulator over its bilateral schedule entries. The off-AIR verifier (`dregg-verifier bilateral-pair <wr_sender> <wr_receiver>`) reconstructs the schedule from `(call_forest, ACTOR_NONCE)` and confirms accumulators agree. `IS_AGENT_CELL` PI gate identifies which cell in a multi-cell proof is the actor.

**Phase 1** (PI-only): both sides produce independent proofs whose PIs cross-validate.
**Phase 2** (joint aggregation AIR): a single outer proof verifies both inner proofs *and* enforces the cross-cell agreement algebraically. Substrate landed via plonky3 recursion generalization (Lane Golden-Edge Block 1).

Composite operations get bilateral binding by composing the primitives: an auction settlement is `Transfer + Grant(NFT cap)`; a paired escrow swap is two `Transfer`s bound together; a ring trade is N `Transfer`s in a cycle.

### Trustless intent matching

`TrustlessIntentEngine` accepts threshold-encrypted intents. Real cryptography wired this season:
- Encryption: Shamir-over-GF(256) secret-shares a 32-byte ChaCha20 key; encrypted under the threshold scheme.
- Each validator produces a `DecryptionShare { validator_index, share, ciphertext_id, share_mac }`; the `share_mac` is verified at submission.
- Once `t-of-n` shares are collected for *every* ciphertext in a batch, `combine_shares` reconstructs the key and ChaCha20-Poly1305 decrypts to real `Intent`s.
- The cleartext sideband `set_decrypted_intents` was deleted.
- `NodeStateInner.trustless_intent_engine` is owned in production state; three REST endpoints (`/intents/trustless/{submit,share,status}`) drive the pipeline.
- Lowering: `Intent::RingSettlement` composes `Effect::Transfer` primitives (with γ.2 bilateral binding); not a bespoke "settle_ring_leg" method (which no cell implements).
- Fulfillment uses real STARK proofs via `dregg_circuit::multi_step_air` with replay-resistant `request_hash` binding.

### DFA as a first-class predicate

`dregg` now has a canonical `dregg-dfa` crate. Its `GovernedRouter` is a constitutionally-governed atomic-swap routing table with BLAKE3 commitment + threshold-sig-verified updates. AIR integration: `circuit::dsl::circuit` has DFA AIR rows; `dfa::compile_to_air` + `dfa::verify_acceptance` provide the registry verifier for `WitnessedPredicateKind::Dfa`. Three real consumers migrated: `apps/governed-namespace` (canonical replacement for its prior 287-line BTreeMap pretender), `intent/src/gossip_filter.rs` (gossip topic filtering), and `wire/src/dfa_router.rs::IngressFilter` (wire-level pre-filter at server ingress).

Userspace can compose DFA caveats via `StateConstraint::Witnessed(WitnessedPredicate { kind: Dfa, ... })` — "this slot can only be set to inputs the route table accepts."

### Storage as cell-programs

The thesis: storage primitives are not new Effects. They are *cell-program patterns* composing existing primitives (`SetField`, `EmitEvent`, `Transfer`) under cell programs declaring slot caveats from the unified vocabulary.

`STORAGE-AS-CELL-PROGRAMS.md` lays out per-primitive reference designs:
- **`CapInbox`** — cell with `WriteOnce` message slots + `MonotonicSequence` head/tail counters + `SenderAuthorized` publishers/consumers
- **`ProgrammableQueue`** — direct: `QueueConstraint` vocabulary IS slot-caveat vocabulary
- **`PubSubTopic`** — cell with append-only message log + Monotonic seq + Merkle-root slot for subscribers
- **`BlindedQueue`** — the only one needing `WitnessedPredicate::Custom { vk_hash }` registration (reuses `NoteSpendingAir`)
- **`RelayOperator`** — uses DFA caveats for dispatch

Net retirement: `storage/`'s middle layer (`storage::programmable::*`) graduates into cell-program reference templates; only truly-low-level primitives (Poseidon2 commitment trees, KV backend) remain in the storage crate.

### Federation-bypass: `peer_exchange`

For sovereign cells that don't want federation in the trust path: `cell::peer_exchange::PeerExchange` is a P2P state-exchange protocol between two sovereign cells. Each `PeerStateTransition { cell_id, old_commitment, new_commitment, effects_hash, timestamp, sequence, signature, transition_proof: Option<Vec<u8>> }` is signed (Ed25519) and optionally STARK-proven. Verification: signature against the peer's pubkey, sequence-exactly-prior-plus-one, commitment continuity, timestamp non-regression, optional inner-STARK via `EffectVmAir`.

This is the **federation-bypass** primitive. Alice and Bob can interact directly with their own cells without a federation knowing. The post-soundness-sweep `SovereignCellWitness` shape now matches `PeerStateTransition` (Ed25519 + sequence + optional STARK) — the same shape serves both the federation-mediated sovereign turns and the federation-bypass peer exchange.

### Persistence: receipts are the stream

Per `HOUYHNHNM-COMPARISON.md`'s closing reframe: **the WitnessedReceipt chain IS dregg's persistence layer.** Not an auxiliary log, not a sidecar — the canonical, source-of-truth stream. The `dregg_persist` on-disk database is a *cache* of state derived from this stream; given the receipt chain alone, any verifier can re-derive the cell's state at any tip. Operator-side retention is therefore a *policy on the persistence stream*, not a policy on a database: `dregg_node::config::RetentionPolicy` (default `Forever`) declares which suffix this operator commits to *serving*, and the wire-level `WireMessage::RequestReceipt` / `ReceiptResponse` returns a structured "covered by archival attestation X" response — never a bare 404 — when the hot tail has been pruned. This is the houyhnhnm "persistence-is-policy" framing put on a cryptographic substrate: the persistence stream is *the* thing the operator hosts, and the rest is cache.

## Boundary discipline

`BOUNDARIES.md` names 14 boundaries with a unified vocabulary:

- **cleartext-inside** — sees the plaintext datum
- **commitment-inside** — sees the commitment but not the value
- **acceptance-inside** — sees only proof-of-acceptance (yes/no)
- **out-of-band** — learns nothing

For every subsystem (CapTP, Federation, Blocklace, Turn/Executor, WitnessedReceipt, Cell, Storage, Wire, Privacy/Sealing, Intent, Bridge), we declare the boundary contract using this vocabulary. The doc names nine inconsistencies (e.g., `FieldVisibility::Committed` hides from external readers but NOT from the host executor; sovereign cells *intended* to hide from host, implementation does not yet algebraically enforce). The vocabulary is a *rustdoc convention*, not a new type system.

## Executor honesty audit (soundness ledger)

`EXECUTOR-HONESTY-AUDIT.md` enumerates 15 threats a malicious executor could attempt and where each is defended:

- **T1, T3, T15** (reorder/skip/forge effects) — single-cell closed via Stage 7-γ.0 (effects_hash binding); multi-cell closed via γ.2 Phase 1
- **T2** (invent effects) — actor signature covers `effects_hash`
- **T5** (reuse nonce) — closed at AIR (row-0 boundary binds state_before.nonce to PI[ACTOR_NONCE])
- **T6** (cross-federation replay) — closed algebraically via AttestedRoot v3 `federation_id` binding
- **T8** + **T11** (fake previous_receipt_hash; stale-proof replay) — closed via verifier PI completeness pass
- **T9** (skip sovereign witness) — Phase 1 design landed (AIR boundary constraints gated by `IS_SOVEREIGN_CELL`); Phase 2 (recursive verifier) depends on plonky3 recursion completion
- **T10** (skip capability check) — closed at AIR (per-effect cap-presence constraints; 4 CapTP variants verified real Merkle membership)
- **T12** (lie about balance deltas) — `compute_balance_delta_from_effects` derives from effect list; bound in AIR

Three boundary cuts are *not yet algebraically enforced* (executor-trusted): T9 sovereign witness at AIR level (Phase 1 designed); the bridge proof-to-action binding (lives in executor comments); `coord::BudgetCoordinator` signature verification gaps.

## Aggregation / Golden Vision direction

Per `KIMCHI-SURVEY.md` + `STAGE-7-GAMMA-2-PI-DESIGN.md`:

**Option A (transparent all-the-way, recommended):** generalize `plonky3_recursion_impl.rs` past `P3MerklePoseidon2Air` to accept the Effect VM AIR shape. Block 1 landed. Subsequent blocks: recursive verification of full Effect VM traces; hook into WitnessedReceipt scope-2 replay as an optional compression mode (no re-execution required).

**Option B (Kimchi/Pickles outer layer):** Mina's production recursive composition over the Pasta cycle. We already have `circuit/src/backends/{kimchi,mina}/`. Trade-off: production-proven recursion vs. losing transparency at the outer layer.

**γ.2 Phase 2** uses Option A's recursive verifier to consume per-cell PIs into a single outer proof attesting bilateral consistency. Substrate is in place; full implementation is the first concrete Golden Vision lane.

## Userspace surface

- **`AppCipherclerk`** (`app-framework/src/cipherclerk.rs`) — narrow 6-method handle wrapping `Arc<RwLock<AgentCipherclerk>>`: `make_action`, `sign_action`, `make_turn`, `cell_id`, `public_key`, `federation_id`. Apps don't see the 107-method `AgentCipherclerk`.
- **`AppServer`** — axum server with `.with_cclerk(...)` and `.with_embedded_executor(...)` extension hooks. `EmbeddedExecutor` is the submission path: the app authors a signed action and `EmbeddedExecutor` actually applies it to a ledger + returns the receipt. (Pre-this-season, apps authored actions and dropped them on the floor.)
- **`StarbridgeAppContext`** — the canonical mounting point for starbridge-apps: cclerk handle, embedded executor, KnownFederations reference, factory registry, inspector registry for Studio integration.
- **`FactoryDescriptor`** — `cell::factory::FactoryDescriptor` bakes program VK + state constraints + capability templates. `Effect::CreateCellFromFactory` creates cells via this canonical path. Apps register descriptors; users create instances.
- **DSL** — `dregg-dsl` is the *caveat predicate language* (descended from macaroons/biscuits). It compiles to 7 backends (`gen_air`, `gen_kimchi`, `gen_plonky3`, `gen_sp1`, `gen_midnight`, `gen_datalog`, `gen_rust`); cross-backend differential testing (40 cases × 5 voting backends; 2 lint-only) confirms agreement. The DSL stays at the caveat layer; it does not author Effect VM transitions.

## Starbridge — dregg's IDE/runtime

`starbridge` is the in-browser dregg IDE. The wasm runtime drives real `AgentCipherclerk` + `Ledger` + `TurnExecutor` (not a JS simulation — wasm-bindgen routes to the canonical crates). The Chrome extension exposes `window.dregg` with `signTurn`, `createFromFactory`, `verifyProvenance`, `shareCapability`, etc.

**Starbridge-apps** (`starbridge-apps/`) are the new userspace. Each is a Rust crate exporting `FactoryDescriptor[]` arrays + turn builders, plus a `pages/` directory with web components. The pattern: cell-program patterns + slot caveats + DSL caveats. **No new Effect variants.** The order (per `STARBRIDGE-APPS-PLAN.md`): nameservice → identity → subscription → governed-namespace → bounty-board → gallery → privacy-voting → compute-exchange. The legacy `apps/` retires as starbridge-apps replace each one.

The slop-list (`amm`, `lending`, `orderbook`, `stablecoin`, `dao-treasury`, `prediction-market`) is already deleted.

## Inventory: what landed this season

**Substrate (prior session — 2026-05-24):**
- Slot caveats v1 (21+ `StateConstraint` variants) + the three surface variants (`StateConstraint::Witnessed`, `Precondition::Witnessed`, `CapabilityCaveat::Witnessed`)
- `WitnessedPredicate` unification + kind registry (Dfa, TemporalPredicate, BlindedSet, MerkleMembership, Custom)
- `Action::witness_blobs` canonical carrier
- `Authorization::CapTpDelivered` and `Authorization::Custom` (Phase 1)
- Federation unification (`Federation` type subsumes the 4 disjoint concepts; `federation_id = H(committee_pubkeys)`; AttestedRoot v3; KnownFederations registry; `register-federation` CLI)
- γ.2 bilateral binding Phase 1 (PI exposure + off-AIR verifier subcommand)
- Sovereign-witness Phase 1 design (AIR teeth gated by `IS_SOVEREIGN_CELL`)
- Real Shamir + ChaCha20-Poly1305 threshold decryption wired into `TrustlessIntentEngine` in production
- Cipherclerk v1→v3 signing migration (closes the witness wire-malleability bug)
- Verifier PI completeness pass (closes T8 + T11)
- Bridge `destination_federation` AIR enforcement (closes a part of T6)
- `Cell::seal` `allowed_effects` round-trip fix (closes the unseal authority-amplification bug)
- `TurnError::SovereignWitnessRequired` actually constructed at the rejection site
- `StarkMembership` variant deleted (no longer always-errors)
- `plonky3_recursion_impl` generalized past `P3MerklePoseidon2Air` (Golden-Edge Block 1)

**Substrate (session 2026-05-25 — soundness emergency + receipt foundation):**
- **Temporal AIR boundary binding** — `THRESHOLD`, `STATE_ROOT_INITIAL`, `STATE_ROOT_FINAL` now bound into STARK PI; forged-threshold attack closed (`df122d4c`, SILVER-DEBT T1.5)
- **NonMembership adjacency_tag** — `CONSECUTIVE_TAG = [0xFE;32]` public sentinel replaced with per-`(commitment, lower, upper)` derived tag; sorted-neighbor bypass attack closed (`5d557969`, SILVER-DEBT T2.7 Silver-Sound interim)
- **NotYetWiredVerifier registry** — `default_builtins()` switched from `StubVerifier` (accept-all) to `NotYetWiredVerifier` (reject-all) for every non-NonMembership kind; honest fail-closed posture (`c86aecd7`, SILVER-DEBT T2.8)
- **Executor signature widening** — `canonical_executor_signed_message` promoted to `v3`, now covers full `receipt_hash` field set (`e0fe3316`, SILVER-DEBT T1.6)
- **VK integrity gate** — `SetVerificationKey` apply now enforces `hash == blake3(data)`; `from_parts_checked` added for untrusted-input call sites (`08e01ea7`, SILVER-DEBT T1.3 partial)
- **block1-bind TODO closure** — `convert_turn_effects_to_vm` queue/capability arms now source real ledger values (queue_len, old_capacity, permissions, refcount) instead of zero/synthetic placeholders (`9834b3d4`, SILVER-DEBT T2.1 + T2.2)
- **Custom-effect VK widened to 8 BabyBear felts** — `expand_vk_hash_16_to_32` retired; dispatch now carries full 32-byte VK hash (`46a886a5`, SILVER-DEBT T3.3)
- **Proof-carrying receipt real effects_hash** — `verify_and_commit_proof` path now populates `effects_hash`, `action_count`, `computrons_used` from PI rather than emitting stub zeros (`57f2b041`, SILVER-DEBT T1.7 partial)
- **Cclerk strict receipt-chain** — `append_receipt` now rejects mismatched `previous_receipt_hash` instead of silently rewriting it; strict atomicity semantics (`83718782`)
- **AttestedRoot `receipt_stream_root` wired** — threaded through stand-in constructors in federation/node (`aab40d37`)
- **Lifecycle Effects shipped** — `Effect::LifecycleActivate`, `LifecycleSuspend`, `LifecycleTerminate`, `LifecycleDestroy` variants with adversarial test suite (`f4a4fd17`)
- **`SCHEMA_BURN` AIR** — algebraic Burn invariant with nullifier binding (`bf7060fc`)
- **Poseidon24To1 OOB panic fixed** — evaluation-domain out-of-bounds access repaired (was breaking 30+ tests) (`2a06e669`)
- **CellProgram::Cases default-deny** — unknown-method calls to Cases programs now return an error instead of silently succeeding (`1597c528`)

**Userspace (prior session):**
- `AppCipherclerk` + `EmbeddedExecutor` + `StarbridgeAppContext`
- `dregg-credentials` crate (G31 from DREGG-FLAWS-FROM-APPS: promotes `bridge::present`)
- `dregg-directory` crate (G32/G33: promotes nameservice/governed-namespace directory pattern)
- `dregg-dfa` crate (canonical DFA + AIR + governance)
- `starbridge-apps/nameservice` bootstrap
- `starbridge-apps/identity` bootstrap

**Tests (session 2026-05-25 — ~200 new integration tests):**
- `CELL-TURN-TEST-AUDIT.md` + integration suites: `integration_lifecycle`, `integration_burn_receipt`, `integration_attenuate_capability`, `integration_destroy_terminal`, `integration_attestation_archive`
- Starbridge-apps executor-invoking tests for all 4 current apps (`d235a86b`)
- Intent/bridge integration tests (40 tests, `e404a0af`)
- SDK/node/wire integration tests (`f49b732b`)
- Substrate integration tests for storage-templates, credentials, app-framework (`2f3d5977`)
- Meta-test audit + labeling of fake assertions (`5dd9106f`)

**Cleanup / retirement (prior session):**
- 6 slop apps deleted (amm, lending, orderbook, stablecoin, dao-treasury, prediction-market)
- discord-bot promoted to toplevel; migrated to AppCipherclerk
- `cod/` deleted
- `store/` renamed `persist/`
- Crate name normalization (`dregg-` prefix everywhere: `dregg-token`, `dregg-macaroon`, `dregg-tokenizer`, `dregg-secrets`, `dregg-hints`, `dregg-discharge-gateway`)
- `hints/` edition 2024 + profile override removed
- Morpheus retirement Blocks 1-5 + 7-8 (Block 6: physical deletion of the 2515-LOC simulator pending teasting/wasm/sdc migrations)

**Design (canonical docs — prior session):**
- `BOUNDARIES.md` — the 14-boundary vocabulary
- `PREDICATE-INVENTORY.md` — the unified predicate taxonomy
- `SLOT-CAVEATS-DESIGN.md` + `SLOT-CAVEATS-EVALUATION.md` — the StateConstraint vocabulary
- `STORAGE-AS-CELL-PROGRAMS.md` — the storage migration thesis
- `AUTHORIZATION-CUSTOM-DESIGN.md` — the Custom auth surface
- `FEDERATION-UNIFICATION-DESIGN.md` — the Federation collapse
- `STAGE-7-GAMMA-2-PI-DESIGN.md` — bilateral binding PI layout
- `SOVEREIGN-WITNESS-AIR-DESIGN.md` — AIR teeth phases
- `old-docs/2026-05-26/SILVER-VISION-E2E-VERIFICATION.md` — archived end-to-end demo design; stale as an active status source
- `DFA-RATIONALIZATION-DESIGN.md` — DFA as caveat
- `KIMCHI-SURVEY.md` — recursion landscape
- `EXECUTOR-HONESTY-AUDIT.md` — the T1-T15 threat ledger
- `CAVEAT-LAYER-COVERAGE.md` — what's enforced where
- `STARBRIDGE-APPS-PLAN.md` — the userspace migration plan
- 8 audit docs (`AUDIT-distributed-semantics`, `AUDIT-offline-mode`, `AUDIT-blocklace-consensus`, `AUDIT-federation`, `AUDIT-protocol-composition`, `AUDIT-privacy`, `AUDIT-nullifiers`, `AUDIT-sovereign-witness-teeth`, `AUDIT-coord-crate`, `AUDIT-trace-crate`, `BACKWATER-CRATES-AUDIT`, `CELL-CRATE-REVIEW`, `STORAGE-REFLECTIVITY-RBG-DFA-AUDIT`)

**Audit + study docs (session 2026-05-25 — 20+ new documents):**
- `SILVER-DEBT.md` — the canonical Silver-vs-Golden debt ledger (T1–T3 items; CI enforcement design)
- `AIR-SOUNDNESS-AUDIT.md` — complete AIR soundness sweep (attack sketches for T1.5, T2.7, T2.9, T2.5, T2.11)
- `EXECUTOR-VK-AUDIT.md` — executor + VK layering audit (closure plans for T1.3, T1.6, T1.7, T2.17, T2.18, T3.3)
- `RECEIPT-ARCHITECTURE-STUDY.md` — receipt chain / audit trail deep dive
- `HOUYHNHNM-COMPARISON.md` + `HOUYHNHNM-DEEP-CRITIQUE.md` — Houyhnhnm system comparison + deep critique
- `PROTOCOL-CATEGORICAL-ANALYSIS.md` — categorical treatment of dregg's protocol primitives
- `old-docs/2026-05-26/KIMI-DAMAGE-AUDIT.md` — archived audit of prior Kimi-authored code for soundness regressions
- `TEST-REALITY-AUDIT.md` — test suite honesty audit (fake assertions, scaffold must_pass)
- `old-docs/2026-05-26/MULTI-NODE-DEVNET-RUN.md` — archived multi-node devnet run report; not current proof of Silver E2E
- `old-docs/2026-05-26/PREV-SESSION-AUDIT.md` — archived cross-session state reconciliation
- `DEMO-INTERACTION-MATRIX.md` — demo scenario matrix for the two-AI handoff
- `STORAGE-SECONDARIES-TRIAGE.md`, `CELL-TURN-TEST-AUDIT.md`, `CIRCUIT-VERIFIER-TEST-AUDIT.md`, `INTENT-BRIDGE-TEST-AUDIT.md`, `FEDERATION-CAPTP-TEST-AUDIT.md`, `SDK-NODE-WIRE-TEST-AUDIT.md`, `META-TEST-AUDIT.md`, `SUBSTRATE-TEST-AUDIT.md` — active per-layer test audit suite
- `old-docs/2026-05-26/STARBRIDGE-APPS-TEST-AUDIT.md` — archived starbridge-apps audit snapshot
- `BLOCK1-BIND-CLOSURE-NOTES.md` — closure notes for the block1-bind debt wave

## What's not done (honest)

The remaining Silver Vision items, in priority order:

1. **AIR completeness** — `ValidateHandoff` recipient/introducer pk placeholders (T2.3); 30-bit value truncations in interior balance arithmetic (`BridgeMint/BridgeLock/CreateEscrow`, T2.5); `EffectVmShapeAir` covers only a structural subset of `EffectVmAir` constraints (T2.6). The main queue/capability block1-bind group is closed (`9834b3d4`).
2. **StateConstraint AIR teeth** — most variants are executor-side only; AIR boundary constraints are opt-in per variant (start with `SenderAuthorized` since the swiss-table-membership gadget exists).
3. **Sovereign-witness AIR Phase 1 + 2** — Phase 1 implementation; Phase 2 depends on plonky3 recursion completion.
4. **Bridge proof-to-action binding** — backwater audit: lives in executor comments, not the circuit.
5. **`coord::BudgetCoordinator` signature verification** — two real security bugs (test has comment "Forged signature not verified in rebalance yet").
6. **Storage primitive migrations** — Phase 1 (ProgrammableQueue → cell-program) and Phase 2 (CapInbox → cell-program) bring the design's thesis into code.
7. **Morpheus retirement Block 6** — physical deletion of ~2515 LOC dead simulator after teasting/wasm/sdc migrations.
8. **Test suite coverage** — 200 new integration tests landed this session; remaining gaps catalogued in `META-TEST-AUDIT.md` and the per-layer test audit docs.
9. **Token caveat modernization** — discard the 12 ancient caveat types; converge the 3 shape-similar ones with `cell::CapabilityCaveat`.
10. **Real STARK ProofVerifier for intent fulfillment** — `TrustlessIntentEngine::new` still defaults to `WitnessedProofVerifier::with_stub_registry()` (SILVER-DEBT T1.2); the registry plumbing exists, wiring it is the remaining work.
11. **Studio integration** — `STUDIO-REFACTOR-PICKUP.md` documents 13 refactors the resumed studio agent absorbs; we wrote the substrate.
12. **`dregg-witnessed-registry-default` crate** — no in-tree host binary installs real verifiers for all 6 `WitnessedPredicateKind` variants; `default_builtins()` correctly rejects them but doesn't provide them (SILVER-DEBT T1.4, T2.8).

The Golden Vision items (γ.2 Phase 2 joint aggregation AIR, full mesh attestation) sit on top of these.

## How to read this

`dregg`, today, is the *Silver Vision in motion*. The substrate is mostly in tree. Each remaining gap above has a concrete plan or design doc. The thesis — *proof-carrying capability mesh, with programmable cell semantics, federated consensus, cross-cell algebra, and zero-knowledge predicate composition under one design discipline* — is coherent and partially realized.

The vocabulary across the system is unified. The boundaries are named. The vision is real and reachable.

## Cross-references

- `dev-philosophy/01-north-star.md` — what dregg is for (mission)
- `THOUGHTS-AND-DREAMS.md` — historical session notes
- The 25+ audit / design docs listed above
- `paper/` — the formal write-up of all of this
