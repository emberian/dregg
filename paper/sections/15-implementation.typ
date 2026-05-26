// =============================================================================
// Section 9: Implementation
// =============================================================================

= Implementation

== Crate Architecture

The system is implemented in approximately 400k lines of Rust across $tilde$45 workspace crates:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Crate*], [*Role*], [*Key Dependencies*]),
    [`macaroon`], [HMAC-SHA256 bearer tokens, attenuation, `CaveatType` polymorphic registry], [hmac, sha2],
    [`secrets`], [Key management, X25519, sealing, ChaCha20-Poly1305], [x25519-dalek, chacha20poly1305],
    [`token`], [Capability token lifecycle, validation], [macaroon, secrets],
    [`tokenizer`], [Token serialization, BIP39 HD derivation], [token],
    [`hints`], [BLS12-381 threshold signatures (real `ark_bls12_381` pairing + `hash_to_g2` + KZG)], [ark-bls12-381],
    [`blocklace`], [Cordial Miners $tau$ + Constitutional Consensus DAG + equivocation detection], [hints],
    [`commit`], [Poseidon2 Merkle trees, typed `Commitment<T>` framework], [p3-poseidon2],
    [`trace`], [STARK trace generation, AIR evaluation], [commit, p3-fri],
    [`circuit`], [DSL-only circuits, Effect VM AIR (~151 cols post-$gamma$.2 P1 + sovereign-witness P1), Kimchi backends, plonky3 recursion (`plonky3_recursion_impl` substrate)], [trace, commit, p3-uni-stark, kimchi],
    [`federation`], [Unified `Federation` type, `FederationCommittee`, `AttestedRoot` v3, `FederationReceipt`, `ThresholdQC`, real Shamir-over-GF(256)+ChaCha20-Poly1305 `threshold_decrypt`], [blocklace, hints],
    [`audit`], [Security audit trail, policy evaluation], [token],
    [`bridge`], [High-level API bridging proof + token layers, `BridgePresentationProof`, `BridgePredicateProof`], [circuit, token],
    [`wire`], [Network protocol, QUIC transport, hardening, `dfa_router`, `Authorization::CapTpDelivered` routing], [quinn, postcard],
    [`store`], [Persistent state: redb ACID, Blocklace blocks, ledger checkpoints, `KnownFederations` registry], [redb],
    [`cell`], [Cell state, c-lists, factories, sovereignty, `CellProgram::StateConstraint` (21+ variants), `WitnessedPredicate`, `peer_exchange`, `predicate` module], [types],
    [`turn`], [Turn execution, journal, atomicity, v3 canonical signing, `WitnessedReceipt` scope-1/scope-2, `SovereignCellWitness` with sequence + signature + optional `transition_proof`, `EncryptedTurn`], [cell, circuit],
    [`coord`], [2PC atomic coordination, causal DAG], [turn, federation],
    [`types`], [Shared types (`CellId`, `CapabilityRef`, `FederationId`, ...)], [],
    [`sdk`], [Client SDK, `AgentCipherclerk`, `AppCipherclerk` (six-method handle), presentation API, `captp_client`], [bridge, wire],
    [`wasm`], [WebAssembly bindings for Studio in-browser runtime], [sdk],
    [`node`], [Federation daemon (API + gossip sync), `node::state::trustless_intent_engine` (real threshold-decryption integration), `CapTpState::sync_known_federations`], [wire, federation],
    [`intent`], [Intent engine, `MatchSpec`, `trustless` 7-layer protocol (consumes real `federation::threshold_decrypt::combine_shares`), bond escrow, delay pool, gossip], [token, commit, federation],
    [`net`], [QUIC P2P, topic gossip, Plumtree, Dandelion++], [quinn],
    [`chain`], [EVM on-chain verification via SP1/Groth16, `EvmCredentialProof`], [sp1-sdk],
    [`dregg-dsl`], [Constraint DSL proc macros (multi-backend: AIR, Kimchi, Plonky3, ZKIR, SP1, Rust evaluator)], [syn, quote],
    [`dregg-dsl-runtime`], [DSL runtime: composition, verification, `WitnessedPredicateRegistry`], [circuit],
    [`dregg-dsl-tests`], [DSL integration tests and examples], [dregg-dsl],
    [`app-framework`], [Shared framework for Dragon's Egg applications: `EmbeddedExecutor`, `StarbridgeAppContext`, `AppCipherclerk` consumer], [sdk, node],
    [`discharge-gateway`], [Third-party caveat discharge service], [token, wire],
    [`verifier`], [Standalone `dregg-verifier` binary: per-cell STARK verify, `bilateral-pair` ($gamma$.2 cross-cell), `replay-chain` ($"WitnessedReceipt"$ chain), `verify-bundle` (scope-2)], [circuit, turn],
    [`teasting`], [Test assertions and property-based helpers], [proptest],
    [`preflight`], [Pre-deployment checks (routing, intents, solver, privacy)], [all],
    [`demo`], [End-to-end demo harness], [all],
    [`demo-agent`], [Agent simulation for demos], [sdk],
    [`tests`], [Integration test suite], [all],
  ),
  caption: [Core workspace crates. The newer entries (`predicate` module, `peer_exchange`, `EncryptedTurn`, `KnownFederations`, `verifier`, `EmbeddedExecutor`, `StarbridgeAppContext`) reflect the post-Silver-Vision integration work.],
)

== AppCipherclerk and Userspace Applications

Apps run as *pure userspace* through a narrow handle:

```rust
pub struct AppCipherclerk {
    /// The six methods that every app uses.
    pub fn submit_turn(&self, turn: Turn) -> Result<TurnReceipt, ...>;
    pub fn build_action(&self) -> ActionBuilder;
    pub fn current_cell(&self) -> &Cell;
    pub fn discover_intent(&self, pred: MatchSpec) -> Option<Intent>;
    pub fn present_handoff(&self, cert: HandoffCertificate) -> ...;
    pub fn create_from_factory(&self, fd: FactoryDescriptor, ...) -> CellId;
}
```

`AppCipherclerk` is the *only* surface most apps see. The framework also provides `EmbeddedExecutor` (a thin reactor running cells in-process) and `StarbridgeAppContext` (the in-browser equivalent backed by `wasm/src/runtime.rs`). The discipline that drove the design:

- No app-specific `Effect` variants (storage primitives are cell-program patterns).
- No `Authorization::Unchecked` placeholder turns (CI guard via Stage 8 P2.F).
- No `[0u8; 64]` stub signatures (the cclerk always holds a real signing key).
- No app-specific cclerk wrappers (`createFromFactory` is the universal cell-construction verb).

In the in-browser Studio runtime (`wasm/src/runtime.rs`), the *browser is the host executor*. Anything cleartext-inside the host executor is cleartext-inside the browser process. The browser is *not* the federation: a wasm node does not hold BLS shares and cannot produce `ThresholdQC`s. `dregg_federation` does not cross-compile to wasm32; federation operations are remote-only. Browser-to-browser sealing and browser-as-prover both work.

== Production Apps

Eight production-shaped applications drive the runtime. Several formerly-app-specific primitives have been retired in favor of the userspace pattern (the apps audit `APPS-AS-USERSPACE-AUDIT.md` enumerated each one):

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Application*], [*Domain*], [*Key cell-program patterns*]),
    [`gallery`], [NFT auction marketplace], [Commit-reveal via `PreimageGate`, anti-sniping via `FieldDeltaInRange`],
    [`stablecoin`], [Collateralized debt positions], [CDP creation, health-factor via `BoundedBy`, liquidation],
    [`amm`], [Automated market maker], [`SumEqualsAcross` for constant-product invariant, LP tokens via factory],
    [`orderbook`], [Central limit order book], [Verified matching engine, partial fills via `FieldDeltaInRange`],
    [`lending`], [Interest-bearing lending], [Accrual via `FieldDelta`, health monitoring],
    [`identity`], [Verifiable credentials], [Selective disclosure, anonymous presentation via blinded issuer ring],
    [`compute-exchange`], [Compute marketplace], [Capability-gated inference, sealed models, predicate matching],
    [`bounty-board`], [Task bounties], [Bond-backed quality assurance via escrow, adjudication via threshold],
    [`discord-bot`], [Discord integration], [Custodial cclerk, DeFi commands, presence attestation],
  ),
  caption: [Production applications. Each runs as `AppCipherclerk`-driven userspace; no app-specific `Effect` variants.],
)

A devnet deployment runs federation nodes with application services, Caddy TLS termination, and multi-architecture support (AMD64 + Graviton ARM64) via Docker Compose.

== Performance

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Latency*], [*Notes*]),
    [Macaroon verify (trusted)], [$tilde 8 mu s$], [HMAC-SHA256, constant-time],
    [Datalog evaluation], [$tilde 12 mu s$], [7 rules, 5 facts, bottom-up],
    [STARK proof generation], [$tilde 64 mu s$], [BabyBear4, real Poseidon2 constraints],
    [STARK verification], [$tilde 438 mu s$], [FRI proximity + Merkle check],
    [BLS threshold verify], [$tilde 32 "ms"$], [4-member committee],
    [End-to-end (wire)], [$tilde 560 "ms"$], [3-node QUIC, real STARK],
    [Proof size], [24 KiB], [Single fold step],
  ),
  caption: [Measured performance on Apple M-series. Non-optimized implementation.],
)

== Test Coverage

The test suite includes thousands of test functions covering:

- Unit tests for each crate (token validation, Datalog evaluation, Poseidon2 correctness, BLS aggregation, DSL compilation, threshold decryption combination).
- Integration tests spanning the full pipeline (token creation through STARK verification through turn execution through EVM wrapping).
- Property-based tests via proptest (conservation invariant, attenuation monotonicity, nullifier uniqueness, EffectMask narrowing, federation_id derivation determinism).
- End-to-end demo scenarios covering delegation, revocation, multi-party turns, intent fulfillment, pipeline execution, cross-federation swaps, cclerk interactions, factory spawning, sovereign cell transitions, `peer_exchange` direct exchange, and `CapTpDelivered` Turn production.
- DSL code generation tests (all backends produce correct output for a common test suite).
- Effect VM soundness tests (conservation violation detection, authority bypass attempts, state continuity breaks, sovereign-witness Phase 1 boundary).
- Consensus correctness tests (Blocklace + Cordial Miners under simulated network conditions).
- Security regression tests for every audit finding.
- Application integration tests (each app has its own test harness).
- Cross-federation bridge integration test (`federation/tests/cross_federation_bridge_receipt.rs`).
- The Silver Vision two-federation-handoff end-to-end demo (`demo/two-ai-handoff/`).

== Audit Findings (Closed)

Per the security audits (May 2026), critical findings have been addressed:

+ Turn executor verifies Ed25519 signatures via `verify_authorization`.
+ Turn executor verifies ZK proofs via the `ProofVerifier` trait.
+ Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`.
+ Wire protocol uses 64-byte signatures.
+ Integer overflow in excess tracking and note conservation replaced with `checked_add`/`checked_sub`.
+ `CreateCell` rejects non-zero balance (prevents value creation).
+ QC forgery bypass (aggregate_qc short-circuit) removed.
+ Body fact membership now proven via Poseidon2 Merkle STARKs (not just asserted).
+ Batch gamma Fiat-Shamir for correct KZG batch verification (fixed).
+ `federation_id` is now a commitment to the committee, not a random tag (Lane D).
+ `AttestedRoot.signing_message` includes `federation_id` + `blocklace_block_id` + `finality_round`.
+ Bridge `destination_federation` algebraically bound in AIR (closes T6).
+ `Authorization::Unchecked` guarded by CI grep (Stage 8 P2.F) with explicit carve-out list.
+ `pending_captp_turns` queue actually drained by executor (closes "CapTP messages never produce receipts" loop).
+ Trustless intent engine wired to real `federation::threshold_decrypt`---the `set_decrypted_intents` cleartext side-channel is replaced.

== Remaining work

- Stage 7 cont P1.C: verify the 4 CapTP AIR variants (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`) are real Merkle membership, not tautological.
- Trace-side boundary completeness for `{EFFECTS_HASH_GLOBAL, TURN_HASH, PRE/POST_STATE, PREVIOUS_RECEIPT_HASH}`---ACTOR_NONCE + EFFECTS_HASH_BASE row-0 binding landed; rest is followup-pass.
- Sovereign-witness AIR teeth: Phase 1 (signature binding) designed in `SOVEREIGN-WITNESS-AIR-DESIGN.md`; Phase 2 (`transition_proof` recursion) depends on Lane Golden-Edge's recursive verifier AIR.
- `EncryptedTurn` executor consumption (Layer 2 federation privacy): well-tested in isolation, not yet wired into the production executor path.
- $gamma$.2 Phase 2 joint aggregation AIR: PI-only Phase 1 closes the cross-cell binding gap for off-AIR verification; Phase 2 lifts the match-loop inside an AIR.
- Recursive aggregation: lift `plonky3_recursion_impl` past the `P3MerklePoseidon2Air` placeholder (Lane Golden-Edge Block 1), or commit to Kimchi/Pickles as the production-grade outer recursive layer.

== Command-Line Interface (`dregg`)

The `dregg` CLI provides full-citizen access to all runtime operations:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Subcommand*], [*Operations*]),
    [`cell`], [Create, inspect, sovereign/hosted transition, split, merge, migrate],
    [`turn`], [Build, sign, submit, inspect receipts, verify chains],
    [`cap`], [Mint, attenuate, delegate, revoke, present, verify proofs],
    [`cclerk`], [Create identity, import/export, backup mnemonic, balance],
    [`federation`], [Join, leave, status, peers, roots, epochs],
    [`register-federation`], [Add an entry to the local `KnownFederations` registry],
    [`namespace`], [Mount, resolve, list, register petname, rent, dispute],
    [`storage`], [Space bank status, quota, rent, erasure shards, GC status],
    [`directory`], [Edge names, proposed names, lookup, publish],
    [`proof`], [Generate, verify, export, compose, benchmark backends],
    [`route`], [Classify path, inspect DFA, test ACL, amend proposal],
    [`doctor`], [Diagnose node health, verify chain integrity, check connectivity],
  ),
  caption: [CLI subcommands. The `register-federation` subcommand is the operator's entry point for trust-root management.],
)

The standalone `dregg-verifier` binary (separate from `dregg`) provides:

- `verify <receipt>`: per-cell STARK verification against PI.
- `bilateral-pair <receipt_a> <receipt_b>`: $gamma$.2 cross-cell consistency check using canonical `transfer_id`/`grant_id`/`intro_id` recomputation.
- `replay-chain <chain-export>`: scope-1 verification across a `WitnessedReceipt` chain.
- `verify-bundle <chain-export>`: scope-2 verification, re-deriving the trace from inline witness data.

== Cryptographic Dependencies

- *Hash functions*: BLAKE3 (general purpose, MAC), Poseidon2 over BabyBear (STARK-friendly).
- *Signatures*: Ed25519 (node identity, cell auth), BLS12-381 (threshold QCs).
- *Encryption*: X25519 + ChaCha20-Poly1305 (sealer/unsealer, stealth addresses), Shamir-over-GF(256) + ChaCha20-Poly1305 (federation threshold decryption).
- *Commitments*: Pedersen over Ristretto (note values, per-asset-type generators).
- *Range proofs*: Bulletproofs over Ristretto (value range verification).
- *Proof systems*: Custom STARK (BabyBear/FRI), Plonky3 (`p3-uni-stark`), Kimchi/Pickles (Pasta/IPA).
- *EVM bridge*: SP1 zkVM wrapping to Groth16.
- *Key derivation*: BIP39 HD derivation for stable identity.
- *Network privacy*: Dandelion++ stem routing, delay pool with dummy traffic.
