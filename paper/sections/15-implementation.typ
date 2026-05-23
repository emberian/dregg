// =============================================================================
// Section 9: Implementation
// =============================================================================

= Implementation

== Crate Architecture

The system is implemented in approximately 355k lines of Rust across 41 workspace crates:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Crate*], [*Role*], [*Key Dependencies*]),
    [`macaroon`], [HMAC-SHA256 bearer tokens, attenuation], [hmac, sha2],
    [`secrets`], [Key management, X25519, sealing], [x25519-dalek, chacha20poly1305],
    [`token`], [Capability token lifecycle, validation], [macaroon, secrets],
    [`tokenizer`], [Token serialization, BIP39 HD derivation], [token],
    [`hints`], [BLS12-381 threshold signatures], [ark-bls12-381],
    [`blocklace`], [Blocklace DAG + Cordial Miners $tau$ + Constitutional Consensus], [hints],
    [`commit`], [Poseidon2 Merkle trees, commitments], [p3-poseidon2],
    [`trace`], [STARK trace generation, AIR evaluation], [commit, p3-fri],
    [`circuit`], [DSL-only circuits, 3 proof backends, Effect VM (14 effects)], [trace, commit, p3-uni-stark],
    [`federation`], [Consensus orchestration, revocation trees], [blocklace, hints],
    [`audit`], [Security audit trail, policy evaluation], [token],
    [`bridge`], [High-level API bridging proof + token layers], [circuit, token],
    [`wire`], [Network protocol, QUIC transport], [quinn, postcard],
    [`store`], [Persistent state: redb ACID, Blocklace blocks, ledger checkpoints], [redb],
    [`cell`], [Cell state, c-lists, factories, sovereignty], [types],
    [`turn`], [Turn execution, journal, atomicity], [cell, circuit],
    [`coord`], [2PC atomic coordination, causal DAG], [turn, federation],
    [`types`], [Shared types (CellId, CapabilityRef, etc.)], [],
    [`sdk`], [Client SDK, wallet, presentation API], [bridge, wire],
    [`wasm`], [WebAssembly bindings for browser extension], [sdk],
    [`node`], [Federation daemon (API + gossip sync)], [wire, federation],
    [`intent`], [Intent engine, matching, delay pool, gossip], [token, commit],
    [`net`], [QUIC P2P, topic gossip, Plumtree, Dandelion++], [quinn],
    [`chain`], [EVM on-chain verification via SP1/Groth16], [sp1-sdk],
    [`pyana-dsl`], [Constraint DSL proc macros (multi-backend)], [syn, quote],
    [`pyana-dsl-runtime`], [DSL runtime: composition, verification], [circuit],
    [`pyana-dsl-tests`], [DSL integration tests and examples], [pyana-dsl],
    [`app-framework`], [Shared framework for Pyana applications], [sdk, node],
    [`discharge-gateway`], [Third-party caveat discharge service], [token, wire],
    [`teasting`], [Test assertions and property-based helpers], [proptest],
    [`demo`], [End-to-end demo harness], [all],
    [`demo-agent`], [Agent simulation for demos], [sdk],
    [`tests`], [Integration test suite], [all],
  ),
  caption: [Core workspace crates (35 of 41). The remaining 6 are application crates in `apps/` (see below).],
)

== Applications

Eight production applications demonstrate the runtime's capabilities:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Application*], [*Domain*], [*Key Features*]),
    [`gallery`], [NFT auction marketplace], [Sealed-bid auctions, provenance tracking],
    [`stablecoin`], [Collateralized debt positions], [CDP creation, liquidation, price oracles],
    [`amm`], [Automated market maker], [Constant-product pools, LP tokens, fee tiers],
    [`orderbook`], [Central limit order book], [Verified matching engine, partial fills],
    [`lending`], [Interest-bearing lending], [Accrual computation, health factor monitoring],
    [`identity`], [Verifiable credentials], [Selective disclosure, anonymous presentation],
    [`compute-exchange`], [Compute marketplace], [Capability-gated inference, sealed models],
    [`bounty-board`], [Task bounties], [Bond-backed quality assurance, adjudication],
    [`discord-bot`], [Discord integration], [Custodial wallet, DeFi commands, presence attestation],
  ),
  caption: [Production applications. Each runs as an independent service communicating with federation nodes via the SDK.],
)

A devnet deployment runs 3 federation nodes with application services, Caddy TLS termination, and multi-architecture support (AMD64 + Graviton ARM64) via Docker Compose.

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
    [End-to-end (wire)], [$tilde 560 "ms"$], [3-node TCP, real STARK],
    [Proof size], [24 KiB], [Single fold step],
  ),
  caption: [Measured performance on Apple M-series. Non-optimized implementation.],
)

== Test Coverage

The test suite includes 4,046 test functions covering:

- Unit tests for each crate (token validation, Datalog evaluation, Poseidon2 correctness, BLS aggregation, DSL compilation)
- Integration tests spanning the full pipeline (token creation through STARK verification through turn execution through EVM wrapping)
- Property-based tests via proptest (conservation invariant, attenuation monotonicity, nullifier uniqueness, EffectMask narrowing)
- End-to-end demo scenarios (20+) covering delegation, revocation, multi-party turns, intent fulfillment, pipeline execution, cross-federation swaps, wallet interactions, factory spawning, and sovereign cell transitions
- DSL code generation tests (all backends produce correct output for a common test suite)
- Effect VM soundness tests (conservation violation detection, authority bypass attempts, state continuity breaks)
- Consensus correctness tests (Blocklace + Cordial Miners under 3--7 node simulated network conditions)
- Security regression tests for all audit findings
- Application integration tests (each app has its own test harness)

== Security Audit Findings (Resolved)

Per the security audit (May 2026), all critical findings have been addressed:

+ Turn executor now verifies Ed25519 signatures via `verify_authorization`.
+ Turn executor verifies ZK proofs via the `ProofVerifier` trait.
+ Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`.
+ Wire protocol uses 64-byte signatures (via `pyana-types`).
+ Integer overflow in excess tracking and note conservation replaced with `checked_add`/`checked_sub`.
+ `CreateCell` rejects non-zero balance (prevents value creation).
+ QC forgery bypass (aggregate_qc short-circuit) removed.
+ Body fact membership now proven via Poseidon2 Merkle STARKs (not just asserted).

== Command-Line Interface (`pyana`)

The `pyana` CLI provides full-citizen access to all runtime operations. It is the primary interface for operators, developers, and advanced users:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Subcommand*], [*Operations*]),
    [`cell`], [Create, inspect, sovereign/hosted transition, split, merge, migrate],
    [`turn`], [Build, sign, submit, inspect receipts, verify chains],
    [`cap`], [Mint, attenuate, delegate, revoke, present, verify proofs],
    [`wallet`], [Create identity, import/export, backup mnemonic, balance],
    [`federation`], [Join, leave, status, peers, roots, epochs],
    [`namespace`], [Mount, resolve, list, register petname, rent, dispute],
    [`storage`], [Space bank status, quota, rent, erasure shards, GC status],
    [`directory`], [Edge names, proposed names, lookup, publish],
    [`proof`], [Generate, verify, export, compose, benchmark backends],
    [`route`], [Classify path, inspect DFA, test ACL, amend proposal],
    [`doctor`], [Diagnose node health, verify chain integrity, check connectivity],
  ),
  caption: [CLI subcommands. Each maps to SDK operations; the CLI is a thin shell over the Rust SDK.],
)

Common workflows:

```
# Create a sovereign cell and mint a root capability
pyana wallet create --mnemonic
pyana cell create --sovereign --federation devnet.pyana.io:8420
pyana cap mint --service compute --root-key ./keys/root.key

# Delegate an attenuated capability to another agent
pyana cap delegate --token $TOKEN_ID --to $BOB_PUBKEY \
  --restrict service=compute,action=inference,budget=5000

# Submit a turn and verify the receipt
pyana turn build --target $CELL_ID --effect set-field:counter=42
pyana turn submit --signed
pyana turn verify-receipt --latest

# Bridge to Mina
pyana proof generate --backend kimchi --turn $TURN_HASH
pyana proof wrap-pickles --input $KIMCHI_PROOF

# Check node health
pyana doctor --full
```

== Cryptographic Dependencies

- *Hash functions*: BLAKE3 (general purpose, MAC), Poseidon2 over BabyBear (STARK-friendly)
- *Signatures*: Ed25519 (node identity, cell auth), BLS12-381 (threshold QCs)
- *Encryption*: X25519 + ChaCha20-Poly1305 (sealer/unsealer, stealth addresses)
- *Commitments*: Pedersen over Ristretto (note values, per-asset-type generators)
- *Range proofs*: Bulletproofs over Ristretto (value range verification)
- *Proof systems*: Custom STARK (BabyBear/FRI), Plonky3 (p3-uni-stark), Kimchi/Pickles (Pasta/IPA)
- *EVM bridge*: SP1 zkVM wrapping to Groth16
- *Key derivation*: BIP39 HD derivation for stable identity
- *Network privacy*: Dandelion++ stem routing, delay pool with dummy traffic
