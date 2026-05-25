# Phase 3a Decision: pyana-federation simulator cleanup

Follow-up to `AUDIT-morpheus-federation-blocklace.md` Phase 3. Records the
judgment call for the dead Morpheus-shaped BFT simulator types in
`pyana-federation` (`node` / `transport` modules) and their downstream
consumers.

## Recap

`pyana_federation::node` (`Federation`, `FederationNode`, `ConsensusConfig`,
`ConsensusState`, `ConsensusOrchestrator`, `ReconfigurationProposal`,
`PendingStateRoots`) and `pyana_federation::transport`
(`NetworkConsensusNode`, `TcpFederationTransport`, `LocalTransport`,
`FederationEnvelope`, `FederationTransport`, `TransportError`) are a
synchronous in-process BFT simulator that predates the live
`pyana-blocklace` engine. The live node does not use any of these types.

## Classification of each downstream consumer

| Consumer                                              | Verdict             | Rationale |
| ----------------------------------------------------- | ------------------- | --------- |
| `demo/sdk-consensus/src/main.rs`                      | KEEP (out-of-scope) | Explicitly out-of-scope per instructions. Drives `Federation::new` → `mint_token` → `submit_revocation` → `run_consensus_round` → `AttestedRoot` and persists the artifact. Forces the simulator types to remain in `pyana-federation` as a library surface. |
| `teasting/src/harness.rs`                             | KEEP-AS-TEST-INFRA  | `SimulationHarness` / `SimFederation` wrap `Federation` to provide a multi-federation, multi-node deterministic in-process test environment. Used by `teasting::{captp_sim, mesh_sim, router_sim, agent, fault, federation}`. This IS the testing setup the user asked about — already lives in a crate purpose-built for integration test simulation. |
| `teasting/src/federation.rs`                          | KEEP-AS-TEST-INFRA  | Thin convenience module re-exporting harness helpers (`quick_federation`, `dual_federation`, `drive_to_finalization`). Companion to harness.rs. |
| `teasting/src/fault.rs`                               | KEEP                | `FaultyNetwork` / `MessageBuffer` / `CrashableNode` / `SimpleRng`. Operates on `pyana_wire::message::WireMessage`, no dependency on the simulator types. Useful generic fault-injection layer. |
| `tests/src/byzantine.rs`                              | DELETE              | Module is feature-gated behind `__legacy_tests`. The feature is not defined anywhere in `tests/Cargo.toml` (or the workspace), so the file never compiles. Pure dead weight. The byzantine/fault scenarios it describes are better expressed against `teasting::fault::FaultyNetwork` (which is real, compiles, and has working tests). |
| `wire/src/federation_bridge.rs`                       | DELETE              | Wraps `NetworkConsensusNode` to plug into `SiloServer`. Audit already established it is off the live node path. Only call sites are its own tests and the multi_node demo. Dead. |
| `wire/src/bin/multi_node.rs`                          | DELETE              | Standalone TCP demo binary that strings together `TcpFederationTransport` + `FederationBridge` + STARK proofs. Not a test. Demonstrates a code path that isn't shipped. |
| `federation/src/bin/demo.rs`                          | DELETE              | Standalone CLI demo of the `Federation` API. Duplicates what `demo/sdk-consensus` already does. |
| `federation/src/bin/node.rs`                          | DELETE              | TCP federation node CLI for the dead simulator. The live node binary is `pyana-node` in `node/src/main.rs`. |
| `federation/tests/tcp_consensus.rs`                   | DELETE              | Integration test for `TcpFederationTransport`. Transport stays in-tree because of `demo/sdk-consensus`, but this test exercises the TCP path that has no real consumers. |
| `federation/benches/consensus_bench.rs`               | KEEP                | Benchmarks `FederationCommittee`, `MemberSecret`, `generate_test_committee` (BLS threshold sigs). These are LIVE utilities, not the simulator. |
| `demo-agent/examples/federation_bootstrap.rs`         | DELETE              | Pure example walking through `ConsensusConfig` / `ConsensusOrchestrator` / `ReconfigurationProposal` mechanics. Not exercised by any test. |
| `demo-agent/examples/federation_exit.rs`              | DELETE              | Example demonstrating "autarky" via `Federation::new` + `run_consensus_round` + receipt chains. The receipt-chain proof story is already covered by `ivc_attenuation_chain.rs`, `offline_verification.rs`, and `wallet_lifecycle.rs`. |
| `demo-agent/examples/unified_harness.rs`              | KEEP                | Uses `Federation::new` + `run_consensus_round` in `run_federation_bootstrap()`. Since the simulator types stay (because of `demo/sdk-consensus`), this example keeps compiling unchanged. |
| `demo-agent/examples/offline_verification.rs`         | KEEP                | Only uses `AttestedRoot`, `PublicKey`, `generate_keypair`, `sign`. All live primitives. |
| `demo-agent/examples/cross_federation_nft_swap.rs`    | KEEP                | "Federation" appears only as narrative text; the example doesn't import `pyana_federation` at all. |
| `demo/src/federation.rs`                              | KEEP                | Self-contained membership type (`Federation`, `FederationMember`, `FederationRole`); no dependency on the simulator. Already has an explanatory comment about it. |
| `demo/src/revocation.rs`                              | KEEP                | Uses `pyana_federation::RevocationTree` — live util. |

## Landing zone

The "testing setup" the user posed as a possibility — `teasting/` — already
exists, already wraps the simulator, and is already where multi-federation
test scenarios live. The right call is to leave the simulator types in
`pyana-federation` (forced by `demo/sdk-consensus`) and let `teasting` keep
consuming them as it does today. No code needs to move.

Considered but rejected:

- `protocol-tests/` — invariant property tests over single-crate APIs.
  Would have to grow a multi-node concept it doesn't currently have. Wrong
  shape.
- `preflight/` — operator-facing health checks (e.g. "are stores reachable
  before startup"). Wrong layer entirely; byzantine/fault scenarios are
  not preflight concerns.

## Acceptance

Phase 3b deletes only the dead-weight files listed above. The simulator
types remain part of `pyana-federation`'s public API because removing them
would break `demo/sdk-consensus`, which is out-of-scope this iteration.
The audit's deferred recommendation (split `pyana-federation` into
`pyana-federation-utils` + a `teasting`-owned simulator module) remains
deferred — it requires touching `demo/sdk-consensus`.

`cargo check --workspace --all-targets` must remain clean after Phase 3b.
