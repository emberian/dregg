# Backwater Crates Audit

> Read-only audit of workspace members that have not received a dedicated `AUDIT-*.md`.
> Scope: every member of the root `Cargo.toml` `[workspace] members` list that
> is not already covered by an existing `AUDIT-<name>.md` (i.e. not
> `cell`, `turn`, `captp`, `federation`, `blocklace`, `circuit`, `intent`,
> `node`, `sdk`, `wallet`, `wasm`, `dsl`, `extension`, etc.). One read-only
> pass; no source modifications.
>
> Generated 2026-05-24 against `main` @ commit `8a66164` (working tree has
> unrelated WIP edits to `circuit/`, `intent/`, `turn/`, `wire/`).

---

## `bridge/` (~10.7K LOC, 8 src modules + tests + benches)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 63 | Module wiring + re-exports |
| `authorize.rs` | 639 | Token state → `AuthorizationTrace` via Datalog |
| `convert.rs` | 680 | Token caveats → `FactSet` (delegates to `pyana_token::factset`) |
| `delta.rs` | 424 | Attenuation → `FoldDelta` |
| `present.rs` | **4161** | Presentation builder, `Predicate` enum, STARK prove/verify entry points |
| `verifier.rs` | 724 | `pyana_turn::ProofVerifier` impl (cfg `turn`) |
| `midnight.rs` | 895 | Midnight bridge wire types + validation |
| `midnight_observer.rs` | 739 | Async task watching finalised Midnight blocks |
| `mina.rs` | 1351 | Mina bridge (proof-carrying via Pickles) |
| `tests.rs` | 739 | E2E integration tests (mint → attenuate → prove → verify) |

- **Purpose.** The seam between the plaintext token world (`token`,
  `macaroon`) and the ZK proof world (`commit`, `trace`, `circuit`): token
  → FactSet, attenuation → FoldDelta, request → AuthorizationTrace, and the
  full presentation builder that produces STARK-backed presentation proofs.
  Also hosts the cross-chain interop bridges (Midnight, Mina) and the
  concrete `ProofVerifier` impl that the `TurnExecutor` actually plugs into.
- **Key types/functions.**
  - `present::BridgePresentationBuilder`, `BridgePresentationProof`,
    `WirePresentationProof`, `FederationRegistry` trait, plus the
    constellation of `prove_predicate_*`/`verify_predicate_*` and
    `verify_presentation_*` entry points.
  - `verifier::StarkProofVerifier` — concrete `pyana_turn::ProofVerifier`
    impl. Without this crate the executor has no real proof verifier.
  - `midnight::{MidnightBridgeConfig, FederationAttestation,
    PyanaToMidnightMessage, MidnightToPyanaMessage}` + `validate_*`.
  - `midnight_observer::run_observer` — async task watching finalised
    Midnight blocks and feeding events to the pyana federation.
  - `mina::{MinaBridgeState, StateAdvance, MinaFederationPresence}` —
    Pickles/Pasta proof-carrying bridge state for Mina.
  - `convert::{macaroon_to_factset, grant_to_facts}`,
    `delta::{attenuation_to_delta, further_attenuation_delta}`,
    `authorize::authorize_with_trace`.
- **Integration status.** Heavily depended on. Reverse deps:
  `circuit` (Mina dependency cycle via `pyana-circuit/mina` feature),
  `sdk`, `wire`, `preflight`, `teasting`, `tests`, `demo-agent`. This is
  the load-bearing connector between the token layer and the prover.
- **Dormant / load-bearing.** **Load-bearing core**, with one important
  caveat: `midnight`, `midnight_observer`, and `mina` are *design-complete
  scaffolding* — they define wire protocols, validation, and event flow,
  but the actual cross-chain submission/verification on the foreign chain
  is described in the doc comments rather than executed here (Midnight is
  observer-pattern with on-chain pieces external; Mina would land on a
  zkApp). The pyana-side validators are real.
- **Surprises.**
  - There is a hidden `mina` feature on `pyana-circuit` that activates the
    Mina-side path. Without it most of `bridge/src/mina.rs` is "just
    types".
  - `present.rs` is 4.1k LOC in a single file — the entire presentation
    builder pipeline plus all `verify_*` entry points and `Predicate`
    enum live there. That's the file you have to read if you want to
    understand how a token chain becomes a proof.
  - `verifier.rs` deliberately decouples the proof's "actual" public
    inputs (Merkle leaf+root) from the executor's notion of public
    inputs (federation root vk + action signing hash), with the binding
    enforced by the executor's fail-closed design. That's subtle and
    worth a security review focus.
- **Open issues.** `verifier.rs` notes that proof-to-action binding lives
  in the executor, not the circuit. If you ever loosen the executor's
  proof-ingress checks you silently lose action binding. This is a
  load-bearing comment, not enforced by types.
- **Recommendation.** Keep. Promote `present.rs` to be split into at
  least `present/builder.rs`, `present/predicate.rs`, `present/verify.rs`
  — at 4k LOC it dominates the crate. Promote bridge security model into
  a dedicated `AUDIT-bridge.md`.

## `coord/` (~6.9K LOC, 6 src modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 68 | Module wiring + re-exports |
| `atomic.rs` | 1113 | 2PC: `AtomicForest`, `Coordinator`, `Participant`, votes |
| `budget.rs` | 1237 | Bounded counter / `BudgetCoordinator` / `FastUnlockManager` |
| `causal.rs` | 408 | Layer 1 causal chaining (wraps `pyana_types::CausalDag`) |
| `error.rs` | 221 | `CoordError` enum + `From` impls |
| `serde_sig.rs` | 25 | Serde adapter for ed25519 signatures inside coord messages |
| `shared_budget.rs` | 1897 | `SharedResourceBudget` (Stingray pre-allocative) |
| `tests.rs` | 1897 | Roughly 1:1 test mass with implementation |

- **Purpose.** "Two-layer turn coordination": Layer 1 = causal chaining
  DAG of turn hashes (no consensus needed); Layer 2 = atomic multi-party
  turn 2PC (propose → vote → commit/abort) with threshold QCs. Also
  hosts the *bounded-counter* primitives (`BudgetCoordinator`,
  `SharedResourceBudget`) adapted from Stingray, and a fast-unlock
  manager for 2PC abort recovery.
- **Key types/functions.**
  - `atomic::{AtomicForest, Coordinator, Participant, ProposeMessage,
    Vote, Decision, CommitMessage, AbortMessage}` — the 2PC state machine.
  - `causal::{CausalTurn, CausalDag, CausalLedger}` — Layer-1 DAG. The
    `CausalDag` itself is re-exported from `pyana_types`; this crate adds
    the turn-aware wrappers.
  - `budget::{BudgetCoordinator, BudgetSlice, FastUnlockManager,
    UnlockCertificate, UnlockRequest}` — distributed bounded counter à
    la Stingray. Closely related to (but architecturally distinct from)
    `audit::budget::BudgetEnforcer`.
  - `shared_budget::{SharedResourceBudget, SharedBudgetObserver,
    ResourceState, DebitResolution}` — generalises the bounded-counter
    pattern from "one agent across silos" to "one resource across
    agents".
- **Integration status.** Used by `node`, `wasm`, `demo-agent`, and
  `teasting`. `node/src/state.rs` and `node/src/api.rs` import
  `Coordinator`, `AtomicForest`, `BudgetCoordinator` — this is the live
  multi-party path the node runs.
- **Dormant / load-bearing.** Load-bearing for multi-party turns and
  budgets. The `shared_budget` module appears to be newer (the
  Stingray-style invariant `allowance = balance * (f+1) / (2f+1)` is
  documented in the module head) and may be partially aspirational —
  consumers outside `coord/src/tests.rs` are sparse; only `demo-agent`
  examples and `node/src/state.rs` import the *original* `BudgetCoordinator`.
- **Surprises.**
  - `serde_sig.rs` is 25 LOC. It's a serde adapter for ed25519
    signatures inside coordination messages. Easy to miss.
  - The tests file is 1.9k LOC — same size as `shared_budget.rs`
    itself. Test mass roughly matches implementation mass.
  - The "Stingray" lineage is documented in the module doc string but
    invisible from the API names. If you greppped for "Stingray" you'd
    find it; otherwise the resemblance to `arXiv:2501.06531` is hidden.
- **Open issues.** No TODOs / stubs visible. The crate looks production-
  grade in shape; whether the 2PC is truly Byzantine-tolerant is
  beyond this audit's scope (no AUDIT-coord.md exists).
- **Recommendation.** Keep, audit. This is the most under-documented
  important crate in the workspace — multi-party atomicity and budget
  enforcement are *both* live in node and *neither* has its own
  AUDIT-*.md. Promote to `AUDIT-coord.md` is a priority.

## `audit/` (~2.5K LOC, 5 src modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 84 | Re-exports + module wiring; deep doc preamble |
| `event.rs` | 169 | `UsageEvent`, `AuditReceipt`, `InclusionProof` |
| `log.rs` | 783 | `AuditLog`: 4-ary Merkle tree, append/prove/snapshot |
| `proofs.rs` | 541 | 5 privacy-preserving proofs (Count/Range/Consistency/Budget/LastUse) |
| `budget.rs` | 393 | `BudgetEnforcer` ties audit log to budget specs |
| `tests.rs` | 486 | Coverage roughly half of impl LOC |

- **Purpose.** Privacy-preserving append-only audit log for *token usage
  events* — distinct from the `AUDIT-*.md` doc artefacts. Implements
  `UsageEvent` records, a 4-ary Merkle-committed log, and four canonical
  proofs (`CountProof`, `RangeProof`, `ConsistencyProof`, `BudgetProof`,
  `LastUseProof`). Plus a `BudgetEnforcer` that ties usage limits to
  the audit log.
- **Key types/functions.**
  - `event::{UsageEvent, AuditReceipt, InclusionProof}`
  - `log::{AuditLog, LogSnapshot}` — backed by `pyana_commit::hash`'s
    4-ary Merkle primitives (tree depth 12 → 16M event cap).
  - `proofs::{BudgetProof, ConsistencyProof, CountProof, RangeProof,
    LastUseProof}` — each independently verifiable from the published
    root.
  - `budget::{BudgetEnforcer, BudgetSpec, BudgetExhausted}`.
- **Integration status.** Only direct workspace dep: `store/` (behind
  `audit-bridge` feature, default-on). Also imported by
  `tests/src/budget.rs`. Nothing else in the workspace touches it.
- **Dormant / load-bearing.** **Borderline dormant.** It compiles, it
  has 486 LOC of tests, and `store/` mirrors its events into redb via
  `store/src/audit.rs`. But no app, no node path, no executor surface
  drives it — usage events are not emitted anywhere in the executor
  or token-presentation paths. It's a self-consistent module waiting
  for an integration that hasn't happened.
- **Surprises.**
  - The naming collision with the AUDIT-*.md document set is hostile.
    `pyana-audit` is the *budget/usage* audit log, not a self-audit
    framework.
  - The crate predates `coord::budget::BudgetCoordinator`. There are
    now **two** "BudgetEnforcer/Coordinator"-shaped types in the
    workspace, with different invariants (audit budget = single-agent
    usage counter with proofs; coord budget = distributed bounded
    counter with rebalance).
- **Open issues.** No active TODOs but the integration gap is itself an
  open question: who is supposed to call `BudgetEnforcer::record_use`?
- **Recommendation.** Either wire it into the executor (the token
  presentation path is the natural hook — every presentation is a
  `UsageEvent`) or fold its proof scaffolding into `coord::budget` and
  delete this crate. Document the gap explicitly.

## `protocol-tests/` (~2.9K LOC, 5 invariants + 4 generators)

- **Purpose.** Property-based testing of *protocol invariants* (as
  opposed to scenario-based unit tests living in each crate). Each
  module under `invariants/` picks one claimed property (balance
  conservation, nonce monotonicity, receipt-chain integrity, capability
  attenuation, facet attenuation, sealed-field integrity, permission
  enforcement, effect-VM differential) and drives the executor against
  it with `proptest` strategies from `generators/`.
- **Key types/functions.**
  - `Invariant` trait (documentation hook, no enforcement).
  - `generators::{cell, turn, effect, capability}` — proptest strategies
    that emit shape-valid executor inputs.
  - `invariants::effect_vm_differential` (1.2k LOC) — runtime executor
    vs Effect-VM AIR cross-check; explicitly categorises mismatches as
    CONSISTENT / PASSTHROUGH GAP / REAL BUG and marks passthrough gaps
    `#[ignore]` with explanations.
- **Integration status.** Zero reverse deps. Pure cargo-test target.
- **Dormant / load-bearing.** Load-bearing for *correctness assurance*,
  but invisible to production code. Per the lib.rs doc the thesis is
  "audit-discovered bugs were protocol-level, not scenario-level" — so
  this is the crate that's supposed to catch the next class of bugs
  unit tests miss.
- **Surprises.**
  - `effect_vm_differential` distinguishes between "AIR is conservative
    (sound)" and "AIR is incomplete (some state mutations not covered)"
    — it documents tripwires for AIR expansion rather than treating
    every divergence as a bug. That's an unusual and welcome design.
  - lib.rs lists capability_attenuation/facet_attenuation/
    sealed_field_integrity/permission_enforcement as "STUB (next
    session)" but the files exist and run; the doc comment is stale.
- **Open issues.** Stale "STUB" markers in lib.rs vs. real implementation
  files. The differential module's `#[ignore]`d tests need follow-up
  whenever the Effect-VM AIR grows.
- **Recommendation.** Keep. Update the stale STUB comments. Add a CI job
  that runs `cargo test -p pyana-protocol-tests -- --include-ignored`
  weekly so passthrough-gap tripwires don't drift.

## `observability/` (1 file, 378 LOC, binary only)

- **Purpose.** Single-file binary that builds a minimal realistic turn
  (one `Transfer`), runs the executor, runs the Effect-VM trace
  generator, runs `stark::prove` + `stark::verify`, and emits a JSON
  document covering pre/post state, effects, public inputs, and proof
  hashes. Explicitly self-identified as the **seed crate for the
  in-browser turn explorer**.
- **Key types/functions.** All file-scoped helpers (`make_cell`,
  `project_turn_effects_for_cell`, `render_effects`, `cell_state_view`)
  and a `main` that dumps JSON to stdout.
- **Integration status.** Zero reverse deps. Standalone binary.
- **Dormant / load-bearing.** **Dormant scaffolding.** It compiles, runs
  one turn, prints JSON. Nothing consumes the JSON yet (no in-browser
  explorer in tree).
- **Surprises.**
  - It deliberately *duplicates* the executor's private
    `convert_turn_effects_to_vm` projection rather than widening
    visibility. That's clean isolation but means it has to be kept in
    sync by hand.
  - There is no `src/lib.rs`, only `src/main.rs`. The Cargo.toml's
    library/binary surface is binary-only.
  - The description says "seed crate for the browser explorer" but
    there's no WASM target and no browser code anywhere. The crate's
    *output* is intended for a browser; the crate itself is `cargo run`.
- **Open issues.** Doc comment is honest: "It is **not** the executor's
  internal trace stream — that would require instrumenting `executor.rs`
  itself (a separate, larger lift)."
- **Recommendation.** Either build the browser explorer that consumes
  this JSON (promote), or stop maintaining it (delete). As-is it's a
  pleasant proof-of-concept that isn't paying rent. If kept, document
  what consumes its output.

## `store/` (~4.5K LOC, 11 modules + tests)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 645 | `PersistentStore`, `StoreError`, hex helpers, note-insertion API |
| `audit.rs` | 303 | `StoredAuditEvent` (mirror of `pyana_audit::event`) |
| `blocklace_store.rs` | 224 | `BlocklaceMeta` + incremental block persistence |
| `checkpoint.rs` | 186 | Periodic checkpoint scheduling |
| `federation.rs` | 330 | `StoredAttestedRoot`, revocation set persistence |
| `keys.rs` | 244 | AEAD-encrypted signing keys (ChaCha20-Poly1305 / BLAKE3 KDF) |
| `ledger_store.rs` | 225 | `LedgerCheckpoint` for fast restart |
| `note_tree.rs` | 431 | `NoteTree`, `PersistentNullifierSet` (BLAKE3 + Poseidon2) |
| `poseidon2_note_tree.rs` | 194 | Poseidon2-only path |
| `recovery.rs` | 167 | `RecoveredState` + `recover_federation_state` |
| `tables.rs` | 135 | Private redb table definitions |
| `tokens.rs` | 145 | `TokenChain`, `StoredFoldStep` |
| `tests.rs` | 1246 | Coverage |

- **Purpose.** Persistent storage backend for "all the things that used
  to be in-memory": token chains, federation state (revocations,
  attested roots), key management, audit log mirroring, ledger
  checkpoints, blocklace, note commitment tree, nullifier set. Backed
  by `redb` (embedded ACID KV). Signing keys are AEAD-encrypted at rest.
  **Distinct from `storage/`** — that crate is the *user-facing*
  programmable queue / inbox / pubsub / relay layer with KZG sampling.
  `store/` is internal node persistence.
- **Key types/functions.**
  - `PersistentStore` — root handle, opens redb file.
  - `note_tree::{NoteTree, PersistentNullifierSet}`,
    `poseidon2_note_tree::Poseidon2NoteTree` — dual BLAKE3 + Poseidon2
    note commitment trees (BLAKE3 for non-ZK consensus, Poseidon2 for
    proof generation).
  - `blocklace_store::{BlocklaceMeta}` — incremental block persistence
    so the DAG reconstructs without re-syncing.
  - `federation::{StoredAttestedRoot}`,
    `recovery::{RecoveredState, recover_federation_state}`,
    `ledger_store::{LedgerCheckpoint}`.
  - `audit::StoredAuditEvent` (audit-bridge feature).
  - `tokens::{TokenChain, StoredFoldStep}`.
- **Integration status.** Used by `node` (real), `wire` (one type),
  `teasting`. `node/src/state.rs` does both `pyana_store::PersistentStore`
  and `Poseidon2NoteTree` — this is the live persistence path.
- **Dormant / load-bearing.** Load-bearing for `node`. The `audit-bridge`
  feature is the only thing keeping `audit/` alive as a non-test dep.
- **Surprises.**
  - The crate exports its own `StoreError` enum with manual `From`
    impls (no `thiserror`), and inlines hex encode/decode helpers
    rather than using the `hex` crate. Small style inconsistency.
  - Tables module is private; everything goes through `lib.rs`'s
    `PersistentStore` API. Good encapsulation.
  - The double-tree (BLAKE3 + Poseidon2) shows up here, in `commit/`,
    and in `circuit/` — duplicating the maintenance cost across crates.
- **Open issues.** No major TODOs. `ledger_store.rs` notes that "the
  blocklace replay layer, when implemented, will fill in the gap" if no
  checkpoint exists — that "when implemented" is a real gap, not a doc
  artefact.
- **Recommendation.** Keep. Consider whether the name "store" vs
  "storage" is sustainable; see §5.

## `cod/` (21 LOC, single stub fn)

- **Purpose.** Doc comment: "Closable Overspending Detector for pyana
  shared resources." Acronym belongs with `coord::shared_budget` —
  COD = close → open → debit, the reactive complement to the
  pre-allocative bounded-counter scheme.
- **Key types/functions.** `pub fn version() -> &'static str`. Returns
  `env!("CARGO_PKG_VERSION")`. That is the entire crate.
- **Integration status.** Zero reverse deps. Not even in the workspace
  `[workspace.dependencies]` block; not referenced by any other crate.
- **Dormant / load-bearing.** **Pure scaffolding stub.** Lib.rs literally
  says "Scaffolding stub: this crate exists in the workspace so its
  eventual API surface (close + detect on a shared budget) can be wired
  in without later having to rearrange workspace membership."
- **Surprises.** The crate is admitted to be empty by its own doc
  comment. That's honest but disconcerting; nothing in cargo or CI
  rules out forgetting about it forever.
- **Open issues.** Entire intended functionality is "TODO: actual
  implementation."
- **Recommendation.** **Delete or merge.** Either fold the
  close-open-debit logic into `coord::shared_budget` (where the
  comparison with COD is already documented at the module level) and
  drop the workspace member, or commit to writing the real crate this
  session. As-is it's a workspace squatter.

## `discharge-gateway/` (~460 LOC, lib + binary)

- **Purpose.** Standalone HTTP service that wraps
  `pyana_macaroon::DischargeGateway` and exposes three axum routes:
  `POST /discharge`, `GET /conditions`, `GET /health`. Loads its
  evaluator stack (allowlist, payment, rate-limit, proof-required,
  time-window, etc.) from a TOML config or CLI args.
- **Key types/functions.**
  - `GatewayConfig`, `GatewaySettings`, `ConditionConfig`,
    `build_gateway` (lib API).
  - `main()` + `Cli` (binary).
- **Integration status.** Reverse deps: only `discharge-gateway`'s own
  binary depends on its lib. Nothing else in the workspace pulls it in.
  The *core* discharge logic it wraps lives in
  `macaroon::discharge_gateway` (1100 LOC) and IS depended on by `token`
  and `bridge` indirectly via macaroon — but this *service* wrapper has
  no in-tree consumer.
- **Dormant / load-bearing.** Service binary is dormant in the sense
  that no other workspace crate launches it; it's a deployable artifact.
  The underlying logic in `macaroon/` is load-bearing.
- **Surprises.**
  - The crate name has no `pyana-` prefix, breaking the convention used
    by `pyana-bridge`, `pyana-coord`, etc.
  - The lib target is `discharge_gateway_service` (with underscore) but
    the binary is `discharge-gateway` (with hyphen). Workable but
    confusing.
  - Imports from `pyana_macaroon` even though the crate name is just
    `macaroon` — i.e. the crate uses the rust-name alias.
- **Open issues.** None obvious in the code; the gap is that no
  deployment doc references this binary.
- **Recommendation.** Keep as a deployable binary, but either rename to
  `pyana-discharge-gateway` for naming consistency or document why it's
  exempt from the prefix rule. Add a deploy/ entry.

## `commit/` (~5.4K LOC, 11 modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 299 | Top-level exports + crate doc |
| `accumulator.rs` | 984 | `PolynomialAccumulator` (BabyBear^4) + ext-field arith |
| `fact.rs` | 214 | `Fact` (predicate + ≤3 terms as field elements) |
| `factset.rs` | 358 | `FactSet` ordered set with Merkle commitment |
| `field.rs` | 140 | `FieldElement` 253-bit value, encoding |
| `fold.rs` | 533 | `FoldDelta`, `FoldDeltaBuilder`, `FoldVerification` |
| `hash.rs` | 129 | 4-ary hash primitives (`hash_leaf`, `hash_node`, `empty_hash_at_depth`) |
| `merkle.rs` | 912 | BLAKE3-backed sparse 4-ary Merkle tree |
| `poseidon2_tree.rs` | 679 | Poseidon2-backed 4-ary Merkle tree (BabyBear) |
| `state.rs` | 260 | `TokenState` = FactSet + symbols + commitment |
| `symbol.rs` | 173 | `SymbolTable` (BLAKE3-based string interning) |
| `typed.rs` | 739 | `Commitment4<S>` + `CommitmentSchema` (dual-form framework) |

- **Purpose.** Core *commitment primitives* for the token system:
  `Fact`, `FactSet`, `FoldDelta`, `SymbolTable`, `FieldElement`,
  4-ary BLAKE3 Merkle tree, 4-ary Poseidon2 Merkle tree,
  polynomial-evaluation accumulator (BabyBear^4) for O(1) non-
  membership proofs, and the typed dual-form `Commitment` framework
  (blake3 + poseidon2 with cross-binding).
- **Key types/functions.**
  - `Fact`, `FactSet`, `TokenState`, `FoldDelta`, `FoldDeltaBuilder`.
  - `merkle::{MerkleTree, MerkleProof, SurvivalWitness}`,
    `poseidon2_tree::{Poseidon2MerkleTree, Poseidon2MerkleProof}`.
  - `accumulator::{PolynomialAccumulator, AccumulatorWitness,
    BabyBear4}` — quartic-extension accumulator for non-membership.
  - `typed::{Commitment4, CommitmentSchema}` — the typed dual-form
    framework from `DESIGN-commitment-framework.md`.
  - `symbol::SymbolTable`, `field::FieldElement`, `hash::*`.
- **Integration status.** Massive reverse dep graph: `audit`, `bridge`,
  `cell`, `demo`, `demo-agent`, `federation`, `intent`, `node`,
  `preflight`, `sdk`, `store`, `teasting`, `token`, `turn`, `wasm`,
  `wire`. This is one of the most-imported workspace members.
- **Dormant / load-bearing.** **Foundational.** Without this nothing
  proves anything.
- **Surprises.**
  - `accumulator.rs` (984 LOC) implements a *separate* BabyBear^4
    extension field arithmetic stack from the one in `pyana-circuit`.
    Two extension-field implementations for the same field is a
    soundness footgun if they ever diverge.
  - The doc comment notes "Currently uses BLAKE3 as a placeholder for
    the algebraic Poseidon hash" for the original 4-ary tree, but the
    Poseidon2 tree already exists in a separate file. The placeholder
    has outlived its placeholder status.
  - `typed.rs` (739 LOC) is the *typed* commitment framework with
    `CommitmentSchema` trait, but its consumers are limited — most
    of the workspace still works with the untyped `Fact`/`FactSet`.
- **Open issues.** Migration to Poseidon2 only is incomplete; the dual
  BLAKE3+Poseidon2 maintenance burden runs through `commit`, `store`,
  `circuit`. The accumulator's BabyBear4 vs circuit's BabyBear4 is a
  consolidation candidate.
- **Recommendation.** Keep. **Audit-deeper** the BabyBear4 duplication
  (cross-check `commit::accumulator::BabyBear4` against
  `pyana-circuit`'s extension field for behavioural equivalence). Promote
  the dual-form Commitment framework adoption (it's defined but
  underused).

## `trace/` (~3.9K LOC, 7 modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 22 | Module wiring + re-exports |
| `types.rs` | 255 | `Term`, `Fact`, `Rule`, `BodyAtom`, `AuthorizationRequest`, `AuthorizationTrace`, `Conclusion` |
| `eval.rs` | 527 | `Evaluator`: bottom-up Datalog with proof recording |
| `verify.rs` | 420 | `verify_trace`, `verify_trace_with_request` |
| `policy.rs` | **1216** | Standard + secure policy rule sets, named rule IDs |
| `check.rs` | 232 | Guard evaluation (`MemberOf`, time comparisons) |
| `tests.rs` | 1246 | Coverage |

- **Purpose.** Datalog derivation traces — the data model that captures
  *how* an authorization decision was reached, suitable for ZK proving.
  Standalone reference evaluator (`Evaluator`), a verifier
  (`verify_trace`), the canonical pyana policy rule set
  (`standard_policy`, `secure_policy`), and the check evaluator.
- **Key types/functions.**
  - `types::{Term, Fact, Rule, BodyAtom, AuthorizationRequest,
    AuthorizationTrace, Conclusion, ...}`.
  - `eval::Evaluator` — bottom-up Datalog with proof recording.
  - `verify::{verify_trace, verify_trace_with_request}`.
  - `policy::{standard_policy, secure_policy, rule_ids}` — 12 named
    pyana policy rules (`APP_ACTION`, `SERVICE_ACTION_SECURE`,
    `NOT_BEFORE_DENY`, `BUDGET_OK`, `REVOCATION_DENY`, etc.).
  - `check::eval_check` — guard evaluation (e.g. `MemberOf`, time
    comparisons).
- **Integration status.** Reverse deps: `bridge`, `circuit`, `intent`,
  `sdk`, `token`, `wasm`, `demo-agent`.
- **Dormant / load-bearing.** Load-bearing — every token authorization
  pass that goes through `token::datalog_verify` produces a `trace`
  AST. The "trustless" path STARK-proves the trace exactly as it stands.
- **Surprises.**
  - `policy.rs` is 1.2k LOC of named rules with deeply specific
    semantics (BUDGET_OK, NOT_BEFORE_DENY, REVOCATION_DENY, etc.).
    This is effectively pyana's *policy language* — and it lives in a
    rules constructor function, not a configuration file.
  - There are *two* policies (`standard_policy` and `secure_policy`)
    where the secure one uses exact hash matching (`MemberOf`) and the
    standard one uses substring matching (`Contains`). The default
    should be obviously secure.
  - The crate has *no* dependency on `pyana-commit` or any other pyana
    crate — only `blake3` + `serde`. This is the cleanest reusable
    module in the auth stack.
- **Open issues.** None obvious. The policy duality (standard vs
  secure) deserves a unit test that asserts every consumer uses
  `secure_policy()`.
- **Recommendation.** Keep, audit. Make `secure_policy` the default and
  deprecate `standard_policy`. Promote `policy.rs` into a dedicated
  `AUDIT-trace-policy.md` to document the rule semantics.

## `token/` (~8.1K LOC, 12 modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 110 | Module wiring + feature-gated re-exports |
| `traits.rs` | 210 | `AuthToken`, `TokenVerifier`, `AuthRequest`, `Capability`, `Attenuation`, `BudgetSpec`, `TokenClearance`, `FeatureGlobSpec` |
| `action_set.rs` | 408 | `ActionId`, `ActionSet` typed action vocabulary |
| `format.rs` | 221 | `TokenFormat::detect` self-describing prefixes (`em2_`/`eb2_`) |
| `error.rs` | 53 | `TokenError` enum |
| `macaroon_backend.rs` | 254 | `MacaroonToken` (cfg `macaroon` + `rand-deps`) |
| `biscuit_backend.rs` | 400 | `BiscuitToken` (cfg `biscuit`) |
| `pyana.rs` | 538 | Pyana-specific token semantics, `pyana` re-export module |
| `pyana_caveats.rs` | 1603 | 16 typed pyana caveat IDs + `verify_caveats` collective check |
| `factset.rs` | 422 | Canonical caveat → FactSet/SymbolTable encoder |
| `datalog_verify.rs` | **2897** | Canonical Datalog verification path (sole source of truth) |
| `revocation.rs` | 999 | `RevocationRegistry` (sorted Merkle) + deprecated cuckoo filter |

- **Purpose.** Unified abstraction over two token formats (HMAC
  macaroons and Ed25519 biscuits) plus the *canonical* pyana caveat set,
  the *canonical* Datalog verification path (which subsumes the older
  imperative `verify_caveats`), and the revocation registry.
- **Key types/functions.**
  - `traits::{AuthToken, TokenVerifier, AuthRequest, Capability,
    Attenuation, BudgetSpec, TokenClearance, FeatureGlobSpec}`.
  - `MacaroonToken` (in `macaroon_backend.rs`), `BiscuitToken` (in
    `biscuit_backend.rs`).
  - `pyana_caveats::{verify_caveats, PyanaGrant, ...}` — 16 typed pyana
    caveat IDs (App, Service, Feature, ValidityWindow, ConfineUser,
    OAuthProvider, OAuthScope, FromMachine, Command, FeatureGlob,
    Budget, Revocable, Organization).
  - `datalog_verify::{DatalogVerifyResult, verify_token_datalog}` —
    canonical authorization evaluator.
  - `revocation::{RevocationRegistry, RevocationFilter,
    AttestedRevocationRoot, NonMembershipProof}`.
  - `factset::caveat_set_to_factset` (1k LOC of fact encoding).
  - `format::TokenFormat` (prefix-based self-describing tokens:
    `em2_` macaroon, `eb2_` biscuit).
- **Integration status.** Pervasive. Reverse deps include
  `apps/privacy-voting`, `apps/subscription`, `bridge`, `circuit`,
  `circuit/sp1-guest`, `demo-agent`, `demo/sdk-consensus`, `intent`,
  `preflight`, `sdk`, `store`, `teasting`, `tests`, `trace` (wait —
  this is reversed; `trace` does NOT depend on `token`, but the grep
  matches `trace = { path = "../trace" }` inside `token/Cargo.toml`),
  `wasm`, `wire`.
- **Dormant / load-bearing.** Load-bearing core.
- **Surprises.**
  - `datalog_verify.rs` is 2.9k LOC. Half the crate is the canonical
    verifier.
  - `revocation.rs` retains the legacy cuckoo `RevocationFilter` even
    though it's `#[deprecated]` — to provide a pre-filter for high-
    throughput deployments. Documented but easy to misuse.
  - Crate name is just `token` (no `pyana-` prefix), library name is
    `pyana_token`. Matches the inconsistency with `macaroon`,
    `tokenizer`, `secrets`, `hints`.
  - 16 caveat IDs in `pyana_caveats.rs` — this is the canonical pyana
    permission vocabulary, but it's table-formatted in a doc comment
    not a registry.
- **Open issues.** Deprecated cuckoo filter is still default-on (rand-
  deps feature includes scalable_cuckoo_filter). Datalog vs imperative
  consistency: the doc says Datalog "replaces" the imperative path but
  both files still exist.
- **Recommendation.** Keep. Promote `AUDIT-token-caveats.md` to lock
  the 16-ID assignment. Consider feature-gating the deprecated cuckoo
  path to off-by-default.

## `tokenizer/` (~1.2K LOC, 5 modules + bin + service-integration tests)

- **Purpose.** **NOT** an NLP tokenizer. It's a *credential-isolation
  daemon*: a sealed-secret encryption service. The tokenizer holds an
  X25519 private key; the runtime only has the public key and encrypts
  secrets before storage. Plaintext credentials are never seen by guest
  code. Protocol uses postcard over a local TCP socket.
- **Key types/functions.**
  - `TokenizerService` — daemon side (`service.rs`, 477 LOC).
  - `TokenizerClient` — runtime side.
  - `SealedSecret`, `TokenizerKeypair` (X25519 + ChaCha20-Poly1305 box).
  - `protocol::{Request, Response}` — over postcard.
- **Integration status.** Reverse deps: workspace root `[workspace.
  dependencies]` only. Nothing actually `use`s it. The binary
  `pyana-tokenizer` exists; nothing in tree spawns it.
- **Dormant / load-bearing.** **Dormant.** Compiles, has tests, has a
  binary, but nothing in the rest of the workspace imports it. The
  conceptual seam ("guests can't see secrets") is good architecture
  that isn't wired up.
- **Surprises.**
  - The name "tokenizer" is highly confusing in any ML-adjacent context.
    Renaming to `pyana-sealer` or `pyana-secret-daemon` would clarify.
  - The protocol is over local TCP — there's no in-process API. If you
    wanted to use this from `node` you'd need to spawn a daemon.
  - This *parallels* the role of `secrets` (which is in-process secret
    storage). Two crates, two non-overlapping ways of being a secret
    boundary.
- **Open issues.** Zero in-tree consumers is the open issue.
- **Recommendation.** Either wire into the executor (the natural hook
  is the OAuth caveat path that needs to dereference secret material
  without exposing it to guest code) or delete. Rename if kept.

## `macaroon/` (~3.0K LOC, 12 modules)

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 67 | Re-exports + crate doc |
| `access.rs` | 23 | `Access` trait |
| `action.rs` | 213 | `Action` bitmask resource permissions |
| `caveat.rs` | 209 | `Caveat` trait, `CaveatSet`, wire encoding |
| `caveat_3p.rs` | 235 | `ThirdPartyCaveat` (tickets, discharge, encryption) |
| `crypto.rs` | 186 | HMAC-SHA256 chain + XChaCha20-Poly1305 sealing |
| `discharge_gateway.rs` | **1096** | Evaluator stack (Allowlist/Payment/RateLimit/TimeWindow/ProofRequired/AllOf/AnyOf) |
| `error.rs` | 62 | `MacaroonError` enum |
| `format.rs` | 110 | MsgPack + base64url + `em2_` prefix |
| `macaroon.rs` | 626 | Core `Macaroon` type: create/attenuate/verify/bind/discharge |
| `resource.rs` | 173 | `ResourceSet<ID, Action>` typed permission map |

- **Purpose.** Pyana's *Fly.io-flavoured* macaroon implementation.
  HMAC-chained bearer tokens with first-party caveats, third-party
  caveats (ticket/discharge with XChaCha20-Poly1305 sealing),
  attenuation, and a 1100-LOC `discharge_gateway` module of pluggable
  condition evaluators.
- **Key types/functions.**
  - `Macaroon::{new, attenuate, verify, bind}`,
    `caveat::{Caveat, CaveatSet, WireCaveat}`,
    `caveat_3p::ThirdPartyCaveat`.
  - `discharge_gateway::{DischargeGateway, DischargeRequest,
    DischargeResponse, AllowlistEvaluator, PaymentEvaluator,
    RateLimitEvaluator, TimeWindowEvaluator, ProofRequiredEvaluator,
    AllOfEvaluator, AnyOfEvaluator, AlwaysAllow,
    VerifyingProofEvaluator, ProofVerifierFn, ConditionEvaluator}`.
  - `format::{em2_*}` — base64url + msgpack wire format with `em2_`
    prefix.
  - `crypto::{hmac_chain, seal_xchacha20poly1305}`.
  - `access::Access` trait, `action::Action` bitmask,
    `resource::ResourceSet<ID, Action>`.
- **Integration status.** Reverse deps: `bridge`, `discharge-gateway`,
  `node`, `sdk`, `teasting`, `token`, `wasm`. Token uses macaroon as
  *one* of its two backends.
- **Dormant / load-bearing.** Load-bearing. Macaroons are the workhorse
  token format on hot paths (~0.5μs verify).
- **Surprises.**
  - The 1100-LOC `discharge_gateway` evaluator module lives *here*, not
    in the `discharge-gateway/` crate. The latter just HTTP-wraps this.
  - `caveat_3p.rs` (235 LOC) implements full third-party caveats —
    encrypted root keys, separate verifier service, etc. This is a
    large feature most users may never know exists.
  - `resource.rs` (173 LOC) is generic `ResourceSet<ID, Action>` — an
    independent typed permission registry sibling to the caveat system.
- **Open issues.** None visible in the code. Crate is mature.
- **Recommendation.** Keep. The discharge_gateway module's ancestry
  (Fly.io's flyio-rust-macaroon, mentioned in `lib.rs`) deserves an
  attribution doc.

## `secrets/` (~830 LOC, 4 modules + integration tests)

- **Purpose.** Pluggable secret storage. Two backends: encrypted file
  store (AES-256-GCM, `~/.pyana/secrets/`, 0600 perms) and OS keychain
  (via `keyring`). `CompositeStore` tries keychain first, falls back
  to files.
- **Key types/functions.**
  - `SecretStore` trait, `SecretId`, `SecretMetadata`, `SecretValue`.
  - `EncryptedFileStore` (358 LOC) — file-backed AES-256-GCM.
  - `KeychainStore` (117 LOC, feature-gated).
  - `CompositeStore` — try-then-fallback wrapper.
- **Integration status.** Reverse deps: workspace root only. No `use
  pyana_secrets` outside the crate's own tests. Zero in-tree consumers.
- **Dormant / load-bearing.** **Dormant.** Like `tokenizer`, this is a
  well-formed credential-handling primitive that nothing wires into.
- **Surprises.**
  - The crate name is `secrets` (no prefix), library name `pyana_secrets`.
  - This *overlaps in role* with `tokenizer` (which seals secrets via
    a daemon) — but the threat models differ. `secrets` is "secret at
    rest"; `tokenizer` is "secret never decrypted in guest memory".
  - `tempfile` is a *runtime* dep (not just dev), which suggests the
    encrypted store uses atomic write via temp+rename. Reasonable.
- **Open issues.** Zero consumers is the issue.
- **Recommendation.** Wire into the node's OAuth/credential paths or
  delete. If retained, document the relationship with `tokenizer`.

## `hints/` (~3.8K LOC, 5 src modules + examples + benches; edition 2021)

- **Purpose.** **Out-of-tree library, vendored.** Implements weighted
  threshold signatures over BLS12-381 + KZG using the *hints* scheme
  (key insight: each party precomputes a "hint" that doesn't depend on
  other parties' keys, allowing committee setup amortisation). Sub-
  module `snark` adds the prover/verifier.
- **Key types/functions.**
  - `SecretKey`, `PublicKey`, `Hint`, `GlobalData`, `UniverseSetup`,
    `Aggregator`, `Verifier`, `PartialSignature`, `Signature`,
    `Proof`, `AggregationKey`, `VerifierKey`.
  - `setup_universe`, `generate_hint`, `sign`, `sign_aggregate`,
    `verify_aggregate`.
- **Integration status.** Reverse deps: `federation`. Heavily used in
  `federation::threshold` to produce constant-size quorum certs.
- **Dormant / load-bearing.** **Load-bearing for federation.** Without
  hints, federation QCs would be N×64 byte ed25519 aggregates instead
  of a single BLS sig.
- **Surprises.**
  - Edition is `2021`, not the workspace's `2024`. Author block is
    `["hints authors", "ember arlynx <ember@hellas.ai>"]` — this is a
    fork.
  - Description: "A library for computing weighted threshold
    signatures". Categories `cryptography`, keywords `cryptography,
    finite-fields, elliptic-curves, pairing`. Self-contained.
  - Crate name is `hints`, no prefix, plural noun.
  - `[profile.test] opt-level = 2` — this crate forces release-ish
    test compilation, presumably because the BLS pairing tests are
    glacial in debug.
- **Open issues.** Edition skew (2021 vs workspace 2024). The
  `[profile.test]` override is workspace-wide via cascading and can
  confuse other crates' debug-test workflows.
- **Recommendation.** Keep. Audit the edition-2021 island; consider
  whether forking it as `pyana-hints` and upstreaming patches is worth
  the unification.

## `net/` (~4.5K LOC, 5 modules + demo bin) — `pyana-net`

### File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 34 | Module wiring + re-exports |
| `node.rs` | 960 | `PeerNode`: quinn endpoint, mTLS, rate-limit, allowlist |
| `gossip.rs` | **2602** | Plumtree eager/lazy push gossip (single file) |
| `message.rs` | 452 | `PeerMessage` enum (PublishTurn / RequestTurn / AttestedRoot / RevocationGossip / cell-sync) |
| `causal.rs` | 403 | `CausalDag` for happened-before of turns |
| `bin/demo.rs` | — | `pyana-p2p-demo` standalone runner |



- **Purpose.** P2P networking via QUIC (quinn). Implements direct mTLS
  QUIC connections (`PeerNode`), Plumtree-inspired hybrid eager/lazy-
  push gossip (`GossipNetwork`), pyana wire protocol (`PeerMessage`),
  and a causal DAG of turn dependencies (`CausalDag`).
- **Key types/functions.**
  - `PeerNode`, `PeerNodeConfig`, `PeerConnection`, `NodeId`,
    `AllowlistVerifier`, `ConnectionRateLimiter`.
  - `GossipNetwork`, `GossipEvent`, `TopicHandle`, `MessageStream`,
    `MessagePhase`.
  - `PeerMessage` — wire enum: PublishTurn, RequestTurn, TurnResponse,
    AttestedRootUpdate, RevocationGossip, etc.
  - `CausalDag`, `DagEntry`, `HashMismatch`.
- **Integration status.** Reverse deps: `node`, `teasting`, workspace
  root.
- **Dormant / load-bearing.** **Load-bearing for `node`.** This is how
  pyana nodes talk to each other.
- **Surprises.**
  - The crate documents "designed for iroh, but iroh 0.96 has pre-
    release dependency conflicts (ed25519-dalek 3.0.0-pre.1 vs pkcs8)"
    — i.e. the workspace ducked an upgrade. Quinn was a tactical
    substitution.
  - `gossip.rs` is 2.6k LOC of single-file Plumtree. Worth a dedicated
    audit.
  - The CausalDag here is *separate* from `pyana_types::CausalDag`
    (which `coord/src/causal.rs` re-exports). Two CausalDag types in
    the workspace, possibly redundant.
- **Open issues.** iroh return path. Two CausalDags.
- **Recommendation.** Keep. Audit-deeper the gossip.rs (security
  surface). Reconcile `net::CausalDag` vs `pyana_types::CausalDag`.

## `preflight/` (~6.3K LOC, 26 check modules + report + main)

### Check modules (sorted by LOC, descending)

| File | LOC | Subsystem |
|------|-----|-----------|
| `turns.rs` | 466 | transfer, set_field, grant, multi_effect, nonce, conservation, budget_gate |
| `effect_vm.rs` | 399 | trace_generation, 14 effect types, effects_hash, net_delta, custom dispatch, adversarial overdraft |
| `proofs.rs` | 387 | STARK + tamper rejection + derivation + effect_vm + IVC (+ wrong-root) |
| `solver.rs` | 337 | Ring 2-party, 3-party, validation rejects, generalized swap |
| `blocklace.rs` | 324 | DAG ordering / finality |
| `caps.rs` | 319 | Capability lifecycle + attenuation |
| `storage.rs` | 300 | Merkle queue, cap inbox, programmable queue, WAL recovery, dedup, pubsub |
| `demo_agent.rs` | 284 | End-to-end multi-agent flow |
| `composition.rs` | 272 | AND composition, IVC chain, aggregation |
| `sovereign.rs` | 263 | Factory deploy, peer exchange, multi-party atomic, IVC history |
| `captp.rs` | 259 | CapTP session exercise |
| `apps.rs` | 254 | Gated by `apps-sdk` feature (pyana-sdk broken) |
| `privacy.rs` | 231 | Privacy invariants |
| `intents.rs` | 195 | Intent solver |
| `wire.rs` | 191 | Wire-format checks |
| `cli.rs` | 179 | CLI integration |
| `nameservice.rs` | 174 | Nameservice apps check |
| `backends.rs` | 173 | Cross-backend proof |
| `routing.rs` | 162 | DFA routing |
| `node.rs` | 158 | Node lifecycle |
| `federation.rs` | 148 | Federation boot + revocation |
| `relay.rs` | 148 | Relay operators (storage subset) |
| `cells.rs` | 122 | Cell lifecycle |
| `bridges.rs` | 80 | Bridge checks |
| `boot.rs` | 43 | Boot smoke |
| `mod.rs` | 25 | Module wiring |



- **Purpose.** "Golden Master Preflight" — end-to-end integration test
  gate for devnet → testnet → mainnet promotion. Twenty-six subsystem
  check modules, each invoked from `main.rs::run_all_subsystems`.
  Each `checks::<X>::run()` returns a `Vec<CheckResult>` and the
  aggregate `PreflightReport` decides whether the build is fit to ship.
- **Key types/functions.**
  - `main.rs::run_all_subsystems` — the manifest of what gets
    preflighted (boot, cells, turns, proofs, effect_vm, privacy, caps,
    intents, apps, composition, federation, blocklace, sovereign,
    backends, captp, routing, storage, nameservice, bridges, demo_agent,
    cli, wire, node, relay, solver).
  - `report::{PreflightReport, SubsystemResult, CheckResult,
    run_subsystem, run_check}`.
- **Integration status.** Reverse deps: zero. Binary only.
- **Dormant / load-bearing.** **Load-bearing for release engineering.**
  The user noted that "Lane I trimmed it for the slop retirement",
  suggesting AMM/lending/orderbook/etc. checks were excised when those
  apps moved to `starbridge-apps/`. The remaining surface is real:
  turns (466), proofs (387), effect_vm (399), solver (337), blocklace
  (324), caps (319), storage (300).
- **Surprises.**
  - The `apps-sdk` feature gates `pyana-gallery` because *pyana-sdk
    is currently broken* ("missing `custom_program_proofs` field in
    Turn"). Preflight documents the breakage in its own Cargo.toml.
  - `relay.rs` (148 LOC) checks `MeteredRelay` and `SpaceBank` from
    the *user-facing* `storage` crate; `storage.rs` (300 LOC) checks
    the programmable queue / cap inbox / WAL / dedup / pubsub. The
    division of labour between these check files is by storage
    feature, not by crate.
  - The Cargo.toml explicitly lists which apps were retired in the
    migration to `starbridge-apps/` — useful provenance for future
    spelunkers.
- **Open issues.** SDK-broken comment is the largest in-tree TODO
  signal; preflight can run without it via `--no-default-features`.
- **Recommendation.** Keep. Treat preflight as the canonical "what is
  pyana made of" manifest — `main.rs::run_all_subsystems` is the most
  useful single file for onboarding.

## `teasting/` (~15K LOC, 9 src modules + 29 integration test files)

### File-level breakdown (src/)

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 44 | Module wiring |
| `harness.rs` | 348 | `SimulationHarness`, `SimFederation`, `SimNode`, `SimClock` |
| `agent.rs` | 131 | `SimAgent` — name + `AgentWallet` + ergonomic test helpers |
| `assertions.rs` | 263 | Domain-specific assertions (proof valid / verifies / forges fail) |
| `captp_sim.rs` | 400 | `SimCapTpSession` — VecDeque-channel CapTP exercising real sessions/GC |
| `fault.rs` | 760 | `FaultyNetwork` + `CrashableNode` + `Partition` (seeded RNG) |
| `federation.rs` | 31 | `quick_federation`, `dual_federation`, `drive_to_finalization` |
| `mesh_sim.rs` | 371 | In-process service mesh wrapping the real DFA router |
| `router_sim.rs` | 183 | `SimRouter` wrapping `pyana_wire::dfa_router::GovernedRouter` |

### Test catalogue (tests/)

```
captp_sessions, consensus_liveness, cross_federation, defi_primitives,
dfa_routing, effect_vm_captp, escrow_lifecycle, fast_path_vs_consensus,
fault_byzantine, fault_crash, fault_ordering, fault_partition,
fuzz_captp, fuzz_governance, fuzz_turns,
invariants, multi_asset_fees, negation_proofs, predicate_soundness,
privacy_unlinkability, proof_round_trip, pubsub, relay_operators,
revocation_propagation, service_mesh,
storage_faults, storage_lifecycle, storage_with_captp, token_lifecycle
```

- **Purpose.** "Tease testing — if it wasn't a test it would be the
  live chain". Multi-node simulation harness for end-to-end testing of
  authorization, consensus, privacy, and faults. Uses in-process gossip
  rather than real networking; exercises real federation, executor,
  CapTP, DFA, storage, blocklace code paths.
- **Key types/functions.**
  - `harness::{SimulationHarness, SimFederation, SimNode, SimClock}`.
  - `captp_sim::SimCapTpSession` — bilateral CapTP over VecDeque
    channels, exercising real CapSession + SwissTable + GC.
  - `fault::{FaultyNetwork, CrashableNode, Partition, SimpleRng}` —
    seeded fault injection (drop / reorder / duplicate / delay /
    crash / partition). Deterministic by seed.
  - `mesh_sim`, `router_sim` (wraps `GovernedRouter` from
    `pyana_wire::dfa_router`), `assertions`, `agent`.
  - 29 integration test files including: captp_sessions, dfa_routing,
    consensus_liveness, cross_federation, escrow_lifecycle, fault_*
    (byzantine/crash/ordering/partition), fuzz_captp/governance/turns,
    invariants, multi_asset_fees, predicate_soundness, privacy_
    unlinkability, proof_round_trip, pubsub, relay_operators,
    revocation_propagation, service_mesh, storage_*, token_lifecycle.
- **Integration status.** Zero reverse deps. Pure integration suite.
- **Dormant / load-bearing.** **Load-bearing for correctness.** This is
  the workspace's largest test surface (~15K LOC, more than any single
  production crate). The integration tests in teasting/tests/ are the
  closest pyana has to a system test.
- **Surprises.**
  - `fault.rs` (760 LOC) is a fully seeded deterministic fault injector
    — same seed → same failure sequence. Eliminates flaky tests by
    construction if the production code is deterministic.
  - `captp_sim.rs` (400 LOC) reuses *real* `CapSession`/`SwissTable`/
    `ExportGcManager`/`ImportGcManager` from `pyana-captp` — only the
    transport is simulated. This is the right move: gives you E2E
    coverage of GC and refcounting without a TCP socket.
  - The test file list is the most informative tour of pyana's
    correctness claims — read `ls teasting/tests/` for the contract.
- **Open issues.** None obvious. The test file naming convention
  (fault_byzantine vs fault_crash vs fault_ordering vs fault_partition)
  is good; consider an index file.
- **Recommendation.** Keep, audit. **Promote teasting/tests/ index to
  a top-level doc** — currently the only way to know what's tested
  end-to-end is to `ls`.

---

# Synthesis

## §1. Dependency graph (high-level)

```
                        ┌──────────────┐
                        │   commit/    │ ◄── audit, bridge, cell, demo*,
                        └──────┬───────┘     federation, intent, node,
                               │             preflight, sdk, store, token,
                               │             turn, wasm, wire
                  ┌────────────┼────────────┐
                  ▼            ▼            ▼
              trace/        circuit/      cell/
                │            │ ▲            │
                │            │ │            │
                ▼            │ │            ▼
              token/ ────────┘ └──────── turn/
                │ ▲                          │
                │ │                          │
                ▼ │                          ▼
            macaroon/                      coord/
                                             │
                                             ▼
                                           node/ ◄── store/, net/

bridge/  ── pulls in: commit, trace, circuit, turn, dsl-runtime, token, macaroon
coord/   ── pulls in: cell, blocklace, turn, types
store/   ── pulls in: types, commit, cell, circuit, blocklace, federation, audit
preflight/ ── pulls in basically everything plus apps
teasting/  ── pulls in basically everything except apps

audit/         ◄── only store/, tests/
secrets/       ◄── nothing
tokenizer/     ◄── nothing
cod/           ◄── nothing
discharge-gateway/  ◄── nothing (binary)
observability/      ◄── nothing (binary)
protocol-tests/     ◄── nothing (test-only)
hints/         ◄── federation/
net/           ◄── node/, teasting/
```

Five distinct "tiers":

1. **Foundation:** `commit/`, `trace/`, `types/` (excluded), `cell/`
   (excluded), `circuit/` (excluded). Everyone depends on these.
2. **Token system:** `macaroon/`, `token/`, `bridge/`. The full
   authorization stack.
3. **Coordination:** `coord/`, `net/`, `federation/` (excluded),
   `captp/` (excluded), `blocklace/` (excluded). Multi-party + network.
4. **Persistence:** `store/`, `storage/` (excluded). Distinct concerns:
   `store/` = node-internal persistence, `storage/` = user-facing
   programmable queues.
5. **Aspirational / dormant:** `secrets/`, `tokenizer/`, `cod/`,
   `observability/`, `audit/`, `discharge-gateway/`. Compiles, mostly
   tested, mostly unused.

## §2. The dormant cluster

These crates have zero or near-zero production consumers. In order of
deadness:

- **`cod/`** — 21 LOC stub by its own admission. **Delete or implement.**
  No reverse deps. Just `pub fn version()`.
- **`tokenizer/`** — 1.2K LOC daemon for sealed-secret isolation. No
  in-tree consumer outside its own bin/tests. **Wire into the OAuth
  caveat path or delete.** Also rename if kept (the ML overload is
  hostile).
- **`secrets/`** — 830 LOC encrypted-file + keychain store. No in-tree
  consumer. **Wire into the node credential path or delete.**
- **`observability/`** — 378 LOC single-file JSON dumper. No browser
  consumer in tree. **Build the browser explorer or delete.**
- **`audit/`** — 2.5K LOC privacy-preserving audit log + budget
  enforcer. One in-tree consumer (`store/`, behind `audit-bridge`
  feature) which is itself a mirror, not a driver. **Wire into the
  executor's presentation path or fold into `coord::budget`.**
- **`discharge-gateway/`** — 460 LOC HTTP wrapper around
  `macaroon::discharge_gateway`. Real deploy target but no in-tree
  consumer. **Keep** as a release artifact but document deployment.
- **`protocol-tests/`** — 2.9K LOC of proptest invariants. Test-only,
  no production consumer **by design**. **Keep.**

Net recommendation: definitely delete `cod/`. Either-or for `tokenizer/`
+ `secrets/` + `observability/`. Make a decision on `audit/`'s seam to
the executor or fold it in.

## §3. The load-bearing cluster (beyond cell/turn/captp/federation/blocklace/circuit)

The five most critical crates in this audit's scope:

1. **`commit/`** — Foundational primitives (`Fact`, `FoldDelta`,
   Merkle, Poseidon2 tree, BabyBear4 accumulator). 16+ reverse deps.
   *Everything* commits things.
2. **`bridge/`** — The connector between plaintext tokens and ZK proofs.
   Without `verifier.rs` the executor has no real `ProofVerifier`.
   Also hosts the cross-chain bridges (Midnight, Mina).
3. **`token/`** — 8K LOC unified token abstraction, the canonical
   pyana caveat set, the canonical Datalog verification path. The
   actual user-facing auth model.
4. **`coord/`** — Multi-party turn atomicity (2PC), Stingray-style
   bounded counters, fast unlock. Node consumes it. No `AUDIT-coord.md`.
5. **`trace/`** — Datalog derivation traces and the canonical pyana
   policy ruleset (`secure_policy`, 12 named rules). Has no other
   pyana deps; very clean.

Honourable mentions: **`macaroon/`** (discharge gateway evaluator stack
lives here), **`net/`** (P2P transport for `node`), **`hints/`** (BLS
threshold sigs for federation QCs).

## §4. Surprises

1. **`cod/` is an admitted stub.** The crate exists in the workspace
   "so its eventual API surface can be wired in without later having
   to rearrange workspace membership." That's a *new* workspace
   anti-pattern: empty-by-design.
2. **`audit/` is plumbed but unused.** The crate is 2.5K LOC of
   well-tested code, has a `store::audit::StoredAuditEvent` mirror,
   and *nothing emits usage events*. Two parallel BudgetEnforcer
   types exist (audit vs coord) with different semantics.
3. **`tokenizer/` is not a tokenizer.** It's a sealed-secrets daemon
   with X25519+ChaCha20-Poly1305. The name is hostile.
4. **`observability/` produces JSON for a browser explorer that does
   not exist.** Self-documented as "the seed crate for the in-browser
   turn explorer". The seed has been planted; the tree has not grown.
5. **There are two `CausalDag` types in the workspace** —
   `net::CausalDag` and `pyana_types::CausalDag` (the latter
   re-exported by `coord::causal`). Possibly redundant.
6. **There are two BabyBear^4 implementations** —
   `commit::accumulator::BabyBear4` and the one in `pyana-circuit`.
   Soundness footgun if they ever diverge.
7. **`hints/` is edition 2021 and overrides `[profile.test]
   opt-level = 2`**. An island in an otherwise edition-2024 workspace.
8. **`preflight/Cargo.toml` admits `pyana-sdk` is broken.** It
   feature-gates the gallery app behind `apps-sdk` because the SDK
   is missing a `custom_program_proofs` field on `Turn`. This is the
   loudest in-tree "things are not quite finished" signal.

## §5. Crates that should merge

- **`cod/` → `coord::shared_budget`.** The close-open-debit pattern is
  already documented at the top of `coord/src/shared_budget.rs` as the
  reactive complement to the bounded-counter pre-allocative scheme.
  Drop the empty crate; the design comparison can live where the
  implementation lives.
- **`audit/` → `coord::budget` (or executor).** The two BudgetEnforcer-
  shaped types ought to live together. The audit log + privacy proofs
  are the harder half; reuse them from a single BudgetEnforcer that
  records into either the in-memory bounded-counter ledger
  (coord-style) or the persistent Merkle log (audit-style) depending
  on configuration.
- **`net::CausalDag` ↔ `pyana_types::CausalDag`.** Two implementations
  of the same data structure. Pick one; have `net::` use the canonical
  type from `pyana_types`.
- **`commit::accumulator::BabyBear4` ↔ `pyana-circuit`'s BabyBear4.**
  Likely the same field with two arithmetic implementations. Audit
  for behavioural equivalence; merge if equivalent.
- **`store/` and `storage/` should NOT merge,** despite the name
  collision. They have legitimately different roles: `store/` =
  node-internal persistence (redb-backed), `storage/` = user-facing
  programmable queues with KZG sampling. But one of them should
  rename. `store/` → `pyana-persist` would be clearer.
- **`tokenizer/` and `secrets/` should be unified or one should be
  deleted.** Both are credential-handling primitives with different
  threat models. If both are kept, document the boundary explicitly.
- **`discharge-gateway/` could fold into `macaroon/` as a `service`
  feature.** Currently it's a 460-LOC binary that imports the 1100-LOC
  evaluator stack from `macaroon`. The split is by deployment shape,
  not by abstraction.

## §6. Composition with the rest of pyana

In Silver Vision terms ("E2E from intent to receipt"):

- **Token issuance / authorization:** `macaroon/` → `token/` →
  `trace/` (Datalog evaluation) → `bridge/` (FactSet, FoldDelta,
  AuthorizationTrace) → `circuit/` (STARK proof) → `verifier` in
  `bridge/` → `turn/` executor.
- **Multi-party turn execution:** `cell/` / `turn/` → `coord/`
  (2PC + bounded counters) → `federation/` (threshold QCs via
  `hints/`) → `blocklace/` (DAG ordering) → `store/` (persistence).
- **Networking:** `net/` (QUIC + gossip) → `captp/` (object protocol)
  → `node/` orchestrates.
- **Cross-chain:** `bridge::midnight*` (observer + attestation),
  `bridge::mina` (proof-carrying via Pickles), `discharge-gateway/`
  (third-party caveat clearing).
- **Test surface:** `protocol-tests/` (invariants over generators) +
  `teasting/` (multi-node sim) + `preflight/` (release gate, runs
  EVERY subsystem). Three independent layers.
- **Dormant tier:** `audit/`, `secrets/`, `tokenizer/`, `cod/`,
  `observability/` are *designed-for* slots that the live code does
  not yet occupy. They are pre-allocated workspace memberships in
  hopes of future integration.

The composition is dense at the core (circuit / commit / trace / token
/ bridge / turn / cell) and frayed at the edges (the dormant tier).

## §7. Recommendations

**Delete now:**

- `cod/` — empty stub. Fold the close-open-debit concept comment into
  `coord::shared_budget` and drop the workspace member.

**Decide-or-delete this session:**

- `tokenizer/` — wire into OAuth secret path or delete. Rename if kept.
- `secrets/` — wire into node credential paths or delete. Document
  relationship with `tokenizer/` if both retained.
- `observability/` — ship the browser explorer or delete. As-is it's
  a pleasant prototype that ages.

**Merge / reconcile:**

- `audit/` into `coord::budget` OR wire its usage-event hooks into the
  token presentation path. Pick a story.
- `net::CausalDag` ↔ `pyana_types::CausalDag` — pick one.
- `commit::accumulator::BabyBear4` ↔ `pyana-circuit::BabyBear4` —
  cross-audit and merge if equivalent.

**Rename:**

- `store/` → `pyana-persist` (or similar) to disambiguate from
  `storage/`.
- `discharge-gateway/` → `pyana-discharge-gateway` for naming
  consistency.
- `tokenizer/` → `pyana-sealer` if kept.

**Promote (write a dedicated AUDIT-*.md):**

- `coord/` — multi-party 2PC + Stingray budgets are live in node, zero
  audit doc. **Highest priority.**
- `bridge/` — the STARK-verifier seam plus two cross-chain protocols.
- `trace/` — policy.rs defines the de facto pyana policy language.
- `net/` — Plumtree gossip security surface.
- `teasting/tests/` — index the integration test contract.

**Audit-deeper (security focus):**

- `bridge::verifier` — proof-to-action binding is comment-enforced.
- `bridge::midnight_observer` — observation pattern trust assumptions.
- `net::gossip` — eager/lazy push security under Byzantine peers.
- `coord::shared_budget` — Stingray invariant `slice = balance *
  (f+1) / (2f+1)` and its blocklace integration.
- `trace::policy::secure_policy` vs `standard_policy` — assert
  consumers use secure.

**Document:**

- `preflight/src/main.rs::run_all_subsystems` is the most useful
  single-file inventory of pyana's surface. Link it from CLAUDE.md.
- The 16 caveat IDs in `token::pyana_caveats` are the canonical pyana
  permission vocabulary. Lock the IDs.
- The 12 named policy rules in `trace::policy::rule_ids` are the
  canonical pyana policy language. Lock the rule IDs.

## §8. Open questions for designer

1. **Is `cod/` ever happening?** If yes, when, by whom, and what does
   the close-open-debit detector actually do that
   `coord::shared_budget::SharedBudgetObserver` does not?
2. **Is `audit/` the audit story?** The crate's `BudgetEnforcer` and
   `coord/`'s `BudgetCoordinator` are two coexisting universes. Pick
   one. If `audit/` is the long-term home, what wires it into the
   presentation path?
3. **Is the browser explorer real?** `observability/` exists for it.
   Plans?
4. **What's the `tokenizer/` story?** Is the sealed-secret daemon
   meant to be spawned by `node`, run as a sidecar, or be a per-user
   foreground process? Without a hook in `node` or `sdk`, it's
   architecture-as-aspiration.
5. **Why is `pyana-sdk` "currently broken"?** Preflight's Cargo.toml
   says so. Is this acknowledged elsewhere, or is the SDK quietly
   rotting?
6. **Two CausalDags — which is canonical?** `net::CausalDag` vs
   `pyana_types::CausalDag`. The former predates or postdates the
   latter; which lives?
7. **Two BabyBear4s — which is canonical?** Same question, soundness
   stakes higher.
8. **Is the `hints/` fork upstreamable?** Edition 2021 island, fork
   authorship. Is the plan to merge back, or to keep a divergent
   `pyana-hints`?
9. **`store/` vs `storage/`: who renames?** Both names are taken and
   both crates are live. This is going to confuse a new contributor
   approximately monthly forever.
10. **`secure_policy` vs `standard_policy` — why both?** Why is the
    insecure one still default-constructed and selectable? Is there a
    deployment that needs the substring-matching path?
11. **`protocol-tests/lib.rs` claims most invariants are STUB but the
    files exist.** Is the doc stale, or are the files placeholders that
    pass vacuously?

---

# Annex A — Security surface notes (per crate)

This annex captures security-shaped observations from the code I read.
None of it is a finding; it's a list of "places where a future
AUDIT-*.md should focus first."

### `bridge/`

- `verifier.rs::StarkProofVerifier` decouples the proof's "actual"
  public inputs (Merkle leaf + root) from the executor's notion of
  public inputs (federation root vk + action signing hash). The
  binding to "this specific action" is enforced not by the circuit
  but by the **executor's fail-closed design**. If the executor's
  ingress checks are weakened, action binding silently degrades to
  "presenter holds *some* valid token chain from *some* federated
  issuer" with no per-action tie. This is the single most load-bearing
  comment in `bridge/verifier.rs` and it should be lifted into a
  property test against the executor.
- `present.rs` defines `UnsafeLocalOnlyMarker`. Grep for usages and
  ensure none cross network boundaries.
- `midnight_observer` provides at-least-once delivery with idempotent
  deduplication on the federation side. The dedup state is in
  `ObserverState` — if that file is wiped without coordination, you
  can replay events. Crash-recovery doc is clear; deployment doc may
  not be.
- `mina.rs` is "scaffolding-complete, runtime-pending" — much of the
  module is wire types and validation; the zkApp side is described
  but not constructed here.

### `coord/`

- The Stingray invariant `allowance = balance * (f+1) / (2f+1)` is
  documented in the `shared_budget` doc preamble but not enforced by
  a type or named constant. If a future caller miscomputes `f` they
  get a quiet integer answer, not a panic.
- 2PC commit phase in `atomic.rs` collects votes by `Coordinator`
  with a fixed timeout. Liveness depends on participants being
  responsive within timeout; safety does not.
- `serde_sig.rs` is a 25-line adapter for ed25519 signatures inside
  coordination messages. Worth eyeballing for canonicalisation
  (signature encoding ambiguity is a classic attack vector).

### `commit/`

- `accumulator.rs` defines `BabyBear^4` (quartic extension field)
  independently of `pyana-circuit::field`'s `BabyBear` operations.
  Cross-check for arithmetic equivalence. If they diverge, the
  polynomial accumulator's non-membership proofs may verify in one
  crate and reject in another.
- `symbol.rs` interns strings via BLAKE3 truncated to 253 bits. The
  forward direction is deterministic; the *reverse* direction depends
  on the table having seen the string. A serialized symbol with no
  reverse entry is a "hash → empty string" that may print as `???`.
  This is a UX issue, not a security one, but worth tracking.

### `token/`

- The default feature set is `["biscuit", "macaroon", "rand-deps"]`
  which pulls in `scalable_cuckoo_filter`. The cuckoo
  `RevocationFilter` is `#[deprecated]` but still default-on.
  Production deployments that accidentally rely on it get a
  false-positive-rate-bearing revocation check.
- `datalog_verify.rs` (2.9K LOC) is the canonical evaluator. It
  replaces but does not delete the imperative `verify_caveats`.
  Belt-and-suspenders is good; double maintenance is bad.

### `trace/`

- `standard_policy` uses `Contains` (substring) for action matching;
  `secure_policy` uses `MemberOf` (exact hash). Substring is a
  capability-expansion footgun — `action="readwrite"` would satisfy
  any caveat allowing `"read"`. The crate offers both; calling code
  must remember to pick `secure_policy`.

### `macaroon/`

- `discharge_gateway::DischargeGateway` holds a `Mutex<...>` over a
  rate-limit window and an evaluator dispatch table. Standard
  pluggable-evaluator pattern; the security surface depends on which
  evaluators are wired in by the deployer.
- `caveat_3p::ThirdPartyCaveat` uses XChaCha20-Poly1305 for the
  ticket — random 24-byte nonce + 32-byte tag.

### `net/`

- `gossip.rs` at 2.6k LOC is the biggest single-file security surface
  in this audit's scope. Plumtree-style eager/lazy push has a known
  amplification risk with Byzantine peers; the doc notes signed
  envelopes (Ed25519) and bounded pending-IHave state, but the proof
  is in the impl.
- `node.rs::ConnectionRateLimiter` is per-IP; if a peer is behind NAT
  with many others, the limit applies to the NAT.
- The crate explicitly notes iroh was the original choice and quinn
  was substituted due to dep conflicts. If iroh comes back, the
  whole transport layer changes.

### `store/`

- Signing keys encrypted at rest via ChaCha20-Poly1305 with key
  derived via BLAKE3 KDF. The master key acquisition mechanism is
  out of scope of this crate — that's the caller's responsibility.
- Note tree maintains BOTH BLAKE3 and Poseidon2 trees in lockstep.
  A bug that updates one but not the other yields silent root
  divergence between non-ZK and ZK paths.

### `audit/`

- The Merkle tree depth is 12, giving 4^12 ≈ 16M event capacity.
  Hardcoded. If a real deployment exceeded this it would either
  truncate or fail; no rotation scheme visible.
- `DEFAULT_HISTORICAL_ROOTS_LIMIT = 10_000` — older roots pruned on
  append. Consistency proofs against pruned roots will fail.

### `hints/`

- BLS12-381 + KZG threshold signatures. Trusted setup parameters
  loaded from `trusted_setup.rs`. The fork status (edition-2021
  island, fork authorship) means upstream security fixes do not
  automatically arrive.
- `[profile.test] opt-level = 2` is a workspace cascade hazard.

### `discharge-gateway/`

- The HTTP service runs axum on a single bind address. mTLS, rate
  limiting, and request size limits are deployment-time concerns
  not visible in this crate.
- The CLI supports `--key-hex` on the command line. That's a 32-byte
  symmetric key in `ps aux`. The TOML path is the production answer.

### `discharge-gateway`, `tokenizer`, `observability` (binaries)

All three are deployable binaries with no in-tree consumer that
spawns them. The "how to deploy" story for each is in code comments,
not in `deploy/`.

---

# Annex B — Cross-reference index

### Where to look for…

| Concern | Crate(s) | Entry point |
|---------|----------|-------------|
| Token format detection | `token` | `format::TokenFormat::detect` |
| Macaroon attenuation | `macaroon` | `Macaroon::attenuate` |
| Biscuit verification | `token` | `biscuit_backend::BiscuitToken::verify` |
| Caveat-to-fact encoding | `token` | `factset::caveat_set_to_factset` |
| Datalog evaluation | `trace` | `eval::Evaluator` |
| Authorization decision | `token` | `datalog_verify::verify_token_datalog` |
| Presentation builder | `bridge` | `present::BridgePresentationBuilder` |
| STARK prove (presentation) | `bridge` + `circuit` | `present::prove_predicate_program_full` |
| STARK verify (executor) | `bridge` | `verifier::StarkProofVerifier` |
| 2PC multi-party atomic | `coord` | `atomic::Coordinator` |
| Causal turn DAG | `coord` + `pyana_types` | `coord::causal::CausalLedger` |
| Bounded counter (Stingray) | `coord` | `budget::BudgetCoordinator` |
| Shared-resource budget | `coord` | `shared_budget::SharedResourceBudget` |
| Threshold QC (BLS) | `federation` + `hints` | `federation::threshold::FederationCommittee` |
| Revocation registry | `token` | `revocation::RevocationRegistry` |
| Revocation root attest | `token` | `revocation::AttestedRevocationRoot` |
| Audit log (usage events) | `audit` | `log::AuditLog::append` |
| Audit privacy proofs | `audit` | `proofs::{CountProof, RangeProof, ...}` |
| Persistent ledger | `store` | `PersistentStore::checkpoint_ledger` |
| Persistent blocklace | `store` | `blocklace_store::BlocklaceMeta` |
| Note commitment tree | `store` | `note_tree::NoteTree` (BLAKE3 + Poseidon2) |
| Nullifier set | `store` | `note_tree::PersistentNullifierSet` |
| P2P gossip | `net` | `gossip::GossipNetwork` |
| QUIC peer connections | `net` | `node::PeerNode` |
| CapTP wire messages | `wire` + `net` | `PeerMessage` |
| Discharge gateway logic | `macaroon` | `discharge_gateway::DischargeGateway` |
| Discharge HTTP service | `discharge-gateway` | binary |
| Sealed secrets daemon | `tokenizer` | `service::TokenizerService` |
| At-rest secrets | `secrets` | `EncryptedFileStore`, `KeychainStore` |
| Cross-chain (Midnight) | `bridge` | `midnight::{validate_*}` + `midnight_observer::run_observer` |
| Cross-chain (Mina) | `bridge` | `mina::wrap_stark_for_mina` |
| Protocol invariant tests | `protocol-tests` | per-invariant module under `invariants/` |
| Multi-node simulation | `teasting` | `harness::SimulationHarness` |
| Fault injection | `teasting` | `fault::FaultyNetwork`, `CrashableNode`, `Partition` |
| Release gate | `preflight` | `main::run_all_subsystems` |
| Single-turn JSON dump | `observability` | binary |

### Crate name → library name mapping

Inconsistency you should know about:

| Workspace member | `[package].name` | `[lib].name` |
|------------------|------------------|--------------|
| `bridge/` | `pyana-bridge` | (default) |
| `coord/` | `pyana-coord` | (default) |
| `audit/` | `pyana-audit` | (default) |
| `commit/` | `pyana-commit` | (default) |
| `trace/` | `pyana-trace` | (default) |
| `store/` | `pyana-store` | `pyana_store` |
| `net/` | `pyana-net` | (default) |
| `preflight/` | `pyana-preflight` | (default) |
| `protocol-tests/` | `pyana-protocol-tests` | (default) |
| `observability/` | `pyana-observability` | bin only |
| `teasting/` | `pyana-teasting` | (default) |
| `cod/` | `cod` | (default) |
| `discharge-gateway/` | `discharge-gateway` | `discharge_gateway_service` (lib), `discharge-gateway` (bin) |
| `token/` | `token` | `pyana_token` |
| `tokenizer/` | `tokenizer` | `pyana_tokenizer` |
| `macaroon/` | `macaroon` | `pyana_macaroon` |
| `secrets/` | `secrets` | `pyana_secrets` |
| `hints/` | `hints` | (default) |

The split between "pyana-X with default lib" and "X with pyana_X
library name" follows no obvious rule. `hints/`, `token/`,
`tokenizer/`, `macaroon/`, `secrets/`, `cod/`, `discharge-gateway/`
all break the convention `pyana-bridge`/`pyana-coord`/etc. follow.

---

# Annex C — Reading order for a new contributor

If you're new to pyana and want to understand the system bottom-up,
read the workspace crates in this order:

1. `types/` (excluded from this audit) — primitive types and IDs.
2. `commit/` — facts, fact sets, fold deltas, Merkle, Poseidon2.
3. `trace/` — Datalog, traces, policy rules.
4. `macaroon/` — HMAC macaroons + discharge.
5. `token/` — `AuthToken` abstraction + canonical Datalog verification.
6. `bridge/` (skim `present.rs`) — token → STARK proof pipeline.
7. `cell/` + `turn/` (excluded) — execution model.
8. `coord/` — multi-party atomicity + bounded budgets.
9. `blocklace/`, `federation/`, `hints/`, `captp/` (mostly excluded) —
   coordination & consensus.
10. `net/` — P2P transport.
11. `store/` — persistence.
12. `storage/` (excluded; programmable queues / inboxes / relay).
13. `node/` (excluded) — assembles everything.
14. `preflight/main.rs::run_all_subsystems` — the manifest.
15. `teasting/tests/` — the contract.
16. `protocol-tests/invariants/` — the invariants.

If you only have time for the surprising parts, jump to:

- `cod/src/lib.rs` (21 LOC) — read in 30 seconds, learn a lot.
- `observability/src/main.rs` — read in 5 minutes, see how a turn
  becomes a JSON document.
- `preflight/src/main.rs` — read in 2 minutes, learn what pyana
  thinks it is.


