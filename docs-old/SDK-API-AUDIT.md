# dregg-sdk + dregg-app-framework + starbridge-apps: Rust API Ergonomics Audit

**Date:** 2026-05-25
**Auditor:** Sonnet 4.6 (read-only lane; no cargo, no persvati, no worktree isolation)
**Files read:** `sdk/src/cipherclerk.rs` (7,735 lines), `sdk/src/lib.rs`, `app-framework/src/lib.rs`,
`app-framework/src/cipherclerk.rs`, `app-framework/src/starbridge.rs`, `app-framework/src/server.rs`,
`app-framework/src/middleware.rs`, `starbridge-apps/nameservice/src/lib.rs` (1,621 lines),
`starbridge-apps/identity/src/lib.rs`, `starbridge-apps/subscription/src/lib.rs`,
`starbridge-apps/governed-namespace/src/lib.rs`,
`starbridge-apps/nameservice/tests/integration_register_full_flow.rs`,
`starbridge-apps/governed-namespace/tests/integration_propose_vote_commit.rs`

---

## §1 Top 5 Friction Points

### #1 — `CellProgram::Cases` types not re-exported from the framework

`app-framework/src/lib.rs:171–175` re-exports `CellProgram`, `ChildVkStrategy`, `FactoryDescriptor`,
and friends from `dregg_cell` — but omits the types needed to *build* a non-trivial `CellProgram`:

```rust
// starbridge-apps/identity/src/lib.rs:78
use dregg_cell::program::AuthorizedSet;

// starbridge-apps/nameservice/src/lib.rs:86-87
use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
use dregg_cell::program::AuthorizedSet;

// starbridge-apps/governed-namespace/src/lib.rs:168 (similar)
```

Every app that writes an operation-scoped `CellProgram::Cases(vec![TransitionCase { ... }])` must add
`dregg-cell` to its own `Cargo.toml` and import from `dregg_cell::program` and `dregg_cell::predicate`
directly. The promise "everything via `dregg_app_framework`" is broken at the first non-trivial cell
program. Missing from the re-export: `TransitionCase`, `TransitionGuard`, `AuthorizedSet`,
`WitnessedPredicate`, `WitnessedPredicateKind`, `InputRef`.

**Fix:** `app-framework/src/lib.rs` — add two lines after line 175:
```rust
pub use dregg_cell::program::{AuthorizedSet, TransitionCase, TransitionGuard};
pub use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
```

### #2 — Field-encoding helpers copy-pasted into every app

Three micro-functions appear as private/pub copies in all four apps:

| Function | Copies | Locations |
|----------|--------|-----------|
| `fn blake3_field(bytes: &[u8]) -> FieldElement` | 4 | nameservice:842, subscription:891, governed-namespace:1205 (pub), identity — missing; uses inline BLAKE3 |
| `fn u64_field(value: u64) -> FieldElement` | 4 | nameservice:852, identity:676, subscription:885, governed-namespace:1210 (pub) |
| `fn hex_encode(bytes: &[u8; 32]) -> String` | 4 | nameservice:681, identity:705, subscription:854, governed-namespace:1226 |

These encode the canonical field-element convention used by `SetField` effects: BLAKE3 hash into 32
bytes, and big-endian u64 in trailing 8 bytes. They are load-bearing for cross-app compatibility:
nameservice and identity share field elements without any compile-time guarantee that they use the
same encoding. `governed-namespace` exposes `blake3_field` and `u64_field` as `pub` so its
integration tests can call them; the others mark them `fn` (private), deepening the inconsistency.

`app-framework/src/hex.rs` already exists (for short hex display) but does not expose these.

**Fix:** Add `dregg_app_framework::field_from_bytes`, `field_from_u64`, `hex_encode_32` in
`app-framework/src/fields.rs` (~15 lines) and re-export from `lib.rs`. Remove all 12 per-app copies.

### #3 — `FactoryDescriptor` struct requires the same VK value in two fields simultaneously

Every app builds a `FactoryDescriptor` with this duplication (`nameservice/src/lib.rs:239–272`):

```rust
FactoryDescriptor {
    factory_vk: NAME_FACTORY_VK,
    child_program_vk: Some(name_child_program_vk()),          // VK here...
    child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(name_child_program_vk()))), // ...and here
    allowed_cap_templates: vec![...],
    field_constraints: vec![...],
    state_constraints: vec![...],
    default_mode: CellMode::Sovereign,
    creation_budget: Some(DEFAULT_CREATION_BUDGET),
}
```

All four apps use `ChildVkStrategy::Fixed(Some(vk))` with the same value as `child_program_vk`.
Failing to keep them in sync breaks constructor-transparency silently. `governed-namespace` already
shows drift: it uses a byte-string placeholder `*b"starbridge-governed-namespace-cp"` for
`GOVERNANCE_CHILD_PROGRAM_VK` while others compute it canonically.

**Fix:** `FactoryDescriptor::with_fixed_program_vk(factory_vk, program_vk, ...)` constructor in
`dregg-cell`. The `child_vk_strategy` would be derived as `Fixed(program_vk)`. 8-field struct literal
becomes a 6-argument call.

### #4 — `ExecutorSubmitError` erases the underlying error type entirely

`app-framework/src/cipherclerk.rs:409`:
```rust
pub struct ExecutorSubmitError(pub String);
```
Converting `SdkError` to a `String` prevents app handlers from mapping failure causes to HTTP status
codes, and forces tests to substring-match:

```rust
// governed-namespace/tests/integration_propose_vote_commit.rs:154-160
let msg = e.to_string();
assert!(
    msg.contains("Custom") || msg.contains("verifier") || msg.contains("witness")
        || msg.contains("authorization") || msg.contains("predicate"),
    ...
);
```

This is the correct "don't leak SDK internals to apps" instinct, but the execution is wrong. An app
that wants to return 400 for authorization failure and 500 for chain mismatch cannot distinguish the
two without implementing its own substring parser.

**Fix:** Add `ExecutorSubmitKind` enum with variants (`Authorization`, `SlotCaveat`, `ChainMismatch`,
`Rejected`) and a `kind()` accessor on `ExecutorSubmitError`. The `Display` stays as a plain string;
the `kind()` lets handlers branch on structured cause. (~30 lines in `app-framework/src/cipherclerk.rs`.)

### #5 — `#[must_use]` missing from the 7 functions where dropping the result is a programming error

`sdk/src/cipherclerk.rs:1098,1118` correctly annotates `export_mnemonic` and `export_seed`. The
execution-path functions are not annotated:

| Function | File | Consequence of silent drop |
|----------|------|---------------------------|
| `AgentCipherclerk::mint_token` | sdk/src/cipherclerk.rs:1198 | Minted token lost, orphaned root key |
| `AgentCipherclerk::attenuate` | sdk/src/cipherclerk.rs:1232 | Attenuated token never transmitted |
| `AgentCipherclerk::delegate` | sdk/src/cipherclerk.rs:1279 | Delegation envelope never sent |
| `AgentRuntime::execute` | sdk/src/runtime.rs | Receipt not appended to chain |
| `EmbeddedExecutor::submit_turn` | app-framework/src/cipherclerk.rs:368 | Receipt never inspected |
| `EmbeddedExecutor::submit_action` | app-framework/src/cipherclerk.rs:386 | Same |
| `AppCipherclerk::create_from_factory` | app-framework/src/cipherclerk.rs | Factory turn never submitted |

**Fix:** Seven `#[must_use = "..."]` attributes, one per function. Zero runtime cost.

---

## §2 Recurring Boilerplate (Extract Candidates)

### Pattern A — `fn test_cipherclerk()` / `fn make_cipherclerk(seed)` — 8 copies

All four apps and their integration tests define nearly-identical fixtures:

```rust
// In each app's src/lib.rs test module:
fn test_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
}

// In each integration test file:
fn make_cipherclerk(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
}
```

Exact locations: nameservice:867, identity:722, subscription:871 (in-module);
nameservice/tests/integration_register_full_flow.rs:33,
governed-namespace/tests/integration_propose_vote_commit.rs:29 (integration).

**Extract to:** `AppCipherclerk::test_fixture(seed: u8) -> AppCipherclerk` under
`#[cfg(any(test, feature = "dev"))]` in `app-framework/src/cipherclerk.rs`.

### Pattern B — `fn make_executor_with_cell(cipherclerk)` — 4 copies

Each integration test creates an `EmbeddedExecutor` and immediately captures `cell_id()`:

```rust
fn make_executor_with_cell(cipherclerk: &AppCipherclerk) -> (EmbeddedExecutor, CellId) {
    let executor = EmbeddedExecutor::new(cipherclerk, "default");
    let cell = executor.cell_id();
    (executor, cell)
}
```

**Extract to:** `EmbeddedExecutor::with_default_cell(cipherclerk)` returning `(Self, CellId)`, or
document that `executor.cell_id()` is idempotent and callers can just keep the executor.

### Pattern C — `blake3_field` / `u64_field` / `hex_encode` — 12 copies total

See §1 Friction #2. 4 copies each, all functionally identical. Centralizing eliminates encoding drift.

### Pattern D — canonical VK test trio — 3 copies

Each app that computes a canonical VK writes three tests: `vk_is_canonical_recipe`,
`vk_is_not_placeholder_bytes`, `vk_is_v2_layered_hash`. These test the framework's VK derivation,
not the app's logic.

**Extract to:** `dregg_app_framework::vk::assert_canonical_vk(vk, program, desc)` test helper.

### Pattern E — untyped `serde_json::json!({...})` inspector descriptors — 4+ copies

Every app passes a `|| serde_json::json!({...})` closure to `register_inspector_with`. The JSON
shape is untyped; required fields (`component`, `module`, `uri_prefix`) are not checked at
registration time.

**Extract to:** a typed `InspectorDescriptorBuilder` once the inspector contract stabilizes.

---

## §3 Error-Handling Ergonomics

### Good: `SdkError` is a proper typed enum

`sdk/src/error.rs` — 17 `thiserror::Error` variants with named fields on the actionable cases:
```rust
SdkError::ReceiptChainMismatch { expected: Option<[u8; 32]>, got: Option<[u8; 32]> }
SdkError::DuplicateReceipt { turn_hash: [u8; 32] }
```
`ChainAppendError::ReceiptChainMismatch` mirrors this. `From<ChainAppendError> for SdkError` is
clean. This is the right pattern; everything else should follow it.

### Bad: `ExecutorSubmitError` erases all structure at the framework boundary

See §1 Friction #4. The framework converts `SdkError` → `String` at `submit_action`. The investment
in typed SDK errors is wasted. App tests must `contains()`-match; handlers cannot branch on cause.

### Ugly: `PersistError` is not connected to the SDK error hierarchy

`persistence.rs` `PersistError` implements `std::error::Error` with `source()` but is not a variant
of `SdkError`. An app mixing persistence with turn submission must box both or define a custom error
enum. There is no natural composition path.

### Missing: `TurnError` not re-exported from `dregg_app_framework`

`TurnError` is re-exported from `dregg_sdk` but not from `dregg_app_framework`. An app importing
only the framework cannot pattern-match `SdkError::Turn(TurnError::...)` without adding `dregg-sdk`
to `Cargo.toml`. Currently academic (error erasure in `ExecutorSubmitError` makes it moot), but it
blocks the natural fix once `ExecutorSubmitKind` variants are added.

### Missing: `CredentialError` umbrella in `dregg-credentials`

Three distinct error enums (`IssuanceError`, `PresentationError`, `VerificationError`) from three
submodules. A handler that sequences issue → verify must box or erase both:
```rust
issue(...).map_err(|e| MyError::Credential(e.to_string()))?;
verify(...).map_err(|e| MyError::Credential(e.to_string()))?;
```
No `CredentialError` umbrella exists. Low urgency until the credential API is in production use.

---

## §4 Documentation Gaps

### D1 — `AgentCipherclerk` has no "start here" orientation (sdk/src/cipherclerk.rs:1)

The 7,735-line file has a 16-line module-level docstring that accurately describes what the type
does, but not what to call first. `new()` appears on line 970. The Quick Start in `sdk/src/lib.rs`
shows `mint_token` as the second call after `new()` — but most starbridge-app authors never call
`mint_token` at all. The Quick Start does not mention `AppCipherclerk` or the framework entry point.

### D2 — `AppCipherclerk::new` requires `[u8; 32]` federation ID with no sourcing guidance

The parameter is documented as "the federation identifier this app operates in" with no guidance on
where the value comes from (config file, environment variable, derived from a public key, hardcoded
for devnet). All four apps use `[42u8; 32]` in tests. A new developer will not know what to pass in
production.

### D3 — `submit_turn` vs `submit_action` distinction is not signposted

`app-framework/src/cipherclerk.rs:368,386` — two methods with similar names and overlapping docs.
`submit_action` calls `make_turn` internally (the common case); `submit_turn` is for multi-action or
custom turn structures. This distinction is present in the doc text but invisible at IDE hover: the
developer sees two choices and must read both docs to distinguish them.

### D4 — `WitnessBlob` mutation after `make_action` is undocumented at the framework level

`nameservice/src/lib.rs` (build_register_with_credential_action) does:
```rust
let mut action = cipherclerk.make_action(registry_cell, "register_name_attested", effects);
action.witness_blobs = vec![WitnessBlob::proof(proof_bytes)];
action
```
The action's signature was computed before `witness_blobs` was set. Whether the signature covers
`witness_blobs` or not (it does not — signature covers method, target, and effects at signing time)
is a security-critical question with no framework-level documentation. A developer doing this wrong
produces unbound proofs silently.

### D5 — `ChildVkStrategy` variants undocumented for app authors

`ChildVkStrategy::Fixed` vs `ChildVkStrategy::Deterministic` — every app uses `Fixed`. When to use
`Deterministic` is explained only in `dregg_cell`, not at the framework re-export location. App
authors see an opaque import with one obvious variant and one mysterious one.

### D6 — `StarbridgeAppContext` does not cross-reference `AppServer::with_starbridge`

A developer who constructs a `StarbridgeAppContext` and registers factories on it has no doc pointer
from the context to the HTTP wiring step. The `AppServer` example shows the wiring; the
`StarbridgeAppContext` doc does not link to it.

### D7 — `Turn` struct's 19 fields have no "you care about these" marker

`dregg_turn::Turn` — 19 fields, 12 with `#[serde(default)]`. A developer introspecting a
`TurnReceipt` or building a custom `Turn` confronts all 19. The `make_turn` helpers hide this, but
only if the developer finds them. No builder typestate or field grouping comments orient the reader.

---

## §5 "If I Write a New Starbridge-App Tomorrow" — Badge-Issuance Narration

**Goal:** `starbridge-badge` — create badge cells, issue badges, let holders present them.

**Step 1: Add `dregg_app_framework` to Cargo.toml.** Straightforward; the crate re-exports
everything at the root. ✓

**Step 2: Define slot layout constants.** Easy; follows the nameservice pattern. ✓

**Step 3: Define a `CellProgram` with per-operation cases.**
I want `CellProgram::Cases(vec![TransitionCase { guard: TransitionGuard::MethodIs("issue_badge"), ... }])`.
I try to import `TransitionCase` from `dregg_app_framework`. Not found. I grep across the workspace:
`use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard}`. I add `dregg-cell` to my
`Cargo.toml`. **[Friction #1 — first real obstacle]**

**Step 4: Define field-encoding helpers.**
I need to hash badge IDs and encode block heights as field elements. I look at nameservice:
private functions `blake3_field` and `u64_field`. I copy them. **[Friction #2 — third copy of same code]**

**Step 5: Build the `FactoryDescriptor`.**
Eight-field struct literal. I see that `child_program_vk` and `child_vk_strategy` must both carry
the same VK. I copy the pattern from nameservice. It works, but I don't understand why both exist.
**[Friction #3 — mild; followable but non-obvious]**

**Step 6: Write turn-builder functions.**
`cipherclerk.make_action(target, "issue_badge", effects)`. Clean. `AppCipherclerk` API is excellent.
The federation ID is hidden. ✓

**Step 7: Implement `register(ctx)`.** Copy from nameservice. ✓

**Step 8: Write unit tests.**
I write `fn test_cipherclerk()`. It is identical to the function already in nameservice, identity,
and subscription. **[Friction #4 — tedious, signals missing test ergonomics]**

**Step 9: Write integration tests with `EmbeddedExecutor`.**
`EmbeddedExecutor::new` + `submit_action`. Clean; receipt comes back. ✓

**Step 10: Handle errors in HTTP handlers.**
`executor.submit_action(...)` returns `ExecutorSubmitError(String)`. I want 400 for invalid badge
ID and 500 for chain mismatch. I cannot distinguish them. I log the string and return 500 for
everything. **[Friction #5 — significant production-quality gap]**

**Step 11: Wire into `AppServer`.**
```rust
AppServer::new(AppConfig::from_env())
    .with_health().with_cors()
    .with_cipherclerk(cipherclerk)
    .with_embedded_executor(executor)
    .with_starbridge(ctx)
    .routes(badge_routes(state))
    .serve().await
```
Best part of the experience. Fluent builder works well. ✓

**Summary:** Happy path (straight-line submission) is smooth. The `dregg_cell::program` detour is
the first real wall. Field-helper duplication is tedious. Error erasure in `ExecutorSubmitError` is
the worst production-quality gap.

---

## §6 Prioritized Improvement List

Ranked by impact-per-line-changed.

| # | Change | File | LoC | Impact |
|---|--------|------|-----|--------|
| 1 | Re-export `TransitionCase`, `TransitionGuard`, `AuthorizedSet`, `WitnessedPredicate`, `WitnessedPredicateKind`, `InputRef` from framework | `app-framework/src/lib.rs` | 2 | Closes the "everything via dregg_app_framework" promise; removes mandatory `dregg-cell` dep from all apps |
| 2 | Add `field_from_bytes`, `field_from_u64`, `hex_encode_32` to framework | `app-framework/src/fields.rs` + `lib.rs` | ~15 | Eliminates 12 per-app copies; prevents silent encoding drift in cross-app field elements |
| 3 | Add `#[must_use]` to 7 execution-path functions | `sdk/src/cipherclerk.rs`, `sdk/src/runtime.rs`, `app-framework/src/cipherclerk.rs` | 7 attrs | Compiler errors on "action built but never submitted" class of bugs |
| 4 | Add `AppCipherclerk::test_fixture(seed: u8)` under `cfg(any(test, feature = "dev"))` | `app-framework/src/cipherclerk.rs` | ~8 | Eliminates 8 near-identical fixture functions across the codebase |
| 5 | Add `ExecutorSubmitKind` enum + `kind()` accessor on `ExecutorSubmitError` | `app-framework/src/cipherclerk.rs` | ~30 | Unblocks precise HTTP status mapping and removes substring-match test pattern |
| 6 | Add `FactoryDescriptor::with_fixed_program_vk(...)` constructor | `dregg-cell` | ~20 | Eliminates `child_vk_strategy` duplication; prevents silent divergence |
| 7 | Deprecate (`#[deprecated]`) the `cclerk` module aliases | `sdk/src/lib.rs:112–116`, `app-framework/src/lib.rs:72–79` | ~4 | Clears invisible API surface from autocomplete; currently `#[doc(hidden)]` but not deprecated |
| 8 | Add `CredentialError` umbrella in `dregg-credentials` | `credentials/src/lib.rs` | ~25 | Single error type for multi-step credential flows; unblocks credential-API adoption |
| 9 | Add `TurnError` re-export from `dregg_app_framework` | `app-framework/src/lib.rs` | 1 | Prerequisite for structured `ExecutorSubmitKind` matching without adding `dregg-sdk` dep |
| 10 | Add "starbridge-app quick start" doc section to `app-framework/src/lib.rs` | `app-framework/src/lib.rs` | ~20 doc lines | Orients new developers to the `AppCipherclerk` → `EmbeddedExecutor` → `AppServer` flow; current Quick Start in `sdk` shows the token-management path, not the app-authoring path |

---

## Summary (under 300 words)

### 3 Highest-Leverage Improvements

**1. Re-export `CellProgram`-building types from the framework** (`TransitionCase`, `TransitionGuard`,
`AuthorizedSet`, `WitnessedPredicate`, `WitnessedPredicateKind`, `InputRef`). Two lines in
`app-framework/src/lib.rs`. Every app with an operation-scoped cell program currently breaks the
"one Cargo.toml dep" promise at step 3. This is the first wall a badge-app author hits.

**2. Centralize `field_from_bytes`, `field_from_u64`, `hex_encode_32`.** Fifteen lines of new code
eliminates twelve per-app copies. More importantly it enforces one encoding for the field-element
convention used by `SetField` effects — nameservice and identity share these values across apps and
today have no compile-time guarantee they agree on encoding.

**3. Add `#[must_use]` to the 7 execution-path functions.** Seven attributes, zero runtime cost,
compiler-enforced correctness. `EmbeddedExecutor::submit_action` is the most critical: it is the
canonical "I submitted a turn" call and dropping its result is exactly the "action authored and
abandoned" bug the framework was designed to prevent. `AgentCipherclerk::mint_token`,
`attenuate`, and `delegate` are close behind.

### 1 Architectural Smell Justifying a Bigger Refactor

**`ExecutorSubmitError` erases `SdkError` into a `String` at the framework boundary.** The intention
("don't leak SDK internals to app authors") is correct. The execution is wrong: app handlers cannot
distinguish authorization failures from chain mismatches, tests must substring-match error messages,
and every app that ships production HTTP handlers will independently paper over this with its own
`match e.to_string().contains(...)` logic. Adding `ExecutorSubmitKind` variants (~30 lines) is the
right fix before the first external app ships.

### SDK Readiness: substrate, not ready

The happy path works and is well-documented. But the `dregg_cell::program` leakage, the field-helper
duplication, the `test_cipherclerk()` copy-paste pattern, and especially the error erasure in
`ExecutorSubmitError` all signal a surface designed for current team members who know the internals.
An external developer picking this up fresh hits a real obstacle by step 3 and an invisible production
gap by step 10.
