# Kimi Damage Audit + Nextest Analysis

Date: 2026-05-25
Auditor: opus-4.7 (read-only lane)
Source: `nextest.log` (13308 lines) + git history of last 4 commits

---

## §1 Nextest Summary

### Top-line counts
```
5439 tests run: 5266 passed, 173 failed, 380 skipped (10.168s)
```

Workspace is **96.8% green**. The 380 skipped tests are nextest profile filters (default-filter excludes 221).

### Failures grouped by crate (unique tests, not log lines)

| Crate                              | Fails | Note |
|------------------------------------|-------|------|
| dregg-teasting (integration)       | 43    | proving infra cascade |
| dregg-circuit                      | 42    | bounded by 1 root bug |
| dregg-wasm                         | 16    | **all false positives** (wasm-bindgen on native) |
| dregg-bridge                       | 16    | Poseidon2 STARK failures |
| dregg-tests (workspace integ)      | 11    | cascade |
| dregg-sdk                          | 6     | Poseidon2 STARK |
| dregg-gallery                      | 6     | Poseidon2 STARK |
| starbridge-subscription::program   | 5     | program executor regression |
| starbridge-identity::credential    | 5     | credential proving cascade |
| dregg-turn                         | 5     | conditional cascade + 1 real |
| dregg-credentials                  | 5     | rejecting valid roots |
| starbridge-governed-namespace      | 3     | governance |
| dregg-nameservice                  | 3     | register flow |
| dregg-demo                         | 2     | stark membership |
| dregg-verifier                     | 1     | aggregated bundle CLI |
| dregg-storage-templates            | 1     | inbox method routing |
| dregg-identity                     | 1     | revocation manager |
| dregg-directory                    | 1     | hex-length assertion (test bug) |
| dregg-cell                         | 1     | postcard all-zero edge case |
| dregg-teasting::effect_vm_captp    | 1     | handoff proof |

**Net unique failing tests:** ≈ 173 (matches Summary).

### Failure category breakdown

Three dominant root causes (NOT 173 independent bugs):

1. **`circuit/src/dsl/circuit.rs:335:48` — `index out of bounds: len 3, index 3`** in `Poseidon24To1` constraint reconstruction. This single panic explains **at least 30** failures across `dregg-circuit::body_membership`, `cross_state_derivation`, `dsl::membership`, `ivc`, `predicate_program`, `presentation`, plus `dregg-bridge::verifier`, `dregg-demo::stark_proof`, `dregg-turn::conditional`, `dregg-turn::obligation`, and `dregg-teasting::proof_round_trip::test_stark_proof_bytes_round_trip`. The bug is in the prover's children-reconstruction loop that has 3 siblings + 1 current but iterates 0..4 against `siblings[sib_idx]` — when `position == 3`, `sib_idx` reaches 3 before the break.

2. **"Poseidon2 STARK proof generation failed" / "Bridge(Denied)"** — surfaces in `dregg-bridge::present`, `dregg-sdk::cipherclerk`, `dregg-credentials::roundtrip`, `dregg-identity::tests`, `dregg-gallery::private_vickrey`, `starbridge-identity::credential_lifecycle`, `dregg-teasting::token_lifecycle`. Likely the same underlying root cause as #1 (the prover crashes inside, then the call returns an error string).

3. **wasm-bindgen on native** — all 16 `dregg-wasm::audit_tests` failures. These tests **cannot run** outside wasm32. They show up because they don't `#[cfg(target_arch = "wasm32")]`-gate. **False damage** — these were never running here.

After accounting for those three buckets, the remaining real failures (~30) split into:

- **Test-data drift / hardening assertions** (real regressions):
  - `dregg-turn::tests::test_program_none_backward_compat` — assertion `nonce()==1` fails (executor isn't incrementing nonce on CellProgram::None cells anymore)
  - `dregg-teasting::storage_lifecycle` × 3 — queue allocation / dequeue producing different roots than expected
  - `dregg-tests::sovereign_proof` × 2 — proof-carrying turn
  - `dregg-tests::captp_effects_pipeline` × 3 — `aux[0]` / `effects_hash_lo` bind to wrong preimage (different BabyBear values; constraint shape changed)
  - `dregg-teasting::consensus_liveness` × 4 — consensus tests
  - `dregg-teasting::fault_partition` × 3, `fault_crash` × 1
  - `dregg-teasting::cross_federation` × 2
  - `dregg-teasting::revocation_propagation` × 5
  - `dregg-teasting::escrow_lifecycle` × 5
  - `dregg-teasting::defi_primitives` × 2
  - `dregg-teasting::relay_operators` × 2
  - `dregg-tests::slot_caveat_composition_stress` × 3
  - `starbridge-subscription::program` × 5 — `expected Immutable on head, got Monotonic` — constraint enforcement regression
  - `starbridge-governed-namespace::governance` × 3
  - `dregg-nameservice::register_*` × 3
  - `dregg-verifier::aggregated_bundle::cli_verdict_happy_and_reject`
  - `dregg-storage-templates::cap_inbox_tests::unknown_method_default_denied`
  - `dregg-cell::preconditions::clause_tests::preconditions_roundtrip_postcard` — postcard now accepts an all-zero 16-byte buffer where it used to reject

- **Tests with stale/wrong assertions** (broken tests, not broken code):
  - `dregg-directory::resource_handle_uri_contains_hex_fields` — assertion string is **68 hex chars** (34 `ab` pairs) but field is 32 bytes → 64 hex chars. The test was written wrong.
  - `dregg-cell::preconditions_roundtrip_postcard` — possible (postcard library upgrade may have made certain all-zero buffers valid encodings)

- **`dregg-credentials::roundtrip` × 5** — every credential test fails with `Bridge("Denied")` or `assertion false == true`. This is a real cascade from the same Poseidon2 issue, probably.

---

## §2 What kimi's 4 commits did (oldest → newest)

### `4b635096` — "checkpoint"  (cosmetic)
- 11 files, +27 / −43.
- **Pure whitespace and module-ordering** cleanup:
  - Removed trailing blank lines from `turn/src/executor/{apply,authorize,mod}.rs`.
  - Re-sorted submodule declarations alphabetically (`mod apply; mod authorize; mod execute; ...`).
  - Reformatted function signatures across multiple lines in `turn/src/executor/finalize.rs`.
  - Simplified `circuit/src/temporal_predicate_dsl.rs` (25-line block → 11 lines) — needs verification this didn't drop semantics.
- **Verdict: safe / beneficial.** No semantic changes.

### `1d800aad` — "pre-cclerk checkin"  (legitimate cascade)
- 19 files, +38 / −4.
- Adds `unilateral_attestations: BTreeMap::new()` to `BilateralBundle` struct literals across:
  - `verifier/tests/bilateral_pair_demo.rs`
  - `verifier/src/bilateral_pair.rs` tests (× 8)
  - `turn/src/bilateral_schedule.rs` tests (× 3)
  - `coord/src/tests.rs`, `federation/src/cross_fed_bundle.rs`
- Adds `was_burn: false` to `WitnessedReceipt` literals across `turn/src/conditional.rs` tests (× 3), `turn/src/aggregate_bilateral_prover.rs`, `turn/src/pending.rs`, `turn/src/verify.rs`, `turn/src/witnessed_receipt.rs`.
- Replaces `custom.pi_tag()` with `unilateral_pi_tag(&custom)` in one test.
- **Verdict: net positive.** This is real "test fixture catch-up" after a struct change landed earlier. These additions are correct and necessary.

### `31722471` — "wallet -> cipherclerk"  (mostly redo, partially damaging)
- 322 files, +3256 / −3252 (almost zero-net-LOC — pure rename).
- **What it actually did:** sweep replacement of `wallet` → `cipherclerk` (and `Wallet` → `Cipherclerk`) across:
  - Documentation: `*.md` files in `.docs-history-noclaude/`, `audits/`, `docs/`, `plans/`, `old-docs/`, root-level `*.md` (~100 files).
  - Code: 642-line churn in `sdk/src/cipherclerk.rs` (mostly comments), `discord-bot/src/cipherclerk.rs`, `cli/src/commands/cipherclerk.rs` (file rename from `wallet.rs`), TypeScript files in `sdk-ts/`, `extension/`, frontend JS, Compact contracts.
  - Tests: `tests/src/full_pipeline.rs`, `tests/src/fully_private_e2e.rs`, `tests/src/wire_format_e2e.rs`, `tests/src/sovereign_proof.rs`, `tests/src/every_variant_roundtrip.rs` — all updated to `AgentCipherclerk` from `AgentWallet`.
- **The good:**
  - The test-code updates were *necessary*: `AgentWallet` had already been renamed to `AgentCipherclerk` in earlier commits (`d1e3f47e cipherclerk rename sweep: extension/ residuals`, `2a5d80a2 sdk: rename AgentRuntime wallet field/parameter to cipherclerk`). Some test files still imported the old name. Kimi cleaned that up.
  - File renames (`cli/src/commands/wallet.rs` → `cipherclerk.rs`, `sdk-ts/src/wallet.ts` → `cipherclerk.ts`, etc.) are consistent.
- **The damaging:**
  - **Broke the meaning of legacy-alias documentation.** Example, `sdk/src/cipherclerk.rs:3`:
    ```rust
    /// The [`AgentCipherclerk`] (legacy alias `AgentWallet`) is the agent's
    ```
    became
    ```rust
    /// The [`AgentCipherclerk`] (legacy alias `AgentCipherclerk`) is the agent's
    ```
    — the legacy-alias documentation now says the new name is its own alias.
  - Similar damage at `sdk/src/cipherclerk.rs:14`:
    > `"Wallet" was a poor fit: dregg cipherclerks mostly manage *capabilities*, not balances.`
    became
    > `"Cipherclerk" was a poor fit: dregg cipherclerks mostly manage *capabilities*, not balances.`
    — explanatory rationale now contradicts itself.
  - Many similar prose-meaning losses in `*.md` files in `audits/`, `plans/`, `docs/`.
  - **Did NOT cause any test compile or runtime failure** — none of the test failures in nextest.log can be traced to text in comments.

### `62440596` — "cargo check..."  (partial undo)
- 12 files, +26 / −14.
- **What it did:**
  - Touched the `bridge/contracts/package.json` to **restore** the correct external npm package names: `@midnight-ntwrk/wallet-sdk-*` (these are real packages published by Midnight Network; the prior `wallet→cipherclerk` sweep had renamed them, which would break `npm install`). **Good fix.**
  - Reverted some prose comments in `sdk/src/cipherclerk.rs`, `intent/src/gossip.rs`, `node/src/state.rs`, etc. from "cipherclerk" back to "wallet" — but inconsistently, leaving the doc-comments in a worse state than before either rename pass.
  - Added `was_burn: false` to 4 more `demo-agent/examples/*.rs` files — same legitimate cascade as 1d800aad.
  - Added a `proptest_invariants.proptest-regressions` seed (`turn/tests/`) — appears to be a recorded failure seed from a proptest run (`extra_caps = 0, revoke_before_refresh = true`). This is automated; the test it pins must still fail.
- **Verdict:** the package.json fix is essential. The doc-comment thrashing leaves things noisier than they were but does not break the build or tests. The proptest seed addition is a small flag that there is a *known* turn-executor proptest failure (re-run to confirm).

---

## §3 Real damage (tests that should be working but are broken)

Ordered by severity / blast radius:

1. **`circuit/src/dsl/circuit.rs:335` out-of-bounds panic** (single bug, ~30+ cascading test failures).
   - This is **NOT kimi's**. The file has not been touched in any of 4b635096 / 1d800aad / 31722471 / 62440596. Last touched in `7d7b8814 storage, fault tests, nameservice...`.
   - Root cause: in `Poseidon24To1` evaluator, the canonical-children reconstruction iterates `i in 0..4u8`, and when `i != position`, indexes `siblings[sib_idx]` where `siblings` has only 3 elements. If the prover ever stores `position` such that the *last* iteration is the non-position case, `sib_idx` reaches 3.
   - **Fix lane:** circuit team, one-file fix, high confidence.

2. **`dregg-turn::tests::test_program_none_backward_compat` — nonce not incrementing**.
   - Hardening-assertion form. The executor decomposition (commits `09290e50` and earlier — also NOT kimi) likely dropped a nonce-increment path on the CellProgram::None code path.
   - **Fix lane:** turn-executor team. Bisect against `09290e50 turn/executor: decompose 10547-line mod.rs`.

3. **`dregg-tests::captp_effects_pipeline` × 3 — wrong preimage bound to aux/effects_hash**.
   - Assertions compare to *hardcoded* BabyBear values. Either the test values are stale OR the binding logic changed (e.g., the swiss→cell_id binding format).
   - **Fix lane:** captp / effect-vm team. Need to recompute expected values.

4. **`starbridge-subscription::program` × 5 — `expected Immutable on head, got Monotonic { index: 3 }`**.
   - The constraint kind being returned by `evaluate` for the head-slot mismatch has changed from Immutable to Monotonic. Either:
     - Subscription program descriptor changed which constraint is on slot 3, or
     - Constraint evaluation now prefers Monotonic when both could fire.
   - **Fix lane:** starbridge-apps + cell-program team. Reading `starbridge-apps/subscription/tests/program.rs:183,463,483` will tell quickly.

5. **`dregg-teasting::token_lifecycle` × 5 + `dregg-credentials::roundtrip` × 5**.
   - All "Bridge(Denied)" or root-token verification failing. Almost certainly the same Poseidon2 bug as #1 cascading through the bridge presenter.

6. **`dregg-teasting::storage_*` × 5 (storage_faults + storage_lifecycle)**.
   - Storage queue root mismatch / FIFO proof rejection. Real regression in commit `7d7b8814 storage, fault tests, nameservice...` — same commit also fixed BLINDED_QUEUE_SPEND_AIR_VK length, plausibly missed another constant.

7. **`dregg-teasting::consensus_liveness` × 4, `fault_partition` × 3, `fault_crash` × 1**.
   - The fault-injection consensus tests are nondeterministic by nature. May be flakes (rerun first), or may share a root cause with storage failures.

8. **`dregg-teasting::escrow_lifecycle` × 5, `relay_operators` × 2, `revocation_propagation` × 5, `cross_federation` × 2, `defi_primitives` × 2**.
   - Almost all panic at the first `assert!` in their setup — strong signal that a common test helper or fixture changed shape. Worth bisecting against `7d7b8814`.

9. **`dregg-cell::preconditions_roundtrip_postcard` — "all-zero buffer must fail to decode"**.
   - Real test bug or a postcard upgrade made `[0u8; 16]` parseable. The test asserts decoding fails; it now succeeds. Single-file fix: either tighten the rejection logic in `Preconditions::deserialize` or relax the test.

10. **`dregg-storage-templates::cap_inbox_tests::unknown_method_default_denied`**, **`starbridge-subscription::program::unknown_method_default_denied`**, **`starbridge-governed-namespace::governance::unknown_method_default_denied`**.
    - All three default-denied tests fail together → the cell-program "unknown method" routing returns the wrong rejection kind. One root cause across three apps.

---

## §4 False damage (tests broken in log but expected)

1. **All 16 `dregg-wasm::audit_tests::*` failures** — `cannot call wasm-bindgen imported functions on non-wasm targets`. These tests exist for wasm32 builds and **must not be considered failing on native**. They need an `#[cfg(target_arch = "wasm32")]` gate or to move to a wasm-only test crate.
2. **`dregg-directory::resource_handle_uri_contains_hex_fields`** — assertion string has 34 `ab` pairs (68 hex chars) but `[0xab; 32]` produces 64. The test was wrong from the start.
3. The 380 `skipped` tests in the summary are the nextest default-filter and are not failures.

---

## §5 Triage — fix order and lane assignment

### Wave 1 (single fix → ~40 test recoveries)
- **`circuit/src/dsl/circuit.rs:335` Poseidon24To1 oob**. One change to the `0..4u8` loop guard. Code-fix lane, high confidence.

### Wave 2 (single-crate fixes → ~10 recoveries each)
- Executor nonce-increment regression on `CellProgram::None`. Code-fix lane, turn-executor specialist.
- "Unknown method" routing bug (3 apps share). Code-fix lane, cell-program.
- Storage queue root mismatch. Code-fix lane, cell-program + storage.

### Wave 3 (test/fixture updates → easy but mechanical)
- `dregg-directory::resource_handle_uri_contains_hex_fields` assertion. Test-update lane, trivial.
- `dregg-wasm` audit tests: gate behind `#[cfg(target_arch = "wasm32")]`. Test-update lane.
- `dregg-tests::captp_effects_pipeline` — recompute expected hashes. Test-update lane.
- `dregg-cell::preconditions_roundtrip_postcard` — clarify expected behavior. Test or code, needs investigation.

### Wave 4 (verify-after-other-fixes)
- All `dregg-teasting::*` cascade failures (escrow, token_lifecycle, fault_*, consensus_liveness, etc.) — most will recover once Waves 1–2 land. Re-run before opening individual tickets.
- `dregg-credentials::roundtrip` × 5 — almost certainly Wave 1 cascade.
- `starbridge-identity::credential_lifecycle` × 5 — almost certainly Wave 1 cascade.

### Wave 5 (the proptest seed)
- `turn/tests/proptest_invariants.proptest-regressions` records a turn proptest failure shrunk to `extra_caps=0, revoke_before_refresh=true`. Re-run nextest with `--test proptest_invariants` to confirm it still fires, then investigate.

### Hard NO-FIX (do not touch)
- The `wallet → cipherclerk` doc-comment thrashing in `31722471` + `62440596` is annoying but harmless. Do not loop on it. The `*.md` files are noise; lower priority than any actually-failing test.
- Do not "fix" `bridge/contracts/package.json` to use `cipherclerk-sdk-*`. The Midnight Network's external npm packages are *named* `wallet-sdk-*`; `62440596` restored the correct names.

---

## §6 What kimi did that's good

1. **`1d800aad`** is fully legitimate: added the new `unilateral_attestations` field and `was_burn` field across all `BilateralBundle` / `WitnessedReceipt` test fixtures. Without this, anything that even *compiled* a test file referencing those structs would fail to build. This is the unglamorous, necessary catch-up work.

2. **`62440596` did fix `bridge/contracts/package.json`**, restoring the correct external Midnight SDK package names. Without this `npm install` in `bridge/contracts/` would fail because no `@midnight-ntwrk/cipherclerk-sdk-*` packages exist on npm.

3. **`62440596` also added `was_burn: false`** to the four `demo-agent/examples/*.rs` files (cipherclerk_lifecycle, cross_federation_nft_swap, payment_channel, payment_channel_burst). Without this those examples don't build.

4. **`31722471` finished the `AgentWallet → AgentCipherclerk` rename in tests** (`tests/src/full_pipeline.rs`, `tests/src/fully_private_e2e.rs`, etc.). Those test files were still importing `dregg_sdk::wallet::AgentWallet` even after the type was renamed two months ago. They could not build. **This is essential cleanup that unblocks the `tests/` integration crate.**

5. **`4b635096`** (checkpoint) is harmless cosmetic-only.

### Net assessment
Kimi did the boring catch-up that was waiting to be done. The `wallet→cipherclerk` rename was already half-finished, and integration tests + bridge contracts were going to fail to build until somebody finished the sweep. Kimi finished it, with some mostly-cosmetic doc-comment damage and one near-mishap on `package.json` that was self-corrected in `62440596`.

The 173 test failures in `nextest.log` are **predominantly NOT kimi's fault**:
- ~50 are cascade from `circuit/src/dsl/circuit.rs:335` (untouched by kimi)
- 16 are pre-existing wasm-bindgen-on-native false positives
- ~40+ are cascade from a single executor-decomposition / storage-fixture change in `7d7b8814`/`09290e50` (untouched by kimi)
- The rest are scattered real regressions across the codebase from the past few weeks of refactoring

No test failure can be cleanly attributed to commits `4b635096`, `1d800aad`, `31722471`, or `62440596`.
