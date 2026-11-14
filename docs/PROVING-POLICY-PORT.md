# Proving-policy port review

Implemented against current main; changes are left unstaged for coordinator review.
The source was commit `228f76f04`; its superseded worker/cache/checkpoint/pruning
implementations were not transplanted.

## Behavior and design

A `Turn::is_coordination()` turn is `not_required`: executor/committee signature
attestation only, never a validity proof. Balance changes (including an explicit
zero delta), foreign-cell effects, and empty effect forests do not qualify.
`--force-prove-all` and full-turn proving disable the exemption. Force does not
turn a disabled worker pool on. Required work with no worker is `unattested`,
not indefinitely pending. Worker failures become durable terminal failures.

Current main stages and rolls back HTTP admission. Async witness preparation now
runs at durable finalization against the canonical before/after actor images and
receipt, rather than proving that provisional admission image. The native signed
ingress regression checks exactly one canonical job and its pre-state.

Policy metadata is local auxiliary store configuration. Old receipts without the
metadata remain unattested unless actual proof material exists; no historical
backfill is attempted. Actual artifacts take precedence over a policy hint.
Receipt/proof/witness/anchor/SSE consumers preserve the distinction; proof-required
SDK fetchers reject exempt envelopes. Federation authentication and light-client
validity verification remain strict.

`dregg-node compact --data-dir DIR` runs before executor/network initialization.
Pinned redb 2.6.3's builder `open` opens an existing database and acquires its
exclusive nonblocking lock, then `Database::compact` relocates live pages and
releases free tail pages. It refuses a missing or locked store without creating
one. It reclaims space from deleted records; it does not delete live receipts,
blocks, proofs, checkpoints, or retained historical versions. Store schema and
trust-policy initialization are deliberately bypassed.

`--enable-pruning` stays removed. A successful startup with a no-op pruning flag
would leave service configuration claiming retention behavior that does not exist.
Remove that flag from service units; compaction is explicit physical maintenance.

## Files

- `node/src/{api,blocklace_sync,state,events,prove_pool,lib,compact}.rs` and MCP
  consumers: disposition, canonical job timing, failure reporting and command.
- `persist/src/lib.rs`: offline existing-store compaction and storage tests.
- Rust/TS/Python SDKs, CLI, TUI, Discord bot, extension, site explorer, both Drex
  sites, Starbridge desktop/live mirror and web surface: preserve/show signature
  status; reject it where a proof is required.
- Federation/lightclient tests: refuse missing authentication/proof, with canonical
  signed bytes unchanged. `docs/reference/node.md`: operator behavior and migration.

## Local validation

All Cargo invocations used `CARGO_TARGET_DIR=./target-dep CARGO_BUILD_JOBS=4
DREGG_LEAN_COLD_BUILD=0`, with package and test filters. No Lean/lake build ran;
these are marshal-only policy, storage and presentation greens, not native
cryptographic verification. Logs are ignored worktree files `dep-*-test.log`.
Standalone crates used a worktree-local Cargo home to unpack missing dependencies.
Generated standalone lockfile changes were removed from this patch.

Passed filters (18 Rust tests):

| Package / target | Filter | Tests |
| --- | --- | ---: |
| dregg-persist | offline_compaction_tests | 2 |
| dregg-node | proof_policy_ | 2 |
| dregg-node | prove_pool::policy_tests | 1 |
| dregg-node | compact::tests | 2 |
| dregg-sdk | not_required_hint_is_never_a_validity_proof | 1 |
| dregg-federation, turn_anchor_refusals | coordination_hint_never_bypasses_committee_authentication | 1 |
| dregg-lightclient, coordination_policy | coordination_policy | 2 |
| starbridge-web-surface | coordination_policy_survives_ingest_without_changing_receipt_identity | 1 |
| starbridge-v2, lib | coordination_policy_survives_live_step_projection | 1 |
| dregg-sdk-net | coordination_event_preserves_hint_without_a_proof | 1 |
| dregg-cli | coordination_is_rendered_as_signature_only | 1 |
| dregg-tui (standalone manifest) | coordination_policy_tests | 1 |
| dregg-discord-bot (standalone manifest) | coordination_policy_tests | 2 |

`node --test sdk-ts/test/proving-policy.test.mjs
scripts/tests/proving-policy-consumers.test.mjs`: seven passing tests, using the
freshly emitted SDK JS bundle and actual UI rendering functions. Tests distinguish
signature-only from proof, preserve receipt/SSE hints, and refuse malformed or
unknown proof envelopes. Compaction tests assert actual file shrinkage and retained
record equality. Rust receipt tests assert canonical serialized bytes/hash equality.
Syntax checks passed for both Drex servers, the v2 app, and Python smoke tests;
`git diff --check` passed.

## Checks still requiring another environment

No native STARK/PQ test below ran on this Mac: `dregg-lean-ffi/libdregg_lean.a`
and the required Lean seed are absent. On a seeded build host, run filtered
`cargo test -p dregg-node FILTER` for each exact test below (release mode for
proof-heavy cases; use that host's resource controls):

- `api::tests::remote_signed_envelope_e2e_accepts_then_refuses_tamper_and_replay`
- `api::tests::http_submit_prepare_rotatable_carries_real_actor_and_rotation`
- `turn_proving::tests::committed_turn_carries_verifying_proof`
- `transport_parity_e2e::the_two_http_turn_ingresses_agree_on_a_transfer_to_a_fresh_destination`
- `faucet_grant_e2e::faucet_grant_credits_the_recipient_after_finalization`
- `faucet_grant_e2e::a_second_faucet_grant_in_the_same_process_also_lands`
- `finalized_proof_failure_e2e::a_finalized_turn_whose_proof_failed_is_recorded_durably_and_served_as_gone`
- `finalized_proof_failure_e2e::an_honest_finalized_turn_leaves_no_proving_failure_record`
- `mcp::tests::grant_capability_commits_and_reports_its_attestation`
- `mcp::tests::bilateral_action_transfer_commits_and_reports_the_schedule`
- `mcp::tests::register_name_commits_and_reports_a_live_attestation_disposition`

Additional blockers/unchecked surfaces:

- Python Rust `proving_policy_tests::proof_required_python_paths_reject_exempt_and_malformed_responses`:
  compilation fails because the standalone manifest lacks main's local p3-fri
  patch: missing `CpuTwoAdicFriFold` / `TwoAdicFriFoldBackend`, and mismatched
  `HidingFriPcs` generic arity. No crypto dependency substitutions were made.
- Python smoke `test_coordination_proof_is_refused` and `test_proof_lazy_fetch`:
  no pytest or installed `dregg` module; identity setup also needs native PQ/Lean.
- TypeScript declaration build: missing local `dregg-wasm` module (TS2307).
  JS emission succeeded and its four policy tests passed; no WASM build attempted.
- Desktop `deos_desktop::dregg_computers::coordination_policy_tests::coordination_policy_receipt_row_is_signature_only`:
  requires the gpui-ui feature; no native desktop build attempted.
- Extension browser packaging/runtime was not exercised.

## Consensus, trust and format

No canonical receipt/block/anchor/proof encoding, signature payload, VK, epoch or
genesis change. Rust receipt policy hints are outside canonical serialization.
There are additive HTTP/SSE JSON fields/status values and local policy metadata.
Trust remains executor/committee attestation for exempt turns, with no invented
validity guarantee. Existing async proof coverage remains state-transition coverage;
this patch does not add authority or freshness coverage.

Next: run the listed seeded-host regressions, especially the strengthened canonical
job test, and resolve standalone Python dependency alignment before release. Then
exercise SDK packaging and desktop/extension consumers in their normal build lanes.
