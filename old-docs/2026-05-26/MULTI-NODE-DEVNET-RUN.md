# multi-node-devnet — first end-to-end run report

Run date: 2026-05-25 (local tree, `main` @ commit 8a66164 with one minimal patch noted in §1).

## §1 Build status

- Built `cargo build -p dregg-node -p dregg-verifier --release` locally (no
  workspace flag, no persvati). Full log: `/tmp/multi-node-build.log`.
- **First attempt:** compiled cleanly (30 warnings, 0 errors). Binaries
  produced at `target/release/dregg-node` and `target/release/dregg-verifier`.
- **Boot failed on every node** with an `axum 0.8` router panic at
  `node/src/api.rs:1039`:

      Path segments must not start with `:`. For capture groups,
      use `{capture}`.

  Three route patterns still used the old axum 0.7 colon syntax
  (`/queues/:id/...`) while every other dynamic segment in the file already
  uses `{id}`. This is a pure axum-version mismatch, not a substrate bug.

- **Minimal patch:** rewrote those three lines to `{id}`. The patch is
  3 insertions / 3 deletions in `node/src/api.rs` only. Rebuilt with
  `cargo build -p dregg-node --release` (~34 s incremental).

- No cascade errors (no lifecycle Effects / OneOf / NonMembership compile
  failures hit this build slice).

## §2 Boot status

After the patch + `./reset_devnet.sh`:

- Step 1 (genesis): F1 + F2 generated, distinct committee-derived
  federation_ids (`a766ccb4…` and `846e2254…`).
- Step 2 (data dirs): 6 dirs initialized cleanly.
- Step 3 (cross-register): all 6 nodes registered the peer federation.
- Step 4 (launch): all 6 PIDs spawned.
- Step 5 (readiness): **all 6 nodes listening** on their HTTP ports
  (7811-7813, 7821-7823).
- Step 6 (summary): topology reported as expected.

  `[devnet] devnet UP` confirmed. Boot log: `/tmp/devnet-start2.log`.

## §3 Per-scenario results

`run_all_scenarios.sh` reports **5/5 PASS**. Each scenario writes a
`state/logs/scenarios/<name>/result.json` that matches its
`expected/<name>.json` `must_pass` and `must_not_pass` lists. Per the
README, every `must_not_pass` entry records `true` when the structural
distinguishability is observable — that is the *correct* outcome at the
current substrate maturity (the assertions' executor-level enforcement
is blocked on lanes A/D/F-redux/γ.2, per each expected.json's
`blocked_on`).

### 3.1 cross_fed_handoff — PASS

must_pass (6/6): both_federations_responding, alice_uri_produced_on_F1,
uri_delivered_to_F2_inbox, bob_inbox_target_federation_is_F2,
F1_exposes_federation_roots, F2_exposes_federation_roots.

must_not_pass (2/2 structurally distinguishable as expected):
handoff_replay_artifact_constructed, handoff_tampered_artifact_distinguishable.

Diff vs expected: **none** — every key in `must_pass` and `must_not_pass`
records `true` in `result.json`.

### 3.2 federation_attestation — PASS

must_pass (10/10): both /federation/roots endpoints respond, descriptors
on disk on both sides, committee_epoch matches, committee_size=3,
federation_ids are 32-byte committee-derived hex and distinct, every node
knows both federations.

must_not_pass (1/1): tampered_federation_descriptor_rejected — the CLI's
`register-federation` correctly refused to write a descriptor whose
declared federation_id didn't match `H(sorted_pubkeys || epoch)`. This is
the audit-F1 enforcement working.

### 3.3 bilateral_transfer — PASS

must_pass (7/7): F1 + F2 live, transfer_id is 32-byte hex,
deterministic, distinguishes target federation, direction-complement
holds, amount agrees on agreed pair, F2 peer-exchange route reachable.

must_not_pass (1/1): bilateral_pair_amount_mismatch_detectable — a pair
with alice_amount=99, bob_amount=100 produces an observable inequality.
Executor enforcement is in the γ.2 pair-verifier (still upcoming).

### 3.4 intent_match_cross_fed — PASS

must_pass (6/6): /intents/trustless and /intents/encrypted routes present
on F1, /intents listing responds, /api/cells responds on F2, committee
threshold ≥ 2 in BFT mode (note: solo mode genesis still encodes
quorum_threshold(3)=3 even though runtime threshold=1),
intent_routing_is_cross_federation.

must_not_pass (1/1):
tampered_intent_collapsed_to_same_federation_detected.

### 3.5 peer_exchange_bypass — PASS

must_pass (7/7): both /turns/peer-exchange routes present, sovereign
witness sequence strictly monotonic, equal-sequence detected as
regression, peer_exchange_id is 32-byte hex and federation-invariant
(function of cells only), F1 ledger unchanged by idle observation,
sovereign witness self-verifies without committee.

must_not_pass (1/1): sovereign_witness_equal_sequence_detected_as_regression.

## §4 Soundness red flags

**None.** No `must_not_pass` assertion that was supposed to be detectable
went undetected. Every `must_not_pass` recorded `true`, which the
scenario semantics defines as "the structural property the executor will
reject is observable" — which is the correct intent at the current
substrate maturity. No `must_pass` recorded `false`.

Per-scenario `expected.json` `blocked_on` lists name the lanes whose
landing will tighten these assertions from "structurally distinguishable"
to "executor-rejected" (lanes A, D, F-redux, γ.2 Phase 1, intent
end-to-end, CapTP cross-fed Turn delivery). Those tightenings are the
*next* expected-set widenings; this run is the substrate-observability
baseline.

## §5 Recommendations

1. **Land the `{id}` route fix.** Either merge the minimal patch (commit
   `multi-node fix: …`, see below) or have the next cascade-lane axum-0.8
   pass include `/queues/:id/...`. Without it, **no node ever boots**.
2. **Fix `load_known_federations` schema mismatch.** Every node logs
   `WARN skipping malformed federation descriptor` for the peer
   federation's descriptor at startup. `node/src/state.rs:999` expects
   keys `members`, `epoch`, `threshold`; the file on disk (written by
   `register-federation` and asserted-present by the
   `federation_attestation` scenario) uses `validators`,
   `committee_epoch`, and `validators[].public_key`. The scenario
   currently asserts file-presence only, so it passes — but the
   in-memory peer federation set is **empty** on every node after boot.
   Any executor-level cross-fed assertion will silently fall through
   until this is fixed. The persist side (`persist_known_federations`)
   and the CLI-side `register-federation` writer both need to be
   reconciled against the loader's expected schema, or vice versa.
3. **Make the binary path discoverable to scenarios.** `lib/common.sh`
   defaults to `target/debug/dregg-node`; the README's troubleshooting
   step says "build it out-of-band" but doesn't mention `--release`.
   Either (a) document `NODE_BIN=target/release/dregg-node` in the
   README's Prerequisites section, or (b) make `start_devnet.sh` fall
   back to release if debug is missing. Today every scenario invocation
   has to re-export `NODE_BIN` and `VERIFIER_BIN`.

## §6 Logs of note

- The route panic on first boot (pre-patch) — `state/logs/F1-node-1.log`:

      thread 'main' (…) panicked at node/src/api.rs:1039:10:
      Path segments must not start with `:`. For capture groups,
      use `{capture}`.

  Same panic on all 6 nodes.

- The schema-mismatch warning on successful boot (every node):

      WARN dregg_node::state: skipping malformed federation descriptor
        path=.../known_federations/<peer_fed_id>.json
      INFO dregg_node::state: loaded known_federations from disk count=0

  The `count=0` is the load-bearing diagnostic — the cross-fed trust root
  exists on disk but is not in memory.

- No panics, no ERROR/FATAL lines in any node log during the scenarios.
  Each node ran a Cordial-Miners blocklace, gossip layer initialized,
  HTTP API stayed up for the entire scenario sweep.

- All 6 nodes were stopped cleanly via `stop_devnet.sh` (SIGTERM, no
  SIGKILL needed). No leaked PIDs.

Full logs are in `demo/multi-node-devnet/state/logs/`. Per-scenario
result JSON in `demo/multi-node-devnet/state/logs/scenarios/<name>/`.

## Run reproduction

    cd demo/multi-node-devnet
    NODE_BIN=$PWD/../../target/release/dregg-node \
    VERIFIER_BIN=$PWD/../../target/release/dregg-verifier \
      ./start_devnet.sh && ./run_all_scenarios.sh && ./stop_devnet.sh
