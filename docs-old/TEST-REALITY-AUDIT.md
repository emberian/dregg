# Test Reality Audit — dregg

Audit date: 2026-05-25
Auditor: read-only research lane
Scope: claim-bearing tests in cell/, turn/, circuit/effect_vm/, bridge/, intent/,
federation/, verifier/, demo/, tests/, teasting/, apps/, starbridge-apps/

The question this audit answers:

> Are dregg's "passing" claims backed by tests that genuinely prove the
> thing claimed, or by tests that look like proofs and aren't?

A test is **real** if (1) it constructs the artifact through the real surface
the system uses, (2) it invokes the actual verifier / executor / AIR /
runtime under audit, and (3) its assertion fails when the system genuinely
mis-behaves on that input. A test is **seeming** if it asserts something
that holds by construction, mocks the thing it claims to verify, prints
instead of asserting, is silently `#[ignore]`d, or asserts on a
divergent code path while documenting the real claim as "still TODO".

The headline: dregg's **unit tests for primitives** are largely real
(predicates, threshold sigs, CellState, NonMembership). dregg's
**adversarial / soundness / cross-cutting tests** are the weak spot
— this is exactly the place where seemingness costs the most. The
multi-node-devnet scripts are scaffolding-shaped: they test their own
fixtures and call it composition. The `cross-app-e2e` Python demo is
the brightest spot in the whole audit; it's structurally honest.

---

## §1. Method and scope

Sampled (counts approximate, big files spot-sampled):

| Area | Test LOC | Sampled | Notes |
| ---- | -------- | ------- | ----- |
| `cell/src/predicate.rs` | ~600 | all `#[test]` | post-soundness-emergency suite |
| `cell/src/tests.rs` | 1922 | first 200 + zero-pinned hits + p1_5/p1_6 | |
| `turn/src/tests.rs` | 10776 | first 700 + signature / replay / executor tests | |
| `turn/src/executor/*` | ~1700 | atomic.rs replay-chain block, migration.rs | |
| `circuit/src/effect_vm/tests.rs` | 3368 | all #[test] names + soundness block + tamper block | |
| `circuit/src/backends/kimchi_native/tests.rs` | 2201 | spot — `assertion_gates_constraining` | |
| `circuit/src/backends/mina/tests.rs` | 1450 | spot — `add_copy_constraints_no_panic` | |
| `bridge/src/tests.rs` | 732 | end-to-end + denial + chain | |
| `verifier/src/lib.rs` | 1194 | replay_chain + pi_binding adversarial set | |
| `federation/src/threshold.rs` | 530 | full | |
| `intent/src/trustless.rs` | ~1100 of 2415 | sample of submit/aggregate/decrypt tests | |
| `apps/identity/src/tests.rs` | 844 | first 300 | |
| `apps/gallery/src/private_vickrey.rs` | spot | one `#[ignore]` justified | |
| `demo/cross-app-e2e/verify.py` | 294 | full | + `canonical.py` 181 LOC |
| `demo/two-ai-handoff/charlie.py` | 414 | full | + `silver_helper.rs` 1669 LOC spot |
| `demo/multi-node-devnet/scenarios/*.sh` | ~1200 across 5 | full of 2 (cross_fed_handoff + intent_match_cross_fed) | |
| `tests/src/*.rs` workspace harness | ~13000 | structural — counted ignores + read 2 honesty files | |
| `teasting/tests/*.rs` | ~6000 | counted ignores, sampled storage_faults | |
| `protocol-tests/src/invariants/effect_vm_differential.rs` | 1256 | first 50 LOC | |

**Not sampled** (would need a follow-up lane):
- `dregg-dsl-tests/` (~10000 LOC, sees a lot of TODO/Phase-3 markers)
- `circuit/src/backends/kimchi_native/tests.rs` middle/end
- `coord/src/tests.rs` body (only `#[cfg(any())]` block read)
- `chain/`, `wire/`, `tokenizer/`, `directory/` tests
- `starbridge-apps/*/tests/` (only governed-namespace zero-pinned spot)
- the bulk of `teasting/tests/*.rs` (storage_faults sampled)
- `protocol-tests` proptest bodies
- the apps' private-vickrey / gallery / privacy-voting interior tests

---

## §2. The seeming-tests catalog

Each entry: file:line — what it claims to test — why it's seeming — fix.

### S1. FRI single-row gap silently swallowed in claim-bearing test
**File:** `circuit/src/effect_vm/tests.rs:177`
**Test:** `test_wrong_state_transition_caught`
**Claim:** "Wrong state transition is caught."
**Reality:** The test tampers row 0 of a 7-effect trace, runs `prove`/`verify`, then if `result.is_ok()` it **only prints to stderr** ("[stage2-fri-single-row-gap] STARK accepted single-row tamper"). The test passes whether or not the STARK rejects the forgery. The accompanying AIR-level `assert_ne!(c0, BabyBear::ZERO)` only proves the algebra is non-zero at that point — it does NOT prove the STARK rejects. The headline soundness claim ("wrong state transition is caught") is **not enforced** by this test.
**Fix:** Either (a) widen FRI queries / change parameters until single-row tamper is reliably caught, then `assert!(result.is_err())`; or (b) rename the test to `test_air_constraint_nonzero_at_tampered_row` so it doesn't claim what it doesn't prove. **Do not** leave a test whose name claims soundness while its body documents a soundness gap.

### S2. Claim-bearing soundness test `#[ignore]`d as "flaky"
**File:** `circuit/src/effect_vm/tests.rs:1700–1722`
**Test:** `test_soundness_non_boolean_delta_sign_rejected`
**Claim:** Non-boolean `net_delta_sign` MUST be rejected.
**Reality:** `#[ignore = "flaky: relies on FRI sampling to catch a single-row tamper"]`. The author wrote the right adversarial test, observed it fails to consistently reject, and silenced it. The "must be rejected" comment is still there as a tripwire, but in CI it's a no-op.
**Fix:** Same as S1 — fix the FRI parameters or reduce trace width so a single-row tamper reliably reaches a FRI query. This is a real soundness gap, not a test-hygiene issue.

### S3. Adversarial test that asserts on a divergent code path
**File:** `circuit/src/effect_vm/tests.rs:1754–1777`
**Test:** `test_soundness_wrapped_balance_different_commitment`
**Claim:** "A crafted trace with wrapped balance produces a DIFFERENT state commitment."
**Reality:** Only asserts `honest_final.state_commitment != wrapped_state.state_commitment`. The verifier is **never invoked**. The closing comment ("A verifier that knows the expected new_commitment will reject…") is left as a paragraph of prose, not as test code. The test proves Poseidon2 is collision-resistant — it does not prove the verifier rejects.
**Fix:** Construct a wrapped-balance trace, hand to `verify(&air, &proof, &public_inputs)` with the honest expected commitment as PI, and assert `result.is_err()`.

### S4. Tamper-detection asserted only at the hash layer, not the AIR
**File:** `circuit/src/effect_vm/tests.rs:1001–1030`
**Test:** `test_noop_padding_cannot_be_exploited`
**Claim:** Implied by the name — injecting a NoOp into the trace cannot pass.
**Reality:** Only asserts `compute_effects_hash(real) != compute_effects_hash(tampered)`. This is "blake3 has collision resistance, your honor." It does not produce a tampered trace, run prove/verify, and assert rejection. Same shape as S3.
**Fix:** Generate a tamper trace that injects NoOp, attempt to prove with the honest-effects-hash PI, assert verify fails.

### S5. Interior-row tamper covered by AIR-only check (not STARK)
**File:** `circuit/src/effect_vm/tests.rs:1102–1160`
**Test:** `test_interior_noop_state_change_caught`
**Claim:** Interior NoOp padding state-change is "caught."
**Reality:** Author documents (lines 1100–1101) that they "verify via direct constraint evaluation (deterministic) rather than relying on probabilistic STARK verification." So the test calls `air.eval_constraints(...)` directly and never goes through `verify`. Same problem as S1: the algebra is checked, the cryptographic enforcement isn't.
**Fix:** Run `verify` on the tampered trace and assert failure. If it's flaky, that's a soundness gap, see S1.

### S6. Verifier replay-chain test passes for the wrong reason — author admits it
**File:** `verifier/src/lib.rs:986–1002`
**Test:** `replay_chain_no_witness_no_hash_is_unwitnessable_only_when_proof_invalid`
**Claim:** The `Unwitnessable` rejection branch fires when no bundle and no hash are provided.
**Reality:** Author comment: "No bundle, witness_hash zero, no proof → STARK verify rejects FIRST (empty proof bytes). The Unwitnessable branch fires only when proof + hash zero coexist; here proof is empty so step 1 already fails." The test passes because the STARK step rejects, not because Unwitnessable does. The actual `Unwitnessable` branch (`verifier/src/lib.rs:598, 609`) is **never exercised by this test**.
**Fix:** Build an entry that has plausible-looking nonzero proof bytes (so the STARK step's structural check passes) but the trivial witness state, and assert `Unwitnessable`. Or: extract the Unwitnessable predicate, test it directly with a constructed entry that bypasses STARK.

### S7. Subscription head/tail "advance" only validates the JSON the agent itself wrote
**File:** `demo/cross-app-e2e/verify.py:152–161`
**Test in expected.json:** `subscription_head_advances_claim` / `_fulfill` / `_settle`, `bob_consume_advances_tail_by_one`
**Claim:** Subscription head advances by +1 per publish.
**Reality:** The check reads `dan_claim["new_head"]` (a number Dan's script wrote into the file) and compares against `1`. If Dan's script has a bug that writes `new_head = 1` regardless of whether the subscription substrate actually advanced, the assertion still passes. The canonical re-derivation in this file (`bounty_state_payload_hash`) is honest — the subscription head check is the weak spot. **However**: §6 will note that dregg's cross-app-e2e is on the whole the best demo in the audit because of the *other* checks.
**Fix:** Have the canonical Python compute the expected head from the prior state's pinned head + the publish count, not read it back from Dan's output.

### S8. `cross_fed_handoff.sh` — pure scaffolding theater
**File:** `demo/multi-node-devnet/scenarios/cross_fed_handoff.sh:114–199`
**Tests:** `alice_uri_produced_on_F1`, `uri_delivered_to_F2_inbox`, `bob_inbox_target_federation_is_F2`, `handoff_replay_artifact_constructed`, `handoff_tampered_artifact_distinguishable`
**Claim (from expected.json):** Cross-federation bearer-cap handoff works; replays and tampers are distinguishable.
**Reality:** The script `cat > handoff.uri.json <<EOF ... EOF` writes a placeholder JSON, then `cp`'s it. Every assertion checks "did I write that file?" / "does diff produce output?":
- `alice_uri_produced_on_F1 = [ -s handoff.uri.json ]` → tests `cat` produces a non-empty file
- `handoff_replay_artifact_constructed = (n1 == n2)` after `cp` of the same file → tests `cp` preserves bytes
- `handoff_tampered_artifact_distinguishable = diff_count > 0` after `jq '.permissions = "ALL"'` → tests `jq` modifies its input
None of these touch the cross-fed handoff substrate. The script's own comments admit it (lines 30–34, 98–108) but the assertions still claim "true" in the result JSON, which `run_all_scenarios.sh` collates into a green check.
**Fix:** Either (a) the scenario should call the real `dregg_create_cross_fed_bearer_cap` MCP tool and submit the resulting Turn to F2; if the lane isn't built yet, mark every assertion `null`/`pending`, NOT `true`. Or (b) move these to a `pending/` directory until the lane lands so they cannot accidentally be counted as passes.

### S9. `intent_match_cross_fed.sh` — same scaffolding shape
**File:** `demo/multi-node-devnet/scenarios/intent_match_cross_fed.sh:104–120`
**Tests:** `intent_routing_is_cross_federation` (and friends)
**Reality:** Script writes `intent.json` with `submitter_federation=$F1_ID`, `target_federation=$F2_ID`, then asserts `sub_fed = F1 && tgt_fed = F2 && sub_fed != tgt_fed`. This tests bash string interpolation and jq, not the intent surface. The intent body is **never submitted** to F1's executor.
**Fix:** POST the body to `/intents/trustless` and assert acceptance, then poll for decryption + settlement.

### S10. Disabled-via-`#[cfg(any())]` causal-DAG tests
**File:** `coord/src/tests.rs:1394, 1446`
**Tests:** `many_node_causal_dag`, `rejected_turn_still_in_dag`
**Claim:** Multi-node causal DAG behaves correctly.
**Reality:** Both wrapped in `#[cfg(any())]` (a Rust idiom for "always-false" that disables the test). Documented as "blocked on causal-test-port lane", but until that lane lands, the suite includes 0 multi-node causal-DAG tests. Anyone reading `cargo test -p dregg-coord` will see "all green" while these never run.
**Fix:** Move to a `tests/causal_dag.rs.disabled` file or document them in `BLOCKED-TESTS.md` so the disabling is louder.

### S11. Massive ignore-list in `tests/src/executor_honesty_threats.rs`
**File:** `tests/src/executor_honesty_threats.rs:108, 141, 151, 161, 167, 204, 214, 224, 230, 240, 250, 295, 305, 318, 328, 338, 344, 354, 364, 370, 376`
**Tests:** 21 separate `#[ignore = "blocked on EXECUTOR-HONESTY-AUDIT.md T*"]` tests covering T2 (verify path is the only entry to executor), T4 (state binding), T6 (federation_id in signing message), T7 (executor key in receipt), T8 (previous_receipt_hash binding), T11 (TURN_HASH PI binding), T12 (conservation derivation), T13 (Cell::remote_stub_with_id escape hatch), plus three cross-cutting threats.
**Claim (from EXECUTOR-HONESTY-AUDIT.md):** These are the threat model for executor honesty.
**Reality:** The entire suite of threats is documented and stubbed out. The verifier-side PI binding tests (`verifier/src/lib.rs:1046–1098`) cover T8/T11 at the verifier layer — that's real and good — but the executor-side and AIR-side teeth are absent from CI.
**Fix:** The unblock-by-lane labels are clear; this is a tracking problem, not a test-hygiene problem. The audit's recommendation: enumerate these in `SILVER-DEBT.md` (which already exists) so the user can see at a glance which T* threats are CI-covered vs documentary-only.

### S12. `sovereign_witness_threats.rs` — 19 ignores
**File:** `tests/src/sovereign_witness_threats.rs`
**Reality:** Module header confesses: "All currently `#[ignore]`d on the sovereign-witness AIR teeth lane." So sovereign-cell witness threats — which the two-ai-handoff demo claims it covers — are tested entirely by the demo's silver_helper self-verify (which IS real, see §6), and **NOT** by any `cargo test` claim-bearing assertion.

### S13. `gamma2_bilateral_binding.rs` — 19 ignores
**File:** `tests/src/gamma2_bilateral_binding.rs`
**Reality:** "Most are `#[ignore]`d on γ.2 wiring." The bilateral-binding teeth that `silver_helper.rs` exercises live entirely in the demo, not the Rust test suite.

### S14. `witnessed_predicate_kinds.rs` — 18 ignores
**Reality:** "positive paths are all `#[ignore]`d on the caveat-correctness lane." But: the post-audit `cell/src/predicate.rs` *negative* tests (audit_attack_default_rejects_* family, lines 2052–2103) ARE real and run. So the soundness floor (default registry rejects garbage) is enforced; the positive-path correctness floor (when honestly produced, accepted) is not. Acceptable, but worth knowing.

### S15. `state_constraint_variants.rs` — 16 ignores
**Reality:** The slot-caveat surface has positive-path tests; negative paths and sentinel-shape tests are `#[ignore]`d. The demo's `silver.slot-caveat-suite.json` covers some of these — see §6.

### S16. `dispatchless_test`: `test_predicate_age_gte_various` short-circuits the verifier
**File:** `apps/identity/src/tests.rs:112–142` + `apps/identity/src/presentation.rs:226–254`
**Claim:** Predicate `age >= threshold` verification yields the expected result.
**Reality:** The `false` branch (age 30, threshold 65) **never reaches the STARK verifier**: `generate_predicate_proof` short-circuits at the "satisfiable" check (line 238) and returns `PredicateResult { verified: false, proof: None, ... }`. The test asserts `verified == false` and passes — but it never exercised the "verifier rejects a false predicate proof" path. The `true` branch DOES reach `verify_predicate_dsl` and IS real. So the test is half-seeming: positive path real, negative path tautological.
**Fix:** Either (a) construct a forged `proof` for the `false` case and submit it through `verify_predicate_dsl`, asserting rejection; or (b) split the test into two and rename the negative one to `test_unsatisfiable_predicate_short_circuits` so the claim matches what's tested.

### S17. `replay_chain_detects_witness_hash_tamper` passes for the wrong reason
**File:** `verifier/src/lib.rs:962–984`
**Claim from name:** "Detects witness-hash tamper."
**Reality:** Author admits in the comment: "The proof step rejects first because we use empty proof_bytes — but the structural check still demonstrates the verdict shape is wired." So the test confirms `overall_verified == false`, but the cause is "the proof was empty," not "the witness hash was wrong." The witness-hash-tamper detection path is **not exercised** by this test.
**Fix:** Same shape as S6 — supply non-empty proof bytes (or stub the STARK step) so the rejection comes from the hash mismatch.

### S18. `demo-agent/examples/unified_harness.rs` disabled via `#[cfg(any())]`
**File:** `demo-agent/examples/unified_harness.rs:1109`
**Comment:** "disabled: API drift — Federation::new no longer accepts &[&str]; needs port to verifier_only(members, epoch, threshold)"
**Reality:** Module-level disable on what the file header advertises as the unified-harness example. The doc comment promises a worked example; the body compiles to a unit because no test functions exist behind the gate.

### S19. `protocol-tests/src/invariants/effect_vm_differential.rs` "passthrough gap" tripwires
**File:** `protocol-tests/src/invariants/effect_vm_differential.rs:20–22` (module header)
**Reality:** Module documents that "PASSTHROUGH GAP" tests are intentionally `#[ignore]`d — they describe known gaps where the AIR's state delta is a subset of the runtime's. The tests are tripwires for when AIR coverage expands. This is a *deliberate* and *documented* tradeoff, not a bullshit; flagged here because anyone running `cargo test -p dregg-protocol-tests` will see green while 22 effect variants have known AIR-vs-runtime divergence.

### S20. `every_variant_roundtrip.rs` — 2 ignores covering "the audit observed 31 of 41" variant gaps
**File:** `tests/src/every_variant_roundtrip.rs:843–897`
**Reality:** The roundtrip test for every effect variant is gated on per-variant AIRs landing. The roundtrip works at the postcard layer (real test, runs); the AIR-roundtrip does not.

---

## §3. The real-tests showcase — dregg's house style when it's good

These are the load-bearing examples of what "real" tests look like in this codebase. Worth holding up as the bar for new tests.

### R1. `cell/src/predicate.rs` post-AIR-audit adversarial family
**Lines 2052–2115.** Every built-in witnessed-predicate kind has an `audit_attack_default_rejects_*_forged_one_byte_proof` test. Each:
1. Constructs a forged 1-byte proof against a known commitment.
2. Submits it through `WitnessedPredicateRegistry::default_builtins().verify(...)`.
3. Asserts the *specific* `WitnessedPredicateError::Rejected` variant.
4. Repeats with 64 bytes of garbage.

This is the prior-incident regression suite for the ce1e2def "playground bypass" attack and it is genuine. The associated `audit_default_registry_keeps_nonmembership_real_verifier` (line 2108) pins the dispatch by name (`"sorted-neighbor-non-membership"`) so a silent fall-back to a stub can't pass undetected.

### R2. `cell/src/predicate.rs` NonMembership adversarial family
**Lines 1667–1758.** Tests for the renunciation / non-membership predicate include:
- accepts legal renunciation (positive)
- rejects candidate equal to lower neighbor (the prover IS in the set)
- rejects candidate equal to upper neighbor
- rejects out-of-interval candidate
- rejects forged zero adjacency tag (soundness binding to commitment)
- rejects malformed proof bytes

Every test exercises a different adversarial shape against the real `WitnessedPredicateRegistry::with_stubs()` (which uses the real `sorted-neighbor-non-membership` verifier). This is the bar.

### R3. `bridge/src/tests.rs::test_end_to_end_macaroon_to_zk_proof`
Mints a real `MacaroonToken`, attenuates twice, builds the fold chain through `BridgePresentationBuilder`, generates a real STARK proof via `builder.prove`, and verifies through `verify_presentation_bb`. The federation-root computation is a Python-style mirror of the on-circuit Poseidon2 path (lines 48–67). Pinning `proof.is_valid()`, `proof.chain_length == 3`, `policy_rule_id == 40 (APP_ACTION_SECURE)`, and a final STARK verify against the computed root — five independent checks at five different layers.

### R4. `bridge/src/tests.rs::test_issuer_membership_circuit_rejects_wrong_federation_root`
Direct adversarial test: submit a proof with a different federation root and assert verification fails. Tests the actual security claim, not the structural roundtrip.

### R5. `turn/src/tests.rs::test_real_signature_verification` + `test_invalid_signature_rejected` + `test_wrong_key_signature_rejected`
Triple — positive Ed25519, garbage signature, wrong-key signature. Real `ed25519_dalek::SigningKey`, real `TurnExecutor`, real ledger. The negative tests pattern-match the exact `TurnError::InvalidAuthorization { reason }` and pin the reason string. This is the bar for "we tested signature verification."

### R6. `turn/src/executor/atomic.rs` previous_receipt_hash chain tests
**Lines 895–976.** Three tests:
- `previous_receipt_hash_replay_blocked` — second turn from same agent without prev hash → `ReceiptChainMismatch`
- `previous_receipt_hash_wrong_chain_rejected` — second turn with wrong hash → `ReceiptChainMismatch`
- `previous_receipt_hash_correct_chain_accepted` — properly-chained turns commit

Each goes through the real `TurnExecutor`, real ledger, real receipt-chain bookkeeping, and pattern-matches the exact error variant. T8 of EXECUTOR-HONESTY-AUDIT is closed at the executor layer by these tests (even though the AIR-side T8 is in the S11 ignore-pile).

### R7. `circuit/src/effect_vm/tests.rs` storage queue lifecycle (lines 1802–1985)
The storage AllocateQueue / EnqueueMessage / DequeueMessage / multi-effect lifecycle / Resize tests each:
1. Construct a `CellState`.
2. Run `assert_effect_vm_roundtrip(...)` which evaluates AIR constraints over ALL rows with three different challenge values AND runs prove/verify.
3. Pin the net delta and the expected queue root hash.

This is what `test_wrong_state_transition_caught` (S1) should look like, only inverted — verify accepts the honest case, and you'd want a sibling test that constructs a tamper trace and asserts verify rejects.

### R8. `verifier/src/lib.rs::pi_binding_rejects_tampered_*` family (lines 1046–1140)
For each of `TURN_HASH_BASE`, `PREVIOUS_RECEIPT_HASH_BASE`, `IS_AGENT_CELL`: construct a receipt, build PI vector from it, XOR a bit, call `check_receipt_pi_binding`, assert the rejection names the tampered field. This is *real* T11/T8 coverage at the verifier layer, isolated from the STARK step so PI completeness is testable independently. Excellent shape.

### R9. `federation/src/threshold.rs` threshold-signature suite (lines 404–520+)
Real `generate_test_committee`, real sign_share, real aggregate, real verify. Below-threshold rejects, wrong-message rejects, serialize/deserialize roundtrip preserves verification, constant-QC-size across committee sizes. Standard but properly executed — nothing seeming here.

### R10. `intent/src/trustless.rs::test_encrypted_intents_opaque_before_decrypt`
Goes the extra step of trying `postcard::from_bytes::<Intent>` on the raw ciphertext bytes and asserting deserialization fails — confirming the encrypted payload doesn't accidentally look like a valid plaintext intent. Most codebases would skip that and just assert "decrypted is None."

### R11. `circuit/src/backends/mina/tests.rs::test_assertion_gates_constraining` (lines 800–872)
Uses `std::panic::catch_unwind` to wrap a dishonest-witness prove attempt and asserts it panics. Comment: "If this passes, the assertion gates are not constraining." That's exactly the right framing for circuit-level adversarial tests.

### R12. `demo/cross-app-e2e/verify.py` + `canonical.py`
See §6 for the full breakdown. The structurally most honest demo in the codebase: independent Python implementation of every commitment derivation, then cross-checked against the Rust starbridge-apps' output. Negative tests forge issuers / schemas / actor pubkeys / prior-states and assert the resulting commitments don't match.

### R13. `teasting/tests/storage_faults.rs`
Real fault simulator harness (`FaultyNetwork`, `MessageBuffer`) drives storage subsystems through partitions and byzantine behavior. Tests invariants ("deposits never lost") under real fault injection, not against mocks. ~30 tests, no `#[ignore]`s.

---

## §4. Per-area assessment

Subjective "real-coverage" estimate — fraction of the area's CLAIMS that have a real test against them, weighted by how load-bearing each claim is. Ranges, not point estimates.

| Area | Real-coverage | Why |
| ---- | ------------- | --- |
| `cell/predicate.rs` | 75–85% | Post-audit adversarial family + NonMembership are real (R1, R2). Custom-kind dispatch tested. Gap: positive-path correctness of every built-in verifier (most are `with_stubs()` rejecting garbage, real verification only for NonMembership) |
| `cell/src/tests.rs` body | 70–80% | Lifecycle + permissions + delegation + P1-* audit regressions all real; few zero-pinned sentinels are legitimately documented |
| `turn/src/tests.rs` + `executor/*` | 75–85% | Signature verification, chain replay, atomicity, capability isolation all real (R5, R6). The proof verifier IS mocked (`AlwaysAcceptVerifier`/`AlwaysRejectVerifier`) but only to test executor dispatch — real proof-circuit tests live elsewhere. Gap: AIR-side T2/T4/T6/T7/T13 threats (see S11) are all `#[ignore]`d |
| `circuit/effect_vm/tests.rs` | 55–70% | Roundtrip + multi-variant compose tests real. The soundness/tamper block (S1–S5) is where seemingness clusters. ~6 of the 85 tests have the "passes for wrong reason" or "ignored as flaky" shape. CapTP variants real |
| `circuit/backends/kimchi_native` | sampled only; assertion_gates_constraining is real (R11) |
| `circuit/backends/mina` | sampled only; copy-constraint wiring + assertion-gate panic-catching are real |
| `bridge/src/tests.rs` | 80–90% | End-to-end + denial + wrong-root rejection + fold-chain verification all real (R3, R4). One of the cleanest test suites in the codebase |
| `verifier/src/lib.rs` | 60–75% | `pi_binding_*` adversarial family is real (R8). Two replay-chain tests pass for wrong reasons (S6, S17) — minor but documented |
| `federation/src/threshold.rs` | 90% | Standard threshold-sig suite, real (R9) |
| `intent/src/trustless.rs` | 70–80% | Real engine integration tests, including post-decrypt structural checks (R10). Gap not audited: cross-fed routing semantics under the encrypted path |
| `apps/identity/src/tests.rs` | 60–70% | Selective disclosure / revocation / non-revocation real. Predicate-result negative path short-circuits the verifier (S16) |
| `apps/gallery`, `apps/privacy-voting`, etc. | not audited beyond spot-checks |
| `starbridge-apps/*` | not audited (one zero-pinned spot in governed-namespace looks legitimate) |
| `demo/cross-app-e2e` | 90% | Best demo. Real cross-implementation Python + Rust derivation (R12). One weak spot: subscription-head advances (S7) |
| `demo/two-ai-handoff` | 75–85% | `silver_helper.rs` does real signature verification, real `CellProgram::evaluate`, real STARK proofs via `dregg-verifier`. Charlie's verdict mostly depends on `silver_helper` doing the right thing — but `silver_helper` IS real and visible. The bilateral-tamper-rejection path goes through real `dregg-verifier bilateral-pair` invocations |
| `demo/multi-node-devnet` | 20–35% | Scaffolding theater. Five scenarios; we audited two and both write fixtures the assertions then check. Federation-attestation and bilateral-transfer not audited but I expect similar shape unless they call real `/api/*` endpoints |
| `demo/silver-vision-e2e` | abandoned (expected.json only, no scripts) |
| `tests/src/*` workspace harness | ~30% running, ~70% `#[ignore]`d (see S11–S15, S20) |
| `teasting/tests/*` | spot-sampled — `storage_faults.rs` real (R13); most files have 0–1 ignores |
| `protocol-tests/effect_vm_differential.rs` | 60–75% real — but documents (S19) that the AIR-vs-runtime divergence tests are intentionally `#[ignore]`d |

**Aggregate (high-value areas only):** roughly **55–70%** of the claim-bearing tests in the codebase are real tests; the rest are either seeming (S1–S20) or `#[ignore]`d-but-documented. The biggest *load-bearing seeming* concentrations are (a) the FRI single-row gap in effect_vm tamper tests (S1, S2, S5), (b) the multi-node-devnet scenarios (S8, S9), and (c) the executor honesty / sovereign-witness / γ.2 / witnessed-predicate ignore-piles in `tests/src/*`.

---

## §5. The "we claim X passes but the test for X is fake" list

Prioritized. The user is leaning on these.

1. **`circuit/effect_vm`: "tamper detection works"** — S1, S3, S4, S5. Five claim-bearing tamper tests that either print instead of assert, skip verify, or are `#[ignore]`d. The FRI gap is real and undocumented in user-facing material. **Action:** Either fix FRI sampling so single-row tampers are reliably caught, or rewrite these tests to assert what they actually demonstrate (algebraic non-zero at row, not STARK rejection).

2. **`demo/multi-node-devnet` cross-federation handoff & intent-match** — S8, S9. Both claim to demonstrate cross-federation flows; both write fixtures the test then re-reads. **Action:** Either submit real intents / handoff URIs to F1's HTTP surface, or mark these `pending` (not `true`) in `expected.json` until the lane lands.

3. **Executor honesty threats T2/T4/T6/T7/T13** — S11. The audit document EXECUTOR-HONESTY-AUDIT.md enumerates 13 cross-cutting threats; the test file `executor_honesty_threats.rs` has 21 `#[ignore]`s covering them. The verifier-layer T8/T11 tests (R8) are real; the executor-layer and AIR-side teeth are not. **Action:** Don't claim "executor is honest" in any user-facing doc until at least T2 (verify path is the only entry) and T6 (federation_id in signing message) have a real test.

4. **Sovereign-witness AIR teeth** — S12. The two-ai-handoff demo's sovereign-witness check (`silver.sovereign-witness.json.self_verifies`) is structurally fine but only tests Ed25519 sign+verify, not the AIR-side teeth. The Rust-test-suite teeth are 19 `#[ignore]`s. **Action:** Either rename the demo claim to "sovereign witness signature self-verifies" (which is what's actually tested) or land the AIR teeth.

5. **`verifier::Unwitnessable` rejection path** — S6, S17. Two tests claim to exercise this path; both fall through to the STARK step's empty-proof rejection. The actual Unwitnessable branch (lines 598, 609) has no test that reaches it. **Action:** Construct a non-empty-proof entry with `witness_bundle: None, witness_hash: [0; 32]` and a passing STARK-shape proof; assert `Unwitnessable`.

6. **`apps/identity` predicate-false negative path** — S16. The `verified == false` assertion short-circuits and never invokes the STARK verifier. Real risk: a bug in `verify_predicate_dsl` that accepts forged false-predicate proofs would not be caught by this test. **Action:** Construct a forged proof for a known-false predicate, submit through `verify_predicate_dsl`, assert rejection.

---

## §6. Demos specifically

### `demo/cross-app-e2e` — genuinely robust

This demo is the brightest spot in the audit. Architecture:

1. `canonical.py` (181 LOC) is an **independent Python implementation** of every commitment derivation. It uses `blake3.derive_key_context=domain` to mirror the Rust `blake3::Hasher::new_derive_key(domain)`, with byte-level documentation comments showing the exact Rust call shape (e.g., lines 60–66 for `credential_set_commitment`).
2. Each agent script (alice, bob, carol, dan) runs real CLI / MCP calls against `dregg-node` (or the real `starbridge_*` crates) and writes its receipt artifacts to `state/`.
3. `verify.py` (294 LOC) loads every agent's artifact, re-derives every commitment from raw inputs using `canonical.py`, and asserts the agent's pinned commitment matches the canonical re-derivation.
4. **Negative tests** (lines 192–249) reproduce tamper attempts (wrong issuer, wrong schema, wrong actor pk, tampered prior_state, tampered resolve target, wrong method, wrong constraint variant) and assert the resulting commitments don't match.

The independent-implementation property is the soundness floor. If the Rust `dregg_cell::program::AuthorizedSet::credential_set_commitment` had a subtle bug, the Python re-derivation would catch it byte-equal. This is exactly the shape (R12, "cross-implementation test") that the audit's §"What real tests look like" describes.

Single weak spot: subscription-head advance checks (S7) read back the agent's own claimed `new_head` rather than re-deriving it. Not load-bearing — every other check in the verifier is honest.

**Verdict:** This demo's `verify.py` does what it claims to do.

### `demo/two-ai-handoff` — mostly real, depends on `silver_helper.rs`

`charlie.py` is a thin runner that:
1. Calls the real `dregg-verifier` binary (`verify-proof`, `replay-chain`, `bilateral-pair`, `scope-recursive`) on real artifacts.
2. Calls `silver_helper` for verification subcommands (`verify-captp-delivered`, `verify-captp-delivered-tampered`).
3. Reads `silver.sovereign-witness.json.self_verifies` etc. directly from disk — these are populated by `silver_helper`'s `cmd_make_*` functions which DO run real Ed25519 verification (`silver_helper.rs:643–667`).
4. For bilateral binding: writes a tampered bundle, calls `dregg-verifier bilateral-pair` on it, asserts rejection.

The substrate-honest claim hinges on whether `silver_helper.rs` is honest. Sampling `cmd_make_sovereign_witness` (lines 599–685): real `SovereignCellWitness::signing_message`, real `alice_sk.sign(...)`, real `verify_strict`, tampered `new_commitment[0] ^= 0x01` re-derives the message and confirms the original signature no longer verifies. The slot-caveat demo (`cmd_slot_caveat_demo`, line 695+) installs a real `CellProgram::Predicate(vec![WriteOnce, Monotonic])` and exercises positive + negative paths against real `CellProgram::evaluate`.

**Verdict:** Robust within scope. The scope is narrower than the demo advertises — the "two AIs handing off via CapTP" narrative is dramatized; the substrate checks beneath it are real.

### `demo/multi-node-devnet` — scaffolding theater (S8, S9)

Bullshit. Five scenario scripts; we audited two (cross_fed_handoff + intent_match_cross_fed), both write fixtures and re-check their own writes. The scenarios that might be real:
- `bilateral_transfer.sh` — claims `transfer_id_derivation_deterministic` etc. Not sampled; likely similar shape.
- `federation_attestation.sh` — claims `tampered_federation_descriptor_rejected`. Not sampled; would be a real test if it shells to a real federation node, fake if it writes its own descriptor.
- `peer_exchange_bypass.sh` — not sampled.

**Verdict:** Until I sample the other three, I lean toward "treat the whole multi-node-devnet as scaffolding." The accompanying `expected.json` files are honest about gaps in their `must_not_pass_explanation` comments, but the scripts still emit `true` for assertions that test nothing.

### `demo/silver-vision-e2e` — abandoned

Only `expected.json` exists; no driver scripts.

---

## §7. Prioritized add-test list

The 10 highest-leverage new tests that would close real gaps. Ordered by leverage (most gap closed per LOC of test).

### A1. STARK rejects single-row tamper end-to-end
**Target:** Fix the FRI gap behind S1/S2/S5. Either (a) raise FRI query count for small traces, or (b) write the test against a trace size where FRI's probabilistic soundness is reliable; in either case, make the test do prove+verify and assert `result.is_err()`.
**Why:** Closes the single most load-bearing seeming test in the entire effect_vm soundness story.

### A2. STARK rejects wrapped-balance trace with honest commitment PI
**Target:** S3. Construct the wrap manually, prove, verify against the honest `new_commitment` as PI, assert rejection.
**Why:** Currently the only "soundness gap 1" test (`test_soundness_wrapped_balance_different_commitment`) demonstrates only that Poseidon2 is collision-resistant. The actual claim — "the verifier rejects wrapped balance" — has no test.

### A3. STARK rejects injected-NoOp trace with honest effects_hash PI
**Target:** S4. Currently `test_noop_padding_cannot_be_exploited` only tests blake3 collision resistance.
**Why:** The "NoOp can't be exploited" claim is the foundation of trace-padding security; nothing currently tests it cryptographically.

### A4. Verifier `Unwitnessable` rejection branch is reachable
**Target:** S6/S17. Construct a `ReplayEntry` with `witness_bundle: None`, `witness_hash: [0; 32]`, and a passing-shape proof; assert the verdict is `Unwitnessable`, not `Rejected (empty proof bytes)`.
**Why:** The two existing tests pass for the wrong reason. The Unwitnessable code path is genuinely untested.

### A5. Multi-node-devnet `cross_fed_handoff` against real HTTP / CapTP surface
**Target:** S8. Either invoke the real `dregg_create_cross_fed_bearer_cap` MCP tool and submit the resulting URI to F2's executor (asserting the transfer applies and F2's `/federation/roots` advances), or mark every assertion `pending`.
**Why:** Closes the largest single seeming-demo in the audit. Currently the user cannot tell from `run_all_scenarios.sh` output whether cross-fed handoff is actually wired.

### A6. Executor T6: signing message includes federation_id
**Target:** S11 (one of 21). Construct a turn signed against a *different* federation_id than the executor expects; assert rejection.
**Why:** This is one of EXECUTOR-HONESTY-AUDIT.md's highest-impact threats and the test exists but is `#[ignore]`d. Three lines of code in the test, one assertion against `TurnError::InvalidAuthorization`.

### A7. Executor T2: `Authorization::Unchecked` cannot reach the executor
**Target:** S11. Either a compile-time-private check (e.g., constructor not callable from outside the crate), or a runtime test that asserts an `Unchecked` action through the public `execute` API is rejected.
**Why:** This is the "is there a back door to the executor" threat. Currently un-tested.

### A8. Forged predicate-false proof is rejected by `verify_predicate_dsl`
**Target:** S16. Construct a witness where `private_value < threshold` but the prover claims `Gte`; manually drive `prove_predicate_dsl`'s internals or hand-craft a proof; assert `verify_predicate_dsl` returns `Err`.
**Why:** The "negative path" in `test_predicate_age_gte_various` short-circuits at the satisfiability gate and never reaches the verifier. A real bug in the verifier (accepts forged false-predicate proof) would not be caught.

### A9. Sovereign-witness AIR teeth: tampered transition rejected by AIR (not just by signature)
**Target:** S12. Construct a witness with valid signature but tampered `old_commitment → new_commitment` transition; assert the AIR rejects (separately from the executor's signature check).
**Why:** Currently the two-ai-handoff demo's claim is "sovereign witness self-verifies" — a signature check. The AIR teeth — the actual structural binding to commitments — have 19 ignored tests and no real one.

### A10. Cross-cell composition: one positive + one negative through the full pipeline
**Target:** A capstone test that:
1. Issues a credential through `starbridge_identity` (real).
2. Mounts via `starbridge_nameservice` with credential-set constraint (real).
3. Submits a turn under that constraint (real).
4. Replays a turn with a tampered credential (negative).
The cross-app-e2e Python demo does this, but there's no corresponding Rust-side `cargo test` equivalent. **A `tests/src/cross_app_credential_pipeline.rs`** would let `cargo test --workspace` see this composition.
**Why:** The cross-app composition is the silver-vision headline; currently the test for it is a Python script. A Rust-side mirror would give CI a chance to catch breakages between releases.

---

## Appendix A. Tally of `#[ignore]`s by directory (signal only)

```
tests/src/executor_honesty_threats.rs        21
tests/src/sovereign_witness_threats.rs       19
tests/src/gamma2_bilateral_binding.rs        19
tests/src/witnessed_predicate_kinds.rs       18
tests/src/state_constraint_variants.rs       16
circuit/src/plonky3_prover.rs                12
tests/src/authorization_variants.rs           7
tests/src/state_constraint_executor.rs        6
tests/src/state_constraint_composition.rs     6
circuit/src/plonky3_recursion.rs              3
tests/src/slot_caveat_composition_stress.rs   3
teasting/tests/bridge_four_phase_extended.rs  3
tests/src/every_variant_roundtrip.rs          2
circuit/src/effect_vm/tests.rs                1  (S2)
apps/gallery/src/private_vickrey.rs           1  (legitimate — 30min stress test)
circuit/src/backends/plonky3.rs               1  (legitimate — slow)
teasting/tests/revocation_propagation.rs      1
circuit/src/backends/kimchi_native/tests.rs   1
circuit/src/poseidon2_air.rs                  1
```

The `tests/src/` block (21 + 19 + 19 + 18 + 16 + 7 + 6 + 6 + 3 + 2 = 117 ignored tests in a single directory) is the largest concentration of claim-bearing-but-not-running tests in the codebase.

## Appendix B. The "zero-pinned" sentinel inventory

These are `assert_eq!(x, [0u8; 32])` style assertions. Most are legitimate (empty state = zero root); a few are worth a second look:

Legitimate (documented sentinels):
- `cell/src/tests.rs:86` — `CellId::ZERO` is zero by definition.
- `cell/src/tests.rs:1754` — committed-field stale sentinel.
- `cell/src/tests.rs:1775` — placeholder signature on `pub(crate)` spawn helper (the audit's point is compile-time enforcement).
- `cell/src/predicate.rs:1997` — built-in predicates report all-zero vk_hash by design.
- `commit/src/typed.rs:648` — empty Commitment4 is zero.
- `token/src/action_set.rs:363` — empty ActionSet has zero merkle root.
- `intent/src/state_machine.rs:218` — `IntentLifecycleState::from_slot_value(&[0u8; 32]) == None`.

Worth examining:
- `verifier/src/lib.rs:397` (`d.federation_id_bytes() == [0u8; 32]`) — only if this is a `null federation` test it's fine; if it's pinning a real federation's id to zero, it's a placeholder.
- `dregg-storage-templates/src/cap_inbox.rs:642–645` — four `[0u8; 32]` slot reads. Almost certainly legitimate (empty inbox = zero slots), but worth a glance if anyone's auditing the templates crate.
- `sdk/src/embed.rs:806, 895` — `engine.federation_root() == [0u8; 32]`. Same question: empty-federation sentinel, or a placeholder waiting for a real root?

None of these stood out as actively misleading; flagged here so a follow-up audit knows what to spot-check.
