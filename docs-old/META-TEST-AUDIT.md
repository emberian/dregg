# Meta-Test Audit: tests/, teasting/, demo/

Audit date: 2026-05-25. Authored by Sonnet Polish Lane.

---

## 1. Scope and methodology

Directories audited: `tests/`, `teasting/`, `demo/`. Each file was read
line-by-line. No cargo runs; findings are purely static.

---

## 2. `tests/` crate — cross-cutting integration tests

**Location:** `tests/src/`

### Active modules (no feature gate)

| Module | What it tests | Assessment |
|---|---|---|
| `sovereign_proof.rs` | Proof-carrying sovereign turns through TurnExecutor | Real: builds actual proofs, executes real executor path |
| `dsl_pipeline.rs` | DSL descriptor → CellProgram → ProgramRegistry → executor | Real pipeline |
| `captp_effects_pipeline.rs` | ExportSturdyRef, EnlivenRef, DropRef, ValidateHandoff via Effect VM STARK | Real |
| `dfa_circuit.rs` | Transition table commitment + STARK proof of classification | Real |
| `service_mesh_e2e.rs` | CAS, splice, mount, governance vote + route table | Real |
| `every_variant_roundtrip.rs` | All 41 Effect variants: execute, project to VM, prove+verify | Real. Documented that ~25/41 collapse to NoOp — these are `#[ignore]`d |
| `state_constraint_variants.rs` | Every StateConstraint at cell-side evaluator | Real |
| `state_constraint_executor.rs` | StateConstraint through full TurnExecutor | Real |
| `state_constraint_composition.rs` | Multi-variant Predicate(Vec<_>) composition | Real |
| `witnessed_predicate_kinds.rs` | Every WitnessedPredicateKind (Dfa, Temporal, MerkleMembership, BlindedSet, etc.) | Real, most blocked on caveat-correctness registry dispatch |
| `authorization_variants.rs` | Every Authorization variant | Real |
| `gamma2_bilateral_binding.rs` | γ.2 transfer/grant/intro id agreement | Real |
| `sovereign_witness_threats.rs` | Phase 1 algebraic teeth + wire-malleability | Real |
| `executor_honesty_threats.rs` | T1–T15 from EXECUTOR-HONESTY-AUDIT.md | Real |
| `slot_caveat_composition_stress.rs` | 16-variant conjunctions, large AnyOf, Cases dispatch | Real |
| `fully_private_e2e.rs` | Privacy-preserving e2e | Real |
| `wire_format_e2e.rs` | Wire format round-trip | Real (gated `__wip_tests`) |
| `adversarial_boundaries.rs` | Property-based adversarial | Real (gated `__wip_tests`) |
| `adversarial_pipeline.rs` | Full pipeline with tampering | Real (gated `__wip_tests`) |

### Legacy modules (gated `__legacy_tests` feature — never enabled)

`budget.rs`, `commitment.rs`, `fuzz.rs`, `soundness.rs`, `trace_attacks.rs`,
`integration.rs`, `full_pipeline.rs`

**FINDING (F1): Dead legacy tests.** Seven modules are gated behind
`__legacy_tests` which is never enabled in `Cargo.toml`. They are never
run. They exist only as source — either promote to active or delete.

---

## 3. `teasting/` crate — simulation harness + tests

### Harness quality (`teasting/src/`)

`harness.rs` — Real: backed by `dregg_blocklace::finality::Blocklace` + real
`dregg_federation::Federation` + real `TurnExecutor`. Not mock.

`assertions.rs` — Real domain-specific invariant checkers: conservation,
nonce monotonicity, GC consistency, nullifier uniqueness, directory version
monotonicity, constitution validity.

`captp_sim.rs`, `mesh_sim.rs`, `router_sim.rs` — Simulation layers, realistic.

`fault.rs`, `federation.rs`, `agent.rs` — Support infrastructure.

### Test files (`teasting/tests/`)

| File | Assessment |
|---|---|
| `proof_round_trip.rs` | Real: generates STARK proofs, serializes, deserializes, verifies. |
| `token_lifecycle.rs` | Real: mint → attenuation → chain proofs via real SDK. |
| `cross_federation.rs` | Real: conditional turns, hashlock atomic swap, note bridges. |
| `adversarial_federation.rs` | Real adversarial scenarios. |
| `bridge_four_phase.rs` / `bridge_four_phase_extended.rs` | Real bridge lifecycle. |
| `captp_sessions.rs` | Real CapTP session establishment + GC. |
| `consensus_liveness.rs` | Real: N nodes reach agreement via blocklace + tau. |
| `cross_federation_captp_turn.rs` | Real cross-fed CapTP turn delivery. |
| `defi_primitives.rs` | Real DeFi primitive compositions. |
| `dfa_routing.rs` | Real DFA routing proof. |
| `effect_vm_captp.rs` | Real Effect VM + CapTP interaction. |
| `escrow_lifecycle.rs` | Real escrow state machine. |
| `fast_path_vs_consensus.rs` | Real fast/slow path selection. |
| `fault_byzantine.rs` / `fault_crash.rs` / `fault_ordering.rs` / `fault_partition.rs` | Real fault injection. |
| `fuzz_captp.rs` / `fuzz_governance.rs` / `fuzz_turns.rs` | Fuzz/property tests. |
| `invariants.rs` | Real invariant checking (conservation, nonces, GC, constitution). |
| `multi_asset_fees.rs` | Real fee computation. |
| `negation_proofs.rs` | Real negation proof verification. |
| `predicate_soundness.rs` | Real predicate soundness. |
| `privacy_unlinkability.rs` | Real unlinkability checks (uses `assert_unlinkable`). |
| `pubsub.rs` | Real pub/sub queue lifecycle. |
| `relay_operators.rs` | Real relay operator tests. |
| `revocation_propagation.rs` | Real revocation propagation across nodes. |
| `service_mesh.rs` | Real service mesh simulation. |
| `silver_vision_substrate.rs` | Real silver-vision substrate tests. |
| `storage_faults.rs` / `storage_lifecycle.rs` / `storage_with_captp.rs` | Real storage path tests. |
| `token_lifecycle.rs` | Real token lifecycle. |

**FINDING (F2): `teasting/tests/` is largely sound.** The SimulationHarness
uses real production types (`Blocklace`, `TurnExecutor`, `Federation`) not
mock doubles. Tests exercise real code paths.

**FINDING (F3): Duplicate harness overlap with `tests/`.** Both crates have
tests for sovereign proofs, token lifecycle, service mesh, CapTP sessions,
and proof round-trips. There is no consolidation — `teasting/tests/` runs in
process-sim context; `tests/src/` runs against the full executor surface.
The duplication is intentional layering, but several tests appear equivalent
(e.g., proof round-trips appear in both). A note in the crate-level docs
would help.

---

## 4. `demo/cross-app-e2e/` — verify.py line-by-line

**File:** `demo/cross-app-e2e/verify.py`

`verify.py` is **structural-only**, exactly as the user suspected. Here is the
taxonomy:

### What it actually checks

1. **Canonical re-derivation** (lines 65–68): Re-derives `schema_commitment`
   from raw inputs using Python's `canonical.py` (which mirrors the Rust
   BLAKE3 domain-separation). Checks equality with the stored artifact.
   *This is a real cross-language consistency check.*

2. **Field equality between artifacts** (lines 71–73, 82–88, etc.):
   Checks that `alice["bob_holder_id"] == bob_id["bob_cell"]`. *Real field
   coherence.*

3. **Structural shape checks** (lines 97–99): `len(bob_reg["witness_blobs"]) == 1`
   and `witness_blobs[0]["kind"] == "ProofBytes"`. *Shape-only — does not
   verify the proof bytes.*

4. **Hard-coded effect indices** (line 104): `event = bob_reg["effects"][3]`.
   This is a **fragile snapshot assertion**: if the effect ordering ever
   changes, this silently reads the wrong event.

5. **Subscription head assertions** (lines 152–160): `dan_claim["new_head"] == 1`,
   `dan_fulfill["new_head"] == dan_claim["new_head"] + 1`. These check numeric
   consistency, not cryptographic correctness.

6. **Negative tests** (lines 192–248): Re-derive commitments with forged
   inputs and assert inequality. *Real: different inputs → different BLAKE3
   outputs — but only proves hash collision resistance, not that the executor
   enforced anything.*

### What it does NOT check

- It does not call `dregg-verifier` or any proof verifier.
- It does not inspect proof bytes in `witness_blobs[0]` at all — only that
  the field exists and has kind `"ProofBytes"`.
- It does not verify that the executor ran, that receipts are signed, or that
  any state transition was authorized.
- It reads pre-existing `state/*.json` artifacts produced by a previous run;
  if those artifacts were hand-crafted, the check passes trivially.

**VERDICT: verify.py is a structural coherence checker, not a cryptographic
verifier.** The name "verify" is misleading. See section 7 for the design doc.

---

## 5. `demo/two-ai-handoff/run.sh` — real end-to-end?

**File:** `demo/two-ai-handoff/run.sh` + `charlie.py`

### What IS real

- **Step 1:** Calls `cargo build` for `dregg-node`, `dregg-verifier`,
  `silver-helper`. Real binaries.
- **Steps 2–3:** `bob.py` and `alice.py` invoke `dregg-node` (real binary)
  to create cells, issue grants, drop bearer-cap URIs.
- **Step 4:** `silver-helper make-handoff`, `make-captp-delivered`,
  `make-sovereign-witness`, `slot-caveat-demo`, `make-bilateral-bundle` —
  all call the real `silver-helper` binary, which assembles real Ed25519
  signatures and canonical artifacts.
- **Step 8 / charlie.py:** Charlie shells to `dregg-verifier` for
  grant/exercise STARK proof verification, replay-chain verification, and
  `bilateral-pair` verification. These invoke real STARK verifier logic.
- **Tamper/negative tests:** silver-helper's `verify-captp-delivered-tampered`
  produces a modified signature and confirms rejection.

### What is NOT real (gap acknowledged in comments)

- **Step 7 (line 250):** The comment says "GAP: today's MCP tool
  `dregg_exercise_bearer_cap` uses `Authorization::Bearer`, not
  `CapTpDelivered`." The CapTpDelivered artifact is built by silver-helper
  for charlie to verify *separately*; Bob's actual exercise still uses the
  Bearer legacy path.
- **recursive-witness step (4c):** The `make-recursive-witness` artifact is
  verified via `dregg-verifier scope-recursive` but the chain.json it produces
  may use a minimal/mock Effect VM proof depending on whether the recursive
  prover landed.

**VERDICT:** The `two-ai-handoff` demo exercises real binaries with real
STARK proofs through charlie's independent verifier. It is not purely
artifact comparison. The Bearer/CapTpDelivered gap is documented inline.

---

## 6. `demo/multi-node-devnet/scenarios/` — bash assertions

### General pattern

All five scenarios share the same structure:
- Declare `declare -A RESULTS`
- Call `record <key> <true|false>`
- Emit `result.json`
- Check `expected.json` must_pass/must_not_pass lists

### Weak assertions found

**`bilateral_transfer.sh`**

- **Lines 56–97 (F2):** `transfer_id` is derived using Python `hashlib.blake2b`
  — *not* `dregg_cell`'s canonical BLAKE3 `transfer_id` from `cell/src/witness.rs`.
  The expected.json documents this as a gap ("stand-in, not the canonical derivation").
  But the test passes unconditionally because the Python derivation always
  succeeds given valid hex. `transfer_id_derived_32_byte_hex` just checks
  `${#TRANSFER_ID} -eq 64` (line 74) — length only.

- **Lines 126–142 (F3):** `bilateral_pair_direction_complement_holds`: both
  direction values are hardcoded shell variables (`ALICE_DIR=1`, `BOB_DIR=0`).
  The bash arithmetic `$((ALICE_DIR ^ BOB_DIR)) -eq 1` always evaluates to
  1. This assertion **always passes regardless of any system behavior**.

- **Lines 138–142:** `bilateral_pair_amount_agrees` always passes because
  both `ALICE_AMOUNT=100` and `BOB_AMOUNT=100` are hardcoded constants.

**`cross_fed_handoff.sh`**

- **Lines 119–135 (F3):** Alice's handoff URI is written directly in the
  script as a `cat > ... <<EOF` heredoc with `"note": "Scaffold artifact"`.
  It is never signed or validated. `alice_uri_produced_on_F1` passes iff
  the file exists (`-s`). Trivially true after a successful write.

- **Lines 175–187 (F4):** `handoff_replay_artifact_constructed` asserts
  that nonce in the replay copy equals the original (`n1 == n2`). Since both
  files come from `cp`, this is always true. The assertion passes trivially —
  it is not testing executor replay defense at all.

**`peer_exchange_bypass.sh`**

- **Line 103:** `record peer_exchange_id_federation_invariant true` — this
  line unconditionally records `true` with no computation. Pure lie.

- **Lines 64–77:** `sovereign_witness_sequence_monotonic_strict` and
  `sovereign_witness_equal_sequence_detected_as_regression` both use
  `PREV=0` / `POST=1` hardcoded shell integers. No real witness is constructed.

- **Lines 115–125:** `F1_ledger_unchanged_by_idle_observation` records `true`
  unconditionally even in the else-branch (line 124): `devnet_warn ...` then
  immediately `record F1_ledger_unchanged_by_idle_observation true`. The
  observation can fail and the assertion still passes.

**`intent_match_cross_fed.sh`**

- **Lines 46–54 (F1):** Route-presence check: `code != "404" && code != "000"`.
  Any HTTP response (including 400/500) counts as "route present." This does
  not check that the route accepts valid payloads.

- **Lines 128–141 (F7):** `tampered_intent_collapsed_to_same_federation_detected`
  runs `jq '.submitter_federation = .target_federation'` on a local JSON file
  and asserts that after the edit `submitter == target`. This is a pure
  JSON manipulation check — no executor call. Always passes if `jq` works.

**`federation_attestation.sh`**

- **Lines 100–108 (F4):** The most meaningful negative test: calls
  `"$NODE_BIN" register-federation --descriptor "$TAMPER"` and checks exit
  code is non-zero. This is real — it invokes the production binary. PASS.

- **Lines 113–120:** `federation_ids_are_committee_derived_32_byte_hex` checks
  `${#F1_ID} == 64`. Length only — a 64-char garbage string passes.

---

## 7. `demo/silver-vision-e2e/`

**Files:** only `expected.json` exists.

`expected.json` is a comprehensive spec document (51 must_pass, 35 must_not_pass).
It explicitly states in `documented_gaps`:

```json
"no harness binary exists yet — this expected.json is the spec"
```

And in `blocked_on`:
```
"caveat-correctness lane: WitnessedPredicateRegistry dispatch from cell-program path"
"γ.2 Phase 1: PI fields + off-AIR pair/triple verifier"
"sovereign-witness AIR teeth"
"AUTHORIZATION-CUSTOM-DESIGN: Auth::Custom executor dispatch through registry"
```

**VERDICT:** `silver-vision-e2e` is a **pure spec stub** — a forward-looking
design document formatted as an expected.json. No harness exists. It is not a
fake-pass scenario (it would fail every check if a harness ran it); it is an
aspirational target blocked on multiple open lanes.

---

## 8. `demo/sdk-consensus/`

**File:** `demo/sdk-consensus/src/main.rs`

Real demo binary that stitches together blocklace finality, federation
attestation persistence, CapTP wire encoding, SDK-direct turn submission,
and cross-cell capability handoff. It uses real production types throughout.
Not a test (no assertions framework) — it panics on failure.

---

## 9. `demo/src/` (older demo crate)

**Files:** `authority.rs`, `commit_state.rs`, `federation.rs`, `revocation.rs`,
`stark_proof.rs`, `token.rs`, `trace.rs`, `verifier.rs`, `main.rs`.

This is the **original federated authorization demo** that predates the current
architecture. It uses in-crate shadow types for `Authority`, `Federation`,
`Token`, `Verifier` — it does not import the production `dregg_*` crates in
the same way the newer code does. It demonstrates concept correctness but does
not exercise production code paths. Status: **legacy reference material**.

---

## 10. The 3 most-egregious seeming-tests / fake-demos

### #1: `peer_exchange_bypass.sh` line 103 — unconditional true

```bash
record peer_exchange_id_federation_invariant true
```

No computation. No call to any binary. The assertion that peer exchange IDs
are federation-invariant is stated as a constant. This fires as PASS in the
expected.json must_pass list unconditionally. File: `demo/multi-node-devnet/scenarios/peer_exchange_bypass.sh:103`.

### #2: `cross_fed_handoff.sh` — scaffold URI treated as real handoff

Alice's handoff URI is a JSON heredoc written by bash (lines 119–133). It has
the comment `"note": "Scaffold artifact: real cert + Ed25519 sig require dregg_create_cross_fed_bearer_cap"`.
Yet `alice_uri_produced_on_F1` and `uri_delivered_to_F2_inbox` appear in
`expected.json` must_pass. These always pass as long as bash can write a file.
File: `demo/multi-node-devnet/scenarios/cross_fed_handoff.sh:119-141`,
`demo/multi-node-devnet/expected/cross_fed_handoff.json:8-11`.

### #3: `bilateral_transfer.sh` hardcoded direction-complement

```bash
ALICE_DIR=1
BOB_DIR=0
if [ $((ALICE_DIR ^ BOB_DIR)) -eq 1 ]; then
    record bilateral_pair_direction_complement_holds true
```

The "test" is that 1 XOR 0 == 1, evaluated in bash arithmetic on hardcoded
constants. It verifies no system behavior whatsoever. It appears in
`expected.json` must_pass. File:
`demo/multi-node-devnet/scenarios/bilateral_transfer.sh:126-130`.

---

## 11. Summary table: seeming-tests across the three directories

| Location | File | Line(s) | Finding | Severity |
|---|---|---|---|---|
| `tests/src/main.rs` | main.rs | 10–25 | 7 modules gated by `__legacy_tests` never enabled | Medium |
| `demo/cross-app-e2e/verify.py` | verify.py | 97–99 | ProofBytes shape check, never verifies content | Medium |
| `demo/cross-app-e2e/verify.py` | verify.py | 104 | Hard-coded `effects[3]` index — fragile snapshot | Low |
| `demo/cross-app-e2e/verify.py` | verify.py | 152 | `new_head == 1` — hardcoded expected value, not derived | Low |
| `demo/multi-node-devnet/scenarios/bilateral_transfer.sh` | bilateral_transfer.sh | 56 | transfer_id uses blake2b not canonical BLAKE3 | High |
| `demo/multi-node-devnet/scenarios/bilateral_transfer.sh` | bilateral_transfer.sh | 74 | `transfer_id_derived_32_byte_hex` checks len only | Medium |
| `demo/multi-node-devnet/scenarios/bilateral_transfer.sh` | bilateral_transfer.sh | 126–130 | Hardcoded direction-complement always true | High |
| `demo/multi-node-devnet/scenarios/bilateral_transfer.sh` | bilateral_transfer.sh | 138–142 | Hardcoded amounts always equal | High |
| `demo/multi-node-devnet/scenarios/cross_fed_handoff.sh` | cross_fed_handoff.sh | 119–135 | Scaffold URI file always succeeds | High |
| `demo/multi-node-devnet/scenarios/cross_fed_handoff.sh` | cross_fed_handoff.sh | 175–187 | Replay artifact always identical (same cp) | Medium |
| `demo/multi-node-devnet/scenarios/peer_exchange_bypass.sh` | peer_exchange_bypass.sh | 64–77 | Hardcoded PREV/POST integers | High |
| `demo/multi-node-devnet/scenarios/peer_exchange_bypass.sh` | peer_exchange_bypass.sh | 103 | Unconditional `true` record | Critical |
| `demo/multi-node-devnet/scenarios/peer_exchange_bypass.sh` | peer_exchange_bypass.sh | 115–125 | Ledger-unchanged recorded true even in else-branch | High |
| `demo/multi-node-devnet/scenarios/intent_match_cross_fed.sh` | intent_match_cross_fed.sh | 46–54 | Route-present: any HTTP code counts | Medium |
| `demo/multi-node-devnet/scenarios/intent_match_cross_fed.sh` | intent_match_cross_fed.sh | 128–141 | Tamper detection: pure JSON edit, no executor | Medium |
| `demo/multi-node-devnet/scenarios/federation_attestation.sh` | federation_attestation.sh | 113–120 | Fed-id length check only (64 chars) | Low |
| `demo/silver-vision-e2e/expected.json` | expected.json | entire file | Spec stub, no harness | Documented |
| `demo/src/main.rs` | main.rs | entire crate | Shadow types, not production crates | Documented |

---

## 12. Recommendations

1. **peer_exchange_bypass.sh line 103**: Replace the unconditional `true` with
   an actual derivation (re-derive XID with and without a fed-id input and
   assert equality). See improvements in `demo/multi-node-devnet/scenarios/peer_exchange_bypass.sh`.

2. **bilateral_transfer.sh**: Add a comment + `blocked_on` entry for
   direction-complement and amount checks, or replace with calls to a helper
   binary that exercises real per-cell witnesses. Until then, mark these with
   `# SYNTHETIC: no real witness` comments.

3. **cross_fed_handoff.sh**: The scaffold URI must_pass assertions should be
   demoted to informational-only (not in must_pass) or marked `blocked_on`
   the MCP tool.

4. **verify.py**: Rename to `check-coherence.py` OR add a real verifier call
   as described in `demo/cross-app-e2e/REAL-VERSION.md`.

5. **Legacy tests**: Enable or delete `__legacy_tests`-gated modules.

6. **`F1_ledger_unchanged_by_idle_observation`**: Fix the else-branch to
   record `false` (or reclassify as informational / remove from must_pass).
