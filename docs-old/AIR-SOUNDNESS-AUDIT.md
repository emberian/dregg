# AIR Soundness Audit — Silver-Vision Pre-Playground

Status: audit-only. No code changes; read-only sweep performed against
`circuit/src/`, `cell/src/predicate.rs`, `cell/src/vk_v2.rs`,
`cell/src/note_bridge.rs`, `cell/src/custom_effect.rs`, and the relevant
DSL backings under `circuit/src/dsl/`. Concurrent edits in progress on
`turn/src/executor.rs`, `cell/`, and `demo/two-ai-handoff/` were left
untouched.

Sources cited inline by `file:line` so a future reviewer can re-execute
the audit against a moving tree.

---

## §1. Executive summary

Coarse classification of the AIR/verifier surfaces in scope:

| Class            | Count | Examples |
|------------------|------:|----------|
| **SOUND**        | 9     | `bridge_action_air`, `bridge_lock_action_air`, `effect_action_air` (all 23 schemas), `effect_vm` (with documented limb-range carve-out), `ivc::StateTransitionAir`, `accumulator_air` (DSL-backed), `poseidon2_air`, `note_spending_air` (felt-PI binding), `vk_v2::canonical_vk_v2` |
| **SILVER-SOUND** | 5     | `SortedNeighborNonMembershipVerifier` (cell/src/predicate.rs:1142), `recursive_witness_bundle` (effect-vm shape AIR, not the full VM AIR), `note_bridge::verify_portable_note` (trusts caller-vetted roots; ThresholdQC structural-only at `types/src/lib.rs:394`), `effect_vm` interior-row limb ranges (executor-side checked, not in-circuit), `temporal_predicate_dsl` boundary binding (proof metadata, not STARK-bound — see §2.K) |
| **STUB**         | 7     | `StubVerifier::dfa()`, `::temporal()`, `::merkle_membership()`, `::blinded_set()`, `::bridge_predicate()`, `::pedersen_equality()` (all in cell/src/predicate.rs:1003-1070), `StubCustomEffectVerifier` (cell/src/custom_effect.rs:377) |
| **MISSING**      | 4     | Adjacency check in `SortedNeighborNonMembershipVerifier`, body-fact-existence binding in `multi_step_air::verify_authorization_stark` (circuit/src/multi_step_air.rs:280), recursive proof coverage of the full `EffectVmAir` constraint set (recursive_witness_bundle uses `EffectVmShapeAir`, a structural subset — circuit/src/recursive_witness_bundle.rs:51-58), `MultiStepStarkAir::eval_constraints` returns `BabyBear::ZERO` (circuit/src/multi_step_air.rs:190-199) which propagates into `chunked_derivation::verify_chunked_authorization` (circuit/src/chunked_derivation.rs:354) |

### Top-3 most urgent gaps

1. **StubVerifier registry is the executor default** (`cell/src/predicate.rs:620`, `default_builtins() = with_stubs()`). Every `WitnessedPredicate::{Dfa, Temporal, MerkleMembership, BlindedSet, BridgePredicate, PedersenEquality}` evaluates to `Ok(())` for any non-empty `proof_bytes`. A playground user constructing a slot-caveat that requires "Bob proves blinded-set membership against root X" gets a passing verifier with a single byte of garbage as the "proof."
2. **`SortedNeighborNonMembershipVerifier` (cell/src/predicate.rs:1142)** enforces only structural ordering + a fixed sentinel tag. A playground prover with knowledge of the sentinel (`0xFE * 32`, a public constant) can construct fake `Renounced { authorized_set }` "proofs" with arbitrary `lower`/`upper` neighbors that aren't actually in the set.
3. **`temporal_predicate_dsl::verify_temporal_predicate` metadata-only binding** (circuit/src/temporal_predicate_dsl.rs:419-458). The STARK's `boundary_constraints` (line 147-164) only pin `ACCUMULATOR` (a step counter) and `STEP_INDEX`. Threshold, value, and state-root chain are *not* bound to PIs. The wrapper verifier compares `proof.threshold` / `proof.initial_state_root` as plain struct fields — a prover can substitute any threshold/state-roots after the fact and the wrapper still accepts.

### Top recommendation

The Silver-Vision-blocker is **registry wiring**: stand up `dregg-circuit`-side real verifiers for the 6 stubbed `WitnessedPredicateKind` variants and have `WitnessedPredicateRegistry::default_builtins()` (cell/src/predicate.rs:620) return them, replacing `with_stubs()`. The underlying AIRs (`dsl::circuit` for DFA, `dsl::membership` for MerkleMembership/BlindedSet, `temporal_predicate_dsl` for Temporal, `bridge::present` for BridgePredicate, the existing Schnorr/Bulletproof primitives for PedersenEquality) already exist with real `eval_constraints`. The current registry default is the single biggest playground-risk amplifier: it converts every witnessed-predicate caveat into a no-op.

---

## §2. Per-AIR / per-verifier sections

### §2.A `effect_action_air::EffectActionAir` — `circuit/src/effect_action_air.rs:151`

**Doc claim** (lines 30-55): "full-fidelity binding of typed parameters into
the proof's PI. Tampering on any byte of any 32-byte field, or any bit of any
u64 amount, produces a different limb encoding which mismatches the boundary
constraint, which fails STARK verification."

**Actual constraints**:
- `eval_constraints` (line 222-240): every column equals next row across all
  rows (`next[c] - local[c] == 0`).
- `boundary_constraints` (line 242-263): per-PI-slot row-0 column pin.

**Classification**: SOUND for the binding semantics it claims. Adversarial
tests (lines 686-870 in tests mod) cover tampering on every field type.

**Caveat**: this AIR is *binding-only*. It does not enforce
replay-protection, semantics of the bound effect (e.g. that a `BridgeMint`
nullifier is in the source state's nullifier set), or cross-effect
ordering. Those properties live one layer up. **No playground impact**
provided the executor downstream actually consults the bound parameters
against its semantic checks.

**Per-schema sweep** (lines 332-610, 23 schemas):
- `SCHEMA_GRANT_CAPABILITY`, `_REVOKE_CAPABILITY`, `_EMIT_EVENT`,
  `_CREATE_CELL`, `_SET_PERMISSIONS`, `_SET_VERIFICATION_KEY`,
  `_INTRODUCE`, `_CREATE_SEAL_PAIR`, `_BRIDGE_FINALIZE`, `_BRIDGE_CANCEL`,
  `_REVOKE_DELEGATION`, `_SPAWN_WITH_DELEGATION`, `_RELEASE_ESCROW`,
  `_REFUND_ESCROW`, `_EXERCISE_VIA_CAPABILITY`, `_CREATE_OBLIGATION`,
  `_CREATE_ESCROW`, `_PIPELINED_SEND`, `_CREATE_CELL_FROM_FACTORY`,
  `_CREATE_COMMITTED_ESCROW`, `_NOTE_SPEND`, `_NOTE_CREATE`,
  `_BRIDGE_LOCK`: each is a `EffectActionSchema` of `(field_count,
  amount_count)` and the generic AIR's column/PI mapping applies
  uniformly. Domain separation via `kind_name` (used as `air_name()`)
  prevents cross-effect proof confusion.

All 23 are **SOUND** for binding.

### §2.B `bridge_action_air::BridgeActionAir` — `circuit/src/bridge_action_air.rs:224`

**Doc claim** (lines 30-75): full-fidelity binding of nullifier, recipient,
destination_federation (~248 bits each), and amount (full 64 bits).

**Actual constraints**:
- `eval_constraints` (line 282-303): every column constant across rows.
- `boundary_constraints` (line 305-346): 26 row-0 pins (8 nullifier + 8
  recipient + 8 destination + 2 amount).

**Classification**: SOUND. Test coverage in lines 490-560 exercises tamper
on every field.

### §2.C `bridge_lock_action_air::BridgeLockActionAir` — `circuit/src/bridge_lock_action_air.rs:117`

Wrapper around `effect_action_air::EffectActionAir` with
`SCHEMA_BRIDGE_LOCK` (4 fields × 8 + 3 amounts × 2 = 38 PI). The
re-export adds adversarial tests (lines 158-381) including
`tamper_value_above_2_pow_30_rejected` (line 274) confirming closure of
the 30-bit truncation gap from the legacy path. **SOUND**.

### §2.D `effect_vm::EffectVmAir` — `circuit/src/effect_vm.rs:2254`

**Doc claim**: per-effect-type selector + state transition + balance
limb correctness.

**Actual constraints** (lines 2261-…): selector booleanity, selector
sum-to-one, per-effect gated balance/nonce/cap_root deltas, etc.
Documented carve-outs at lines 2289-2328:

- Balance limb range checks deferred to executor (no 30-bit / 34-bit
  in-circuit range proof).
- Underflow protection deferred to executor (BabyBear subtraction wraps;
  executor cross-checks against pre-transaction balance).

**Classification**: SOUND in-circuit for the selector/algebraic identities,
SILVER-SOUND for the limb-range / underflow story (relies on executor
re-derivation). For playground purposes the executor side is already
applied for every action — see `turn/src/executor.rs` — so the gap does
not surface to a casual user. A federation-context attacker who can
control inter-row state but not the boundary commitment could in
principle produce malformed interior limbs, but the final-row
commitment binding rejects them.

**Playground impact**: LOW. Federation-level review needed for Golden.

### §2.E `multi_step_air::MultiStepStarkAir` — `circuit/src/multi_step_air.rs:167-207`

**Doc claim** (lines 162-166): "stub that delegates to
`crate::dsl::derivation`. Use `prove_authorization_stark` which already uses
the DSL internally."

**Actual constraints**:
```rust
fn eval_constraints(...) -> BabyBear {
    BabyBear::ZERO            // line 198
}
fn boundary_constraints(...) -> Vec<BoundaryConstraint> {
    vec![]                    // line 205
}
```

The AIR is empty: zero algebraic enforcement of anything. The verifier
`verify_authorization_stark` (line 280) merely cross-checks two PI fields
(`CONCLUSION`, `FINAL_ACCUMULATED_HASH`) against caller-supplied
expectations, then calls `stark::verify(&air, proof, &public_inputs)` —
which passes with overwhelming probability because there are no
constraints to violate.

The DOC comment on line 258-273 *itself* admits "This function verifies
ONLY that the derivation rules were applied correctly. It does NOT
verify that the body facts referenced in the derivation actually
exist in any committed Merkle tree." The reality is worse: the AIR
delegated to is empty, so even rule-application correctness is not
algebraically forced.

**Classification**: MISSING (constraints) + STUB (verifier wrapper).
The `#[deprecated]` annotations exist but the function is still callable
by `chunked_derivation::verify_chunked_authorization` (see §2.F).

**Playground impact**: HIGH if exposed. A prover whose only check is
`verify_authorization_stark` can produce a proof with arbitrary
`conclusion` and arbitrary `accumulated_hash` — the AIR contains no
constraint that ties either to the trace contents.

### §2.F `chunked_derivation::verify_chunked_authorization` — `circuit/src/chunked_derivation.rs:235`

Chains the deprecated `verify_authorization_stark` (§2.E) at line 354.
Inherits the MISSING-constraint gap of `MultiStepStarkAir`. Even though
the verifier does real cross-chunk root-evolution checks (lines 272-301)
and conclusion-position checks (lines 338-351), the individual STARK
proofs it verifies are vacuous — any prover-supplied
`(conclusion, accumulated_hash)` pair shows up as "valid."

**Classification**: SILVER-SOUND on structural chaining; MISSING on
per-chunk STARK semantics.

**Playground impact**: MEDIUM. Reachable through any
chunked-authorization surface. Closure requires re-pointing chunk-proof
generation at `dsl::derivation` so the real `eval_constraints` runs.

### §2.G `recursive_witness_bundle` — `circuit/src/recursive_witness_bundle.rs:336-403`

**Doc claim** (lines 22-27): "Both modes attest the same fact: 'the
trace satisfied the AIR's constraints against this public-input
vector.'"

**Actual behavior** (lines 51-58, quoted verbatim):
> "It is **not** a soundness equivalent of the full `EffectVmAir`. A
> trace accepted by `EffectVmShapeAir` would not necessarily satisfy
> the full Effect VM constraint set. The honest framing: a verifier
> that accepts a Golden Vision proof has learned that the trace
> satisfies the structural subset…"

The recursive aggregation calls `verify_recursive_layer_bytes` (line 399)
which validates the inner STARK proof in the recursion library, but the
inner AIR is `EffectVmShapeAir` — a constraint-subset shape AIR. The
recursive proof DOES verify the inner proof cryptographically (no
"accepted without checking" gap on the recursion plumbing itself), and
the verifier does enforce:

1. Registry lookup of `recursive_vk_hash` (line 364) — UnknownVkHash
   rejected up-front.
2. PI width minimum (line 371).
3. Optional PI cross-binding (line 379-395) — critical for tying the
   recursive proof to the receipt's declared boundary state.
4. Recursive STARK verify (line 399).

**Classification**: SILVER-SOUND. The aggregation is real, the proof is
cryptographically verified, the PI is cross-bound to receipt-side data
when the caller supplies `expected_pi_u32`. The gap is the inner AIR
**coverage**: the recursive proof certifies the structural subset only.
A `WitnessedReceipt` whose recursive path verifies could still represent
a trace that violates a non-structural constraint of `EffectVmAir`. In
Silver Vision this is mitigated by the inline-trace replay path (the
authoritative scope-2 check today). Golden Vision must grow
`EffectVmShapeAir::eval` to cover every selector branch of
`EffectVmAir::eval_constraints`.

**Playground impact**: LOW for Silver Vision (inline trace remains
authoritative). HIGH for any deployment that drops the inline trace and
relies on the recursive proof alone.

### §2.H `vk_v2::canonical_vk_v2` — `cell/src/vk_v2.rs:213`

Encodes program_bytes || air_fingerprint ||
verifier_fingerprint.canonical_bytes() || ps_bytes under the
`"dregg-vk-v2"` BLAKE3 derive_key. Length-prefixed where variable, fixed
fingerprint widths fixed-width. Tests (lines 240-376) cover every
single-component change producing distinct hashes, variant-tag
disambiguation, and concatenation-attack resistance.

**Classification**: SOUND. No stub arms.

### §2.I `WitnessedPredicateRegistry` defaults — `cell/src/predicate.rs:579-622`

`with_stubs()` (line 579) registers `StubVerifier` for every kind except
NonMembership. `default_builtins()` (line 620) returns
`with_stubs()` verbatim. `StubVerifier::verify` (line 1056-1069):

```rust
fn verify(&self, _commitment: &[u8;32], _input: &PredicateInput<'_>,
          proof_bytes: &[u8]) -> Result<(), …> {
    if proof_bytes.is_empty() {
        return Err(…);
    }
    Ok(())
}
```

The `_commitment` is ignored. The `_input` is ignored. Any non-empty
proof bytes pass for any commitment and any kind. The dedicated doc
comment (lines 597-622) is honest about this — "fail-safe-but-loud" —
but the host-side upgrade-to-real-verifiers contract is *not* exercised
anywhere in the tree; no production caller installs a real verifier for
`Dfa`, `Temporal`, `MerkleMembership`, `BlindedSet`, `BridgePredicate`,
or `PedersenEquality`.

**Classification per kind** (when running the default registry):

| Kind                | Verifier installed                         | Class |
|---------------------|---------------------------------------------|-------|
| `Dfa`               | `StubVerifier { name: "stub-dfa" }`         | STUB  |
| `Temporal`          | `StubVerifier { name: "stub-temporal" }`    | STUB  |
| `MerkleMembership`  | `StubVerifier { name: "stub-merkle…" }`     | STUB  |
| `NonMembership`     | `SortedNeighborNonMembershipVerifier`       | SILVER-SOUND |
| `BlindedSet`        | `StubVerifier { name: "stub-blinded-set" }` | STUB  |
| `BridgePredicate`   | `StubVerifier { name: "stub-bridge…" }`     | STUB  |
| `PedersenEquality`  | `StubVerifier { name: "stub-pedersen…" }`   | STUB  |

**Playground impact (all stubs)**: HIGH. Every `StateConstraint`,
`Authorization`, or `Caveat` carrying a `WitnessedPredicate` of a
stubbed kind passes with garbage proof bytes against any commitment a
playground user picks.

### §2.J `SortedNeighborNonMembershipVerifier` — `cell/src/predicate.rs:1142`

**Doc claim** (lines 1093-1098, quoted): "When `dregg-circuit`'s real
non-membership STARK lands the adjacency check joins this verifier
(today the STARK is the proof of 'lower, upper are consecutive leaves
under `commitment`'; this verifier proves only the ordering relation
between candidate and neighbors, which is necessary-but-not-sufficient
for soundness on its own)."

**Actual checks** (lines 1153-1219):
1. `proof_bytes.len() == 96` (decode shape).
2. `proof.consecutive_tag == [0xFE; 32]` — the canonical sentinel
   `NonMembershipNeighborProof::CONSECUTIVE_TAG`.
3. `proof.lower < candidate` (byte-lex).
4. `candidate < proof.upper` (byte-lex).

**Missing**: any Merkle adjacency proof binding `lower` and `upper` to
the set whose root is `commitment` (the `_commitment` parameter is
discarded, see line 1155).

**Attack sketch** (LOW barrier — the sentinel is a public constant):
- Attacker `A` wants to "prove" `candidate = 0x42…42` is *not* in a
  set committed under root `R`.
- `A` constructs `lower = 0x00…00`, `upper = 0xFF…FF`,
  `consecutive_tag = 0xFE…FE`. Neither `lower` nor `upper` exist in the
  real set — `A` need not even know the set's contents.
- `A` ships the 96-byte proof. Verifier checks `lower < candidate <
  upper` (trivially true for the bound choices) and the sentinel —
  accepts.
- `A` has just satisfied a `Renounced { authorized_set: R }` constraint
  against an arbitrary unrelated identity.

**Classification**: SILVER-SOUND (structural ordering enforced) but
**playground impact HIGH** — `Renounced` is documented as a Tier-2
categorical primitive used for governance recusal and revocation
lookups (PREDICATE-INVENTORY references at lines 252-258 of
`cell/src/predicate.rs`).

### §2.K `temporal_predicate_dsl::verify_temporal_predicate` — `circuit/src/temporal_predicate_dsl.rs:419`

**Doc claim** (lines 415-418): "The verifier provides the expected
parameters and checks the proof is consistent."

**STARK constraints** (`TemporalPredicateAir::eval_constraints` and
`boundary_constraints`, lines 81-164): per-row diff/bit-decomposition,
accumulator increment, step-index increment. **Boundary constraints
bind only**:
- Row 0: `ACCUMULATOR = 1`
- Row 0: `STEP_INDEX = 0`
- Last row: `ACCUMULATOR = pi[0]` (`padded_len`).

**The verifier wrapper** (lines 426-457) compares the *plain proof
struct fields* `proof.threshold`, `proof.num_steps`,
`proof.initial_state_root`, `proof.final_state_root` to caller
expectations — none of which are bound into the STARK trace's
boundary/PI constraints.

**Missing**: boundary constraints binding `VALUE` and `THRESHOLD`
columns to PI slots that the verifier would receive; boundary
constraints binding `STATE_ROOT` columns at row 0 and row N-1 to the
declared `initial_state_root` / `final_state_root`.

**Attack sketch (MEDIUM barrier — must construct a STARK proof):**
- Attacker constructs a witness with `threshold = 0` (trivially
  satisfiable) and arbitrary values + arbitrary state-roots.
- `stark::prove` succeeds because the per-row constraint
  `diff = value - threshold` always passes and bits decompose fine.
- Attacker sets `proof.threshold = 99999` and `proof.initial_state_root
  = whatever_the_verifier_expects` *after* the fact — these are plain
  serde fields.
- Verifier wrapper compares `proof.threshold == threshold` (passes
  because the attacker chose to forge that field), then runs
  `stark::verify` against `pi = [padded_len]` (passes because the STARK
  was actually generated honestly for *some* trace of the right padded
  length).
- Verifier accepts a "proof" that the attacker maintained a high
  threshold over the receipt chain.

**Classification**: SILVER-SOUND for trace-length / monotone-step
checks; effectively **STUB** for threshold / state-chain binding. The
DSL-side AIR has the *capability* to enforce these via additional
boundary constraints; today it does not.

**Playground impact**: HIGH if `Temporal` witnessed predicates reach
playground surfaces (intent matching exposes this — see
`TemporalPredicateRequirement` referenced at line 469).

### §2.L `note_spending_air::NoteSpendingAir` — `circuit/src/note_spending_air.rs:521-669`

**Doc claim** (lines 27-78): proves knowledge of spending key + Merkle
membership + binds `nullifier`/`merkle_root`/`value`/`asset_type`/
`destination_federation` to public inputs.

**Actual constraints**:
- Position validity (line 539)
- `is_merkle` booleanity (line 548)
- Merkle hash binding gated by `is_merkle` (lines 552-582)
- Commitment preimage gated by commitment row (lines 584-597)
- Nullifier derivation gated by commitment row (lines 599-610)

**Boundary** (lines 615-668):
- `pi[4]` → `col::DESTINATION_FEDERATION` (cross-federation replay
  protection)
- `pi[0]` → `col::NULLIFIER`
- `pi[1]` → last-row `merkle_col::CURRENT` (merkle root)
- `pi[2]` → `col::VALUE`
- `pi[3]` → `col::ASSET_TYPE`

**Classification**: SOUND, with the *single-felt PI* caveat the module
itself documents (lines 4-22): 32-byte hashes are Poseidon2-compressed
to single BabyBear felts (~31-bit binding). Action binding has migrated
to `effect_action_air::SCHEMA_NOTE_SPEND` (8-limb / 248-bit per field).
The legacy AIR continues to provide spend-side semantics.

**Playground impact**: LOW. The compress-to-felt is a binding *width*
loss, not an algebraic gap. Combined with the schema-based binding the
combined story is sound.

### §2.M `ivc::StateTransitionAir` — `circuit/src/ivc.rs:609-687`

Single algebraic constraint (`new_hash == extend_accumulated_hash(...)`)
plus four boundary constraints (initial step, initial accumulated hash,
final step count, final accumulated hash). Transition continuity is
enforced by boundary constraints + per-row hash binding (lines 626-643).

**Classification**: SOUND. Reduces to Poseidon2 collision resistance.

### §2.N `accumulator_air::AccumulatorNonRevocationAir` — `circuit/src/accumulator_air.rs`

Module is `#[deprecated]` in favor of `dsl::accumulator::verify_*`. The
deprecated wrapper still composes into `stark::verify`. The DSL
implementation has real constraints; the wrapper merely re-encodes
public inputs.

**Classification**: SOUND (delegated). Watch for the same
deprecated-wrapper-still-callable pattern as `multi_step_air` (§2.E).

### §2.O `note_bridge::verify_portable_note` — `cell/src/note_bridge.rs:1181`

**Doc claim** (lines 1180-1188): closure-based STARK verification +
trusted-roots membership.

**Actual flow** (lines 1190-1252):
1. Destination-federation match check (`local_federation_id`).
2. Trusted-root membership: **structural equality** only —
   `r.merkle_root == proof.source_root.merkle_root && r.height ==
   proof.source_root.height && r.note_tree_root ==
   proof.source_root.note_tree_root` (lines 1201-1205). No
   `is_valid_with_keys` call.
3. `note_tree_root` extraction.
4. Caller-provided closure verifies the STARK.

The signature verification *exists* on `AttestedRoot::is_valid()`
(types/src/lib.rs:389) — full Ed25519 quorum check with duplicate-signer
rejection — but `verify_portable_note` assumes its `trusted_roots`
argument was already vetted. If a caller hands an unvetted attested-root
through, this verifier accepts without a signature check.

**Classification**: SILVER-SOUND. The signature-verification surface
exists; this wrapper trusts the caller's curation. Document the
precondition or wire `AttestedRoot::is_valid_with_keys` into the
verifier.

**ThresholdQC sub-gap** (`types/src/lib.rs:386-394`):

```rust
if let Some(ref qc) = self.threshold_qc {
    return qc.0.len() >= 48;          // structural-only
}
```

When `threshold_qc` is `Some`, `is_valid` does NOT perform the
cryptographic BLS verification — only a 48-byte length check. The doc
comment (lines 385-388) explicitly defers to a higher layer. **Federation
contexts that rely on `is_valid` for BLS QCs are silently
structurally-checked-only**. SILVER-SOUND with explicit deferral; needs
a caller-side BLS check.

### §2.P `custom_effect::StubCustomEffectVerifier` — `cell/src/custom_effect.rs:377`

Same pattern as `StubVerifier`: requires non-empty proof bytes, ignores
public inputs. Registered explicitly via
`CustomEffectRegistry::register(...)` by callers — there is no default
factory installing stubs. Production callers must supply a real
`CustomEffectVerifier` impl per registered vk_hash.

**Classification**: STUB by name. Whether it amounts to a soundness
hole depends on caller hygiene; the registry doesn't ship a default,
which is better than `WitnessedPredicateRegistry`'s situation. **LOW
playground impact** unless an app's host wiring uses
`StubCustomEffectVerifier::new(...)` in production.

### §2.Q DSL backings (cross-reference)

The following DSL modules have real `eval_constraints` and serve as the
inner machinery that the `WitnessedPredicate` stubs *should* be wired
to:

- `circuit/src/dsl/circuit.rs::DreggCircuit` (line 426) — DFA / state
  machine AIR.
- `circuit/src/dsl/membership.rs::verify_membership_dsl_full` (line 256)
  / `verify_blinded_membership_dsl_full` (line 312) — Merkle and
  blinded-set membership.
- `circuit/src/dsl/derivation.rs::verify_derivation_dsl` (line 917) /
  `verify_authorization_dsl` (line 1033) — the real multi-step
  derivation verifier (replacing the empty `MultiStepStarkAir`).
- `circuit/src/temporal_predicate_dsl.rs::TemporalPredicateAir` (the
  AIR exists; the *binding* is the gap — see §2.K).
- `circuit/src/dsl/predicates/{arithmetic,compound,…}` — predicate
  primitives.

These are SOUND in their own right; the gap is purely the
WitnessedPredicateRegistry wiring (§2.I) + the temporal-binding
wrapper (§2.K) + the multi-step deprecation cleanup (§2.E).

---

## §3. Playground risk matrix

| Surface / verifier                                                  | Attack sketch                                                                                                                            | Severity | Fix-cost |
|---------------------------------------------------------------------|------------------------------------------------------------------------------------------------------------------------------------------|----------|----------|
| `StubVerifier::dfa` (`cell/src/predicate.rs:1009`)                  | Construct any 1-byte "proof"; verifier accepts. Satisfies any `Dfa { route_table_root: R, input: SignedMessage }` for arbitrary R.       | HIGH     | M        |
| `StubVerifier::temporal` (line 1015)                                | Same. Satisfies any `Temporal { dsl_hash, … }` against any DSL.                                                                          | HIGH     | M        |
| `StubVerifier::merkle_membership` (line 1021)                       | Same. Satisfies any `MerkleMembership { set_root, candidate }` against any set, any candidate.                                           | HIGH     | M        |
| `StubVerifier::blinded_set` (line 1027)                             | Same. Satisfies any `BlindedSet { set_commitment, member }`.                                                                             | HIGH     | M        |
| `StubVerifier::bridge_predicate` (line 1033)                        | Same. Satisfies any `BridgePredicate` (Gte/Lte/etc.) over any committed fact.                                                            | HIGH     | M        |
| `StubVerifier::pedersen_equality` (line 1039)                       | Same. Satisfies any `PedersenEquality` for any commitment.                                                                               | HIGH     | M        |
| `SortedNeighborNonMembershipVerifier` (line 1142)                   | Choose `lower = 0x00…`, `upper = 0xFF…`, sentinel `0xFE…`; "prove" non-membership in arbitrary set against arbitrary candidate.          | HIGH     | M-H      |
| `temporal_predicate_dsl::verify_temporal_predicate` (line 419)      | Construct honest STARK for threshold=0, then forge `proof.threshold`/`proof.state_root` plain fields. Satisfies any temporal predicate.   | HIGH     | M        |
| `multi_step_air::MultiStepStarkAir` (line 167)                      | Empty AIR; any proof with matching PI fields passes. Affects `verify_authorization_stark` and `chunked_derivation`.                       | HIGH     | M        |
| `chunked_derivation::verify_chunked_authorization` (line 235)       | Inherits multi-step gap; cross-chunk root chaining is sound but individual chunks are vacuous.                                            | HIGH     | M        |
| `recursive_witness_bundle` (line 354)                               | Recursive proof verifies the *shape* AIR not the full Effect VM AIR. A wrong-semantics trace whose shape-subset constraints hold passes. | MEDIUM   | H        |
| `note_bridge::verify_portable_note` trusted-roots check (line 1201) | Caller hands in an attested root with un-verified `quorum_signatures`; verifier accepts the spending proof.                              | MEDIUM   | L        |
| `AttestedRoot::is_valid` ThresholdQC arm (`types/src/lib.rs:390-394`) | When `threshold_qc.is_some()`, only `len >= 48` is checked. BLS aggregate not verified.                                                  | MEDIUM   | M        |
| `StubCustomEffectVerifier` (`cell/src/custom_effect.rs:377`)         | If a host wires this for production `Effect::Custom`, any non-empty proof passes. No default registry installs it.                       | LOW-MED  | App-side |
| `note_spending_air` felt-sized PIs                                  | Two distinct 32-byte hashes collide under Poseidon2-to-felt with prob 2^-31. Schema-based binding closes this for *new* spends.          | LOW      | Already migrated |
| `effect_vm` interior-row limb ranges                                | Malicious prover puts out-of-30-bit limbs on interior rows; executor re-derivation rejects. Federation-level concern.                    | LOW      | H (lookup tables) |

Severity legend: HIGH = playground user can trigger trivially / with little protocol knowledge; MEDIUM = requires unusual flow or partial prover capability; LOW = adversarial federation-context only.

Fix-cost legend: L = ≤1 day wiring; M = 1-3 days (new verifier + tests); H = ≥1 week (new circuit / range proofs / aggregation work).

---

## §4. Closure plan

### Per SILVER-SOUND / STUB

- **`StubVerifier::dfa`** → register `dregg_circuit::dsl::circuit`'s
  DFA verifier under `WitnessedPredicateRegistry::default_builtins()`.
  The DSL backend has a complete AIR with real `eval_constraints`
  (`circuit/src/dsl/circuit.rs:426`); the wiring task is wrapping it in
  a `WitnessedPredicateVerifier` impl that decodes the input bytes
  (`PredicateInput::Bytes(b)`) as the DFA input string, looks up the
  route-table by the `commitment` (route-table root), and dispatches to
  `verify_…`.

- **`StubVerifier::temporal`** → wire to a *fixed*
  `temporal_predicate_dsl::verify_temporal_predicate`. **Before** wiring,
  add boundary constraints binding `VALUE`, `THRESHOLD`, `STATE_ROOT`
  columns to PI slots (see §2.K). The current wrapper-side check on
  `proof.threshold` becomes a re-derivation of the PI rather than a
  comparison against an unbound struct field.

- **`StubVerifier::merkle_membership`** /
  **`StubVerifier::blinded_set`** → wire to
  `circuit/src/dsl/membership.rs::verify_membership_dsl_full` /
  `verify_blinded_membership_dsl_full`. Both have real
  `eval_constraints` over Poseidon2 Merkle paths.

- **`StubVerifier::bridge_predicate`** → wire to
  `bridge::present::verify_predicate_proof`
  (`bridge/src/present.rs:3135`). The cell crate cannot depend on
  bridge (cycle); resolve by having the *host* registry install the
  bridge-side verifier at startup.

- **`StubVerifier::pedersen_equality`** → register the existing
  Schnorr / Bulletproof verifier from `value_commitment.rs` /
  `commitment.rs` (the primitives exist; need a
  `WitnessedPredicateVerifier` adapter).

- **`SortedNeighborNonMembershipVerifier`** → either:
  (a) Replace the sentinel tag with a per-`(set, lower, upper)`
      adjacency commitment computed off the sorted set's adjacency
      table (the "categorical dual" form of Merkle inclusion), or
  (b) Compose with a real STARK gadget that proves Merkle inclusion of
      both `lower` and `upper` with adjacent leaf-indices under
      `commitment`. The PI of that STARK includes the two leaves and
      the two leaf-indices; the wrapper checks
      `leaf_index_upper == leaf_index_lower + 1`.
  (b) is the categorically correct form; (a) is a
      pre-cryptographic-gadget interim.

- **`recursive_witness_bundle`** → grow `EffectVmShapeAir::eval` to
  cover every selector branch of `EffectVmAir::eval_constraints`. The
  doc comment at lines 60-63 acknowledges this as "a mechanical
  translation task." Until then, retain the inline-trace replay path
  as the authoritative scope-2 check.

- **`note_bridge::verify_portable_note` trusted-roots**: drop the
  structural-equality `iter().any(...)` (lines 1201-1205) and instead
  require `trusted_roots[i].is_valid_with_keys(&federation_keys)` for
  the match. Alternatively, document the precondition on the function
  contract and add a debug_assert.

- **`AttestedRoot::is_valid` ThresholdQC arm**: land a real BLS
  aggregate verification (hints crate already pulled in elsewhere per
  comment line 387-388). Until then, document the structural-only
  surface and reject `threshold_qc.is_some()` in code paths that
  expect cryptographic finality.

- **`StubCustomEffectVerifier`** in production: not a platform bug,
  but consider renaming to `DevelopmentOnlyStubCustomEffectVerifier`
  and adding a `cfg(not(production))` gate to make accidental
  production use a compile error.

### Per MISSING

- **`SortedNeighborNonMembershipVerifier` adjacency check** — see (b)
  above.
- **`multi_step_air::MultiStepStarkAir::eval_constraints`** returns
  zero; replace with delegation to `dsl::derivation`'s real AIR or
  delete the deprecated `MultiStepStarkAir` + `verify_authorization_stark`
  pair entirely. `chunked_derivation` must migrate to
  `dsl::derivation::verify_authorization_dsl` for its per-chunk
  verification (line 354 in chunked_derivation.rs).
- **`recursive_witness_bundle` constraint coverage** — translate the
  remaining selector branches of `EffectVmAir::eval_constraints` into
  `EffectVmShapeAir::eval`.
- **Temporal AIR boundary binding** — add boundary constraints binding
  `VALUE`, `THRESHOLD`, `STATE_ROOT_INITIAL`, `STATE_ROOT_FINAL`
  columns to PI slots in `TemporalPredicateAir::boundary_constraints`
  (currently only `ACCUMULATOR` and `STEP_INDEX` are pinned).

---

## §5. Triage — Silver Vision vs. Golden Vision

### Silver Vision blockers (must land before playground)

1. **Replace `WitnessedPredicateRegistry::default_builtins()` with real
   verifiers** (§2.I, §4). This single change closes 6 of the top-13
   playground risks. Pre-requisite: wire the cell-crate registry from
   the host so the dependency cycle (cell → circuit/bridge) does not
   need to be broken in the cell crate itself.

2. **Fix `temporal_predicate_dsl` boundary binding** (§2.K). The wire
   format of `TemporalPredicateProof` does not need to change; add
   columns to the boundary-constraint vector and update
   `verify_temporal_predicate` to construct PI from caller-supplied
   parameters rather than from `proof.<field>`.

3. **Replace `SortedNeighborNonMembershipVerifier` with adjacency-bound
   form** (§2.J). The interim is the per-(set, lower, upper) commitment;
   the Golden form is the Merkle gadget. Silver-blocking the interim is
   sufficient.

4. **Delete or rewire `MultiStepStarkAir`** (§2.E). The deprecated
   wrapper masks an empty AIR. `chunked_derivation` (§2.F) must move
   to `dsl::derivation::verify_authorization_dsl` for its per-chunk
   STARK verify.

5. **Add a precondition or signature-check in
   `note_bridge::verify_portable_note`** (§2.O). One-line change to
   require `AttestedRoot::is_valid_with_keys` on the trusted-roots
   argument — closes the unvetted-root surface.

### Golden Vision deferrable

- **`recursive_witness_bundle` shape→full-AIR translation** (§2.G).
  Inline-trace replay remains authoritative in Silver. Closing the
  recursive coverage gap is required only for deployments that drop the
  inline trace.

- **`effect_vm` in-circuit limb-range / underflow proofs** (§2.D). The
  executor-side cross-check is real and exercised. Lookup-table-based
  in-circuit range proofs are a Golden-Vision-cleanup item.

- **`AttestedRoot::is_valid` BLS aggregate** (§2.O sub-gap). For
  federations that mostly use the Ed25519 quorum path today, this can
  defer until the `hints` integration matures.

- **`note_spending_air` felt-sized PIs** (§2.L). The schema-based
  binding (`SCHEMA_NOTE_SPEND` in `effect_action_air`) already provides
  the full-fidelity binding for new spends. Legacy PIs continue to ship
  but are not the source of truth for action binding.

### Cross-cutting Silver hardening

- Audit the *host* binary that constructs `TurnExecutor`s and confirm
  it calls `set_witnessed_registry(...)` with a real-verifier registry
  before any action evaluation. Document this precondition prominently
  in `TurnExecutor::new` docstrings and add a startup self-test that
  refuses to run with the stub registry when `cfg(production)` is set.

- Land a `WitnessedPredicateRegistry::sanity_check_no_stubs` API for
  hosts that want a runtime assertion that all installed verifiers are
  real.

---

## Appendix A — File:line citation index

| Symbol                                                  | Location |
|---------------------------------------------------------|----------|
| `EffectActionAir`                                       | `circuit/src/effect_action_air.rs:151` |
| `SCHEMA_*` (23 schemas)                                 | `circuit/src/effect_action_air.rs:332-610` |
| `BridgeActionAir`                                       | `circuit/src/bridge_action_air.rs:224` |
| `BridgeLockActionAir`                                   | `circuit/src/bridge_lock_action_air.rs:117` |
| `EffectVmAir::eval_constraints`                         | `circuit/src/effect_vm.rs:2254` |
| `MultiStepStarkAir::eval_constraints` (returns ZERO)    | `circuit/src/multi_step_air.rs:190-199` |
| `verify_authorization_stark`                            | `circuit/src/multi_step_air.rs:280` |
| `verify_chunked_authorization`                          | `circuit/src/chunked_derivation.rs:235` |
| `RecursiveProofProducer::produce`                       | `circuit/src/recursive_witness_bundle.rs:233` |
| `verify_recursive_proof_variant`                        | `circuit/src/recursive_witness_bundle.rs:354` |
| `EffectVmShapeAir` (structural subset)                  | `circuit/src/effect_vm_p3_air.rs` |
| `canonical_vk_v2`                                       | `cell/src/vk_v2.rs:213` |
| `WitnessedPredicateRegistry::default_builtins`          | `cell/src/predicate.rs:620` |
| `WitnessedPredicateRegistry::with_stubs`                | `cell/src/predicate.rs:579` |
| `StubVerifier::{dfa,temporal,merkle_membership,...}`    | `cell/src/predicate.rs:1003-1070` |
| `SortedNeighborNonMembershipVerifier`                   | `cell/src/predicate.rs:1142` |
| `NonMembershipNeighborProof::CONSECUTIVE_TAG`           | `cell/src/predicate.rs:1139` |
| `StubCustomEffectVerifier`                              | `cell/src/custom_effect.rs:377` |
| `verify_portable_note`                                  | `cell/src/note_bridge.rs:1181` |
| `AttestedRoot::is_valid`                                | `types/src/lib.rs:389` |
| `TemporalPredicateAir::eval_constraints`                | `circuit/src/temporal_predicate_dsl.rs:81` |
| `TemporalPredicateAir::boundary_constraints`            | `circuit/src/temporal_predicate_dsl.rs:147` |
| `verify_temporal_predicate`                             | `circuit/src/temporal_predicate_dsl.rs:419` |
| `NoteSpendingAir::eval_constraints`                     | `circuit/src/note_spending_air.rs:521` |
| `NoteSpendingAir::boundary_constraints`                 | `circuit/src/note_spending_air.rs:615` |
| `StateTransitionAir::eval_constraints` (IVC)            | `circuit/src/ivc.rs:609` |
| DSL real DFA AIR                                        | `circuit/src/dsl/circuit.rs:426` |
| DSL real membership verifier                            | `circuit/src/dsl/membership.rs:256` |
| DSL real derivation verifier                            | `circuit/src/dsl/derivation.rs:1033` |
