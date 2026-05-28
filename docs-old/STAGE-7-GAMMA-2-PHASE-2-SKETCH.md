# Stage 7-γ.2 Phase 2 — Joint Aggregation AIR (Sketch)

**Status:** design sketch only. Phase 1 (PI surface + AIR bilateral aux columns
+ off-AIR verifier loop) is implemented and lives in
`circuit/src/effect_vm.rs`, `turn/src/bilateral_schedule.rs`,
`turn/src/executor.rs::verify_bilateral_bundle`, and
`verifier/src/bilateral_pair.rs`. Phase 2 lifts the Rust verifier loop into
a recursive aggregation STARK that consumes N per-cell `WitnessedReceipt`s
and emits one outer proof.

The Phase 1 PI fields **are** the inputs to Phase 2 — the seven 4-felt
accumulator roots, the seven count fields, and `IS_AGENT_CELL` — so no
per-cell AIR work is required for Phase 2; only an outer aggregation AIR.

---

## 1. Design intent

Phase 1 verifies bilateral consistency by running, in Rust, against each
`WitnessedReceipt` independently:

1. `stark::verify` against `EffectVmAir`.
2. `TurnExecutor::verify_bilateral_bundle` — recompute the schedule from
   `(call_forest, ACTOR_NONCE)`, then compare each per-cell PI's bilateral
   slots against the schedule.

Phase 2 collapses both checks into a single outer recursive STARK. A
verifier holding only one outer proof, the original `Turn`, and the public
verification key of `EffectVmAir` learns:

- N inner Effect VM proofs were all individually valid.
- All N per-cell PIs share the same `TURN_HASH` / `EFFECTS_HASH_GLOBAL` /
  `ACTOR_NONCE` / `PREVIOUS_RECEIPT_HASH` (γ.0 binding).
- Each per-cell PI's bilateral count + root fields agree with the schedule
  derived from `Turn`.
- Exactly one of the inner proofs has `IS_AGENT_CELL == 1` (and it's the
  one whose cell-id matches `Turn.agent`).

The outer proof's public input is *just* the turn-level summary:
`(TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE, PREVIOUS_RECEIPT_HASH,
N_CELLS, AGENT_CELL_ID, BILATERAL_CONSISTENT=1)`. ~12-16 felts vs. the
N × (BASE_COUNT ≈ 74) felts of per-cell PIs.

---

## 2. Concrete AIR shape

### 2.1 Public inputs (outer AIR)

```text
const OUTER_TURN_HASH_BASE: usize = 0;     // 4 felts
const OUTER_EFFECTS_HASH_GLOBAL_BASE: usize = 4;  // 4 felts
const OUTER_ACTOR_NONCE: usize = 8;        // 1 felt
const OUTER_PREVIOUS_RECEIPT_HASH_BASE: usize = 9; // 4 felts
const OUTER_AGENT_CELL_ID_BASE: usize = 13; // 8 felts
const OUTER_N_CELLS: usize = 21;           // 1 felt
const OUTER_BILATERAL_CONSISTENT: usize = 22; // 1 felt, must == 1 for accept
const OUTER_BASE_COUNT: usize = 23;
```

The outer AIR's PI surface is **fixed-width** — independent of N. This is
the headline win for outer-verifier complexity: instead of dispatching on a
variable-length bundle, a single sequence of 23 felts is sufficient.

### 2.2 Trace layout (outer AIR)

The outer trace has one *block* of rows per inner proof. Inside each block:

```
columns:
  inner_proof_verify_aux[i]   : Plonky3 recursive-verifier columns for proof i
                                (same shape as RecursiveIvcStep — already
                                exists in circuit/src/plonky3_verifier_air.rs)
  inner_pi_buffer[i][0..74]   : the inner proof's full PI vector, lifted
                                into trace columns for per-row constraint
                                access
  cell_id_decomp[i][0..8]     : the inner proof's claimed cell-id, in
                                8-felt decomposition
  schedule_replay_cols        : aux columns running the same accumulator
                                update as turn::bilateral_schedule, in-AIR
  is_agent_seen_cumulative    : running count of how many inner proofs
                                have set IS_AGENT_CELL == 1 (must end at
                                exactly 1)
```

Block height per inner proof is a power-of-two; the outer trace pads to
the next power-of-two N rounds up to. `MAX_TOUCHED_CELLS = 8` from the
design (see open question 3 in the Phase 1 design) caps the outer trace
height at `8 × per_proof_block_height`, well within Plonky3 budget.

### 2.3 Constraint groups (outer AIR)

For each inner-proof block:

- **CG-1: inner verify.** The recursive-verifier AIR constrains
  `inner_proof_verify_aux[i]` to be a transcript of a verifying execution
  of `EffectVmAir` against `inner_pi_buffer[i]`. (This is what
  `RecursiveIvcStep` already does for a single inner proof.)

- **CG-2: turn-identity agreement.** For each of `TURN_HASH`,
  `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`, `PREVIOUS_RECEIPT_HASH`:
  ```
  inner_pi_buffer[i][slot] == OUTER_PI[slot]
  ```

- **CG-3: schedule replay.** The aux columns recompute the per-cell
  schedule projection in-trace, using the call_forest data embedded in
  `OUTER_TURN_HASH` (preimage is supplied as private trace witness).
  The recomputed counts + accumulator roots must equal the
  `inner_pi_buffer[i][OUTBOUND_TRANSFER_COUNT..INTRO_AS_TARGET_ROOT_BASE+4]`
  slots. This is the in-AIR version of `verify_bilateral_bundle`'s
  per-cell loop.

- **CG-4: IS_AGENT_CELL accounting.** Running cumulative sum over the
  inner blocks; must equal exactly 1 at the last row, and the one
  block where `IS_AGENT_CELL == 1` must have `cell_id_decomp[i] ==
  OUTER_AGENT_CELL_ID`.

- **CG-5: cross-side existence.** A *boolean matrix* of "did this cell
  appear in this turn's schedule entry?" is constrained at the trace level.
  Specifically:
  - For each `(i, schedule_transfer_idx)`: there's a felt indicating
    whether `cell_id[i]` plays a role (sender or receiver) in transfer
    `idx`. The matrix must satisfy: if any entry is 1 in a row, the
    counterparty's row also has a 1 in the matching column.

  This is the in-AIR version of `verify_bilateral_bundle`'s
  cross-side existence check.

### 2.4 Boundary constraints

```
last_row.is_agent_seen_cumulative == 1
last_row.BILATERAL_CONSISTENT == 1
```

### 2.5 Cell-id binding

A subtle point: each inner proof carries no explicit "this is my cell-id"
PI field today (cell-id is encoded into `IS_AGENT_CELL` via boundary
constraints on row 0's `NONCE` column matching `ACTOR_NONCE`, but the cell
itself is named only by the bundle harness in Rust). Phase 2 requires
either:

- (a) Adding `OWNER_CELL_ID_BASE: usize` to the per-cell PI (8 felts) so
  the outer AIR can directly compare `cell_id_decomp[i]` to
  `inner_pi_buffer[i][OWNER_CELL_ID_BASE..+8]`. This is the cleaner option.
- (b) Constraining `cell_id_decomp[i]` indirectly via the bilateral
  accumulators' peer-cell encodings — i.e., the schedule replay only
  matches the right accumulator if `cell_id_decomp[i]` was the cell
  whose bilateral PI was constructed.

Recommend (a). It's one additional per-cell PI field, mechanical to add,
and Phase 1's design doc §10 question 2 already gestures at it.

---

## 3. Witness construction (prover side)

The outer prover receives, from the harness:

```
struct OuterProverInputs {
    turn: Turn,
    per_cell: Vec<(CellId, WitnessedReceipt)>,
}
```

It builds the outer trace by:

1. Running `EffectVmAir::generate_trace` for each inner proof
   (recursive-verifier witness construction).
2. Running `ExpectedBilateral::from_turn(&turn)` to derive the schedule.
3. For each `(cell, wr)`, lifting `wr.public_inputs` into trace columns
   and computing the schedule replay aux columns by mirroring
   `roots_for(cell, turn.nonce)` per-row.
4. Computing the cumulative `is_agent_seen_cumulative` column.

The prover is *purely classical Rust* over the existing primitives —
there's no new gadget research required. The aggregation AIR is
engineering on a known shape.

---

## 4. Constant-size verification savings

| | Phase 1 | Phase 2 |
|---|---|---|
| Verifier work per turn | N inner verifies + Rust loop | 1 outer verify |
| PI footprint per turn | N × 74 felts | 23 felts |
| Bundle size (bytes) | ~10-50 KB × N | ~10-50 KB (single proof) |
| Cross-side existence check | Rust loop with `HashSet` | In-AIR matrix constraint |
| Chain-IVC step (Stage 7-ζ) | Fold N proofs per turn | Fold 1 proof per turn |

For a 4-cell turn (typical batch transfer), Phase 2 cuts the verifier's
work by ~4× and the on-wire PI by ~12×. For an 8-cell turn (the
`MAX_TOUCHED_CELLS` cap), the savings are ~8× and ~26×.

---

## 5. What Phase 2 does NOT change

- **Phase 1's PI layout.** Outer AIR consumes the existing per-cell PI
  fields as-is; no new bilateral PI slots are introduced. (Only one
  additional `OWNER_CELL_ID_BASE` slot is recommended, see §2.5.)
- **Phase 1's id derivation.** Same canonical preimages
  (`dregg-transfer-id-v1`, etc.) — Phase 2 *constrains* them in-AIR
  instead of recomputing in Rust.
- **The cell program's STARK shape.** Per-cell `EffectVmAir` is
  unchanged; Phase 2 only adds an outer wrapper.
- **`WitnessedReceipt` wire shape.** Phase 2 emits a *new* artifact (an
  `AggregateBilateralReceipt` containing one outer proof + the per-cell
  receipts as embedded witness for replay/audit only). Existing chains
  continue verifying as Phase 1 bundles.

---

## 6. Implementation order (post-Phase-1)

1. **Add `OWNER_CELL_ID_BASE`** to the per-cell PI (§2.5 option (a)).
   Mechanical PI slot addition + AIR boundary constraint binding to the
   per-cell `NONCE_OWNER_CELL` column (which already carries the cell-id
   on row 0 of every cell's trace).
2. **Build the outer AIR scaffold** in `circuit/src/aggregate_bilateral_air.rs`,
   reusing the `RecursiveIvcStep` recursive-verifier columns for inner-proof
   blocks.
3. **Implement CG-2 (turn-identity agreement)** — N×4 cross-block equality
   constraints. Simple to author and verify.
4. **Implement CG-3 (schedule replay)** by transliterating
   `bilateral_schedule::roots_for` into AIR aux-column updates. The
   Poseidon2 absorb gadget is already paved (`circuit/src/poseidon2_air.rs`).
5. **Implement CG-4 (IS_AGENT_CELL accounting)** — single running-sum
   column; trivial.
6. **Implement CG-5 (cross-side existence)** — schedule-by-cell matrix.
   This is the most complex CG; consider whether to lift it to a
   separate AIR if the constraint degree explodes.
7. **Wire it through the prover** in
   `turn/src/aggregate_bilateral_prover.rs` (new file) and add a
   `dregg-verifier aggregate-bilateral` subcommand.

Estimated effort: 4-6 weeks for an experienced Plonky3 author, mostly
front-loaded into CG-3 and CG-5 authoring.

---

## 7. Open questions for the architect (deferred to Phase 2 kickoff)

1. **MAX_TOUCHED_CELLS in-AIR cap.** Phase 1 left this at 8 informally;
   Phase 2's trace must pad to a power-of-two count of inner blocks. Cap
   at 8 (3-bit selector) or 16 (4-bit selector)? Real turns sit at 2-4.
2. **Cross-federation aggregation.** Phase 2 stays single-federation
   (per §8.5 of the Phase 1 design). Cross-federation `Introduce` aggregation
   requires bridge work — outside Phase 2 scope.
3. **Verifier crate dependencies.** Phase 2 introduces an outer-AIR
   verification path; `dregg-verifier` will need to deserialize the outer
   proof shape. Recommended: a new module `verifier/src/aggregate_bilateral.rs`
   mirroring `bilateral_pair.rs`.
4. **Recursive-verifier soundness.** The recursive-verifier AIR's
   security level is the same as the inner AIR (Plonky3 100-bit). Phase 2
   composes 1 + N proofs; the security is the minimum across all of them,
   not a degradation per inner proof.

---

## 8. Closing

Phase 2 is *engineering on a known shape*. The recursive-verifier AIR
exists (`circuit/src/plonky3_verifier_air.rs::RecursiveIvcStep`); the
schedule replay logic exists (in Rust, `turn/src/bilateral_schedule.rs`);
the Poseidon2 gadget is paved; the per-cell PI surface is finalized at
Phase 1.

Phase 1 alone is a sufficient artifact for the audit-of-record use case
(an auditor holding 2-3 WitnessedReceipts can replay the Rust loop and
verify cross-cell agreement). Phase 2 is the *production-scale*
shape — when bundle ingest becomes a hot path in the verifier (e.g., for
the chain-IVC step in Stage 7-ζ), the constant-size verification cost
matters.
