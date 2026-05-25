# Stage 7-γ — Turn-Level Aggregation AIR

**Status:** design exploration, no Rust changes. Companion to
`STAGE-7-PLUS-DESIGN.md` (which named 7-γ as "where the research begins")
and `EFFECT-VM-SHAPE-A.md`. This document picks 7-γ off the shelf and
makes it concrete enough that an implementation agent can pick up the
keyboard.

The animating sentence is the Golden Vision: *the algebraic proof fully
constrains ALL operations and attests to ALL capability operations
across ALL turns; receipt chains + private witness data are sufficient
to replay the protocol within a useful margin.* Today we have the
opposite: each per-cell Effect VM proof attests to a slice of one turn,
and the federation runtime stitches the slices together with executor
trust. 7-γ is the proof-system change that turns the stitching into
algebra.

---

## 1. The semantic gap, precisely

A turn `T` carries a `call_forest: CallForest` (a tree of `Action` nodes
each targeting some `target: CellId`). The set of touched cells is
`touched(T) = { a.target : a ∈ T.call_forest }`. The current proving
flow (`turn/src/executor.rs::convert_turn_effects_to_vm` at
`turn/src/executor.rs:1541`) does, per cell `c ∈ touched(T)`:

1. Walk the forest. For every `Effect e ∈ action.effects` that "touches"
   `c` (heuristically: a field of `e` equals `c`), push a `VmEffect`
   row into a vector. Effects not touching `c` are silently dropped.
2. Compute `effects_hash_4 = compute_effects_hash_4(per_cell_vm_effects)`
   (`circuit/src/effect_vm.rs:1425`).
3. Build a 105-column trace for the per-cell `EffectVmAir`, including
   `state::STATE_COMMIT` continuity, `bal_lo`/`bal_hi` balance evolution,
   the 46 selector columns, and the param columns.
4. Prove. Public inputs (`circuit/src/effect_vm.rs::pi`):
   - `OLD_COMMIT[4]`, `NEW_COMMIT[4]` — 4-felt typed `Commitment4<T>` of the
     cell's state before/after the turn.
   - `EFFECTS_HASH[4]` — Poseidon2 over the cell-projected `VmEffect` rows.
   - `INIT_BAL_LO/HI`, `FINAL_BAL_LO/HI`, `NET_DELTA_MAG`, `NET_DELTA_SIGN`.
   - `CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS`, `CUSTOM_EFFECT_COUNT`.
   - `APPROVED_HANDOFFS_BASE[4]`, custom proof entries.

There is **no field for `Turn::hash`**, no field for `Turn::nonce`, no
field for `previous_receipt_hash`, no field for any *other* cell's
state. The AIR is parameterised on `(cell_id, OLD, NEW, effects_local)`
and that is the universe it can speak about.

The "gap" is what this universe cannot say. Three canonical examples:

### 1a. `Transfer { from: alice, to: bob, amount: 100 }`

Two per-cell proofs.
- alice's proof sees `VmEffect::Transfer { amount: 100, direction: 1 }`
  (`turn/src/executor.rs:1576..1587`). Its `bal_lo` column decreases by
  100 across one row. Its `NET_DELTA_MAG = 100, NET_DELTA_SIGN = 1`.
- bob's proof sees `VmEffect::Transfer { amount: 100, direction: 0 }`.
  Its `bal_lo` increases by 100. `NET_DELTA_MAG = 100, NET_DELTA_SIGN = 0`.

The AIR proves each row's `state_after = state_before ± amount` within
its own trace. **It does not prove** that alice's `-100` equals
`-(bob's +100)`. A malicious prover with witness-generator access can
produce two proofs where alice sent 100 and bob received 50, or two
proofs where the `amount` field in the `effects_hash` preimage on each
side differs. The executor catches this today because it sees the
original `Effect::Transfer` and runs both projections from the same
source. *Strip the executor away* (think bridge boundary or third-party
verification) and the cross-cell binding evaporates.

### 1b. `GrantCapability { from: alice, to: bob, cap }`

Asymmetric. The projection at `turn/src/executor.rs:1595..1599`
emits a `VmEffect::GrantCapability` row only for `to == cell_id`. So
bob's proof advances `cap_root` via a one-felt hash-chain
(`effect_vm.rs:1542..1547`). Alice's proof emits nothing for this
effect — her per-cell projection skips it entirely. Her c-list change
(consume slot) is *invisible* to the AIR, present only in the executor's
mutation of `CellState.capabilities`. There is no algebraic statement
that bob's new `cap_root` was derived from a slot alice actually held,
and there is no algebraic statement that alice consumed anything.

### 1c. `Introduce { introducer, recipient, target, permissions }`

Three cells touched (`introducer`, `recipient`, `target`), three
projections, three independent per-cell proofs. Each emits
`VmEffect::Introduce { intro_hash }` over the same
`(introducer, recipient, target, permissions)` tuple. The three
`intro_hash` values happen to be equal because the inputs are equal —
no AIR constraint forces equality across the three proofs. A prover
controlling all three could emit divergent `intro_hash` values, each of
which independently passes the per-cell AIR, and only the executor
notices the divergence.

The shape of the gap is always the same. **A turn's call_forest is one
object. Its proof is N objects glued together at runtime by the
prover/executor and never algebraically joined.** Replacing the
runtime glue with algebra is what 7-γ is for.

---

## 2. Three candidate aggregation approaches

### A. Bundle-with-shared-PI

```
                  Turn (v3 hash)
                       |
                       v
        +--------------+----------------+
        |              |                |
        v              v                v
   per-cell A     per-cell B       per-cell C
   PI: turn_hash  PI: turn_hash    PI: turn_hash
       effects_g      effects_g        effects_g
       nonce          nonce            nonce
   (executor PI-match enforces shared values)
```

**Mechanism.** Add three new PI fields to `EffectVmAir::pi` — let us
call them `TURN_HASH_BASE[4]`, `EFFECTS_HASH_GLOBAL_BASE[4]`,
`ACTOR_NONCE`. Each per-cell proof binds them. The verifier checks
that for the N proofs of a turn, all N agree on the same triple. **No
aggregation AIR. No recursion.** The constraint is protocol-level: the
executor refuses to accept a turn unless all N proofs' PIs match on
those slots.

**Prover cost.** Identical to baseline: N independent Effect VM proofs.
The trace gets three new PI bindings but the cost is the boundary
constraints in the prover's last row.

**Proof size.** N × `~30KB` (current Plonky3 STARK), no aggregation
saving.

**Algebraically constrained.** All three identifiers (turn hash,
global effects hash, actor nonce) are in PI, so the executor's
PI-match against the canonical `Turn::hash` (post-Stage-7-α) and a
canonical `effects_hash_global = Poseidon2(call_forest)` settles
agreement. Equivalent to the executor stamping "these all belong to
turn T."

**Stays executor-trusted.** The actual cross-cell *semantics* — that
alice's `-100` matches bob's `+100`, that `effects_local[c]` is a
correct projection of `effects_hash_global` to `c`, that there are no
*extra* per-cell proofs that don't appear in the call_forest, and
conversely. The bilateral arithmetic is verified by the executor.

**Composability.** Trivial. The recursive verifier (Plonky3-native, the
`circuit/src/plonky3_verifier_air.rs::RecursiveIvcStep` building
block) can run N inner Effect VM proofs as N parallel branches of an
IVC chain.

**Engineering risk.** Low. ~1 week. Touches `EffectVmAir` PI layout,
`turn/src/executor.rs::verify_proof_carrying_turn`'s PI-matching loop,
and `Turn::hash` (the 7-α prerequisite).

### B. Single outer AIR over the call_forest

```
                       Turn
                        |
                        v
   +------------------------------------------+
   | OuterTurnAir trace (rows × wide-cells)   |
   |  row 0: cell A pre-state, deltas, ...    |
   |  row 1: cell A post / cell B pre         |
   |  row 2: ... cell C pre                   |
   |  ... cross-row constraints bind          |
   |      cell A.bal_lo[N-1] == final_A       |
   |      Σ row.delta == 0                    |
   +------------------------------------------+
                        |
                        v
                  one STARK proof
                  PI: turn_hash, effects_g,
                      ε(touched cells), fee, nonce
```

**Mechanism.** Replace the per-cell AIR with a single big AIR whose
trace columns are indexed `(cell_idx, field)` for `cell_idx ∈
0..MAX_CELLS_PER_TURN`. Each row corresponds to one *effect* (not one
cell), with a `cell_idx` selector that gates which "lane" gets updated.
Cross-lane constraints add: `Σ_lanes Δbal_lo == 0` enforces
conservation row-by-row.

**Prover cost.** Trace area is now `O(rows_per_effect × MAX_CELLS)`.
With current EFFECT_VM_WIDTH=105 and (say) MAX_CELLS=8, the column
count balloons to ~800. Prover memory and FFT cost scale roughly
linearly in column count for fixed row count, so a 4-8× slowdown over
per-cell baseline at the minimum.

**Proof size.** One proof.

**Algebraically constrained.** Everything within the trace. Bilateral
Transfer arithmetic is a row constraint over two lanes. Introduce
constraints are 3-lane row constraints. The AIR can natively express
"effect e touches cells {a,b}" without ever talking to an executor.

**Stays executor-trusted.** Authorization (signatures, bearer caps),
the `Turn::hash` v3 v3 binding, and any cell whose program is custom
(those still chain to `custom_program_proofs`).

**Composability.** Very poor. Every turn shape needs a separate AIR
instance with MAX_CELLS chosen ahead of time. Sparse turns (most are
1-2 cells) pay full cost. Cannot fold N turns into one without an outer
recursion layer anyway.

**Engineering risk.** High. ~2 months. The cleanest version of "the
proof says everything" — and also the version that breaks every
existing trace-generation utility. Recommend treating it as a
*specification* of what the algebra should constrain, then implementing
that via approach A or C.

### C. Recursive IVC over the call_forest tree

```
                            root proof
                           (whole turn)
                                 |
                  IVC fold over call_forest tree
                                 |
                  +--------------+--------------+
                  |              |              |
              root tree[0]   root tree[1]   root tree[2]
              (sub-IVC)      (sub-IVC)      (sub-IVC)
                  |              |              |
            +-----+-----+        ...
            |           |
       leaf proof   leaf proof
        (per-cell)   (per-cell)
```

**Mechanism.** Walk the call_forest bottom-up. Each leaf `Action`
produces a proof attesting to its effects against the targeted cell's
trace slice (this is a smaller version of today's Effect VM, scoped
to one Action rather than the whole turn). Each internal node folds
its children's proofs into a parent proof using a Nova-style folding
scheme (or Plonky3's recursive verifier as the IVC step). The fold
preserves the running invariants: `effects_acc` (accumulated effects
hash), `delta_acc` (running balance net delta), `cells_seen`
(commitment set). The root proof attests to the whole turn.

**Prover cost.** Proportional to forest size; each step is small but
the folding scheme adds per-step overhead. Estimate 2-4× per-cell
baseline for forests of 4-8 cells.

**Proof size.** Constant (one root proof). This is the IVC win.

**Algebraically constrained.** Everything natively expressible at the
fold step. Bilateral Transfer becomes a fold-step row where the
running `delta_acc` updates by both `+100` and `-100`. Causality
(`parent action before children`) is structural in the fold order.

**Stays executor-trusted.** Authorization signatures (unless we bring
in a signature gadget); the original cell-state commitments at leaves
(those still come from a trusted federation snapshot).

**Composability.** Best. The root proof of turn T can itself become a
leaf in a turn-chain IVC (this is 7-ζ).

**Engineering risk.** High. Requires either picking a folding scheme
(Nova, ProtoStar, HyperNova — none of these are in `pyana-circuit`
today) or building the Plonky3-native recursive verifier into a
proof-of-proofs loop. `circuit/src/ivc.rs` and
`circuit/src/plonky3_verifier_air.rs` have *some* of the primitives
(`IvcAir`, `RecursiveIvcStep`, `build_recursive_ivc_chain`) but they
target state-root chains, not Effect VM proofs. The recursive
verification of an EffectVmAir proof inside an AIR is the unsolved bit.

### Summary

| Property              | A. Bundle | B. Outer AIR | C. IVC fold |
|-----------------------|-----------|--------------|-------------|
| Prover cost vs. baseline | 1×       | 4-8×        | 2-4×        |
| Proof size              | N proofs  | 1 proof      | 1 proof     |
| Bilateral binding       | executor  | algebraic    | algebraic   |
| Projection totality     | executor  | algebraic    | algebraic   |
| Engineering risk        | low       | high         | high        |
| Time-to-first-artifact  | ~1 week   | ~2 months    | ~4-6 weeks  |
| Composes across turns?  | only via 7-ζ | needs wrap | natively    |

---

## 3. The proof composition language

Whichever approach lands, the aggregate proof needs to express five
statements. Calling them `P1..P5`:

### P1. Turn-identity binding

> "These N per-cell traces refer to the same turn T."

Realised by sharing a single `turn_hash` PI across all per-cell proofs,
where `turn_hash` is the v3 `Turn::hash()` that covers all
execution-proof fields (this is the 7-α prerequisite —
`turn/src/turn.rs:144` today is v2 and excludes the proof fields).

- **A. Bundle**: native via shared PI + executor PI-match.
- **B. Outer AIR**: native — one trace, one PI.
- **C. IVC fold**: native — `turn_hash` is the carried public state.

### P2. Projection totality and soundness

> "Every effect in `call_forest` is projected to at least one per-cell
> trace, and conversely every per-cell projection row corresponds to a
> real call_forest effect."

This is the subtle one. Today's `convert_turn_effects_to_vm` (`turn/src/executor.rs:1541`)
silently drops effects that don't reference `cell_id`. The aggregate
proof needs to assert that the union of cell-projected rows reconstructs
the global effect sequence. The clean formulation:

```
  Poseidon2(effects_local[c1] ‖ effects_local[c2] ‖ ...)
     ==  effects_hash_global  ==  Poseidon2(call_forest_effects)
```

where the order of concatenation is canonical (e.g., DFS over the
call_forest, cells in first-appearance order).

- **A. Bundle**: needs an extra Poseidon2-merge constraint in PI plus
  executor-side enforcement that the canonical order is followed.
- **B. Outer AIR**: native — the trace literally contains the global
  effect sequence, with cell_idx selectors.
- **C. IVC fold**: native — the fold step at each Action node
  accumulates `effects_local[targeted_cell]` into `effects_acc`.

### P3. Bilateral arithmetic agreement

> "Cross-cell effects' two-sided arithmetic agrees."

Concretely:
- `Transfer(a, b, n)`: a's net_delta contribution `-n`, b's `+n`,
  summed = 0.
- `GrantCapability(a → b, cap)`: a's c-list `consume(slot)`, b's c-list
  `insert(slot_image)`, joined by a `delegation_cert_hash`.
- `Introduce(intro, recip, tgt, perm)`: all three sides bind the same
  `intro_hash`.

The canonical algebraic form is a *bilateral log*: a Poseidon2
accumulator `transfer_log_root` (or `grant_log_root`,
`intro_log_root`) that each touched cell's per-cell proof contributes
to. The aggregation step asserts both sides contributed equally:

```
  for each Transfer(a,b,n) in turn:
    transfer_log_a contributes hash(direction=1, amount=n, peer=b)
    transfer_log_b contributes hash(direction=0, amount=n, peer=a)
    => merged_transfer_log_root must reflect both
```

- **A. Bundle**: the cleanest version requires an *aggregation
  micro-AIR* — one that recomputes the merged log from per-cell PIs
  and asserts pairwise matches. Roughly a fourth Poseidon2 chain in PI;
  not free, but tractable. Without that micro-AIR, this stays
  executor-trusted.
- **B. Outer AIR**: native — bilateral Transfer is a single row with
  constraints over two cell lanes.
- **C. IVC fold**: native — the fold step at an Action emitting
  Transfer updates both cells' lanes of the carried state.

### P4. Cell program (`CellProgram`) verification

> "Every cell whose `program` is non-None had its program's AIR run
> over the turn's effects on that cell."

Today's `custom_program_proofs: Option<Vec<CustomProgramProof>>` on
`Turn` carries per-custom-effect proofs that the executor verifies
out-of-band against `program.vk_hash`. The PI layout already reserves
`CUSTOM_PROOFS_BASE` (8 felts per custom effect: 4 vk_hash + 4 proof
commitment, `circuit/src/effect_vm.rs:596`). The aggregation step must
ensure that *for each cell c with a program*, the number of custom
proofs corresponds to `s_custom` rows in c's trace, and that each
proof was checked.

- **A. Bundle**: today's mechanism survives — executor checks
  `custom_program_proofs` against the proof commitments in PI. This is
  already algebraic in the sense that the proof commitment is bound.
- **B/C**: same as A; custom program proofs are just another "leaf"
  that the aggregate verifier consumes.

### P5. Authorization

> "For each Action a, its `a.authorization` was a valid auth for the
> targeted cell's permissions."

Per-cell AIR has no view of authorization today; this is fully
executor-trusted (`turn/src/executor.rs`'s authorization gate).
Bringing it inside the proof system requires either:
- (a) An in-circuit Ed25519 / Schnorr verifier (the
  `circuit/src/schnorr_air.rs` and `circuit/src/native_signature_air.rs`
  bones exist). Cost: ~10K constraints per signature; not crazy.
- (b) A bearer-cap derivation proof (`DelegationProofData::StarkDelegation`
  in `turn/src/action.rs:163`) folded in as a custom child proof.

**For 7-γ scope we keep authorization executor-trusted.** Stage 9
(per `STAGE-7-PLUS-DESIGN.md` §6.4 L-3) brings signature-in-circuit at
the federation boundary. 7-γ's job is the *cross-cell* binding, not the
*auth-in-AIR* binding.

| Property | A. Bundle | B. Outer AIR | C. IVC fold | Where it sits today |
|----------|-----------|--------------|-------------|---------------------|
| P1 turn-id | native (PI) | native | native | executor-trusted |
| P2 projection totality | needs constraint + canonical order | native | native | dropped silently |
| P3 bilateral agreement | needs micro-AIR | native | native | executor reads source `Effect` |
| P4 program verification | already mostly there | same | same | executor-checks custom_program_proofs |
| P5 authorization | out-of-scope (Stage 9) | out-of-scope | out-of-scope | executor-trusted |

---

## 4. What the receipt chain carries

The Golden Vision asks that "receipt chains + private witness data" be
sufficient to *replay* the protocol. Today's `TurnReceipt`
(`turn/src/turn.rs:263`) carries `turn_hash`, `pre_state_hash`,
`post_state_hash`, `effects_hash`, `previous_receipt_hash`, plus
derivation records, events, executor signature. **It carries no proof
bytes and no witness.** The proof lives on `Turn.execution_proof`; the
witness lives nowhere — the prover's trace is constructed in-memory and
discarded after proving.

For algebraic replay to work, we need three things bundled together.

### 4.1 The `WitnessedReceipt` structure

A proposed shape (lives in `pyana-turn` next to `TurnReceipt`):

```rust
pub struct WitnessedReceipt {
    /// The public-input-bearing receipt as it appears today.
    pub receipt: TurnReceipt,
    /// The full Turn, including all execution_proof fields.
    pub turn: Turn,
    /// The aggregation proof's full public-inputs vector.
    /// For approach A: one PI vector per cell + an outer "agreement
    /// vector" capturing the shared (turn_hash, effects_global, ...).
    /// For approach B/C: one PI vector for the single proof.
    pub public_inputs: Vec<BabyBear>,
    /// The proof bytes — same as Turn.execution_proof but typed for
    /// the aggregation backend (A/B/C).
    pub proof_bytes: Vec<u8>,
    /// Per-cell private witnesses (rows × 105 columns each).
    /// One entry per touched cell. Optional: prover may keep this
    /// local and not ship it.
    pub vm_witnesses: Option<BTreeMap<CellId, EffectVmWitness>>,
    /// The aggregate-level witness for the fold/outer step (for
    /// approaches B/C). For A this is None.
    pub aggregate_witness: Option<AggregateWitness>,
    /// Authorization preimages: signatures, bearer-cap delegation
    /// chains, etc. — the private data that the executor checked
    /// out-of-band and would need to recheck.
    pub auth_witnesses: AuthorizationWitnesses,
}

pub struct EffectVmWitness {
    /// Full trace: rows × 105 BabyBear columns.
    pub trace: Vec<[BabyBear; 105]>,
    /// Pre-state of the cell (full CellState, not just commitment).
    pub pre_state: CellState,
    /// Post-state of the cell.
    pub post_state: CellState,
}
```

### 4.2 Storage strategy

Three options, mirroring the choices in `STAGE-7-PLUS-DESIGN.md §5.2`:

- **Local-only.** The prover keeps `WitnessedReceipt` on disk; the
  receipt-as-shipped contains only `TurnReceipt + proof_bytes +
  public_inputs`. Witnesses are producible on demand for audit.
  Cheapest; most-private. Vulnerable to prover data loss.
- **Encrypted to a recovery authority.** `vm_witnesses` and
  `aggregate_witness` are serialized, encrypted (Curve25519 XSalsa20
  AE, say) to the federation's recovery key, and shipped alongside
  the receipt. A new field `encrypted_witness_root: [u8; 32]` in
  `TurnReceipt` binds the ciphertext. The federation can decrypt to
  audit; outside parties cannot. **Default for Pyana.**
- **Split-key.** Same as encrypted, but the recovery key is sharded
  across federation members via Shamir; reconstruction requires
  threshold cooperation. Higher censorship-resistance.

A fourth option (public) is mentioned for completeness — public-witness
mode for audit-heavy apps that opt in via a per-cell flag.

### 4.3 Replay semantics

Given a `WitnessedReceipt` stream starting from genesis, an auditor:

1. Reconstructs each `Turn` from `receipt.turn`.
2. For each cell in `vm_witnesses`, *executes* the trace row-by-row:
   `state_after[i] = apply(state_before[i], row[i])` and verifies the
   final state matches `post_state.state_commitment()`.
3. Recomputes `effects_hash_local` over the trace's `VmEffect` rows
   and matches against the proof's PI.
4. For each pair of touched cells in a turn, runs the *cross-cell
   ledger*: the bilateral arithmetic that the AIR (under 7-γ) was
   supposed to enforce — `Transfer` pairs balance, `GrantCapability`
   pairs across c-lists, etc.
5. Re-proves the aggregate proof from the witness; under Plonky3's
   deterministic Fiat-Shamir, the regenerated proof bytes match
   `proof_bytes` exactly. (This is *the* test for "did the prover
   honestly run the prover".)
6. Walks `previous_receipt_hash` to confirm chain causality.

The "useful margin" from the Golden Vision becomes precise: **an
auditor in possession of `WitnessedReceipt[]` can detect any deviation
from the protocol that affects state, balances, or capability
provenance, by re-execution.** It does not detect authorization fraud
(P5 stays executor-trusted in 7-γ). It does not detect bridge
double-spend across federations (Stage 6). It detects everything else.

### 4.4 Relationship to `pyana_compress_history` IVC

`node/src/mcp.rs::tool_compress_history` (`node/src/mcp.rs:2250`)
runs an IVC over state roots derived from receipts — it produces a
proof attesting to a chain of state-root transitions, *without
witness data*. That tool is the chain-side complement of 7-γ: 7-γ
compresses *one turn's N proofs into one*, `pyana_compress_history`
compresses *N turn proofs into one chain proof*. The two compose to
Stage 7-ζ's IVC-over-receipt-chain story.

The key gap: today's `compress_history` cannot replay because the
witness was discarded. `WitnessedReceipt` repairs this.

---

## 5. Recommended path

**Recommendation: approach A (Bundle-with-shared-PI), staged.**

Reasons:
- Lowest engineering risk; no new primitives (the recursive verifier
  shell is already in `circuit/src/plonky3_verifier_air.rs`).
- Captures P1 (turn-identity) and P4 (program verification) cleanly.
- Captures P2 (projection totality) with one new constraint
  (Poseidon2-merge of per-cell `effects_local` into
  `effects_hash_global`).
- Captures P3 (bilateral agreement) with one *additional* small
  micro-AIR (the "aggregation micro-AIR" — see Stage 7-γ.2 below).
  This micro-AIR is the work-product that makes A *real* and not just
  a protocol-level hack.
- Composes naturally with 7-δ (`WitnessedReceipt`), which is the
  Golden-Vision-replay piece.
- Path to 7-ζ stays open: the bundle proof itself becomes an IVC step
  in the chain-level recursion.

Approach C (IVC fold) is the right *long-term* shape and we should plan
to migrate to it at 7-ζ. But the IVC scheme choice (Nova / Hyper-Nova /
Plonky3-native folding) is genuinely research-grade, and shipping A
first lets us *exercise* the cross-cell semantics in production before
committing to a folding scheme.

Approach B is the right *specification* of what aggregation should
mean. We should write a tiny outer-AIR sketch as a reference oracle
for the test suite (a 2-cell, 1-effect outer AIR that we manually
prove and use as a golden output), but not ship it as the artifact.

### Three-chunk roll-out

**Stage 7-γ.0 — Shared PI Bundle (smallest viable, ~1 week)**
- Land 7-α first (`Turn::hash` v3 covering all proof fields).
- Add to `EffectVmAir::pi`:
  - `TURN_HASH_BASE: usize = …` (4 felts, Poseidon2 of `Turn::hash`).
  - `EFFECTS_HASH_GLOBAL_BASE: usize = …` (4 felts).
  - `ACTOR_NONCE: usize = …` (1 felt; the outer `Turn::nonce` —
    this also closes W-1 from `STAGE-7-PLUS-DESIGN.md`).
  - `PREVIOUS_RECEIPT_HASH_BASE: usize = …` (4 felts).
- Modify `turn/src/executor.rs::convert_turn_effects_to_vm` to compute
  both `effects_local` (the current per-cell projection) and
  `effects_hash_global` (a single Poseidon2 over the whole call_forest's
  `Effect::hash()`-derived bytes, in canonical DFS order).
- In `verify_proof_carrying_turn`, add a PI-matching loop that
  requires all N per-cell proofs of the same turn to agree on the
  four new PI fields.
- Crate ownership: `pyana-circuit` (effect_vm PI extensions);
  `pyana-turn` (`convert_turn_effects_to_vm`, executor verify path).
- Tests: differential test that produces a turn where two per-cell
  proofs claim different `turn_hash` → rejected.

**Stage 7-γ.1 — Projection-totality constraint (medium, ~2 weeks)**
- New AIR in `circuit/src/turn_aggregation.rs` —
  `TurnAggregationAir` (the "aggregation micro-AIR"). Its trace has
  one row per touched cell. Each row consumes the per-cell proof's
  `effects_local[c]` (4 felts) as input. The AIR's final row's
  Poseidon2 accumulator must equal the `effects_hash_global` PI.
- Constraint: row-by-row Poseidon2 absorption of `effects_local[c]`
  in canonical-cell order; boundary constraint on the last row.
- The outer proof carries both the N inner proofs and this aggregation
  proof. Verifier runs N inner verifications, then one aggregation
  verification, then asserts the shared PIs.
- Crate ownership: `pyana-circuit::turn_aggregation`; `pyana-turn`
  prover-side glue.
- Tests: differential test where prover swaps `effects_local[bob]`
  contents between two `Transfer` proofs of different turns → the
  aggregation micro-AIR's Poseidon2 disagrees → rejected.

**Stage 7-γ.2 — Bilateral-arithmetic micro-AIR (medium-high, ~3 weeks)**
- Extend `TurnAggregationAir` with per-bilateral-effect-kind columns:
  - A `transfer_log_acc[4]` running Poseidon2 over `(direction, amount,
    peer)` triples.
  - A `grant_log_acc[4]` similarly.
  - An `intro_log_acc[4]` similarly.
- Each per-cell Effect VM proof exports (via PI) its contribution to
  each accumulator. The aggregation AIR asserts:
  - `transfer_log_acc` is balanced: the polynomial sum over
    `(+amount, peer=b)` from `a`'s side equals the sum over `(-amount,
    peer=a)` from `b`'s side. Concretely, each `Transfer(a, b, n)`
    contributes `+n` to one running sum and `-n` to another; the
    final sum must be zero. (Same accountant trick as the `net_delta`
    PI today, lifted to bilateral pairs.)
  - `intro_log_acc` matches across all three contributors (three
    rows in the aggregation trace must hash to the same final value).
- Crate ownership: `pyana-circuit::turn_aggregation`. This is the
  meat of "the algebra binds bilateral".
- Tests: adversarial — produce `Transfer(a, b, 100)` and `Transfer(a,
  b, 50)` proofs and try to bundle them as a single turn. The
  aggregation AIR's `transfer_log_acc` mismatch rejects.

After γ.0-γ.2, the executor's role in cross-cell binding is reduced
to: "produce the right `effects_hash_global` and PI-match the four
shared fields." Everything else is algebra.

### Companion: 7-δ (`WitnessedReceipt`) lands in parallel after γ.0

Pure engineering. Independent crate-slice (`pyana-turn` + `pyana-node`
for storage). Lands the replay piece. Crate ownership:
`pyana-turn::witnessed_receipt` (the struct, serialization); `pyana-
node` for the storage layer; `pyana-cipherclerk` / `pyana-sdk` for the
export interface; `pyana-storage` for the encrypted-witness blob
table.

---

## 6. What stays outside the proof system, deliberately

Even after 7-γ.0-γ.2 + 7-δ lands, the following remain executor-trusted
or wire-trusted by design:

- **Ed25519 / Schnorr signature verification.** The `Authorization`
  variant's actual signature check (`turn/src/action.rs::Authorization`,
  the executor's auth gate). 7-γ does not attempt this; Stage 9 brings
  in-circuit signature verification at the federation boundary where
  it matters. Within a federation, the executor's verify-once trust
  domain is acceptable.
- **Network-level censorship resistance.** The proof says nothing
  about which turns the federation chose to include in a block, or
  about ordering across turns within an epoch. That is the wire layer
  + consensus (`wire/`, `federation/`, `node/`).
- **BLS threshold consensus.** `FederationReceipt::ThresholdQC`
  (recent commit `47490eb0`) covers federation-level finality. The
  aggregate proof attests to *one* turn's execution; the QC attests
  to the federation's *acceptance* of that turn. These are different
  trust statements.
- **Federation snapshot consistency.** The `OLD_COMMIT[4]` PI for
  each per-cell proof comes from a federation-trusted snapshot of
  cell state. The proof attests "given this OLD, this NEW is
  derivable", not "this OLD is the authoritative cell state". The
  snapshot's authority is consensus-level.
- **Wire-level replay protection.** `Turn::depends_on` and
  `previous_receipt_hash` are checked by the executor. 7-γ.0 binds
  the *receipt hash* into PI but not the *causal ordering rules*
  themselves; those remain executor-trusted.
- **Bridge phase semantics.** `BridgeMint/Lock/Finalize/Cancel`
  cross-federation semantics live in Stage 6's bridge work
  (`bridge/`, `DESIGN-receipts.md` §5). 7-γ binds the per-cell
  effect-projection contribution of bridge effects, not the
  cross-federation phase machine.
- **Custom program (`CellProgram`) source-level correctness.** Each
  custom proof attests that *its* AIR was satisfied. Whether the AIR
  itself encodes the program's intent is the cell program author's
  responsibility, not the aggregation layer's.
- **Random-beacon usage.** Any effect that consumes randomness (the
  block height column `CURRENT_BLOCK_HEIGHT` is the only "randomness"
  the AIR sees; deeper randomness like VRF outputs is wire-trusted).

Listing these explicitly is part of the discipline: it lets us
*describe* the proof system's trust boundary as a small, growable set
of items, rather than as a vague "the executor is trusted."

---

## 7. Open questions for the architect

1. **Canonical effect ordering for `effects_hash_global`.** DFS over
   call_forest with cells in first-appearance order is the obvious
   choice. Alternative: lexicographic over `(cell_id, effect_idx)`.
   The former binds causal structure; the latter is invariant under
   forest reordering. Recommendation: DFS.
2. **Maximum touched cells per turn.** The aggregation micro-AIR has a
   per-row cost; bounding `MAX_TOUCHED_CELLS = 8` keeps the trace
   small. Real-world turns rarely touch more than 4. Cells beyond
   the bound require *chained* aggregation proofs (an outer fold
   over multiple bundles). Recommendation: 8 with explicit chaining
   above.
3. **Where does `aggregate_witness` live in `Turn`?** Today
   `Turn.execution_proof` is `Option<Vec<u8>>` opaque. Either keep
   it opaque and tag the bytes with a backend selector, or
   distinguish `execution_proof: PerCellProof[]` from
   `aggregation_proof: AggregationProof`. Recommendation: keep
   `execution_proof` as the aggregated bytes (post-γ.0+) and add a
   dedicated `aggregation_metadata` field for the
   per-cell-PI-vectors that the verifier needs.
4. **Encrypted-witness recovery vs. fully-local.** 7-δ default
   recommendation is encrypted-to-recovery; need a federation policy
   decision on key-rotation cadence.

---

## 8. Closing

Stage 7-γ is the proof-system response to a precise observation:
*Pyana's algebra speaks of cells, but its semantics speak of turns,
and the two languages have not been joined.* The cleanest, lowest-risk
join is approach A — shared-PI bundle plus a small aggregation
micro-AIR that captures projection totality (P2) and bilateral
agreement (P3). It composes naturally with `WitnessedReceipt` (7-δ)
to deliver the Golden Vision's "receipts + witness ⇒ replayable
protocol" promise within the cross-cell scope of a single turn, and
it leaves the door open to 7-ζ (IVC across the receipt chain) without
locking in a folding scheme today.

The smallest first chunk that delivers a useful artifact: **7-γ.0,
the shared-PI bundle.** After it lands, the executor's role in
cross-cell binding is *reduced but not eliminated* — that reduction
is the algebraic progress, and γ.1 + γ.2 finish the job.

The recursion that makes the Golden Vision true at chain scale is
7-ζ. The recursion that makes it true at turn scale is 7-γ. They are
the same idea applied at two scales, and once 7-γ exists, 7-ζ is a
matter of picking a folding scheme and wiring it through; until 7-γ
exists, 7-ζ has nothing to fold.
