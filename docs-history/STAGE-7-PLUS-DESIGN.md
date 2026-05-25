# Stage 7+ — From Per-Cell AIR to Whole-Turn Algebraic Attestation

**Status:** design exploration. No code changes. Companion to `EFFECT-VM-SHAPE-A.md`
(which goes through Stage 12 of *per-cell* coverage) and `REVIEW-effect-vm.md`
(which lays out the per-cell soundness ledger). This document picks up where
those stop and asks: *what would it take for the algebraic proof to fully
constrain a turn, not just a cell-slice of a turn?*

The "Golden Vision" framing (verbatim from the design brief): the algebraic
proof fully constrains ALL operations and attests to ALL capability
operations and supports ALL cap, turn, etc operations; receipt chains
should be sufficient to replay the protocol (with also the private
inputs/witness data) to within a margin that is useful for constraining
behavior in the future.

The current Effect VM proves a single-cell, single-turn property, with the
soundness gaps catalogued in `REVIEW-effect-vm.md`. Stage 3 (commits
`ec9b2469..f2b84cb7`, follow-up `1c3f648c..cea77c6c`) closed the projection
side: all 41 runtime `Effect` variants now have a real AIR variant on the
proven-cell projection. That is real progress, but it is per-cell progress.
The cross-cell composition, the cross-turn composition, and the
cross-layer (AIR + signature + threshold + storage) composition are the
work ahead of us.

---

## 1. The current trust boundary, precisely

Three layers are involved when a sovereign cell takes a turn today:

```
                       +-----------------------------------+
   wallet / DSL  --->  | Turn (turn::turn::Turn)           |
                       |  agent, nonce, call_forest,       |
                       |  previous_receipt_hash,           |
                       |  execution_proof: Option<Vec<u8>> |
                       |  execution_proof_new_commitment   |
                       |  custom_program_proofs            |
                       +-----------------------------------+
                                       |
                                       v
                       +-----------------------------------+
   executor       <--- | Authorization gate                |
                       |  cell.permissions vs              |
                       |  Authorization variant            |
                       |  (Signature / Proof / Bearer /    |
                       |   Breadstuff / Unchecked)         |
                       +-----------------------------------+
                                       |
                                       v
            +----------+   +-------------------------+   +-----------------+
   AIR  <-- | Effect   |   | convert_turn_effects    |   | EffectVmAir     |
            | runtime  |-->| _to_vm  (per cell)      |-->| 46-selector    |
            | enum     |   | turn/src/executor.rs    |   | trace + PIs     |
            | (41)     |   |   :1488                 |   | circuit/.../ |
            +----------+   +-------------------------+   |   effect_vm.rs  |
                                                         +-----------------+
```

**The per-cell AIR's domain.** The Effect VM AIR
(`circuit/src/effect_vm.rs:109..3500`) is parameterised by:

- One *target cell* (call it `cell_id`).
- The cell's old and new wide `state_commitment` (4 BabyBear felts each, since
  Stage 1 widened the PI; `pi::OLD_COMMIT_BASE..+4` and
  `pi::NEW_COMMIT_BASE..+4` at `effect_vm.rs:500..508`).
- A 4-felt `effects_hash` over the sequence of `VmEffect` rows for `cell_id`
  (`pi::EFFECTS_HASH_BASE..+4`, `effect_vm.rs:507..521`; the synthetic-hi hack
  is dropped — the four felts are real Poseidon2 output).
- A signed `(net_delta_mag, net_delta_sign)` pair against `cell_id`'s balance
  columns (`pi::NET_DELTA_MAG`, `pi::NET_DELTA_SIGN`).
- `CURRENT_BLOCK_HEIGHT` (used by escrow timeout witnesses).
- `MAX_CUSTOM_EFFECTS` and `CUSTOM_EFFECT_COUNT` — the count of `Custom`
  rows, sum-checked against the selector trace
  (`effect_vm.rs:3195..3325`).
- `APPROVED_HANDOFFS_BASE..+4` — the federation's approved-handoffs Merkle
  root, used by `ValidateHandoff`.

The trace is `EFFECT_VM_WIDTH = 105` columns wide, one row per `VmEffect`,
padded with `NoOp`. The 46 selectors gate all per-variant constraints
(`effect_vm.rs:109,112,1200..2900`).

**What the proof attests.** Exactly the following statement:

> Given the public inputs above, there exists a sequence of `VmEffect`s whose
> selectors are gated by the trace's selector columns, whose state-after of
> each row equals the state-before of the next, whose final `state_commitment`
> equals `NEW_COMMIT`, whose first equals `OLD_COMMIT`, whose
> Poseidon2-accumulated effects-hash equals `EFFECTS_HASH`, whose balance
> column transitions sum (signed) to `(NET_DELTA_MAG, NET_DELTA_SIGN)`, and
> whose count of `s_custom = 1` rows equals `CUSTOM_EFFECT_COUNT`.

That is a per-cell statement. The rest of the turn — every other cell it
touched, the cross-cell agreement, the signature on the turn body, the
`Turn::hash`, the receipt-chain back-pointer — sits *outside* the AIR.

**What lives in the executor.** Everything else, in particular:

- The `Authorization` check against `cell.permissions` lives in
  `turn/src/executor.rs`. The AIR has no view of authority.
- The `Turn::nonce` bump is enforced by the executor's nonce check on the
  *next* turn (`Turn::nonce` vs `cell.state.nonce`). The AIR's trace
  internally increments `state.nonce` per row, but the *Turn-level nonce*
  is not in PI at all — a turn that wrote the wrong nonce into a successor
  receipt could pass the AIR even though the receipt chain would lie.
  **This is the surprising soundness finding** from differential tests:
  per-cell AIR cannot see the actor's outer nonce; executor sees it; no
  proof binds the two views.
- `previous_receipt_hash` is enforced executor-side and folded into
  `Turn::hash`, but `Turn::hash` itself (v2 tag at `turn::turn::144`) does
  *not* cover `execution_proof` / `execution_proof_new_commitment` /
  `custom_program_proofs`. R-2 in `EFFECT-VM-SHAPE-A.md`: proof-swap
  attack until Stage 9.
- `CellState.capabilities` is consulted by the executor for
  `ExerciseViaCapability`, but the AIR's `cap_root` is a one-felt
  hash chain — it does **not** prove membership of the exercised slot.
  The AIR row is passthrough binding `(cap_slot, inner_effect_hashes)`
  into `effects_hash`, trusting executor for membership
  (`turn/src/executor.rs:2025..2039`).
- Bearer-cap signature verification is fully executor-side. The AIR
  sees neither the signature, nor delegator's pubkey, nor bearer's pubkey.

---

## 2. What "proving a whole turn" would mean

A turn touches multiple cells. The current AIR proves *one cell's slice* of
that turn. The Golden Vision asks for a single mathematical statement:

> *This turn, with this call_forest, transitioned the federation's set of
> touched cells from `S_pre` to `S_post`, with these effects, satisfying
> these conservation laws, and the receipts emitted are mutually consistent
> with that transition.*

There are four ways to get there. They are not exclusive.

### 2a. Aggregation: bundle N per-cell proofs

Prove each cell's slice independently (the existing AIR), then bundle.
Shared public inputs across the per-cell proofs:

- `turn_hash` (v3 — covering all execution-proof fields)
- `effects_hash_global` — a Poseidon2 over the *whole* turn's effect
  sequence, not the cell-projected subset.
- `previous_receipt_hash`
- `nonce`

Each per-cell proof additionally has a *local* `effects_hash_local` (its
projection). The aggregation proof attests:

```
   for each cell c in touched(turn):
     verify(per_cell_proof[c], PI = { OLD[c], NEW[c], effects_local[c], ... })
   AND  Poseidon2-merge(effects_local[c] for c in touched) == effects_hash_global
   AND  net_delta sum across cells == 0   (turn-level conservation)
   AND  effects_hash_global == Poseidon2(call_forest)   (binds to Turn::hash)
```

Trade-offs:
- **Prover time**: linear in cells; each per-cell proof is unchanged.
- **Proof size**: one outer recursive proof + N inner proofs, or fold via IVC
  → constant inner.
- **Composability**: clean. The verifier composes per-cell verifiers it
  already runs, plus a small recursive AIR.
- **What's provable**: cross-cell conservation; that all cell projections
  share a common turn-hash; that custom-effect count globally bounds.
- **What's NOT provable**: cross-cell ordering. The per-cell traces are
  unordered relative to each other except via the `effects_hash_global`
  Poseidon2 (which fixes order) and via the call_forest.

### 2b. Single outer AIR over the whole turn

One trace, many cells. Each row carries a `cell_id` selector. State columns
become a structured array indexed by cell. The constraint system gates
balance arithmetic per cell, and conservation is a row-by-row invariant:
the sum of balance deltas across all active-cell rows in the same "logical
moment" is zero.

Trade-offs:
- **Prover time**: dominated by a much larger trace.
- **Proof size**: one proof.
- **Composability**: poor — every new cell touched grows the AIR's shape;
  bad for sparse turns.
- **What's provable**: full turn-level semantics in one statement.
- **Reality check**: not viable for turns that touch >10 cells. Better as
  *the model* for what aggregation should produce, not as the actual
  artifact.

### 2c. IVC over the call_forest tree

The call_forest is a tree of `Action` nodes. Fold it bottom-up:
each leaf produces a "leaf claim" (per-cell effect-list contribution), and
each internal node produces a "subtree claim" by combining its children's
claims with the parent action's effects. The IVC step is the same AIR
applied recursively.

Trade-offs:
- **Prover time**: O(forest size) but well-batched; each step is small.
- **Proof size**: constant.
- **Composability**: this is the cleanest match to the call_forest shape.
  It also gives a natural place to enforce ordering: the IVC step sees
  parent-before-children causality structurally.
- **What's NOT provable today**: this needs an IVC scheme. Plonky3 doesn't
  give it for free; we'd need a Nova-style folding scheme or
  proof-of-proofs recursion. This is **research-grade** work.

### 2d. Hybrid: aggregation in space, IVC in time

For a single turn: aggregation over cells (2a). For the receipt chain across
turns: IVC over receipts. Each turn's aggregation proof becomes the
"witness" of an IVC step whose state is `(federation_state_root,
receipt_chain_tail_hash, accumulated_audit_log_root)`. This is the
practical shape of a system that wants "a proof carrying the whole history
forward."

---

## 3. How turns differ from cells (and why this matters)

The cell vs. turn distinction is the load-bearing structural mismatch.

| | **Cell** | **Turn** |
|---|---|---|
| Persistence | Long-lived; has identity (`CellId`), permissions, balance, nonce, capability table | Ephemeral; one act of execution |
| State | `CellState` | None of its own; it *causes* state changes in cells |
| Identity | `CellId = [u8;32]` | `Turn::hash()` (v2, see `turn::turn::144`); R-2 means not yet covering all proof fields |
| Receipt scope | The receipt chain is *per-cell* (`previous_receipt_hash` links a cell's successive receipts) | The receipt is *per-turn-per-cell*; a turn touching 3 cells produces routing directives/exports for each but a single `TurnReceipt` |
| AIR coverage today | One AIR proves one cell's slice of one turn | No turn-level AIR |
| Capability check | Cell holds the cap table; executor checks pre-state membership | Turn exercises caps; AIR sees only `cap_root` chain updates, not membership |
| Authority | `Permissions` decides what auth modes are admissible | `Authorization` variant is per turn (signed by agent, or proof, or bearer, etc.) |

**The crucial asymmetry:** receipts are per-cell-per-turn, but the
`call_forest` is a per-turn tree spanning cells. There is no single
"this turn happened" cryptographic statement we can hand a verifier today.
What we have is N receipts (one per touched cell), each chained to its
predecessor *in that cell*, plus the turn-level `Turn::hash` which is the
hash of the call_forest and metadata.

The minimum bridge we need is a **turn-level commitment that is reachable
from each touched cell's receipt**. That's the cross-cell join that's
missing today.

---

## 4. Cell interactions — what's algebraic, what isn't

Walking concrete `Effect` variants and asking: what does the AIR prove
today, what's executor-trusted, what's missing for cross-cell binding?

### 4.1 `Transfer { from, to, amount }` (single-effect bilateral)

- **AIR today:** Projected against `from`, `VmEffect::Transfer
  { direction: 1, amount }` → `bal_lo -= amount`. Against `to`,
  `direction: 0` → `bal_lo += amount`. Independent proofs, 30-bit `amount`
  in `bal_lo`; `bal_hi` unchanged (P1-18 in `REVIEW-effect-vm.md`).
- **Executor today:** Conservation at call_forest level via
  `compute_balance_delta_from_effects`, which backs the AIR's `net_delta`
  PI.
- **Gap:** no algebraic statement that `from`'s outflow equals `to`'s
  inflow — two independent statements about two columns. A prover
  controlling both sides could produce mismatched proofs; the executor
  catches it only because it sees both sides of the original `Effect`.
- **Witness data:** Add a shared PI `transfer_log_root` accumulating all
  `Transfer` effects in the turn; each per-cell proof binds its
  contribution into the same root. Natural Stage 7 add.

### 4.2 `GrantCapability { from, to, cap }` (asymmetric bilateral)

- **AIR today:** Against `to`, `GrantCapability` folds `cap_entry` into
  `cap_root` via hash chain (`executor.rs:1542..1547`). Against `from`,
  nothing is emitted — the grantor's c-list change isn't modeled.
- **Executor today:** verifies grantor had the cap, applies `to`-side
  cap-root update, emits `DerivationRecord`.
- **Gap:** AIR doesn't bind grantor's authority (membership in `from`'s
  c-list) to recipient's c-list growth. The `DerivationRecord` in the
  receipt is a plaintext join, not algebraic.
- **What would close it:** grantor's per-cell proof emits an
  "authorized grant" row binding `(from, to, cap_entry,
  delegation_cert_hash)`; recipient's proof binds the same tuple;
  aggregation AIR checks equality. Plus grantor-side AIR-level c-list
  membership (needs committed cap-table).

### 4.3 `Effect::Introduce { introducer, recipient, target, permissions }`

- **Today, AIR:** projection against any of three parties produces
  passthrough `VmEffect::Introduce { intro_hash }` over `(introducer,
  recipient, target, permissions)` (`executor.rs:1918..1939`). Recipient's
  cap-list growth isn't modeled at AIR level — handled by `ExportGcManager`.
- **Gap:** three independent projections, three `intro_hash` values that
  *happen* to be equal because inputs are the same, but no AIR constraint
  forces equality. Aggregation step would assert all three contributions
  share the same `intro_hash` and that recipient's `cap_root` grew by one
  entry derived from it.
- **Witness data:** `permissions` is a 1-byte selector; the full
  `AuthRequired` semantics (allowed_effects, facet) are off-AIR. For
  replay we'd widen the permissions field.

### 4.4 `ExerciseViaCapability { cap_slot, inner_effects }`

- **Today:** passthrough binding `(cap_slot, inner_effect_hashes)` into
  `effects_hash`. AIR does *not* prove `cap_slot ∈ pre-state c-list`.
  Inner effects are recursively expanded by the executor.
- **Gap:** membership purely executor-side. `cap_root` is a hash chain
  of grants/revokes — no way to prove "slot N is present" from it.
- **What would close it:** committed cap-table Merkle structure (per
  `DESIGN-captp-integration.md`: `swiss_table_root`, `refcount_table_root`)
  + in-AIR Merkle membership proof for `ExerciseViaCapability`.
  Stage 7 in `EFFECT-VM-SHAPE-A.md`.

### 4.5 Bearer-cap exercise (`Authorization::Bearer(BearerCapProof)`)

- **Today:** signature verified by the executor's auth gate. AIR has *no
  view* of signature or delegation chain.
- **Gap:** *everything* — signature, delegator pk, bearer pk,
  delegation_proof, expiry, revocation_channel.
- **What would close it:** SignatureGadgetAir composed alongside Effect VM
  AIR, with shared PIs `(delegator_pk, bearer_pk, expiry, msg_hash)` and
  constraint `msg_hash == Turn::hash()`. Composed-AIR work, well-trodden.
- **Open call:** within a federation the executor is trusted to verify
  Ed25519. Signature-in-circuit only matters at the bridge boundary —
  Stage 9 concern, not Stage 7.

### 4.6 Summary: cross-cell binding catalog

| Effect | Today's binding | Gap | Stage |
|---|---|---|---|
| `Transfer` | per-cell `net_delta`; executor sums | transfer_log_root + AIR contribution | 7 |
| `GrantCapability` | per-cell `cap_root` update on `to` | grantor-side membership + bilateral binding | 7 |
| `Introduce` | per-side `intro_hash` (equal by computation, not by constraint) | aggregation equality constraint | 7 |
| `ExerciseViaCapability` | passthrough + executor c-list check | committed cap_root + Merkle membership | 7 |
| `RevokeCapability` | per-cell `cap_root` update | bound to executor's c-list removal | 7 |
| `Bearer` (auth) | executor signature check | optional: signature-in-circuit at fed boundary | 9 |
| `BridgeMint/Lock/Finalize/Cancel` | per-cell balance + `*_hash` | full bridge phase semantics | 6 (already planned) |
| `Seal/Unseal` | tautological at AIR; mask not in state tree | real sealed-mask column + tree inclusion | 2 (already planned) |

---

## 5. Receipt chain as replayable witness

The brief specifically says the receipt chain must support replay
*with also the private inputs/witness data*. Today's `TurnReceipt`
(`turn/src/turn.rs:263`) carries:

- Public `turn_hash`, `pre_state_hash`, `post_state_hash`, `effects_hash`.
- A `previous_receipt_hash`.
- Federation ID, derivation records, emitted events, executor signature.
- *No proof*, *no PIs explicitly* (they're reconstructed), *no witness*.

The `execution_proof` itself lives on `Turn`, not `TurnReceipt`. The
receipt records that a turn happened; the turn carries the proof.

**For replay-with-witness, two things need to change.**

### 5.1 `WitnessedReceipt`: witness + proof packaged with the receipt

```rust
/// A receipt paired with the data required to *re-derive* its proof.
/// The witness is the private input; the receipt is the public input
/// summary; together they let an auditor regenerate the proof and
/// confirm the prover's claim by recomputation, not just by
/// verifier-acceptance.
pub struct WitnessedReceipt {
    pub receipt: TurnReceipt,
    /// The full turn, including execution_proof, execution_proof_*,
    /// custom_program_proofs.
    pub turn: Turn,
    /// The Effect VM's *witness columns* for this turn. One per touched
    /// cell. Witness includes the full trace (all 105 columns × all
    /// rows including the padding `NoOp`s) and the cell pre-state.
    pub vm_witnesses: BTreeMap<CellId, EffectVmWitness>,
    /// Authorization-side private data: signature + delegation chain
    /// preimages for Bearer caps; the proof inputs for Proof auth.
    pub auth_witnesses: AuthorizationWitnesses,
    /// Witnesses for any custom program proofs (the prover-side data
    /// the CellProgram's AIR consumed).
    pub custom_witnesses: Vec<CustomProgramWitness>,
}

pub struct EffectVmWitness {
    /// Full trace, row-by-row, 105 columns.
    pub trace: Vec<[BabyBear; 105]>,
    /// The cell's full pre-state (not just commitment) — necessary to
    /// re-derive the commitment.
    pub pre_state: CellState,
    /// The cell's post-state.
    pub post_state: CellState,
    /// The PI vector at proof time.
    pub public_inputs: Vec<BabyBear>,
}
```

### 5.2 Where the witness lives

Three options:

- **Prover keeps it.** Cheapest. The receipt is verifier-sufficient; the
  witness is for *the prover's* records and is only producible by them on
  demand. Downside: the prover can lose it.
- **Encrypted to a recovery authority.** Each
  `WitnessedReceipt.vm_witnesses[cell]` is encrypted to a federation's
  recovery key. The prover commits to the ciphertext hash in the receipt
  (a new field). The federation can decrypt to audit; outside parties
  cannot. This is a privacy-friendly variant.
- **Public.** Some applications (audit-heavy, public-by-design) just
  publish the witness alongside the receipt. Then anyone can replay.

For Pyana's positioning, **option 2** is the natural default: the
federation's recovery authority can decrypt to settle disputes; normal
verifiers run only the receipt-level check.

### 5.3 Replay semantics

"Replay" here means: given a stream of `WitnessedReceipt`s starting from
genesis (or a checkpoint), an auditor can:

1. Reconstruct each `Turn` and its `vm_witnesses`.
2. Re-derive `pre_state → post_state` by applying the witnessed trace to
   the cells (no STARK verification required — direct execution).
3. Confirm the witnessed trace is consistent with the receipt's
   `pre_state_hash` and `post_state_hash`.
4. *Independently re-prove* if desired, and confirm the regenerated proof
   matches the stored `execution_proof` byte-for-byte (Plonky3 is
   deterministic given the same trace + Fiat-Shamir transcript).
5. Walk the `previous_receipt_hash` chain to confirm causal continuity.

The "margin that is useful for constraining behavior in the future" then
becomes: anyone holding the witnesses can dispute by *showing the trace
that contradicts a later receipt's claim about the pre-state*. That's the
useful constraint.

---

## 6. The honest gap, categorised

### 6.1 Within-cell tightening (per-cell AIR shape unchanged)

- **W-1.** Outer `Turn::nonce` in PI, algebraic bump.
- **W-2.** Sealed-field mask in state-commitment tree (review P0-3).
- **W-3.** `Seal/Unseal` actually update the mask (Stage 2).
- **W-4.** Real FIFO `DequeueMessage` (head/tail, Stage 2).
- **W-5.** Real Merkle membership for `ValidateHandoff`, `EnlivenRef`
  (Stage 2 + Stage 7 to populate roots).
- **W-6.** `Transfer` widened to full u64 with carry (P1-18; Stage 2).
- **W-7.** AIR-side c-list membership for `ExerciseViaCapability`
  (needs committed `cap_table_root`).

### 6.2 Cross-cell binding (single turn) — new composition layer

- **X-1.** Bilateral `Transfer` via shared `transfer_log_root`.
- **X-2.** Bilateral `Grant`/`Introduce`/`Revoke` binding.
- **X-3.** Turn-level conservation: `Σ per-cell net_delta == fee`.
- **X-4.** `Turn::hash` v3 covers `execution_proof*` (R-2, Stage 9).

### 6.3 Cross-turn composition

- **T-1.** Receipt chain as a cryptographic structure (IVC over receipts),
  not just a hash chain.
- **T-2.** `WitnessedReceipt` packaging (§5) — engineering.
- **T-3.** Nonce monotonicity proved across the chain.

### 6.4 Cross-layer (AIR + sig + threshold + storage)

- **L-1.** Real BLS aggregation for federation receipts
  (`DESIGN-receipts.md` §8, Stage 9).
- **L-2.** Bridge receipts in phase-locked AIR (Stage 6).
- **L-3.** Signature-in-circuit only at fed/bridge boundary.
- **L-4.** All committed roots (`swiss_table_root`, `refcount_table_root`,
  `approved_handoffs_root`, `cap_table_root`, `escrow_root`,
  `bridge_state_root`) inside the federation snapshot; each per-cell proof
  binds to the same snapshot.

### 6.5 New primitives we don't have

- **N-1.** Aggregation AIR (N inner proofs → 1 outer). Plonky3 supports
  recursion in principle; we have none today.
- **N-2.** IVC scheme (Nova-style folding or proof-of-proofs). Research.
- **N-3.** In-circuit Ed25519/Schnorr signature gadget. Engineering.
- **N-4.** Committed Merkle structures for cap-table (today: HashMap),
  design in `DESIGN-captp-integration.md`. Engineering.

---

## 7. A staged path that doesn't rebuild the world

Order matters. The smallest set of changes that *closes the most gap*:

### Stage 7-α — Turn-level cryptographic identity (must come first)

**Subsumes:** Stage 9's `Turn::hash` v3 bump (R-2). **Requires no new
primitives.** This is engineering.

- Bump `Turn::hash` to v3, covering all execution-proof fields, the new
  commitment, and the custom-program-proof binding.
- Add a turn-level `effects_hash_global` field, computed as Poseidon2
  over the full call_forest's effects (not per-cell).
- Each per-cell proof's `effects_hash` PI is constrained — *executor-side
  for now* — to equal `Poseidon2(cell_projection_of(effects_hash_global))`.

This gives us a well-defined object to aggregate over. Without this, every
later stage builds on quicksand.

### Stage 7-β — Outer nonce and turn-level conservation in PI

**Subsumes:** part of W-1 and X-3. **Engineering.**

- Add to Effect VM PI: `actor_nonce_pre`, `actor_nonce_post`. AIR
  constrains `nonce_post = nonce_pre + 1` on the agent-side row only.
- The executor commits the actor's outer-nonce values into the PI when
  building the proof; the receipt records them. A turn that writes the
  wrong nonce now fails the AIR check, not just the executor check.
- Turn-level conservation: the *executor* checks that
  `sum(per_cell.net_delta) == fee` for the touched cells in the turn.
  Algebraic binding waits for Stage 7-γ.

### Stage 7-γ — Aggregation AIR (the recursion step)

**Subsumes:** X-1, X-2, X-3. **Requires N-1 (aggregation AIR primitive).**
**Hybrid engineering + research.**

- A new AIR (`circuit/src/turn_aggregation.rs`) that:
  - Verifies N inner Effect VM proofs (recursive verification).
  - Constrains shared PIs across them: `turn_hash`, `effects_hash_global`,
    `previous_receipt_hash`, `actor_nonce`, `fee`.
  - Asserts `sum(net_delta) == fee` algebraically across cells.
  - Asserts cross-cell bindings: for each bilateral `Effect`, both sides
    contribute the same bilateral_hash.
- This is a real research milestone; the AIR verifier itself needs to
  fit in BabyBear. Plonky3 has a recursive flavour we can leverage but
  it isn't drop-in. Plan ~3 weeks plus a research review.

### Stage 7-δ — `WitnessedReceipt` packaging

**Subsumes:** T-2. **Pure engineering.**

- Define the struct (§5.1).
- Plumb the witness trace through the executor and prover.
- Add an optional `--export-witness` mode to the wallet/executor.
- Define the encrypted-to-recovery variant in
  `DESIGN-receipts.md` follow-up; not required for Stage 7.

### Stage 7-ε — Committed cap-table root

**Subsumes:** W-7, part of Stage 7 from `EFFECT-VM-SHAPE-A.md`. **Engineering.**

- Move `CellState.capabilities` from HashMap to a Merkle-committed
  structure. The root is `cap_table_root`, added to `CellState`.
- `ExerciseViaCapability` AIR row carries a Merkle path proving
  `cap_slot ∈ cap_table_root@pre_state`.

This is a prerequisite for any honest "the actor held the cap" claim. It
is independent of aggregation and can land in parallel with 7-γ.

### Stage 7-ζ — IVC over the receipt chain (deferred)

**Subsumes:** T-1, T-3. **Research-grade.**

- Pick an IVC scheme (Nova, ProtoStar, HyperNova, or in-house folding).
- Aggregation proof becomes the IVC step's "witness". State carried
  forward: `(federation_state_root, receipt_chain_tail_hash)`.
- Defer until 7-α through 7-ε are landed; this is the multi-month payoff.

### Ordering rationale

```
   7-α  (engineering, mandatory)
     |
     +--> 7-β  (engineering)
     |     |
     |     +--> 7-γ  (research + engineering, recursion)
     |
     +--> 7-δ  (engineering, parallel)
     |
     +--> 7-ε  (engineering, parallel)
                          |
                          v
                       7-ζ  (deferred research)
```

7-α is the keystone. Everything else builds on `Turn::hash` v3 plus the
global `effects_hash`. 7-β and 7-ε can run in parallel after 7-α. 7-γ is
the big-ticket item; 7-δ unlocks replay independently. 7-ζ is the
post-Stage-12 cherry.

### Subsumes/requires summary vs `EFFECT-VM-SHAPE-A.md`

| Stage in this doc | Subsumes from EFFECT-VM-SHAPE-A | New work |
|---|---|---|
| 7-α | Stage 9 (R-2 `Turn::hash` v3) | global `effects_hash`; per-cell binding |
| 7-β | part of Stage 2 (W-1 outer nonce) | turn-level conservation PI |
| 7-γ | none — entirely new | aggregation AIR (N-1) |
| 7-δ | none — entirely new | `WitnessedReceipt` packaging |
| 7-ε | Stage 7 CapTP from EFFECT-VM-SHAPE-A | committed cap-table root |
| 7-ζ | none | IVC scheme (N-2) |

Note that Stages 4 (`ExerciseViaCapability` AIR), 5 (escrow), 6 (bridge),
8 (DSL), 10 (storage Poseidon2) from `EFFECT-VM-SHAPE-A.md` are
*independent* per-cell tightening that does not get subsumed by Stage 7.
They should run in parallel.

---

## 8. ASCII diagram: how the proofs compose under Stage 7-γ

```
                        +---------------------------+
                        |  Turn (v3 hash)           |
                        |   - call_forest           |
                        |   - effects_hash_global   |
                        |   - previous_receipt_hash |
                        |   - execution_proof:      |
                        |     AggregationProof      |
                        +-------------+-------------+
                                      |
                +---------------------+----------------------+
                |                     |                      |
                v                     v                      v
        +---------------+     +---------------+      +---------------+
        | Cell A proof  |     | Cell B proof  |      | Cell C proof  |
        | (Effect VM    |     | (Effect VM    |      | (Effect VM    |
        |  AIR)         |     |  AIR)         |      |  AIR)         |
        | PI: OLD/NEW   |     | PI: OLD/NEW   |      | PI: OLD/NEW   |
        |   effects_loc |     |   effects_loc |      |   effects_loc |
        |   net_delta   |     |   net_delta   |      |   net_delta   |
        +-------+-------+     +-------+-------+      +-------+-------+
                |                     |                      |
                +----------+----------+--------+-------------+
                           |                   |
                           v                   v
                +--------------------+   +-------------------+
                | Aggregation AIR    |   | Per-cell receipts |
                |  verifies N inner  |   |  share turn_hash, |
                |  proofs; constrains|   |  effects_global,  |
                |   effects_loc[c] = |   |  agent_nonce      |
                |   project(global,c)|   +-------------------+
                |   sum(delta) = fee |
                |   shared turn_hash |
                +--------------------+
                           |
                           v
                +--------------------+
                |  AggregationProof  |
                |  PI: turn_hash,    |
                |  effects_global,   |
                |  fee, agent_nonce, |
                |  previous_receipt  |
                +--------------------+
                           |
                           v
                  signed TurnReceipt
                  (with optional
                   WitnessedReceipt
                   companion)
```

The outer `AggregationProof` is one proof; the inner N are unchanged
Effect VM proofs. The verifier runs the recursive verifier once and is
done. The optional `WitnessedReceipt` lets auditors replay.

---

## 9. Out of scope

Cross-federation aggregation (handled by Stage 6 bridge work); DSL-level
invariants (separate); receipt indexing/querying (off-chain, observability
crate); custom-program-proof composition (already exists per-cell via
`custom_program_proofs: Vec<…>` on `Turn`, unaffected by aggregation).

---

## 10. Open design questions for the architect

1. **Encrypted vs plaintext witnesses.** Default encrypted-to-recovery
   (§5.2 option 2), `--public-witness` opt-in for audit-heavy apps?
2. **IVC choice for 7-ζ.** Nova folding (trace-level), HyperNova (AIR-
   shape), or Plonky3-native recursive verifier? Instinct: Plonky3-native
   recursive verifier for 7-γ now; revisit IVC at 7-ζ.
3. **Aggregation granularity.** Fix N (e.g., 4 or 8) and chain for larger
   turns, or variadic with padding? Instinct: fix small N — most real
   turns touch ≤4 cells.
4. **`cap_table_root` migration cost.** Migrate HashMap→Merkle now while
   small, or after first deployment? Recommendation: now.
5. **`Turn::hash` v3.** Coordinated landing across `wallet/`, `sdk/`,
   executor, `protocol-tests/` (R-1 pain redux).

---

## 11. Closing

The Effect VM today is a per-cell, single-turn statement; Stage 3 finally
covered every runtime variant. The *architecture* is fine; the *scope*
is too narrow for the Golden Vision. The path forward is recursion +
aggregation, anchored by a turn-level hash that covers what it claims to,
a committed cap-list, and `WitnessedReceipt` packaging. Most is
engineering on a sound design; IVC (7-ζ) is the one genuine research bet.
The smallest start that most closes the gap: **7-α + 7-β**. Until 7-α
lands, everything downstream is provisional.
