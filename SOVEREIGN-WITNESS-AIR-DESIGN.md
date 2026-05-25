# Sovereign-witness AIR teeth — implementation design

**Date:** 2026-05-24. **Status:** design only; no implementation in this
lane. **Companion audits:** `AUDIT-sovereign-witness-teeth.md` (the
diagnosis), `EXECUTOR-HONESTY-AUDIT.md` T9 (the threat statement),
`BOUNDARIES.md` §2.6, §3.2, §7.2 (the boundary contract), the soundness
sweep's witness-shape work (`turn/src/turn.rs::SovereignCellWitness`),
Lane Golden-Edge's recursive verifier (target dependency for Phase 2).

## 1. What this doc proposes

`AUDIT-sovereign-witness-teeth.md` §8 establishes that sovereign
witnesses are not algebraically constraining today: there are no
sovereign-witness columns, no sovereign-witness PI slots, no AIR
constraints gated on the witness. The witness is a federation-side
bookkeeping handshake whose only binding is the pre-image relation
between `witness.cell_state.state_commitment()` and the federation's
stored commitment.

This document describes how to **give the witness algebraic teeth** in
two phases:

- **Phase 1 (minimal teeth).** Add a witness column to the Effect VM
  AIR + a boundary constraint that the in-trace witness signing key
  matches the cell's owning key. Closes the "any-snooper-can-resubmit"
  surface from `AUDIT-sovereign-witness-teeth.md §2.2`.
- **Phase 2 (STARK-attested teeth).** When the soundness sweep's
  `transition_proof: Option<Vec<u8>>` (the peer-exchange-style optional
  STARK on a `SovereignCellWitness`) is present, the AIR recurses into
  verification via Lane Golden-Edge's recursive verifier. Closes the
  "executor decides the post-state for the agent" surface from
  `AUDIT-sovereign-witness-teeth.md §8` and replaces the witness-vs-
  proof-carrying fork (today mutually exclusive) with a layered
  spectrum.

Phase 1 is implementable today against the existing Effect VM AIR.
Phase 2 depends on the recursive verifier being callable inside an
AIR; that capability is Lane Golden-Edge's deliverable. This doc
specifies the column/constraint surface so both phases can be
landed independently and so the migration story (§4) is concrete
before either implementation begins.

## 2. The soundness sweep's witness shape

The witness today (`turn/src/turn.rs:22-30`) is a pre-image opener:

```rust
pub struct SovereignCellWitness {
    pub cell_state: Cell,
    pub state_proof: [u8; 32],   // = cell_state.state_commitment()
}
```

The soundness sweep's in-flight extension (per task framing) gives
the witness a real signature shape:

```rust
pub struct SovereignCellWitness {
    pub cell_state: Cell,
    pub state_proof: [u8; 32],
    /// Ed25519 signature by the cell's signing key over a domain-tagged
    /// commitment to (state_commitment, sequence, optional STARK PI).
    pub signature: [u8; 64],
    /// Monotonic per-cell witness counter; rejects replay even when the
    /// state commitment hasn't moved.
    pub sequence: u64,
    /// Optional STARK proof attesting to the transition that produced
    /// `cell_state` from a prior committed state. Same shape as
    /// `cell/src/peer_exchange.rs::PeerStateTransition::transition_proof`
    /// (Option<Vec<u8>>) so the two structures stay isomorphic.
    pub transition_proof: Option<Vec<u8>>,
}
```

Phase 1 adds AIR teeth for the `signature` + `sequence` parts. Phase 2
adds AIR teeth for `transition_proof`. The `cell_state` + `state_proof`
fields keep their existing pre-image-opener semantics; what the AIR
gains is the means to *witness the witness*, not just the
state.

> **Boundary status post-soundness-sweep, pre-AIR-teeth.** The
> signature closes wire malleability (§6 of the audit). The sequence
> closes replay (§2.2 of the audit). The transition proof closes
> "where did this state come from." But none of those properties hold
> *inside the AIR* yet — they hold at the executor's pre-AIR
> injection step. The AIR still applies sovereign effects uniformly
> with hosted ones, just as `AUDIT-sovereign-witness-teeth.md §3.3`
> describes.

## 3. Phase 1 — minimal AIR teeth

### 3.1 New trace column

Add one BabyBear-felt aux column to `EffectVmAir`:

- `WITNESS_KEY_COMMIT` (single felt, aux). Computed by the prover as
  `Poseidon2(cell.owner_pubkey)` and bound to the witness's signing
  identity. For non-sovereign-witnessed turns the column is zero
  (sentinel) and `IS_SOVEREIGN_CELL` (see §3.3) gates the boundary.

This places the prover under the obligation to populate the column
deterministically; a verifier comparing it against PI catches any
deviation.

### 3.2 New PI slots

Add two PI slots, both single felts, to the Effect VM PI layout
(`circuit/src/effect_vm/pi.rs`):

- `SOVEREIGN_WITNESS_KEY_COMMIT` (single felt). The verifier-supplied
  expected value of `Poseidon2(cell.owner_pubkey)`, bound to whatever
  key the *signature* in §2 verified under at executor injection time.
- `IS_SOVEREIGN_CELL` (single felt boolean). 1 iff this proof is
  attesting to a sovereign-witnessed effect; 0 for hosted cells.

The verifier's PI-matching loop populates `SOVEREIGN_WITNESS_KEY_COMMIT`
from `witness.cell_state.owner_pubkey` (after the executor's signature
check has already verified the signature is by that key). The prover
populates the in-trace column from the same source. The boundary
constraint (§3.3) enforces equality.

### 3.3 New boundary constraint

```text
// Row-0 boundary: when IS_SOVEREIGN_CELL == 1, the in-trace
// WITNESS_KEY_COMMIT column at row 0 must equal the PI.
constraint (row=0, gated by PI[IS_SOVEREIGN_CELL]):
    trace[0][WITNESS_KEY_COMMIT] - PI[SOVEREIGN_WITNESS_KEY_COMMIT] == 0
```

When `IS_SOVEREIGN_CELL == 0` (hosted-cell path), the constraint is
trivially satisfied (gated out), so this addition does not change the
semantics of existing hosted-cell proofs.

When `IS_SOVEREIGN_CELL == 1`, the AIR refuses any trace whose
`WITNESS_KEY_COMMIT` disagrees with the PI. The verifier supplies the
PI from the *signature-verified* key. Combined effect: a sovereign
turn whose witness was signed by key K and verified by the executor
will produce a proof whose AIR-bound `WITNESS_KEY_COMMIT` is
`Poseidon2(K)`. A malicious executor cannot apply the effects under a
*different* key without changing PI, and a verifier supplied with the
honest PI will reject.

This is the minimum-viable algebraic tie between the witness's
signing identity and the AIR transition. It does **not** prove the
*signature itself* (no Ed25519-in-AIR is required); it proves that the
prover and verifier agree on which key was the signing principal, with
the executor's signature check at injection time serving as the
acceptance-inside boundary.

### 3.4 Sequence column (replay-in-trace)

An additional optional Phase 1 column:

- `WITNESS_SEQUENCE` (single felt, aux). Bound to PI
  `SOVEREIGN_WITNESS_SEQUENCE` via a row-0 boundary constraint, gated
  by `IS_SOVEREIGN_CELL`.

The verifier supplies the expected sequence from the executor's
post-validation state; the prover binds it into the trace. Two
adjacent sovereign turns on the same cell must show monotonically
increasing `WITNESS_SEQUENCE` PI values across receipts, enforced by
the verifier's chain-walk loop (not by the AIR itself, since each
proof is per-cell-per-turn).

### 3.5 Phase 1 column layout cost

- 2 new aux columns (`WITNESS_KEY_COMMIT`, `WITNESS_SEQUENCE`).
- 3 new PI slots (`SOVEREIGN_WITNESS_KEY_COMMIT`,
  `SOVEREIGN_WITNESS_SEQUENCE`, `IS_SOVEREIGN_CELL`).
- 2 new boundary constraints (both row-0, both gated by
  `IS_SOVEREIGN_CELL`).
- No new transition constraints (Phase 1 binds *identity* at the
  boundary; it does not constrain *evolution* mid-trace).

This is a small AIR-width footprint (~2 extra felts × trace_len). The
PI surface grows by 3, which is a non-issue.

## 4. Phase 2 — STARK-attested AIR teeth

Phase 2 lifts the optional `transition_proof: Option<Vec<u8>>` into
the AIR. When present, the witness carries a STARK proof attesting to
how the witnessed `cell_state` was produced from a prior committed
state. The recursive verifier (Lane Golden-Edge's deliverable)
provides the means to verify-a-STARK-inside-a-STARK.

### 4.1 Recursive composition shape

Following Lane Golden-Edge's recursive-verifier API (its exact shape
depends on whether they expose a `RecursiveVerifyAir` or wrap into
`EffectVmAir`), Phase 2 either:

- **Option A (in-line).** Embeds the recursive verifier into
  `EffectVmAir`, gated by `IS_SOVEREIGN_CELL` and a new
  `HAS_TRANSITION_PROOF` PI flag. Only sovereign-cell rows with a
  transition_proof exercise the recursive path; everything else
  passes the gate trivially.
- **Option B (compose).** Treats the transition_proof as a separate
  proof that the outer `EffectVmAir` references via a PI commitment
  (`SOVEREIGN_TRANSITION_PROOF_VK_HASH` + `SOVEREIGN_TRANSITION_PROOF_COMMITMENT`),
  with the recursive verification done by the off-AIR verifier. The
  cost is one extra hop in the verification chain; the benefit is no
  AIR-width inflation for hosted-cell paths.

Option B is the lower-risk first step (mirrors the existing
`CUSTOM_PROOFS_BASE` pattern in `circuit/src/effect_vm/pi.rs:78`,
where custom effects ship a vk_hash + proof_commitment PI pair).
Option A is the long-term home; Option B is the bridge.

### 4.2 PI additions (Option B, recommended first step)

Per sovereign cell with a transition_proof, two PI slot groups (8 felts
total, matching the existing `CUSTOM_ENTRY_SIZE`):

- `SOVEREIGN_TRANSITION_PROOF_VK_HASH` (4 felts). The vk-hash of the
  AIR that the transition proof was generated under. For peer-
  exchange-shaped transitions, this is `EFFECT_VM_VK_HASH` (a sovereign
  cell's prior turn was, itself, an Effect VM execution).
- `SOVEREIGN_TRANSITION_PROOF_COMMITMENT` (4 felts). A Poseidon2 hash
  of the canonical (proof_bytes, public_inputs) tuple.

The off-AIR verifier:

1. Reads `SOVEREIGN_TRANSITION_PROOF_VK_HASH` + `SOVEREIGN_TRANSITION_PROOF_COMMITMENT`
   from PI.
2. Reads the transition_proof bytes from the witness.
3. Verifies the inner STARK via `EffectVmAir` (or whichever AIR the
   vk_hash names), with the inner PI also reconstructable from the
   witness's `cell_state.state_commitment()` (the inner OLD_COMMIT) and
   the current turn's `OLD_COMMIT` (the inner NEW_COMMIT).
4. Recomputes the commitment locally and compares to PI.
5. Rejects on any mismatch.

This is the "scope-(2)-style" recursive composition: the outer proof
attests to "this turn applied effects correctly given the witness;"
the inner proof attests to "the witness is a legitimate state
transition from a prior commitment." Together they reconstruct the
full causal history without trusting the executor.

### 4.3 PI additions (Option A, in-line — long-term home)

When Lane Golden-Edge's recursive verifier is callable inside an AIR,
the outer `EffectVmAir` gains:

- A new selector column `SEL_RECURSE_TRANSITION_PROOF`.
- A block of aux columns mirroring the inner proof's VK-state-hash
  (size depends on the recursive verifier's interface; typically tens
  to hundreds of felts).
- Transition constraints over those aux columns that mirror the
  recursive verifier's per-step polynomial.

This is a substantial AIR-width increase and a degree-bound concern;
landing it depends on the recursive verifier's `max_degree` fitting
into the Effect VM AIR's existing degree budget (≤ 4 with the current
blowup). Lane Golden-Edge owns the degree negotiation.

### 4.4 What Phase 2 actually buys

Today (post-Phase-1): the AIR enforces that the trace ran under the
signing key K that the executor said it ran under. It does *not*
constrain how the state K signed for *got there*. A malicious executor
could still rewrite history before a witness was first registered.
Phase 2's transition_proof closes that gap: the AIR recursively
demands a proof for every sovereign state transition all the way back
to the cell's MakeSovereign moment.

In `BOUNDARIES.md §2.6` vocabulary, this is the transition from "the
host executor doesn't see cleartext during the turn" (proof-carrying)
to "the host executor *and any predecessor executor* doesn't see
cleartext." The full causal history becomes acceptance-inside.

## 5. Migration story

Sovereign cells today come in two flavours (per
`AUDIT-sovereign-witness-teeth.md §3.4`):

- **Phase 1 witness path** (`sovereign_witnesses` populated,
  `execution_proof` absent). The default; ~dozens of sites construct
  these.
- **Phase 3 proof-carrying path** (`execution_proof` populated,
  `sovereign_witnesses` empty). Algebraically sound; cclerk API is
  `execute_sovereign_turn_with_proof`.

These paths are mutually exclusive at construction
(`sdk/src/cipherclerk.rs:4442-4554`). The witness path is the
weak-by-design fallback; the proof path is the algebraically-sound
target.

### 5.1 Coexistence via `IS_SOVEREIGN_CELL`

The migration plan keeps the witness path alive (so existing call
sites don't break) but raises its soundness floor:

1. **Land Phase 1 (this design).** Every sovereign witnessed proof
   now includes the witness key in PI; the AIR refuses any divergence.
   Hosted-cell proofs see `IS_SOVEREIGN_CELL == 0` and continue
   unchanged. Phase 1 is backward-compatible *except* that older
   sovereign-witness proofs (pre-AIR-teeth) cannot be verified by
   post-AIR-teeth verifiers — they'll fail the new boundary
   constraint with the sentinel value. This is the intended migration
   pressure: old proofs are obsoleted, callers must reprove or use
   the proof-carrying path.

2. **Land Phase 2 (Option B first).** Sovereign witnesses with a
   `transition_proof` get full causal coverage; sovereign witnesses
   without one still pass the Phase 1 teeth but carry the existing
   "executor decides history" caveat in their boundary contract.

3. **Audit the call sites** named in `AUDIT-sovereign-witness-teeth.md
   §9 OQ1`: `node/`, `app-framework/`, `apps/`, `demo-agent/`,
   `teasting/`, `intent/`. For each, decide whether the cell should
   migrate to proof-carrying (Phase 3 path) or whether the new
   Phase-1-plus-signature witness is acceptable.

4. **Mark `SovereignCellWitness` without `transition_proof` as
   `#[deprecated]`** once enough call sites have migrated. Set a
   timeline (e.g. Stage 10) for removal of the un-attested
   transition_proof path entirely.

### 5.2 Per-row gate vs PI flag

Two equivalent designs for `IS_SOVEREIGN_CELL`:

- **Per-row gate.** A new selector column in the trace, set to 1 only
  on the row(s) processing sovereign effects. The boundary
  constraints become per-row constraints gated by the column.
- **PI flag.** A single PI bit covering the whole proof.

The PI flag is simpler (matches the `IS_AGENT_CELL` precedent at
`circuit/src/effect_vm.rs:764`). One per-cell proof is either
sovereign or hosted; mixing in the same proof would be a bundle-
level concern handled by the verifier loop, not a per-row concern.
**Recommendation: use the PI flag.**

### 5.3 Witness-vs-proof-carrying as a spectrum

Pre-design, the two paths are mutually exclusive (per
`AUDIT-sovereign-witness-teeth.md §3.4`). Post-Phase-2, they collapse
into a spectrum:

| Witness shape | AIR teeth | Boundary contract |
|---|---|---|
| Pre-image opener only | None (today) | host executor cleartext-inside for the witnessed turn |
| Pre-image + signature + sequence (post-Phase-1) | Witness key bound to PI | host executor cleartext-inside, but cannot swap keys |
| Pre-image + signature + sequence + transition_proof (post-Phase-2 Option B) | Witness key + recursive verification of prior transition | host executor acceptance-inside (proof verifies, no cleartext-inside) |
| `execution_proof` (current Phase 3 path) | Full algebraic teeth via `verify_and_commit_proof` | host executor acceptance-inside |

The last two rows are operationally equivalent under post-Phase-2:
both ship a proof, both verify recursively, both treat the executor
as acceptance-inside. The structural difference is whether the cell
state ships alongside (witness path) or stays sovereign (proof-only
path). Choosing between them becomes a privacy/bandwidth tradeoff,
not a soundness one.

## 6. Boundary contract (post-Phase-1, post-Phase-2)

Per `BOUNDARIES.md §5.2`, the rustdoc convention for the relevant
types after each phase lands.

### 6.1 `SovereignCellWitness` post-Phase-1

```rust
/// Boundary contract:
/// - Cleartext-inside:  the host executor (during the turn);
///                      the agent constructing the witness;
///                      anyone who has ever seen the cell's preimage state.
/// - Commitment-inside: the federation (stores the 32-byte commitment);
///                      the verifier (verifies the post-AIR-teeth proof
///                      via PI[SOVEREIGN_WITNESS_KEY_COMMIT]).
/// - Acceptance-inside: anyone verifying the outer Effect VM proof;
///                      they learn "this turn was applied under a witness
///                      whose signing key matches PI" — they do NOT
///                      learn cell state contents.
/// - Out-of-band:       network observers, other federations.
/// Enforced by: Ed25519 signature (executor pre-AIR injection check)
///              + AIR boundary constraint (row 0,
///                WITNESS_KEY_COMMIT == PI[SOVEREIGN_WITNESS_KEY_COMMIT])
///              + sequence monotonicity (verifier chain-walk).
/// Failure mode if violated: a malicious executor that swaps the
///   witness for one signed by a different key produces a proof whose
///   AIR-bound WITNESS_KEY_COMMIT disagrees with PI; the verifier
///   rejects. A wire attacker who substitutes a different preimage of
///   the same commitment must also forge the signature (Ed25519) —
///   computationally infeasible.
```

### 6.2 `SovereignCellWitness` post-Phase-2 (with transition_proof present)

```rust
/// Boundary contract:
/// - Cleartext-inside:  the agent;
///                      the host executor (during the turn — UNCHANGED
///                      from Phase 1).
/// - Commitment-inside: the federation;
///                      the verifier (binds WITNESS_KEY_COMMIT,
///                      SOVEREIGN_TRANSITION_PROOF_COMMITMENT, and
///                      the recursive proof's inner PI).
/// - Acceptance-inside: anyone verifying the outer proof + the
///                      recursive transition proof. They learn the
///                      full causal chain back to MakeSovereign without
///                      learning the cleartext state at any link.
/// - Out-of-band:       network observers, other federations.
/// Enforced by: Phase-1 teeth (above) + recursive STARK verification
///              of the transition_proof.
/// Failure mode if violated: the recursive verifier rejects.
```

### 6.3 `EffectVmAir` post-Phase-1

The Effect VM AIR gains a new boundary semantics:

```rust
/// Boundary contract (updated post sovereign-witness teeth):
/// - Cleartext-inside:  prover (knows the trace witness);
///                      for sovereign-witnessed turns: the cell's
///                      owner (signs the witness) + the host executor
///                      (injects the witnessed state).
/// - Commitment-inside: verifier (with PI). For sovereign turns, PI
///                      additionally binds the witness key + sequence
///                      to the trace.
/// - Acceptance-inside: anyone verifying the STARK. They learn
///                      "trace satisfied EffectVmAir under these PI."
///                      For sovereign-witnessed turns, this includes
///                      "trace ran under the signing key whose
///                      Poseidon2 hash equals SOVEREIGN_WITNESS_KEY_COMMIT."
/// - Out-of-band:       everyone else.
```

## 7. Open questions for the implementing lane

This doc is design-only. The lane that implements either phase needs
to answer:

1. **Phase 1 ordering.** Should `IS_SOVEREIGN_CELL` be a new PI slot
   appended after `IS_AGENT_CELL` (slot 74), or slotted into the
   first available position? The latter keeps the PI layout dense;
   the former preserves index stability across lanes. Recommend
   *append*; γ.2 already appended without breaking earlier lanes.

2. **Sentinel semantics.** When `IS_SOVEREIGN_CELL == 0`, what value
   does the prover write to `WITNESS_KEY_COMMIT`? Two options:
   (a) the prover writes `BabyBear::ZERO` and the verifier supplies
   the same sentinel in PI; (b) the prover writes the cell's
   owner-key hash regardless and the verifier checks unconditionally.
   Option (a) preserves backward compatibility with hosted-cell
   proofs that don't know about sovereign keys; option (b) is
   uniform but requires hosted-cell call sites to populate the new
   PI. **Recommend (a)** — gated boundary is the cheaper migration.

3. **Multi-witness turns.** A single turn may witness multiple
   sovereign cells (`turn.sovereign_witnesses` is a
   `HashMap<CellId, SovereignCellWitness>`). Each per-cell proof
   carries its own `IS_SOVEREIGN_CELL` + `SOVEREIGN_WITNESS_KEY_COMMIT`;
   the verifier loops over the bundle. Confirm: is the verifier loop
   in `verify_proof_carrying_turn_bundle` (`turn/src/executor.rs:1685`)
   the right hook, or do we need a sibling for witness-path turns?

4. **Sequence-set persistence.** The `WITNESS_SEQUENCE` PI requires
   the federation to track per-cell witness sequences. Today the
   sovereign commitment store
   (`cell/src/ledger.rs::sovereign_commitments`) holds only the
   commitment; sequence would be a new column in that map. Decide
   the storage shape and migration path before landing Phase 1.

5. **Phase 2 option choice.** Option A (in-line recursive verifier
   in `EffectVmAir`) vs Option B (separate proof + PI commitment).
   This depends on Lane Golden-Edge's recursive verifier shape and
   degree budget. **Recommend B first**, as a bridge; revisit A
   once the recursive verifier has stabilised.

6. **Backward-compat window.** Phase 1 obsoletes pre-AIR-teeth
   sovereign-witness proofs (they fail the new boundary). How long
   do we accept *both* — the new and the old — before the old path
   is rejected outright? Suggested window: one minor version
   (Stage 9), then hard-removal in Stage 10.

7. **Cipherclerk signing-message coverage (P2-10).** The cipherclerk's v1
   signing message (`sdk/src/cipherclerk.rs:3895-3906`) does not yet
   cover `sovereign_witnesses`. The audit at
   `AUDIT-sovereign-witness-teeth.md §6` flags this as a precondition
   for closing T9 fully. Coordinate with the cclerk-signature-v3
   migration: AIR teeth are necessary but not sufficient — the wire
   layer still needs the cclerk to sign over the witness payload.
   Phase 1 lands the AIR teeth; the cclerk migration is a sibling
   lane.

## 8. Cross-references

- `AUDIT-sovereign-witness-teeth.md` — the no-teeth diagnosis, esp.
  §3 (PI/trace/constraints search), §4 (peer-exchange comparison),
  §8 (verdict), §9 (open questions for the designer).
- `EXECUTOR-HONESTY-AUDIT.md` T9 — the threat this design closes.
- `BOUNDARIES.md` §2.6, §3.2, §7.2 — the boundary contract this
  design transitions from "executor sees but doesn't persist" toward
  "executor is acceptance-inside."
- `circuit/src/effect_vm/pi.rs` — current PI layout (extends here).
- `circuit/src/effect_vm.rs:764` — `IS_AGENT_CELL` precedent for
  PI-flag gating, mirrored by `IS_SOVEREIGN_CELL`.
- `circuit/src/effect_vm.rs:8517-8536` — current `mode_flag`
  (RESERVED bits 8..9), which marks "cell IS sovereign" but not
  "actor IS entitled." Phase 1 closes the latter.
- `cell/src/peer_exchange.rs:35-303` — `PeerStateTransition`, the
  structurally-stronger analogue Phase 1's signature shape mirrors.
- `turn/src/executor.rs:3131-3249` — `verify_and_commit_proof`, the
  current Phase-3 proof-carrying path that Phase 2 generalises.
- `turn/src/executor.rs:3258-3330` — current witness-path
  injection, which Phase 1's AIR boundary backstops.
- `turn/src/turn.rs:22-30` — current `SovereignCellWitness`
  definition (pre-soundness-sweep).
- `sdk/src/cipherclerk.rs:3895-3906` — cclerk signing-message gap P2-10
  (sibling lane).
- Lane Golden-Edge's recursive verifier work — Phase 2 dependency.
- `STAGE-7-GAMMA-2-PI-DESIGN.md` — the precedent for adding PI
  fields alongside new boundary constraints, with γ.2's append-only
  layout.
- `EFFECT-VM-SHAPE-A.md` — Effect VM AIR design baseline.

End.
