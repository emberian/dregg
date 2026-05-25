# Sovereign witness algebraic teeth audit (T9)

**Date:** 2026-05-24. **Scope:** read-only. **Question:**
EXECUTOR-HONESTY-AUDIT.md T9 — *Do sovereign witnesses
algebraically constrain the transition, or do they just decorate
the receipt?*

**Verdict (short):** Sovereign witnesses constrain the executor
(failure-closed at the host-side ledger check) but do **not**
constrain the AIR. There are no sovereign-witness columns, no
sovereign-witness PI slots, and no AIR constraints gated on the
witness. The witness is a pre-image opener for the federation's
stored commitment — strong against "lie about pre-state," but
weak against "where did this witness come from" because the
witness is unsigned and any node that has ever seen the cell
state can produce one. The actor signature does not cover the
witness either: `compute_turn_bytes` is still pinned to the
`pyana-turn-v1:` domain (P2-10 open).

---

## 1. Data shape: what *is* a sovereign witness?

`turn/src/turn.rs:22-30`:

```rust
pub struct SovereignCellWitness {
    /// The full cell state (agent provides this).
    pub cell_state: Cell,
    /// Proof that this state matches the stored commitment.
    /// For Phase 1a: BLAKE3 hash must equal `cell_state.state_commitment()`.
    /// Later phases may use Merkle proofs from a state tree.
    pub state_proof: [u8; 32],
}
```

This is a *pre-image opener*, not a *proof*. The two fields are
trivially related: `state_proof` is just `cell_state.state_commitment()`
recomputed by the agent. The doc-comment promises "later phases may
use Merkle proofs from a state tree." None of the later phases have
arrived in this struct. There is no signature field, no STARK
field, no Merkle path field, no sequence/replay counter, no
issuance attestation, no per-actor binding.

The other "field" the doc promises — that `state_proof` "match the
stored commitment" — is enforced once, at executor injection time
(see §2). It is *not* re-checked inside the AIR.

## 2. Witness verification on the executor side

`turn/src/executor.rs:3258-3330` (sovereign-witness injection
block, immediately after Phase 1 fee/nonce debit, before forest
execution):

For each `(cell_id, witness)` in `turn.sovereign_witnesses`:

1. The cell **must** have an entry in `ledger.sovereign_commitments`
   (i.e. it must be a federation-registered sovereign cell).
   Otherwise → `InvalidEffect { reason: "sovereign witness provided
   for non-sovereign cell ..." }` (rejection).
2. `witness.state_proof == witness.cell_state.state_commitment()`,
   else → `SovereignCommitmentMismatch`. (This is the "I can
   recompute the same hash you gave me" check — trivial; the
   prover can always satisfy it because they pick both sides.)
3. `witness.cell_state.state_commitment() == stored_commitment`
   in the ledger, else → `SovereignCommitmentMismatch`. (This is
   the *real* binding: the witness pre-image must hash to the
   federation's previously-recorded sovereign commitment.)
4. `witness.cell_state.id() == cell_id`, else → `InvalidEffect`.
5. The witnessed cell is **injected into the hosted ledger table**
   (either overwriting an existing entry for the agent case, or
   freshly inserted). Subsequent forest execution sees it as a
   normal hosted cell.

After successful forest execution
(`turn/src/executor.rs:3478-3484`):

```rust
for cell_id in &sovereign_cell_ids {
    if let Some(cell) = ledger.remove(cell_id) {
        let new_commitment = cell.state_commitment();
        let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
    }
}
```

The witnessed cell is *removed from the hosted store*, and the
post-execution commitment becomes the new sovereign commitment.
The federation never persistently stores the full cell state.

### 2.1 What this *does* prevent
- **Stale-state replay across federations.** A witness that
  doesn't open the *current* stored commitment is rejected.
- **State-fabrication.** An attacker cannot present an invented
  `cell_state` and have the executor act on it; the recompute step
  ties `cell_state` to the stored 32-byte commitment.
- **Wrong-cell injection.** `witness.cell_state.id() == cell_id`
  catches the trivial "swap the cell" attack.

### 2.2 What this does *not* prevent
- **Identity of the witness provider.** The witness carries no
  signature. Any node — not just the cell's owner — that has at
  some point seen `cell_state` (e.g. via a peer-exchange handshake,
  via a prior witnessed turn, via a sibling federation, via a
  privileged read of the cipherclerk's sovereign cache) can package the
  same `cell_state` into a fresh witness. As long as the stored
  commitment hasn't moved, the witness is accepted.
- **Mid-flight tampering of the witness by an executor.** Since
  the cclerk signature (`compute_turn_bytes`) does not cover
  `sovereign_witnesses` (P2-10 open in `sdk/src/cipherclerk.rs:3895-3906`),
  an executor that holds the SignedTurn can swap the witness payload
  for any other valid-preimage cell (same id, same stored
  commitment) without invalidating the signature. There is exactly
  one such payload at any given stored-commitment instant —
  *provided* the commitment is collision-resistant, which it is —
  so this isn't a state-forgery attack, but it is a wire-malleability
  attack on the SignedTurn struct: the receipt's Turn::hash (v3,
  which *does* cover the witness) will differ from the cipherclerk's
  signed turn-hash (v1, which doesn't). If any downstream verifier
  checks "cclerk signature covers Turn::hash" — and several places
  do compute `turn.hash()` to look up the receipt by content
  address — the mismatch is invisible because the cclerk path
  never authenticates the v3-hash form.

### 2.3 Failure-closed?

For the *positive* attack ("substitute a fake state"), yes —
failure-closed at step 3.

For the *negative* attack ("omit the witness entirely while
targeting a sovereign cell"), almost-closed but **by accident**.
The dedicated error variant `TurnError::SovereignWitnessRequired`
exists (`turn/src/error.rs:158`, `LedgerError::SovereignWitnessRequired`
at `cell/src/ledger.rs:156`) but is **never constructed anywhere in
the tree**:

```
$ rg "TurnError::SovereignWitnessRequired" --type rust
turn/src/error.rs:483:            TurnError::SovereignWitnessRequired { cell } => {
```

(Only the Display arm; no constructor.) The actual rejection path
is `execute_tree` at `turn/src/executor.rs:3706-3708`:

```rust
if ledger.get(&action.target).is_none() {
    return Err((TurnError::CellNotFound { id: action.target }, path.clone()));
}
```

A sovereign cell with no witness is not in the hosted table, so
the action targeting it dies at `CellNotFound`. This is confirmed
by the test `sovereign_cell_rejected_without_witness`
(`turn/src/tests.rs:6975-7050`): it asserts the rejection variant
is `CellNotFound`, **not** `SovereignWitnessRequired`. The dedicated
error is dead code. From a soundness perspective this is fine —
the turn is rejected — but the error message tells the wrong
story, and refactoring the cell-lookup path (e.g. lazy hydration
that materialises a cell from a sovereign commitment on demand)
could *quietly* convert this into a false-positive acceptance,
because the only thing protecting sovereign cells from "skip the
witness" is "the cell happens not to be in the hosted hashmap."

## 3. Witness on the AIR side: searching for teeth

### 3.1 PI layout

`circuit/src/effect_vm/pi.rs` — `rg "sovereign|witness"` returns
**zero hits**. There are no sovereign-witness PI slots. The PI
fields are:

- `OLD_COMMIT_BASE` / `NEW_COMMIT_BASE` (4 felts each) — the
  cell's state commitment before and after the turn.
- `EFFECTS_HASH_BASE`, `INIT_BAL_*`, `FINAL_BAL_*`, `NET_DELTA_*`,
  `CURRENT_BLOCK_HEIGHT`, `MAX_CUSTOM_EFFECTS`,
  `CUSTOM_EFFECT_COUNT`, `APPROVED_HANDOFFS_BASE`,
  `TURN_HASH_BASE`, `EFFECTS_HASH_GLOBAL_BASE`, `ACTOR_NONCE`,
  `PREVIOUS_RECEIPT_HASH_BASE`, bilateral PI fields (Stage 7-γ.2),
  `IS_AGENT_CELL`, per-custom-effect entries.

Nothing in here references a sovereign witness, a sovereign-mode
flag in PI, or an attestation of who-may-act on a sovereign cell.

### 3.2 Trace columns

`circuit/src/effect_vm.rs` — `rg "sovereign|witness"` finds:

- `// MakeSovereign (12): Transition cell from managed to sovereign.`
  (a docstring at line 22).
- `mode_flag` references (lines ~144, ~1155, ~1265, ~1961, ~2612,
  ~7859, ~7927, ~8517-8536) — this is the in-trace bit that says
  "the cell *is* sovereign," kept in the `RESERVED` column (bits
  8..9), encoded such that `MakeSovereign` increments `reserved`
  by `256` (i.e. flips bit 8 from 0 to 1).
- Stage 2 adversarial test `test_stage2_make_sovereign_double_transition_rejected`
  — confirms the AIR rejects a `MakeSovereign` row when the cell
  is *already* sovereign.

The `mode_flag` is a *property of the cell* — "this cell is now
sovereign" — not a *property of the actor* — "this actor is
entitled to act on the sovereign cell." The AIR enforces the
former. It does not check the latter at all.

### 3.3 Per-effect constraints

Walking the per-selector constraint blocks in
`circuit/src/effect_vm.rs` (e.g. SetField at ~1773, Transfer at
the surrounding lines, MakeSovereign at 2599-2630):

- The AIR constrains the *state transition*: old state → new
  state under the given effect parameters, with conservation of
  the untouched fields.
- The AIR does **not** branch on the `mode_flag` for any non-
  `MakeSovereign` effect. SetField, Transfer, Grant, Custom, etc.
  apply uniformly regardless of whether the target is hosted or
  sovereign.
- There is no constraint of the form "if `mode_flag == 1` then
  some witness-bound column must equal X." There is no witness-
  bound column.

### 3.4 The proof-carrying path (Phase 3) is the actual algebraic surface

`turn/src/executor.rs:3131-3249` — when `turn.execution_proof` is
`Some`, the executor takes the *proof-carrying* path. There:

- The proof's PI binds `OLD_COMMIT` to the federation's stored
  sovereign commitment for `execution_proof_cell`.
- `NEW_COMMIT` to `turn.execution_proof_new_commitment`.
- `EFFECTS_HASH` to the effects derived from the turn.
- `TURN_HASH`, `EFFECTS_HASH_GLOBAL`, `ACTOR_NONCE`,
  `PREVIOUS_RECEIPT_HASH` to the canonical Turn identity
  (`compute_turn_identity_pi`).
- The STARK is verified via `EffectVmAir`.

This is the path that has algebraic teeth. It is also the path
that *does not use `sovereign_witnesses` at all* — the cclerk
constructs it with `sovereign_witnesses: HashMap::new()` and the
proof itself is the validation
(`sdk/src/cipherclerk.rs:4442-4554`).

So we have a fork:

- **Phase 1 witness path** (`sovereign_witnesses` populated,
  `execution_proof` absent): no AIR involvement, executor re-runs
  the effects on the injected cell.
- **Phase 3 proof-carrying path** (`execution_proof` populated,
  `sovereign_witnesses` empty): full AIR involvement, executor
  verifies a STARK and updates the commitment without re-executing.

The witness is binding on the *executor classical path*. It is
not binding inside the *AIR proof path*. The two are mutually
exclusive at construction (the executor takes either branch based
on `execution_proof.is_some()`).

## 4. Comparison with `pyana_cell::peer_exchange::PeerStateTransition`

`cell/src/peer_exchange.rs:35-63`:

```rust
pub struct PeerStateTransition {
    pub cell_id: CellId,
    pub old_commitment: [u8; 32],
    pub new_commitment: [u8; 32],
    pub effects_hash: [u8; 32],
    pub timestamp: i64,
    pub sequence: u64,
    #[serde(with = "sig_serde")]
    pub signature: [u8; 64],
    #[serde(default)]
    pub transition_proof: Option<Vec<u8>>,
}
```

Verification (`cell/src/peer_exchange.rs:236-303`):

1. Ed25519 signature over `(old, new, effects_hash, timestamp,
   sequence)` against the peer's known pubkey.
2. `old_commitment == last_known_commitment` for this peer.
3. Monotonic sequence (no gaps).
4. Non-regressing timestamp.
5. *If `transition_proof` is `Some`,* verify the STARK via
   `EffectVmAir` with PI binding old → new + effects_hash + cell_id.

`PeerStateTransition` has:

- A **signature** binding the transition to a specific signer.
- A **sequence number** binding it to a specific causal position.
- An **optional STARK** with PI binding the full transition.

`SovereignCellWitness` has:

- No signature.
- No sequence (the turn's nonce is on the *agent*, not the
  *witnessed cell*; for the common case where agent == sovereign
  cell, the nonce serves both, but this isn't structurally
  required).
- No STARK reference.

`PeerStateTransition` is the *stronger* of the two artifacts. The
sovereign-witness analogue would have at least the signature and
sequence, and ideally the STARK as an option — at which point we
might as well take the proof-carrying path.

The current `SovereignCellWitness` is, structurally, the *weakest*
form of state attestation in the codebase: a pre-image opener
with no actor binding.

## 5. Cross-cutting question: what binds the witness to the actor?

When the agent submits a turn `{ agent: cell_X, sovereign_witnesses: {
cell_Y => witness_Y } }`, what prevents `cell_X` from acting on
`cell_Y`'s state without `cell_Y`'s consent?

The answer is **the same thing that protects hosted cells**: the
forest's `verify_authorization` step
(`turn/src/executor.rs:4124-...`), which checks
`target_cell.permissions` and the actor's c-list. Once the witness
is injected (§2), the cell is in the hosted ledger and the normal
permission/capability checks apply.

This is mostly fine for the common case (agent == sovereign cell,
permissions set such that the agent's own actions are allowed).
For the general case (agent != sovereign cell, sovereign cell is a
shared resource), the picture is murkier:

- The witness submitter doesn't have to be the cell's owner. They
  only have to know the current state.
- The cell's permissions (loaded from `witness.cell_state.permissions`)
  *are* the source of truth — those are baked into the
  `state_commitment`, so they cannot be altered without changing
  the stored commitment.
- So the cell's "who can write me" rule is preserved, but the
  identity of the *witness-provider* is unconstrained.

In practice this means: a third-party node that snooped the
sovereign cell's state can re-submit a turn that the original
owner would have submitted, **as long as that node also possesses
whatever caps/signatures the cell's permissions demand**. So the
witness is not weakening permissions — it's merely admitting more
parties into the "I can package up your state for you" role.

This may be by design. It is not stated as a design property
anywhere in the code.

## 6. Wire-malleability: the Turn::hash v3 vs sign-message v1 split

Session memory notes "Turn::hash v3 covers sovereign_witnesses."
This is correct: `turn/src/turn.rs:149-275` walks every witness
entry and hashes `(cell_id, state_proof, state_commitment)` per
witness. v3's domain tag is `"pyana-turn-v3:"`.

But the *signature* on the SignedTurn is over
`AgentCipherclerk::compute_turn_bytes` (`sdk/src/cipherclerk.rs:3852-3908`),
which uses `TURN_DOMAIN_PREFIX = b"pyana-turn-v1:"` and **does not
cover** `sovereign_witnesses`, `execution_proof`,
`execution_proof_cell`, `execution_proof_new_commitment`,
`conservation_proof`, or `custom_program_proofs`. The function
body has a self-flagging comment (P2-10):

> AUDIT[P2-10]: this signing message does NOT yet cover
> `turn.conservation_proof`, `turn.sovereign_witnesses`,
> `turn.execution_proof`, ... a holder of write access to a
> SignedTurn struct in flight can swap any of them without
> invalidating the cipherclerk's signature.

So Turn::hash and the cclerk signature disagree about the
canonical form of a turn. The receipt chain (and any verifier that
re-derives `turn.hash()` from a SignedTurn) will see one identity;
the cclerk thinks it signed a different one. In the sovereign
witness case, this means:

- **Wire attacker swap:** A relayer/executor between the cclerk and
  the final ledger can substitute the `sovereign_witnesses` field
  on a SignedTurn without breaking the cclerk signature. They
  cannot forge a state that doesn't open the stored commitment
  (the executor catches that at §2 step 3), but they *can* swap
  one valid witness for another — e.g. if the witness includes
  derivable side-data such as freshly-issued ephemeral keys, the
  attacker substitutes their own values. (Whether
  `Cell::state_commitment()` actually covers those side-data is
  governed by `cell/src/commitment.rs` —
  `compute_canonical_state_commitment` — which we did not fully
  audit here, but the field set is broad enough that a tampered
  witness with identical state_commitment is unlikely in practice.
  The point is: this is a property of `state_commitment`, not of
  the witness protocol.)
- **Receipt-mismatch attacker:** A more interesting attack is for
  a malicious executor to *omit* the witness from the turn it
  records in the receipt chain (or substitute an empty map). The
  receipt's `turn_hash` (which uses v3) will differ from what
  the cipherclerk's signature attests to (v1). If a verifier checks
  the signature against the cipherclerk's v1 form, the omission is
  silent at the signature layer. If the verifier rederives
  `turn.hash()` (v3) and compares it to the receipt's
  `turn_hash`, the mismatch is caught at the receipt-binding
  layer, *but only because the receipt commits to v3*. So this
  is partially closed at the receipt-replay layer (witnessed-
  receipt chain), and entirely open at the signature layer.

This is a soundness step-down of the form described in
EXECUTOR-HONESTY-AUDIT.md §"Defense surface": the witness lives
at layer 2/3 (signature/replay), never at layer 1 (AIR).

## 7. Failure modes summary

| Attack | What happens | Where caught |
|---|---|---|
| Skip witness for a sovereign cell | `CellNotFound` at `execute_tree` | Executor (accidental: relies on cell absence from hosted table) |
| Substitute random bytes as `state_proof` | `SovereignCommitmentMismatch` (step 2 then step 3) | Executor §2 |
| Substitute a fabricated `cell_state` (any preimage) | `SovereignCommitmentMismatch` at step 3 (no preimage besides the real one collides) | Executor §2 (assumes commitment is CR) |
| Submit witness for non-sovereign cell | `InvalidEffect { reason: "sovereign witness provided for non-sovereign cell ..." }` | Executor §2 |
| Submit a witness whose cell_id ≠ key | `InvalidEffect { reason: "sovereign witness cell ID mismatch" }` | Executor §2 |
| Swap witness on the wire (after cclerk signature) | Cipherclerk signature still verifies; Turn::hash v3 changes | **Open at the signature layer; partially caught at receipt-replay** |
| Omit witness from receipt but accept turn anyway | Hosted-table lookup fails, turn rejected | Executor (same accidental path as row 1) |
| Replay a witness in a future turn after the cell's commitment moved | Step 3 fails: `state_commitment != stored_commitment` | Executor §2 |
| Apply a Transfer on a sovereign cell with a witness but no cap | `verify_authorization` rejects via permission check | Executor §verify_authorization |
| Forge a proof-carrying turn (no witness, fake proof) | STARK verify fails | AIR (`verify_and_commit_proof`) |
| Lie about post-state inside the witness path (forest path) | Forest re-executes; post-state is recomputed by the executor, not taken from the witness | Executor §3478-3484 |

The last row is worth highlighting because it's *good news*: in
the witness path, the executor doesn't take a claimed post-state
from the turn — it computes the new commitment from
`cell.state_commitment()` after the journal-applied effects, then
calls `update_sovereign_commitment`. So the *post* side is
deterministic and not attacker-controlled. Only the *pre* side
needs binding, and the pre-side is anchored by `stored_commitment`.

## 8. Algebraic teeth verdict

**Sovereign witnesses are not algebraically constraining.** They
are a federation-side bookkeeping handshake: "you sent me a
preimage of the commitment I have on file, fine, I will let you
use it for one turn." There is no AIR column, no AIR constraint,
no PI slot bound to the witness. The Effect VM AIR is unaware that
the cell is sovereign for any purpose other than the
`MakeSovereign` once-only transition. The witness's only soundness
guarantee is "you can't lie about the pre-state because the
federation knows the commitment," which is a property of
`Cell::state_commitment` — not of the witness protocol.

The dedicated `T9` defense the EXECUTOR-HONESTY-AUDIT framework
hoped for ("AIR enforces the witness verifies before the
effect transition takes hold") does **not exist**. The framework's
claim — "sovereign witness columns exist; the AIR enforces the
witness verifies before the effect transition takes hold" — is
incorrect. There are no such columns.

What the framework *should* claim: for sovereign-cell turns, the
witness is enforced at the executor's PRE-AIR injection step, and
the post-state is computed (not asserted) by the executor. The
binding is at layer 2 (executor-classical), not layer 1 (AIR).
This is acceptable for federations that trust the executor to
admit only well-formed witnesses — i.e. the same trust model as
hosted cells — but it is **not** acceptable in a model where the
executor is allowed to be malicious. In that model, a malicious
executor would simply admit a witness that opens the stored
commitment (any cell preimage works; there's only one) and then
re-execute the effects however it wants, because the AIR does not
care about the witness. The post-state hash binding ensures the
*chain* head is honest in retrospect (the receipt commits to the
post-state via the ledger root and effects_hash), but a verifier
replaying the chain without re-doing the executor's work has no
way to distinguish "the agent authorised this transition" from
"the executor decided this transition on the agent's behalf."

The proof-carrying path (Phase 3) closes this gap, but it is the
*alternative* to the witness path, not an enhancement of it. The
two paths are mutually exclusive at construction. The witness
path remains the default for everything that hasn't been migrated
to proof-carrying form (per `sdk/src/cipherclerk.rs:4350-4416`).

## 9. Open questions for the designer

1. **Is the witness path intended to survive Stage 9 / 10, or is
   it a deprecated bridge to the proof-carrying path?** If it's a
   bridge, document the deprecation: list every site that still
   builds a `sovereign_witnesses`-populated turn (there are dozens
   in `node/`, `app-framework/`, `apps/`, `demo-agent/`,
   `teasting/`, `intent/`), and plan migration. If it's a long-term
   API, sections 9.2-9.5 below need answering.

2. **Should `SovereignCellWitness` carry a signature?** The
   peer-exchange analogue does. Adding a signature would close
   the "any-snooper-can-resubmit" gap (§2.2) and the
   "wire-malleability" gap (§6) in one stroke. The signing key
   would naturally be the *cell's* key (`cell.public_key`), not
   the agent's; the witness-issuer cert would be over
   `(cell_id, state_commitment, monotonic_sequence)`. This makes
   `SovereignCellWitness` isomorphic to a one-shot
   `PeerStateTransition`.

3. **Should the witness be in the AIR PI?** A minimal version
   would be: per-cell, include a `WITNESS_HASH` slot in PI,
   set to `BLAKE3(canonical(SovereignCellWitness))` (or just to
   the witness's signature bytes if §9.2 lands). The executor's
   PI-matching loop already does the binding for `EFFECTS_HASH`,
   `TURN_HASH`, etc. — wiring `WITNESS_HASH` through the same
   loop would give the witness genuine AIR teeth: a verifier who
   only has the proof and the receipt can detect any witness
   tampering without re-executing.

4. **What is the threat model for executors of sovereign-witness
   turns?** EXECUTOR-HONESTY-AUDIT.md frames the question as "if
   the executor is malicious, what does this catch?" For sovereign
   witnesses today, the answer is "not very much: the executor
   could omit the witness check, accept any preimage, or replay,
   and the chain would still hash-chain consistently because the
   *post-state* is honest by construction (recomputed from the
   journal)." The asymmetry is interesting and probably worth
   stating explicitly: sovereign-witness turns are honest about
   *what happened* but not necessarily about *whether the agent
   authorised it*.

5. **Why is `TurnError::SovereignWitnessRequired` dead code?**
   Either delete it (and the matching `LedgerError` variant) or
   wire it up at the point where the rejection actually happens
   (`execute_tree` at line 3706). The current "CellNotFound"
   message is a misleading footgun for anyone tracking down why a
   turn was rejected.

6. **Does `Cell::state_commitment` cover the cell's permissions,
   capabilities, program, and delegation slot?** Spot-checking
   `cell/src/commitment.rs::compute_canonical_state_commitment`
   would close out §6's caveat about side-data malleability. If
   it does (likely), then "swap the witness for another valid
   preimage" really is computationally infeasible for any
   non-trivial cell, and §6 collapses to the receipt-vs-signature
   domain-tag mismatch only.

7. **Is the `pyana-turn-v1:` → `pyana-turn-v3:` migration on the
   cclerk signing message planned?** P2-10 flags it as deferred
   to "Stage 9 (Receipts overhaul)." Closing T9 properly probably
   requires closing P2-10 first; otherwise even a witness with a
   signature is still wire-malleable through the SignedTurn
   wrapper.

8. **Multi-witness turns.** The schema (`HashMap<CellId,
   SovereignCellWitness>`) supports multiple sovereign cells per
   turn. The injection loop handles them sequentially. Is there a
   defined invariant about which sovereign cells *can* co-appear
   in a single turn (e.g. they all share a federation, they all
   sit under the same agent), and where is it enforced? Today the
   only constraint is "each must be registered sovereign in the
   ledger." The bilateral PI scheduling (Stage 7-γ.2) operates
   per-cell within a turn, so this is plausibly already addressed
   at the AIR layer for proof-carrying turns; for the witness
   path, no equivalent check exists.

## 10. Cross-references

- `turn/src/turn.rs:23-30` — `SovereignCellWitness` definition.
- `turn/src/turn.rs:149-275` — `Turn::hash` v3 (covers
  sovereign_witnesses).
- `turn/src/executor.rs:3258-3330` — sovereign witness injection
  and validation.
- `turn/src/executor.rs:3478-3484` — post-execution sovereign
  commitment update.
- `turn/src/executor.rs:3131-3249` — proof-carrying path (Phase 3,
  the algebraic-teeth alternative).
- `turn/src/executor.rs:1250-1588` — `verify_and_commit_proof` (the
  STARK-backed sovereign transition verifier).
- `turn/src/error.rs:158, 483` — `TurnError::SovereignWitnessRequired`
  (defined, never constructed).
- `turn/src/tests.rs:6975-7050` — confirms the no-witness
  rejection actually surfaces as `CellNotFound`.
- `cell/src/peer_exchange.rs:35-303` — the stronger
  `PeerStateTransition` analogue.
- `cell/src/ledger.rs:280, 963-1004` — sovereign commitment
  store.
- `sdk/src/cipherclerk.rs:4350-4554` — cipherclerk's two construction paths
  (`execute_sovereign_turn` vs `execute_sovereign_turn_with_proof`).
- `sdk/src/cipherclerk.rs:3852-3908` — `compute_turn_bytes` (the
  signed-message body that omits the witness; P2-10).
- `sdk/src/cipherclerk.rs:916` — `TURN_DOMAIN_PREFIX = b"pyana-turn-v1:"`.
- `tests/src/sovereign_proof.rs` — Phase 1 vs Phase 3 backward-
  compat test, demonstrating the mutual exclusion of the two
  paths.
- `circuit/src/effect_vm.rs` — Effect VM AIR; sovereign-related
  text only mentions the `MakeSovereign` transition and a
  `mode_flag` for the cell.
- `circuit/src/effect_vm/pi.rs` — Effect VM PI layout; no
  sovereign-witness PI slot.
- `EXECUTOR-HONESTY-AUDIT.md:164-174` — the T9 threat statement
  this audit answers.
