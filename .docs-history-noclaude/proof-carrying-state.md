# Proof-Carrying State: Design Direction

A design direction for collapsing pyana's dual-model architecture into a single
proof-centric model, where agent state IS a proof chain and federations shrink to
ordering/nullifier services.

---

## 1. Current Architecture: The Tension

Pyana currently has two models fighting each other:

### Model A: Federated Ledger

The `Ledger` struct (`cell/src/ledger.rs`) holds a `HashMap<CellId, Cell>` and
maintains a binary Merkle tree over all cells. Federation nodes run Morpheus
consensus to agree on a single root. The `AttestedRoot` (`federation/src/types.rs`)
covers this entire state tree with quorum signatures.

Key components:
- `Ledger::cells` -- the canonical state container
- `Ledger::rebuild_tree()` -- recomputes the Merkle root over all cells
- `MembershipProof` -- proves "cell X exists in the ledger with this state"
- `AttestedRoot { merkle_root, height, timestamp, qc }` -- the federation's
  signed commitment to the full state

In this model, the federation IS the authority. If you want to know a cell's
state, you ask the federation. If you want to prove a cell's state, you get a
`MembershipProof` against the `AttestedRoot`.

### Model B: IVC Proof Chain

The circuit layer (`circuit/src/ivc.rs`) already builds a completely independent
proof system. A `TurnReceipt` (`turn/src/turn.rs`) contains:

```rust
pub struct TurnReceipt {
    pub turn_hash: [u8; 32],
    pub forest_hash: [u8; 32],
    pub pre_state_hash: [u8; 32],   // <-- state BEFORE
    pub post_state_hash: [u8; 32],  // <-- state AFTER
    pub timestamp: i64,
    pub effects_hash: [u8; 32],
    pub computrons_used: u64,
    pub action_count: usize,
}
```

Each receipt chains: `receipt[n].post_state_hash == receipt[n+1].pre_state_hash`.
This is already a state proof chain.

Meanwhile, `IvcProof` (`circuit/src/ivc.rs`) proves an arbitrary-length fold
chain in constant size:

```rust
pub struct IvcProof {
    pub initial_root: BabyBear,
    pub final_root: BabyBear,
    pub step_count: u32,
    pub accumulated_hash: BabyBear,
    pub proof: MockProof,
    pub trace_commitment: [u8; 32],
}
```

And `FoldDelta` (`commit/src/fold.rs`) proves attenuation history as a running
accumulation, with each step carrying membership proofs for removed facts.

### The Problem

These two models assign different authorities:

- Model A says: "The federation holds your state. Ask it for proofs."
- Model B says: "Your proof chain IS your state. Anyone can verify it."

When the executor (`turn/src/executor.rs`) commits a turn, it updates the Ledger
AND produces a TurnReceipt. The Ledger is treated as the source of truth (you
need a `MembershipProof` to prove state to third parties). The TurnReceipt is
treated as a side-effect (logged but not required for state validity).

This is backwards.

---

## 2. The SOTA Model: State as Proof

The state-of-the-art (Mina, Aleo, Anoma) says: lean into Model B. Each agent
carries their own state as a proof chain. The federation provides ordering
(preventing double-spends) but never holds state.

| Current | SOTA |
|---------|------|
| `Ledger` holds cells, produces Merkle proofs | Cells are self-proving via IVC chain |
| `AttestedRoot` covers the whole state tree | `AttestedRoot` covers only the nullifier set |
| `MembershipProof` proves "cell exists in tree" | Unnecessary -- IVC proof proves validity |
| `NullifierSet` is per-federation, position-dependent | Nullifiers are global, position-independent |
| Exit = export bundle + ceremony | Exit = stop using this ordering service |
| `TurnReceipt` is a side-effect | `TurnReceipt` chain IS the state |

### What "state as proof" means concretely

An agent's state is a tuple:

```
(current_state_commitment, proof_chain)
```

Where `proof_chain` is a sequence of TurnReceipts satisfying:

```
for i in 1..n:
    proof_chain[i].pre_state_hash == proof_chain[i-1].post_state_hash
```

Anyone can verify the chain from genesis without contacting a federation. The
chain itself is the proof that the state is valid -- it was produced by a
sequence of valid turns, each of which was checked by the executor.

For efficiency, the IVC layer compresses the entire chain into a constant-size
`IvcProof`. A verifier only needs:
1. The `IvcProof` (proves the chain is valid)
2. The current state commitment (proves what state the chain produced)
3. A nullifier non-membership proof (proves no double-spends)

### The federation's remaining role

The federation becomes an ORDERING SERVICE, not a STATE CONTAINER:

- "I saw these nullifiers in this order, no double-spends"
- "Here is the current nullifier set root, with quorum attestation"
- "Here is proof that nullifier X is NOT in the set (your note is unspent)"

This is exactly what `NullifierSet` (`cell/src/nullifier_set.rs`) already does --
an append-only set with non-membership proofs. The federation just needs to do
THAT, consensus-attested.

---

## 3. What This Means Concretely

### Agent lifecycle

1. **Genesis**: Agent creates a cell. The federation records the cell's genesis
   commitment and the note commitment in the note tree.

2. **Turns**: Agent submits a turn. The executor validates it locally, produces
   a `TurnReceipt`, and the agent appends it to their proof chain. Nullifiers
   from spent notes are submitted to the federation for ordering.

3. **Presentation**: To prove state to a third party, the agent presents their
   `IvcProof` (or the relevant suffix of their receipt chain). No federation
   involvement needed.

4. **Interaction**: To interact with another agent, present your proof chain
   (proving your current capabilities) and compose a multi-party turn.

5. **Exit**: Stop submitting nullifiers to this federation. Your proof chain is
   portable. Join another ordering service, or operate standalone (accepting the
   risk of undetected double-spends from notes you received on the old
   federation).

### What the federation DOES attest

```rust
// Current (too much):
pub struct AttestedRoot {
    pub merkle_root: [u8; 32],  // root over ALL cells -- heavy
    pub height: u64,
    pub timestamp: i64,
    pub qc: Option<ThresholdQC>,
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    pub threshold: usize,
}

// SOTA (minimal):
pub struct AttestedRoot {
    pub nullifier_root: [u8; 32],  // root over spent nullifiers only
    pub note_tree_root: [u8; 32],  // root over note commitments
    pub height: u64,
    pub timestamp: i64,
    pub qc: Option<ThresholdQC>,
    pub threshold: usize,
}
```

The federation attests to:
- Which notes exist (note tree)
- Which notes are spent (nullifier set)

It does NOT attest to cell state. Cell state is proved by the cell's own chain.

---

## 4. Migration Path

### Phase 1: TurnReceipt chains become the primary state representation

Keep the `Ledger` but make it a cache/index rather than the source of truth.

Changes:
- Add a `receipt_chain: Vec<TurnReceipt>` field to each agent's local state
  (in `sdk/src/wallet.rs` or equivalent)
- The executor still updates the Ledger (for fast lookups), but the chain is
  what you present to others
- `IvcBuilder` wraps receipt production: each turn that commits also extends
  the IVC accumulation
- Verification of a cell's state can use EITHER a `MembershipProof` (old path)
  OR an `IvcProof` (new path)

Existing code affected:
- `TurnExecutor::execute()` -- already produces `TurnReceipt`, no change needed
- `Ledger::membership_proof()` -- still works, used as fast-path
- `IvcBuilder` -- already exists, just needs to be wired into the executor flow

### Phase 2: AttestedRoot covers only nullifiers + ordering

Narrow what the federation attests to:

- `AttestedRoot.merkle_root` becomes `nullifier_root` + `note_tree_root`
- Federation consensus operates on nullifier batches, not cell state
- The `RevocationTree` in `federation/src/revocation.rs` already does exactly
  this for token revocation -- extend it to cover note nullifiers

Changes:
- `federation/src/node.rs` stops maintaining a cell Merkle tree
- `federation/src/types.rs` `AttestedRoot` fields change
- `NullifierSet::root()` becomes the value the federation attests
- Consensus proposals become "batches of new nullifiers" rather than
  "blocks of state updates"

### Phase 3: Remove Ledger as source-of-truth

The Ledger becomes a local index (like a database cache). It can be reconstructed
from the proof chain.

- Remove `MembershipProof` as a required input for state validity
- `Ledger` becomes `LocalIndex` -- kept for fast local lookups
- Third-party verification uses only `IvcProof` + nullifier non-membership
- The `bridge` crate's presentation proofs use IVC proofs directly
  (`IvcPresentationProof` already exists in `circuit/src/ivc.rs`)

---

## 5. What We Keep

Everything structural survives:

- **Cells** (`cell/src/cell.rs`): Still the state format. 8 field slots, nonce,
  balance, permissions, capabilities. The cell is what the proof chain proves
  transitions over.

- **Programs** (`cell/src/program.rs`): Predicates and circuits still define
  valid transitions. The executor still checks them. The proof chain proves that
  every transition was program-valid.

- **Notes + Nullifiers** (`cell/src/note.rs`, `cell/src/nullifier_set.rs`):
  Still the privacy mechanism. Notes are the UTXO-like private state layer.
  Nullifiers still prevent double-spends.

- **The Executor** (`turn/src/executor.rs`): Still validates turns. Still does
  journal-based atomicity. Still checks preconditions, authorization, programs,
  balance conservation. The executor is the transition function that the proof
  chain proves correct.

- **The Circuit Layer** (`circuit/src/`): Still proves things. The IVC system
  (`ivc.rs`) already provides exactly the compression needed. The fold AIR
  (`fold_air.rs`) proves attenuation chains. The derivation AIR
  (`derivation_air.rs`) proves authorization derivation.

- **Federation Consensus** (`federation/src/consensus.rs`): Still orders
  transactions. The Morpheus protocol still prevents equivocation. Threshold QCs
  (`federation/src/threshold.rs`) still attest.

---

## 6. What Changes

### MembershipProof becomes optional for named cells

Currently, to prove "my cell has state X", you get a `MembershipProof` from the
ledger. In the SOTA model, you present your IVC proof chain instead. The chain
proves your state is valid by construction -- every transition from genesis was
executor-validated.

`MembershipProof` is still needed for ONE thing: **notes**. To spend a note, you
prove the note commitment exists in the note tree. That tree is federation-maintained.
So `MembershipProof` survives but only in the context of `store/src/note_tree.rs`.

### AttestedRoot shrinks

From:
```
AttestedRoot { merkle_root (over all cells), height, timestamp, qc }
```

To:
```
AttestedRoot { nullifier_root, note_tree_root, height, timestamp, qc }
```

The federation stops attesting to cell state. It only attests to the note tree
(what notes exist) and the nullifier set (which are spent).

### Exit becomes trivial

Currently, "exiting" a federation would require extracting your cell state and
getting the federation to sign off on it. In the SOTA model, your proof chain
is already self-contained. To "exit":

1. Stop submitting nullifiers to this federation
2. Join another ordering service (submit your proof chain as your genesis state)
3. Or operate standalone (trusting that nobody double-spends notes you hold from
   the old federation)

The proof chain is portable because it doesn't reference federation-specific
state -- it only proves that transitions were valid.

### `proved_state` becomes always-true (conceptually)

The `proved_state: bool` on `CellState` exists to distinguish "state set by a
verified proof" from "state set by a signature." In the SOTA model, every state
transition is part of a proof chain, so every state is "proof-produced" in the
sense that the chain proves it was produced by valid execution.

The field still has operational meaning (was THIS transition authorized by a ZK
proof vs. a signature?) but the higher-level question "is this state valid?" is
always answered by the proof chain, not by a per-field flag.

---

## 7. The Tradeoff

### What we lose: inspectable shared ledger

In the current model, federation members can look up any cell's state via the
shared ledger. This is useful for:

- Cloud API / "trusted mode": query cell state without the cell being online
- Debugging: inspect any agent's state
- Indexing: build analytics over all cells

In the SOTA model, you can only learn a cell's state if the cell presents its
proof chain to you. This is MORE PRIVATE but LESS CONVENIENT.

### The mitigation: shared ledger as optimization

For the trusted mode / cloud API use case, maintain the shared ledger as a
CACHE -- a convenience index of the latest cell states, backed by proof chains
as the authoritative source:

```
Client queries "what is cell X's balance?"
-> Cloud API looks up local index (fast path)
-> If stale/untrusted: request proof chain from agent (authoritative path)
```

The ledger-as-cache is fine because it's not the source of truth. It can be
wrong (stale, incomplete) without breaking security. The proof chain is what
matters for any security-critical operation.

This means `Ledger` in `cell/src/ledger.rs` survives as-is from an API
perspective -- it's just re-framed as "local index" rather than "global truth."

---

## 8. Relationship to Existing Features

### Balance change + excess tracking

Still enforced per-turn by the executor. The proof chain proves that every turn
conserved value (excess == 0 at turn end). A verifier checking the IVC proof
knows conservation held at every step without re-executing.

### Cell programs

Still checked by the executor on each transition. The proof chain proves that
every transition satisfied the cell's program constraints. For `Circuit` programs,
the inner proof (the action's `Authorization::Proof`) is what the executor verified;
the outer IVC proof proves the executor accepted it.

### Progressive disclosure

Still works. A cell chooses which fields are `Public`, `Committed`, or
`SelectivelyDisclosable` (`cell/src/state.rs`). When presenting state to a
verifier, the agent reveals what they want from their proof chain. The verifier
can check that the revealed fields are consistent with the state commitment in
the chain.

### Multi-party composition

Still works. Multiple agents present their proof chains (proving their current
state and capabilities), then compose a multi-party turn. The executor validates
the composed turn. Each party gets a receipt extending their individual chain.

### Attenuation (fold chains)

Becomes even more natural. The `FoldDelta` chain (`commit/src/fold.rs`) already
IS a proof-carrying state model for token capabilities. The IVC layer already
compresses these into constant-size proofs. The SOTA model just extends this
pattern from "capabilities" to "all state."

---

## 9. Open Questions

### Discovery

How do you discover other agents' capabilities if you can't inspect the ledger?

Options:
- **Bulletin board**: Agents publish capability advertisements (encrypted for
  interested parties)
- **Directory service**: A public index of agent capabilities (opt-in)
- **Direct negotiation**: Agents exchange proof excerpts during interaction setup

This is unsolved but not unique to pyana -- Anoma and Zcash face the same problem.

### Trusted mode / cloud API

How does "I trust the server to hold my state" work?

The server maintains the full proof chain on behalf of the agent. The agent can
request their chain at any time (for portability/verification). The server acts
as both local index (for queries) and proof chain custodian (for the agent).

This is equivalent to "hosted wallet" -- the security model is that you trust the
server, and the proof chain provides an exit path if you stop trusting it.

### Recovery

What happens if you lose your proof chain?

Options:
- **Checkpoint**: The federation periodically publishes attested snapshots. If
  you lose your chain, you can restart from the last checkpoint (losing the
  ability to prove history before that point, but maintaining current state).
- **Custodial backup**: Store encrypted proof chain with a third party.
- **Note tree as anchor**: Your notes are in the federation's note tree. Even
  without your proof chain, you can prove note ownership via the tree + your
  spending key. You lose named-cell state but keep private balances.

### Proof size in practice

The `IvcProof` currently uses `MockProof` (simulated constant size of 128 KiB).
Real recursive STARKs (Plonky3, SP1) produce proofs in the 100-500 KiB range
regardless of chain length. This is acceptable for async verification but may be
too large for latency-sensitive interactions.

Possible mitigations:
- SNARK wrapping (compress STARK proof into a Groth16/PLONK proof, ~300 bytes)
- Proof caching at checkpoints (only prove the suffix since last checkpoint)
- Trust tiers (close collaborators skip verification; strangers get full proofs)

### Interaction with the token/attenuation layer

The `FoldDelta` chain in `commit/src/fold.rs` operates over `TokenState` (fact
sets), while `TurnReceipt` chains operate over `CellState` (field slots). These
are currently separate state models.

In the unified SOTA model, both should be proof-carrying. The question is whether
they share a single IVC chain or maintain parallel chains that cross-reference.
Likely answer: a cell's proof chain proves cell state transitions, and a
separately-carried fold chain proves capability attenuation. The two are linked
at verification time ("this IVC proof chain ends at state S, and this fold chain
proves I hold capabilities C derived from that state").

---

## 10. Implementation Priority

1. **Wire IvcBuilder into the executor flow** -- each committed turn extends
   the agent's IVC accumulation. This is additive (no breaking changes).

2. **Add receipt chain to the SDK wallet** -- agents carry their receipt history
   locally. Still use Ledger for federation-side lookups.

3. **Add IvcProof as an alternative to MembershipProof in the bridge layer** --
   `bridge/src/present.rs` already does presentation proofs. Add an IVC-based
   presentation path alongside the Merkle-based one.

4. **Narrow AttestedRoot** -- federation attests to nullifier + note tree roots
   only. Cell state is no longer federation-attested.

5. **Deprecate cell MembershipProof** -- replace with IVC verification for
   cell state validity. Keep note tree membership proofs.

Steps 1-3 are additive and can land incrementally. Steps 4-5 are the actual
model change and should wait until the IVC path is battle-tested.
