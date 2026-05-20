# Private Programmable State Models: Research for Pyana

This document compares private state models across leading ZK systems to inform pyana's
design direction toward private DEX, auctions, and smart contracts with progressive disclosure.

---

## 1. System Summaries

### 1.1 Aztec (Noir / Aztec.nr)

Aztec is a hybrid ZK rollup on Ethereum that supports **both private and public state** within
a single smart contract. Private state uses a UTXO/note model: data lives as encrypted "notes"
in an append-only Merkle tree (the "note hash tree"). To modify private state, you destroy old
notes (by revealing their nullifier) and create new notes. The nullifier tree is an indexed
Merkle tree (linked list of increasing values at depth 32 rather than sparse depth 254) that
efficiently proves non-membership.

**Private-public composition** uses a dual call-stack model. Private functions execute
client-side in the PXE (Private eXecution Environment), generating ZK proofs. These can enqueue
public function calls that execute on the sequencer. A "partial notes" system allows a private
function to create an incomplete note (missing some field, like the exact amount) which a
subsequent public function completes. This enables patterns like: "place a private order" then
"fill at the publicly-determined price." The kernel circuit recursively validates each function
call, private first, then public.

Aztec uses **Noir** as its DSL, compiling to ACIR (Abstract Circuit Intermediate Representation),
then proving with Barretenberg (UltraPlonk / Honk). Every account is a smart contract (native
account abstraction). The sequencer only sees proofs and nullifiers — never the private function
being called or its arguments.

### 1.2 Penumbra

Penumbra is a shielded DEX and staking chain built on CometBFT (Cosmos SDK). Its privacy model
adapts Zcash Sapling's note/nullifier scheme: an incremental Merkle tree stores commitments to
private notes, and spending reveals a nullifier derived one-way from the note contents. The
nullifier set prevents double-spending without revealing which note was spent.

**Shielded swaps** use a two-phase batch auction model inspired by Budish, Cramton & Shim's
research on eliminating HFT front-running. Phase 1: users create swap actions that publicly burn
input assets (trading pair and amounts currently visible, sealed-bid encryption planned). Phase 2:
all swaps within a block are batched together and executed against concentrated liquidity
positions at a uniform clearing price. Users then claim outputs privately via SwapClaim actions
(requiring only viewing keys, no spend authority). This eliminates front-running because there's
no ordering within a batch.

Penumbra's DEX uses individual constant-sum concentrated liquidity positions (each LP creates
price-range positions revealing amounts and bounds but not identity). The system routes trades
through a graph of these positions. Privacy tradeoff: swap amounts are currently public at
submission (sealed-bid planned via flow encryption), but individual trader identity is hidden
through the shielded pool. The protocol explicitly acknowledges limited privacy when batch sizes
are small.

### 1.3 Aleo (Leo / snarkVM)

Aleo uses a **record model** — an enriched UTXO where each record contains an owner address,
arbitrary typed data fields (each independently marked public or private), a nonce, and a version.
Records differ from raw UTXOs by supporting: (1) encrypted owner identity, (2) per-field
visibility control, (3) arbitrary application data beyond simple values, and (4) parallel
execution (no global state bottleneck).

**Transition/finalize composition**: A "transition" is a private execution that consumes input
records and produces output records, generating a ZK proof (using Varuna, a variant of Marlin).
A transition can optionally include a "finalize" block — public on-chain logic that runs after
the private proof is verified. The finalize phase can read/write public mapping state (key-value
store). This two-phase model means: private logic proves correctness off-chain, public logic
updates shared state on-chain. Serial numbers (derived from records) are revealed publicly to
prevent double-spending — functionally identical to nullifiers.

Aleo's proof system is **Varuna** (evolved from Marlin), a universal SNARK based on polynomial
IOPs. Programs compile to R1CS constraints via the Aleo Virtual Machine (AVM) instruction set.

### 1.4 Zcash Orchard

Orchard is Zcash's third-generation shielded protocol, deliberately simplifying Sapling while
improving privacy. Its key innovation: **every action is simultaneously a spend and an output.**
This hides transaction structure — observers cannot tell how many inputs vs outputs a transaction
has (unlike Sapling where separate spends and outputs leaked the "shape").

**Note structure**: `(address, value, rho, psi, rcm)` where `rho` chains from the nullifier of
the spent note (ensuring uniqueness), `psi` provides sender-controlled randomness, and `rcm` is
the randomness for the note commitment. Commitments use Sinsemilla (efficient in PLONK circuits).

**Nullifier derivation**: `nf = ExtractP([(F_nk(rho) + psi) mod p] * G + cm)` where `F` is a
keyed PRF, `nk` is the nullifier deriving key (tied to spending authority), and `G` is a fixed
base point. This design achieves: (1) only the spending key holder can derive the nullifier,
(2) each note has exactly one nullifier (preventing double-spend), (3) the nullifier reveals
nothing about the note (unlinkability), (4) "Faerie Resistance" (can't trick someone into
accepting an unspendable note) under relatively weak assumptions (DLE only).

Orchard uses **Halo 2** (recursive proof composition without trusted setup) over the Pallas/Vesta
curve cycle, with PLONK arithmetization.

### 1.5 Mina (zkApps)

Mina takes a fundamentally different approach: **account-based model with committed off-chain
state.** Each zkApp account has 8 on-chain field elements (32 bytes each) that can store either
plaintext values or commitments to larger off-chain structures (like Merkle tree roots). The
zkApp proves correct state transitions via zk-SNARKs (Kimchi, a Plonk variant) without revealing
private inputs.

**Actions** are an append-only sequence of public events dispatched by contracts. A "reducer"
processes accumulated actions to produce state updates. Actions MUST commute (order-independent
application) to handle concurrency. This is NOT privacy — actions are public on-chain. Mina's
privacy story is weaker: you can commit to private state (Merkle root of private data) and prove
predicates over it without revealing it, but the account model means all interactions with an
account are publicly linked (same address). There's no equivalent to the anonymity set that
note/nullifier models provide.

**Key limitation**: In an account model, every transaction targeting the same account is publicly
linked. The "who" is always visible even if the "what" can be hidden behind commitments. True
privacy for financial transactions (hiding both sender and receiver) fundamentally requires
consumption/creation patterns — you can't just commit private state to an account and get
meaningful transaction privacy.

---

## 2. Comparison Table

| Property | Aztec | Penumbra | Aleo | Zcash Orchard | Mina |
|----------|-------|----------|------|---------------|------|
| **State model** | Notes (UTXO) + public storage | Notes (UTXO) | Records (enriched UTXO) | Notes (UTXO) | Accounts with committed state |
| **Privacy model** | Full: hide function, args, sender | Shielded pool: hide identity, partial amounts | Per-field visibility on records | Full: hide everything including tx shape | Committed state only; accounts publicly linked |
| **Proof system** | UltraPlonk/Honk (Barretenberg) | Groth16 (decaf377) | Varuna (Marlin variant) | Halo 2 (PLONK, no trusted setup) | Kimchi (Plonk variant) |
| **Nullifier mechanism** | Indexed Merkle tree (depth 32) | Nullifier set (append-only) | Serial numbers from records | PRF-based, single action = spend+output | N/A (nonces on accounts) |
| **Private-public composition** | Dual call stack; partial notes | Swap = public burn + private mint | Transition (private) + finalize (public) | Purely private (no public contracts) | Committed state + public preconditions |
| **DEX capability** | Private orders, public fills via partial notes | Batch auctions with uniform clearing | Record-based atomic swaps | N/A (no programmability) | Possible but all interactions publicly linked |
| **PQ-ready** | No (elliptic curves) | No (elliptic curves) | No (elliptic curves) | No (elliptic curves) | No (elliptic curves) |
| **Programmability** | Full (Noir contracts) | Fixed protocol (no user contracts) | Full (Leo/Aleo instructions) | None (fixed transfer protocol) | Full (o1js / TypeScript) |
| **Anonymity set** | All notes in note hash tree | All notes in state commitment tree | All records on chain | All notes in commitment tree | None (account addresses are public) |

---

## 3. Key Questions Answered

### 3.1 UTXO vs Account Model for Privacy

**Why most private systems choose UTXO/notes**: The fundamental reason is that an account model
publicly links ALL interactions to the same address. Even if you hide the transaction content
behind commitments, observers can see: "address X transacted at time T1, T2, T3" and correlate
patterns. With notes, spending a note reveals only a nullifier (unlinkable to the note
commitment) and creates a new note commitment (unlinkable to the nullifier). The anonymity set
is the entire note tree.

**Tradeoffs**:
- UTXO/notes: Strong anonymity, natural parallelism, but state fragmentation (you own many
  notes rather than one account), complexity in programming (must "consume and recreate" rather
  than "update"), and difficulty with shared mutable state (e.g., a DEX order book).
- Accounts: Simple programming model, easy shared state, but weak privacy even with commitments,
  sequential bottleneck on popular accounts, and public interaction graph.

**Can pyana's cells achieve meaningful privacy?** Partially. The `FieldVisibility::Committed`
and `SelectivelyDisclosable` modes hide WHAT is in a cell. But they cannot hide WHO is
interacting with a cell or WHEN interactions happen. For authorization (pyana's primary use case),
this may be sufficient — the verifier sees a proof but not which cell generated it. For financial
applications (DEX, auctions), the account model leaks interaction patterns that reveal trading
behavior. Meaningful financial privacy REQUIRES either: (1) a note/nullifier layer on top of
cells, or (2) a mixing/batching approach like Penumbra's.

### 3.2 Nullifiers: What They Are and Why They're Necessary

A **nullifier** is a deterministic, unique identifier derived from a note that can only be
computed by the note's owner (holder of the spending key). Properties:

1. **Deterministic**: Each note has exactly one nullifier (prevents double-spend).
2. **One-way**: Given a nullifier, you cannot determine which note commitment it corresponds to
   (unlinkability).
3. **Owner-bound**: Only the spending key holder can compute it (prevents unauthorized spending).
4. **Publicly revealed**: When you spend, you publish the nullifier. The network checks it's not
   in the nullifier set.

**Does pyana NEED nullifiers?** It depends on what you're doing:
- **For authorization tokens (current use case)**: No. Pyana's revocation non-membership proofs
  serve a similar role — they prove "this token has NOT been revoked" which prevents replay. The
  difference: revocation is authority-initiated (the issuer revokes), whereas nullifiers are
  owner-initiated (the holder spends). For capability tokens that are presented (not transferred),
  revocation-based invalidation is actually more appropriate.
- **For transferable value (DEX, auctions)**: YES. If pyana introduces transferable assets
  (tokens, order fills), you need a mechanism where the HOLDER invalidates the old state when
  transferring. Revocation won't work because the issuer shouldn't need to be involved in every
  transfer. Nullifiers solve exactly this: holder-initiated, deterministic invalidation without
  authority participation.

### 3.3 The "State Tree" Problem

In Aztec's model, two trees compose:
1. **Note hash tree** (append-only): Contains commitments to all ever-created notes. When you
   create a note, its hash is appended. Notes are NEVER removed.
2. **Nullifier tree** (indexed, grows monotonically): When you spend a note, its nullifier is
   inserted. Nullifiers are NEVER removed.

The relationship:
- "I committed this note": prove membership of note_hash in the note hash tree.
- "This note is unspent": prove NON-membership of the note's nullifier in the nullifier tree.
- Both proofs together = "this note exists AND has not been spent."

Aztec's indexed Merkle tree innovation (linked list of sorted values, depth 32 instead of 254)
makes non-membership proofs 8x cheaper in circuits. Pyana's current 4-ary Merkle tree with
sorted leaves and adjacency-based non-membership proofs is conceptually similar but uses a
different encoding.

### 3.4 Composability of Private and Public State

**The DEX problem**: How do you make orders private but fills publicly verifiable?

**Aztec's approach** (partial notes):
1. Private function creates an "incomplete" note missing the fill amount.
2. Private function enqueues a public call to the DEX contract.
3. Public DEX contract determines the price, computes the fill amount.
4. Public function "completes" the partial note with the determined value.
5. The completed note hash is added to the note hash tree.
6. The trader's identity is never revealed publicly.

**Penumbra's approach** (batch auctions):
1. User creates a swap action: publicly burns input tokens (amount currently visible).
2. All swaps in a block are batched together (no ordering within a batch).
3. Concentrated liquidity positions determine the clearing price.
4. User claims output privately via SwapClaim (only needs viewing key).
5. Privacy: individual trades hide in the batch. Planned: seal amounts via flow encryption.

**Key insight for pyana**: Both approaches separate "intent declaration" from "settlement."
Aztec makes the intent private and settlement public. Penumbra makes the intent semi-public
(amounts visible now, sealed later) and settlement private. Both work, but Penumbra's approach
is simpler (no programmable contracts needed) while Aztec's is more general.

### 3.5 What Pyana Already Has That Maps to These Concepts

| Pyana Concept | Maps To | Notes |
|---------------|---------|-------|
| Merkle commitments (4-ary tree) | Note commitments / state commitment tree | Same idea: commit to private data, prove membership |
| Non-membership proofs (sorted adjacency) | Nullifier non-membership checks | Similar mechanism, different purpose (revocation vs spending) |
| `FieldVisibility::Committed` | Shielded state fields | Hides value behind commitment; can prove predicates |
| `FieldVisibility::SelectivelyDisclosable` | Selective disclosure (beyond what most systems offer) | Pyana actually has finer-grained disclosure than Aztec/Penumbra |
| Fold chain (attenuation) | Note consumption chain | Each fold "narrows" — creates new state from old. Conceptually similar to spend-and-recreate |
| Revocation non-membership | Nullifier check (but issuer-driven) | Proves token NOT revoked. Similar proof structure, different trust model |
| Cell state (8 fields + nonce) | Mina zkApp account | Directly adapted from Mina. Same limitations for privacy |
| Turn call forest | Aztec's transaction kernel / Mina's zkApp command | Atomic multi-action composition |
| `CommitmentMode::Partial` (action signing) | Aztec's multi-party transaction composition | Allows signers to authorize their part without seeing others |
| STARK proofs (BabyBear + FRI) | Proof of correct execution | PQ advantage over all compared systems |
| Computron budgets | Gas/fee mechanism | But lacks the value-transfer semantics that DEX needs |

**What's MISSING for private financial applications**:

1. **Nullifiers (holder-initiated invalidation)**: Current revocation is issuer-driven. For
   transferable value, holders must be able to "spend" (invalidate) their own state without
   issuer involvement.

2. **Note/record model for transferable assets**: Cells are accounts (publicly addressable).
   For private value transfer, you need notes that are owned but not publicly linked to an
   address.

3. **Value commitments (homomorphic)**: Penumbra and Orchard use Pedersen commitments where
   you can verify `commit(a) + commit(b) = commit(a+b)` without revealing a or b. This is
   essential for proving conservation (total value in = total value out) in private transactions.
   Pyana's BLAKE3 commitments are binding but not homomorphic.

4. **Encrypted note transmission**: When you create a note for someone else, you need to
   encrypt it to their key so they can discover and spend it. Pyana has X25519 sealed secrets
   but hasn't integrated this with the state model.

5. **Batch execution / clearing mechanism**: For a DEX, you need either Penumbra-style batching
   or Aztec-style partial notes. Neither exists in pyana yet.

6. **Asset/token type system**: Pyana's cells have `token_id` but this identifies the capability
   domain, not a fungible asset. A DEX needs typed fungible assets with privacy.

### 3.6 What Would a Pyana-Native Private DEX Require?

Given existing primitives (cells, turns, Datalog auth, STARK proofs, Merkle commitments, fold
chains), here's the minimum addition set:

**Tier 1 — Foundational (required for any private value transfer)**:
1. **Nullifier derivation**: Add `nf = Poseidon2(nk, note_commitment)` where `nk` is derived
   from the cell's spending key. Nullifier tree as an additional indexed structure alongside
   the existing Merkle tree.
2. **Note type**: A new primitive `Note { owner_commitment, asset_id, value, blinding, nonce }`
   that lives in the note hash tree (separate from cells).
3. **Value commitments**: Pedersen commitments over BabyBear (or switch to a curve that supports
   homomorphic operations). Alternatively, use range-proof-constrained field commitments.
4. **Conservation constraint**: In the turn executor, verify that the sum of all value
   commitments in spent notes equals the sum in created notes (plus fees).

**Tier 2 — DEX-specific**:
5. **Order notes**: Specialized notes encoding limit orders `{ asset_in, asset_out, max_price,
   amount, owner_commitment }`.
6. **Batch clearing**: A privileged "sequencer turn" that collects order notes, computes
   clearing price, and creates fill notes. Similar to Penumbra's swap/claim pattern.
7. **Partial note completion**: Allow a note to be created with a "hole" (unknown value) that
   gets filled by a public computation (the clearing price determination).

**Tier 3 — Privacy enhancements**:
8. **Encrypted note discovery**: Integrate X25519 sealed secrets with note creation so
   recipients can scan for their notes without revealing ownership.
9. **Sealed-bid amounts**: Encrypt order amounts to the sequencer set (threshold decryption
   using the existing BLS12-381 hints infrastructure).
10. **Anonymity set growth**: Notes need sufficient volume to provide meaningful privacy.
    Consider dummy notes / cover traffic during low-activity periods.

---

## 4. Recommendation: Hybrid Model

**Neither pure UTXO+nullifiers NOR pure enhanced-account is right for pyana.**

The recommendation is a **dual-layer hybrid**:

### Layer 1: Cells (account model) — for authorization and coordination

Keep the existing cell model for what it's good at:
- Agent authorization (the primary use case)
- Coordination state (nonces, budgets, permissions)
- Public/committed parameters that don't need anonymity
- Programs that define valid state transitions

This is where pyana is already strong and differentiated.

### Layer 2: Notes (UTXO model) — for private value and trading

Add a note layer for transferable private value:
- Notes live in a separate note hash tree (append-only)
- Nullifiers in a separate nullifier tree (indexed, Aztec-style)
- Notes are created/consumed within turns (same execution model)
- A cell can "mint" notes (authorized by its program)
- A cell can "absorb" notes (convert note value back to cell balance)

This gives you:
- Private DEX orders (notes with order parameters)
- Private fills (new notes created by the clearing mechanism)
- Anonymous value transfer (spend note, create note for recipient)
- While keeping the simpler account model for non-financial state

### Why hybrid?

1. **Authorization doesn't need notes.** Pyana's primary value is ZK presentation of
   capabilities. That's a proof-about-committed-state problem, not a value-transfer problem.
   Cells with committed fields are perfect for this.

2. **Value transfer needs notes.** The moment you want "Alice pays Bob without revealing Alice
   or Bob," you need the anonymity set that notes provide. Accounts can't do this.

3. **DEX needs both.** The DEX contract lives in a cell (public program logic, price discovery).
   Orders and fills are notes (private ownership, private amounts). The cell program authorizes
   which note transformations are valid.

4. **Pyana's STARK advantage compounds.** Notes + nullifiers are more expensive in PLONK
   (Aztec, Orchard) than in STARKs. Pyana's BabyBear STARK with Poseidon2 makes Merkle proofs
   cheap. A 4-ary indexed tree at depth 16 with Poseidon2 is very STARK-friendly.

---

## 5. What to Build Next (Prioritized)

### Phase 1: Note Primitives (required foundation)

1. **`pyana-note` crate**: Define `Note`, `NullifierKey`, `NullifierDerivation`. A note is
   `{ owner_pk_hash, asset_id, value, blinding, rho }`. Nullifier is
   `Poseidon2(nk, commitment(note))`.

2. **Note hash tree**: Append-only 4-ary Merkle tree (can reuse existing `commit/` code).
   Separate from the fact-set trees used for authorization.

3. **Nullifier tree**: Indexed variant of the existing Merkle tree that supports efficient
   non-membership proofs (adapt the sorted-leaf design to an indexed structure).

4. **Conservation AIR constraint**: New circuit component proving
   `sum(input_values) = sum(output_values) + fee`. Needs range proofs or value commitments.

### Phase 2: Integration with Execution Model

5. **Turn actions for notes**: New `Effect` variants: `MintNote`, `SpendNote` (with nullifier),
   `CreateNote`. The turn executor validates conservation and nullifier freshness.

6. **Cell-to-note bridge**: Cell programs can authorize note minting (converting cell balance
   to notes) and note absorption (converting notes back to cell balance).

7. **Encrypted note delivery**: When creating a note for another party, encrypt the note
   plaintext to their public key. Store ciphertext alongside the commitment.

### Phase 3: DEX Application

8. **Order note type**: Encode limit orders as notes with additional metadata.

9. **Batch clearing mechanism**: A sequencer-executed turn that collects unfilled orders,
   computes clearing prices, and produces fill notes. Can use Penumbra's approach (simpler)
   or Aztec's partial-note approach (more flexible).

10. **LP positions**: Concentrated liquidity as public cell state (Penumbra-style: positions
    reveal parameters but not owner identity).

### Phase 4: Privacy Hardening

11. **Sealed-bid encryption**: Use BLS threshold decryption (existing `hints` crate) to
    encrypt order amounts so only the sequencer committee can see them during matching.

12. **Viewing key hierarchy**: Spending key -> nullifier key -> incoming viewing key.
    Allow delegation of scan-only access without spending authority.

13. **Dummy notes / cover traffic**: Mechanism for padding transactions to fixed sizes
    (like Orchard's action = spend + output approach).

---

## 6. Honest Assessment: What We Cannot Do

### Cannot do with current primitives (require fundamental additions):

- **Anonymous value transfer**: Cells are publicly addressed. Period. Need notes.
- **Homomorphic balance verification**: BLAKE3 commitments aren't homomorphic. Need either
  Pedersen commitments (not PQ) or a different approach (range proofs over field commitments,
  or Bulletproofs-style protocols adapted for STARKs).
- **Hide transaction shape**: Currently turns reveal how many actions they contain. Would need
  padding or Orchard-style "every action is both spend and output."
- **MEV protection for DEX**: Need either Penumbra-style batching or commit-reveal schemes.
  Cannot be solved with ZK alone.

### Tension: PQ-safety vs homomorphic commitments

The biggest architectural tension: Pyana's PQ guarantee (hash-based STARKs) conflicts with
Pedersen commitments (which require elliptic curves and are NOT PQ-secure). Options:

1. **Accept curves inside trust boundary** (like pyana already does with BLS12-381): Use
   Pedersen commitments for value conservation but only within the federation. External
   verification uses STARK proofs that verify the Pedersen math in-circuit.
2. **Lattice-based commitments**: PQ-safe homomorphic commitments exist (based on Module-LWE)
   but are much larger and more expensive.
3. **Field-arithmetic conservation**: Prove `sum(v_i) = sum(v_j)` directly in BabyBear field
   using range proofs (prove each value is in [0, 2^64]). No homomorphism needed — the STARK
   circuit directly enforces the sum equality on the plaintext values (which are private witness).
   This is the most STARK-native approach and preserves PQ safety.

**Recommendation**: Option 3. The STARK circuit already sees the private values (they're
witness data). It can directly compute and constrain the sum. You don't NEED homomorphic
commitments if your proof system can handle the conservation check internally. This is a
key advantage of STARKs over Groth16/PLONK-based systems where public verification of
balances typically requires homomorphic tricks.

---

## 7. Summary

Pyana is well-positioned for private programmable state because its existing primitives
(Merkle trees, non-membership proofs, STARK circuits, fold chains, committed fields) map
cleanly to the concepts that private systems need. The main gaps are:

1. **Notes + nullifiers** for anonymous transferable value (not needed for auth, required for DEX)
2. **Conservation proofs** for ensuring no value is created from thin air
3. **A batch clearing mechanism** for fair DEX execution

The STARK-native approach (option 3 above) elegantly sidesteps the PQ-vs-homomorphism tension
that plagues curve-based systems, and pyana's existing 4-ary Merkle infrastructure provides a
solid foundation for both note commitment trees and nullifier trees.

The hybrid cell+note architecture preserves pyana's strengths (authorization, coordination,
progressive disclosure) while adding the anonymity properties that financial applications demand.
