# E-Language Semantics Deep Dive: From Miller to zkPromises

## Status: RESEARCH (2026-05-23)

---

## 1. What Agoric/Spritely/OCapN Do That We Should Learn From

### 1.1 Agoric's SwingSet Kernel

SwingSet is the vat orchestrator. Vats are isolated JS compartments (think: our
cells). The kernel mediates all inter-vat communication. Key architectural
decisions:

**Message dispatch is a kernel service, not peer-to-peer.**
Vats don't send messages directly to each other. Every `E(target).method(args)`
goes through the kernel's run-queue. The kernel decides ordering, batches
deliveries, and handles promise resolution. This is precisely our executor model:
turns are submitted to the executor, not sent cell-to-cell.

**Promises are kernel-tracked objects with lifecycle.**
When vat A does `const p = E(vatB).doSomething()`, the kernel creates a promise
table entry. If vatB resolves it, the kernel delivers the resolution to all
subscribers. If vatB is terminated, the kernel rejects all its outstanding
promises. We have the `PendingTurnRegistry` with `BrokenReason` propagation --
this IS the same pattern.

**What they do better than us:**
- Promise table is first-class infrastructure with GC (when all references to a
  promise are dropped, the entry is collected). Our `PendingTurnRegistry` doesn't
  GC -- timed-out entries linger.
- Cranks (their name for turns) can produce multiple promises per crank. Our
  turns produce `TurnOutput` entries, but the connection between output slots
  and downstream pending turns is implicit (via `EventualRef.source_turn`), not
  tracked as a reference-counted graph.

**Mapping: SwingSet kernel = our executor + PendingTurnRegistry combined.**

### 1.2 Agoric's "Offer" and "Invitation" Patterns

Zoe's offer pattern:
1. Contract publishes an Invitation (a capability to participate).
2. User makes an Offer (proposal + payment). The offer says: "I give X, I want Y."
3. Zoe holds the escrowed payment. The contract evaluates the offer.
4. On success: reallocate (give Y to user, give X to contract).
5. On failure: return X to user (offer safety guarantee).

**This maps directly to our intent + escrow system:**
- Invitation = Intent of kind `Offer` (published on gossip network)
- User's offer = Intent of kind `Need` that matches the `Offer` intent
- Zoe's escrow = `CommittedEscrow` (value locked, condition-gated release)
- Offer safety = timeout refund (our `timeout_height` on escrow)
- Reallocation = Turn with `Transfer` effects executed after condition proof

**What Zoe adds that we lack: "offer safety" as a KERNEL GUARANTEE.**
In Agoric, Zoe guarantees that if your offer fails, you get your payment back.
This is not just a timeout -- it's synchronous rollback. In pyana, if a
conditional turn times out, the deposit is burned (not returned). The escrow
timeout_height does give refund semantics, but only after the timeout -- there's
no immediate rollback on condition failure.

**Recommendation:** Add a `ConditionalTurn` variant where timeout returns the
deposit rather than burning it. Call it `SafeConditional` -- it mimics Zoe's
offer safety. The existing burn-on-timeout variant is useful for DoS prevention
(penalizes wasteful conditional submissions), but for user-facing "offer"
patterns, the Zoe-style refund is more appropriate.

### 1.3 Agoric's Purse/Payment Abstraction

A Purse holds fungible value. A Payment is a one-shot value transfer object.
You withdraw from a purse to create a payment, then deposit the payment into
another purse. Payments are linear (single-use, unforgeable transfer tokens).

**This maps to our note system:**
- Purse = Cell balance (or note tree membership)
- Payment = Note (committed value with nullifier for single-use)
- Withdraw = Create note (commit value, get nullifier)
- Deposit = Spend note (reveal nullifier, credit recipient)

The fit is quite good. Agoric's insight: separating the "holding place" (purse)
from the "transfer medium" (payment) enables safe composition. You can hand a
payment to untrusted code without giving them access to your purse. We already
have this: you can pass a note commitment to untrusted code, and they can only
spend it if they know the spending key + nullifier preimage.

### 1.4 Spritely / OCapN / CapTP

**The OCapN Protocol Stack:**
- CapTP: Capability Transport Protocol (handles distributed promise resolution)
- OCapN locators: identify objects across network boundaries
- Goblins: actor system implementing CapTP

**CapTP's promise resolution across network boundaries:**

When machine A holds a promise that will be resolved by machine B:
1. A asks B for a "vine" (a forward reference that keeps the remote object alive).
2. When B resolves, it sends the resolution to A via the vine.
3. A substitutes the resolution everywhere the promise was held.
4. The vine is GC'd once all holders have received the resolution.

**Our equivalent:** `EventualRef` with `federation_id: Some(...)` + the
`PendingTurnRegistry` with `ResolutionCondition::AwaitReceipt { federation_id }`.
We have the wiring. What we lack:

1. **No GC protocol.** CapTP uses "gift tables" and "export tables" with
   reference counting to know when a remote reference is no longer held.
   We don't track who holds an `EventualRef` to a remote turn -- we just
   timeout after `timeout_height`.

2. **No 3-party introduction at the network level.** CapTP supports: A introduces
   B to C's object by sending B a CapTP "handoff" -- B can then communicate
   directly with C without routing through A. Our `Effect::Introduce` works at
   the cell level (within a federation), but we have no cross-federation
   introduction protocol.

3. **No vine/sturdy-ref distinction.** CapTP distinguishes "live references"
   (vines -- exist only while the connection is up) from "sturdy references"
   (can be persisted, reconnected later). Our bearer caps are closest to sturdy
   refs (self-contained, transferable), while c-list entries are closest to live
   refs (exist only while the cell exists). But we don't have an explicit
   reconnection protocol for bearer caps that target a temporarily-offline
   federation.

### 1.5 Capability Attenuation in These Systems

All three systems agree: **attenuation is monotonically narrowing.**

- Agoric: "facets" on objects (an object has multiple facets; you can give
  someone a facet that exposes only a subset of methods).
- Spritely/Goblins: membrane pattern (a membrane wraps an object and filters
  which messages pass through).
- E original: caretaker pattern (an intermediary that forwards only approved
  messages).

Our `EffectMask` + the unified model's facet enforcement is the right approach.
The key insight from all three: **attenuation must be ENFORCED at the boundary,
not trusted from the holder.** The unified capability model (routing all paths
through `enforce_capability`) is exactly the right fix -- it makes the boundary
enforcement uniform.

---

## 2. How Eventual Sends Can Work in Our Turn-Based Model

### 2.1 The Fundamental Tension

E's model assumes an event loop: messages arrive, handlers fire, new messages
are sent, eventually promises resolve. Time is asynchronous and non-deterministic.

Pyana's model is block-based: turns execute deterministically within a block,
state transitions are atomic, time advances discretely (block heights). There is
no event loop.

The question from the prompt was: which of options A, B, C maps best to E's
actual semantics?

### 2.2 Answer: Option B (Intents) is the closest semantic match

**E's eventual send:** `alice <- transfer(100)`
- Semantics: "I want alice to receive a transfer(100) message. I don't know when.
  I get back a promise for the result."
- The message enters a queue. It resolves when alice's vat processes it.
- The sender continues executing without waiting.

**Option B: Eventual send = intent.**
- Semantics: "I want to transfer 100 to alice. Here's my intent. The system
  matches it (finds alice's cell, resolves routing), and the fulfillment is the
  promise resolution."
- The intent enters the gossip pool. It resolves when a matcher pairs it.
- The sender continues operating without waiting.

Why Option B wins over A and C:

**Option A** ("submit a turn targeting another cell, result available for next
turn") is just the existing `Pipeline`/`TurnBatch` mechanism. It's synchronous --
everything resolves in one block. This is E's IMMEDIATE call (`.`), not eventual
send (`<-`). The "promise" resolves instantly.

**Option C** ("conditional turn that executes when condition is met") is closer
but semantically different. A `ConditionalTurn` doesn't express WHAT you want --
it expresses WHEN to act. You must already know the exact turn to execute; you're
just gating on a condition. E's eventual send is about DISCOVERY and ROUTING,
not just timing.

**Option B** captures the full semantics:
- Discovery: "find alice" = matching against gossip intents
- Routing: "deliver the message" = fulfillment protocol
- Non-blocking: sender publishes intent and continues
- Promise: the fulfillment IS the resolution
- Failure: intent expiration = broken promise (timeout)

### 2.3 The Eventual Send as Intent + Conditional Turn (Composed)

The full E-style eventual send in pyana requires composing two primitives:

```
1. Sender publishes Intent { kind: Need, matcher: "transfer(100) to alice" }
2. Wallet/matcher discovers it can fulfill (has route to alice's cell)
3. Fulfillment creates a ConditionalTurn:
     - Turn: Transfer { from: sender, to: alice, amount: 100 }
     - Condition: ProofCondition::LocalProof { ... } (proof of alice's acceptance)
4. When alice's cell confirms -> turn executes -> promise resolves
5. BrokenReason::Timeout if no match found before intent expiry
```

The "promise" that the sender receives is a `PendingHandle` from the
`PendingTurnRegistry`. The sender can use this handle's `turn_hash` as a
dependency for subsequent turns (pipelining).

### 2.4 Promise Pipelining in This Model

E's killer feature: `alice <- transfer(100) <- getReceipt()` -- send `getReceipt`
to the UNRESOLVED result of `transfer(100)`, avoiding a round-trip.

In our model:
```
1. Intent A: "transfer 100 to alice, I want the receipt"
2. Intent B (depends on A): "get receipt from result of A"
   - B.condition = TurnExecuted { turn_hash: A.turn_hash }
   - B.target = EventualRef { source_turn: A.turn_hash, output_slot: 0 }
```

This IS meaningful pipelining -- B is submitted before A resolves. The system
knows B depends on A and will execute B after A (or break B if A breaks). The
two intents can potentially be matched and fulfilled together by a solver who
sees both, eliminating one round-trip.

**Key insight:** Pipeline semantics emerge from the COMPOSITION of intents +
conditional turns + output refs. We don't need a separate `PipelinedSend` effect
-- it's just a dependent entry in the pending registry whose target is an
output ref.

### 2.5 Recommendation: Rename, Don't Remove

The existing machinery (`PendingTurnRegistry`, `EventualRef` with `federation_id`,
`ResolutionCondition`, `BrokenReason`) is the RIGHT infrastructure for E-style
distributed promises. What's wrong is:

1. The MODULE-LEVEL naming (calling the synchronous batch "eventual") is wrong.
   The batch is just a batch. The PENDING REGISTRY is where eventual semantics
   live.

2. `Effect::PipelinedSend` should become a submission to the `PendingTurnRegistry`
   with a dependent turn, not an effect within a synchronous batch.

3. The connection between the intent system and the pending registry should be
   explicit: a fulfilled intent produces a pending turn (with appropriate
   conditions) rather than a direct synchronous turn.

---

## 3. The zkPromise Construction

### 3.1 Definition

A **zkPromise** is a cryptographic commitment to produce a future value, carrying
a zero-knowledge proof that the promisor HAS THE CAPABILITY to fulfill, combined
with economic stake that makes failure costly.

Formally:
```
zkPromise = (commitment, capability_proof, stake_lock, condition, deadline)
```

Where:
- `commitment`: Pedersen commitment to the promised value (hides V until fulfillment)
- `capability_proof`: STARK proof that the promisor CAN produce V (has the
  resources, permissions, knowledge required)
- `stake_lock`: Escrowed collateral forfeited on non-fulfillment
- `condition`: What "fulfillment" means (reveal commitment opening, deliver proof)
- `deadline`: Block height by which fulfillment must occur

### 3.2 Properties and Pyana Mapping

| Property | Meaning | Pyana Primitive |
|----------|---------|-----------------|
| Binding | Promisor MUST fulfill or lose stake | `CreateObligation { stake, deadline }` |
| Transferable | Promise can be passed to others | Bearer cap over obligation ID |
| Composable | Chain promises (A's output feeds B's input) | `ConditionalTurn` with `depends_on` |
| Private | Promised value hidden until fulfillment | Pedersen `value_commitment` in escrow |
| Verifiable | Proof that fulfillment is possible | Presentation proof of resource ownership |

### 3.3 Construction (Composing Existing Primitives)

A zkPromise is NOT a new primitive. It's a protocol-level composition:

```
Step 1: Promisor generates capability proof
  - Proves: "I own a note with value >= V" (Merkle membership + value range)
  - Proves: "I hold a capability that permits Transfer to target"
  - This is a PresentationProof with specific public inputs

Step 2: Promisor creates obligation
  Effect::CreateObligation {
    beneficiary: promisee_cell,
    condition: ProofCondition::LocalProof {
      expected_air: "value_delivery",
      expected_public_inputs: [commitment_hash, ...],
    },
    deadline_height: current + TTL,
    stake: locked_note,
    stake_amount: collateral_value,
  }

Step 3: Promisor creates committed escrow for the promised value
  CommittedEscrow {
    creator_commitment: hash(promisor_id || blind_1),
    recipient_commitment: hash(promisee_id || blind_2),
    value_commitment: pedersen(V, r),
    condition_commitment: hash(obligation_id || nonce),
    timeout_height: deadline,
  }

Step 4: The "zkPromise token" is:
  (obligation_id, escrow_id, capability_proof, stake_amount)
  + a bearer cap authorizing the holder to claim the escrow
```

### 3.4 Transfer of zkPromise (Bearer Semantics)

The promisee can transfer the promise to a third party by delegating their
bearer cap over the escrow:

```
Original promisee -> new holder:
  BearerCapProof {
    target: escrow_cell,  // the escrow tracking cell
    permissions: AuthRequired::Proof,
    delegation_proof: ...,  // chain from promisee to new holder
    expires_at: deadline,
    revocation_channel: Some(obligation_id),  // tied to the obligation
    allowed_effects: Some(EFFECT_TRANSFER),   // can only claim, not modify
  }
```

The bearer cap IS the transferable promise. Whoever holds it can claim the
escrow when the obligation is fulfilled. If the obligation is slashed (broken
promise), the `revocation_channel` trips (obligation_id is marked as slashed),
and the bearer cap becomes inert -- but the holder receives the slash penalty
from the obligation instead.

### 3.5 Composition (Promise Chaining)

Promise A: "I will deliver X by height 100"
Promise B: "When A delivers X, I will transform it and deliver Y by height 150"

```
Obligation B's condition:
  ProofCondition::TurnExecuted {
    turn_hash: fulfillment_turn_of_A
  }
```

B can't even BEGIN fulfilling until A resolves. This is the categorical dual:
- A's obligation creates a `ConditionalTurn` dependency for B
- B's obligation is gated on A's resolution

The `PendingTurnRegistry` handles the cascading:
- A resolves -> B's condition is met -> B becomes executable
- A breaks (timeout/slash) -> B's dependency breaks -> B auto-breaks

This gives us **promise pipelining with economic enforcement**: each promise in
the chain has its own stake, and broken-promise propagation is automatic.

### 3.6 What Makes This "ZK"

The "zk" in zkPromise is not about hiding the promise itself -- it's about:

1. **Private capability proof**: The promisor proves they CAN fulfill without
   revealing WHAT they hold. The presentation proof says "I have sufficient
   resources" without exposing balances, token chains, or identities.

2. **Private fulfillment**: The escrow release can use a ZK claim (future work
   noted in `CommittedEscrow` docs) -- the recipient proves they're the
   authorized holder without revealing their identity.

3. **Private composition**: Promise chains can be constructed where intermediate
   parties never see the full pipeline. Each participant sees only their adjacent
   obligations.

### 3.7 Pitch to Mina Architects

The zkPromise maps cleanly to Mina's programming model:
- Mina's `AccountUpdate` has preconditions (our `ProofCondition`)
- Mina's proofs bind to specific account states (our capability proofs bind to
  federation roots)
- Mina's recursive verification (proof-of-proof) enables the composition layer:
  "verify this proof verifies that proof" is how you chain promises without
  re-executing the full computation

What pyana adds beyond what Mina has natively:
- The ECONOMIC BINDING (obligation + slash) -- Mina has no built-in staking on
  future actions
- The PRIVACY layer (committed escrow hides parties and amounts)
- The TRANSFER mechanism (bearer caps make promises negotiable instruments)
- The INTENT DISCOVERY (gossip matching connects promisors to promisees)

---

## 4. Sealer/Unsealer as Commitment-Gated Capabilities

### 4.1 Current State

The current system has:
- `Effect::CreateSealPair` -- creates a paired sealer/unsealer (X25519 keypair)
- `Effect::Seal` -- encrypts a capability reference into a `SealedBox`
- `Effect::Unseal` -- decrypts the box, granting the capability to the recipient

The crypto: X25519 key agreement + ChaCha20-Poly1305 AEAD. Sound construction.

### 4.2 E-Language Rights Amplification Pattern

In E, the canonical use of sealers:

```e
def makeBrandPair() {
  var sealedBoxes := []
  def sealer {
    to seal(value) { 
      def box := [value]
      sealedBoxes := sealedBoxes.with(box)
      return box 
    }
  }
  def unsealer {
    to unseal(box) { return box[0] }
  }
  return [sealer, unsealer]
}
```

The pattern: anyone can LOOK at a sealed box. But only the matching unsealer can
extract the value. This is used for RIGHTS AMPLIFICATION:

"If you can unseal this box, it PROVES you are the entity I shared the unsealer
with. Therefore, you may perform action X."

The proof-of-identity is implicit in the ability to unseal.

### 4.3 Unifying with ZK

The E-language sealer/unsealer pattern maps to commitment schemes:

| E concept | ZK equivalent |
|-----------|---------------|
| Sealed value | Pedersen commitment `C = vG + rH` |
| Unsealer | Knowledge of `(v, r)` (the opening) |
| Proving you can unseal | Schnorr proof of knowledge of `(v, r)` such that `C = vG + rH` |
| Rights amplification | "If you can open commitment C, you're authorized for X" |

### 4.4 Commitment-Gated Capabilities (New Pattern)

A **commitment-gated capability** is:

```
CapabilityGate {
  gate_commitment: [u8; 32],  // Pedersen commitment (or BLAKE3 for simpler cases)
  gated_effect: EffectMask,   // What you can do if you open the gate
  target: CellId,             // Who you can do it to
}
```

To exercise: prove knowledge of the commitment opening. The proof IS the
authorization.

This differs from current bearer caps because:
- Bearer caps prove a DELEGATION CHAIN (someone who holds the cap delegated to you)
- Commitment-gated caps prove KNOWLEDGE (you know a secret that opens a commitment)

The E insight: sometimes "knowing a secret" IS your authority. Not because
someone delegated to you, but because the system was DESIGNED so that secret-
knowledge is the authorization mechanism.

### 4.5 Where This Is Useful

**1. Anonymous credentials without delegation chains.**

Current: to prove you're authorized, you show a delegation chain from an issuer.
This reveals the chain structure (how many hops, which intermediaries).

With commitment gates: the issuer publishes `C = commit(your_identity, r)`. You
prove knowledge of `(your_identity, r)` without revealing either. The proof IS
your credential. No chain, no intermediaries.

**2. Threshold-gated capabilities.**

"This capability activates when 3 of 5 parties can each open their commitment."
Each party has a commitment to their share. A threshold proof (k-of-n Schnorr)
demonstrates sufficient openings exist. No single party can exercise alone.

**3. Time-locked capabilities (via VDF commitments).**

"This capability activates after time T." The gate commitment is to a value
that can only be computed after T (VDF output). Once computed, the opener can
exercise the capability.

### 4.6 Relationship to Current Sealer/Unsealer

The current sealer/unsealer is a SPECIAL CASE of commitment-gated capabilities:
- The "commitment" is the sealed box (the ciphertext commits to the plaintext)
- The "opening" is the decryption (knowing the X25519 private key)
- The "gated effect" is receiving the capability that was sealed inside

But it's implemented via symmetric encryption rather than commitment schemes.
This is fine for the offline-delegation use case (you actually want to TRANSFER
the sealed data, not just prove you could open it). The ZK version (commitment
gates) is for when you want to PROVE authority without actually revealing/
transferring the gated value.

**Keep both:**
- Sealer/Unsealer: for actual data transfer in partition-tolerant scenarios
- Commitment-gated caps: for proof-of-knowledge authorization (new primitive)

### 4.7 Implementation Sketch

```rust
/// A capability gated by knowledge of a commitment opening.
pub struct CommitmentGatedCap {
    /// The commitment that gates this capability.
    /// Opening this commitment (proving knowledge of value + blinding) authorizes exercise.
    pub gate_commitment: [u8; 32],
    /// What effects are authorized upon proof-of-opening.
    pub gated_effects: EffectMask,
    /// Target cell for the gated effects.
    pub target: CellId,
    /// Optional: time constraint (gate only opens after this height).
    pub opens_after: Option<u64>,
}

/// Authorization variant for commitment-gated exercise.
enum Authorization {
    // ... existing variants ...
    /// Prove knowledge of commitment opening via Schnorr proof.
    CommitmentOpening {
        /// The gate commitment being opened.
        gate_commitment: [u8; 32],
        /// Schnorr proof of knowledge of (value, blinding).
        proof: Vec<u8>,
    },
}
```

The resolution function:
```rust
fn resolve_commitment_gate(
    gate: &CommitmentGatedCap,
    proof: &[u8],
    current_height: u64,
) -> Result<ResolvedCapability, TurnError> {
    // 1. Verify Schnorr proof against gate_commitment
    // 2. Check opens_after constraint
    Ok(ResolvedCapability {
        target: gate.target,
        permissions: AuthRequired::Proof,
        allowed_effects: Some(gate.gated_effects),
        expires_at: None,
        revocation_channel: None,
        proof_method: ProofMethod::CommitmentOpening { gate: gate.gate_commitment },
    })
}
```

---

## 5. Concrete Recommendations for Pyana

### BUILD (High Value, Fits Naturally)

**5.1 zkPromise as protocol-level composition (not new primitive)**

Don't add a `zkPromise` type. Instead, document the PROTOCOL for composing:
`CreateObligation` + `CommittedEscrow` + bearer cap = transferable promise.

Add a builder/helper in the `turn` crate:
```rust
pub fn create_zk_promise(
    promisor: CellId,
    promisee: CellId,
    value_commitment: ValueCommitmentBytes,
    capability_proof: StarkProof,
    stake_amount: u64,
    deadline: u64,
) -> (Vec<Effect>, ZkPromiseHandle)
```

This emits the 2-3 effects needed and returns a handle (obligation_id + escrow_id
+ bearer cap template) that the promisee can use or transfer.

**5.2 SafeConditional variant (Zoe-style offer safety)**

Add to `ConditionalTurn`:
```rust
pub refund_on_timeout: bool,  // default: false (current burn behavior)
```

When true, timeout returns the deposit to the submitter instead of burning it.
This enables "offer" patterns where failed matches are costless (excluding
opportunity cost of locked funds).

**5.3 Commitment-gated capability as new authorization path**

Add `Authorization::CommitmentOpening` variant. Route through the unified
`enforce_capability` function. This enables:
- Anonymous credentials (prove identity without revealing it)
- Threshold-gated access (k-of-n)
- Rights amplification (E pattern) without symmetric crypto

**5.4 Explicit intent-to-pending-turn bridge**

Currently the intent system (`intent/src/fulfillment.rs`) creates turns directly.
Add an explicit path where fulfillment creates a `PendingEntry` in the registry
rather than executing synchronously. This gives fulfilled intents the full
promise lifecycle (cascading resolution, broken-promise propagation).

### RENAME/CLARIFY (Low Cost, Reduces Confusion)

**5.5 EventualRef -> OutputRef (primary name)**

Already aliased. Make `OutputRef` the canonical name in all new code. Keep
`EventualRef` as a deprecated alias.

**5.6 Pipeline -> TurnBatch (for synchronous batches)**

The word "pipeline" suggests streaming. What we have is a DAG of turns with
topological execution. `TurnBatch` is more honest.

**5.7 PipelinedSend -> remove from Effect enum**

`Effect::PipelinedSend` should become a submission to the `PendingTurnRegistry`
with `ResolutionCondition::AwaitReceipt`. The "inner action" becomes a regular
turn. The `EventualRef` targeting still works -- it's just no longer an effect
but a turn-level dependency.

### SKIP (Low Value, High Complexity, Wrong Fit)

**5.8 Full CapTP-style reference tracking and GC**

CapTP's gift-table/export-table/reference-counting protocol is designed for
long-lived connections between two specific machines. Our federation model is
different: state is replicated, not located on one machine. GC of cross-
federation references isn't needed because timeout-based expiry is simpler and
sufficient for a blockchain-like system. The complexity of distributed GC isn't
justified when you have block heights as a universal clock.

**5.9 Cross-federation 3-party introduction protocol**

In CapTP, A introduces B to C by giving B a direct-communication channel to C.
In our model, all inter-federation communication goes through conditional turns
with STARK proofs. There's no "direct channel" -- everything is mediated by the
respective federations' consensus. Adding a direct-channel protocol would
undermine the federation model's security guarantees.

Instead: A introduces B to C by delegating a bearer cap (B gets authority over
C's resource via A's delegation). This doesn't require a new protocol -- it's
just bearer cap delegation with a cross-federation target.

**5.10 Event-loop/actor-model runtime**

Trying to implement E's event loop model would fight against the deterministic
block-based execution model. The intent system + pending registry already
provides the asynchronous coordination semantics. Bolting on a non-deterministic
event loop would make consensus impossible.

---

## 6. Relationship to the Unified Capability Model

The unified capability model (from `plans/unified-capability-model.md`) defined
`ResolvedCapability` as the common enforcement point. Everything in this document
DEPENDS on that being implemented first:

### 6.1 zkPromise requires unified enforcement

The bearer cap that constitutes a transferable zkPromise must have its facets
enforced. Currently, bearer caps go through `verify_bearer_cap` which (as the
unified model documented) doesn't enforce facets. Without Phase 3 of the unified
model (route bearer path through enforcement), a zkPromise's facet restriction
is meaningless.

### 6.2 Commitment-gated caps are a new resolution path

The unified model defined five resolution functions (signature, zk_proof,
breadstuff, bearer, clist_exercise). Commitment-gated caps add a sixth:

```rust
fn resolve_commitment_opening(
    gate: &CommitmentGatedCap,
    proof: &[u8],
) -> Result<ResolvedCapability, TurnError>
```

This slots naturally into the unified model: resolve via commitment proof,
then enforce uniformly. No special cases needed.

### 6.3 Intent-as-eventual-send flows through enforcement

When an intent fulfillment creates a pending turn, that turn still goes through
the normal executor path (including `enforce_capability`). The eventual-send
semantics are OUTSIDE the enforcement boundary (they're about scheduling and
routing). Once the pending turn fires, it's just a regular turn subject to all
the same checks.

### 6.4 Sealer/Unsealer remains separate from enforcement

Sealers are for DATA TRANSFER (moving encrypted capability references between
parties). They don't need to go through `enforce_capability` because they don't
EXERCISE authority -- they PACKAGE it for later exercise. The recipient, upon
unsealing, gets a capability that they then exercise through the normal paths.

This is architecturally correct: sealers are at the DATA PLANE level (how caps
are transported), while enforcement is at the CONTROL PLANE level (how caps are
exercised).

### 6.5 Implementation Order

1. **Unified model Phases 1-3** (prerequisite for everything else)
2. **SafeConditional variant** (trivial extension to `ConditionalTurn`)
3. **Intent-to-pending bridge** (connects intent fulfillment to promise lifecycle)
4. **Commitment-gated authorization** (new resolution path in unified model)
5. **zkPromise builder** (composition helper over obligation + escrow + bearer)
6. **Naming cleanup** (EventualRef -> OutputRef, PipelinedSend removal)

Items 2-4 can proceed in parallel after item 1. Item 5 depends on 3 and 4.
Item 6 can happen any time (pure rename/refactor).

---

## Appendix A: E-Language Promise States and Their Pyana Equivalents

| E state | Meaning | Pyana equivalent |
|---------|---------|------------------|
| Unresolved | Promise exists, no value yet | `PendingStatus::Pending` |
| Fulfilled | Promise resolved to a value | `ResolutionOutcome::Resolved(receipt)` |
| Broken (aka smashed) | Promise will never resolve | `ResolutionOutcome::Broken(reason)` |
| Near (local) | Reference to a local object | `Target::Concrete(cell_id)` |
| Far (remote) | Reference to a remote object | `EventualRef { federation_id: Some(...) }` |

## Appendix B: Agoric Concept Mapping

| Agoric | Pyana | Notes |
|--------|-------|-------|
| Vat | Cell | Isolated execution context |
| Kernel | Executor | Mediates all interactions |
| Crank | Turn | Atomic state transition |
| E(target).method() | `PipelinedSend` / pending turn | Async dispatch |
| Promise | `PendingHandle` | Future value |
| Purse | Cell balance / note tree | Holds fungible value |
| Payment | Note commitment | One-shot value transfer |
| Invitation | `Intent { kind: Offer }` | Published offer to participate |
| Offer | `Intent { kind: Need }` matching an Offer | User's acceptance |
| Zoe (escrow) | `CommittedEscrow` | Trustless settlement |
| Offer safety | `SafeConditional` (proposed) | Refund on failure |
| Brand | Token domain (`token_id`) | Identifies asset type |
| Amount | Value commitment | Typed quantity |

## Appendix C: OCapN/CapTP Concept Mapping

| OCapN/CapTP | Pyana | Gap? |
|-------------|-------|------|
| Locator | `CellId` + `federation_id` | OK |
| Vine (live ref) | C-list entry | OK |
| Sturdy ref | Bearer cap | OK |
| Gift table | No equivalent | Not needed (timeout-based) |
| Export table | No equivalent | Not needed (content-addressed) |
| Handoff (3-party intro) | `Effect::Introduce` (local only) | Cross-fed gap exists, skip for now |
| Promise | `PendingEntry` | OK |
| Broken promise | `BrokenReason` | OK |
| Near/Far | `Target::Concrete` / `Target::Eventual` | OK |
