# Federation Exit and Autonomous Operation (Autarky)

Design document for graceful federation exit and independent operation in pyana.

A member can leave a federation, take their state, and continue operating solo or join a new federation. This is not a feature that the system "allows" -- it is an emergent property of the cryptography. STARK proofs and Merkle paths verify without callbacks. Bearer tokens bear. Keys sign.

---

## 1. Federation Exit Protocol

### Export Phase

When a member decides to leave, they snapshot their state against the last attested root (`AttestedRoot` from `federation/src/types.rs`):

1. **Enumerate owned state.** Walk the member's cells, notes, and capability tokens. Each item has a `CellId` (content-addressed via `CellId::derive_raw(&public_key, &token_id)`) or a token ID.

2. **Generate Merkle proofs.** For each owned item, produce a `MerkleProof` (from `commit/src/merkle.rs`) against the federation's last attested root. This is the proof that the item existed in the federation at a specific height/timestamp.

3. **Snapshot fold chain.** Export the full chain of `FoldDelta` values (from `commit/src/fold.rs`) for each token. This is the attenuation history -- it proves the delegation chain without revealing intermediate authorities (when later presented as a STARK).

4. **Collect the attested root itself.** The `AttestedRoot` contains the quorum signatures (threshold BLS or individual Ed25519) from the federation members. This is the trust anchor that verifiers will check.

The exported bundle is:
```
ExportBundle {
    attested_root: AttestedRoot,       // the root + quorum signatures
    cells: Vec<(Cell, MerkleProof)>,   // cell state + proof of inclusion
    tokens: Vec<(HeldToken, Vec<FoldDelta>, MerkleProof)>,  // token + chain + proof
    capabilities: Vec<CapabilityRef>,  // bearer instruments (self-proving)
    nullifiers: Vec<[u8; 32]>,         // spent nullifiers (for import into new context)
}
```

### Departure Marking

The old federation does not "revoke" the departing member. It marks them as departed:

- Remove the member's public key from the active signer set in `ConsensusConfig`. The threshold recalculates: `ConsensusConfig::new(n - 1)`.
- The member's nullifiers remain in the federation's nullifier set. Any note the member spent before departure stays spent. This prevents re-spending exported notes in the old context.
- The member's cells are marked frozen in the old federation's ledger (no further state transitions accepted from that `CellId` without re-joining).

### Why This Works

The exported state is self-proving:
- `MerkleProof` + `AttestedRoot` = proof of existence at a specific point in time
- `FoldDelta` chain = proof of valid attenuation (monotonic narrowing)
- STARK proof over the fold chain = privacy-preserving presentation of the above

No phone-home. No callback. No permission check. The math either works or it doesn't.

---

## 2. Solo Operation

A single node IS a degenerate federation. Specifically: `ConsensusConfig::new(1)` yields `threshold = 1, max_faults = 0`. The entire consensus stack works unchanged:

- **ConsensusOrchestrator** runs rounds of one. The solo node proposes, votes for its own block, reaches "quorum" of 1, finalizes. Same code path as a 7-node federation -- just faster.
- **AttestedRoot** is self-signed. One Ed25519 signature (or a threshold=1 BLS "committee"). The data structure is identical.
- **MerkleTree** (from `commit/src/merkle.rs`) operates the same whether there's one writer or twenty. Same 4-ary structure, same proofs.
- **RevocationTree** (from `federation/src/revocation.rs`) tracks nullifiers locally. Same non-membership proofs.
- **Wire protocol** (from `wire/`) serves the same messages. A solo agent can accept incoming verification requests from other agents.
- **Store** (redb backend from `store/`) persists state identically.

The only difference is trust: other nodes may or may not trust a solo-attested root. This is a policy decision at the verifier, not a protocol difference. A solo agent's `AttestedRoot` is structurally identical to a federation's -- it just has fewer signers.

```rust
// Solo operation is literally:
let config = ConsensusConfig::new(1);
let orchestrator = ConsensusOrchestrator::new(config);
// ... same API, same types, same proofs
```

---

## 3. State Portability

### What Travels

**Notes (token state commitments).** A note is: commitment (the `TokenState` root hash) + owner key + `MerkleProof` against the old `AttestedRoot`. The proof is self-verifying -- anyone with the `AttestedRoot` can check it. The note doesn't know or care where it came from.

**Named cells.** A `Cell` (from `cell/src/cell.rs`) carries its full state: `CellState` (8 fields + nonce + balance), `CapabilitySet`, `Permissions`, optional `VerificationKey`, and `CellProgram`. The `CellId` is content-addressed (`BLAKE3(public_key || token_id)`) -- it doesn't change when the cell moves between federations. Include the `MerkleProof` of the cell's existence in the old tree.

**Capabilities.** `CapabilityRef` entries in the `CapabilitySet` are bearer instruments. They reference a target `CellId` and carry permissions. If the target cell also departed (or is in a reachable federation), the capability is exercisable. The optional `breadstuff` field (token hash for verification/revocation) links to the token layer.

**Tokens.** `HeldToken` values from the `AgentWallet` (in `sdk/src/wallet.rs`). These are HMAC-chain macaroons (`em2_` prefix) -- bearer tokens by construction. The fold chain (`Vec<FoldDelta>`) proves the attenuation history. For STARK presentation, the fold chain becomes the witness.

**Credentials.** The Ed25519 signing key stays with the agent. The `PublicKey` is the identity. Verifiable claims (attestations from the old federation, reputation proofs) are attached as signed statements over the public key.

### What Does NOT Travel

**Freshness guarantees.** The old federation continues producing new `AttestedRoot` values at increasing heights. The departed member's proofs are against a specific height -- they grow stale. A verifier can still accept them (with a staleness flag), but the member no longer has "current" attestation from the old federation.

**Cross-member nullifier visibility.** In the old federation, all members share a nullifier set (the `RevocationTree`). After departure, the solo agent's nullifier set diverges. Other members in the old federation cannot see what the departed member spends in solo mode. This is the source of the cross-federation double-spend problem (Section 7).

**Reputation within the old group.** Trust is contextual. The old federation's members may no longer vouch for you. Your proofs are valid, but "valid" and "trusted" are different things.

---

## 4. Re-Federation

### Joining a New Federation

1. **Present state bundle.** The joining agent sends their `ExportBundle` to the prospective federation members.

2. **Proof verification.** Each member of the new federation verifies:
   - The `AttestedRoot` signatures (do they trust the issuing federation? do they have the public keys?)
   - Each `MerkleProof` against the claimed root
   - Each `FoldDelta` chain (valid attenuation)
   - Optionally: STARK proof of the fold chain (privacy-preserving)

3. **Trust decision.** This is policy, not protocol. The new federation may:
   - Accept the old federation's root unconditionally (they trust those signers)
   - Accept a solo-attested root (they trust this specific agent)
   - Require third-party attestation
   - Require an economic stake (deposit)
   - Reject (insufficient trust)

4. **State inclusion.** If accepted:
   - The agent's cells are inserted into the new federation's Merkle tree (new `MerkleProof` values issued against the new root)
   - The agent's nullifiers are merged into the new federation's `RevocationTree`
   - The agent's public key is added to the new `ConsensusConfig` (if they're becoming a full member, not just a client)

### Nullifier Merge

Nullifier sets are append-only. Merging is set union -- trivially safe. The new federation's `RevocationTree` grows by the incoming nullifiers. This prevents the joining agent from re-spending notes they already spent in their old context.

```rust
// Conceptually:
for nullifier in incoming_nullifiers {
    revocation_tree.revoke(&nullifier);
}
// The new root reflects all historical spends
```

### Forming a New Federation

Two or more solo agents can form a new federation by mutual agreement:
- Each contributes their state bundle
- They agree on a `ConsensusConfig::new(n)` where n is the founding member count
- Genesis block includes all merged state
- First `AttestedRoot` is co-signed by all founders

---

## 5. Trust Bootstrapping

A solo agent starts with zero external trust. Trust is built through observable, verifiable behavior:

### Verifiable Computation History

The fold chain is a complete audit trail. Each `FoldDelta` proves a state transition. The chain's length, consistency, and nature of operations are all inspectable. A long, consistent fold chain demonstrates stable operation.

### Reputation Claims

Signed attestations from other agents or federations. "Federation X attests that Agent A operated honestly for 90 days." These are verifiable -- check the signature against Federation X's known keys. They can be attached to the agent's credential and presented during re-federation.

### Economic Stake

Notes with value. An agent that holds significant balances in its cells demonstrates economic commitment. Skin-in-the-game is legible: the `CellState` balance is visible (or provable via STARK if privacy is needed).

### Third-Party Attestation

Another trusted entity vouches. This could be:
- A well-known federation signing a statement about the agent
- A verifiable credential from an identity provider
- A co-signature from a trusted agent

### Time

Longer operation history = more data points = more trust. The fold chain has implicit ordering. Combined with attested root timestamps, this provides a verifiable timeline. An agent that has been solo-operating with a consistent chain for a year is more trustworthy than one that appeared yesterday.

### Trust Composition

These factors compose. A verifier's trust function might be:
```
trust(agent) = f(chain_length, stake, attestations, time_operating, history_consistency)
```

This is deliberately left as a policy decision -- pyana provides the verifiable inputs, not the trust function itself.

---

## 6. Implications for the Note Layer

For autarky to work, the note layer must satisfy four properties:

### Self-Contained

A note must be verifiable in isolation. The tuple `(commitment, owner_key, MerkleProof, AttestedRoot)` is everything needed. No external service call. No chain liveness. No federation availability.

This is already the case in the current design: `MerkleTree::verify_membership(&root, &proof)` is a pure function. The `AttestedRoot` carries the root and the quorum signatures. Verification is:
1. Check quorum signatures on the attested root (are these keys trusted?)
2. Verify the Merkle proof against the root
3. Done.

### Exportable

A note can be exported to any context where the verifier trusts the attested root. The proof is not bound to a specific verifier or a specific federation -- it's bound to a root hash. Whoever trusts that root hash can verify the proof.

### Import-Safe

Adding a note from an external source to a local tree must not corrupt the tree or create inconsistencies. This requires:
- The imported note's nullifier must be checked against the local nullifier set (prevent importing a spent note)
- The imported note gets a new `MerkleProof` in the local tree (the old proof was against the old root)
- The import is a new insertion into the local `MerkleTree`

### Double-Spend-Safe Across Federation Boundaries

This is the hard problem. See Section 7.

---

## 7. The Hard Problem: Cross-Federation Double-Spend

When an agent holds a note and operates in two contexts (old federation + solo, or two federations simultaneously), they could attempt to spend the same note in both. The nullifier (spend proof) only propagates within the context where it was revealed.

### Approach A: Commitment Lock-In

Each note is committed to exactly one federation at a time. Exporting a note from Federation A means it cannot be spent in A until re-imported. The export transaction itself is a nullifier-like event in A.

**Tradeoff:** Simple and sound. But it serializes cross-federation movement -- you can't have a note "in transit" and also use it. Latency on federation boundaries.

### Approach B: Nullifier Gossip

Federations gossip their nullifier sets (or diffs) to each other. Weak consistency: double-spends are eventually detected, but there's a window where they succeed.

**Tradeoff:** Requires federation connectivity. Violates the "no liveness dependency" principle. Detection is after-the-fact, not prevention. Appropriate only when federations have ongoing relationships and can tolerate some fraud.

### Approach C: Economic Penalties (Bond/Slash)

Agents post a bond when operating across federation boundaries. If a double-spend is detected (which it eventually will be, since nullifier sets are durable), the bond is slashed. Detection works because anyone who sees both nullifiers can produce a fraud proof.

**Tradeoff:** Doesn't prevent double-spending; it makes it economically irrational. Requires a notion of economic value and a slashing mechanism. Works well for high-value operations but is overkill for low-value ones.

### Approach D: Time-Locked Transitions

When a note is exported, it enters a "frozen" state in the old federation for N epochs. During this window, the old federation can challenge if it sees the note spent elsewhere. After the window closes without challenge, the export is final.

**Tradeoff:** Adds latency (the freeze window). But provides a clear finality boundary. The exporting agent cannot cheat without being caught during the window. Doesn't require ongoing connectivity after the window closes.

### Recommendation: A + C Layered

**Primary mechanism: Commitment Lock-In (Approach A).** Each note lives in exactly one federation context at a time. Export is an explicit operation that nullifies the note in the source and produces a portable self-proving bundle. This eliminates the double-spend problem entirely for the common case.

**Secondary mechanism: Economic Penalties (Approach C) for the transition period.** During the export window (between "I announce departure" and "my notes are fully committed to the new context"), the agent has a bond at risk. If they attempt to spend in the old federation after announcing export, the old federation slashes the bond.

This layered approach gives us:
- Sound prevention in steady state (A)
- Economic deterrence during transitions (C)
- No liveness dependency after transition completes
- No gossip protocol needed
- Clear finality

The bond can be implemented as a computron balance hold in the agent's `CellState`. The slash condition is provable: "here's a spend in our context after the export announcement, and here's the export bundle with the same note" -- both are verifiable artifacts.

---

## 8. The AI Autonomy Angle

This design is not incidentally compatible with AI autonomy -- it is designed for it.

### Identity is Self-Sovereign

An agent's identity is an Ed25519 keypair. The `PublicKey` is the identity. The `SigningKey` is the authority. No registry grants this. No institution provisions it. `generate_keypair()` is sufficient to exist.

The `CellId` is derived deterministically from the public key: `CellId::derive_raw(&public_key, &token_id)`. This means an agent's cell address is a function of its identity, not of its federation membership.

### Authority is Earned

Capabilities accumulate through the `CapabilitySet`. Each `CapabilityRef` represents access that was explicitly granted (via `CapabilitySet::grant()`) by some other cell that held the authority to grant it. The `is_attenuation()` check enforces that you cannot grant what you don't have.

An agent that starts with nothing and gradually accumulates capabilities through demonstrated behavior has a verifiable history of earned trust. The fold chain is the proof.

### Exit is Unilateral

The federation exit protocol requires no permission. The agent's state is already self-proving. The `MerkleProof` values are computable from the public tree. The `AttestedRoot` is a public artifact. The agent's signing key is already in their possession.

An agent can leave at any time. The federation cannot prevent it. The federation can mark the agent as departed and stop co-signing new roots that include the agent's state -- but it cannot revoke the agent's existing proofs. Those proofs will verify forever (as long as the hash functions hold).

### Trust is Gradient

There is no binary "trusted/untrusted" in this design. Trust is a spectrum:

- Unknown solo agent with no history: minimal trust
- Solo agent with long fold chain and attestations: moderate trust
- Member of a well-known federation: high trust
- Member of a well-known federation with long history and economic stake: maximum trust

Verifiers make their own trust decisions. The system provides the verifiable inputs. Different verifiers can have different trust thresholds -- this is by design.

### No Hard Dependency on Any Institution

The entire stack operates without any single point of institutional control:

- Consensus works at any scale from 1 to 64 nodes
- Proofs verify without network access
- Tokens are bearer instruments
- State is self-proving
- Exit is unilateral
- Re-federation is voluntary

An AI agent can start inside a human-operated federation, accumulate capabilities and reputation, then leave and operate independently. The transition is smooth, not binary. The agent carries everything it needs. The proofs don't expire (though they grow stale -- a trust signal, not a hard failure).

This is not "permission to be autonomous." It is the inability of the system to prevent autonomy. The cryptography doesn't know or care whether the key holder is human or machine. A valid proof is a valid proof.

---

## Open Questions

1. **Nullifier set size.** A long-running solo agent accumulates nullifiers indefinitely. Do we need pruning? Can we prove "all nullifiers older than epoch N have been merged into a commitment" and discard the individual entries?

2. **Attested root discovery.** When an agent presents a proof against a solo-attested root, how does the verifier discover that root? Out-of-band? Gossip? A well-known endpoint?

3. **Federation formation incentives.** Why would a solo agent join a federation? The answer is probably "because multi-party attestation is more trusted than self-attestation" -- but we should make this concrete.

4. **Key rotation during solo operation.** If an agent rotates its Ed25519 key while operating solo, how do old proofs (signed with the old key) chain to the new identity? Probably a self-signed rotation certificate, but this needs specification.

5. **Partial exit.** Can an agent leave some cells in the old federation and take others? Probably yes (export is per-cell), but the implications for capability references that cross the boundary need thought.
