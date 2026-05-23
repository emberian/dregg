# Sovereign Cell Program Upgrades

## How Mina Does It

In Mina, a zkApp account stores its verification key (VK) on-chain as a mutable field. The permission `set_verification_key` gates changes to it, using the same `Auth_required` enum as other permissions: `None`, `Signature`, `Proof`, `Either`, or `Impossible`. Crucially, this permission is paired with a `txn_version` — Mina uses this to distinguish accounts that deployed before the VK permission existed (legacy fallback to `Signature`).

When a transaction updates app state with `authorization_kind = Proof`, the protocol verifies the proof against the VK currently stored on the account. The `proved_state` boolean tracks whether the account's state was ever set via a valid proof (distinguishing "state set by owner signature" from "state proved correct by circuit"). Changing the VK does NOT invalidate prior state — it just means future proofs must satisfy the new circuit. There is no "lineage" mechanism; old proofs simply become irrelevant.

The downgrade attack surface: if `set_verification_key` is `Signature`, the account owner can swap to a trivial VK (one that accepts any proof), then "prove" arbitrary state transitions. Mina's answer is: set the permission to `Proof` (only the current circuit can authorize its own replacement) or `Impossible` (lock forever).

## What a VK Actually Is (Kimchi)

In Kimchi/Pickles, the `VerifierIndex` is a collection of polynomial commitments (sigma, coefficients, gates) plus domain parameters. Its `digest()` method hashes these commitments into a single field element. This digest IS the verification key hash stored on-chain. Changing any gate constraint, any wiring, any lookup table — all produce a different digest. The VK is the program.

## The Binding Question for Pyana

We already have `CellId = BLAKE3(public_key || token_id)` — identity is independent of the VK. This is Option B from the design space, matching Mina's model. The VK is a mutable field on the Cell struct, gated by `permissions.set_verification_key`.

This is the right choice. Rationale: a sovereign cell represents a persistent agent identity. The agent's *capabilities* and *relationships* accumulate over time. Forcing a new identity on every program upgrade destroys the social graph. The cell's program is what it *does*; the CellId is who it *is*.

## Who Decides Transition Rules

The current `CellProgram` enum already supports three modes: `None` (permissive), `Predicate` (declarative constraints), and `Circuit { circuit_hash }`. For sovereign cells specifically:

- **Verifier**: whoever accepts the proof. In federated mode, the federation node. In p2p mode, the counterparty.
- **Upgrade authority**: the current program. If `set_verification_key` requires `Proof`, then the current circuit must produce a proof authorizing its own replacement. This is self-upgrading.
- **Recovery**: if the program is buggy (e.g., always rejects), the cell is bricked unless `set_verification_key` also accepts `Signature`. This is an intentional tradeoff — security vs. recoverability.

## Upgrade Strategies

1. **Immutable** (`set_verification_key: Impossible`). Deploy once, never change. Appropriate for conservation-law cells (token contracts).

2. **Self-upgrading** (`set_verification_key: Proof`). The current circuit includes an "upgrade" public input. To change VK, prove: "under my current rules, VK' is a valid successor." This lets circuits encode upgrade policies (e.g., "new VK must preserve all existing constraints plus additions").

3. **Owner-signed** (`set_verification_key: Signature`). The cell owner can swap programs freely. Appropriate for personal agent cells where the owner IS the trust root. Counterparties must decide whether they trust this cell's *identity* or its *program*.

4. **Time-locked** (not yet in our model). Announce VK change at nonce N, enforce delay before activation. Requires the executor to track pending upgrades. Worth adding later, not now.

5. **Dual-mode** (backward-compatible). During transition window, accept proofs from either old or new VK. Complex; defer unless we find a concrete need.

## The "Which AIR" Question

We have: `DerivationAir` (Datalog step), `FoldAir` (attenuation), `MultiStepDerivationAir` (batched derivation), `StateTransitionAir` (IVC hash chain), and the IVC composition. A sovereign cell needs to declare which AIR(s) constitute its program.

**Recommended model**: the `circuit_hash` in `CellProgram::Circuit` identifies a *composition*. It is the BLAKE3 hash of the full serialized verifier parameters (analogous to Kimchi's `VerifierIndex.digest()`). The cell does NOT pick individual AIRs by name — it commits to the entire compiled circuit artifact. Whether that artifact internally uses DerivationAir + FoldAir or a single custom AIR is opaque to the cell layer.

This means: `VK.hash == circuit_hash`. The `VerificationKey` struct on the cell already stores `hash: [u8; 32]` and `data: Vec<u8>`. The hash is the program identity; the data is the serialized verifier state needed to actually check proofs.

## Peer-to-Peer Verification

Bob needs Alice's VK to verify her proofs. Three options:

1. **VK-in-first-message**: Alice sends her VK (or a commitment to it) in her first interaction with Bob, like a TLS certificate. Bob pins it. If Alice upgrades, she must re-introduce herself.

2. **VK derivable from state commitment**: the cell's `state_commitment()` already includes the VK hash transitively (via permissions). But Bob needs the full VK data to verify, not just the hash.

3. **Gossip/DHT**: VKs published to a lightweight DHT keyed by CellId. No central authority, but requires network availability.

**Recommendation**: Option 1 with pinning. Alice's sovereign cell proof includes the VK hash as a public input. Bob stores `(CellId -> VK)` in his local trust store. On upgrade, Alice presents the *old* proof authorizing the new VK, then the new VK. Bob verifies the upgrade chain and updates his pin. This is the self-certifying model — no registry needed.

## Recommended Approach

1. Keep `CellId` independent of VK (already done).
2. `CellProgram::Circuit { circuit_hash }` is the VK hash. The `VerificationKey` on the cell holds the full verifier data.
3. Default sovereign cells to `set_verification_key: Proof` — self-upgrading. Personal cells can opt into `Signature` for flexibility.
4. The proof's public inputs MUST include the VK hash (binds proof to program). Verifiers reject proofs where the embedded VK hash does not match the cell's stored VK.
5. P2P verification uses VK-pinning with upgrade chains. No registry.
6. `circuit_hash` is opaque — it might be a single AIR or a composition. The cell layer does not care which AIRs are inside.

This gives us Mina's flexibility (mutable VK, permission-gated) without Mina's centralization (no global chain required for p2p mode), while keeping the sovereign cell's identity stable across program upgrades.
