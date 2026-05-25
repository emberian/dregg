# Trust Model Architecture

This document defines the trust boundaries in the Pyana protocol stack and the
verification properties at each level.

## Trust Levels

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│   TRUSTLESS (cryptographically enforced)                                    │
│   ┌───────────────┐  ┌───────────────┐  ┌───────────────────────────────┐  │
│   │  circuit/     │  │  blocklace/   │  │  intent/trustless.rs          │  │
│   │  STARK proofs │  │  consensus    │  │  (threshold + STARK solving)  │  │
│   │  + Plonky3    │  │  finality     │  │                               │  │
│   └───────┬───────┘  └───────┬───────┘  └───────────────┬───────────────┘  │
│           │                  │                           │                  │
├───────────┼──────────────────┼───────────────────────────┼──────────────────┤
│           │                  │                           │                  │
│   EXECUTOR-TRUSTED (federation BFT replication)         │                  │
│   ┌───────┴───────┐  ┌──────┴────────┐  ┌──────────────┴────┐             │
│   │  turn/        │  │  captp/       │  │  intent/           │             │
│   │  executor     │  │  session,     │  │  matcher, solver   │             │
│   │  (classical)  │  │  swiss table  │  │  (current path)    │             │
│   └───────┬───────┘  └──────┬────────┘  └───────────────────┘             │
│           │                  │                                              │
├───────────┼──────────────────┼──────────────────────────────────────────────┤
│           │                  │                                              │
│   OPERATOR-TRUSTED (bonded, disputable)                                    │
│   ┌───────┴───────┐  ┌──────┴────────┐                                    │
│   │  storage/     │  │  captp/       │                                    │
│   │  relay nodes  │  │  store_forward│                                    │
│   │  (bonded)     │  │  (relay)      │                                    │
│   └───────────────┘  └───────────────┘                                    │
│                                                                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   CLIENT-LOCAL (user's device only)                                        │
│   ┌───────────────┐  ┌───────────────┐                                    │
│   │  sdk/         │  │  cclerk       │                                    │
│   │  agent runtime│  │  key mgmt     │                                    │
│   └───────────────┘  └───────────────┘                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘

TRANSPORT (not a trust boundary):
┌───────────────┐
│  wire/        │  Authenticated channels (TLS + PeerRole)
│  codec, server│  Does NOT verify payload semantics
└───────────────┘
```

## Boundary Crossings

### Client -> Executor Boundary

| What crosses | How it's verified | What's assumed |
|---|---|---|
| Signed turns | Ed25519 signature + nonce | Client's key is not compromised |
| STARK proofs | Circuit verification (trustless!) | Nothing (proof is self-validating) |
| Fee payment | Balance check | Client has sufficient computrons |

### Executor -> Trustless Boundary

| What crosses | How it's verified | What's assumed |
|---|---|---|
| Sovereign cell state | STARK proof (Effect VM) | Hash function security |
| Presentation proofs | Circuit constraints | Circuit is correctly encoded |
| Blocklace finality | Supermajority signatures | Honest >2/3 participants |

### Executor -> Operator Boundary

| What crosses | How it's verified | What's assumed |
|---|---|---|
| Storage writes | Content-addressed (BLAKE3) | Operator stores honestly |
| Relay messages | Encrypted (X25519) | Operator delivers (liveness) |
| Quota charges | Executor-enforced metering | Federation charges correctly |

### Operator -> Client Boundary

| What crosses | How it's verified | What's assumed |
|---|---|---|
| Stored data | BLAKE3 hash verification | Nothing (integrity is cryptographic) |
| Erasure chunks | Reconstruction + hash check | Sufficient honest operators |
| Relayed messages | Authenticated decryption | Relay did not drop (liveness only) |

## Per-Crate Trust Summary

| Crate | Trust Level | Soundness Property | Failure Mode |
|---|---|---|---|
| `circuit/` | Trustless | Valid proof => valid witness | Soundness bug => forged tokens |
| `blocklace/` | Consensus-Trustless | Finalized => permanent | >1/3 Byzantine => fork |
| `turn/` (sovereign) | Trustless | STARK proof verified | Verifier bug => invalid state |
| `turn/` (classical) | Executor-Trusted | BFT replicated | >1/3 Byzantine => wrong state |
| `captp/` (handoff) | Trustless | Signature verified | Ed25519 break => forged certs |
| `captp/` (session) | Executor-Trusted | Replicated state | Executor compromise => leaked caps |
| `intent/` (trustless) | Trustless | STARK + threshold | Threshold break => front-running |
| `intent/` (current) | Executor-Trusted | Replicated matching | Executor censors matches |
| `storage/` | Operator-Trusted | Content-addressed | Withholding => data unavailable |
| `wire/` | Transport | TLS + replay protection | Not a trust boundary |
| `sdk/` | Client-Local | Local-only | Device compromise => key theft |

## Path: Executor-Trusted -> Trustless

The long-term goal is to minimize the executor-trusted surface. Here is the
migration plan for each component:

### 1. Turn Execution (in progress)

**Current**: Classical call-forest execution (executor interprets effects).
**Target**: All turns carry STARK proofs (Effect VM covers all effect types).
**Status**: Phase 3 (sovereign cells) is complete. Phase 4 will extend to
all cell types.

### 2. Intent Solving (designed, partially implemented)

**Current**: Executor evaluates matches and runs the ring solver.
**Target**: `intent/trustless.rs` 7-layer protocol with threshold encryption
and STARK-proven solutions.
**Status**: Protocol implemented, needs production threshold crypto and real
STARK solver circuit.

### 3. Authorization Verification

**Current**: Executor checks Ed25519 signatures and delegates to ProofVerifier.
**Target**: All authorizations expressed as STARK proofs (signature verification
circuit already exists in `circuit/schnorr_air`).
**Status**: Signature verification is executor-side. Need to wrap Ed25519 verify
in a circuit for full trustlessness.

### 4. Precondition Evaluation

**Current**: Executor evaluates temporal/state guards.
**Target**: Preconditions proven inside the Effect VM circuit.
**Status**: Not started. Requires extending the Effect VM AIR with conditional
constraints.

### 5. Fee Metering

**Current**: Executor counts computrons and deducts fees.
**Target**: Fee accounting proven in the turn proof (balance conservation check).
**Status**: The `FullConservationProof` in `pyana_cell` already proves balance
conservation for note-based transfers. Need to extend to computron metering.

## Security Invariants

These properties MUST hold across all trust levels:

1. **No capability escalation**: A token can only be attenuated (narrowed), never
   widened. Enforced by the circuit's fold AIR constraints.

2. **Balance conservation**: Total supply is constant except for explicit minting
   (epoch minter) and burning (fee burn). Enforced by the executor + conservation
   proofs.

3. **Nonce monotonicity**: Each cell's nonce strictly increases. Prevents replay.
   Enforced by the executor (Phase 2) and the Effect VM (Phase 3+).

4. **Causal consistency**: Effects are applied in a deterministic order derived from
   the blocklace's topological sort. No observer sees a different ordering.

5. **Confinement**: A capability cannot escape its confinement boundary (cell
   permissions + revocation channels). Enforced by the executor's authorization check.
