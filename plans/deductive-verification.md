# Deductive Verification Framework for Proof Composition

## Problem Statement

Pyana composes multiple zero-knowledge proofs to form a complete authorization
proof. Each proof (IVC fold chain, Merkle membership, Datalog derivation, effect
VM execution) proves one piece of the puzzle, and they are composed together in
the PresentationProof. But **how do we know the composition is sound?**

Specifically:
- Do all proof outputs feed correctly-typed inputs to downstream proofs?
- Are there semantic type mismatches hidden behind "it's all field elements"?
- Which properties are actually cryptographically enforced vs. trust-dependent?
- Where exactly is the trust boundary?

## Approach: Typed Composition Checking

**Key insight:** We don't need a full theorem prover (Coq, Lean, etc.). We need a
TYPED COMPOSITION CHECKER. Each proof has:

1. **Input types** — what it requires (public inputs with semantic types)
2. **Output types** — what it guarantees (properties proven if verification passes)
3. **Assumptions** — what must be true externally for the proof to be meaningful
4. **Bindings** — how inputs/outputs connect to other proofs

If we model these as a type system, **composition checking becomes type checking.**

## Architecture

```
                    CompositionGraph
                    ┌────────────────────────────────────┐
                    │                                    │
                    │  ProofStatement[]                  │
                    │    - public_inputs: TypedInput[]   │
                    │    - guarantees: Property[]        │
                    │    - assumptions: Assumption[]     │
                    │    - discharges: Discharge[]       │
                    │                                    │
                    │  CompositionBinding[]              │
                    │    - source_proof.output[i]        │
                    │    - target_proof.input[j]         │
                    │    - semantic_type (must match)    │
                    │                                    │
                    └──────────────┬─────────────────────┘
                                   │
                         ┌─────────┼─────────┐
                         │         │         │
                    ┌────▼───┐ ┌──▼──┐ ┌───▼────┐
                    │ Type   │ │Cycle│ │Assump- │
                    │ Check  │ │Check│ │tion    │
                    │        │ │     │ │Coverage│
                    └────────┘ └─────┘ └────────┘
                         │         │         │
                         └─────────┼─────────┘
                                   │
                         ┌─────────▼─────────┐
                         │  AnalysisResult   │
                         │  - type_errors    │
                         │  - gaps           │
                         │  - guarantees     │
                         │  - trust_boundary │
                         └───────────────────┘
```

## Semantic Type System

Instead of treating all public inputs as "BabyBear field elements," we assign
semantic types that carry meaning:

| Type | Meaning | Example |
|------|---------|---------|
| StateCommitment | Poseidon2 hash of cell state | fold chain roots |
| MerkleRoot | Root of a Merkle tree | federation_root |
| ActionBinding | H(action, resource) | request_predicate |
| EffectsHash | Hash of effect sequence | EffectVM output |
| Nonce | Monotonic counter | step_count, verifier_nonce |
| NullifierHash | Spend-once token | note spending |
| AccumulatedHash | Running IVC hash chain | IVC accumulator |
| PresentationTag | Blinded unlinkability tag | presentation_tag |
| CompositionCommitment | Sub-proof binding | composition_commitment |

A binding between proofs must have **matching semantic types on both sides**.
This catches bugs like accidentally connecting a Balance output to a MerkleRoot
input — they're both field elements but semantically incompatible.

## Four Checks

### 1. Type Consistency

For every binding `source.output[i] -> target.input[j]`:
- source.public_inputs[i].semantic_type == target.public_inputs[j].semantic_type
- Both match the binding's declared semantic_type

### 2. Acyclicity

The proof composition graph must be a DAG. Cycles would mean proof A depends on
proof B which depends on proof A — logically circular and unsound.

Uses Kahn's algorithm (topological sort) for O(V+E) detection.

### 3. Assumption Coverage

Every assumption must be either:
- **Discharged by another proof** — a downstream proof's guarantee covers it
- **Discharged by protocol** — a protocol mechanism (challenge-response, etc.)
- **Flagged as trust required** — explicitly documented trust assumption

Undischarged assumptions are either bugs or undocumented trust requirements.

### 4. Gap Detection

Every non-external input should have a binding from another proof. Inputs with
no source are either:
- **External inputs** (provided by the environment: federation_root from consensus,
  timestamp from verifier, action from the authorization request)
- **Gaps** that indicate missing composition rules

## Findings from Pyana Analysis

### Cryptographically Enforced (11 guarantees)

1. Fold chain monotonicity (capabilities only narrow)
2. Hash chain integrity (no fold steps omitted)
3. Valid state transitions (fold chain)
4. Issuer federation membership (Merkle inclusion)
5. Datalog derivation correctness
6. Effect VM state transition validity
7. Effect conservation (no value creation/destruction)
8. Presentation unlinkability
9. Sub-proof binding (no mix-and-match)
10. Membership (via presentation)
11. Authorization (via presentation)

### Trust Requirements (7 assumptions)

| Component | What's Trusted | Impact if Violated |
|-----------|---------------|-------------------|
| Cell executor | Correct state commitment | Derivation proves against fake state |
| Cell executor | Atomic effect application | Partial effects applied |
| Federation consensus | Key revocation propagation | Revoked keys still valid |
| Verifier clock | Block height accuracy | Expired tokens accepted |
| Prover RNG | Randomness quality | Presentations linkable (privacy) |

### Composition Gaps (12 unbound inputs)

Most gaps are **by design** — they are external inputs provided by the environment:
- `federation_root`: comes from the verifier's local state
- `presentation_tag`: computed by the prover (private + random)
- `effects_hash`: comes from the executor
- `old_state_commitment`: comes from the cell's persisted state

The gap analysis helps distinguish "external input" from "missing binding."

## Trust Boundary Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│  CRYPTOGRAPHIC LAYER (trustless)                                │
│                                                                 │
│  ┌──────────┐    ┌────────────┐    ┌──────────────┐           │
│  │ IVC Fold │───▶│ Derivation │    │  Membership  │           │
│  │ Chain    │    │ Proof      │    │  Proof       │           │
│  └──────────┘    └────────────┘    └──────────────┘           │
│       ▲                                    ▲                   │
│       │                                    │                   │
├───────┼────────────────────────────────────┼───────────────────┤
│  TRUST BOUNDARY                            │                   │
├───────┼────────────────────────────────────┼───────────────────┤
│       │                                    │                   │
│  ┌────┴──────┐                    ┌───────┴────────┐          │
│  │ Executor  │                    │ Federation     │          │
│  │ (state    │                    │ (root          │          │
│  │  compute) │                    │  freshness)    │          │
│  └───────────┘                    └────────────────┘          │
│                                                                 │
│  TRUST LAYER (requires honest components)                      │
└─────────────────────────────────────────────────────────────────┘
```

## Future Extensions

1. **Fraud proofs**: For trust assumptions (executor), add a fraud proof circuit
   that can prove misbehavior. This would discharge TrustedExecution assumptions
   with "trust + slash" instead of pure trust.

2. **Recursive verification**: When Plonky3 recursion is production-ready, the
   IVC fold chain can verify previous proofs inside the circuit, eliminating the
   hash-chain accumulation approach.

3. **Formal extraction**: The ProofStatement model could be exported to Lean4 or
   Coq for machine-checked verification of the composition properties.

4. **CI integration**: Run `cargo run -p pyana-verification` in CI to catch
   composition regressions when proof interfaces change.

## Usage

```bash
cd verification/
cargo run       # Full analysis report
cargo test      # Verify model consistency
```

The tool exits with code 1 if type errors or cycles are detected, making it
suitable for CI gating.
