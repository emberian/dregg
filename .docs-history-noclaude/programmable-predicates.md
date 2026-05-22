# Programmable Private Predicates

The unifying abstraction over all predicate types in pyana.

---

## 1. The Unifying Abstraction

Every proof in pyana is an instance of one primitive:

```
prove_program(program, private_input) -> proof
```

- **program**: A function `f: PrivateState -> bool` — the predicate.
- **private_input**: The prover's state (token facts, balances, history, relations).
- **proof**: A STARK convincing any verifier that the program accepted on SOME valid
  input, without revealing the input.

The existing circuit layer already implements several specializations of this primitive:

| Existing AIR | What it proves | Program (fixed shape) | Private input |
|---|---|---|---|
| `PredicateAir` | value >= threshold | Range comparison | The value |
| `CompoundPredicateAir` | Boolean combo of range checks | AND/OR/Threshold formula | N values |
| `TemporalPredicateAir` | Predicate held for N steps | Range check at each step | N values + state roots |
| `CommittedThresholdAir` | value >= committed threshold | Range + commitment check | Value + threshold + blinding |
| `MultiStepDerivationAir` | Datalog program concludes ALLOW | Policy rule set | Facts + derivation trace |
| `MerklePoseidon2StarkAir` | Value is member of committed set | Membership check | The value + Merkle path |
| `NonRevocationAir` | Value is NOT in a set | Non-membership check | The value + sorted tree |

These are all **programs** over **private inputs** producing a **single bit** (pass/fail).
The unification recognizes that the "program" can be expressed in a single language —
extended Datalog — and compiled to whichever underlying AIR is appropriate.

### The Universal Interface

```rust
/// A programmable predicate: a program that can be proven in zero knowledge.
pub trait PrivatePredicate {
    /// The program (rules, constraints, built-in invocations).
    fn program(&self) -> &PredicateProgram;

    /// Evaluate locally: can the prover satisfy this with their state?
    fn evaluate(&self, state: &PrivateState) -> bool;

    /// Compile to an AIR and generate a STARK proof.
    fn prove(&self, state: &PrivateState) -> Option<PredicateProof>;

    /// Verify a proof against public inputs.
    fn verify(&self, proof: &PredicateProof, public_inputs: &PublicInputs) -> bool;

    /// Commit to this program (for committed/marketplace scenarios).
    fn commit(&self) -> ProgramCommitment;
}
```

---

## 2. The Predicate Language

The natural language for programmable predicates is **Datalog extended with built-in
predicates**. This leverages the existing `pyana_trace` evaluator and `MultiStepDerivationAir`.

### 2.1 Core Syntax

```datalog
% Simple range predicate (dispatches to PredicateAir)
allow :- balance(B), B >= 1000.

% Compound boolean (dispatches to CompoundPredicateAir)
allow :- age(A), country(C), A >= 18, member(C, {US, CA, UK}).

% Temporal accumulation (dispatches to TemporalPredicateAir)
allow :- held_for(balance, 1000, 30).

% Relational comparison (dispatches to committed-threshold protocol)
allow :- compare(my_balance, their_balance, gte).

% Threshold/quorum
allow :- at_least(2, [verified_email, phone_verified, kyc_passed]).

% Nested composition
allow :- (age(A), A >= 21) ; (guardian_consent, age(A), A >= 16).
```

### 2.2 Built-in Predicates

Each built-in maps to a specialized AIR:

| Built-in | Semantics | Underlying AIR |
|---|---|---|
| `X >= Y` | Range comparison | `PredicateAir(Gte)` |
| `X <= Y` | Range comparison | `PredicateAir(Lte)` |
| `X > Y` | Strict comparison | `PredicateAir(Gt)` |
| `X < Y` | Strict comparison | `PredicateAir(Lt)` |
| `X != Y` | Inequality | `PredicateAir(Neq)` |
| `in_range(X, L, H)` | Interval membership | `PredicateAir(InRangeLow)` + `PredicateAir(InRangeHigh)` |
| `member(X, Set)` | Set membership | `MerklePoseidon2StarkAir` |
| `not_member(X, Set)` | Non-membership | `NonRevocationAir` |
| `held_for(Attr, Threshold, Duration)` | Temporal continuity | `TemporalPredicateAir` |
| `committed_gte(Value, Commitment)` | Private threshold | `CommittedThresholdAir` |
| `at_least(K, Predicates)` | Threshold gate | `CompoundPredicateAir(Threshold)` |
| `all(Predicates)` | Conjunction | `CompoundPredicateAir(And)` |
| `any(Predicates)` | Disjunction | `CompoundPredicateAir(Or)` |

### 2.3 Fact Binding

Every variable in a predicate program is bound to a committed fact in the prover's
token state via `fact_commitment = Poseidon2(fact_hash, state_root)`. This is enforced
by the AIR constraints — the prover cannot fabricate values not in their actual state.

### 2.4 Program Representation

A predicate program is a structured value:

```rust
pub struct PredicateProgram {
    /// The Datalog rules (head + body + checks).
    pub rules: Vec<PredicateRule>,
    /// Built-in invocations referenced by the rules.
    pub builtins: Vec<BuiltinInvocation>,
    /// The program's content hash (for commitment/addressing).
    pub hash: BabyBear,
}

pub enum BuiltinInvocation {
    Range { var: VarId, op: PredicateType, threshold: BabyBear },
    Membership { var: VarId, set_root: BabyBear },
    Temporal { attr: Symbol, threshold: BabyBear, duration: u32 },
    CommittedThreshold { var: VarId, commitment: BabyBear },
    Compound { formula: BooleanFormula, sub_predicates: Vec<BuiltinInvocation> },
}
```

---

## 3. Compilation to AIR

### 3.1 The Compilation Pipeline

```
PredicateProgram
    │
    ▼
┌─────────────────────┐
│  Program Analyzer   │  Determine which built-ins are needed
└─────────────────────┘
    │
    ▼
┌─────────────────────┐
│  AIR Selector       │  Map each built-in to its specialized AIR
└─────────────────────┘
    │
    ▼
┌─────────────────────┐
│  Witness Generator  │  Fill traces from private state
└─────────────────────┘
    │
    ▼
┌─────────────────────┐
│  Proof Compositor   │  Compose sub-proofs into a single proof
└─────────────────────┘
    │
    ▼
PredicateProof (verifiable by anyone)
```

### 3.2 Simple Programs: Direct AIR Mapping

For programs that use a single built-in, compilation is trivial:

```datalog
allow :- balance(B), B >= 1000.
```

Compiles to: `PredicateAir { witness: { private_value: B, threshold: 1000, ... } }`

### 3.3 Compound Programs: Multi-AIR Composition

For programs using multiple built-ins:

```datalog
allow :- age(A), balance(B), A >= 18, B >= 1000.
```

Compiles to:
```
CompoundPredicateAir {
    predicates: [
        PredicateWitness { value: A, threshold: 18, type: Gte },
        PredicateWitness { value: B, threshold: 1000, type: Gte },
    ],
    formula: And([0, 1]),
}
```

### 3.4 Full Datalog Programs: Multi-Step Derivation

For programs with multiple rules, recursion, or non-trivial variable bindings:

```datalog
premium_member :- balance(B), B >= 10000.
premium_member :- invited_by(I), premium_member_by(I).
allow :- premium_member, not_revoked.
```

Compiles to: `MultiStepDerivationAir` with the full rule set as `policy_root` and
the derivation trace as the witness. The existing `multi_step_air.rs` already handles
up to 32 derivation steps, 8 body atoms per rule, and 8 variables.

### 3.5 Parameterized AIR (the Truly Programmable Case)

For a FULLY programmable system where the program is not known at circuit-compile time,
the AIR itself must be parameterized by the program:

```
Public Inputs: [program_hash, fact_commitment, result_bit]
Private Witness: [program_bytecode, facts, derivation_trace]

Constraints:
1. Poseidon2(program_bytecode) == program_hash           (program binding)
2. Datalog_eval(program_bytecode, facts) == result_bit   (correct evaluation)
3. Facts are bound to fact_commitment                    (state binding)
```

This is the `MultiStepDerivationAir` with `policy_root` as the program hash. The
verifier need not know the program details — only its hash and that it accepted.

---

## 4. Program Supply Models

### 4.1 Verifier-Supplied Programs

The verifier sends a predicate program as part of their request:

```
Verifier -> Prover: "Prove you satisfy this program: [rules...]"
Prover evaluates locally, generates proof
Prover -> Verifier: proof
```

**Properties:**
- The prover learns the full program (needed to generate the proof).
- The verifier learns only pass/fail (from whether a valid proof arrives).
- Third parties learn nothing (the program is not broadcast).

**When to use:** Standard authorization checks, credit verification, access control.

**Already implemented:** This is exactly what `verify_token_datalog()` does in trusted
mode, and what `prove_authorization_stark()` does in trustless mode.

### 4.2 Committed Programs

The verifier commits to a program without revealing it:

```
program_hash = Poseidon2(program_bytes)

Verifier -> World: program_hash                    (public commitment)
Verifier -> Prover: program_bytes (sealed channel) (private reveal)
Prover generates proof with program_hash as public input
```

**Properties:**
- Third parties see only `program_hash` — they learn "some program was satisfied" but
  not which program.
- The prover learns the program (necessary for proof generation).
- The verifier can prove WHICH program they committed to by revealing the preimage later.

**When to use:** Proprietary business logic (hiring thresholds, risk models, scoring
algorithms) where the program itself is a trade secret.

**Implementation:** The `CommittedThresholdAir` is a special case of this pattern (the
"program" is just `value >= threshold`). The general case uses `MultiStepDerivationAir`
with `policy_root` as the commitment.

### 4.3 Program Marketplace

Programs are published as content-addressed objects:

```
Programs are identified by hash: program_id = Poseidon2(program_bytes)
Anyone can prove their state satisfies a published program.
Programs compose: one program can reference another by hash.
```

**Properties:**
- Programs are public (anyone can inspect them).
- Privacy comes from the INPUTS, not the program.
- Programs become a shared vocabulary: "satisfies program 0xABC..." is meaningful.
- Composition: `allow :- satisfies(user, program_X), satisfies(user, program_Y).`

**When to use:** Standards compliance (KYC/AML programs), industry certifications,
platform-wide access policies, governance proposals.

**Analogy:** Smart contracts are programs on public state. Programmable predicates are
programs on PRIVATE state.

### 4.4 Comparison of Supply Models

| Dimension | Verifier-supplied | Committed | Marketplace |
|---|---|---|---|
| Who knows the program? | Prover + Verifier | Prover + Verifier | Everyone |
| Third-party visibility | Nothing | program_hash only | Full program |
| Prover privacy (inputs) | Full ZK | Full ZK | Full ZK |
| Program reusability | One-shot | Reusable via hash | Fully reusable |
| Composability | None | By hash reference | Full |
| Trust model | Trust verifier's intent | Trust commitment binding | Trust the code |

---

## 5. Intent Integration

### 5.1 Intents as Predicate Program Matching

An intent becomes: "I need someone who satisfies program P."

```rust
pub struct PredicateIntent {
    /// The predicate program (or its commitment).
    pub program: ProgramRef,
    /// How the program is supplied.
    pub supply: ProgramSupplyModel,
    /// Expiry, stake, metadata.
    pub meta: IntentMeta,
}

pub enum ProgramRef {
    /// Full program inline (verifier-supplied model).
    Inline(PredicateProgram),
    /// Content hash only (committed or marketplace model).
    Hash(BabyBear),
    /// Marketplace reference with human-readable name.
    Named { hash: BabyBear, name: String },
}

pub enum ProgramSupplyModel {
    /// Program is in the intent (public to all who see the intent).
    Public,
    /// Program hash is in the intent; full program revealed on handshake.
    CommittedRevealOnHandshake,
    /// Program is in the marketplace (everyone can look it up).
    Marketplace,
}
```

### 5.2 Fulfillment as Proof

Fulfilling a predicate intent means generating a proof:

```
1. Wallet sees intent with program P (or obtains P via handshake).
2. Wallet evaluates P locally against its private state.
3. If satisfiable: wallet generates PredicateProof.
4. Wallet sends proof as fulfillment.
5. Intent creator verifies proof against P's public inputs.
```

**Privacy guarantees in the fulfillment:**
- The fulfiller reveals only that they satisfy P — not their values, token chain, or
  other capabilities.
- The intent creator learns only pass/fail (plus the binding to a specific state root
  for freshness).
- Other observers of the gossip network see only the intent hash and that it was
  fulfilled.

### 5.3 Private Intent Matching (Committed Programs)

For the committed model, the full protocol is:

```
Creator broadcasts: { intent_id, program_hash, shape_hint, expiry }
                                    │
Potential fulfiller sees shape hint, decides to engage
                                    │
Handshake: fulfiller sends ephemeral pubkey
                                    │
Creator encrypts program to fulfiller's key, sends sealed program
                                    │
Fulfiller evaluates locally, generates proof if satisfiable
                                    │
Fulfiller sends proof (or declines silently)
```

The shape hint (e.g., "this concerns balance predicates") enables routing without
revealing the exact program. The existing `TemporalPredicateRequirement` in
`temporal_predicate_air.rs` already sketches this pattern for temporal intents.

---

## 6. The Capability Type System

### 6.1 Programs Define What Capabilities Mean

In pyana, a capability is an attenuated token chain ending in specific facts. Today,
capability MEANING is implicit — the verifier interprets fact values. With programmable
predicates, meaning becomes explicit:

```
Capability "Premium Access" = Program {
    allow :- balance(B), B >= 10000.
    allow :- tier(T), T == "enterprise".
    allow :- invited_by(I), known_premium(I).
}
```

A capability TYPE is a predicate program. Holding a capability means possessing private
state that satisfies the program. Proving a capability means generating a STARK proof.

### 6.2 Subtyping via Implication

Program A is a subtype of program B if satisfying A implies satisfying B:

```
Program "Enterprise" = { allow :- tier(T), T == "enterprise". }
Program "Premium"    = { allow :- balance(B), B >= 10000.
                         allow :- tier(T), T == "enterprise". }
```

Enterprise implies Premium (it's one of Premium's disjuncts). This subtyping relationship
can be checked statically (Datalog containment) or dynamically (if you have a proof for
Enterprise, you can generate a proof for Premium).

### 6.3 Attenuation as Program Restriction

Token attenuation (the fold chain) becomes program refinement:

```
Original program: { allow :- app(A), action(X). }
After attenuation: { allow :- app(A), action(X), A == "specific_app". }
```

Each fold step NARROWS the program (adds constraints). The IVC chain proves that each
step is a valid restriction. The final program is the most restricted — the actual
capability presented.

### 6.4 Composition as Program Conjunction

Composing two capabilities is program conjunction:

```
Combined = Program_A AND Program_B
         = { allow :- satisfies(Program_A), satisfies(Program_B). }
```

The proof is a compound proof (CompoundPredicateAir) over two sub-proofs.

---

## 7. Security Model

### 7.1 What If the Program is Malicious?

A malicious verifier could supply a program designed to:
- **Extract information**: A program that only accepts if specific private values are used,
  leaking information through the accept/reject bit.
- **Cause DoS**: A program with exponential evaluation cost.
- **Exploit the prover**: A program that triggers bugs in the prover software.

**Mitigations:**

#### Information Extraction

The accept/reject bit ALWAYS leaks 1 bit of information. This is inherent and cannot be
avoided. A carefully crafted program could narrow this to extract more:

```
% Malicious: binary search on balance
allow :- balance(B), B >= 500.  % First query: learn if B >= 500
allow :- balance(B), B >= 750.  % Second query: narrow further
```

**Defense**: The prover sees the full program before deciding whether to prove. The wallet
UI presents: "Service X is asking you to prove: balance >= 500. Approve?" The user can
decline. Rate limiting prevents rapid binary search.

**Stronger defense (committed programs):** If the program is committed (the prover
doesn't see it), use the OT/MPC approach from `mpcith-predicates.md` — the prover
evaluates without learning the program details.

#### Resource Exhaustion

Datalog without negation or recursion limits terminates in polynomial time. The built-in
evaluator enforces:

```rust
pub struct ResourceLimits {
    /// Maximum derivation steps (prevents infinite loops).
    pub max_steps: u32,         // default: 32 (MAX_STEPS in multi_step_air.rs)
    /// Maximum rule applications per step.
    pub max_rule_fires: u32,    // default: 64
    /// Maximum trace width (memory bound).
    pub max_trace_width: usize, // default: 256 columns
    /// Maximum proof generation time.
    pub timeout_ms: u64,        // default: 5000
}
```

Programs exceeding these limits are rejected before proof generation begins. The limits
are hardcoded in the AIR (MAX_STEPS = 32) so no malicious program can produce a valid
proof that exceeds them.

#### Prover Exploitation

All program evaluation occurs within the BabyBear field arithmetic layer. There are no
raw memory accesses, no syscalls, no I/O. The "virtual machine" for predicate programs
is the Datalog evaluator — a pure function with no side effects. Malformed programs
produce evaluation failures, not security vulnerabilities.

### 7.2 Termination Guarantee

Datalog without negation, function symbols, or unrestricted recursion is guaranteed to
terminate. The finite domain (BabyBear field elements as ground terms) ensures the
Herbrand base is finite. Combined with the step limit (MAX_STEPS = 32), every program
terminates within bounded time.

Programs with temporal built-ins have cost proportional to the temporal range (N steps).
This is bounded by the prover's willingness to compute, not by the program itself.

### 7.3 Soundness

All predicate proofs inherit soundness from the underlying STARK:

- **Computational soundness**: ~124-bit security via BabyBear4 extension field.
- **Fact binding**: The `fact_commitment` constraint prevents proving predicates over
  fabricated values. Every value must exist in the prover's committed state.
- **Program binding**: The `policy_root` public input ensures the verifier knows WHICH
  program was evaluated. The prover cannot substitute a weaker program.
- **Freshness**: Proofs are bound to specific state roots and timestamps, preventing
  replay.

### 7.4 Zero-Knowledge

- The verifier learns ONLY the public inputs (threshold, program hash, pass/fail).
- The private witness (values, derivation trace, intermediate states) is hidden.
- With presentation randomness, multiple proofs from the same prover are unlinkable.

---

## 8. Implementation Roadmap

### What Exists Today

| Component | Location | Status |
|---|---|---|
| Range predicates (GTE/LTE/GT/LT/NEQ/InRange) | `circuit/src/predicate_air.rs` | Complete |
| Boolean compound predicates (AND/OR/Threshold/Custom) | `circuit/src/compound_predicate_air.rs` | Complete |
| Temporal predicates (held-for-N-steps) | `circuit/src/temporal_predicate_air.rs` | Complete |
| Committed thresholds (private threshold + binding) | `circuit/src/committed_threshold.rs` | Complete |
| Multi-step Datalog derivation proving | `circuit/src/multi_step_air.rs` | Complete |
| Merkle membership (Poseidon2 4-ary tree) | `circuit/src/poseidon2_air.rs` | Complete |
| Non-revocation (sorted tree non-membership) | `circuit/src/non_revocation_air.rs` | Complete |
| IVC fold chain accumulation | `circuit/src/ivc.rs` | Complete |
| Real STARK prover (FRI + Merkle + Fiat-Shamir) | `circuit/src/stark.rs` | Complete |
| Datalog evaluator | `trace/src/eval.rs` | Complete |
| Token verification via Datalog | `token/src/datalog_verify.rs` | Complete |
| Intent engine + matching | `intent/src/` | Complete |
| MPC-in-the-head design | `docs/mpcith-predicates.md` | Design only |

### Phase 1: Predicate Program Type (2-3 weeks)

Define the `PredicateProgram` struct that unifies all predicate types:

1. **Program representation**: Datalog rules + built-in invocation list + content hash.
2. **Compiler front-end**: Parse a predicate program and determine which AIRs are needed.
3. **Dispatch table**: Map each built-in to its AIR, generate the appropriate witness.
4. **Unified proof type**: A `PredicateProof` that wraps the underlying proof(s) and
   carries the program hash.

### Phase 2: Composition Engine (2-3 weeks)

Build the proof compositor that handles multi-AIR programs:

1. **Sub-proof orchestration**: For a program needing PredicateAir + MerkleMembership,
   generate both proofs and compose them.
2. **Shared fact bindings**: Ensure all sub-proofs reference the same committed state.
3. **Composition proof**: A meta-proof that "these N sub-proofs all belong to the same
   program evaluation and all reference the same state root."
4. **Verification bundle**: Verifier checks all sub-proofs + composition proof.

### Phase 3: Intent Integration (2-3 weeks)

Wire programmable predicates into the intent system:

1. **ProgramRef in intents**: Intents carry inline programs, hashes, or marketplace refs.
2. **Fulfillment protocol**: Wallet evaluates program locally, generates proof bundle.
3. **Committed intent handshake**: X25519-sealed program delivery on engagement.
4. **Verification on fulfillment**: Intent creator verifies the proof bundle.

### Phase 4: Program Marketplace (3-4 weeks)

Content-addressed program registry:

1. **Storage**: Programs stored by hash in a content-addressed store.
2. **Publishing**: Authors publish programs with metadata (name, description, version).
3. **Discovery**: Search/browse programs by category, capability type, author.
4. **Versioning**: Programs are immutable (content-addressed); new versions are new hashes.
5. **Composition**: Programs can reference other programs by hash (import/require).

### Phase 5: Research Frontier (ongoing)

1. **Fully parameterized AIR**: The program itself as a public input, not just its hash.
   The trace proves correct evaluation of an ARBITRARY program. This requires a "Datalog
   VM" encoded as AIR constraints — a universal circuit.
2. **Program obliviousness**: Prove satisfaction of a program you don't know (via
   MPC-in-the-head, per `docs/mpcith-predicates.md`).
3. **Recursive composition**: Proofs-of-proofs via Plonky3 recursion, enabling
   constant-size proofs regardless of program complexity.
4. **Cross-program proofs**: "I satisfy programs A and B" in a single proof, with shared
   state binding (prevents using different states for A vs. B).

---

## 9. Comparison to Related Systems

### 9.1 Ethereum Smart Contracts

| Dimension | Ethereum | Pyana Programmable Predicates |
|---|---|---|
| Execution | Public (everyone re-executes) | Private (only prover executes) |
| State | Public (on-chain) | Private (in prover's wallet) |
| Verification | Re-execution | STARK proof verification |
| Privacy | None (all state visible) | Full ZK (only pass/fail revealed) |
| Cost model | Gas (per instruction) | Proof generation time (prover-local) |
| Composability | Contract calls | Program hash references |
| Upgradability | Proxy patterns, migration | Content-addressed (immutable programs) |

**Key difference**: Ethereum programs operate on PUBLIC state and produce PUBLIC results.
Pyana programs operate on PRIVATE state and produce PRIVATE results backed by PUBLIC proofs.

### 9.2 Zcash Circuits (Sapling/Orchard)

| Dimension | Zcash | Pyana Programmable Predicates |
|---|---|---|
| Circuit language | R1CS / Halo2 (fixed circuit) | Datalog (programmable) |
| What's proven | "I know a valid spend" (fixed statement) | Arbitrary predicate programs |
| Programmability | None (circuit is hardcoded) | Fully programmable via Datalog |
| Field | Pallas/Vesta (curves) | BabyBear (hash-based, PQ-safe) |
| Recursion | Halo2 accumulation | IVC + future Plonky3 recursion |
| Proof size | ~1 KB (Halo2) | ~24 KB (FRI-based STARK) |

**Key difference**: Zcash proves a FIXED statement ("this is a valid spend"). Pyana proves
ARBITRARY statements ("I satisfy whatever program you specify"). Zcash is a specific
application; pyana is a programmable substrate.

### 9.3 Mina zkApps

| Dimension | Mina | Pyana Programmable Predicates |
|---|---|---|
| Proof system | Kimchi (Plonk variant) | STARK (FRI-based) |
| Programming model | o1js (TypeScript DSL) | Datalog with built-ins |
| State model | On-chain state + off-chain Merkle trees | Fully private committed state |
| Privacy | Selective (some state private) | Full (all state private by default) |
| Recursion | Yes (Pickles) | IVC today, Plonky3 recursion planned |
| Post-quantum | No (curve-based) | Yes (hash-based STARK) |
| Verification | On-chain (constant cost) | Off-chain (verifier checks proof) |

**Key difference**: Mina zkApps still have on-chain state. The program's logic is
public (deployed as a verification key). In pyana, both the state AND the program can
be private (committed model). Mina's programming model is imperative (TypeScript); pyana's
is declarative (Datalog), enabling static analysis and containment checking.

### 9.4 Cairo Programs (Starknet)

| Dimension | Cairo/Starknet | Pyana Programmable Predicates |
|---|---|---|
| Language | Cairo (Rust-like imperative) | Datalog (declarative) |
| Execution model | Blockchain VM (public execution) | Prover-local (private execution) |
| Proof system | STARK (Stone/Stwo prover) | STARK (custom BabyBear prover) |
| State model | Contract storage (public) | Private committed state |
| Privacy | Not built-in (requires app-level) | Fundamental (ZK by default) |
| Expressiveness | Turing-complete | Datalog (decidable, terminates) |
| Verification cost | O(log n) on-chain | O(log n) anywhere |

**Key difference**: Cairo is a general-purpose STARK-proven language for public
computation. Pyana predicates are specifically designed for PRIVATE authorization — the
program's purpose is always "does this private state satisfy this condition?" Cairo
could express the same thing, but pyana's Datalog restriction gives termination
guarantees and enables the capability type system (subtyping via Datalog containment).

### 9.5 Summary Table

| | Public State | Private State | Programmable | PQ-Safe | Terminates |
|---|:---:|:---:|:---:|:---:|:---:|
| Ethereum | Yes | No | Yes | No | No* |
| Zcash | No | Yes | No | No | Yes |
| Mina | Partial | Partial | Yes | No | No* |
| Cairo/Starknet | Yes | No | Yes | Yes | No* |
| **Pyana** | **No** | **Yes** | **Yes** | **Yes** | **Yes** |

(*) Turing-complete languages don't guarantee termination; they use gas/step limits as
a practical bound. Pyana's Datalog restriction gives a STRUCTURAL termination guarantee.

---

## 10. The Vision

**Any statement about private state, provable in zero knowledge, matchable via intents.**

The full picture:

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Programmable Private Predicates                    │
│                                                                     │
│  "I need someone     Intent Layer      "I can satisfy         │
│   who satisfies P"  ─────────────────>  program P"            │
│                      (discovery)                               │
│                                                                     │
│  Program P          Predicate Layer     Private State S        │
│  (Datalog rules)   ─────────────────>  (committed facts)      │
│                      (evaluation)                              │
│                                                                     │
│  AIR constraints    Proof Layer         STARK proof            │
│  (compiled from P) ─────────────────>  (convinces anyone)     │
│                      (proving)                                 │
│                                                                     │
│  Proof              Verification        pass/fail              │
│  + public inputs   ─────────────────>  (1 bit output)         │
│                      (checking)                                │
└─────────────────────────────────────────────────────────────────────┘
```

The key properties, all holding simultaneously:

1. **Expressiveness**: Any statement that can be written as Datalog over committed facts
   can be proven. Range checks, set membership, temporal properties, boolean
   combinations, multi-step derivations — all in one framework.

2. **Privacy**: The prover reveals NOTHING about their state beyond the 1-bit
   accept/reject. Not the values, not the derivation path, not even which rule fired.

3. **Verifiability**: Anyone can verify a proof without re-executing the program or
   knowing the private inputs. Verification is O(log n) regardless of program complexity.

4. **Composability**: Programs reference other programs by hash. Proofs compose via
   compound AIRs. Capabilities (programs) form a type system with subtyping.

5. **Discoverability**: The intent layer matches "I need X" with "I can provide X"
   without either party revealing more than necessary.

6. **Post-quantum safety**: The entire stack (STARK proofs, Poseidon2 hashing, BabyBear
   arithmetic) is hash-based. No elliptic curve assumptions. No lattice problems.
   Secure against quantum computers.

7. **Programmability without Turing-completeness**: Datalog's restriction to finite,
   stratified programs guarantees termination, enables static analysis, and makes the
   capability type system decidable — while still being expressive enough for all
   real-world authorization policies.

This is the endgame for private authorization: not a fixed set of predicates with
hardcoded circuits, but a LANGUAGE for expressing what you need to prove, with
compilation to efficient STARK proofs, discovery via intents, and a type-theoretic
foundation for capability composition.
