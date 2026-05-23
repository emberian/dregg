// =============================================================================
// Section 16: Formal Verification
// =============================================================================

= Formal Verification <sec-formal>

== Typed Composition Checker

Pyana's proof system comprises 30+ circuit descriptors that must compose correctly. A _typed composition checker_ verifies at compile time that composed proofs maintain soundness---that public input/output types align, that witness bindings are consistent, and that trust assumptions compose without contradiction.

=== Circuit Descriptors

Each circuit in the system is described by a `CircuitDescriptor`:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Field*], [*Description*]),
    [`name: &str`], [Human-readable circuit identifier],
    [`public_inputs: Vec<TypedSlot>`], [Typed public input schema],
    [`public_outputs: Vec<TypedSlot>`], [Typed public output schema],
    [`witness_schema: Vec<TypedSlot>`], [Private witness structure],
    [`constraint_degree: usize`], [Maximum polynomial degree in AIR],
    [`trust_assumptions: Vec<Assumption>`], [Explicit trust model],
    [`soundness_bits: usize`], [Security parameter (typically 124)],
  ),
  caption: [CircuitDescriptor fields. The typed schema enables compile-time composition checking.],
)

=== Composition Rules

The four composition operators are type-checked:

*`compose_chain(A, B)`*: Sequential composition. Requires $A."public_outputs" supset.eq B."public_inputs"$ (type-compatible). The composed circuit proves "A then B" with $A$'s outputs fed as $B$'s inputs.

*`compose_and(A, B)`*: Parallel conjunction. Both proofs must be valid. Public inputs are the union of $A$ and $B$'s inputs. Trust assumptions are the union.

*`compose_or(A, B)`*: Parallel disjunction. At least one proof must be valid. Public inputs must have compatible types. Trust assumptions are the intersection (only assumptions common to both paths hold unconditionally).

*`compose_aggregate([A_1, ..., A_n])`*: Batch composition. All $n$ proofs are valid. Amortizes verification cost. Trust assumptions are the union of all components.

=== Type Errors Caught at Compile Time

The checker prevents:

- Feeding a nullifier (field element) where a state commitment (hash) is expected.
- Composing circuits with incompatible field sizes (BabyBear vs. BN254).
- Chaining circuits where the output of $A$ is a different Merkle root type than the input of $B$.
- Aggregating circuits with contradictory trust assumptions.

== The 30-Circuit Catalog

Pyana's proof system comprises the following verified circuit descriptors:

=== Core Cryptographic Circuits (8)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Poseidon2 Permutation], [7], [Correct hash computation],
    [Merkle Membership (4-ary)], [7], [Leaf exists in committed tree],
    [Merkle Non-Membership], [7], [Leaf does NOT exist in committed tree],
    [Note Spending], [7], [Nullifier correctly derived, note exists],
    [Range Proof], [3], [Value in range $[0, 2^k)$ without revealing value],
    [Pedersen Commitment], [5], [Value correctly committed with blinding],
    [Ed25519 Signature], [5], [Signature valid for message and public key],
    [BLS12-381 Aggregation], [7], [Aggregate signature valid],
  ),
  caption: [Core cryptographic circuits. These are the building blocks for all higher-level proofs.],
)

=== Authorization Circuits (6)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Fold (attenuation step)], [7], [Single capability restriction is valid],
    [Multi-Step Fold (IVC)], [7], [Chain of $k$ restrictions from root],
    [Derivation (Datalog)], [7], [Authorization rules yield "allow"],
    [Body Membership], [7], [Facts used in derivation exist in tree],
    [Blinded Issuer Ring], [7], [Issuer is in set without revealing which],
    [Presentation Randomization], [7], [Blinded tag correctly derived from root],
  ),
  caption: [Authorization circuits. Compose to prove "I am authorized" without revealing the chain.],
)

=== Effect VM Circuits (5)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [Effect VM (14 effects)], [7], [Arbitrary turn is valid (conservation + state + auth)],
    [Conservation], [3], [Total value in $=$ total value out],
    [State Continuity], [7], [Post-state correctly derived from pre-state + effects],
    [CapTP Send], [7], [Message correctly dispatched via protocol],
    [CapTP Handoff], [5], [Certificate correctly constructed],
  ),
  caption: [Effect VM circuits. The Effect VM composes all per-effect proofs into a single STARK per turn.],
)

=== Governance and Economics Circuits (6)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [DFA Classification], [3], [Message correctly classified by committed DFA],
    [Fee Sufficiency], [3], [Turn fee covers base fee + priority],
    [Stake Threshold], [3], [Staked value $>=$ minimum without revealing exact],
    [Budget Gate], [3], [Silo budget not exceeded (Stingray bounded counter)],
    [Conditional Turn], [7], [Turn executes only if condition proof verified],
    [Intent Satisfaction], [7], [Solution satisfies all intent constraints],
  ),
  caption: [Governance and economics circuits. Enable privacy-preserving economic participation.],
)

=== Bridge and Recursion Circuits (5)

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, auto, left),
    table.header([*Circuit*], [*Degree*], [*Proves*]),
    [IVC Compression], [7], [Receipt chain valid from genesis (constant-size)],
    [STARK-in-Kimchi], [7], [BabyBear STARK verified inside Pasta circuit],
    [Plonky3 Recursive], [7], [Inner proof verified by outer proof],
    [SP1 Guest (STARK Verifier)], [N/A (RISC-V)], [STARK valid (for Groth16 extraction)],
    [Checkpoint Proof], [7], [Group state at height $H$ is commitment $C$],
  ),
  caption: [Bridge and recursion circuits. Enable cross-system proof translation.],
)

== Cryptographic Guarantees

The system provides 11 cryptographic guarantees, each derivable from the circuit catalog:

+ *Authorization soundness*: No cell can exercise a capability it was not delegated (Fold + Derivation + Body Membership).
+ *Attenuation monotonicity*: Delegation can only narrow scope (Fold constraint: $F_(i+1) subset.eq F_i$).
+ *Conservation*: No value created or destroyed in a turn (Conservation circuit).
+ *State continuity*: Post-state is deterministically derived from pre-state + effects (State Continuity).
+ *Nullifier uniqueness*: No note spent twice (Note Spending + federation nullifier set).
+ *Issuer anonymity*: Verifier cannot determine which group member issued a credential (Blinded Issuer Ring).
+ *Presentation unlinkability*: Multiple presentations of the same credential are uncorrelatable (Presentation Randomization).
+ *Routing integrity*: Messages are classified according to the committed DFA (DFA Classification).
+ *Fee validity*: Every turn pays at least the base fee (Fee Sufficiency).
+ *Stake privacy*: Validator stake amount is hidden; only threshold satisfaction is proven (Stake Threshold + Range Proof).
+ *IVC correctness*: Any receipt chain can be verified from genesis in constant time (IVC Compression).

== Trust Boundary

The system explicitly identifies 7 trust assumptions---points where cryptographic proofs are insufficient and operational trust is required:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Assumption*], [*Boundary*], [*Mitigation*]),
    [Federation honest majority], [$f < n\/3$ Byzantine], [Equivocation detection + slashing],
    [Executor state correctness], [Executor faithfully maintains state], [Challenge protocol + bonding],
    [Swiss table integrity], [Federation maintains swiss table], [Replication across nodes],
    [Relay availability], [Relays deliver messages (may delay)], [Multiple relays + TTL],
    [Clock synchrony], [Bounded clock drift for TTL], [NTP + generous bounds],
    [RNG quality], [Random number generators produce entropy], [Hardware RNG + mixing],
    [Cryptographic hardness], [Poseidon2, Ed25519, BLS12-381, FRI], [Conservative parameters + agility],
  ),
  caption: [Explicit trust assumptions. Each is documented, bounded, and mitigated.],
)

The key principle: every trust assumption is _explicit_ and _bounded_. No assumption says "the system is secure"---each says "IF this specific property holds (with this specific mitigation), THEN this specific guarantee follows."

== Verification Methodology

=== Compile-Time Checks

The typed composition checker runs at Rust compile time (via proc macros):

- All `compose_chain` calls are type-checked for input/output compatibility.
- All `compose_and` calls verify no conflicting assumptions.
- Circuit degree bounds are verified against FRI parameters.
- Public input schemas are checked against proof generation code.

=== Test-Time Verification

The test suite (4,046 tests) includes:

- *Soundness tests*: For each circuit, verify that invalid witnesses produce failing proofs (adversarial testing).
- *Composition tests*: For each composition operator, verify that composed proofs are valid iff both components are valid.
- *Property tests*: Proptest-generated random inputs verify conservation, monotonicity, and nullifier properties across 10,000+ random cases.
- *Regression tests*: Every security audit finding has a regression test that would catch reintroduction.

=== Path to Full Formal Verification

The remaining path beyond compile-time and test-time:

+ Extract the executor's critical path (turn validation, conservation, nullifier dedup) into verified Rust (Verus or Prusti).
+ Model the full system in Lean 4: cells, turns, proofs, federation, composition.
+ Prove that the 11 cryptographic guarantees compose correctly under concurrent execution.
+ Verify that DFA routing correctly enforces governance rules under all membership transitions.
+ Machine-check the STARK soundness argument (FRI proximity + AIR degree bound + challenge sampling).
