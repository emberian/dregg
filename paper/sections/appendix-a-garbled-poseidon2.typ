// =============================================================================
// Poseidon2 as Garbling Function for STARK-Provable Garbled Circuits
// =============================================================================

= Poseidon2 as Garbling Function for STARK-Provable Garbled Circuits

== Motivation

Standard garbled circuit constructions instantiate the garbling PRF with AES or SHA-256---primitives optimized for hardware execution but catastrophically expensive inside arithmetic STARKs. We observe that Poseidon2 @poseidon2, a permutation designed for efficient arithmetization over prime fields, can serve as the garbling function in a Yao-style garbled circuit @yao86 while remaining _natively provable_ in a BabyBear STARK. This yields verifiable garbled circuits @jawurek13 with three orders of magnitude fewer constraints per gate than AES-based alternatives.

== The Construction

=== Notation

Let $FF_p$ denote the BabyBear field ($p = 2^(31) - 2^(27) + 1$). A _label_ is a vector $bold(l) in FF_p^8$ (8 field elements, providing 248 bits of entropy). For a wire $w$ carrying a Boolean value $b in {0,1}$, we write $bold(l)_w^b$ for the label encoding value $b$ on wire $w$. The function $"P2": FF_p^(16) -> FF_p^8$ denotes the first 8 output elements of a width-16 Poseidon2 permutation with $alpha = 7$ and 21 rounds (8 external + 13 internal).

=== Gate Garbling

For a gate $g$ with left input wire $a$, right input wire $b$, output wire $c$, and Boolean function $f_g: {0,1}^2 -> {0,1}$, the garbled table consists of four ciphertexts:

$ bold(C)_g^(i,j) = "P2"(bold(l)_a^i || bold(l)_b^j || bold(e)_g) xor bold(l)_c^(f_g (i,j)) quad forall (i,j) in {0,1}^2 $

where $bold(e)_g in FF_p^8$ is a _gate encoding_ vector: the gate index $g$ placed in the first element with the remaining elements set to zero (preventing cross-gate correlation of PRF outputs), and $||$ denotes concatenation forming the 16-element input to P2.

The XOR operation ($xor$) is defined component-wise over the unsigned 32-bit integer representation of each field element---that is, interpreting each $x in FF_p$ as an element of $ZZ_(2^(32))$ via canonical reduction, XORing the bit patterns, and retaining the result as an element of $ZZ_(2^(32))$ (which may exceed $p$). We emphasize: this is _not_ field subtraction.

=== Point-and-Permute

The garbled table rows are permuted using the least significant bit of the first element of each input label. Define $pi(bold(l)) = bold(l)[0] mod 2$. The evaluator uses $(pi(bold(l)_a), pi(bold(l)_b))$ as a 2-bit index to select the correct row, reducing evaluation from four trial decryptions to one.

Label generation enforces that for each wire $w$, $pi(bold(l)_w^0) != pi(bold(l)_w^1)$: the garbler samples $bold(l)_w^0$ uniformly, then sets $bold(l)_w^1[0] = bold(l)_w^0[0] xor 1$ (flipping the LSB) with remaining elements sampled independently.

=== Circuit Garbling

Given a Boolean circuit $C$ with $n$ gates and input/output wires:

+ *Label generation:* For each wire $w$, sample $bold(l)_w^0 arrow.l.long FF_p^8$ uniformly; derive $bold(l)_w^1$ per the point-and-permute constraint above.
+ *Table construction:* For each gate $g$, compute the four ciphertexts $bold(C)_g^(i,j)$ and permute rows by $(pi(bold(l)_a^i), pi(bold(l)_b^j))$.
+ *Circuit commitment:* $h_C = "Poseidon2"("Poseidon2"(bold(C)_1) || ... || "Poseidon2"(bold(C)_n))$, a Merkle-style hash binding the garbled tables.
+ *Output commitment:* For each output wire $w_"out"$, publish $h_"out"^b = "Poseidon2"(bold(l)_(w_"out")^b)$ for both $b in {0,1}$.

== Security Argument

=== Garbling Privacy

We argue security in the simulation-based framework of Bellare, Hoang, and Rogaway @bhr12.

#quote(block: true)[
*Theorem (informal).* If Poseidon2 (width-16, $alpha = 7$, 21 rounds over $FF_p$) is a pseudorandom function when keyed by a uniformly random 16-element input, then the construction above satisfies garbling privacy (prv.sim security) with computational security $lambda >= 124$ bits.
]

*Proof sketch.* The simulator, given only the topology and the output labels corresponding to the true output, must produce garbled tables indistinguishable from real ones. Under the PRF assumption on P2:

+ For each gate $g$ and each input pair $(i,j)$ not on the evaluation path, the ciphertext $bold(C)_g^(i,j) = "P2"("key"_(i,j,g)) xor bold(l)_c^(f_g(i,j))$ is indistinguishable from uniform, since $"P2"("key"_(i,j,g))$ is pseudorandom and XOR with a fixed value preserves pseudorandomness.

+ For the single row $(i^*, j^*)$ on the evaluation path, the evaluator recovers $bold(l)_c^(f_g(i^*,j^*))$ but learns nothing about $bold(l)_c^(1 - f_g(i^*,j^*))$ since the other rows remain pseudorandom.

+ The gate encoding $bold(e)_g$ ensures domain separation: even if two gates receive identical input labels, distinct gate indices produce independent PRF outputs under standard multi-key PRF security.

The 248-bit label space provides a birthday bound of $2^(124)$, meaning an adversary must evaluate P2 on the order of $2^(124)$ distinct inputs before observing a collision that could distinguish real garbled tables from simulated ones.

=== XOR Correctness and Security

The choice of bitwise XOR (over $ZZ_(2^(32))$) rather than field subtraction (over $FF_p$) is security-critical.

*Correctness.* Evaluation recovers the output label:

$ bold(C)_g^(i,j) xor "P2"(bold(l)_a^i || bold(l)_b^j || bold(e)_g) = bold(l)_c^(f_g(i,j)) $

by definition of XOR's self-inverse property.

*Security.* Under the PRF assumption, $"P2"(bold(l)_a^i || bold(l)_b^j || bold(e)_g)$ is computationally indistinguishable from a uniform element of ${0, ..., 2^(32)-1}^8$. Bitwise XOR of a uniform mask with any fixed value produces a uniform distribution (one-time pad). Thus each ciphertext individually reveals no information about $bold(l)_c^(f_g(i,j))$.

Had we used field subtraction, the algebraic structure of $FF_p$ would be preserved: an adversary could exploit the fact that $a - b + b = a$ in the field to construct linear relations between ciphertexts across gates sharing wires. Bitwise XOR destroys this algebraic structure---it is not a group operation over $FF_p$ and admits no useful homomorphic properties.

=== STARK Proof Composition

The STARK proves the following compound statement:

#quote(block: true)[
"I know labels $bold(l)_1, ..., bold(l)_m$ and a circuit evaluation path such that:
1. For each gate $g$ on the path, $"P2"(bold(l)_(a_g) || bold(l)_(b_g) || bold(e)_g) xor bold(l)_(c_g) = bold(C)_g^(pi(bold(l)_(a_g)), pi(bold(l)_(b_g)))$
2. The output label $bold(l)_"out"$ satisfies $"Poseidon2"(bold(l)_"out") = h_"out"^1$ (the committed 'true' hash)"
]

*Public inputs:* Circuit commitment $h_C$, output label hash $h_"out"^1$.

*Private witness:* All wire labels on the evaluation path, the garbled table entries accessed, the Poseidon2 intermediate states.

*Zero-knowledge property:* The verifier learns only that the evaluator possesses labels consistent with an output of 1. The garbled tables are entirely within the private witness---the verifier sees only $h_C$ (binding the proof to a specific circuit) and $h_"out"^1$ (binding to the expected "true" output). The delegation chain, input values, and intermediate wire labels remain hidden.

=== Verifiable Evaluation: What the STARK Adds

In standard Yao garbled circuits, the garbler must trust that the evaluator reports the output honestly (or reveal a decoding table). The STARK proof eliminates this trust assumption:

- *Completeness:* An honest evaluator with valid input labels can always produce a valid proof.
- *Soundness:* A cheating evaluator cannot produce a valid proof for output 1 unless they actually possess labels that evaluate to 1.
- *Zero-knowledge:* The proof reveals nothing beyond the single output bit.

This achieves the same goal as the verifiable garbled circuits of Jawurek, Kerschbaum, and Orlandi @jawurek13, but replaces their cut-and-choose mechanism with a STARK. The STARK approach is _non-interactive_ (no multi-round protocol), _publicly verifiable_ (any third party can check the proof), and _succinct_ (~24 KiB regardless of circuit size).

== Why Poseidon2 (Not AES, Not SHA-256)

The choice of garbling PRF is dictated by the constraint cost inside a BabyBear STARK.

=== AES-128

Each AES S-box computes inversion in $"GF"(2^8)$. Expressing this as a degree-254 polynomial over $FF_p$ requires approximately 1,000 multiplication constraints per S-box. With 160 S-boxes across 10 rounds:

$ "Constraints per AES call" approx 160 times 1000 = 100,000 $

For a single gate evaluation (one AES call as PRF): ~100,000 constraints.

=== SHA-256

SHA-256 uses 32-bit AND, XOR, and ROTATE operations. In a prime-field STARK, each bit operation requires bit decomposition (31 binary constraints) plus reconstruction. The compression function performs ~1,100 such operations:

$ "Constraints per SHA-256 call" approx 1,100 times 23 approx 25,000 $

(using optimized gadgets that amortize decomposition across related operations).

=== Poseidon2 (Width-16, BabyBear)

Poseidon2 over $FF_p$ is _native_ to the STARK: each round consists of field multiplications and additions that are single constraints. With 21 rounds and width 16:

$ "Constraints per Poseidon2 call" approx 21 times 8 = 168 $

(8 degree-7 S-box constraints per round, with the MDS matrix application being linear and thus "free" in the AIR).

=== Cost Comparison

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, right, right, right),
    table.header([*Garbling PRF*], [*Constraints/gate*], [*62-gate circuit*], [*Est. proving time*]),
    [AES-128], [$tilde$100,000], [$tilde$6,200,000], [$tilde$60 s],
    [SHA-256], [$tilde$25,000], [$tilde$1,550,000], [$tilde$15 s],
    [Poseidon2 (ours)], [$tilde$170], [$tilde$10,500], [$tilde$50 ms],
  ),
  caption: [Constraint cost per garbled gate evaluation inside a BabyBear STARK. The 62-gate column corresponds to a 31-bit integer comparison circuit. Proving times estimated on a single core at $tilde$200K constraints/second.],
)

The 600x reduction from Poseidon2 vs. AES makes the difference between "impractical" and "real-time on commodity hardware."

== Concrete Parameters

For a 31-bit BabyBear integer comparison (the motivating application: proving a private value exceeds a threshold without revealing either):

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Parameter*], [*Value*]),
    [Label entropy], [8 $times$ BabyBear = 248 bits (124-bit security)],
    [Circuit topology], [62 AND gates + free XOR (half-gates)],
    [Garbled table size], [62 gates $times$ 4 rows $times$ 32 bytes = 7,936 bytes],
    [STARK trace dimensions], [62 rows $times$ $tilde$40 columns (Poseidon2 state + I/O)],
    [STARK proof size], [$tilde$24 KiB (FRI over BabyBear4)],
    [Proving time], [$tilde$50--100 ms (single core)],
    [Verification time], [$tilde$2 ms],
    [Total protocol payload], [$tilde$32 KiB (circuit + proof + OT messages)],
  ),
  caption: [Concrete parameters for a 31-bit comparison garbled circuit with STARK verification.],
)

== Limitations and Assumptions

=== One-Time Evaluation

Each garbled circuit supports exactly one evaluation (standard Yao limitation). The labels for a given wire encode a single Boolean value; reuse would allow the evaluator to learn both labels and decrypt all four rows. For repeated comparisons against the same threshold, fresh circuits must be garbled.

=== Evaluator Learns Output

The evaluator (prover) necessarily learns the comparison result. This is inherent to garbled circuit evaluation---the evaluator decrypts output labels and can identify which corresponds to "true" vs. "false." Only the _threshold_ (garbled into the circuit by the garbler) remains hidden from the evaluator. The STARK proof conveys this result to third parties without revealing anything else.

=== Semi-Honest Security

The basic construction provides security against semi-honest adversaries (both parties follow the protocol but may attempt to extract additional information from their view). For malicious security---where the garbler might construct an incorrect circuit---standard techniques apply:

- *Cut-and-choose:* Generate $kappa$ garbled circuits, open $kappa/2$ for verification, evaluate the remainder. Overhead: $2$--$3 times$ in computation, $kappa times$ in communication.
- *Dual execution:* Both parties garble and evaluate; compare outputs via equality test. Overhead: $2 times$ in computation with only 1-bit leakage to a malicious adversary.

These extensions compose naturally with STARK verification (the STARK proves correct evaluation of whichever circuit was selected in cut-and-choose).

=== PRF Assumption on Poseidon2

Poseidon2 @poseidon2 is a relatively recent construction (2023). While the permutation has been analyzed for collision resistance, preimage resistance, and algebraic attacks (Grobner basis, interpolation, differential/linear), it has not undergone the decades of cryptanalytic scrutiny applied to AES. The concrete security bounds from @poseidon2 give:

- Algebraic attack complexity: $> 2^(128)$ for the 21-round parameterization
- Statistical attack complexity: $> 2^(128)$ (wide trail strategy)

We consider this adequate for the application (private threshold comparisons with economic, not nation-state, adversaries) but note that a future break of Poseidon2's PRF security would invalidate garbling privacy.

== Relation to Prior Work

*Yao @yao86* introduced garbled circuits as the foundational technique for secure two-party computation. Our construction follows the standard Yao framework, differing only in the choice of garbling PRF.

*Bellare, Hoang, and Rogaway @bhr12* formalized garbling scheme security via simulation-based definitions (prv.sim, prv.ind, obv.sim). Our security argument targets prv.sim: the garbled circuit together with the output labels can be simulated given only the circuit topology and the output.

*Jawurek, Kerschbaum, and Orlandi @jawurek13* introduced verifiable garbled circuits, where the evaluator proves correct evaluation via zero-knowledge proofs. Their construction uses Sigma protocols and cut-and-choose. We replace this with a STARK, gaining non-interactivity, public verifiability, and succinctness.

*Grassi et al. @poseidon2* designed Poseidon2 as an arithmetization-friendly hash for use inside SNARKs/STARKs. We extend its application from commitment/hashing to garbling---using it as a PRF for encryption rather than merely for Merkle trees.

*CAPSS @capss24* constructs digital signatures from arithmetization-oriented permutations inside proof systems. This is the closest prior work in spirit: both use AO primitives for cryptographic functionality (signatures there, garbling here) inside arithmetic circuits.

*Free XOR and Half-Gates* (Kolesnikov and Schneider 2008; Zahur, Rosulek, and Evans 2015) reduce garbled circuit size by encoding XOR gates without ciphertexts. These optimizations are orthogonal to our PRF choice and apply directly: XOR gates require no Poseidon2 evaluations, and half-gates reduce AND gate cost by 50%.

== Security Definitions

For completeness, we state the formal security property.

*Definition (prv.sim, adapted from @bhr12).* A garbling scheme $cal(G) = ("Garble", "Eval", "Decode")$ satisfies prv.sim if there exists a PPT simulator $cal(S)$ such that for all PPT distinguishers $cal(D)$, circuits $C$, and inputs $x$:

$ |Pr[cal(D)("Garble"(C, x)) = 1] - Pr[cal(D)(cal(S)(C, C(x))) = 1]| <= "negl"(lambda) $

where $"Garble"(C, x)$ outputs the garbled circuit $tilde(C)$ and input labels $tilde(x)$, and $cal(S)(C, C(x))$ receives only the circuit topology and the output value.

*Claim.* Under the assumption that $"P2": FF_p^(16) -> FF_p^8$ (first 8 outputs of width-16 Poseidon2) is a $(t, epsilon)$-secure PRF for $t = 2^(124)$ and $epsilon = 2^(-124)$, our construction satisfies prv.sim with $lambda = 124$.

The reduction is standard: the simulator constructs fake garbled tables by replacing all non-output labels with fresh random values and computing ciphertexts as $"P2"("random input") xor "random label"$. Distinguishing real from simulated requires distinguishing P2 outputs from random, contradicting the PRF assumption.
