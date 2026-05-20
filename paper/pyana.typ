// =============================================================================
// Pyana: Zero-Knowledge Object-Capability Authorization
// with Backend-Agnostic Commitment
// =============================================================================

#set document(
  title: "Pyana: Zero-Knowledge Object-Capability Authorization with Backend-Agnostic Commitment",
  author: ("Ember Arlynx"),
  date: datetime(year: 2026, month: 5, day: 20),
)

#set page(
  paper: "us-letter",
  margin: (x: 1.2in, y: 1.2in),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 9pt, fill: luma(100))
      Pyana: ZK Object-Capability Authorization
      #h(1fr)
      Draft -- May 2026
    ]
  },
)

#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.58em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#show heading.where(level: 1): it => {
  v(1.2em)
  text(size: 14pt, weight: "bold", it)
  v(0.6em)
}
#show heading.where(level: 2): it => {
  v(0.8em)
  text(size: 12pt, weight: "bold", it)
  v(0.4em)
}
#show raw.where(block: true): set text(size: 9pt)
#show raw.where(block: true): block.with(
  fill: luma(245),
  inset: 8pt,
  radius: 3pt,
  width: 100%,
)

// ─── Title ───────────────────────────────────────────────────────────────────

#align(center)[
  #text(size: 18pt, weight: "bold")[
    Pyana: Zero-Knowledge Object-Capability Authorization \
    with Backend-Agnostic Commitment
  ]
  #v(1em)
  #text(size: 11pt)[Ember Arlynx]
  #v(0.3em)
  #text(size: 10pt, fill: luma(80))[
    Draft -- May 20, 2026 \
    `github.com/pyana-dev/breadstuffs`
  ]
]

#v(2em)

// ─── Abstract ────────────────────────────────────────────────────────────────

#heading(level: 1, numbering: none)[Abstract]

We present Pyana, a distributed object-capability authorization system in which an agent proves possession of a valid, attenuated capability chain in zero knowledge. The core observation is that monotonic capability attenuation---restricting a bearer token's scope through successive delegation---forms an incrementally verifiable computation: each restriction step is a fold over a committed fact set, producing a strictly smaller successor state. We encode capabilities as Datalog fact sets, commit them to 4-ary Merkle trees using algebraic hashes (Poseidon2 over BabyBear), and prove correct evaluation of Datalog authorization rules inside a STARK. The verifier learns a single bit---authorized or not---without observing the delegation chain, intermediate authorities, or the agent's other capabilities.

Pyana supports multiple proof backends (BabyBear STARK, Binius, Halo2, Nova, Kimchi) that prove the same logical statement against the same data model, unified by a multi-root federation commitment. A federated BFT layer (Morpheus adaptive consensus with BLS12-381 threshold signatures) provides attested state roots for offline verification. Bounded counters adapted from Stingray enable concurrent resource spending across silos without per-operation consensus. The external verification interface is entirely hash-based and post-quantum secure; classical signatures are confined within federation trust boundaries.

The system is implemented in approximately 45k lines of Rust across 16 crates, with real STARK proof generation ($tilde$24 KiB proofs, sub-second generation), real Ed25519/BLS12-381 cryptography, and a working multi-node TCP demonstration.

#v(1em)

// ─── 1. Introduction ─────────────────────────────────────────────────────────

= Introduction

Cross-domain authorization for autonomous agents presents a challenge that existing systems address incompletely. Consider an AI agent dispatched by Organization A to invoke a service hosted by Organization B. The agent must prove it is authorized---but without revealing Organization A's internal delegation structure, the identities of intermediate signatories, or what other capabilities the agent holds.

Existing approaches each fail along a different axis:

- *UCAN/ZCAP-LD* @ucan provide delegation chains but require revealing the full chain to the verifier. Privacy is absent.
- *Coconut credentials* @coconut offer selective disclosure of attributes but lack the delegation semantics needed for capability attenuation.
- *Blockchain-based authorization* (smart contract ACLs) achieves transparency but requires chain liveness, incurs gas costs, and exposes all authorization state on-chain.
- *Mina Protocol's* @mina succinct state proofs compress an entire blockchain into a constant-size proof, but target financial state transitions rather than authorization semantics.

Pyana's contribution is proving monotonic attenuation of a bearer token chain in zero knowledge, with backend-agnostic commitment. The system achieves:

+ *Zero-knowledge presentation*: The verifier learns only that the presenter is authorized for the requested action. Nothing about the delegation chain, intermediate authorities, or other capabilities leaks.
+ *Offline verification*: No chain liveness or callback is required. Verification needs only the proof and the federation's attested root.
+ *Post-quantum security at the trust boundary*: The external interface (STARKs, Merkle commitments, HMAC chains) is entirely hash-based.
+ *Backend agility*: The same authorization semantics can be proved with different proof systems, selected per deployment context.
+ *Blockchain-grade adversarial soundness*: The system targets environments where the prover is actively malicious.

The design draws directly from Mina Protocol's execution model---one of this paper's authors was a founding architect of Mina---recontextualizing zkApp accounts, call forests, and precondition-gated state transitions for authorization rather than financial ledgers.

// ─── 2. System Model ─────────────────────────────────────────────────────────

= System Model

== Cells

A _cell_ is the fundamental unit of isolated state, analogous to a Mina zkApp account. Each cell holds:

- A content-addressed identity $"CellId" in {0,1}^(256)$.
- Mutable state: 8 generic field slots $s_0, ..., s_7 in FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear prime).
- A _capability set_ (c-list): the set of capabilities the cell may exercise.
- Permission requirements specifying what authorization kind (None, Signature, Proof, Either) is needed for each action type (Send, Receive, SetState, SetPermissions, SetVerificationKey).
- An optional verification key for ZK proof validation.

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant (you cannot delegate what you do not hold).

== Turns

A _turn_ is an atomic transaction over one or more cells, analogous to a Mina ZkappCommand. A turn contains:

- A _call forest_: a tree of actions, executed depth-first.
- A fee (in computrons) covering execution cost.
- A nonce (monotonically increasing per cell) for replay protection.
- Authorization: Ed25519 signature, ZK proof, or both.

If any action in the call forest fails (precondition violation, insufficient authorization, budget exhaustion), all effects are rolled back via journal replay. This provides atomicity.

== Silos

A _silo_ is a node that holds cells, executes turns, and participates in federation consensus. Silos maintain:

- A cell ledger (the set of cells they are responsible for).
- A _bounded counter slice_ for each agent's resource budget.
- A connection to the federation gossip network.

== Federations

A _federation_ is a committee of 3--64 silos that share a trust root. Federation members run BFT consensus (Morpheus @morpheus) to agree on:

- Attested Merkle roots (published periodically as freshness anchors).
- Revocation tree updates.
- Budget rebalancing epochs.

The honest-majority assumption is standard BFT: tolerate $< n\/3$ Byzantine members.

== Trust Assumptions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, center),
    table.header([*Layer*], [*Assumption*], [*PQ?*]),
    [External proofs (STARKs)], [Collision-resistant hash], [Yes],
    [Merkle commitments], [Collision-resistant hash], [Yes],
    [Macaroon HMAC chain], [PRF security of HMAC-SHA256], [Yes],
    [Federation QCs (BLS12-381)], [Bilinear DH in $GG_1 times GG_2$], [No],
    [Node identity (Ed25519)], [DLP in twisted Edwards], [No],
    [Sealed secrets (X25519)], [CDH in Curve25519], [No],
  ),
  caption: [Trust assumptions by layer. Items marked "No" are confined within federation trust boundaries.],
)

The critical invariant: *everything that crosses a trust boundary is post-quantum secure*. Classical cryptography exists only between parties that already trust each other (federation members).

// ─── 3. Authorization Semantics ──────────────────────────────────────────────

= Authorization Semantics

== Capabilities as Datalog Facts

Authorization state is encoded as a set of Datalog facts. A fact is a ground atom:

$ "fact" := "predicate"("term"_1, ..., "term"_k) $

For example, a token granting read access to the DNS service is encoded as:

```
service("dns", "read")
```

A token granting multiple actions to an application:

```
action_allowed("dashboard", H("read"))
action_allowed("dashboard", H("write"))
```

where $H$ denotes a collision-resistant hash used for exact-match semantics (eliminating substring vulnerabilities in action matching).

== Attenuation as Monotonic Restriction

Attenuation transforms a fact set $F$ into $F' subset.eq F$ by removing facts. The restriction types include:

- *Service/app scoping*: Remove facts for services the delegate should not access.
- *Action restriction*: Remove action facts, narrowing permitted operations.
- *Time bounding*: Add a `valid_until(t)` fact that gates evaluation.
- *Budget enrollment*: Add `budget_remaining(id, amount)` facts subject to counter enforcement.
- *Revocability*: Add `revocable(token_id)` enabling later revocation.
- *User confinement*: Add facts restricting the token to a specific identity.

The HMAC chain in a macaroon token makes removal of caveats cryptographically impossible---each caveat is chained into the authentication tag. Attenuation is irreversible.

== The Caveat-to-Fact-to-Evaluation Pipeline

#figure(
  ```
  Macaroon caveat (wire format)
       |
       | parse + validate
       v
  Datalog fact set F (logical representation)
       |
       | inject request facts: request_app(A), request_action(X), ...
       v
  Evaluator: bottom-up Datalog to fixpoint
       |
       | check: allow(...) derived AND deny() NOT derived
       v
  Conclusion: Allow { rule_id } | Deny
  ```,
  caption: [The evaluation pipeline from token to authorization decision.],
)

== Datalog Rules

The standard policy consists of rules that derive `allow` or `deny` from the conjunction of token facts and request facts. The core rules (simplified):

$ "allow" &:- "app"(A, "Actions"), "request_app"(A), "request_action"("Act"), "Act" in "Actions" $
$ "allow" &:- "service"(S, "Actions"), "request_service"(S), "request_action"("Act"), "Act" in "Actions" $
$ "allow" &:- "unrestricted"(1), "request_action"("Act") $
$ "deny" &:- "budget_remaining"(B, R), "request_cost"(C), C > R $
$ "deny" &:- "revocable"(T), "revoked"(T) $

Evaluation is bottom-up (forward-chaining) to a fixpoint. The evaluator records every derivation step---which rule fired, which facts matched, what substitution was applied---producing a _derivation trace_. This trace is the witness for the ZK circuit.

== Dual-Mode Evaluation

The same Datalog rules yield the same answer in two modes:

- *Trusted mode* (local evaluation): The silo runs the Datalog evaluator directly. Cost: $tilde 8 mu s$. Used when prover and verifier share a trust boundary.
- *Trustless mode* (STARK proof): The prover generates a STARK proof that the Datalog evaluation produced `allow`. The verifier checks the proof without seeing the fact set. Cost: $tilde 64 mu s$ prove, $tilde 438 mu s$ verify. Used across trust boundaries.

Both modes evaluate identical rules over identical data. The proof attests to the computation, not to a separate protocol.

// ─── 4. Commitment Scheme ────────────────────────────────────────────────────

= Commitment Scheme

== FactSet Encoding

A fact set $F = {f_1, ..., f_n}$ is encoded as a sequence of field elements via a symbol table. Each predicate and constant term is interned to a 32-bit symbol ID. The encoding of a fact is:

$ "encode"(f) = ("predicate_id" || "term"_1 || ... || "term"_k) $

padded to a fixed width. The encoded facts are then committed in a Merkle tree.

== 4-ary Merkle Trees

Pyana uses 4-ary (quaternary) Merkle trees rather than binary. Each internal node hashes 4 children:

$ H_"node" = "Poseidon2"(c_0, c_1, c_2, c_3) $

where $"Poseidon2"$ is instantiated with width 8 over BabyBear (state width 8, $alpha = 7$, 8 external rounds, 22 internal rounds). The 4-ary structure reduces tree height by half relative to binary trees, halving the number of hash invocations in a membership proof.

Two hash functions are used depending on context:

- *BLAKE3* (fast path): For local commitment operations where ZK provability is not required. 256-bit output, hardware-accelerated.
- *Poseidon2* (ZK path): For commitments that will be verified inside a STARK circuit. Native BabyBear arithmetic, no expensive bit-decomposition.

*Known limitation*: These two Merkle systems are not yet unified. The BLAKE3 commitment layer cannot currently produce proofs verifiable inside the STARK circuit. Unification (Poseidon2 end-to-end for the provable path) is the highest-priority engineering task.

== Multi-Hash Roots

The federation publishes roots under multiple commitment schemes simultaneously:

$ R_"STARK" &= "Poseidon2Root"(F) \
  R_"Binius" &= "Groestl256Root"(F) \
  R_"Halo2" &= "PoseidonBN254Root"(F) \
  R_"Nova" &= "PoseidonPastaRoot"(F) $

Each proof backend references the root in its native field. A single attested state can be verified by any backend without cross-field translation.

== Fold Deltas

A _fold delta_ records a monotonic state transition:

$ Delta_(i -> i+1) = { f in F_i | f in.not F_(i+1) } $

The delta contains only removals (capabilities that were attenuated away). The commitment to $F_(i+1)$ can be computed from $F_i$ and $Delta$ without re-committing the entire tree. This is the incremental structure that enables IVC.

// ─── 5. Zero-Knowledge Presentation ─────────────────────────────────────────

= Zero-Knowledge Presentation

== The Fold AIR

The core of the proof system is an Algebraic Intermediate Representation (AIR) that constrains the fold computation. The STARK proves:

#quote(block: true)[
  "There exists a sequence of fact sets $F_0 supset.eq F_1 supset.eq ... supset.eq F_k$ such that $F_0$ is committed under a federation-attested root, each $F_(i+1) = F_i backslash Delta_i$ for valid removal sets $Delta_i$, and evaluating the standard policy rules over $F_k$ with the given request yields `allow`."
]

The AIR has three constraint families:

+ *Membership constraints*: Each fact referenced in the derivation trace is a valid leaf of the committed Merkle tree.
+ *Fold constraints*: Each removal in $Delta_i$ was present in $F_i$ and absent in $F_(i+1)$. The new root is correctly computed.
+ *Derivation constraints*: The Datalog evaluation steps are valid---each rule's body atoms unify against facts in $F_k$ under the claimed substitution, and all checks pass.

== Public Inputs

The verifier receives exactly:

- The federation root hash $R$ (attesting to the issuer's membership).
- The authorization request $(A, S, "Act")$ (app, service, action).
- The current time $t$ (for freshness).
- The STARK proof $pi$ ($tilde$24 KiB).

From these, the verifier checks $pi$ against $R$ and the request. The output is a single bit.

== What the Verifier Learns

The verifier learns:

+ The presenter holds a valid capability chain rooted at an issuer in the federation.
+ The chain, after all attenuations, authorizes the specific requested action.
+ The token is not expired (if time-bounded).
+ The token is not revoked (via non-membership proof against the revocation tree).

The verifier does *not* learn:

- The delegation chain length or structure.
- The identities of intermediate delegators.
- What other capabilities the agent holds.
- The original token's full scope.
- The issuer's identity (only that _some_ issuer in the federation issued it).

== Proof Generation (Pseudocode)

```rust
fn prove_presentation(
    token_chain: &[FactSet],     // F_0, F_1, ..., F_k
    deltas: &[FoldDelta],         // removals at each step
    request: &AuthRequest,
    federation_root: &[u8; 32],
) -> StarkProof {
    // 1. Evaluate Datalog over F_k to produce derivation trace
    let trace = evaluator.evaluate(token_chain.last(), request);
    assert!(trace.conclusion == Allow);

    // 2. Build fold witness: Merkle membership for each removed fact
    let fold_witness = deltas.iter()
        .map(|d| d.membership_proofs())
        .collect();

    // 3. Build derivation witness: fact indices + substitutions
    let deriv_witness = trace.steps.iter()
        .map(|step| (step.body_fact_indices, step.substitution))
        .collect();

    // 4. Build issuer membership witness: F_0's root in federation tree
    let issuer_witness = federation_tree
        .prove_membership(token_chain[0].root());

    // 5. Generate STARK proof over combined AIR
    stark::prove(&fold_witness, &deriv_witness, &issuer_witness)
}
```

== Verification

```rust
fn verify_presentation(
    proof: &StarkProof,
    federation_root: &[u8; 32],
    request: &AuthRequest,
) -> bool {
    let public_inputs = encode_public_inputs(federation_root, request);
    stark::verify(proof, &public_inputs)
}
```

Verification is fail-closed: any malformed proof, incorrect public inputs, or FRI check failure produces `Err`. There is no soft-fail mode.

// ─── 6. Proof Backend Agility ────────────────────────────────────────────────

= Proof Backend Agility

== The ProofBackend Trait

Different deployment contexts demand different proof system tradeoffs. Pyana abstracts the proof system behind a unified trait:

```rust
pub trait ProofBackend: Send + Sync {
    type Proof: Serialize + Deserialize;

    fn prove_membership(
        leaf: &[u8; 32],
        siblings: &[Vec<[u8; 32]>],
        root: &[u8; 32],
    ) -> Result<Self::Proof, String>;

    fn verify_membership(
        proof: &Self::Proof, root: &[u8; 32]
    ) -> Result<bool, String>;

    fn prove_fold_step(
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        removals: &[[u8; 32]],
    ) -> Result<Self::Proof, String>;

    fn verify_fold(proof: &Self::Proof) -> Result<bool, String>;

    fn proof_size(proof: &Self::Proof) -> usize;
    fn backend_name() -> &'static str;
}
```

== Available Backends

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, left, center, center, center),
    table.header([*Backend*], [*Field/Curve*], [*Proof Size*], [*PQ?*], [*Recursion*]),
    [BabyBear STARK], [$FF_(2^(31)-2^(27)+1)$ + FRI], [$tilde$24 KiB], [Yes], [Planned],
    [Binius], [GF(2) tower + Groestl-256], [$tilde$1--4 KiB], [Yes], [No],
    [Halo2], [BN254 / Pasta + KZG], [$tilde$1--5 KiB], [No], [Yes],
    [Nova], [Pasta cycle (Pallas/Vesta)], [$tilde$10 KiB], [No], [IVC native],
    [Kimchi], [Pasta cycle + IPA], [$tilde$1--2 KiB], [No], [Yes (Pickles)],
  ),
  caption: [Proof backend characteristics. PQ = post-quantum secure.],
)

== Why Multiple Backends Compose

The backends prove the *same logical statement* about the *same data model*. What differs is:

+ The commitment scheme (hash function native to each field).
+ The arithmetization (AIR for STARK, Plonkish for Halo2/Kimchi, R1CS for Nova, binary tower for Binius).
+ The proof size and verification cost.

The multi-root approach (@sec-multi-root) ensures that every backend can reference a root attested by the same federation. A verifier that supports backend $B$ can check any proof generated by backend $B$, regardless of which other backends exist.

== Nova for EVM Settlement <sec-nova-evm>

Nova @nova provides native IVC: each fold step accumulates into a _running instance_ of constant size. After $k$ folds, the prover produces a single relaxed R1CS instance---no matter how long the attenuation chain. For on-chain verification, this Nova proof is compressed to Groth16 via a final "decider" step, yielding a proof verifiable in $tilde$200k gas on EVM chains (Base, Ethereum L1).

// ─── 7. Federation Consensus ─────────────────────────────────────────────────

= Federation Consensus

== Morpheus Adaptive BFT

Federation consensus uses Morpheus @morpheus, an adaptive BFT protocol that tolerates up to $f$ Byzantine nodes in a $3f+1$ committee with the following properties:

- *Adaptive adversary*: The adversary can corrupt nodes after seeing the protocol's random coins. Safety holds as long as the corrupted set remains below $f$.
- *View-change protocol*: Handles leader failure without requiring synchrony assumptions during normal operation.
- *Block finalization*: Once $2f+1$ members attest to a block, it is finalized and cannot be reverted.

Federation blocks contain:

- Attested Merkle roots (the freshness anchors for offline verification).
- Revocation tree updates.
- Budget rebalancing instructions.

== BLS Threshold Signatures (Hints)

Instead of collecting $n$ individual Ed25519 signatures for each attested root, the federation produces a _constant-size_ BLS12-381 threshold signature:

```rust
pub struct FederationCommittee {
    pub global: Arc<GlobalData>,      // KZG parameters
    pub universe: UniverseSetup,      // committee-specific
    pub num_members: usize,
    pub threshold: F,                 // BFT threshold as field element
}
```

A quorum certificate (QC) is a single aggregate BLS signature proving that a weighted threshold of committee members signed the root. Verification cost is constant regardless of committee size ($tilde$32 ms for aggregate verification including the SNARK check).

== Attested Roots <sec-multi-root>

The federation periodically publishes attested roots---signed Merkle root hashes that serve as freshness anchors:

$ "AttestedRoot" = ("root": ["u8"; 32], "height": "u64", "timestamp": "u64", "qc": "ThresholdQC") $

A verifier with a recent attested root can verify any presentation offline. If the root is stale (beyond a configurable freshness window), the verifier may:
- Accept with a freshness warning.
- Reject and request a newer root.
- Accept unconditionally (for use cases where revocation timeliness is not critical).

There is no "call home" requirement for verification.

// ─── 8. Coordination ─────────────────────────────────────────────────────────

= Coordination

== Causal Ordering (DAG)

For operations that do not require atomicity, silos maintain a causal DAG of events. Each event references its causal predecessors via hash pointers. This provides:

- Partial ordering without global consensus.
- Duplicate detection (content-addressed events).
- Convergent state under concurrent non-conflicting operations.

== Atomic Coordination (2PC)

Cross-silo turns that touch multiple cells require atomicity. Pyana uses two-phase commit with threshold quorum certificates:

+ *Prepare*: The coordinator sends the turn to all participant silos. Each silo validates preconditions and locks the affected cells.
+ *Commit/Abort*: If all participants vote `Yes` (with valid signatures), the coordinator broadcasts `Commit`. Otherwise, `Abort` triggers fast unlock.

*Known limitation*: The current 2PC implementation lacks a timeout mechanism. A crashed coordinator can leave resources locked indefinitely. Adding a timeout with recovery protocol is planned.

== Bounded Counters (Stingray)

Concurrent resource spending (computron budgets, API rate limits, storage quotas) uses bounded counters adapted from Stingray @stingray:

$ "slice"(i) = "balance" dot (f+1) / (2f+1) $

where $f$ is the number of Byzantine silos to tolerate. Each silo $i$ can debit locally up to its slice without coordination. The invariant:

$ sum_i "spent"(i) <= "balance" $

holds even if $f$ silos are Byzantine (they can spend at most their slice, and the total of all slices does not exceed the balance).

When a slice is exhausted, the silo must _rebalance_---requesting a fresh allocation from the budget coordinator. Rebalancing is the only coordination point; between rebalances, debits are purely local.

*Fast unlock*: When a 2PC abort occurs, locked budget amounts are released immediately without waiting for an epoch boundary. This is critical for responsiveness in abort-heavy workloads.

```rust
pub type ComputronBudget = BudgetCoordinator;

// Each silo maintains:
pub struct BudgetSlice {
    pub silo_id: SiloId,
    pub remaining: ResourceAmount,
    pub version: BudgetVersion,
}
```

// ─── 9. Network Layer ────────────────────────────────────────────────────────

= Network Layer

== Plumtree Gossip

Message dissemination uses a Plumtree-inspired @plumtree hybrid push protocol over QUIC:

- *Eager push*: Full messages are forwarded immediately to a small eager set (default degree 3), forming a spanning tree for $O("diam")$ latency delivery.
- *Lazy push*: `IHave` notifications (32-byte message hash) are sent to remaining peers. If a peer receives an `IHave` for an unseen message and the eager delivery does not arrive within 500ms, it sends a `Graft` request.
- *Prune*: Demotes a slow eager link when a faster path already delivered the message.
- *Anti-entropy*: Periodic Bloom filter exchange (every 30s) catches messages missed by the eager/lazy protocol.

```rust
const DEFAULT_EAGER_DEGREE: usize = 3;
const IHAVE_TIMEOUT: Duration = Duration::from_millis(500);
const ANTI_ENTROPY_INTERVAL: Duration = Duration::from_secs(30);
const SEEN_TTL: Duration = Duration::from_secs(300);
```

*Known limitation*: The current gossip implementation is one-hop only (messages are not re-forwarded beyond the first gossip step). Multi-hop forwarding with TTL-bounded propagation is planned.

== QUIC Transport

All inter-silo communication uses QUIC (via Quinn). QUIC provides:

- Multiplexed streams over a single connection.
- 0-RTT connection resumption for repeated inter-silo communication.
- Native flow control and congestion management.
- TLS 1.3 for transport encryption.

*Known limitation*: The current implementation uses `SkipCertVerification` (no peer authentication at the transport layer). Production deployment requires certificate pinning or a node ID allowlist.

== Wire Protocol

The presentation/verification wire protocol uses `postcard` framing over TCP:

- `SubmitPresentation { proof, public_inputs, signature }`
- `VerifyPresentation { result: bool, error: Option<String> }`
- `SubmitRevocation { token_id, signature }`
- `QueryRoot { response: AttestedRoot }`

STARK proofs are verified on receipt---a silo never stores or forwards an unverified proof.

// ─── 10. Security Analysis ───────────────────────────────────────────────────

= Security Analysis

== Soundness

*STARK soundness*: The BabyBear STARK achieves $tilde 100$-bit soundness via FRI proximity testing. A computationally bounded adversary cannot produce a valid proof for a false statement except with negligible probability.

*Datalog soundness*: The trace verifier checks that each derivation step is valid (rule exists, body atoms unify against known facts, checks pass, derived fact matches rule head). Completeness is not verified---only that the _claimed_ derivation is correct.

*Capability confinement*: The fold AIR enforces that each $F_(i+1) subset.eq F_i$. A prover cannot add facts (amplify capabilities) at any fold step.

*Replay protection*: Turns carry monotonically increasing nonces per cell. The executor rejects duplicate nonces.

== Known Vulnerabilities (Honest Disclosure)

Per the security audit (May 2026), the following critical issues exist in the current implementation:

+ *Turn executor does not verify Ed25519 signatures*---accepts any 64 bytes. This means any party can submit turns as any cell.
+ *Turn executor does not verify ZK proofs*---accepts any byte sequence. Proof-authorized cells are effectively unprotected.
+ *Coordinator does not check vote signatures in 2PC*---a single malicious node can force commits.
+ *Wire protocol uses truncated signatures (32 bytes instead of 64)*---unverifiable.

These are straightforward fixes (each is a missing verification call) but represent the current gap between the cryptographic primitives (which are real and correct) and their integration into the execution layer.

== Trust Boundary Diagram

#figure(
  ```
  ┌──────────────────────────────────────────┐
  │     Federation Trust Boundary             │
  │                                           │
  │  Ed25519 identity, BLS12-381 threshold    │
  │  (classical -- PQ migration planned)      │
  │                                           │
  │    ┌─────────┐       ┌─────────┐         │
  │    │ Silo A  │ ←───→ │ Silo B  │         │
  │    └────┬────┘       └────┬────┘         │
  │         │                  │              │
  └─────────┼──────────────────┼─────────────┘
            │                  │
       STARK proofs only (PQ-secure)
            │                  │
  ┌─────────▼──────────────────▼─────────────┐
  │       External Verifiers                  │
  │  (see only: proof + public inputs)        │
  └──────────────────────────────────────────┘
  ```,
  caption: [Trust boundaries. Classical cryptography is confined within the federation.],
)

== Post-Quantum Roadmap

The STARK proof path is post-quantum today (hash-based, no elliptic curves). The classical components (BLS12-381, Ed25519, X25519) are inside trust boundaries and have a staged migration path:

+ *Phase 1 (current)*: Scheme-agile `ThresholdScheme` trait abstracts signature operations.
+ *Phase 2 (2027)*: Replace BLS12-381 QCs with lattice threshold signatures (Hermine, Oriole, or TalonG---pending NIST threshold call).
+ *Phase 3*: Replace Ed25519 node identity with ML-DSA (FIPS 204).
+ *Phase 4*: Replace X25519 in sealed secrets with ML-KEM (FIPS 203).

The architecture was designed for this migration: classical signatures never cross trust boundaries, so replacing them is an internal committee operation.

// ─── 11. Chain Integration ───────────────────────────────────────────────────

= Chain Integration

== EVM/Base Settlement

For applications requiring on-chain settlement (e.g., staking, slashing, or cross-chain authorization verification), Pyana provides an EVM bridge:

+ The prover generates a Nova IVC proof of the full attenuation chain (constant size regardless of chain length).
+ The Nova proof is compressed to Groth16 via the decider circuit.
+ The Groth16 proof is submitted to a verifier contract on Base/Ethereum.
+ Verification cost: $tilde$200k gas (comparable to a Tornado Cash withdrawal).

== Federation Root Anchoring

Federation roots can be anchored on-chain for maximum availability:

$ "anchor"("root", "height", "qc") -> "on-chain event" $

This provides a fallback for verifiers that cannot reach the federation gossip network directly. The on-chain root is updated per federation epoch (configurable; e.g., every 10 minutes).

== What Settlement Provides

On-chain settlement is *optional*. It provides:

- *Public verifiability*: Anyone can verify a federation root was attested at a given height.
- *Slashing*: Misbehaving federation members can have stake slashed.
- *Cross-chain interop*: Other chains can read Pyana federation state.

Without settlement, the system still functions (offline verification against gossip-distributed roots). Settlement adds economic security guarantees.

// ─── 12. Performance ─────────────────────────────────────────────────────────

= Performance

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Latency*], [*Notes*]),
    [Macaroon verify (trusted mode)], [$tilde 8 mu s$], [HMAC-SHA256, constant-time],
    [Datalog evaluation (7 rules, 5 facts)], [$tilde 12 mu s$], [Bottom-up to fixpoint],
    [STARK proof generation], [$tilde 64 mu s$], [BabyBear + FRI, single fold step],
    [STARK verification], [$tilde 438 mu s$], [FRI proximity + Merkle check],
    [BLS threshold aggregate + verify], [$tilde 32 "ms"$], [4-member committee, includes SNARK],
    [End-to-end presentation (wire)], [$tilde 560 "ms"$], [3-node demo, TCP, real STARK],
    [Proof size (BabyBear STARK)], [24 KiB], [Single fold step],
  ),
  caption: [Measured performance on Apple M-series hardware. Numbers represent the current (non-optimized) implementation.],
)

*Performance trajectory*: The 560ms end-to-end number includes unoptimized TCP setup, proof generation for a single fold step, serialization, and verification. With recursive proof composition (planned), multi-step chains would not increase this linearly---each step would fold into the running instance.

*Comparison*: Mina Protocol's Kimchi proofs take $tilde$1--3 seconds to generate but achieve constant-size via Pickles recursion. Pyana's BabyBear STARK is faster to generate but currently grows with chain length. Nova-based IVC (when integrated) will provide constant-size proofs with per-step cost comparable to the current 64$mu s$ generation time.

// ─── 13. Related Work ────────────────────────────────────────────────────────

= Related Work

*Mina Protocol* @mina. Pyana's execution model (cells$equiv$accounts, turns$equiv$ZkappCommands, call forests, preconditions) is directly adapted from Mina. The key difference is domain: Mina manages financial state with succinct blockchain proofs; Pyana manages authorization state with private capability proofs. Both use recursive proof composition to compress state histories, though Pyana's recursion is not yet implemented.

*Midnight* @midnight. A privacy-focused blockchain using Plonk proofs for shielded transactions. Like Pyana, Midnight separates public and private state. Unlike Pyana, it targets DeFi rather than authorization, requires chain liveness, and does not support capability delegation semantics.

*Cosmos IBC* @ibc. Cross-chain messaging with light-client verification. IBC requires active relayers and chain liveness for message delivery. Pyana's offline verification (proof + root) is a stronger availability guarantee for authorization use cases.

*UCAN/ZCAP-LD* @ucan. Decentralized authorization with delegation chains. UCAN provides the correct _semantics_ (attenuation, delegation, invocation) but delegation chains are transparent---any verifier sees the full chain. Pyana proves the same authorization relationship without revealing the chain.

*Coconut* @coconut. Threshold issuance of anonymous credentials with selective attribute disclosure. Coconut is attribute-based (prove you have attribute X) rather than capability-based (prove you can do action Y on resource Z). It lacks delegation/attenuation semantics.

*Stingray* @stingray. Bounded counters for BFT payment channels. Pyana adapts Stingray's split-balance model for concurrent resource budgets across silos. The formula $"slice" = "balance" dot (f+1)/(2f+1)$ is directly from Stingray.

*Morpheus* @morpheus. Adaptive BFT consensus tolerating a dynamic adversary. Used as-is for federation block finalization. The key property (safety under adaptive corruption) is important for federations where the adversary may observe protocol messages before choosing which nodes to corrupt.

*Google Macaroons* @macaroons. HMAC-chained bearer tokens with caveats. Pyana uses macaroons as the _encoding format_ for capabilities (the wire representation that agents carry). The novel contribution is proving properties of the macaroon chain in zero knowledge.

*Biscuit* @biscuit. Ed25519 + Datalog bearer tokens. Pyana supports Biscuit as an alternative token backend alongside macaroons, inheriting its Datalog policy language.

// ─── 14. Conclusion ──────────────────────────────────────────────────────────

= Conclusion and Future Work

Pyana demonstrates that object-capability attenuation is naturally structured as incrementally verifiable computation, and that this structure enables zero-knowledge authorization presentation without bolting privacy onto an existing system. The authorization semantics (Datalog evaluation over capability fact sets) map directly to AIR constraints, and the monotonic narrowing invariant (capabilities can only shrink) is exactly the fold operation that IVC proves efficiently.

The system is operational with real cryptography (BabyBear STARK, Poseidon2, Ed25519, BLS12-381, HMAC-SHA256) across 45k lines of Rust. The current implementation achieves sub-second end-to-end presentation with 24 KiB proofs. Critical gaps remain in execution-layer verification (audit findings) and Merkle system unification.

== Future Work

+ *Recursive STARK composition*: True STARK-in-STARK recursion for constant-size proofs regardless of attenuation chain length. This is the single most impactful engineering task.

+ *Datalog evaluation inside the STARK*: Currently the Datalog evaluator runs outside the circuit (the circuit verifies the _trace_ of evaluation). Moving evaluation fully into the AIR would eliminate the need to trust the evaluator implementation, at the cost of a larger circuit.

+ *Unified Poseidon2 Merkle*: End-to-end algebraic hashing for the provable path, eliminating the current BLAKE3/Poseidon2 split.

+ *Post-quantum federation*: Lattice-based threshold signatures (replacing BLS12-381) when NIST standards mature.

+ *Formal verification*: Machine-checked proofs of the fold monotonicity invariant and Datalog evaluation soundness.

+ *Full chain replacement*: For applications currently using lightweight blockchains primarily for authorization (service meshes, IoT device authorization), Pyana may serve as a complete replacement---providing the same guarantees without consensus costs for the common case.

// ─── References ──────────────────────────────────────────────────────────────

#heading(level: 1, numbering: none)[References]

#set text(size: 9.5pt)

#bibliography(title: none, style: "ieee", "refs.yml")
