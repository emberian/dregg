// =============================================================================
// Pyana: A Distributed Object-Capability Runtime
// with Zero-Knowledge Authorization and Proof-Carrying State
// =============================================================================

#set document(
  title: "Pyana: A Distributed Object-Capability Runtime with Zero-Knowledge Authorization and Proof-Carrying State",
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
      Pyana: Distributed Object-Capability Runtime
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

// --- Title -------------------------------------------------------------------

#align(center)[
  #text(size: 18pt, weight: "bold")[
    Pyana: A Distributed Object-Capability Runtime \
    with Zero-Knowledge Authorization and Proof-Carrying State
  ]
  #v(1em)
  #text(size: 11pt)[Ember Arlynx]
  #v(0.3em)
  #text(size: 10pt, fill: luma(80))[
    Draft -- May 20, 2026 \
    `github.com/emberian/pyana`
  ]
]

#v(2em)

// --- Abstract ----------------------------------------------------------------

#heading(level: 1, numbering: none)[Abstract]

We present Pyana, a distributed object-capability runtime in which isolated objects (cells) communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. The core observation is that monotonic capability attenuation---restricting a bearer token's scope through successive delegation---forms an incrementally verifiable computation: each restriction step is a fold over a committed fact set, producing a strictly smaller successor state. We encode capabilities as Datalog fact sets, commit them to 4-ary Merkle trees using Poseidon2 over BabyBear, and prove correct evaluation of authorization rules inside a STARK. The verifier learns a single bit---authorized or not---without observing the delegation chain, intermediate authorities, or the agent's other capabilities.

The runtime implements E-style distributed object semantics: promise pipelining via eventual references, three-party introduction for capability routing, and sealer/unsealer pairs for partition-tolerant offline transfer. A privacy-preserving intent marketplace enables capability discovery without leaking what agents hold. State is proof-carrying: receipt chains serve as the primary state representation, with IVC compression and federation reduced to an ordering service over nullifiers. A Capability Derivation Tree---the distributed dual of seL4's CDT---tracks delegation lineage as a proof structure rather than a kernel-enforced tree.

The system is implemented in approximately 97k lines of Rust across 26 crates, with 1400+ tests, real STARK proof generation ($tilde$24 KiB proofs, sub-second generation on BabyBear4 extension field at 124-bit security), real Ed25519/BLS12-381 cryptography, working multi-node TCP consensus, a browser extension wallet, and 20+ end-to-end demo scenarios in a unified harness.

#v(1em)

// --- 1. Introduction ---------------------------------------------------------

= Introduction

Cross-domain authorization for autonomous agents presents a challenge that existing systems address incompletely. Consider an AI agent dispatched by Organization A to invoke a service hosted by Organization B. The agent must prove it is authorized---but without revealing Organization A's internal delegation structure, the identities of intermediate signatories, or what other capabilities the agent holds.

Existing approaches each fail along a different axis:

- *UCAN/ZCAP-LD* @ucan provide delegation chains but require revealing the full chain to the verifier. Privacy is absent.
- *Coconut credentials* @coconut offer selective disclosure of attributes but lack the delegation semantics needed for capability attenuation.
- *Cap'n Proto RPC* provides promise pipelining and E-style messaging but operates within a single trust domain with no privacy, no proof of authorization, and no offline verification.
- *Blockchain-based authorization* achieves transparency but requires chain liveness, incurs gas costs, and exposes all authorization state on-chain.
- *seL4* @sel4 provides a rigorous Capability Derivation Tree with synchronous kernel-enforced revocation, but requires a single address space and cannot distribute across trust boundaries.

Pyana's contributions are: (1) proving monotonic attenuation of a bearer token chain in zero knowledge with backend-agnostic commitment; (2) a distributed CDT that replaces kernel enforcement with cryptographic proof; (3) E-style messaging semantics (promise pipelining, three-party introduction) integrated with proof-carrying state; and (4) a privacy-preserving intent marketplace for capability discovery.

The design draws from Mina Protocol's execution model (cells as zkApp accounts, turns as ZkappCommands, call forests), E's distributed object semantics (eventual sends, three-party handoff), and seL4's capability derivation (recast as a proof structure for asynchronous distributed systems).

// --- 2. System Model ---------------------------------------------------------

= System Model

== Cells

A _cell_ is the fundamental unit of isolated state, analogous to a Mina zkApp account or an E object. Each cell holds:

- A content-addressed identity $"CellId" in {0,1}^(256)$.
- Mutable state: 8 generic field slots $s_0, ..., s_7 in FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear prime).
- A _capability list_ (c-list): the set of capabilities the cell may exercise.
- Permission requirements specifying what authorization kind is needed for each action type.
- An optional verification key for ZK proof validation.

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

== Turns

A _turn_ is an atomic transaction over one or more cells, analogous to a Mina ZkappCommand or an E turn. A turn contains:

- A _call forest_: a tree of actions, executed depth-first.
- A fee (in computrons) covering execution cost.
- A nonce (monotonically increasing per cell) for replay protection.
- Authorization: Ed25519 signature, ZK proof, or both.

If any action in the call forest fails, all effects are rolled back via journal replay. This provides atomicity.

== Silos and Federations

A _silo_ is a node that holds cells, executes turns, and participates in federation consensus. A _federation_ is a committee of 3--64 silos sharing a trust root. Federation members run Morpheus @morpheus adaptive BFT consensus to agree on attested Merkle roots, revocation tree updates, and budget rebalancing epochs. The honest-majority assumption is standard: tolerate $< n\/3$ Byzantine members.

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

The critical invariant: *everything that crosses a trust boundary is post-quantum secure*. Classical cryptography exists only between parties that already trust each other.

// --- 3. Execution Model ------------------------------------------------------

= Execution Model

== Pipeline Execution with Topological Ordering

The executor processes turns not only individually but in _pipelines_: batches of turns with declared dependency edges. A pipeline $P = (T, E)$ where $T = {t_0, ..., t_n}$ and $E subset.eq T times T$ is a DAG of dependency edges. The executor computes a topological ordering and processes turns in causal order. If turn $t_i$ fails and $t_j$ depends on $t_i$, then $t_j$ receives a `DependencyFailed` error without executing.

== BudgetGate Integration

Every turn pays a fee in _computrons_. The executor integrates Stingray @stingray bounded counters directly: each silo holds a local budget slice $"slice"(i) = "balance" dot (f+1)/(2f+1)$ and debits locally without coordination until exhaustion. The executor checks $"fee" <= "remaining"$ before execution (fail-fast) and debits atomically upon commit. Budget accounting uses checked arithmetic throughout---overflow produces an executor error, never wraps.

== Conservation Invariant

For any turn $t$ with actions $a_1, ..., a_k$, the executor enforces:

$ sum_i "balance_change"(a_i) + "fee"(t) = 0 $

Value cannot be created or destroyed within a turn. The fee is debited from the agent cell and does not reappear---it is the cost of execution.

// --- 4. Authorization Semantics ----------------------------------------------

= Authorization Semantics

== Capabilities as Datalog Facts

Authorization state is encoded as a set of Datalog facts. A fact is a ground atom $"fact" := "predicate"("term"_1, ..., "term"_k)$. Attenuation transforms a fact set $F$ into $F' subset.eq F$ by removing facts. The HMAC chain in a macaroon token makes removal of caveats cryptographically impossible---attenuation is irreversible.

== Dual-Mode Evaluation

The same Datalog rules yield the same answer in two modes:

- *Trusted mode* (local evaluation): Cost $tilde 8 mu s$. Used within a trust boundary.
- *Trustless mode* (STARK proof): The prover generates a STARK proof that Datalog evaluation produced `allow`. Cost $tilde 64 mu s$ prove, $tilde 438 mu s$ verify.

Both modes evaluate identical rules over identical data. The proof attests to the computation, not to a separate protocol.

// --- 5. E-Style Distributed Object Semantics ---------------------------------

= E-Style Distributed Object Semantics

== EventualRef and Promise Pipelining

In E @elang, a message send returns a _promise_ that resolves when the target processes the message. Multiple messages can be sent to the resolution of a pending promise without waiting for it to resolve---_promise pipelining_ eliminates round-trip latency in distributed object protocols.

Pyana implements this via `EventualRef`: a reference to the output of a pending turn, identified by the turn's hash and an output slot index. A turn may target an `EventualRef` rather than a concrete `CellId`, declaring a dependency that the executor resolves during pipeline execution. The `Target` type is a sum:

$ "Target" = "Concrete"("CellId") | "Eventual"("source_turn": ["u8"; 32], "slot": "u32") $

When the source turn commits, its outputs (granted capabilities, created cells, state updates) populate a resolution table. Dependent turns rewrite their `EventualRef` targets to concrete `CellId` values before execution.

== Three-Party Introduction

Object-capability systems form new communication paths through _introductions_: Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by granting Bob a (possibly attenuated) capability to Carol. In Pyana, an `Effect::Introduce` during a turn emits a `RoutingDirective`:

$ "RoutingDirective" = ("sender": "CellId", "target": "CellId", "authorizing_turn": ["u8"; 32], "expires": "Option"("u64")) $

The node's routing table is populated from these directives. No global directory exists---all communication paths are introduced, not discovered.

== Comparison with E and Cap'n Proto

E's promise pipelining requires a live vat (process) hosting the target object. Cap'n Proto @capnproto extends this to RPC with three-party handoff across address spaces, but within a single trust domain. Pyana differs in three respects:

+ *Proof-carrying*: A pipelined message carries (or can generate) a STARK proof that the sender is authorized to invoke the target. No live vat is needed to check authorization---verification is offline.
+ *Asynchronous, no blocking IPC*: Pipelines are submitted as batches with explicit dependency DAGs. There is no synchronous call semantics.
+ *Privacy*: The introduction graph is private to the parties involved. A routing directive is visible only to the node executing the turn and the introduced parties.

// --- 6. Capability Derivation and Revocation ---------------------------------

= Capability Derivation and Revocation

== The Capability Derivation Tree

In seL4 @sel4, every capability exists in a _Capability Derivation Tree_ (CDT): a tree rooted at the original untyped memory capability, where each child is derived (copied with possible attenuation) from its parent. The kernel traverses this tree synchronously to revoke an entire subtree in $O(n)$ time.

Pyana maintains a distributed analog. Each delegation step records:

$ "DelegationEdge" = ("parent": "CapHash", "child": "CapHash", "attenuation": Delta, "epoch": "u64") $

These edges form a tree committed to a Merkle structure. The CDT is not enforced by a kernel---it is _proved_ by the delegator at each step.

== The Duality: Enforce vs. Prove

The key intellectual distinction:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Property*], [*seL4 (kernel-enforced)*], [*Pyana (proof-carried)*]),
    [Tree structure], [In-kernel data structure], [Merkle-committed proof tree],
    [Revocation], [Kernel walks tree synchronously], [Verifiable revocation claim],
    [Latency], [Instantaneous (same address space)], [Bounded staleness],
    [Distribution], [Single machine], [Cross-federation],
    [Trust model], [Kernel is TCB], [Hash function is TCB],
    [Verification], [Hardware-enforced access], [STARK proof of non-membership],
  ),
  caption: [CDT duality: seL4 ENFORCES the tree; Pyana PROVES the tree.],
)

In seL4, revocation is authoritative because the kernel IS the tree---traversal and deletion are the same operation. In Pyana, the tree is a claim that anyone can verify: the delegator proves their capability descends from a valid root, and the revoker proves non-membership in the current valid set.

== Delegation: Snapshot + Refresh

Delegation follows a snapshot-refresh model with bounded staleness. A child cell receives a point-in-time snapshot of its parent's c-list:

$ "DelegatedRef" = ("source", "snapshot": ["CapabilityRef"], "epoch", "refreshed_at", "max_staleness") $

The child acts offline using the snapshot. Acceptors (remote verifiers) reject presentations where $"now" - "refreshed_at" > "max_staleness"$. This creates a configurable tradeoff between availability and revocation freshness.

== RevocationChannel: Opt-in Synchrony

For applications requiring instant revocation (high-value credentials, safety-critical access), Pyana provides an opt-in synchrony primitive: the _RevocationChannel_. A capability enrolled in a RevocationChannel is checked against a real-time revocation feed before acceptance. This restores seL4-like instant revocation at the cost of requiring channel liveness.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, center),
    table.header([*Mode*], [*Revocation Latency*], [*Requires Liveness*], [*Analogy*]),
    [No check], [$infinity$ (never revoked)], [No], [Bearer token],
    [Epoch-stale], [$<= "max_staleness"$], [No], [OCSP stapling],
    [Channel-sync], [Real-time], [Yes (channel)], [CRL push],
    [Kernel-sync], [Instantaneous], [Yes (kernel)], [seL4 CDT],
  ),
  caption: [Revocation modes from weakest to strongest. Pyana supports the first three; seL4 achieves the fourth by being a kernel.],
)

The design philosophy: instant revocation is not free in a distributed system. Rather than pretending it is (and failing under partition), Pyana makes the cost explicit and lets applications choose their revocation tier.

// --- 7. Privacy-Preserving Intent Marketplace --------------------------------

= Privacy-Preserving Intent Marketplace

== The Discovery Problem

Object-capability systems solve authorization but not discovery: if you need a capability to communicate, how do you find someone who holds the capability you need? Traditional answers (directories, service registries) violate the principle of least authority by publishing capability inventories.

== Architecture

The intent engine inverts discovery. Rather than revealing held capabilities, agents broadcast _needs_ and privately evaluate whether they can satisfy others' needs:

+ *Public intents*: A page broadcasts "I need capability matching spec $S$" as a content-addressed `Intent` identified by a blinded `CommitmentId`. The intent reveals the _shape_ of needed capability without revealing the requester's identity.
+ *Private matching*: Wallets evaluate intents locally using Datalog: "does any token in my wallet satisfy spec $S$?" This evaluation never leaves the wallet.
+ *STARK fulfillment*: If a match exists, the wallet generates a STARK proof of capability satisfaction---proving "I hold a token that satisfies $S$" without revealing which token, what delegation chain, or what else it holds.

== Anti-Frontrunning via Commit-Reveal

Intent fulfillment uses a commit-reveal protocol: the satisfier first publishes a commitment $C = H("intent_id" || "satisfier_secret")$, then reveals the proof. This prevents a frontrunner from observing a match proof in the gossip network and racing to submit their own fulfillment.

== What This Solves

The intent marketplace enables capability discovery without a capability directory. The requester learns only that _someone_ can satisfy their need. The satisfier reveals only that they _can_ satisfy it (via STARK), not what they hold. The gossip network sees intents (public needs) but never capabilities (private holdings).

// --- 8. Proof-Carrying State -------------------------------------------------

= Proof-Carrying State

== Receipt Chains as Primary State

Every committed turn produces a `TurnReceipt` containing pre/post state hashes, effects hash, and computron cost. These receipts chain: $"receipt"[n]."post_state_hash" = "receipt"[n+1]."pre_state_hash"$. The chain of receipts IS the agent's state proof---anyone can verify from genesis without contacting a federation.

== IVC Compression

The IVC layer compresses an arbitrary-length receipt chain into a constant-size proof. A verifier needs only:

+ The `IvcProof` (proves the chain is valid from genesis).
+ The current state commitment (proves what state the chain produced).
+ A nullifier non-membership proof (proves no double-spends).

== Federation as Ordering Service

The federation's role shrinks from state container to ordering service. It attests only to:

$ "AttestedRoot" = ("nullifier_root", "note_tree_root", "height", "timestamp", "qc") $

The federation does NOT attest to cell state. Cell state is proved by the cell's own receipt chain. This separation means the federation provides anti-double-spend ordering while agents own their own state.

== Federation Exit

An agent leaves a federation by simply stopping submission of nullifiers. Their proof chain is portable---it proves state validity from genesis without referencing federation-specific data. The agent can join another ordering service (presenting their chain as genesis state) or operate standalone.

// --- 9. Sealer/Unsealer Pairs ------------------------------------------------

= Sealer/Unsealer Pairs

== Construction

E's sealer/unsealer primitive enables rights amplification: the sealer encrypts data that only the unsealer holder can read. Pyana implements this with X25519 Diffie-Hellman:

- *Key generation*: X25519 keypair. `sealer_public` = public key; `unsealer_secret` = private key.
- *Sealing*: Fresh ephemeral X25519 keypair $arrow.r$ DH(ephemeral, sealer_public) $arrow.r$ ChaCha20-Poly1305 encryption.
- *Unsealing*: DH(unsealer_secret, ephemeral_public) $arrow.r$ same shared secret $arrow.r$ decrypt.

Each seal uses a fresh ephemeral key, providing forward secrecy.

== Partition-Tolerant Offline Transfer

The critical use case: transferring a capability to a party that is currently offline or unreachable. The sender seals the capability under the recipient's `sealer_public`. The sealed box can traverse untrusted channels---the ciphertext reveals nothing about the capability. When the recipient comes online, they unseal using their `unsealer_secret`.

This enables a form of offline capability delegation that neither UCAN (requires online verification of the full chain) nor traditional capability systems (require live introduction) support.

== Relationship to Rights Amplification

In E, sealer/unsealer pairs enable brand-checking: "only the holder of this specific unsealer can access this data." Pyana extends this pattern cryptographically---the sealed box carries a BLAKE3 commitment that binds the ciphertext to the capability without revealing it, enabling verification that the box contains a well-formed capability even without unsealing.

// --- 10. Commitment Scheme ---------------------------------------------------

= Commitment Scheme

== 4-ary Merkle Trees

Pyana uses quaternary Merkle trees: each internal node hashes 4 children via $"Poseidon2"(c_0, c_1, c_2, c_3)$ over BabyBear (width 8, $alpha = 7$, 8 external + 22 internal rounds). The 4-ary structure halves tree height relative to binary trees.

== Multi-Hash Roots

The federation publishes roots under multiple commitment schemes:

$ R_"STARK" &= "Poseidon2Root"(F) \
  R_"Binius" &= "Groestl256Root"(F) \
  R_"Halo2" &= "PoseidonBN254Root"(F) $

Each proof backend references the root native to its field.

== Fold Deltas

A _fold delta_ records a monotonic state transition: $Delta_(i -> i+1) = { f in F_i | f in.not F_(i+1) }$. The commitment to $F_(i+1)$ can be computed incrementally from $F_i$ and $Delta$---this is the structure enabling IVC.

// --- 11. Zero-Knowledge Presentation -----------------------------------------

= Zero-Knowledge Presentation

== The Fold AIR

The STARK proves:

#quote(block: true)[
  "There exists a sequence of fact sets $F_0 supset.eq F_1 supset.eq ... supset.eq F_k$ such that $F_0$ is committed under a federation-attested root, each $F_(i+1) = F_i backslash Delta_i$ for valid removal sets $Delta_i$, and evaluating the standard policy rules over $F_k$ with the given request yields `allow`."
]

The AIR has three constraint families: membership (facts are valid leaves), fold (removals are correct), and derivation (Datalog steps are valid).

== Public Inputs and Zero-Knowledge

The verifier receives: federation root $R$, authorization request $(A, S, "Act")$, current time $t$, and the proof $pi$ ($tilde$24 KiB). From these, verification produces a single bit. The verifier learns nothing about chain length, intermediate delegators, other capabilities, or the issuer's identity.

All STARK proofs use real Poseidon2 constraints over BabyBear4 (degree-4 extension field, providing 124-bit security). There are no vacuous or mock constraints in the production path.

// --- 12. Proof Architecture --------------------------------------------------

= Proof Architecture

This section precisely states what each proof in the system proves, how they compose, and the resulting security guarantees. We work over $FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear) with degree-4 extension $FF_(p^4)$ providing 124-bit challenge security.

== Individual Proof Statements

=== Poseidon2 Permutation Proof

*Public inputs:* Input state $bold(x) in FF_p^8$, output state $bold(y) in FF_p^8$.

*Private witness:* None (this is a deterministic computation proof).

*Statement:* $bold(y) = "Poseidon2"(bold(x))$ where Poseidon2 uses width 8, $alpha = 7$ (degree-7 S-box), 8 external rounds + 22 internal rounds.

*Constraints:* The AIR evaluator recomputes the full Poseidon2 permutation inside the constraint function and checks $bold(y)_i - "computed"_i = 0$ for all $i in {0, ..., 7}$, combined via random linear combination with verifier challenge $alpha$. Constraint degree: 7.

*Soundness:* A cheating prover claiming $bold(y)' != "Poseidon2"(bold(x))$ produces a nonzero constraint polynomial. The STARK quotient polynomial then has degree exceeding the expected bound, and FRI rejects with overwhelming probability.

=== Merkle Membership Proof

*Public inputs:* Leaf hash $ell in FF_p$, root $r in FF_p$.

*Private witness:* For each level $i in {0, ..., d-1}$: siblings $(s_(i,0), s_(i,1), s_(i,2)) in FF_p^3$ and position $p_i in {0, 1, 2, 3}$.

*Statement:* $exists$ authentication path from $ell$ to $r$ in a 4-ary Poseidon2 Merkle tree of depth $d$.

*Constraints (per level):*

$ &"position validity:" quad p_i (p_i - 1)(p_i - 2)(p_i - 3) = 0 \
  &"hash binding:" quad "parent"_i = "Poseidon2"_("4-to-1")(c_0, c_1, c_2, c_3) $

where children $(c_0, ..., c_3)$ are determined by Lagrange interpolation on position: the current hash occupies slot $p_i$, siblings fill the remaining slots. Chain continuity: $"parent"_i = "current"_(i+1)$, with $"current"_0 = ell$ and $"parent"_(d-1) = r$.

*Soundness:* Finding a false membership proof requires either (a) a Poseidon2 collision (finding two distinct inputs that hash to the same output), or (b) forging a valid low-degree polynomial that satisfies the degree-7 hash constraint at random evaluation points. Both reduce to collision resistance of Poseidon2 over $FF_p$.

=== Note Spending Proof

*Public inputs:* Nullifier $nu in FF_p$, Merkle root $r in FF_p$.

*Private witness:* Owner $o$, value $v$, asset type $a$, creation nonce $n$, randomness $rho$, spending key $k$, Merkle path $(bold(s)_i, p_i)$ for $i in {0, ..., d-1}$.

*Statement:* There exist $(o, v, a, n, rho, k)$ and a Merkle path such that:

$ "commitment" &= "Poseidon2"(o, v, a, n, rho) \
  nu &= "Poseidon2"("commitment", k, n) \
  &"commitment is a leaf under root" r "via the given path" $

*Constraints (5 families):*
+ _Is-Merkle binary:_ $m dot (m - 1) = 0$ where $m$ gates commitment vs. Merkle rows.
+ _Commitment preimage (row 0):_ $(1-m) dot ("commitment" - "Poseidon2"(o, v, a, n, rho)) = 0$.
+ _Nullifier derivation (row 0):_ $(1-m) dot (nu - "Poseidon2"("commitment", k, n)) = 0$.
+ _Position validity (all rows):_ $p(p-1)(p-2)(p-3) = 0$.
+ _Hash binding (Merkle rows):_ $m dot ("parent" - "Poseidon2"_("4-to-1")("children by position")) = 0$.

*Soundness:* A cheating prover cannot:
- Spend without the spending key: producing a valid $nu$ requires knowing $k$ (Poseidon2 preimage resistance).
- Spend a nonexistent note: the commitment must exist in the tree (Merkle soundness).
- Double-spend: the nullifier $nu$ is deterministic given $(k, "commitment", n)$; the verifier maintains a nullifier set and rejects duplicates.

=== Multi-Step Datalog Derivation Proof

*Public inputs:* Initial state root $R_0 in FF_p$, request hash $h in FF_p$, conclusion $c in {0, 1}$, step count $N$, final accumulated hash $H_N in FF_p$.

*Private witness:* For each step $i in {1, ..., N}$: rule ID, body fact hashes, substitution $sigma$, head predicate, head terms, equal/memberof/GTE checks.

*Statement:* Starting from fact set committed under $R_0$, there exists a sequence of $N$ valid Datalog rule applications where:
- Each step's body facts have hashes present under root $R_0$
- Variable substitutions are correctly applied (selector columns enforce $sigma$)
- Equal checks hold: $sigma("lhs") = sigma("rhs")$
- MemberOf checks hold: element $in$ set
- GTE checks hold via bit decomposition (high bit = 0 ensures non-negative diff)
- The final step derives predicate $"ALLOW"$ (if $c = 1$)
- The hash chain $H_i = "Poseidon2"(H_(i-1) || "derived_hash"_i)$ commits to the full trace

*Constraints (19 families):* Binary flags, substitution application via selector one-hot vectors, equal/memberof enforcement, GTE range check (31-bit decomposition with high-bit-zero), accumulated hash chain correctness, final-step-derives-ALLOW (gated by conclusion), body roots match state root, active-monotone-decreasing.

*Constraint degree:* 4 (dominated by position validity and GTE bit binary checks).

*Soundness:* A cheating prover cannot:
- Claim ALLOW without deriving it: the constraint $c dot "is_final" dot ("head_pred" - "ALLOW") = 0$ forces the final step's predicate to be ALLOW when $c = 1$.
- Skip a rule step: the accumulated hash chain commits to every derivation step; tampering changes $H_N$.
- Use facts not in the committed set: body root constraints force $"root"_i = R_0$ for every active body atom.
- Forge a substitution: selector-sum and substitution-application constraints algebraically bind derived terms to body atoms.

=== Fold Chain (Attenuation) Proof

*Public inputs:* Old root $R_"old" in FF_p$, new root $R_"new" in FF_p$.

*Private witness:* Removed facts with predicates, terms, and Merkle membership proofs under $R_"old"$.

*Statement:* There exists a set of facts $Delta subset.eq F_"old"$ such that removing $Delta$ from the fact set committed under $R_"old"$ yields the fact set committed under $R_"new"$, and each fact in $Delta$ has a valid Merkle membership proof under $R_"old"$.

*Constraints:*
- Fact hash correct: $"hash" = "Poseidon2"("predicate", "terms")$
- Membership verified: each removed fact's hash is a valid leaf under $R_"old"$
- Root transition binding: $"transition_hash" = "Poseidon2"(R_"old" || R_"new" || "fact_hashes")$

*Soundness:* Capability amplification is impossible: the prover can only _remove_ facts from $F_"old"$ (enforced by membership proofs under $R_"old"$). Adding a fact not in $F_"old"$ requires forging a Merkle membership proof---equivalent to breaking Poseidon2 collision resistance.

=== IVC Fold Chain Accumulation

*Public inputs:* Initial root $R_0 in FF_p$, final root $R_N in FF_p$, step count $N$, accumulated hash $H in FF_p$.

*Private witness:* For each step $i$: old root, new root, fold validity flag, hash chain values.

*Statement:* There exists a sequence of $N$ valid fold steps $R_0 -> R_1 -> ... -> R_N$ where:
- Each transition is a valid fold (monotone fact removal)
- Root continuity: $R_i^"new" = R_(i+1)^"old"$
- Hash chain: $H_i = "Poseidon2"(H_(i-1) || R_i^"new" || i)$ with $H_0 = "Poseidon2"("IVC0" || R_0 || 0)$
- The final accumulated hash $H = H_N$

*Key property:* The proof is _constant size_ regardless of $N$. Growth is $O(log N)$ via FRI compression.

*Soundness:* Reordering attacks are prevented by including step count in the hash. Chain breaks (skipping a root transition) are caught by root continuity constraints. The trace commitment binds the IVC proof to actual fold computations.

=== Recursive Verification Proof

*Public inputs:* Inner proof's public inputs $pi_0, ..., pi_k$, proof commitment $C in FF_p$.

*Private witness:* The inner proof's trace commitment, constraint commitment, FRI betas, query index, query trace values, Merkle authentication paths, quotient value, FRI layer values.

*Statement:* There exists a valid STARK proof $pi$ whose public inputs are $(pi_0, ..., pi_k)$ and whose verification passes: Fiat-Shamir transcript replay produces challenges consistent with the committed data, FRI folding relations hold ($"even" + beta dot "odd" = "folded"$), and the quotient polynomial check passes at the queried point.

*Constraints:*
- Validity binary and always-one: every row passes its local check
- Section tag validity: $"tag" in {0, 1, 2, 3, 4}$
- FRI folding: $"data"_3 = "data"_0 + "data"_2 dot "data"_1$ (universal, satisfied trivially by non-FRI rows)
- Proof commitment binding (last row): $"challenge_acc" = C$ (public input)

*Soundness:* Forging a recursive proof requires either finding a valid STARK proof for a false statement (STARK soundness) or producing a verifier trace that claims valid-but-actually-isn't (caught by the constraint that validity flags must all be 1 and the FRI folding must hold algebraically). The Poseidon2 hash chain in `challenge_acc` binds all verification data, so the final commitment uniquely identifies the verified proof.

== Proof Composition

=== Full Authorization Proof

The complete authorization proof composes:

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Full Authorization Proof =
    Derivation Proof (N rule steps → ALLOW)
  + Body Membership Proofs (each body fact ∈ tree under R₀)
  + Fold Chain Proof (R_issuer → R₀ via attenuation)
  + Issuer Membership Proof (issuer ∈ federation Merkle tree)
```
]]

The binding between components uses shared public inputs:
- The derivation proof's `initial_state_root` = the fold chain's `final_root` $R_0$
- The fold chain's `initial_root` = the issuer's committed capability root
- The issuer membership proof's root = the federation's attested root

=== Note Spending Proof

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Note Spending Proof =
    Spending Key Knowledge (nullifier = H(commitment ‖ key ‖ nonce))
  + Commitment Preimage (commitment = H(owner ‖ value ‖ asset ‖ nonce ‖ rand))
  + Merkle Membership (commitment ∈ note tree under root r)
```
]]

All three sub-statements are enforced in a _single_ AIR with 12 columns. The commitment row (row 0) handles key knowledge and preimage; subsequent rows handle Merkle membership. A row-type flag gates which constraints apply. This avoids composition overhead---one proof, one FRI invocation.

=== Full Private Presentation

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Full Private Presentation =
    Authorization Proof (conclusion = ALLOW, root, accumulated_hash)
  OR Note Spending Proof (nullifier, note_tree_root)

IVC-Compressed Presentation =
    IVC Fold Chain (constant-size, covers N attenuation steps)
  + Derivation Proof (final state → ALLOW)
  + Issuer Membership Proof (issuer ∈ federation)
```
]]

The verifier of a Full Private Presentation receives only: a federation root $R_F$, a conclusion bit, and the proof(s). It learns nothing about delegation chain length, intermediate authorities, or the agent's other capabilities.

=== Receipt Chain with IVC

#align(center)[
#block(
  fill: luma(248),
  inset: 12pt,
  radius: 4pt,
)[
```
Receipt Chain (N turns) =
    N × State Transition (pre_hash → post_hash, effects_hash, cost)

IVC-Compressed Receipt Chain =
    Single constant-size proof (initial_state → final_state)
    + Nullifier non-membership proof
```
]]

Each state transition step contributes one fold to the IVC accumulator. The accumulated hash $H_N = "Poseidon2"(H_(N-1) || R_N || N)$ commits to the full history. Verification is $O(1)$: check the IVC proof, check the final state commitment, check nullifier freshness.

== Why N Proofs Instead of One

The authorization proof currently consists of N separate sub-proofs (derivation + memberships + fold + issuer) rather than a single monolithic proof. This is because:

+ *Different AIRs, different trace shapes.* The Merkle membership AIR has width 6 and depth-dependent rows. The derivation AIR has width 92 with $N$ rows. The fold AIR has width 12. Combining them into a single AIR would require a trace width of $max(6, 12, 92) = 92$ with most columns unused in most rows---wasting prover time on zero constraints.

+ *Modularity.* Each proof can be generated independently and in parallel. The Merkle proofs are embarrassingly parallel; the derivation proof depends only on the committed fact set.

+ *Incremental verification.* A verifier can reject early: if the issuer membership proof fails, it need not check the derivation.

The proofs are bound together via shared public inputs. Specifically, the derivation proof's state root $R_0$ must equal the fold chain's final root, and the fold chain's initial root must appear as a leaf in the issuer membership proof. Tampering with any binding breaks the corresponding Merkle or hash commitment.

== Path to a Single Proof

Recursive verification collapses N proofs into 1:

+ *Generate* each sub-proof (derivation, fold, memberships) independently.
+ *Recursively verify* each sub-proof inside a new STARK circuit. The recursive verifier AIR encodes Fiat-Shamir transcript replay, FRI folding checks, and constraint evaluation at queried points.
+ *Chain* the recursive proofs: the proof verifying sub-proof $k$ also verifies the recursive proof covering sub-proofs $1, ..., k-1$.
+ The final output is a single STARK proof of constant size ($tilde 24$ KiB) that transitively attests to all sub-proofs.

*Current status:* Recursive verification is implemented and working for pairs of proofs (verified via Plonky3). Arbitrary-$N$ aggregation uses sequential chaining (each step verifies the previous recursive proof). The `build_recursive_ivc_chain` function chains $N$ fold proofs into a single recursive attestation. Full composition of heterogeneous AIRs (derivation + fold + membership in one recursive proof) is designed but not yet operational.

== Soundness Analysis

=== Per-Component Security

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Component*], [*Security Parameter*], [*Bound*]),
    [BabyBear4 extension field], [$|FF_(p^4)| approx 2^(124)$], [124-bit challenge],
    [FRI proximity (50 queries, blowup 4)], [$2^(-50) dot (1/4)^(50)$], [$tilde$100-bit soundness],
    [Poseidon2 ($alpha = 7$, width 8)], [Min($|FF_p| dot d, 2^(128)$)], [$tilde$124-bit collision],
    [BLAKE3 Merkle (trace commitment)], [256-bit output], [128-bit collision],
    [Fiat-Shamir (BLAKE3 transcript)], [256-bit state], [128-bit binding],
  ),
  caption: [Security bounds for each proof system component.],
)

=== System Security

The overall system security is the minimum across all components:

$ lambda_"system" = min(lambda_"field", lambda_"FRI", lambda_"hash", lambda_"FS") approx 100 "bits" $

The FRI soundness ($tilde$100 bits with 50 queries and blowup factor 4) is the binding constraint. This is standard for STARKs at this parameter set; production deployment would increase to 80--128 queries for 128-bit security.

=== What Composition Does Not Hide

The number of sub-proofs in a non-recursive presentation leaks the _structure_ (though not the _content_) of the authorization. Specifically:
- A 3-proof presentation reveals "there was a fold chain, a derivation, and an issuer check"
- Proof sizes reveal approximate trace lengths (hence: delegation chain length, derivation depth)

Recursive composition eliminates this leakage: the final proof is constant-size and reveals only the conclusion bit. This is why recursive verification is architecturally critical---not merely a performance optimization, but a privacy requirement.

// --- 13. Proof Backend Agility -----------------------------------------------

= Proof Backend Agility

#figure(
  table(
    columns: (auto, auto, auto, auto, auto),
    align: (left, left, center, center, center),
    table.header([*Backend*], [*Field/Curve*], [*Proof Size*], [*PQ?*], [*Recursion*]),
    [BabyBear STARK], [$FF_(2^(31)-2^(27)+1)$ + FRI], [$tilde$24 KiB], [Yes], [Planned],
    [Binius], [GF(2) tower + Groestl-256], [$tilde$1--4 KiB], [Yes], [No],
    [Halo2], [BN254 / Pasta + KZG], [$tilde$1--5 KiB], [No], [Yes],
    [Nova], [Pasta cycle (Pallas/Vesta)], [$tilde$10 KiB], [No], [IVC native],
  ),
  caption: [Proof backend characteristics. All prove the same logical statement against the same data model.],
)

// --- 14. Federation Consensus ------------------------------------------------

= Federation Consensus

Federation consensus uses Morpheus @morpheus adaptive BFT. Federation blocks contain attested Merkle roots, revocation tree updates, and budget rebalancing instructions. A quorum certificate (QC) is a single aggregate BLS12-381 threshold signature---verification cost is constant regardless of committee size.

Attested roots serve as freshness anchors for offline verification. A verifier with a recent root can check any presentation without contacting the federation. There is no "call home" requirement.

// --- 15. Coordination --------------------------------------------------------

= Coordination

== Bounded Counters (Stingray)

Concurrent resource spending uses bounded counters adapted from Stingray @stingray: $"slice"(i) = "balance" dot (f+1)/(2f+1)$. Each silo debits locally up to its slice without coordination. The invariant $sum_i "spent"(i) <= "balance"$ holds even under $f$ Byzantine silos.

== Atomic Coordination (2PC)

Cross-silo turns use two-phase commit with threshold quorum certificates. Fast unlock releases locked budget immediately upon abort.

== Causal Ordering (DAG)

Non-atomic operations use a causal DAG of hash-linked events, providing partial ordering without global consensus.

// --- 16. Network Layer -------------------------------------------------------

= Network Layer

Message dissemination uses Plumtree-inspired @plumtree hybrid push over QUIC: eager push (degree 3) for spanning-tree delivery, lazy push (`IHave` notifications) for redundancy, and periodic Bloom filter anti-entropy. All inter-silo communication uses QUIC (via Quinn) with multiplexed streams and 0-RTT resumption.

// --- 17. Security Analysis ---------------------------------------------------

= Security Analysis

== Soundness

*STARK soundness*: BabyBear4 achieves $tilde$124-bit soundness via FRI proximity testing over the degree-4 extension field. *Capability confinement*: The fold AIR enforces $F_(i+1) subset.eq F_i$---a prover cannot amplify capabilities. *Replay protection*: Monotonically increasing per-cell nonces.

== Known Vulnerabilities (Honest Disclosure)

Per the security audit (May 2026): (1) Turn executor does not verify Ed25519 signatures. (2) Turn executor does not verify ZK proofs. (3) Coordinator does not check vote signatures in 2PC. (4) Wire protocol uses truncated signatures. These are missing verification calls---the cryptographic primitives are correct; integration is incomplete.

== Post-Quantum Roadmap

The STARK path is post-quantum today. Classical components have a staged migration: BLS12-381 $arrow.r$ lattice threshold (Phase 2), Ed25519 $arrow.r$ ML-DSA (Phase 3), X25519 $arrow.r$ ML-KEM (Phase 4).

// --- 18. Related Work --------------------------------------------------------

= Related Work

*Mina Protocol* @mina. Pyana's execution model (cells $equiv$ accounts, turns $equiv$ ZkappCommands, call forests) derives from Mina. The key divergence: Pyana manages authorization state with federated BFT rather than global Ouroboros, implements distributed object semantics absent from Mina, and carries state as proof chains rather than compressing a global ledger.

*seL4* @sel4. seL4's CDT is the gold standard for capability revocation: kernel-enforced, synchronous, formally verified. Pyana's CDT is the distributed dual---replacing kernel authority with cryptographic proof, synchronous traversal with bounded-staleness snapshots, and single-machine scope with cross-federation reach. The tradeoff is revocation latency for distribution.

*Cap'n Proto* @capnproto. Cap'n Proto provides the closest existing implementation of E-style promise pipelining in production. Pyana extends the model with: ZK-private authorization at each pipeline step, offline verification (no live vat needed), and proof that the pipeline was authorized without revealing the capability chain.

*Midnight* @midnight. Privacy-focused blockchain using Plonk proofs. Unlike Pyana, Midnight targets DeFi, requires chain liveness, and lacks capability delegation semantics.

*UCAN* @ucan. Correct delegation semantics (attenuation, invocation) but transparent chains. Pyana proves the same relationship without revealing intermediate authorities.

*Coconut* @coconut. Attribute-based anonymous credentials. Lacks delegation/attenuation---proves "has attribute X" rather than "can do action Y on resource Z."

*Stingray* @stingray. Bounded counters for BFT payment channels. Pyana adapts the split-balance formula directly for concurrent resource budgets across silos.

*Google Macaroons* @macaroons. HMAC-chained bearer tokens. Pyana uses macaroons as the encoding format; the contribution is proving properties of the chain in zero knowledge.

// --- 19. Current Status ------------------------------------------------------

= Current Status

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Latency*], [*Notes*]),
    [Macaroon verify (trusted)], [$tilde 8 mu s$], [HMAC-SHA256, constant-time],
    [Datalog evaluation], [$tilde 12 mu s$], [7 rules, 5 facts, bottom-up],
    [STARK proof generation], [$tilde 64 mu s$], [BabyBear4, real Poseidon2 constraints],
    [STARK verification], [$tilde 438 mu s$], [FRI proximity + Merkle check],
    [BLS threshold verify], [$tilde 32 "ms"$], [4-member committee],
    [End-to-end (wire)], [$tilde 560 "ms"$], [3-node TCP, real STARK],
    [Proof size], [24 KiB], [Single fold step],
  ),
  caption: [Measured performance on Apple M-series. Non-optimized implementation.],
)

What works today:
- All STARK proofs use real Poseidon2 constraints over BabyBear4 extension field (124-bit security)---no vacuous proofs.
- Full token-to-proof-to-turn-execution pipeline with pipeline execution and topological ordering.
- Working multi-node TCP consensus with Morpheus BFT and BLS12-381 threshold signatures.
- Browser extension wallet with intent matching, local Datalog evaluation, and STARK fulfillment proofs.
- Sealer/unsealer with X25519-ChaCha20Poly1305 for offline capability transfer.
- Promise pipelining with `EventualRef` resolution and three-party introduction routing directives.
- 20+ end-to-end demo scenarios in a unified harness covering delegation, revocation, multi-party turns, intent fulfillment, and pipeline execution.

What remains:
- Recursive proof composition uses hash-chain accumulation, not true STARK-in-STARK.
- Dual Merkle systems (BLAKE3 fast path / Poseidon2 ZK path) not yet unified.
- Gossip is one-hop; multi-hop forwarding is planned.
- RevocationChannel synchrony primitive is designed but not yet implemented.
- CDT Merkle structure exists conceptually; production encoding is in progress.

// --- 20. Conclusion ----------------------------------------------------------

= Conclusion

Pyana demonstrates that object-capability authorization is naturally structured as incrementally verifiable computation, and that this structure enables a full distributed object runtime---not merely a credential system---with zero-knowledge privacy, E-style messaging, and proof-carrying state.

The Capability Derivation Tree duality (kernel-enforced vs. proof-carried) suggests a broader principle: any security invariant maintained synchronously by a kernel can be maintained asynchronously by a proof system, trading latency for distribution. The RevocationChannel spectrum (from bearer-token impunity to kernel-like instant revocation) makes this tradeoff explicit and application-selectable.

The system is operational across 97k lines of Rust with real cryptography, working federation consensus, and a browser-to-node-to-proof pipeline. Critical gaps remain in execution-layer verification and recursive proof composition.

// --- References --------------------------------------------------------------

#heading(level: 1, numbering: none)[References]

#set text(size: 9.5pt)

#bibliography(title: none, style: "ieee", "refs.yml")
