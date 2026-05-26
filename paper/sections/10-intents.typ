// =============================================================================
// Section 10: Intent Engine
// =============================================================================

= Intent Engine <sec-intents>

== From Matching to Solving

Traditional order books match pairs: buyer meets seller. Dragon's Egg's intent engine generalizes this to _constraint satisfaction over arbitrary capability exchanges_. An intent declares what a cell wants and what it offers; the solver finds valid combinations---including multi-party ring trades where no bilateral match exists.

== Intent Structure

An intent is a declarative specification:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Field*], [*Description*]),
    [`intent_id: IntentId`], [Content-addressed hash of the intent body],
    [`creator: CommitmentId`], [Anonymous creator (Pedersen commitment to identity)],
    [`offer: AssetSpec`], [What the creator offers (type + amount)],
    [`want: AssetSpec`], [What the creator wants (type + minimum amount)],
    [`constraints: Vec<Predicate>`], [Additional conditions (rate bounds, TTL, etc.)],
    [`expiry: u64`], [Block height after which the intent expires],
    [`priority_tip: u64`], [Additional computrons for eager gossip propagation],
  ),
  caption: [Intent structure. The creator field is a commitment, not an identity---privacy by default.],
)

=== Asset Types (Generalized 5-Type Model)

The solver operates over 5 item types that cover the full range of exchangeable resources:

+ *Fungible tokens*: Computrons, stablecoins, LP tokens (divisible, interchangeable).
+ *Non-fungible tokens*: Unique identifiers (NFTs, cell IDs, credential hashes).
+ *Capabilities*: Attenuated bearer tokens (service access, compute budgets).
+ *Compute*: CPU/GPU time commitments (inference slots, proof generation).
+ *Data*: Content-addressed blobs (models, datasets, query results).

Each type has a well-defined equality relation and ordering (for rate comparison). The solver treats all 5 types uniformly via the `AssetSpec` abstraction.

== Ring Trade Solver

=== Motivation

Bilateral matching fails when no pairwise match exists but a cycle does:

- Alice has token $A$, wants token $B$.
- Bob has token $B$, wants token $C$.
- Carol has token $C$, wants token $A$.

No pair can trade---but the triple $(A -> B -> C -> A)$ satisfies all three. The ring trade solver finds such cycles.

=== Algorithm

The solver constructs a directed compatibility graph $G = (V, E)$ where:

- Each vertex $v in V$ is an active intent.
- An edge $(u, v)$ exists if $u$'s offer satisfies $v$'s want (type match + amount $>=$ minimum).
- Edge weights encode surplus (how much $u$'s offer exceeds $v$'s minimum want).

Ring trades are elementary circuits in $G$. The solver uses Johnson's algorithm (1975) bounded to maximum cycle length $k$ (default $k = 5$):

+ Construct the compatibility graph from active intents.
+ Find all elementary circuits of length $<= k$ via Johnson's algorithm with Tarjan's SCC optimization.
+ Score each circuit by combined surplus (total excess value across all edges).
+ Select the highest-scoring non-conflicting set of circuits (greedy by score, rejecting circuits that share intents with already-selected ones).

=== Complexity

Johnson's algorithm runs in $O((|V| + |E|)(c + 1))$ where $c$ is the number of circuits found. With the cycle length bound $k$, the practical complexity is $O(|V|^k)$ in the worst case. For $|V| = 256$ (max batch size) and $k = 5$: $approx 10^(12)$ operations worst-case, but SCC decomposition and early pruning reduce this to sub-second in practice.

=== Settlement

A ring trade settlement produces a set of atomic transfers:

$ cal(S) = {(v_i, v_((i+1) mod n), a_i, q_i) : i in {0, ..., n-1}} $

where $v_i$ is the $i$-th participant, $a_i$ is the asset type, and $q_i$ is the quantity. Settlement is atomic: all transfers execute or none do (via compound turn).

== Trustless 7-Layer Protocol (production-wired)

The trustless intent engine provides verifiably fair solving without any trusted executor. The threshold-encryption substrate is *real* (`federation::threshold_decrypt`---Shamir over GF(256) + ChaCha20-Poly1305 AEAD) and *production-wired* (`node::state::trustless_intent_engine`). The earlier `set_decrypted_intents` cleartext side-channel is replaced; validators now contribute real decryption shares and `combine_shares` produces the cleartext intents.

=== Layer 1: SUBMIT

Intents are encrypted to the federation's threshold public key (`ThresholdCiphertext` in `federation::threshold_decrypt`). Encrypted intents are broadcast via gossip. No party---including gossip relays---can read intent content before the collective decryption ceremony.

=== Layer 2: BATCH

Batch boundaries are determined by consensus (blocklace finality). A batch closes when either:
- $"DEFAULT_BATCH_INTERVAL"$ waves pass (default: 10 waves), or
- $"MAX_INTENTS_PER_BATCH"$ encrypted intents accumulate (default: 256).

The batch boundary is a consensus decision---no party can manipulate which intents enter a batch.

=== Layer 3: DECRYPT (real Shamir + ChaCha20-Poly1305)

After a batch boundary is finalized, the threshold decryption ceremony begins:

+ Each validator contributes a `DecryptionShare` (Shamir share of the AEAD symmetric key over GF(256)).
+ The `node::state::trustless_intent_engine::contribute_decrypt_share` accumulates shares per `ThresholdCiphertext`.
+ At $t = "decrypt_threshold"$ shares (typically $2f + 1$), `federation::threshold_decrypt::combine_shares` reconstructs the AEAD key and decrypts the ciphertext via ChaCha20-Poly1305.
+ The cleartext `Vec<Intent>` flows into the solver auction.

The critical property: intents are revealed *after* the batch is sealed; no party can see an intent and then submit a competing intent into the same batch (front-running prevention). The Silver Vision integration loop: the production node path actually invokes the threshold-decryption primitive, rather than calling a cleartext `set_decrypted_intents` side-channel. `intent::trustless::DecryptionShare` is now isomorphic to `federation::threshold_decrypt::DecryptionShare` (canonical share type re-exported, per the integration commits).

=== Layer 4: SOLVE

Open solver competition begins. Any party can compute solutions over the decrypted batch:

- Individual solvers run their own algorithms (ring trades, bilateral matching, combinatorial optimization).
- Solvers post their solutions alongside a bond ($>= "DEFAULT_MIN_SOLVER_BOND"$, default 1000 computrons).
- Maximum solver submissions per round: $"MAX_SOLVER_SUBMISSIONS"$ (default: 32).

Competition ensures no single solver can extract MEV---the best public solution wins.

=== Layer 5: PROVE

Each submitted solution must include a STARK proof of validity:

*Statement*: "This set of settlements satisfies all intent constraints: each participant receives at least their minimum want, each participant spends at most their offered amount, no intent is double-satisfied, and all rate bounds are respected."

The proof is generated using the Effect VM's compose operators: each settlement is a sub-proof (authority + transfer), composed via `compose_aggregate`.

=== Layer 6: SELECT

The winning solution is selected by deterministic scoring:

$ "score"(S) = sum_((i,j,a,q) in S) q times "price_oracle"(a) $

The highest-scoring provably-valid solution wins. A challenge window ($"DEFAULT_CHALLENGE_WINDOW"$ waves, default 5) allows any party to dispute:

- Submit a higher-scoring valid solution (with proof). If accepted: challenger's solution replaces winner; original solver's bond returned.
- Submit a proof of invalidity. If accepted: solver's bond slashed, solution rejected, next-best selected.

=== Layer 7: SETTLE

The winning solution generates a single compound turn:

+ All transfers are bundled into one atomic turn (call forest).
+ The turn is submitted to the blocklace for ordering.
+ On commit: all settlements execute atomically.
+ On failure: all settlements revert; solver's bond is slashed.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Property*], [*Mechanism*], [*Comparison*]),
    [Front-running prevention], [Threshold encryption], [Anoma: visible to solvers],
    [Fair batching], [Consensus-determined boundary], [CoW: trusted solver],
    [Solution validity], [STARK proof], [Flashbots: SGX enclave],
    [MEV extraction], [Open competition + challenge], [MEV-Share: proposer auction],
    [Atomicity], [Compound turn], [Serai: cross-chain atomic],
  ),
  caption: [Trustless protocol comparison. Dragon's Egg replaces hardware trust (SGX), reputation (CoW), and visibility (Anoma) with cryptographic proofs.],
)

== Partial Fills and Residuals

When an intent is partially satisfied (e.g., a ring trade uses 60% of the offered amount), the remaining 40% generates a _residual intent_---a new intent for the unsatisfied portion. Residuals enter the next batch automatically, with the original intent's priority and TTL inherited.

== Privacy Properties

- *Creator anonymity*: the `CommitmentId` is a Pedersen commitment. No party learns the creator's identity until fulfillment (and even then, only the fulfiller learns it via the commit-reveal protocol).
- *Intent content privacy*: encrypted until batch closure (via real Shamir-over-GF(256) + ChaCha20-Poly1305 threshold decryption in `federation::threshold_decrypt`). No front-running possible.
- *Fulfillment privacy*: the STARK proof demonstrates satisfaction without revealing which specific capabilities the fulfiller holds.
- *Bond escrow*: solver bonds are held in escrow via the standard escrow primitive; slashing is enforced at spend-time via encumbrance.

The boundary contract (per BOUNDARIES.md §2.12 + §4.10):

- *Cleartext-inside (intent body)*: whoever can decrypt the intent's seal, or after threshold ceremony, the entire federation committee.
- *Cleartext-inside (intent match)*: the two cipherclerks that locally evaluated the Datalog and matched.
- *Commitment-inside*: gossip network (sees intent bodies post-decrypt, SSE keyword tokens, stake nullifiers).
- *Acceptance-inside*: STARK validity verifier; predicate-attestation verifier.

The boundary the trustless engine *delivers* with real threshold decryption:

- Pending intent: nobody learns the `MatchSpec` (threshold-encrypted).
- Sealed intent: only the matched pair learns the bilateral commitment.
- Once decrypted: the entire federation sees the intent body (committee cleartext-inside post-decrypt is unavoidable for solver competition).
- Settlement: the standard Turn/Receipt pipeline; observer sees commitments and atomic effects.

