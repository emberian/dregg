// =============================================================================
// Section 6: The Unified Fabric
// =============================================================================

= The Unified Fabric <sec-fabric>

== From Four Federations to One

Pre-Lane-D, the codebase carried *four* disjoint "federation" concepts:

+ A `FederationCommittee` (the BLS-aggregated committee in `federation/src/threshold.rs`).
+ A `FederationMode { Full, Solo }` runtime flag.
+ An opaque `federation_id: [u8; 16]` random tag (`node/src/genesis.rs`).
+ A Morpheus BFT-simulator harness (`node::Federation`) preserved only because some tests still imported it.

`AUDIT-federation.md` named this seam: $"federation_id"$ was conventional (not algebraic); the `committee_pubkeys` and `federation_id` were not joined; a `FederationReceipt::verify` call accepted a `committee` parameter and never checked `committee` $arrow.l.r$ `federation_id`. An attacker who could route a receipt could mislabel its `federation_id` and the algebra would not notice.

The unified `Federation` type collapses the four into one canonical object:

```rust
pub struct Federation {
    members: Vec<PublicKey>,            // sorted; substrate of federation_id
    bls_committee: Option<FederationCommittee>,
    epoch: u64,                          // part of federation_id preimage
    threshold: u32,
    id: FederationId,                    // = BLAKE3(sorted(members) || epoch)
    blocklace: Arc<Blocklace>,
    local_seat: Option<LocalSeat>,
}
```

The Morpheus simulator harness is dead code (per `AUDIT-morpheus-federation-blocklace.md`); the runtime `FederationMode` flag is a quorum-arithmetic special case (Solo = committee of one, threshold = 1); the random tag becomes a commitment. See @sec-federation for the full type and the five properties that follow from the unified definition.

== `federation_id` as Commitment

$ "federation_id" = "BLAKE3"("dregg-fed-id-v1" || "sorted_members" || "epoch") $

Two federations with the same committee at the same epoch *are the same federation*. Membership rotation produces a new `epoch`, which produces a new `federation_id`. Blocklace continuity across epochs gives the federation its identity-over-time; the `federation_id` itself is per-epoch.

== `AttestedRoot` v3

The attested-root structure binds federation context into the signed message:

```rust
pub struct AttestedRoot {
    pub federation_id: FederationId,        // bound in signing_message
    pub blocklace_block_id: BlockId,        // bound in signing_message
    pub finality_round: u64,                // bound in signing_message
    pub merkle_root: Hash,
    pub height: u64,
    pub timestamp: u64,
    pub threshold_qc: ThresholdQC,
}
```

The signing message includes `federation_id || blocklace_block_id || finality_round || merkle_root || height || timestamp`. This closes prior gaps F1 (random `federation_id`), F3 (`AttestedRoot.blocklace_block_id` missing), and F4 (`committee_epoch` decorative) from the federation audit. The bridge `destination_federation` PI field is now both surfaced *and algebraically bound* in the AIR (closes threat T6 from the executor-honesty audit and `AUDIT-nullifiers.md §5`).

== `KnownFederations` Registry

Each node persists a `KnownFederations` registry at `<data-dir>/known_federations/<federation_id>.json`, listing every federation the node is willing to verify receipts and attestations from. Each entry carries:

```rust
pub struct KnownFederationEntry {
    pub federation_id: FederationId,
    pub committee_members: Vec<PublicKey>,
    pub committee_epoch: u64,
    pub bls_verifier_key: Option<Vec<u8>>,
    pub added_at: SystemTime,
    pub trust_origin: TrustOrigin,           // OperatorAdded | BootstrappedFromPeer | ...
}
```

The `dregg register-federation` CLI subcommand atomically adds an entry. `CapTpState::sync_known_federations` keeps the in-memory CapTP routing table consistent with the on-disk registry on every startup and on every registry change.

This registry is the trust root for cross-federation operations. A receiver of a CapTP-delivered Turn at federation $F_2$ that claims to originate from federation $F_1$ checks: (a) the Turn's `federation_id` matches an entry in $F_2$'s known-federations registry; (b) the introducer's signature on the handoff certificate verifies under the public key listed in that entry; (c) the `AttestedRoot` carries a `ThresholdQC` that verifies under $F_1$'s committee key. No entry in `known_federations` $arrow.r.double$ no acceptance. This closes `AUDIT-distributed-semantics.md` GAP-3 (the wire layer formerly accepted `introducer_pk` from the wire message and trusted it).

== Reference Groups: The Coordination Substrate

A reference group is a named subset of strands in the blocklace whose blocks are ordered together by a shared $tau$ function. Groups overlap, emerge organically, and dissolve without affecting the underlying DAG.

```rust
pub struct ReferenceGroup {
    pub participants: Vec<StrandId>,
    pub threshold: usize,                    // 2n/3 + 1 supermajority
    pub timeout_waves: u64,
    pub routes_commitment: Option<Hash>,     // BLAKE3 of governance DFA
}
```

Multiple reference groups coexist over the same underlying DAG. Blocks from non-members are invisible to the group's ordering function but remain causally reachable for cross-group references. This enables overlapping membership (a strand participates in multiple groups), zero-cost migration (moving between groups is metadata, not state export), and causal cross-references.

== The $tau_"unified"$ Function

$ tau_"unified"(cal(B), G, C) = "xsort"(union.big_(l in cal(L)(cal(B), G, C)) "new_past"(l)) $

where $cal(B)$ is the full blocklace, $G$ is the reference group, $C$ is the ordering configuration (wavelength), and $cal(L)$ is the set of finalized leaders computed over $G$'s blocks only. The algorithm proceeds: filter to $G$'s participants, compute rounds, identify waves, elect leaders (round-robin), check super-ratification, collect and `xsort` (block-hash ordering). Produces *exactly* the same total order as a standalone Cordial Miners instance over $G$'s blocks.

== Governance Modes <sec-governance-modes>

A `GovernedReferenceGroup` wraps the ordering primitive with one of three membership management modes:

=== Constitutional (Formal Organizations)

Membership changes require supermajority vote via the H-rule: changing threshold from $T$ to $T'$ requires $max(T, T')$ votes. Suited to DAOs, regulated entities, formal organizations.

=== Open (Permissionless Networks)

Anyone can join by producing blocks that reference group members. No vote or threshold for admission. Timeout-based cleanup. Suited to public goods networks, open research collaborations.

=== Invite-Only (Small Teams)

Any single existing member can unilaterally add new members. Optimized for small teams, friend groups, rapid-formation working groups.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, center, center, left),
    table.header([*Mode*], [*Join Cost*], [*Threshold*], [*Use Case*]),
    [Constitutional], [Proposal + vote], [$2n\/3 + 1$], [DAOs, regulated entities],
    [Open], [Reference a member], [None], [Public networks, research],
    [Invite-Only], [One member invites], [None], [Teams, friend groups],
  ),
  caption: [Governance modes. All three share the same $tau_"unified"$ ordering---governance affects only membership management.],
)

== Interest-Based Dissemination

In a unified blocklace with many strands, transmitting every block to every node is prohibitive. Dragon's Egg uses _subscriptions_ to filter dissemination. A `Subscription` declares which strands a node wants to receive (direct subscriptions, referenced closure, causal depth). The dissemination protocol (Cordial Dissemination) respects subscriptions: a node pushes blocks only to peers whose subscription includes the block's creator. Bandwidth drops from $O(|"strands"|)$ to $O(|"subscription"|)$ per node while preserving causal closure for ordering.

== Strand-Based Addressing

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Mode*], [*Target*], [*Semantics*]),
    [`Strand(StrandId)`], [Specific block producer], [Direct messaging],
    [`Group(GroupId)`], [Any group member], [Multicast to reference group],
    [`Capability(SwissNum)`], [Swiss number holder], [Bearer-addressed],
    [`Federation(FederationId)`], [Federation-by-commitment], [`FederationId = BLAKE3(committee || epoch)`],
  ),
  caption: [Addressing modes. `FederationId` is now a *commitment* to the committee, not a random tag.],
)

== Per-Federation Checkpoints

Checkpoint proofs are scoped to a single federation. A checkpoint proves: "at height $H$, the state of federation $F$ was commitment $C$, and all turns up to $H$ were valid." This enables pruning (discard blocklace data below the checkpoint), fast sync (new members sync from the latest checkpoint), and portable proofs (independently verifiable without the full DAG).

== Federation-Bypass: `peer_exchange` <sec-fabric-peer-exchange>

Two sovereign cells can exchange signed state transitions directly, without ever touching consensus. See @sec-peer-exchange for the type definition and the boundary contract. The fabric implications:

- *Partition tolerance*: cells operate during federation unreachability and reconcile on reconnect.
- *Strongest sovereign boundary*: the federation learns nothing about the transitions unless one party publishes; observers are out-of-band by default.
- *Federation divergence*: if Alice and Bob both hold federation-tracked sovereign-cell identities, the federation's view of their commitments diverges from the peer-exchange chain head until publication.

The optional `transition_proof: Option<Vec<u8>>` carries actual transition validity through the same `EffectVmAir` the federation would have used. On publication, the federation-side executor verifies the proof against the proof-carrying-turn validation path---the algebra is identical.

== Intra-Fabric Migration

Since all groups share one DAG, migrating a strand between groups requires no state export:

+ The strand's blocks remain in the shared DAG.
+ The source group's $tau_"unified"$ stops including the strand (if removed from membership).
+ The target group's $tau_"unified"$ starts including the strand (upon joining).
+ The strand's receipt chain and IVC proofs remain valid (they reference block hashes, not group IDs).

Migration cost: one membership change in the source group + one in the target.

== Emergent Federation Properties

The unified fabric provides properties impossible with isolated federations:

*Organic growth*: a solo strand ($n = 1$) operates as its own federation. When it finds collaborators, they form a group simply by including each other as participants. No genesis ceremony, no bootstrap coordination.

*Graceful partition*: if a group disagrees, the minority can fork---creating a new reference group with a subset of the original participants. Both groups continue operating over the shared DAG; blocks already ordered remain ordered.

*Federation as a spectrum*: the same mechanism serves a solo developer (1 strand, invite-only), a startup team (5 strands, open), a DAO (50 strands, constitutional), and a public network (1000+ strands, open with DFA governance). No separate code paths---only configuration of the reference group.

== Federation Privacy

Validators in a federation currently see all turn content in cleartext. The target architecture provides layered privacy via the threshold-decryption substrate already real in `federation::threshold_decrypt` (Shamir over GF(256) + ChaCha20-Poly1305); see @sec-federation-privacy.

== Blocklace and Consensus

The blocklace is the substrate over which committee members produce blocks. Each block is Ed25519-signed, content-addressed by BLAKE3, and carries a monotonic per-creator `seq`. Equivocation is detected at receive time (`finality.rs::detect_equivocation`: same `(creator, seq)`, different content) and in `tau` (`ordering.rs::has_equivocation_in_past`: same `(creator, round)`, two distinct blocks). The two predicates differ slightly---a Byzantine node can monotonically bump `seq` across forks while producing two blocks at the same round; unifying the equivocation rule is `AUDIT-blocklace-consensus.md` open question B.

Constitutional auto-eviction at `constitution.rs::auto_evict_equivocator` consumes the finality-layer flavour of proof. The constitution maintains the H-rule for governance amendments (changing threshold from $T$ to $T'$ requires $max(T, T')$ votes).

== Security Properties

*Safety*: $tau_"unified"$ inherits Cordial Miners safety. For a reference group with threshold $t$, safety holds if fewer than $t$ members are Byzantine.

*Liveness*: under partial synchrony, if more than $t$ members are honest and eventually connected, every submitted turn is eventually ordered.

*Group isolation*: faults in one reference group cannot affect ordering in another.

*Equivocation detection*: structural---two blocks by the same author at the same round (or same `seq`) with different content constitute irrefutable proof of Byzantine behavior.

*Federation-identity binding*: $"federation_id" = "BLAKE3"("committee" || "epoch")$ makes the binding *algebraic*. A receipt mislabeled with the wrong `federation_id` is detected by any verifier that holds the committee key.
