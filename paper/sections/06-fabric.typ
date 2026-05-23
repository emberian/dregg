// =============================================================================
// Section 6: The Unified Fabric
// =============================================================================

= The Unified Fabric <sec-fabric>

== From Isolated Federations to Emergent Groups

Traditional distributed consensus systems partition the network into isolated clusters: each federation owns a separate DAG, maintains its own genesis, and communicates with others only through explicit bridges. Pyana inverts this model. A single _unified blocklace_ spans all participants; a _federation_ is merely a reference group---a named subset of strands whose blocks are ordered together by a shared $tau$ function. Groups overlap, emerge organically, and dissolve without affecting the underlying DAG structure.

The key insight: ordering is a _view_, not a partition. Two reference groups operating over the same blocklace can share members, reference each other's blocks causally, and even merge---because the DAG is universal and group membership is a filter applied at ordering time.

== Reference Groups

A `ReferenceGroup` is the primitive unit of coordination:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Field*], [*Description*]),
    [`participants: Vec<StrandId>`], [Public keys of block-producing strands],
    [`threshold: usize`], [Supermajority count for finality ($2n\/3 + 1$)],
    [`timeout_waves: u64`], [Inactivity before auto-removal],
    [`routes_commitment: Option<Hash>`], [BLAKE3 of governance DFA (if governed)],
  ),
  caption: [ReferenceGroup structure. The group ID is the BLAKE3 hash of sorted participant keys.],
)

Multiple reference groups coexist over the same underlying DAG. Blocks from non-members are invisible to the group's ordering function but remain causally reachable for cross-group references. This enables:

- *Overlapping membership*: A strand participates in multiple groups simultaneously.
- *Zero-cost migration*: Moving between groups is a metadata change, not a state export.
- *Causal cross-references*: A block in group $A$ can reference a block in group $B$ without requiring $B$'s ordering permission.

== The $tau_"unified"$ Function

The unified ordering function $tau_"unified"$ generalizes Cordial Miners to operate over an arbitrary subset of the blocklace:

$ tau_"unified"(cal(B), G, C) = "xsort"(union.big_(l in cal(L)(cal(B), G, C)) "new_past"(l)) $

where $cal(B)$ is the full blocklace, $G$ is the reference group, $C$ is the ordering configuration (wavelength), and $cal(L)$ is the set of finalized leaders computed over $G$'s blocks only.

The algorithm proceeds:

+ *Filter*: Consider only blocks whose creator is in $G."participants"$.
+ *Compute rounds*: Round assignment uses only filtered blocks (non-member predecessors do not advance rounds).
+ *Identify waves*: Partition rounds into waves of length $C."wavelength"$.
+ *Elect leaders*: Round-robin leader assignment over $G."participants"$ (sorted).
+ *Check super-ratification*: Leader $l$ is finalized if a supermajority of the wave's last-round blocks ratify $l$.
+ *Collect and sort*: For each finalized leader, collect its new causal past (excluding already-ordered blocks) and sort deterministically via `xsort` (block hash ordering).

The critical property: $tau_"unified"$ produces _exactly_ the same total order as running a standalone Cordial Miners instance over $G$'s blocks---even when those blocks are interleaved in the DAG with blocks from other groups.

== Governance Modes <sec-governance-modes>

A `GovernedReferenceGroup` wraps the ordering primitive with one of three membership management modes:

=== Constitutional (Formal Organizations)

Membership changes require supermajority vote via the H-rule: changing threshold from $T$ to $T'$ requires $max(T, T')$ votes. This is the current federation behavior---preserved for DAOs, regulated entities, and formal organizations.

- Join requires $h$-rule approval (proposal + vote blocks in DAG).
- Leave is explicit or via timeout.
- Equivocation triggers immediate auto-eviction.
- Amendment proposals have bounded lifetime.

=== Open (Permissionless Networks)

Anyone can join by producing blocks that reference group members. No vote or threshold for admission. Timeout-based cleanup removes inactive strands.

- Join: produce a block referencing any group member.
- Leave: stop producing blocks for $"timeout_waves"$ waves.
- Anti-spam: the group can set a routes commitment (DFA) to filter message types.

This mode suits public goods networks, open research collaborations, and permissionless validator sets.

=== Invite-Only (Small Teams)

Any single existing member can unilaterally add new members. No threshold vote needed. Optimized for small teams, friend groups, and rapid-formation working groups.

- Join: any member issues an invitation (a block containing the new strand's key).
- Leave: stop producing or be removed after timeout.
- No governance overhead for groups under 10 members.

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

In a unified blocklace with thousands of strands, transmitting every block to every node is prohibitive. Pyana uses _subscriptions_ to filter dissemination:

A `Subscription` declares which strands a node wants to receive:

- *Direct subscriptions*: Blocks from strands in my reference group.
- *Referenced closure*: Optionally include blocks that my subscribed strands reference (one hop of causal closure).
- *Causal depth*: Maximum hops to follow beyond direct subscriptions.

The dissemination protocol (Cordial Dissemination) respects subscriptions: a node pushes blocks only to peers whose subscription includes the block's creator. This reduces bandwidth from $O(|"strands"|)$ to $O(|"subscription"|)$ per node while preserving causal closure for ordering.

=== Subscription Semantics

For a node $n$ with subscription $S_n$ and reference group $G$:

$ "receive"(n, b) arrow.l.r.double b."creator" in S_n."subscribed_strands" or ("include_referenced" and exists b' in S_n : b in "predecessors"(b')) $

Nodes automatically subscribe to their reference group's participants. Additional subscriptions enable cross-group awareness (e.g., a relay subscribing to multiple groups for routing).

== Strand-Based Addressing

The unified fabric replaces federation-scoped addressing with strand-based addressing:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Mode*], [*Target*], [*Semantics*]),
    [`Strand(StrandId)`], [Specific block producer], [Direct messaging],
    [`Group(GroupId)`], [Any group member], [Multicast to reference group],
    [`Capability(SwissNum)`], [Swiss number holder], [Bearer-addressed],
    [`Federation(FedId)`], [Legacy backward compat], [$"FedId" equiv "GroupId"$],
  ),
  caption: [Addressing modes. FederationId is a type alias for GroupId in the unified model.],
)

The strand address is the public key of a block-producing entity. The group address is the BLAKE3 hash of the sorted participant set---deterministic and content-addressed. A message addressed to a group is delivered to any member; a message addressed to a strand reaches that specific entity.

=== Per-Group Checkpoints

Checkpoint proofs are scoped to a single reference group. A checkpoint proves: "at height $H$, the state of group $G$ was commitment $C$, and all turns up to $H$ were valid." This enables:

- *Pruning*: Discard blocklace data below the checkpoint height for this group.
- *Fast sync*: New members sync from the latest checkpoint rather than replaying history.
- *Portable proofs*: The checkpoint is independently verifiable without the full DAG.

== Intra-Fabric Migration

Since all groups share one DAG, migrating a strand between groups requires no state export:

+ The strand's blocks remain in the shared DAG (they are never deleted).
+ The source group's $tau_"unified"$ stops including the strand (if removed from membership).
+ The target group's $tau_"unified"$ starts including the strand (upon joining).
+ The strand's receipt chain and IVC proofs remain valid (they reference block hashes, not group IDs).

Migration cost: one membership change in the source group + one in the target. The strand's entire history is immediately available to the new group via the shared DAG---no state transfer protocol needed.

== Emergent Federation Properties

The unified fabric provides properties impossible with isolated federations:

*Organic growth*: A solo strand ($n = 1$) operates as its own reference group. When it finds collaborators, they form a group simply by including each other as participants. No genesis ceremony, no bootstrap coordination.

*Graceful partition*: If a group disagrees, the minority can fork---creating a new reference group with a subset of the original participants. Both groups continue operating over the shared DAG; blocks already ordered by the original group remain ordered.

*Federation as a spectrum*: The same mechanism serves a solo developer (1 strand, invite-only), a startup team (5 strands, open), a DAO (50 strands, constitutional), and a public network (1000+ strands, open with DFA governance). No separate code paths---only configuration of the reference group.

== Federation Privacy <sec-federation-privacy>

Validators in a reference group currently see all turn content in cleartext. The target architecture provides layered privacy:

*Layer 1 (Conflict Set Ordering):* Bloom filter conflict sets enable ordering without content. A lightweight STARK proves nonce correctness and fee sufficiency. The group orders and detects conflicts without seeing turn bodies.

*Layer 2 (Threshold Decryption):* Turn bodies are encrypted to a group threshold key. Decrypted AFTER ordering is finalized. Protects against MEV and front-running.

*Layer 3 (Full Validity Proof):* Full STARK proving conservation and authorization eliminates decryption entirely. Agents generate proofs; the group only verifies.

The recommended medium-term approach is validium-style blind ordering: agents submit encrypted turns alongside STARK proofs of valid state transition. Validators see nullifiers and proofs but not turn content or state.

== Security Properties

*Safety*: $tau_"unified"$ inherits Cordial Miners safety. For a reference group with threshold $t$, safety holds if fewer than $t$ members are Byzantine.

*Liveness*: Under partial synchrony, if more than $t$ members are honest and eventually connected, every submitted turn is eventually ordered.

*Group isolation*: Faults in one reference group cannot affect ordering in another (they share DAG structure but not ordering computation).

*Equivocation detection*: Structural---two blocks by the same author at the same round with different content constitute irrefutable proof of Byzantine behavior, visible to all DAG participants regardless of group membership.
