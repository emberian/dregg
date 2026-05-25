// =============================================================================
// Section 2: System Model
// =============================================================================

= System Model

== Cells as Fabric Objects

A _cell_ is the fundamental unit of isolated state in a shared fabric, analogous to an E object or a Mina zkApp account. Cells live within a federation's ledger (or sovereign, outside it); they interact with other cells via capability-mediated messaging that the executor (for hosted-cell turns) or the cell owner directly (for sovereign cells) lowers into atomic Turns. Each cell holds:

- A content-addressed identity $"CellId" in {0,1}^(256)$, derived from $"BLAKE3"("pyana-cell-id-v1" || "owner_pubkey" || "factory_vk" || "genesis_nonce")$.
- Mutable state: a $"STATE_SLOTS"$-wide array of field elements $s_0, ..., s_(n-1) in FF_p$ where $p = 2^(31) - 2^(27) + 1$ (BabyBear prime).
- A _capability list_ (c-list): the set of capabilities the cell may exercise.
- A _cell program_ declaring the cell's slot schema (`FieldVisibility` per slot), its `state_constraints`, and any operation-scoped transition rules.
- An owning Ed25519 signing key (for sovereign-witness signature and for `peer_exchange`-style direct exchange).
- An optional verification key for ZK proof validation.

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

=== The Sovereignty Spectrum

Cells operate at one of three sovereignty levels, forming a spectrum from full autonomy to full replication:

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Level*], [*State Storage*], [*Proof Requirement*], [*Trust Model*]),
    [Sovereign], [Owner holds full state; federation persists only 32-byte commitment], [Cell proves own transitions via STARK *or* presents `SovereignCellWitness`], [None (proof path) or executor-trusted-during-turn (witness path)],
    [Delegated], [Owner holds state; executor generates proofs on behalf], [Executor proves; client verifies before submission], [Executor sees witness],
    [Hosted], [Federation stores full state], [Federation verifies turns directly], [Federation cleartext-inside],
  ),
  caption: [Sovereignty spectrum. Cells move between levels dynamically. The two paths within "sovereign" (proof-carrying and witness-injection) carry different boundary contracts---see @sec-sovereign-paths.],
)

Sovereign cells prove their own state transitions either via a STARK whose AIR binds `OLD_COMMIT == sovereign_commitments[cell_id]` (the proof-carrying path; executor never sees cleartext) or by presenting a `SovereignCellWitness` carrying `(cell_state, state_proof, signature, sequence, transition_proof: Option<Vec<u8>>)`---the witness path, where the executor reads cleartext for the duration of the turn but the federation persists only the post-commitment. The witness path is the integration-complete default in Silver; Phase 1 sovereign-witness AIR teeth (`WITNESS_KEY_COMMIT` column + `SOVEREIGN_WITNESS_KEY_COMMIT` PI + `IS_SOVEREIGN_CELL` PI gate) bind the witness's signing identity to the cell's owning key inside the AIR; Phase 2 recurses into the optional `transition_proof` via Lane Golden-Edge's recursive verifier.

A cell transitions between levels at any time:
- *Sovereign $arrow.r$ hosted*: Submit current state to the federation.
- *Hosted $arrow.r$ sovereign*: Prove state ownership and extract a commitment.
- *Sovereign $arrow.r$ delegated*: Grant an attenuated execution capability to an executor.

=== Faceted Capabilities and EffectMask

Each capability carries an _EffectMask_---a 32-bit bitmask of permitted effects (set field, transfer, grant capability, revoke, emit event, create cell, seal, bridge, introduce, enqueue, dequeue, etc.). Delegation can only _narrow_ the mask (bitwise AND with the parent's mask), enforcing monotonic attenuation at the effect level:

$ "EffectMask"_"child" = "EffectMask"_"parent" and "mask"_"delegation" $

The narrowing invariant is enforced by the runtime (for trusted-mode evaluation) and provable in zero knowledge (for STARK presentations). Faceted capabilities additionally carry `FacetConstraint`s (`MaxTransferAmount`, `AllowedTargets`, `RateLimit`, `Budget`) and may carry an unbounded number of `CapabilityCaveat::Witnessed(WitnessedPredicate)` for app-defined attenuation, with the `is_facet_attenuation` check ensuring child capabilities tighten parents per-variant.

=== Bearer Capabilities

Pyana also supports _bearer capabilities_: tokens that grant authority immediately upon presentation, without requiring storage in the recipient's c-list. A bearer capability carries a `BearerCapProof`---either a signed Ed25519 delegation chain or a STARK proof of delegation validity. Bearer capabilities follow E-semantics for immediate grants: useful for one-shot authorizations, tickets, ephemeral access tokens, and the swiss-number-bearing sturdy ref used for CapTP enlivenment.

== Turns on Strands

A _turn_ is an atomic transaction over one or more cells, executed on a _strand_---a single block-producing entity in the blocklace. A turn contains:

- A _call forest_: an ordered list of actions, executed in sequence.
- A fee (in computrons) covering execution cost.
- A nonce (monotonically increasing per actor cell) for replay protection.
- Authorization: one of the modes `Signature`, `Proof`, `Breadstuff`, `Bearer`, `CapTpDelivered`, or the new `Custom { predicate: WitnessedPredicate, descriptor: AuthModeDescriptor }`.
- Optional `sovereign_witnesses` (one per sovereign cell touched).
- Optional `execution_proof` (proof-carrying path) or `transition_proof` (cross-fed bridge).
- Optional `custom_program_proofs` (one per `Effect::Custom` dispatch).

If any action in the call forest fails, all effects are rolled back via journal replay---atomicity. State threading between effects within a turn uses Poseidon2 commitments: each effect's post-state hash becomes the next effect's pre-state hash, enforced algebraically in the Effect VM trace.

=== Canonical signing message

The actor signs a domain-separated canonical message `pyana-turn-v3:` $||$ canonical body. The body includes `federation_id`, `actor_cell_id`, `actor_nonce`, the ordered effects list (with `effects_hash` algebraically derived), `previous_receipt_hash`, the `sovereign_witnesses` list, `execution_proof` reference, `custom_program_proofs` references, and any `conservation_proof` reference. Including `federation_id` in the signing message closes threat T6 (cross-federation replay); including `previous_receipt_hash` closes T8 (fake chain links); the full v3 body shape is verified by `pyana-verifier` during chain replay.

== The Unified `Federation` <sec-federation>

A *federation* is a *committee of nodes* that (a) collectively run a blocklace, (b) attest shared ledger roots via BLS threshold signatures over a domain-separated message, and (c) ratify each other's Turns through a quorum certificate over a `FederationReceiptBody`. This definition collapses the four prior disjoint concepts (`FederationCommittee`, `FederationMode`, opaque `federation_id`, the Morpheus simulator harness) into one canonical type:

```rust
pub struct Federation {
    members: Vec<PublicKey>,            // sorted; substrate of federation_id
    bls_committee: Option<FederationCommittee>,
    epoch: u64,                          // part of federation_id preimage
    threshold: u32,
    id: FederationId,                    // cached = H(sorted(members) || epoch)
    blocklace: Arc<Blocklace>,
    local_seat: Option<LocalSeat>,
}
```

Five things follow:

+ *A federation is identified by its committee*, not by a random tag. $"federation_id" = "BLAKE3"("pyana-fed-id-v1" || "sorted_members" || "epoch")$ is a commitment, not a name. Two federations with the same committee at the same epoch *are the same federation*. This closes threat F1 from the federation audit (the prior random-16-byte `federation_id` was conventional, not algebraic).
+ *A federation has exactly one mode of operation: committee BFT.* The prior `FederationMode { Full, Solo }` flag is a quorum-arithmetic special case ("Solo" = committee of one, threshold = 1), not a runtime mode.
+ *A federation owns a blocklace.* The blocklace is the substrate over which committee members produce blocks; the federation's `committee` is the set of `StrandId`s authorized to write to that blocklace.
+ *A federation produces two kinds of receipt:* a `TurnReceipt` (per turn, by the local executor, federation-tagged via `federation_id` in the receipt hash), and an optional `FederationReceipt` (committee-attested via `ThresholdQC`; the cross-federation hand-off currency).
+ *A federation rotates.* Membership changes (`join`, `leave`, expel) produce a new `epoch`, which produces a new `federation_id`. Blocklace continuity across epochs gives the federation its identity-over-time; the `federation_id` itself is per-epoch.

=== `KnownFederations` registry

Each node persists a `KnownFederations` registry at `<data-dir>/known_federations/<federation_id>.json`, listing every federation the node is willing to verify receipts and attestations from. Entries carry the committee descriptor, the committee epoch, the BLS verifier key, and trust metadata (when the entry was added, by whom). The `pyana register-federation` CLI subcommand atomically adds an entry; `CapTpState::sync_known_federations` keeps the in-memory CapTP routing table consistent with the on-disk registry.

This registry is the trust root for cross-federation operations. A receiver of a CapTP-delivered Turn at federation $F_2$ that claims to originate from federation $F_1$ checks (a) the Turn's `federation_id` matches an entry in $F_2$'s known-federations registry, (b) the introducer's signature on the handoff certificate verifies under the public key listed in that entry, (c) the `AttestedRoot` accompanying the cross-fed delivery carries a `ThresholdQC` that verifies under $F_1$'s committee. No entry in `known_federations` $arrow.r.double$ no acceptance.

=== `AttestedRoot` v3

The attested-root structure binds the federation context into the signed message:

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

The signing message includes `federation_id || blocklace_block_id || finality_round || merkle_root || height || timestamp`---closing the prior gap where `signing_message` carried only `merkle_root || height || timestamp` and the binding-to-federation was the verifier's responsibility (F1/F3/F4 in the federation audit, addressed by the unification).

== Federation Bypass: `peer_exchange` <sec-peer-exchange>

Two sovereign cells (Alice and Bob) can directly exchange signed state transitions without ever touching consensus. The `PeerStateTransition` carries:

```rust
pub struct PeerStateTransition {
    pub cell_id: CellId,
    pub old_commitment: [u8; 32],
    pub new_commitment: [u8; 32],
    pub effects_hash: [u8; 32],
    pub timestamp: u64,
    pub sequence: u64,                       // monotonic per peer-pair
    pub signature: [u8; 64],                  // Ed25519 over (old, new, effects_hash, ts, seq)
    pub transition_proof: Option<Vec<u8>>,    // optional STARK via EffectVmAir
}
```

The two peers each hold the other's known public key, the chained `(old_commitment, new_commitment)`, the monotonic `sequence`, the timestamp, and optionally the STARK `transition_proof`. The signature is verified with `verify_strict` over a domain-separated message; replay is rejected by the monotonic sequence; the optional STARK (feature-gated `zkvm`) carries actual transition validity through the same `EffectVmAir` the federation would have used.

This is the partition-tolerant escape hatch: if the federation is unreachable, two cells can continue to do business directly, accumulating signed transitions in a local chain. On reconnect, either side may publish the accumulated chain to its federation as a sovereign turn (with the `transition_proof` carrying validity), promoting the bilateral peer-exchange to federation-attested order. Both cells must publish for cross-cell observers to see the chain; otherwise the federation's view of either cell's commitment diverges from the peer-exchange chain head until publication.

`peer_exchange` is the *strongest* sovereign-cell boundary in the codebase. The federation learns nothing about the transitions unless one party publishes; the audit population is exactly Alice and Bob (cleartext-inside) plus anyone they choose to share the chain with (commitment-inside without proof; acceptance-inside with proof).

== Reference Groups and Coordination Substrate

A reference group is a named subset of strands in the unified blocklace whose blocks are ordered together by a shared $tau$ function. After the federation unification, the reference group is one of three coordination substrates:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Substrate*], [*Coordination cost*], [*Use case*]),
    [Sovereign / `peer_exchange`], [Pairwise signature only], [Partition-tolerant bilateral],
    [Stingray bounded counter], [Local debit, periodic rebalance], [Concurrent budget channels],
    [Cordial Miners $tau$ + Constitutional Consensus], [Full BFT], [Committed ordering],
  ),
  caption: [Three coordination tiers. Agents escalate only when needed.],
)

The federation's role is deliberately minimal: ordering, nullifier deduplication, attested-root anchoring, and discovery. It is NOT an execution layer for sovereign cells---verification only. Sovereign cells (proof-carrying path) prove their own state transitions; the federation merely attests that proofs were valid at a given height.

=== Governance modes

A `GovernedReferenceGroup` wraps the ordering primitive with one of three membership management modes:

- *Constitutional*: membership changes require the H-rule (supermajority vote across H members' blocks). Suited to DAOs, regulated entities, formal organizations.
- *Open*: anyone can join by producing blocks that reference group members. Timeout-based cleanup. Suited to public goods networks.
- *Invite-Only*: any single existing member can unilaterally add new members. Suited to small teams.

All three share $tau$ ordering; governance affects only membership management.

== EROS-Style Factories <sec-factories>

A _factory_ is a cell program that constrains what new cells it can create. Inspired by EROS's constructor transparency @eros, a factory publishes a `FactoryDescriptor` that is the complete constructor contract---anyone can inspect exactly what capabilities the factory grants to its creations, what verification keys they will use, and what initial state they receive:

```rust
pub struct FactoryDescriptor {
    pub factory_vk: [u8; 32],                  // BLAKE3 of the descriptor
    pub child_program_vk: Option<[u8; 32]>,    // the cell program every child runs
    pub child_vk_strategy: ChildVkStrategy,
    pub initial_slot_layout: Vec<SlotInit>,
    pub state_constraints: Vec<StateConstraint>,
    pub initial_capabilities: Vec<CapabilityTemplate>,
    pub allowed_effects: EffectMask,
}
```

Factory-created cells have _computable child verification keys_:

- *Fixed*: every child uses the same VK (the factory's own).
- *Derived*: $"child_vk" = "BLAKE3"("pyana-derived-child-vk" || "factory_vk" || "param_hash")$.
- *FromSet*: child VK must be a member of a pre-approved set.

Factory creation is a composable effect within atomic turns---enabling flash-loan-style patterns where a factory spawns a child cell, the child performs work, and the parent observes the result, all within a single atomic turn with journal-based rollback on failure. Provenance tracking records which factory created each cell, enabling machine-auditable supply chains of cell construction. Factories are the foundation of *storage-as-cell-programs* (see @sec-storage-as-cell-programs)---every storage primitive lands as a factory whose descriptor declares the slot layout and `state_constraints`, with apps using the existing `createFromFactory` cclerk method to instantiate.

== Trust Assumptions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, center),
    table.header([*Layer*], [*Assumption*], [*PQ?*]),
    [STARK soundness], [Collision-resistant Poseidon2, FRI proximity], [Yes],
    [Merkle commitments], [Collision-resistant hash], [Yes],
    [Macaroon HMAC chain], [PRF security of HMAC-SHA256], [Yes],
    [Federation QCs (BLS12-381)], [Bilinear DH in $GG_1 times GG_2$], [No],
    [Node identity (Ed25519)], [DLP in twisted Edwards], [No],
    [Sealed secrets (X25519)], [CDH in Curve25519], [No],
    [Threshold decryption (Shamir + ChaCha20-Poly1305)], [PRF security of ChaCha20 + threshold secret-sharing], [No (ChaCha20)],
  ),
  caption: [Trust assumptions by layer. Items marked "No" are confined within federation trust boundaries.],
)

The critical invariant: *everything that crosses a trust boundary is post-quantum secure* (STARK proofs + Merkle commitments). Classical cryptography exists only between parties that already trust each other.

== Execution Model

=== The Effect VM <sec-effect-vm-intro>

The Effect VM is the primary execution mechanism for cells. It is a domain-specific virtual machine whose instruction set matches Pyana's state transition primitives. Each turn produces a single STARK proof regardless of effect count. The AIR trace---approximately 151 columns after Stage 7-$gamma$.0 + $gamma$.2 Phase 1 + sovereign-witness Phase 1, with public inputs growing per-cell to $tilde$73 felts---encodes:

- Pre-state commitment (Poseidon2 hash of cell state before each effect)
- Effect opcode and operands
- Post-state commitment (Poseidon2 hash of cell state after each effect)
- Conservation accumulator (running sum of value changes)
- Authority witness (EffectMask subset proof per effect)
- Queue state (KZG polynomial commitment for programmable queues)
- Per-cell `EFFECTS_HASH_BASE` row-0 aux-bound to in-trace effect bytes (Stage 7 cont §B)
- `ACTOR_NONCE` row-0 boundary-bound to `STATE_BEFORE_BASE + state::NONCE` (closes T5)
- `WITNESS_KEY_COMMIT` (sovereign-witness Phase 1) bound to `SOVEREIGN_WITNESS_KEY_COMMIT` PI
- Bilateral binding accumulators (Stage 7-$gamma$.2 Phase 1): `OUTGOING_TRANSFER_ROOT`, `INCOMING_TRANSFER_ROOT`, `OUTGOING_GRANT_ROOT`, `INCOMING_GRANT_ROOT`, `INTRO_AS_INTRODUCER_ROOT`, `INTRO_AS_RECIPIENT_ROOT`, `INTRO_AS_TARGET_ROOT`

State threading is enforced algebraically: each effect's post-state commitment equals the next effect's pre-state commitment. The final conservation accumulator must equal zero (no value created or destroyed). See @sec-effect-vm for the full instruction set.

=== Programmable Queues

The Effect VM supports _programmable queues_---ordered, committable message buffers with `Enqueue` and `Dequeue` as first-class effects. Queue state is tracked via KZG polynomial commitments, enabling constant-size queue proofs. In the storage-as-cell-programs view (@sec-storage-as-cell-programs), `ProgrammableQueue` is not a separate primitive but a cell whose `CellProgram` declares queue-shaped `StateConstraint`s---the executor's per-turn evaluator enforces queue invariants the same way it enforces any other slot caveat.

=== Pipeline Execution with Topological Ordering

The executor processes turns not only individually but in _pipelines_: batches of turns with declared dependency edges. A pipeline $P = (T, E)$ where $T = {t_0, ..., t_n}$ and $E subset.eq T times T$ is a DAG of dependency edges. The executor computes a topological ordering and processes turns in causal order. If turn $t_i$ fails and $t_j$ depends on $t_i$, then $t_j$ receives a `DependencyFailed` error without executing.

=== BudgetGate Integration

Every turn pays a fee in _computrons_. The executor integrates Stingray @stingray bounded counters directly: each silo holds a local budget slice $"slice"(i) = "balance" dot (f+1)/(2f+1)$ and debits locally without coordination until exhaustion. The executor checks $"fee" <= "remaining"$ before execution (fail-fast) and debits atomically upon commit. Budget accounting uses checked arithmetic throughout---overflow produces an executor error, never wraps.

=== Conservation Invariant

For any turn $t$ with actions $a_1, ..., a_k$, the executor enforces:

$ sum_i "balance_change"(a_i) + "fee"(t) = 0 $

Value cannot be created or destroyed within a turn. The fee is debited from the agent cell and does not reappear---it is the cost of execution. The conservation proof (when value commitments are used) is a Pedersen-Schnorr-Bulletproof combined proof (`FullConservationProof`); cleartext intra-cell conservation lives in `StateConstraint::SumEquals` / `SumEqualsAcross`.

== E-Style Distributed Object Semantics

=== `EventualRef` and Promise Pipelining

In E @elang, a message send returns a _promise_ that resolves when the target processes the message. Multiple messages can be sent to the resolution of a pending promise without waiting for it to resolve---_promise pipelining_ eliminates round-trip latency in distributed object protocols.

Pyana implements this via `EventualRef`: a reference to the output of a pending turn, identified by the turn's hash and an output slot index. A turn may target an `EventualRef` rather than a concrete `CellId`, declaring a dependency that the executor resolves during pipeline execution. The `Target` type is a sum:

$ "Target" = "Concrete"("CellId") | "Eventual"("source_turn": ["u8"; 32], "slot": "u32") $

When the source turn commits, its outputs (granted capabilities, created cells, state updates) populate a resolution table. Dependent turns rewrite their `EventualRef` targets to concrete `CellId` values before execution.

=== Three-Party Introduction

Object-capability systems form new communication paths through _introductions_: Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by granting Bob a (possibly attenuated) capability to Carol. In Pyana, an `Effect::Introduce` during a turn emits a `RoutingDirective` and contributes to the trilateral binding accumulators (`INTRO_AS_INTRODUCER_ROOT`, `INTRO_AS_RECIPIENT_ROOT`, `INTRO_AS_TARGET_ROOT`) with a canonical $"intro_id" = "Poseidon2"("pyana-intro-id-v1" || "introducer" || "recipient" || "target" || "permissions_bits" || "introducer_nonce")$. The pyana-verifier's `bilateral-pair` subcommand cross-checks that the three per-cell proofs of one `Introduce` agree on `intro_id`.

=== `Authorization::CapTpDelivered`

CapTP-delivered messages produce algebraically-bound Turns on the receiving ledger. The receiving executor accepts a Turn with `Authorization::CapTpDelivered { introducer, recipient_pk, handoff_cert, swiss_proof, ... }` after verifying: (a) the handoff certificate's Ed25519 introducer signature against the entry in `known_federations` for the originating federation, (b) the recipient's presentation signature against `recipient_pk`, (c) the swiss-bytes enliven against the local swiss table, (d) `max_uses` not exhausted. The resulting Turn produces a real `TurnReceipt`---the "CapTP messages produce on-chain receipts" Silver invariant.

`Authorization::Unchecked` is, in current production, only allowed via a CI-guarded carve-out list (Stage 8 P2.F); the soundness sweep is closing the last carve-outs. The mirror invariant "every CapTP mutation has a corresponding on-chain receipt" is the executor's responsibility; the wire layer's `pending_captp_turns` queue (formerly a black hole) is drained by `CapTpState::process_pending_turns` on every executor tick.

== DFA Routing as a Userspace Caveat <sec-dfa-routing>

DFA dispatch is a userspace primitive, not an implementation detail of the wire layer. The DFA-classification predicate (formerly tucked inside `wire::dfa_router`) lifts to a first-class `WitnessedPredicate { kind: Dfa, commitment: route_table_root, ... }` that:

- Slot caveats invoke as `StateConstraint::Witnessed(WP { kind: Dfa, ... })`.
- Per-action preconditions invoke as `Preconditions::witnessed`.
- Capability caveats invoke as `CapabilityCaveat::Witnessed`.

The route table commitment is bound in the cell's constitution; atomic table swaps are governance-bound; STARK-proved classification is via DSL lookup tables. `RouteTarget` extends to a fifth variant, `RouteTarget::Userspace { kind, payload }`, that dispatches into an app-registered userspace handler---used today by `apps/governed-namespace`, intent gossip filtering, and CapTP pre/post filters.

Constitutional amendment of a route table follows the reference group's H-rule: a member proposes a new transition table, $h$ members reference the proposal, on acceptance the new table replaces the old and its hash becomes part of the attested root.

== Service Mesh

The service mesh is a governed namespace acting as a capability registry. It provides mount/discover/resolve semantics for services within a federation. Mounting is an atomic turn effect that updates the federation's service registry---a Merkle-committed map from paths to `ServiceDescriptor` entries. Discovery uses direct resolution (Merkle lookup), prefix enumeration (governance-gated), and intent-based discovery (broadcast via the intent marketplace). Resolution is a two-phase lookup: route classification (DFA-attested) and service binding (returns the mounted cell's sturdy ref). See @sec-service-mesh for the full protocol.

== Nameservice <sec-nameservice>

Pyana's nameservice follows the petname model: names are always relative to the namer, never globally authoritative. Resolution through the nameservice is a form of capability discovery---resolving a name yields a capability reference.

- *Petnames* (local): private, per-agent mappings from human-readable strings to cell IDs. Stored in the agent's sealed state. Never published.
- *Edge names*: names that one agent publishes about another. Visible to third parties who query Alice's directory.
- *Proposed names*: names that a cell proposes for itself (self-description). Advisory only.

Names resolve hierarchically through delegation. Sub-delegation creates paths: Alice delegates naming authority for `alice/services/*` to a registry cell. Rental and dispute are governance-bound. The full protocol lives in @sec-service-mesh.

== Cell Migration and Teleportation <sec-cell-migration>

A sovereign cell can _teleport_ from federation $F_1$ to federation $F_2$:

+ Cell deregisters from $F_1$ (publishes final commitment + IVC proof).
+ Cell registers with $F_2$ (presents IVC proof as genesis state).
+ $F_2$ verifies the IVC proof covers valid history from genesis.
+ Cell is now sovereign under $F_2$'s ordering service.

The IVC proof carries the cell's entire history in constant size. No state is lost. The cell's identity ($"CellId"$) is unchanged. Vat splitting and merging follow analogous patterns: splitting partitions state across $N$ child cells via factory; merging unifies $N$ cells' states with a conservation-checked STARK.

== Boundary Discipline and the Two Sovereign Paths <sec-sovereign-paths>

Two distinct paths today serve sovereign cells, with different boundary contracts:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Path*], [*Executor sees*], [*AIR teeth*]),
    [Proof-carrying], [Only the commitment (executor blind)], [AIR binds `OLD_COMMIT == sovereign_commitments[cell_id]`],
    [Witness injection], [Cleartext cell state during turn (not persisted)], [Pre-AIR signature check; Phase 1 AIR adds `WITNESS_KEY_COMMIT` binding],
  ),
  caption: [The two sovereign-cell paths. Proof-carrying is the long-term default; witness injection is the integration-complete Silver default. Phase 2 sovereign-witness AIR teeth recurse into the optional `transition_proof` via Lane Golden-Edge's recursive verifier.],
)

The boundary vocabulary (Section 5) names the four populations per-datum: cleartext-inside (sees the plaintext); commitment-inside (sees the commitment but not the value); acceptance-inside (sees only proof-of-acceptance); out-of-band (learns nothing). A `FieldVisibility::Committed` slot is commitment-inside external readers, *but cleartext-inside the federation executor*: the visibility tag is a publication-policy choice on `public_field_view`, not a confidentiality primitive. Sovereign cells in proof-carrying mode are the only path where the executor is *not* cleartext-inside the cell's interior state.
