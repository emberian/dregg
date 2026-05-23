// =============================================================================
// Section 9: Service Mesh and Naming
// =============================================================================

= Service Mesh and Naming <sec-service-mesh>

== Design Goals

Capability systems excel at access control but traditionally lack discoverability: if you don't already hold a capability, how do you find one? Pyana's service mesh provides governed discovery without compromising the capability model. The three primitives---mount, discover, resolve---build atop DFA-based routing and constitutional governance to provide namespace-level access control provable via STARK lookup tables.

== DFA-Based Routing

The routing layer uses deterministic finite automata to classify incoming messages and determine dispatch targets. The DFA approach provides:

- *$O(n)$ classification*: One state integer per message byte, constant space.
- *Deterministic commitment*: The transition table hashes to a fixed 32-byte value bindable into governance constitutions.
- *Atomic route updates*: Swap the entire DFA table in one operation (constitutional amendment).
- *STARK-provable*: Classification decisions are provable via lookup tables in the Effect VM.

=== Route Table Structure

A compiled `RouteTable` consists of:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*Component*], [*Description*]),
    [`transitions: Vec<u8>`], [Flat array: $"states" times 256$ entries, each a next-state index],
    [`num_states: usize`], [Total states in DFA (state 0 = dead/reject)],
    [`accept_map: Map<u8, Target>`], [Maps accept states to route targets],
    [`commitment: [u8; 32]`], [BLAKE3 hash of transitions (for governance binding)],
  ),
  caption: [Route table structure. The commitment enables governance verification.],
)

=== Route Targets

Each accepted message is dispatched to one of four targets:

- *Cell*: Route to a specific cell by ID (direct delivery).
- *Handler*: Route to a named handler (e.g., "intent\_pool", "admin", "gossip").
- *Federation*: Forward to another reference group (cross-group routing).
- *Drop*: Silently discard (capability revoked or blocked topic).

=== DFA Construction

The DFA is constructed from a set of route rules. Each rule is a regex-like pattern over message prefixes:

```
/cap/*         -> Handler("cap_handler")
/intent/submit -> Handler("intent_pool")
/cell/<id>/*   -> Cell(<id>)
/admin/*       -> Drop  (unless governance override)
```

The rules are compiled into a minimal DFA via Brzozowski's algorithm (derivative-based construction), then the transition table is serialized and hashed. The hash becomes the `routes_commitment` in the group's constitution.

== Constitutional Amendment of Routes

Route tables are governance-controlled: changing the DFA requires a constitutional amendment (in Constitutional mode) or a governance proposal (in Open/Invite-Only modes).

=== Amendment Protocol

+ A member proposes a new route table (publishes the compiled DFA + commitment).
+ The proposal enters the blocklace as a proposal block.
+ Members vote by referencing the proposal in their blocks.
+ At threshold ($2f + 1$ for Constitutional mode), the new routes commitment replaces the old.
+ Nodes atomically swap their route tables to match the new commitment.

=== STARK-Proved Classification

For governance disputes, a STARK proof demonstrates that a given message was correctly classified by the committed DFA:

*Public inputs*: Message prefix hash, route table commitment, classification result.

*Private witness*: The message prefix bytes, the DFA transition trace (sequence of states visited).

*Statement*: Running the committed DFA over the message prefix produces the claimed accept state (or dead state for rejection).

This enables provable enforcement: a cell can prove its message was incorrectly routed (the DFA should have accepted but routed to Drop), triggering a governance dispute.

== Governed Namespaces

A _namespace_ is a governed mapping from human-readable names to capabilities. Namespaces are scoped to reference groups and protected by the group's DFA routing rules.

=== Namespace Operations

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Operation*], [*Authorization*], [*Effect*]),
    [`mount(name, cap)`], [Name owner + DFA permits], [Bind a name to a capability],
    [`discover(pattern)`], [DFA permits query], [Search for matching names],
    [`resolve(name)`], [DFA permits resolution], [Look up the capability for a name],
    [`unmount(name)`], [Name owner], [Remove binding],
    [`transfer(name, new_owner)`], [Current owner], [Change name ownership],
  ),
  caption: [Namespace operations. All are subject to DFA-based access control.],
)

=== Name Structure

Names follow a hierarchical path structure: `/org/team/service/endpoint`. Each path segment can have its own governance policy:

- `/` (root): Controlled by the reference group's constitution.
- `/org/`: Delegated to Organization's cell (sub-namespace authority).
- `/org/team/`: Further delegated by Organization to a team cell.
- `/org/team/service/`: The team mounts their service here.

Sub-delegation is capability-attenuated: the root authority delegates `/org/` with the restriction "cannot mount at root level." Each level can only narrow the scope of its children.

== Petname-Based Nameservice

The nameservice builds atop governed namespaces with a three-tier naming system inspired by Stiegler's petname architecture:

=== Name Types

+ *Petnames* (local, private): A cell's personal nickname for a capability. Never shared, never collide, fully under the cell's control. Stored in the cell's local state.

+ *Edge names* (relational): What one cell calls another in a specific relationship. Cell A's edge name for Cell B is visible to both but is A's choice. Published in A's directory.

+ *Proposed names* (public, contested): Names proposed for inclusion in a governed namespace. Subject to governance approval, rental fees, and dispute resolution.

=== Hierarchical Resolution

Name resolution proceeds through layers:

+ Check local petnames (instant, private).
+ Check edge names from known contacts (relational lookup).
+ Query governed namespace (public, DFA-protected).
+ If unresolved: return `None` (no ambient name authority).

This ensures that name resolution never bypasses capability boundaries: you can only resolve names that you already have some relationship to (via petname, edge, or namespace membership).

=== Name Rental

Proposed names in governed namespaces incur rental fees:

$ "rent"(n) = "base_rate" times |n|^(-1) times "demand_factor"(n) $

Shorter names cost more (inverse length pricing). High-demand names (frequently resolved) have increased rates. Rental is per-epoch; non-payment triggers release after a grace period.

=== Dispute Resolution

Name disputes (two cells claiming the same proposed name) are resolved via:

+ *First-come-first-served* (default): The first cell to mount at a name holds priority.
+ *Auction* (governance-configurable): Disputed names go to sealed-bid auction.
+ *Arbitration* (for trademark-like disputes): A governance vote among reference group members.

== Service Discovery

The service mesh provides three discovery mechanisms:

=== Capability Registry

A governed capability registry maps service descriptors to cell endpoints:

```
{
  "service": "inference",
  "model": "llama-70b",
  "rate_limit": 100,
  "location": StrandId(0xab12...),
  "capability": SturdyRef("pyana://...")
}
```

Registrations are DFA-governed: only cells with mount authority at the appropriate namespace path can register services. Queries are DFA-governed: only cells with resolve authority can discover services.

=== Intent-Based Discovery

Cells that cannot find a service via the registry can broadcast an intent (Section 10). The intent marketplace matches needs to capabilities without requiring prior knowledge of the provider.

=== Three-Party Introduction

The most privacy-preserving discovery: a mutual contact introduces two cells that should communicate. No public registry query, no intent broadcast---just a signed `Effect::Introduce` that creates a bilateral relationship.

== DFA Routing and Access Control Integration

The DFA serves as the unifying enforcement mechanism:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Layer*], [*DFA Role*], [*Enforcement*]),
    [Message routing], [Classify message prefix], [Drop unauthorized messages],
    [Namespace access], [Permit mount/resolve/discover], [Block unauthorized operations],
    [Service registry], [Permit registration/query], [Scope service visibility],
    [Cross-group forwarding], [Permit relay to remote groups], [Contain message scope],
  ),
  caption: [DFA enforcement layers. A single committed transition table governs all access control within a reference group.],
)

The DFA is intentionally _coarse-grained_ (prefix-based classification, not deep inspection). Fine-grained access control is delegated to capability-level checks within cells. The DFA provides namespace-level governance; capabilities provide object-level authority. This separation mirrors the DNS/firewall distinction in traditional networking---the DFA is the firewall, capabilities are the application-level authorization.

== Security Analysis

*Completeness*: Any message that should be routable IS routable (the DFA accepts all legitimate prefixes by construction---the route table is compiled from the complete rule set).

*Soundness*: A message classified as "Drop" cannot reach its target without either (a) amending the constitution (governance) or (b) bypassing the DFA (requires compromising the executor---detected via replication).

*Governance binding*: The routes commitment in the constitution provides cryptographic binding between the governance decision and the enforcement mechanism. A node running a different DFA from the committed one produces verifiably incorrect routing decisions.
